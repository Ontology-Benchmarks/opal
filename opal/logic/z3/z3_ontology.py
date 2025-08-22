from opal.logic.base.base_ontology import Ontology
from opal.logic.z3.z3_literal import Z3Literal
from opal.logic.z3.z3_handler import parse_smt2_declarations, REFERENCE_TAXONOMY_ENV
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, ForAll, Exists, And, Or, Implies
from z3 import parse_smt2_string, Z3Exception
import re
import sexpdata

class Z3Ontology(Ontology):
    """
    A concrete subclass of Ontology that uses Z3 for logical reasoning.
    
    This class is intended to be used with Z3 expressions and provides methods
    for managing axioms, individuals, and the signature of the ontology.
    """

    def __init__(self):
        """
        Initializes a new instance of the Z3Ontology class.
        """
        super().__init__()
        # initialize the environment according to the reference taxonomy
        self._env = REFERENCE_TAXONOMY_ENV
        self._axioms = []
        self._literals = []

    @classmethod
    def from_smt2(cls, ontology_str, mapping):
        """
        Loads the ontology from a SMT-LIB representation.

        Args:
            ontology_str (str): The SMT-LIB text representation of the ontology, or a path to the SMT-LIB file.
            
            mapping (str): The SMT-LIB text representation of the mapping (from the language of the reference taxonomy into the language of the ontology),
            or a path to the SMT-LIB file.

        Returns:
            self: The current instance of the ontology.
        """
        ontology = cls()
      
        # Check if the input is a file path or a string
        if ontology_str.endswith('.smt2'):
            with open(ontology_str, 'r') as f:
                ontology_str = f.read()
                
        if mapping.endswith('.smt2'):
            with open(mapping, 'r') as f:
                mapping = f.read()
                
        # Parse the SMT-LIB string to extract all named assertions
        ont_axioms, ont_ground, ont_str_other = cls._load_assertions_from_smtlib(ontology_str)
        map_axioms, map_ground, map_str_other = cls._load_assertions_from_smtlib(mapping)
        
        # Parse the remaining SMT-LIB string to extract additional non-assertion statements (declarations, signature, etc.)
        remaining_str = ont_str_other + map_str_other
        
        # update the extracted environment to the ontology
        env = parse_smt2_declarations(remaining_str, env = ontology._env)
        ontology._env = env
        
        # Add the parsed assertions to the ontology
        ontology._add_axioms(ont_axioms, prefix="ont")
        ontology._add_literals(ont_ground, prefix="ont")

        # Add the mapping assertions to the ontology
        ontology._add_axioms(map_axioms, prefix="map")
        ontology._add_literals(map_ground, prefix="map")

        return ontology
      
    def load_additional_smt2(self, smt2_str):
        """
        Loads additional SMT-LIB2 declarations into the ontology.

        Args:
            smt2_str (str): The SMT-LIB2 string to parse.
        """
        env = parse_smt2_declarations(smt2_str, env=self._env)
        self._env = env
        
    @staticmethod
    def _load_assertions_from_smtlib(smtlib_str):
        named_assertions, remaining_str = Z3Ontology.extract_named_assertions(smtlib_str)

        axiom_assertions = [a for a in named_assertions if 'forall' in a['formula'] or 'exists' in a['formula']]
        ground_assertions = [a for a in named_assertions if a not in axiom_assertions]

        return axiom_assertions, ground_assertions, remaining_str

    def _add_axioms(self, assertions, prefix):
        for i, assertion in enumerate(assertions):
            name = f"{prefix}_t_{i}_{assertion['name']}"
            print(f"Adding axiom: {name}")
            self.add_axiom({
                'name': name,
                'description': assertion['description'],
                'expr': assertion['formula']
            })

    @staticmethod
    def parse_ground_assertion(smtlib_str):
      expr = sexpdata.loads(smtlib_str)

      # expr looks like: ['assert', ['!', ['transition', 'T_start'], ':named', 'transition_start', ':description', '...']]
      if expr[0].value() != "assert":
          raise ValueError("Not an assertion")

      inner = expr[1]  # match on the (! ...)
      if inner[0].value() != "!":
          raise ValueError("Assertion not annotated")

      formula = inner[1]   # inner part of ground formula (transition T_start)
      
      positive = True

      # Check if the assertion is negated
      if isinstance(formula, list) and formula[0].value() == "not":
          positive = False
          formula = formula[1]  # unwrap inner formula
        
      predicate = formula[0].value()
      terms = [t.value() if isinstance(t, sexpdata.Symbol) else t for t in formula[1:]]

      # get annotations
      name = None
      description = None
      for i in range(2, len(inner), 2):
          key = inner[i].value()
          val = inner[i+1]
          if key == ":named":
              name = val.value() if isinstance(val, sexpdata.Symbol) else val
          elif key == ":description":
              description = val

      return {
          "predicate": predicate,
          "terms": terms,
          "name": name,
          "description": description,
          "positive": positive
      }

    def _add_literals(self, assertions, prefix):
      
        for i, assertion in enumerate(assertions):
            parsed_assertion = self.parse_ground_assertion(assertion['formula'])
            name = parsed_assertion['name']
            name = f"{prefix}_a_{i}_{name}"
            terms = parsed_assertion['terms']
            predicate = parsed_assertion['predicate']
            positive = parsed_assertion['positive']

            self.add_literal({name : Z3Literal(predicate, terms, positive, env=self._env)})

    @staticmethod
    def extract_named_assertions(smtlib_str):
      parsed = sexpdata.loads(f"({smtlib_str})")  # wrap in () to parse multiple top-level forms

      assertions = []
      remaining = []

      for expr in parsed:
          if isinstance(expr, list) and expr and expr[0].value() == "assert":
              inner = expr[1]  # (! ... )
              if isinstance(inner, list) and inner[0].value() == "!":
                  formula = inner[1]
                  attrs = inner[2:]

                  name = None
                  description = None
                  for i in range(0, len(attrs), 2):
                      key = attrs[i].value()
                      val = attrs[i+1]
                      if key == ":named":
                          name = val.value()
                      elif key == ":description":
                          description = val

                  assertions.append({
                      "name": name,
                      "description": description,
                      "formula": sexpdata.dumps(expr)  # dump back to string
                  })
              else:
                  remaining.append(sexpdata.dumps(expr))
          else:
              remaining.append(sexpdata.dumps(expr))

      return assertions, "\n".join(remaining)
    
    def _is_temporal_variable(self, var_name):
        """
        Determines if a variable name represents a temporal variable.
        
        Args:
            var_name (str): The variable name to check
            
        Returns:
            bool: True if the variable represents time, False otherwise
        """
        # Check for common temporal variable patterns
        temporal_patterns = [
            r'^t$',           # just 't'
            r'^t\d+$',        # t1, t2, t3, etc.
        ]
        
        for pattern in temporal_patterns:
            if re.match(pattern, var_name, re.IGNORECASE):
                return True
        
        return False
        
    def add_axiom(self, axiom):
        """
        Adds an axiom to the ontology.
        Args:
            axiom (dictionary): The axiom to add
        """
        self._axioms.append(axiom)

    def add_literal(self, literal):
        """
        Adds a literal to the ontology.
        Args:
            literal (dictionary): The literal to add
        """
        self._literals.append(literal)
    
    @property
    def axioms(self):
        """
        Returns the axioms of the ontology.
        
        Returns:
            An iterable containing the axioms of the ontology.
        """
        return self._axioms

    @property
    def literals(self):
        """
        Returns the literals of the ontology.

        Returns:
            An iterable containing the literals of the ontology.
        """
        return self._literals

REFERENCE_TAXONOMY_SIG_SMT2 = '''
(declare-sort Ind 0)

(declare-fun Event (Ind) Bool)
(declare-fun Transition (Ind) Bool)
(declare-fun Activity (Ind) Bool)
(declare-fun Case (Ind) Bool)
(declare-fun Resource (Ind) Bool)
(declare-fun hasResource (Ind Ind) Bool)
(declare-fun hasRecordedTime (Ind Real) Bool)
(declare-fun hasLifecycleTransition (Ind Ind) Bool)
(declare-fun hasCase (Ind Ind) Bool)
(declare-fun hasActivity (Ind Ind) Bool)


; Declare individual constants for start and complete transitions
(declare-const Ind T_start)
(declare-const Ind T_complete)
'''

PSL_CORE_SIG_SMT2 = '''
(declare-fun activity (Ind) Bool)
(declare-fun activity_occurrence (Ind) Bool)
(declare-fun object_ (Ind) Bool)
(declare-fun timepoint (Real) Bool)

(declare-fun occurrence_of (Ind Ind) Bool)
(declare-fun participates_in (Ind Ind Real) Bool)
(declare-fun exists_at (Ind Real) Bool)
(declare-fun is_occurring_at (Ind Real) Bool)

(declare-fun begin_of (Ind) Real)
(declare-fun end_of (Ind) Real)
'''

PSL_CORE_SMT2 = '''
(assert (! 
  (forall ((x Ind)) 
    (and
      (=> (activity x) (not (or (activity_occurrence x) (object_ x))))
      (=> (activity_occurrence x) (not (or (object_ x) (activity x))))
      (=> (object_ x) (not (or (activity_occurrence x) (activity x))))
    )
  )
  :named type_disjointness
  :description "Activities, occurrences, and objects are different things."
))

(assert (! 
  (forall ((x Ind) (t1 Real) (t2 Real)) 
    (=> (and (= (begin_of x) t1) (= (begin_of x) t2)) (= t1 t2))
  )
  :named begin_unique
  :description "Start points are unique."
))

(assert (! 
  (forall ((x Ind) (t1 Real) (t2 Real)) 
    (=> (and (= (end_of x) t1) (= (end_of x) t2)) (= t1 t2))
  )
  :named ends_unique
  :description "End points are unique."
))

(assert (! 
  (forall ((o Ind)) 
    (=> (activity_occurrence o)
      (exists ((t1 Real) (t2 Real)) 
        (and 
          (= (begin_of o) t1)
          (= (end_of o) t2)
          (<= t1 t2)
        )
      )
    )
  )
  :named occurrence_bounds
  :description "Activity occurrence start points are before or equal to their end points."
))

(assert (! 
  (forall ((a Ind) (o Ind)) 
    (=> (occurrence_of o a) (and (activity_occurrence o) (activity a)))
  )
  :named occurrence_sort_constraints
  :description "Occurrences are the occurrences of activities."
))

(assert (! 
  (forall ((o Ind) (a1 Ind) (a2 Ind)) 
    (=> (and (occurrence_of o a1) (occurrence_of o a2)) (= a1 a2))
  )
  :named unique_activity_occurrence
  :description "Activity occurrences are an occurrence of a single unique activity."
))

(assert (! 
  (forall ((occ Ind)) 
    (=> (activity_occurrence occ) 
      (exists ((a Ind)) 
        (and (activity a) (occurrence_of occ a))
      )
    )
  )
  :named occurrence_has_activity
  :description "Every activity occurrence is the occurrence of some activity."
))

(assert (! 
  (forall ((x Ind) (occ Ind) (t Real)) 
    (=> (participates_in x occ t) 
      (and (object x) (activity_occurrence occ) (timepoint t))
    )
  )
  :named participation_sort_constraints
  :description "The participates_in relation only holds between objects, activity occurrences, and timepoints, respectively."
))

(assert (! 
  (forall ((x Ind) (occ Ind) (t Real)) 
    (=> (participates_in x occ t) 
      (and (exists_at x t) (is_occurring_at occ t))
    )
  )
  :named participation_temporal_constraint
  :description "An object can participate in an activity occurrence only at those timepoints at which both the object exists and the activity is occurring."
))

(assert (! 
  (forall ((x Ind) (t Real)) 
    (= (exists_at x t) 
      (and (object x) (<= (begin_of x) t) (<= t (end_of x)))
    )
  )
  :named object_temporal_existence
  :description "An object exists at a timepoint t if and only if t is between or equal to its begin and end points."
))

(assert (! 
  (forall ((occ Ind) (t Real)) 
    (= (is_occurring_at occ t) 
      (and (activity_occurrence occ) (<= (begin_of occ) t) (<= t (end_of occ)))
    )
  )
  :named occurrence_temporal_extent
  :description "An activity is occurring at a timepoint t if and only if t is between or equal to the begin and end points of the activity occurrence."
))
'''

PSL_CORE_MAPPING_SMT2 = '''
assert (! 
  (forall ((e1 Ind) (e2 Ind) (t1 Real) (t2 Real) (c Ind) (a Ind))
    (=> (and
      (hasCase e1 c)
      (hasCase e2 c)
      (hasActivity e1 a)
      (hasActivity e2 a)
      (hasLifecycleTransition e1 T_start)
      (hasLifecycleTransition e2 T_complete)
      (hasRecordedTime e1 t1)
      (hasRecordedTime e2 t2)
    )
    (exists ((o Ind))
      (and
        (occurrence_of o a)
        (= (begin_of o) t1)
        (= (end_of o) t2)
      )
    )
  )
  :named occurrence_start_end_event_mapping
  :description "Maps start and complete events to activity occurrences."

  assert (! (transition T_start)
  :named transition_start
  :description "declaration of the start transition"

  assert (! (transition T_complete))
  :named transition_complete
  :description "declaration of the complete transition"
)
'''