from opal.logic.base.base_ontology import Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, ForAll, Exists, And, Or, Implies
from z3 import parse_smt2_string, Z3Exception
import re



# This dictionary maps logical operation names (as captured in the ontology JSON) to their corresponding Z3 functions
LOGICAL_OPS = {
    'ForAll': lambda var, body: ForAll(var, body),
    'Iff': lambda a, b: (a) == (b),
    'Exists': lambda var, body: Exists(var, body),
    'And': And,
    'Or': Or,
    'Not': Not,
    'Implies': Implies,
    '=': lambda a, b: a == b, 
    '<': lambda a, b : a < b,
    '<=': lambda a, b : a <= b,
    '>': lambda a, b : a > b,
    '>=': lambda a, b : a >= b,
}

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
    
    @classmethod
    def from_smt2(cls, ontology_str, mapping):
        """
        Loads the ontology from a SMT-LIB representation.

        Args:
            smt2_str (str): The SMT-LIB text representation of the ontology, or a path to the SMT-LIB file.
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

        # Add the parsed assertions to the ontology
        cls._add_axioms(ontology, ont_axioms, prefix="ont")
        cls._add_literals(ontology, ont_ground, prefix="ont")
        
        # Add the mapping assertions to the ontology
        cls._add_axioms(ontology, map_axioms, prefix="map")
        cls._add_literals(ontology, map_ground, prefix="map")
        
        # Parse the remaining SMT-LIB string to extract additional non-assertion statements (declarations, signature, etc.)
        remaining_str = ont_str_other + map_str_other
        parse_smt2_string(remaining_str, )

        return ontology
      
      
    @staticmethod
    def _load_assertions_from_smtlib(smtlib_str):
        named_assertions, remaining_str = Z3Ontology.extract_named_assertions(smtlib_str)

        axiom_assertions = [a for a in named_assertions if 'forall' in a['formula'] or 'exists' in a['formula']]
        ground_assertions = [a for a in named_assertions if a not in axiom_assertions]

        return axiom_assertions, ground_assertions, remaining_str

    @staticmethod
    def _add_axioms(ontology, assertions, prefix):
        for i, assertion in enumerate(assertions):
            name = f"{prefix}_t_{i}_{assertion['name']}"
            print(f"Adding axiom: {name}")
            ontology.add_axiom({
                'name': name,
                'description': assertion['description'],
                'expr': assertion['formula']
            })

    @staticmethod
    def _add_literals(ontology, assertions, prefix):
        for i, assertion in enumerate(assertions):
            predicate = assertion.get('predicate')
            terms = assertion.get('terms', [])
            positive = assertion.get('positive', True)
            name = f"{prefix}_a_{i}_{predicate}({terms})"
            ontology.add_literal({name: Z3Literal(predicate, terms, positive)})

    
    @staticmethod
    def extract_named_assertions(smtlib_str):
        pattern = re.compile(
            r'\(assert\s+\(!\s*(.*?)\)\)', re.DOTALL
        )

        assertions = []
        spans_to_remove = []

        for match in pattern.finditer(smtlib_str):
            full_block = match.group(0)
            inner = match.group(1)
            spans_to_remove.append(match.span())

            # Find attributes (e.g., :named, :description)
            named_match = re.search(r':named\s+(\w+)', inner)
            desc_match = re.search(r':description\s+"(.*?)"', inner)

            name = named_match.group(1) if named_match else None
            description = desc_match.group(1) if desc_match else None

            assertions.append({
                'name': name,
                'description': description,
                'formula': full_block
            })

        # Remove matched spans from the original string
        remaining_parts = []
        last_index = 0
        for start, end in spans_to_remove:
            remaining_parts.append(smtlib_str[last_index:start])
            last_index = end
        remaining_parts.append(smtlib_str[last_index:])

        remaining_str = ''.join(remaining_parts)

        return assertions, remaining_str
    
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
        self.axioms.append(axiom)

    def add_literal(self, literal):
        """
        Adds a literal to the ontology.
        Args:
            literal (dictionary): The literal to add
        """
        self.literals.append(literal)
    
    @property
    def axioms(self):
        """
        Returns the axioms of the ontology.
        
        Returns:
            An iterable containing the axioms of the ontology.
        """
        return self._axioms
        

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


PSL_CORE_JSON = {
    'axioms': [
    {
    'name' : 'type_disjointness',
    'description' : 'activities, occurrences, and objects are different things.',
    'axiom' : '''ForAll([x], And(
    Implies(activity(x), Not(Or(activity_occurrence(x), object_(x)))),
    Implies(activity_occurrence(x), Not(Or(object_(x), activity(x)))),
    Implies(object_(x), Not(Or(activity_occurrence(x), activity(x)))),
    '''
    },
    {
    'name' : 'begin_unique',
    'description' : 'Start points are unique.',
    'axiom' : 'ForAll([x, t1, t2], Implies(And(begin_of(x) = t1, begin_of(x) = t2), (t1 = t2)))'
    },
    {
    'name' : 'ends_unique',
    'description' : 'End points are unique.',
    'axiom' : 'ForAll([x, t1, t2], Implies(And(end_of(x) = t1, end_of(x) = t2), (t1 = t2)))'
    },
    {
    'name' : 'occurrence_bounds',
    'description' : 'Activity occurrence start points are before or equal to their end points.',
    'axiom' : '''ForAll([o], Implies(
        activity_occurrence(o),
        Exists([t1, t2], And(
            begin_of(o) = t1,
            end_of(o) = t2,
            t1 <= t2
        ))))'''
    },
    {
    'name' : 'occurrence_sort_constraints',
    'description' : 'Occurrences are the occurrences of activities.',
    'axiom' : 'ForAll([a, o], Implies(occurrence_of(o,a), And(activity_occurrence(o), activity(a))))'
    },
    {
    'name' : 'unique_activity_occurrence',
    'description' : 'Activity occurrences are an occurrence of a single unique activity.',
    'axiom' : '''ForAll([o, a1, a2], Implies(And(occurrence_of(o, a1), occurrence_of(o, a2)), a1 = a2))'''
    },
    {
    'name': 'occurrence_has_activity',
    'description': 'Every activity occurrence is the occurrence of some activity.',
    'axiom': '''ForAll([occ], Implies(
        activity_occurrence(occ),
        Exists([a], And(
            activity(a),
            occurrence_of(occ, a)))))'''
    },
    {
    'name': 'participation_sort_constraints',
    'description': 'The participates_in relation only holds between objects, activity occurrences, and timepoints, respectively.',
    'axiom': '''ForAll([x, occ, t], Implies(
        participates_in(x, occ, t),
        And(object(x), activity_occurrence(occ), timepoint(t))))'''
    },
    {
    'name': 'participation_temporal_constraint',
    'description': 'An object can participate in an activity occurrence only at those timepoints at which both the object exists and the activity is occurring.',
    'axiom': '''ForAll([x, occ, t], Implies(
        participates_in(x, occ, t),
        And(
            exists_at(x, t),
            is_occurring_at(occ, t)
        )))'''
    },
    {
    'name': 'object_temporal_existence',
    'description': 'An object exists at a timepoint t if and only if t is between or equal to its begin and end points.',
    'axiom': '''ForAll([x, t], Iff(
        exists_at(x, t),
        And(
            object(x),
            begin_of(x) <= t <= end_of(x)
        )))'''
    },
    {
    'name': 'occurrence_temporal_extent',
    'description': 'An activity is occurring at a timepoint t if and only if t is between or equal to the begin and end points of the activity occurrence.',
    'axiom': '''ForAll([occ, t], Iff(
        is_occurring_at(occ, t),
        And(
            activity_occurrence(occ),
            begin_of(occ) <= t <= end_of(occ)
        )))'''
    }
    ]}
    
    
PSL_MAPPING_JSON = {
        'axioms': [
            {'name': 'occurrence_start_end_event_mapping',
            'description': 'Maps start and complete events to activity occurrences.',
            'axiom': '''
            ForAll([e1, e2, t1, t2, c, a],
                Implies(
                    And(
                        hasCase(e1, c),
                        hasCase(e2, c),
                        hasActivity(e1, a),
                        hasActivity(e2, a),
                        hasLifecycleTransition(e1, start),
                        hasLifecycleTransition(e2, complete),
                        hasRecordedTime(e1, t1),
                        hasRecordedTime(e2, t2)
                    ),
                    Exists([o],
                        And(
                            occurrence_of(o, a),
                            begin_of(o, t1),
                            end_of(o, t2),
                            subactivity_occurrence(o, c),
                            o != c 
                        )
                    )
                )
            )
            '''
            },
        ],
    'ground': [
        {'predicate': 'transition', 'terms': ['start'], 'positive': True},
        {'predicate': 'transition', 'terms': ['complete'], 'positive': True},
    ]
}