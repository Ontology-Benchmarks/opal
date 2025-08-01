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

# Define type for individuals
Ind = DeclareSort('Ind')

class Z3Ontology(Ontology):
    """
    A concrete subclass of Ontology that uses Z3 for logical reasoning.
    
    This class is intended to be used with Z3 expressions and provides methods
    for managing axioms, individuals, and the signature of the ontology.
    """

    def __init__(self, signature):
        """
        Initializes a new instance of the Z3Ontology class.
        """
        super().__init__()
        self._predicate_map = signature or {}
    
    @classmethod
    def from_smt2(cls, smt2_str, signature=None):
        """
        Loads the ontology from a SMT-LIB representation.

        Args:
            smt2_str (str): The SMT-LIB text representation of the ontology, or a path to the SMT-LIB file.
        Returns:
            self: The current instance of the ontology.
        """
        ontology = cls(signature=signature)
        
        # Check if supplied json arg is a file path or a string
        if smt2_str.endswith('.smt2'):
            with open(smt2_str, 'r') as f:
                smt2_str = f.read()

        # Segment smt2 string into axioms and signature/declarations


        for i, axiom in enumerate(assertions):
            # Parse the axiom expression
            a_name = f"ont_t_{i}_{axiom['name']}"
            print(f"Adding axiom: {a_name}")
            a_description = axiom['description']
            expr = ontology._parse_expression(axiom['axiom'])
            axiom_dict = {
            'name': a_name,
            'description': a_description,
            'expr': expr
            }
            ontology.add_axiom(axiom_dict)
            
        for i,ground in enumerate(ontology_json['ground']):
            # Parse the ground literal
            predicate = ground['predicate']
            terms = ground.get('terms', [])
            positive = ground.get('positive', True)
            name = f'ont_a_{i}_{predicate}({terms})'
            z3_literal = Z3Literal(predicate, terms, positive)
            literal_dict = {name : z3_literal}
            ontology.add_literal(literal_dict)
            
        
        return ontology
    
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
        

PSL_SMT2 = '''
(declare-sort Ind 0)

(declare-fun activity (Ind) Bool)
(declare-fun activity_occurrence (Ind) Bool)
(declare-fun object_ (Ind) Bool)
(declare-fun event (Ind) Bool)
(declare-fun transition (Ind) Bool)
(declare-fun timepoint (Real) Bool)

(declare-fun occurrence_of (Ind Ind) Bool)
(declare-fun participates_in (Ind Ind Real) Bool)
(declare-fun exists_at (Ind Real) Bool)
(declare-fun is_occurring_at (Ind Real) Bool)

(declare-fun begin_of (Ind) Real)
(declare-fun end_of (Ind) Real)

(assert (! 
  (forall ((x Ind)) 
    (or (activity x) (activity_occurrence x) (object_ x) (event x) (transition x))
  )
  :named type_partition
  :description "All objects are either activities, occurrences, objects, events, or transitions."
))

(assert (! 
  (forall ((x Ind)) 
    (and
      (=> (activity x) (not (or (activity_occurrence x) (object_ x) (event x) (transition x))))
      (=> (activity_occurrence x) (not (or (object_ x) (activity x) (event x) (transition x))))
      (=> (object_ x) (not (or (activity_occurrence x) (activity x) (event x) (transition x))))
      (=> (event x) (not (or (activity_occurrence x) (activity x) (object_ x) (transition x))))
      (=> (transition x) (not (or (activity_occurrence x) (activity x) (object_ x) (event x))))
    )
  )
  :named type_disjointness
  :description "Activities, occurrences, objects, events, and transitions are different things."
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


PSL_CORE_JSON = {
    'axioms': [
    {
    'name' : 'type_partition',
    'description' : 'All objects are either activities, occurrences, objects, events, or transitions.',
    'axiom' : 'ForAll([x], Or(activity(x), activity_occurrence(x), object_(x), event(x), transition(x))'
    },
    {
    'name' : 'type_disjointness',
    'description' : 'activities, occurrences, objects, events, and transitions are different things.',
    'axiom' : '''ForAll([x], And(
    Implies(activity(x), Not(Or(activity_occurrence(x), object_(x), event(x), transition(x)))),
    Implies(activity_occurrence(x), Not(Or(object_(x), activity(x), event(x), transition(x)))),
    Implies(object_(x), Not(Or(activity_occurrence(x), activity(x), event(x), transition(x)))),
    Implies(event(x), Not(Or(activity_occurrence(x), activity(x), object_(x), transition(x)))),
    Implies(transition(x), Not(Or(activity_occurrence(x), activity(x), object_(x), event(x))))))'''
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