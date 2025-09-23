from opal.logic.z3.z3_literal import Z3Literal
from opal.logic.z3.z3_ontology import Z3Ontology
from z3 import parse_smt2_string
import re

class Z3Pattern:
    def __init__(self, args: dict, pattern_str: str, pattern_name: str):
        """
        Initialize a Z3 pattern.
        
        Args:
            args (dict): Dictionary mapping argument names to their descriptions
                        e.g., {"activity1": "First activity name", "activity2": "Second activity name"}
            pattern_str (str): SMT-LIB template string with placeholders like {activity1}, {activity2}
        """
        self.args = args
        self.pattern_str = pattern_str
        self.name = pattern_name
        self._validate_pattern()
    
    def _validate_pattern(self):
        """Validate that all placeholders in pattern_str have corresponding args."""
        placeholders = re.findall(r'\{(\w+)\}', self.pattern_str)
        missing_args = set(placeholders) - set(self.args.keys())
        if missing_args:
            raise ValueError(f"Pattern contains placeholders without corresponding args: {missing_args}")
    
    def apply(self, **kwargs):
        """
        Apply the pattern with concrete argument values.
        
        Args:
            **kwargs: Argument values to substitute into the pattern
            
        Returns:
            str: SMT-LIB string with arguments substituted
            
        Raises:
            ValueError: If required arguments are missing
        """
        missing_args = set(self.args.keys()) - set(kwargs.keys())
        if missing_args:
            raise ValueError(f"Missing required arguments: {missing_args}")
        
        # Substitute arguments into the pattern
        result = self.pattern_str.format(**kwargs)
        return result
    
    def create_z3_expr(self, **kwargs):
        """
        Create a Z3 expression from the pattern string using the provided environment.
        
        Args:
            env: Z3 environment/context
            **kwargs: Argument values to substitute into the pattern
            
        Returns:
            Z3 expression object
        """
        smt2_string = self.apply(**kwargs)
        return smt2_string
    
    def get_arg_descriptions(self):
        """
        Get descriptions of all arguments required by this pattern.
        
        Returns:
            dict: Copy of the args dictionary
        """
        return self.args.copy()
    
    def __str__(self):
        """String representation showing the pattern and its arguments."""
        args_str = "\n".join([f"  {name}: {desc}" for name, desc in self.args.items()])
        return f"Z3Pattern(\n{args_str}\n)\nTemplate:\n{self.pattern_str}"

# Pattern definitions for common process mining patterns

# Pattern definitions based on the formal definitions in the paper

OCCURS_IN_CASE_PATTERN = Z3Pattern(
    args={
        "activity": "Name of the activity to check",
        "case_id": "Case identifier to check within"
    },
    pattern_str="""
(assert (exists ((e Ind))
    (and
        (hasActivity e {activity})
        (hasCase e {case_id})
    )
))""",
    pattern_name="Occurs in Case"
)

HAND_OFF_PATTERN = Z3Pattern(
    args={
        "r1": "First resource involved in the hand-off",
        "r2": "Second resource involved in the hand-off", 
        "o1": "First activity occurrence in the hand-off",
        "o2": "Second activity occurrence in the hand-off",
        "case": "Case identifier for the case in which the hand-off takes place"
    },
    pattern_str="""
(assert (forall ((r1 Ind) (r2 Ind) (o1 Ind) (o2 Ind) (c Ind))
    (=> (and
            (next_subOcc o1 o2 c)
            (participates r1 o1)
            (participates r2 o2)
            (not (= r1 r2))
        )
    )
    (hand_off r1 r2 o1 o2 c)
))""",
pattern_name="Hand-off"
)

PING_PONG_PATTERN = Z3Pattern(
    args={
        "case": "Case identifier to check for ping-pong behavior"
    },
    pattern_str="""
(assert (forall ((c Ind))
    (=> (exists ((e1 Ind) (e2 Ind) (e3 Ind) (e4 Ind) (r1 Ind) (r2 Ind) (r3 Ind) (r4 Ind))
            (and
                (hand_off r1 r2 e1 e2 c)
                (hand_off r3 r4 e3 e4 c)
                (not (= e1 e3))
                (not (= e2 e4))
            ))
        (ping_pong c)
    )
))""",
pattern_name='Ping-pong'
)

# Query pattern to find all instances of ping-pong behavior
PING_PONG_QUERY_PATTERN = Z3Pattern(
    args={},
    pattern_str="""
(assert (exists ((c Ind))
    (ping_pong c)
))"""
)

# Additional common patterns
DIRECTLY_FOLLOWS_PATTERN = Z3Pattern(
    args={
        "activity1": "First activity that must occur",
        "activity2": "Second activity that must directly follow",
        "case_id": "Case identifier"
    },
    pattern_str="""
(assert (exists ((e1 Event) (e2 Event) (t1 Real) (t2 Real))
    (and
        (hasActivity e1 {activity1})
        (hasActivity e2 {activity2})
        (hasCase e1 {case_id})
        (hasCase e2 {case_id})
        (hasRecordedTime e1 t1)
        (hasRecordedTime e2 t2)
        (< t1 t2)
        ; No other event between e1 and e2 in the same case
        (not (exists ((e3 Event) (t3 Real))
            (and
                (hasCase e3 {case_id})
                (hasRecordedTime e3 t3)
                (< t1 t3)
                (< t3 t2)
            )
        ))
    )
))"""
)