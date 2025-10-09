from opal.logic.z3.z3_literal import Z3Literal
from opal.logic.z3.z3_ontology import Z3Ontology
from z3 import parse_smt2_string
import re

class Z3Pattern:
    def __init__(self, args: dict, pattern_str: str, pattern_name: str, requires : list = None):
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
        if requires:
            if not all(isinstance(req, Z3Pattern) for req in requires):
                raise TypeError("All items in 'requires' must be instances of Z3Pattern.")
            self.requires = requires
        else:
            self.requires = []
        
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
        results = []
        
        # verify that correct args are provided
        missing_args = set(self.args.keys()) - set(kwargs.keys())
        if missing_args:
            raise ValueError(f"Missing required arguments: {missing_args}")
        
        extra_args = set(kwargs.keys()) - set(self.args.keys())
        if extra_args:
            raise ValueError(f"Received unexpected arguments: {extra_args}")
        for req in self.requires:
            if not all(arg in kwargs for arg in req.args):
                raise ValueError(f"Missing required arguments for prerequisite pattern '{req.name}': {set(req.args.keys()) - set(kwargs.keys())}")
            req_result = req.apply(**{k: kwargs[k] for k in req.args})
            results.extend(req_result)
        
        subs = {f'{k}:{v}' for k, v in kwargs.items()}
        name = f"p_{self.name}_{'_'.join(subs)}"
        result = {'name': name, 'expr': self.pattern_str.format(**kwargs)}
        results.append(result)

        return results

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
(assert (!(exists ((e Ind))
    (and
        (hasActivity e {activity})
        (hasCase e {case_id})
    )
)))""",
    pattern_name="Occurs in Case"
)

HAND_OFF_PATTERN = Z3Pattern(
    args={},
    pattern_str="""
(assert (! (forall ((r1 Ind) (r2 Ind) (o1 Ind) (o2 Ind) (c Ind))
    (=> (and
            (next_subocc o1 o2 c)
            (participates r1 o1)
            (participates r2 o2)
            (distinct r1 r2)
        )
    (hand_off r1 r2 o1 o2 c))
)))""",
pattern_name="Hand-off"
)

PING_PONG_PATTERN = Z3Pattern(
    args={},
    pattern_str="""
(assert (! (forall ((c Ind))
    (=> (exists ((e1 Ind) (e2 Ind) (e3 Ind) (e4 Ind) (r1 Ind) (r2 Ind) (r3 Ind) (r4 Ind))
            (and
                (hand_off r1 r2 e1 e2 c)
                (hand_off r3 r4 e3 e4 c)
                (distinct e1 e3)
                (distinct e2 e4)
            ))
        (ping_pong c)
    )
)))""",
pattern_name='Ping-pong',
requires = [HAND_OFF_PATTERN]
)

# Query pattern to find all instances of ping-pong behavior
PING_PONG_QUERY_PATTERN = Z3Pattern(
    args={},
    pattern_str="""
(assert (! (not (exists ((c Ind))
    (ping_pong c))
)))""",
pattern_name='Ping-pong Query',
requires = [PING_PONG_PATTERN]
)