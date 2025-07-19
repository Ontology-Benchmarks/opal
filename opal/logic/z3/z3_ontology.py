from opal.logic.base.base_ontology import Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, ForAll, Exists, And, Or, Implies, Lt, Le, Gt, Ge
import re



# This dictionary maps logical operation names (as captured in the ontology JSON) to their corresponding Z3 functions
LOGICAL_OPS = {
    'ForAll': lambda var, body: ForAll(var, body),
    'Exists': lambda var, body: Exists(var, body),
    'And': And,
    'Or': Or,
    'Not': Not,
    'Implies': Implies,
    '=': lambda a, b: a == b, 
    '<': Lt,
    '<=': Le,
    '>': Gt,
    '>=': Ge,
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
    def from_json(cls, json, signature=None):
        """
        Loads the ontology from a JSON representation.
        
        Args:
            JSON (str): The JSON text representation of the ontology, or a path to the JSON file.
        
        Returns:
            self: The current instance of the ontology.
        """
        ontology = cls(signature=signature)
        
        # Check if supplied json arg is a file path or a string
        if json.endswith('.json'):
            with open(json, 'r') as f:
                json_str = f.read()
        else:
            json_str = json
            
        # Try parsing the json text
        try:
            ontology_json = json.loads(json_str)  # parse from string
        except json.JSONDecodeError as e:
            raise ValueError("Invalid JSON supplied") from e
        
        for i, axiom in enumerate(ontology_json['axioms']):
            # Parse the axiom expression
            a_name = f'ont_t_{i}_{axiom['name']}'
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
    
    def _infer_var_sorts(self, expr_str, var_ctx):
        '''Infers variable sorts from the expression string and updates the variable context.'''

        if '(' not in expr_str:
            return

        func_name, inner = expr_str.split('(', 1)
        if func_name not in self._predicate_map:
            return

        arg_str = inner.rsplit(')', 1)[0]
        args = self._split_arguments(arg_str)
        for i, arg in enumerate(args):
            var_name = arg.strip()
            if var_name in var_ctx:
                continue
            func = self._predicate_map[func_name]
            try:
                sig_sort = func.domain(i)
            except:
                continue  # Defensive check

            if sig_sort == RealSort():
                var_ctx[var_name] = Const(var_name, RealSort())
            else:
                var_ctx[var_name] = Const(var_name, Ind)
            
    def _parse_expression(self, expr_str, var_ctx=None):
        """
        Recursively parses a logical expression string into Z3 objects.
        
        Args:
            expr_str (str): The expression string to parse
            var_ctx (dict): Context mapping variable names to Z3 objects
            
        Returns:
            Z3 expression object
        """
        if var_ctx is None:
            var_ctx = {}

        expr_str = expr_str.strip()

        # Quantifiers
        if expr_str.startswith('ForAll') or expr_str.startswith('Exists'):
            quantifier, inner = expr_str.split('(', 1)
            args = inner.rsplit(')', 1)[0]
            var_part, body_part = args.split(',', 1)
            var_names = [v.strip() for v in var_part.strip("[] ").split(',')]

            # Infer sorts based on usage in body
            self._infer_var_sorts(body_part.strip(), var_ctx)

            vars = []
            for var_name in var_names:
                if var_name not in var_ctx:
                    var_ctx[var_name] = Const(var_name, Ind)  # default if not inferred
                vars.append(var_ctx[var_name])

            return LOGICAL_OPS[quantifier](vars, self._parse_expression(body_part.strip(), {**var_ctx}))
        
        # Binary comparison operators
        for op in ['>=', '<=', '==', '>', '<', '=']:
            pattern = fr'(.+?)\s*{re.escape(op)}\s*(.+)'
            match = re.fullmatch(pattern, expr_str)
            if match:
                lhs = self._parse_expression(match.group(1).strip(), var_ctx)
                rhs = self._parse_expression(match.group(2).strip(), var_ctx)
                return LOGICAL_OPS[op](lhs, rhs)

        # Function or logical operator with arguments
        if '(' in expr_str:
            func_name, inner = expr_str.split('(', 1)
            inner_args = [self._parse_expression(arg.strip(), var_ctx) for arg in self._split_arguments(inner.rsplit(')', 1)[0])]
            if func_name in LOGICAL_OPS:
                return LOGICAL_OPS[func_name](*inner_args)
            elif func_name in self._predicate_map:
                return self._predicate_map[func_name](*inner_args)
            else:
                func = Function(func_name, *([Ind] * len(inner_args)), BoolSort())
                self._predicate_map[func_name] = func
                return func(*inner_args)
            
        

        # Numeric constant
        try:
            return RealVal(float(expr_str))
        except ValueError:
            pass

        # Variable
        if expr_str in var_ctx:
            return var_ctx[expr_str]
        else:
            # Otherwise default to individual
            return Const(expr_str, Ind)

    def _split_arguments(self, s):
        """
        Safely splits function arguments, respecting nested parentheses.
        
        Args:
            s (str): The argument string to split
            
        Returns:
            list: List of argument strings
        """
        args, depth, current = [], 0, ''
        for c in s:
            if c == ',' and depth == 0:
                args.append(current)
                current = ''
            else:
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                current += c
        if current:
            args.append(current)
        return args
        
        
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
    
    



PSL_ONTOLOGY_JSON = {
    'axioms': [
    {
    'name' : 'type_partition',
    'description' : 'All objects are either activities, occurrences, objects, events, or transitions.',
    'axiom' : 'ForAll(x, Or(activity(x), activity_occurrence(x), object_(x), event(x), transition(x))'
    },
    {
    'name' : 'type_disjointness',
    'description' : 'activities, occurrences, objects, events, and transitions are different things.',
    'axiom' : '''ForAll(x, And(
    Implies(activity(x), Not(Or(activity_occurrence(x), object_(x), event(x), transition(x)))),
    Implies(activity_occurrence(x), Not(Or(object_(x), activity(x), event(x), transition(x)))),
    Implies(object_(x), Not(Or(activity_occurrence(x), activity(x), event(x), transition(x)))),
    Implies(event(x), Not(Or(activity_occurrence(x), activity(x), object_(x), transition(x)))),
    Implies(transition(x), Not(Or(activity_occurrence(x), activity(x), object_(x), event(x))))))'''
    },
    {
    'name' : 'begin_unique',
    'description' : 'Start points are unique.',
    'axiom' : 'ForAll([x, t1, t2], Implies(And(begin_of(x, t1), begin_of(x, t2)), t1 == t2))'
    },
    {
    'name' : 'ends_unique',
    'description' : 'End points are unique.',
    'axiom' : 'ForAll([x, t1, t2], Implies(And(end_of(x, t1), end_of(x, t2)), t1 == t2))'
    },
    {
    'name' : 'occurrence_bounds',
    'description' : 'Activity occurrence start points are before or equal to their end points.',
    'axiom' : '''ForAll(o, Implies(
        activity_occurrence(o),
        Exists([t1, t2], And(
            begin_of(o, t1),
            end_of(o, t2),
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
    'axiom' : '''ForAll([o, a1, a2], Implies(And(occurrence_of(o, a1), occurrence_of(o, a2)), a1 == a2))'''
    },
    {
    'name': 'occurrence_has_activity',
    'description': 'Every activity occurrence is the occurrence of some activity.',
    'axiom': '''ForAll(occ, Implies(
        activity_occurrence(occ),
        Exists(a, And(
            activity(a),
            occurrence_of(occ, a)))))'''
    },
    
    
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