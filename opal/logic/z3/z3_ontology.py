from opal.logic.base.base_ontology import Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, ForAll, Exists, And, Or, Implies




LOGICAL_OPS = {
    'ForAll': lambda var, body: ForAll(var, body),
    'Exists': lambda var, body: Exists(var, body),
    'And': And,
    'Or': Or,
    'Not': Not,
    'Implies': Implies,
}

# define type for individuals
Ind = DeclareSort('Ind')

class Z3Ontology(Ontology):
    """
    A concrete subclass of Ontology that uses Z3 for logical reasoning.
    
    This class is intended to be used with Z3 expressions and provides methods
    for managing axioms, individuals, and the signature of the ontology.
    """

    def __init__(self, signature, individuals, ):
        """
        Initializes a new instance of the Z3Ontology class.
        """
        super().__init__()
    
    @classmethod
    def from_json(cls, json, signature=None, individuals=None):
        """
        Loads the ontology from a JSON representation.
        
        Args:
            JSON (str): The JSON text representation of the ontology, or a path to the JSON file.
        
        Returns:
            self: The current instance of the ontology.
        """
        ontology = cls(signature=signature, individuals=individuals)
        
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
            raise ValueError("Argument is neither a valid JSON string nor a valid file path") from e
        
        for axiom in ontology_json['axioms']:
            # Parse the axiom expression
            a_name = 'onto_' + axiom['name']
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
            name = f'gr_{predicate}({terms})_{i}'
            z3_literal = Z3Literal(predicate, terms, positive)
            ontology.add_literal(z3_literal, name=name)
            
        
        return ontology
        
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
            
        # Initialize predicate_map if not exists
        if not hasattr(self, '_predicate_map'):
            self._predicate_map = {}
            
        expr_str = expr_str.strip()
        if expr_str.startswith('ForAll') or expr_str.startswith('Exists'):
            quantifier, inner = expr_str.split('(', 1)
            args = inner.rsplit(')', 1)[0]
            var_part, body_part = args.split(',', 1)
            var_name = var_part.strip()
            var = var_ctx.get(var_name, Const(var_name, Ind))
            return LOGICAL_OPS[quantifier](var, self._parse_expression(body_part.strip(), {**var_ctx, var_name: var}))
        elif '(' in expr_str:
            func_name, inner = expr_str.split('(', 1)
            inner_args = [self._parse_expression(arg.strip(), var_ctx) for arg in self._split_arguments(inner.rsplit(')', 1)[0])]
            if func_name in LOGICAL_OPS:
                return LOGICAL_OPS[func_name](*inner_args)
            elif func_name in self._predicate_map:
                return self._predicate_map[func_name](*inner_args)
            else:
                # otherwise, create a new z3 function symbol
                func = Function(func_name, *([Ind] * len(inner_args)), BoolSort())
                self._predicate_map[func_name] = func
                return self._predicate_map[func_name](*inner_args)
        else:
            # It's a variable name
            return var_ctx.get(expr_str, Const(expr_str, Ind))

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
                axiom (Z3 expression): The axiom to add
            """
            self.axioms.append(axiom)
    
        
        
        
        PSL_ONTOLOGY_JSON = {
            'axioms': [
            {
            'name' : '',
            'description' : '',
            'axiom' : ''
            },
            
            ], 
            'ground': [
            {'predicate': 'transition', 'terms': ['start'], 'positive': True},
            {'predicate': 'transition', 'terms': ['complete'], 'positive': True},
            ]}