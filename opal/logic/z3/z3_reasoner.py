from opal.logic.base.base_reasoner import Reasoner
from opal.logic.z3.z3_ontology import Z3Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Solver, parse_smt2_string, sat, unsat, Const, RealSort, BoolSort, IntSort, Context

class Z3Reasoner(Reasoner):
    """
    Reasoner implementation using Z3.
    This class allows loading ontologies, assertions, and facts,
    and performs reasoning tasks such as satisfiability checking and querying.
    It leverages the Z3 SMT solver for logical inference.
    It maintains an internal state with the Z3 context, sorts, functions, constants,
    assertions, and facts.
    """
    def __init__(self):
        super().__init__()
        self.ctx = None
        self.sorts = {}
        self.functions = {} # For function declarations
        self.constants = {} # For constant expressions
        self.assertions = []
        self.facts = []
        
    def _initialize_env(self, source_ctx, source_env=None):
        """
        Initializes the reasoner's context and declarations.
        """
        if self.ctx is None:
            self.ctx = source_ctx
            if source_env:
                self.sorts.update(source_env.get('sorts', {}))
                self.functions.update(source_env.get('functions', {}))
                self.constants.update(source_env.get('constants', {}))

    def load_ontology(self, ontology : Z3Ontology):
        """
        Load the ontology into the Z3 environment.
        
        Args:
            ontology (Z3Ontology object)
            """

        # firstly establish environment to get ctx, sorts, functions, constants
        env = ontology.env
        self._initialize_env(source_ctx=env['ctx'], source_env=env)
        
        # check if ontology has axioms, then load them
        if hasattr(ontology, "axioms"):
            self.load_assertions(ontology.axioms)

        # check if ontology has ground facts, then load them
        if hasattr(ontology, "literals"):
            self.load_facts(ontology.literals)

    def load_assertions(self, assertions):
        
        if self.ctx is None:
            raise RuntimeError("Context must be initialized before loading assertions.")
        
        for assertion in assertions:
            name, expr = assertion['name'], assertion['expr']
            print(f"Loading assertion: {name} : {expr}")
            parsed_expr = parse_smt2_string(expr, ctx=self.ctx, sorts=self.sorts, decls=self.decls)[0]
            self.assertions.append((name, parsed_expr))

    def load_facts(self, facts):
        
        if self.ctx is None:
            raise RuntimeError("Context must be initialized before loading facts.")
        
        for fact in facts:
            name, literal_obj = next(iter(fact.items()))
            expr = literal_obj.z3_expr

            # If the expression's context differs from the reasoner's context, translate it.
            final_expr = expr.translate(self.ctx) if expr.ctx != self.ctx else expr
            self.facts.append((name, final_expr))
            
            
    def load_data_declarations(self, data_env):
        """
        Pre-registers all constants from the mapped data environment.
        This version correctly handles the 'Ind' sort and built-in sorts.
        """
        if self.ctx is None:
            raise RuntimeError("Context must be initialized before loading data declarations.")

        constants_from_data = data_env.get('constants', {})
        print(f"Pre-registering {len(constants_from_data)} constants from data environment...")

        for name, const_obj in constants_from_data.items():
            sort = const_obj.sort()
            if name not in self.constants:
                # Create the constant in the new context and add its declaration.
                new_const = Const(name, sort)
                self.constants[name] = new_const

    def query(self, query):
        
        # firstly do a check
        solver = self.check()

        # if no model can be constructed, do not attempt to query
        if solver.check() == unsat:
            raise ValueError("No model can be constructed from the given facts and assertions.")
        
        if isinstance(query, list):
            for q in query:
                print(f"Adding query: {q['name']} : {q['expr']}")
                expr = parse_smt2_string(q['expr'], ctx=self.ctx, sorts=self.sorts, decls=self.decls)[0]
                solver.assert_and_track(expr, q['name'])
        else:
            expr = parse_smt2_string(query['expr'], ctx=self.ctx, sorts=self.sorts, decls=self.decls)[0]
            solver.assert_and_track(expr, query['name'])

        # check satisfiability with query added
        solver.check()
        
        return solver


    def check(self):
        """
        Check the satisfiability of the current set of assertions and facts.

        """

        if self.ctx is None:
            return Solver()
        solver = Solver(ctx=self.ctx)
        # set model generation options
        solver.set(unsat_core=True)
        
        for name, expr in self.assertions:
            solver.assert_and_track(expr, name)
        for name, expr in self.facts:
            solver.assert_and_track(expr, name)
    
        solver.check()
        # If satisfiable, store the model
        if solver.check() == sat:
            self.model = solver.model()

        return solver
    
    
    def get_model(self):
        """
        Get the model from the last satisfiability check.
        
        Returns:
            Z3 model object if satisfiable, else None.
        """
        if hasattr(self, 'model'):
            return self.model
        else:
            print("No model available. Please run a satisfiability check first.")
            return None
        
    def _get_relation_instances(self, relation_name):
        """
        Helper function to find all unique tuples for a given n-ary relation.
        
        Args:
            relation_name (str): Name of the relation.

        Returns:
            list: A list of unique tuples, where each tuple represents an instance.
                e.g., [('e1', 'c1'), ('e2', 'c1')]
        """
        if relation_name not in self.decls:
            raise ValueError(f"Relation '{relation_name}' not found in declared functions.")

        func = self.decls[relation_name]
        arity = func.arity()
        if arity < 1:
            raise ValueError(f"'{relation_name}' is a constant, not a relation.")

        relevant_tuples = set()
        # This logic is based on your _get_class_instances implementation,
        # assuming your facts are custom objects.
        for name, expr in self.facts:
            # Check if the fact is for the correct relation
            if expr.decl() == func:
                relevant_tuples.add(tuple(str(c) for c in expr.children()))

        return list(relevant_tuples)

    def add_relation_closure_axiom(self, relation_name):
        """
        Adds a domain closure axiom for an n-ary relation.
        """
        true_tuples = self._get_relation_instances(relation_name)
        
        if not true_tuples:
            print(f"No instances found for relation {relation_name}. Skipping closure.")
            return

        arity = len(true_tuples[0])
        # Generate variable names like ['v0', 'v1', ...]
        var_names = [f'v{i}' for i in range(arity)]
        # Generate quantified variable string like '((v0 Ind) (v1 Ind))'
        quant_vars_str = ' '.join([f'({v} Ind)' for v in var_names])
        
        # Build the (and (= v0 val0) (= v1 val1)...) clauses for each tuple
        eq_terms = []
        for tpl in true_tuples:
            pair_clauses = [f'(= {var_names[i]} {tpl[i]})' for i in range(arity)]
            eq_terms.append(f"(and {' '.join(pair_clauses)})")
        
        disj_str = f"(or {' '.join(eq_terms)})"
        axiom_name = f"DomainClosure_{relation_name}"
        
        # Build the final axiom string
        relation_call = f"({relation_name} {' '.join(var_names)})"
        dc_axiom_str = f"(assert (forall ({quant_vars_str}) (= {relation_call} {disj_str})))"
        
        print(f"Adding domain closure axiom for relation {relation_name}")
        parsed_expr = parse_smt2_string(dc_axiom_str, ctx=self.ctx, sorts=self.sorts, decls=self.decls)[0]
        self.assertions.append((axiom_name, parsed_expr))

    def add_unique_name_axioms(self, class_name):
        """
        Add unique name axioms to the reasoner for all constants belonging to the given class.
        """
        relevant_inds = self._get_relation_instances(class_name)
        relevant_inds = [ind[0] for ind in relevant_inds if len(ind) == 1]  # Get only unary instances
        if not relevant_inds:
            print(f"No individuals found for class {class_name}. Skipping unique name axioms.")
            return None
        # The 'distinct' SMT-LIB function requires at least two arguments.
        if len(relevant_inds) < 2:
            print(f"Fewer than two individuals for class '{class_name}', skipping unique name axiom.")
            return
        
        axiom_name = f"UniqueNames_{class_name}"
        distinct_str = f"(assert (distinct {' '.join(relevant_inds)}))"
        parsed_expr = parse_smt2_string(distinct_str, ctx=self.ctx, sorts=self.sorts, decls=self.decls)[0]
        self.assertions.append((axiom_name, parsed_expr))
    
    @property
    def decls(self):
        # A helper property to provide a unified dictionary for the SMT parser
        # It correctly gets declarations for both functions and constants
        fn_decls = self.functions
        const_decls = {name: const.decl() for name, const in self.constants.items()}
        return {**fn_decls, **const_decls}