from opal.logic.base.base_reasoner import Reasoner
from opal.logic.z3.z3_ontology import Z3Ontology
from opal.logic.z3.z3_literal import Z3Literal
from z3 import Solver, parse_smt2_string, sat, unsat

class Z3Reasoner(Reasoner):
    """
    Reasoner implementation using Z3.
    """
    def __init__(self):
        super().__init__()
        self.ctx = None
        self.sorts = None
        self.functions = None
        self.constants = None
        self.assertions = []
        self.facts = []

    def load_ontology(self, ontology : Z3Ontology):
        """
        Load the ontology into the Z3 environment.
        
        Args:
            ontology (Z3Ontology object)
            """

        # firstly establish environment to get ctx, sorts, functions, constants
        env = ontology.env
        if self.ctx is None:
            self.ctx = env['ctx']
        if self.sorts is None:
            self.sorts = env['sorts']
        if self.functions is None:
            self.functions = env['functions']
        if self.constants is None:
            self.constants = env['constants']

        # check if ontology has axioms, then load them
        if hasattr(ontology, "axioms"):
            for axiom in ontology.axioms:
                self.assertions.append(axiom)

        # check if ontology has ground facts, then load them
        if hasattr(ontology, "literals"):
            for literal in ontology.literals:
                self.facts.append(literal)

        self.ctx = ontology._env['ctx']

    def load_assertions(self, assertions):
        for assertion in assertions:
            _, expr = next(iter(assertion.items()))
            if isinstance(expr, str):
                self.assertions.append(assertion)
            else:
                raise TypeError("Expected string expressions in assertions.")

    def load_facts(self, facts):
        for fact in facts:
            _, expr = next(iter(fact.items()))
            if isinstance(expr, Z3Literal):
                self.facts.append(fact)
            else:
                raise TypeError("Expected Z3Literal instances in facts.")

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
        pass
        # check if there are any facts loaded, and use the existing ctx if so.
        if self.facts:
            fact = self.facts[0]
            _, expr = next(iter(fact.items()))
            ctx = expr.z3_expr.ctx

        # init the solver
        solver = Solver(ctx=ctx)
        solver.set(unsat_core=True)
        solver.set(completion=True)
        
        names = set()
        # add assertions
        for assertion in self.assertions:
            # check for duplicate names/assertions
            name = assertion['name']
            if name in names:
                raise ValueError(f"Duplicate assertion name: {name}")
            names.add(name)
            
            expr = parse_smt2_string(assertion['expr'], ctx=ctx, sorts=self.sorts, decls=self.decls)[0]
            solver.assert_and_track(expr, assertion['name'])

        # add facts
        for fact in self.facts:
            name, expr = next(iter(fact.items()))
            expr = expr.z3_expr
            solver.assert_and_track(expr, name)

        solver.check()

        return solver
    
    def add_domain_closure_axioms(self, class_name):
        """
        Add domain closure axioms to the reasoner for the specified class.
        Args:
            class_name (str): Name of the class to include in the domain closure axioms.
        """
        
        if class_name not in self.functions:
            raise ValueError(f"Class {class_name} not found in functions.")
        else:
            func = self.functions[class_name]
            if func.arity() != 1:
                raise ValueError(f"Function {class_name} is not unary.")
            # first obtain list of literals for this class
            relevant_literals = []
            for literal in self.facts:
                _, expr = next(iter(literal.items()))
                if expr.predicate == class_name and expr.positive:
                    relevant_literals.append(expr.terms[0])
            if not relevant_literals:
                return
            
            # build the disjunction expression string
            axiom_name = f"DomainClosure_{class_name}"
            eq_terms = [f"(= x {term})" for term in relevant_literals]
            disj_str = f"(or {' '.join(eq_terms)})"
            dc_axiom_str = f"(assert (forall ((x Ind)) (=> ({class_name} x) {disj_str})))"
            print(f"Adding domain closure axiom for class {class_name}")
            self.assertions.append({'name' : axiom_name, 'expr' : dc_axiom_str})

    @property
    def decls(self):
        return self.functions | self.constants