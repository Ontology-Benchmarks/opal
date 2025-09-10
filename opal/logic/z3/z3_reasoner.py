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


    def load_facts(self, facts):
        for fact in facts:
            name, expr = next(iter(fact.items()))
            if isinstance(expr, Z3Literal):
                self.facts.append(fact)
            else:
                raise TypeError("Expected Z3Literal instances in facts.")

    def query(self, query):
        
        # firstly do a check
        solver = self.check()

        # if no model can be constructed, do not attempt to query
        if solver.check() == unsat:
            # TODO: raise appropriate error
            return None

        # add the query to the solver
        solver.assert_and_track(query['expr'], query['name'])
        
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

        # add assertions
        for assertion in self.assertions:
            expr = parse_smt2_string(assertion['expr'], ctx=ctx, sorts=self.sorts, decls=self.decls)[0]
            solver.assert_and_track(expr, assertion['name'])

        # add facts
        for fact in self.facts:
            name, expr = next(iter(fact.items()))
            expr = expr.z3_expr
            solver.assert_and_track(expr, name)

        solver.check()

        return solver
    

    @property
    def decls(self):
        return self.functions | self.constants