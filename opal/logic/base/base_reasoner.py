class Reasoner:
    """
    Base class for all reasoners.
    """
    def __init__(self):
        pass

    def load_ontology(self, ontology):
        
        raise NotImplementedError("This method should be implemented by subclasses.")

    def load_facts(self, facts):
        
        raise NotImplementedError("This method should be implemented by subclasses.")
    
    def query(self, query):
        
        raise NotImplementedError("This method should be implemented by subclasses.")