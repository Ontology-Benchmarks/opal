import collections
import typing
import abc

class Literal(metaclass=abc.ABCMeta):
    """An abstract class for representing single literals"""
    
    #  CONSTRUCTORS  ###################################################################################################
    
    def __init__(self, predicate: str, terms: typing.Iterable[str] = None, positive: bool = True):
        """Creates a new instance of ``Literal``.

        An example of a positive literal is ``country(austria)``, and a negative one is ``~locatedIn(germany, africa)``.
        The predicates that appear in these literals are ``country`` and ``locatedIn``, respectively, and the terms are
        ``austria`` in the former example and both ``germany`` and ``africa`` in the latter.

        Args:
            predicate (str): The predicate symbol that appears in the literal.
            terms (iterable[str], optional): The terms that appear in the literal in the order that they can be iterated
                over.
            positive (bool, optional): Indicates whether the literal is positive or negative, i.e., an atom or a negated
                atom. By default, this parameters is ``True``.

        Raises:
            TypeError: If ``terms``, given that it has been provided, is not iterable.
            ValueError: If ``predicate`` or any element in ``terms`` is the empty string.
        """
        # sanitize args
        predicate = str(predicate)
        if len(predicate) == 0:
            raise ValueError("The parameter <predicate> must not be the empty string!")
        if terms is not None:
            if not isinstance(terms, collections.Iterable):
                raise TypeError("The parameter <terms> has to be iterable!")
            terms = tuple(str(t) for t in terms)
            for t in terms:
                if len(t) == 0:
                    raise ValueError("None of the terms can be the empty string!")
        else:
            terms = tuple()
        positive = bool(positive)
        
        # define attributes
        self._positive = positive
        self._predicate = predicate
        self._terms = terms
        
    
    #  MAGIC FUNCTIONS  ################################################################################################
    
    def __eq__(self, other) -> bool:
        return isinstance(other, Literal) and str(other) == str(self)
    
    def __hash__(self) -> int:
        return hash(str(self))
    
    @abc.abstractmethod
    def __str__(self) -> str:
        '''
        Returns the string representation of the literal 
        according to the encoding languages syntax
        '''
    
    #  PROPERTIES  #####################################################################################################
    
    @property
    def positive(self) -> bool:
        """bool: Indicates whether the literal is a positive one."""
        return self._positive
    
    @property
    def predicate(self) -> str:
        """str: The predicate symbol that appears in the literal."""
        return self._predicate
    
    @property
    def terms(self) -> typing.Tuple[str]:
        """tuple: The terms that appear in the literal."""
        return self._terms
    
    #  STATIC METHODS  #####################################################################################################
    
    @staticmethod
    def from_string(string: str) -> typing.Optional['Literal']:
        """Creates a new instance of ``Literal`` from a string representation of the literal according to the encoding
        languages syntax.

        Args:
            string (str): The string representation of the literal.

        Returns:
            Literal: The new instance of ``Literal``.
        """
    


