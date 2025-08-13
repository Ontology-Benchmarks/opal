from opal.logic.base.base_literal import Literal
from z3 import Function, BoolSort, RealSort, Not, DeclareSort, RealVal, Const, Context
import re
import typing

def parse_smt2_declarations(smt2_str : str, env=None):
    '''
    A function to parse SMT-LIB2 declarations from a string

    Args:
        smt2_str (str): The SMT-LIB2 string to parse.
        env (dict, optional): The environment to use for parsing - this will be updated in the returned dictionary. If None, a new environment will be created.

    Returns:
        dict: The environment dictionary containing the parsed declarations as Z3 context, sorts, functions, and constants.
    '''
    if env is None:
        env = {}
        env['ctx'] = Context()
        env['sorts'] = {}
        env['functions'] = {}
        env['constants'] = {}

    sorts = env['sorts']
    functions = env['functions']
    constants = env['constants']
    ctx = env['ctx']

    # Match declare-sort
    for match in re.finditer(r'\(declare-sort\s+(\w+)\s+0\)', smt2_str):
        sort_name = match.group(1)
        if sort_name not in sorts:
            sorts[sort_name] = DeclareSort(sort_name, ctx=ctx)

    # Match declare-fun
    for match in re.finditer(r'\(declare-fun\s+(\w+)\s*\((.*?)\)\s*(\w+)\)', smt2_str):
        fname = match.group(1)
        arg_sorts = match.group(2).split()
        ret_sort = match.group(3)

        def get_sort(s):
            if s == 'Real':
                return RealSort(ctx)
            elif s == 'Bool':
                return BoolSort(ctx)
            else:
                return sorts[s]

        z3_args = [get_sort(s) for s in arg_sorts]
        z3_ret = get_sort(ret_sort)
        if fname not in functions:
            functions[fname] = Function(fname, *z3_args, z3_ret)

    # Match declare-const
    for match in re.finditer(r'\(declare-const\s+(\w+)\s+(\w+)\)', smt2_str):
        cname = match.group(1)
        csort = match.group(2)

        if csort == 'Real':
            z3_sort = RealSort(ctx)
        elif csort == 'Bool':
            z3_sort = BoolSort(ctx)
        elif csort in sorts:
            z3_sort = sorts[csort]
        else:
            print(f"Warning: Unknown sort '{csort}' for constant '{cname}'")
        if cname not in constants:
            constants[cname] = Const(cname, z3_sort)

    return {
        "ctx": ctx,
        "sorts": sorts,
        "functions": functions,
        "constants": constants
    }

# TODO: Structure the loading of the environments in a cleaner and more modular fashion

REFERENCE_TAXONOMY_PATH = '../../opal/logic/z3/ontologies/ref/reference_taxonomy.smt2'
with open(REFERENCE_TAXONOMY_PATH, 'r') as f:
    REFERENCE_TAXONOMY_ENV = parse_smt2_declarations(f.read())

PSL_CORE_PATH = '../../opal/logic/z3/ontologies/PSL/psl_core.smt2'
with open(PSL_CORE_PATH, 'r') as f:
    PSL_CORE_ENV = parse_smt2_declarations(f.read(), REFERENCE_TAXONOMY_ENV)

PSL_CORE_MAPPING_PATH = '../../opal/logic/z3/ontologies/PSL/psl_core_mapping.smt2'
with open(PSL_CORE_MAPPING_PATH, 'r') as f:
    PSL_CORE_MAPPING_ENV = parse_smt2_declarations(f.read(), PSL_CORE_ENV)