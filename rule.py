r"""
Module that applies rules of inference to boolean formulas

AUTHORS:

- Paul Scurek (2013-08-08): initial version
"""
#*****************************************************************************
#       Copyright (C) 2013 Paul Scurek <scurek86@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

import propcalc
import logicparser

def modus_ponens(premise1, premise2):
    r"""
    Apply modus ponens to the premises

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance

    - ``premise2`` -- string or :class:`BooleanFormula` instance

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying modus ponens to two formulas.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)->~d")
        sage: g = propcalc.formula("a&c")
        sage: rule.modus_ponens(f, g)
        '~d'

    ::

        sage: h = "~(d|c)->(p&~q)"
        sage: j = "~(d|c)"
        sage: rule.modus_ponens(h, j)
        'p&~q'

    ::

        sage: i = propcalc.formula("a")
        sage: k = "a->b"
        sage: rule.modus_ponens(i, k)
        'b'

    AUTHORS:

    - Paul Scurek (2013-08-08)
    """
    trees = []
    conditional_tree = []
    antecedent_tree = []
    antecedent = ''
    conclusion = ''
    # keeps track of whether the premises are of the right form
    valid_application = True

    try:
        trees = logicparser.get_trees(premise1, premise2)
    except SyntaxError:
        raise

    formula0 = logicparser.recover_formula(trees[0])
    formula1 = logicparser.recover_formula(trees[1])

    # determine which premise could be the conditional
    if len(formula0) > len(formula1):
        conditional_tree = trees[0]
        antecedent_tree = trees[1]
        antecedent = formula1
    else:
        conditional_tree = trees[1]
        antecedent_tree = trees[0]
        antecedent = formula0

    # determine if there really is a conditional
    if conditional_tree[0] != '->':
        valid_application = False
    # determine if premises are of the right form for modus ponens
    elif (isinstance(conditional_tree[1], str) and conditional_tree[1] == antecedent) or conditional_tree[1] == antecedent_tree:
        # case where the consequent is primitive
        if isinstance(conditional_tree[2], str):
            conclusion = conditional_tree[2]
        else:
            conclusion = logicparser.recover_formula(conditional_tree[2])
    else:
        valid_application = False

    if valid_application:
        return conclusion
    else:
        raise Exception("modus ponens cannot be applied to %s and %s." %(premise1, premise2))

def is_modus_ponens(premise1, premise2, conclusion):
    r"""
    Determine if conclusion follows from the premises by modus ponens.

    INPUT:

    - ``premise1`` -- a string or :class:`BooleanFormula` instance.

    - ``premise2`` -- a string or :class:`BooleanFormula` instance.

    - ``conclusion`` -- a string or :class:`BooleanFormula` instance.
      This is supposed to follow from the premises.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by modus ponens

    False - if ``conclusion`` does not follow from the premises by modus ponens

    EXAMPLES:

    This example illustrates checking if one formula follows from others by modus ponens.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(~a&b)->c")
        sage: g = propcalc.formula("~a&b")
        sage: r = propcalc.formula("c")
        sage: rule.is_modus_ponens(f, g, r)
        True

    ::

        sage: h = "~(p|q)->(c<->d)"
        sage: j = "~(p|q)"
        sage: r = "c<->d"
        sage: rule.is_modus_ponens(h, j, r)
        True

    ::

        sage: i = propcalc.formula("a->b")
        sage: k = propcalc.formula("~a")
        sage: r = propcalc.formula("b")
        sage: rule.is_modus_ponens(i, k, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-08)
    """
    conclusion_tree = ''
    actual_conclusion = ''

    try:
        # get parse tree of entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try to do modus ponens on the premises
        actual_conclusion = modus_ponens(premise1, premise2)
    except SyntaxError:
        raise
    # raised by modus_ponens when rule does not apply
    except Exception:
        pass

    # check if entered conclusion same as actual conclusion
    return actual_conclusion == logicparser.recover_formula(conclusion_tree)

def modus_tollens(premise1, premise2):
    r"""
    Apply modus tollens to the premises

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance

    - ``premise2`` -- string or :class:`BooleanFormula` instance

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying modus tollens to two formulas.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)->~d")
        sage: g = propcalc.formula("~~d")
        sage: rule.modus_tollens(f, g)
        '~(a&c)'

    ::

        sage: h = "~(d|c)->(p&~q)"
        sage: j = "~(p&~q)"
        sage: rule.modus_tollens(h, j)
        '~~(d|c)'

    ::

        sage: i = propcalc.formula("~b")
        sage: k = "a->b"
        sage: rule.modus_tollens(i, k)
        '~a'

    AUTHORS:

    - Paul Scurek (2013-08-08)
    """
    trees = []
    conditional_tree = []
    negated_consequent_tree = []
    conclusion = ''
    # keeps track of whether premises are of the right form for modus tollens
    valid_application = True

    try:
        trees = logicparser.get_trees(premise1, premise2)
    except SyntaxError:
        raise

    formula0 = logicparser.recover_formula(trees[0])
    formula1 = logicparser.recover_formula(trees[1])

    # determine which formula might be a conditional
    if len(formula0) > len(formula1):
        conditional_tree = trees[0]
        negated_consequent_tree = trees[1]
    else:
        conditional_tree = trees[1]
        negated_consequent_tree = trees[0]

    # determine if there really is a conditional and a negation
    if conditional_tree[0] != '->' or negated_consequent_tree[0] != '~':
        valid_application = False
    elif negated_consequent_tree == ['~', conditional_tree[2]]:
        conclusion = logicparser.recover_formula(['~', conditional_tree[1]])
    else:
        valid_application = False

    if valid_application:
        return conclusion
    else:
        raise Exception("modus tollens does not apply to %s and %s." % (premise1, premise2))

def is_modus_tollens(premise1, premise2, conclusion):
    r"""
    Determine if conclusion follows from the premises by modus tollens.

    INPUT:

    - ``premise1`` -- a string or :class:`BooleanFormula` instance.

    - ``premise2`` -- a string or :class:`BooleanFormula` instance.

    - ``conclusion`` -- a string or :class:`BooleanFormula` instance.
      This is supposed to follow from the premises.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by modus tollens

    False - if ``conclusion`` does not follow from the premises by modus tollens

    EXAMPLES:

    This example illustrates checking if one formula follows from others by modus tollens.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(~a&b)->c")
        sage: g = propcalc.formula("~c")
        sage: r = propcalc.formula("~(~a&b)")
        sage: rule.is_modus_tollens(f, g, r)
        True

    ::

        sage: h = "~(p|q)->(c<->d)"
        sage: j = "~(c<->d)"
        sage: r = "~~(p|q)"
        sage: rule.is_modus_tollens(h, j, r)
        True

    ::

        sage: i = propcalc.formula("a->b")
        sage: k = propcalc.formula("b")
        sage: r = propcalc.formula("a")
        sage: rule.is_modus_tollens(i, k, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-08)
    """
    conclusion_tree = []
    actual_conclusion = ''

    try:
        # get parse tree of entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try to do modus tollens on the premises
        actual_conclusion = modus_tollens(premise1, premise2)
    except SyntaxError:
        raise
    # raised by modus_tollens when rule does not apply
    except Exception:
        pass

    # check if entered conclusion is same as actual conclusion
    return actual_conclusion == logicparser.recover_formula(conclusion_tree)

def chain_implication(premise1, premise2):
    r"""
    Apply chain implication to the premises

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance

    - ``premise2`` -- string or :class:`BooleanFormula` instance

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying chain implication to two formulas.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)->~d")
        sage: g = propcalc.formula("~d->(b|d)")
        sage: rule.chain_implication(f, g)
        '(a&c)->(b|d)'

    ::

        sage: h = "~(d|c)->(p&~q)"
        sage: j = "(p&~q)->a"
        sage: rule.chain_implication(h, j)
        '~(d|c)->a'

    ::

        sage: i = propcalc.formula("b->c")
        sage: k = "a->b"
        sage: rule.chain_implication(i, k)
        'a->c'

    AUTHORS:

    - Paul Scurek (2013-08-10)
    """
    premise1_tree = []
    premise2_tree = []
    conclusion = ''
    # keeps track of whether premises are of the right form for rule
    valid_application = True

    try:
        premise1_tree, premise2_tree = logicparser.get_trees(premise1, premise2)
    except SyntaxError:
        raise

    # make sure both premises are conditionals
    if premise1_tree[0] != '->' or premise2_tree[0] != '->':
        valid_application = False
    elif premise1_tree[2] == premise2_tree[1]:
        conclusion = logicparser.recover_formula(['->', premise1_tree[1], premise2_tree[2]])
    elif premise2_tree[2] == premise1_tree[1]:
        conclusion = logicparser.recover_formula(['->', premise2_tree[1], premise1_tree[2]])
    else:
        valid_application = False

    if valid_application:
        return conclusion
    else:
        raise Exception("chain implication does not apply to %s and %s." % (premise1, premise2))

def is_chain_implication(premise1, premise2, conclusion):
    r"""
    Determine if conclusion follows from the premises by chain implication.

    INPUT:

    - ``premise1`` -- a string or :class:`BooleanFormula` instance.

    - ``premise2`` -- a string or :class:`BooleanFormula` instance.

    - ``conclusion`` -- a string or :class:`BooleanFormula` instance.
      This is supposed to follow from the premises.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by chain implication

    False - if ``conclusion`` does not follow from the premises by chain implication

    EXAMPLES:

    This example illustrates checking if one formula follows from others by chain implication.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(~a&b)->c")
        sage: g = propcalc.formula("c->~(d|a)")
        sage: r = propcalc.formula("(~a&b)->~(d|a)")
        sage: rule.is_chain_implication(f, g, r)
        True

    ::

        sage: h = "~(p|q)->(c<->d)"
        sage: j = "(c<->d)->~(~a->~b)"
        sage: r = "~(p|q)->~(~a->~b)"
        sage: rule.is_chain_implication(h, j, r)
        True

    ::

        sage: i = propcalc.formula("a->b")
        sage: k = propcalc.formula("b->c")
        sage: r = propcalc.formula("c")
        sage: rule.is_chain_implication(i, k, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-10)
    """
    conclusion_tree = []
    actual_conclusion = ''

    try:
        # get the parse tree of entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try applying chian implication to the premises
        actual_conclusion = chain_implication(premise1, premise2)
    except SyntaxError:
        raise
    #raised by chain_implication when rule does not apply to premises
    except Exception:
        pass

    # check to see if entered conclusion is same as actual conclusion
    return actual_conclusion == logicparser.recover_formula(conclusion_tree)

def dilemma(premise1, premise2, premise3):
    r"""
    Apply constructive dilemma to the premises

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance

    - ``premise2`` -- string or :class:`BooleanFormula` instance

    - ``premise3`` -- string or :class:`BooleanFormula` instance

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying constructive dilemma to two formulas.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)|~d")
        sage: g = propcalc.formula("~d->(b|d)")
        sage: r = propcalc.formula("(a&c)->(p&q)")
        sage: rule.dilemma(f, g, r)
        '(p&q)|(b|d)'

    ::

        sage: h = "~(d|c)|(p&~q)"
        sage: j = "(p&~q)->a"
        sage: r = "~(d|c)->c"
        sage: rule.dilemma(h, j, r)
        'c|a'

    ::

        sage: i = propcalc.formula("b|c")
        sage: k = "b->p"
        sage: r = propcalc.formula("c->q")
        sage: rule.dilemma(i, k, r)
        'p|q'

    AUTHORS:

    - Paul Scurek (2013-08-10)
    """
    trees = []
    disjunction_tree = []
    conditional_tree1 = []
    conditional_tree2 = []

    try:
        trees = logicparser.get_trees(premise1, premise2, premise3)
    except SyntaxError:
        raise

    for i in range(3):
        # determine if it is a disjunction
        if trees[i][0] == '|':
            disjunction_tree = trees[i]
            for tree in trees:
                # determine if it is a conditional
                if tree[0] == '->':
                    if tree[1] == trees[i][1]:
                        conditional_tree1 = tree
                    elif tree[1] == trees[i][2]:
                        conditional_tree2 = tree

    # make sure all of the trees got assigned
    if disjunction_tree and conditional_tree1 and conditional_tree2:
        #return the conclusion
        return logicparser.recover_formula(['|', conditional_tree1[2], conditional_tree2[2]])
    else:
        raise Exception("dilemma does not apply to %s, %s, and %s." % (premise1, premise2, premise3))

def is_dilemma(premise1, premise2, premise3, conclusion):
    r"""
    Determine if conclusion follows from the premises by dilemma.

    INPUT:

    - ``premise1`` -- a string or :class:`BooleanFormula` instance.

    - ``premise2`` -- a string or :class:`BooleanFormula` instance.

    - ``premise3`` -- a string or :class:`BooleanFormula` instance.

    - ``conclusion`` -- a string or :class:`BooleanFormula` instance.
      This is supposed to follow from the premises.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by dilemma

    False - if ``conclusion`` does not follow from the premises by dilemma

    EXAMPLES:

    This example illustrates checking if one formula follows from others by dilemma.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(~a&b)|c")
        sage: g = propcalc.formula("c->~(d|a)")
        sage: h = propcalc.formula("(~a&b)->~p")
        sage: r = propcalc.formula("~p|~(d|a)")
        sage: rule.is_dilemma(f, g, h, r)
        True

    ::

        sage: i = "~(p|q)|(c<->d)"
        sage: j = "(c<->d)->~(~a->~b)"
        sage: k = "~(p|q)->(p<->q)"
        sage: r = "(p<->q)|~(~a->~b)"
        sage: rule.is_dilemma(i, j, k, r)
        True

    ::

        sage: l = propcalc.formula("a|b")
        sage: m = propcalc.formula("b->c")
        sage: n = propcalc.formula("a->d")
        sage: r = propcalc.formula("c|d")
        sage: rule.is_dilemma(l, m, n, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-10)
    """
    conclusion_tree = []
    actual_conclusion = ''

    try:
        # get the parse tree of entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try applying dilemma to the premises
        actual_conclusion = dilemma(premise1, premise2, premise3)
    except SyntaxError:
        raise
    # raised by dillema() when rule does not apply
    except Exception:
        pass

    # check if entered conclusion is same as actual conclusion
    return actual_conclusion == logicparser.recover_formula(conclusion_tree)

def disjunction_elim(premise1, premise2):
    r"""
    Apply disjunction elimination rule to the premises

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance

    - ``premise2`` -- string or :class:`BooleanFormula` instance

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying disjunction elimination to two formulas.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)|~d")
        sage: g = propcalc.formula("~~d")
        sage: rule.disjunction_elim(f, g)
        'a&c'

    ::

        sage: h = "~(d|c)|(p&~q)"
        sage: j = "~(p&~q)"
        sage: rule.disjunction_elim(h, j)
        '~(d|c)'

    ::

        sage: i = propcalc.formula("~a")
        sage: k = "a|b"
        sage: rule.disjunction_elim(i, k)
        'b'

    AUTHORS:

    - Paul Scurek (2013-08-09)
    """
    trees = []
    disjunction_tree = []
    negated_disjunct_tree = []
    conclusion = ''
    # keeps track of whether premises are of the right form for disjunction elimination
    valid_application = True

    try:
        trees = logicparser.get_trees(premise1, premise2)
    except SyntaxError:
        raise

    formula0 = logicparser.recover_formula(trees[0])
    formula1 = logicparser.recover_formula(trees[1])

    # determine which premise might be the disjunction
    if len(formula0) > len(formula1):
        disjunction_tree = trees[0]
        negated_disjunct_tree = trees[1]
    else:
        disjunction_tree = trees[1]
        negated_disjunct_tree = trees[0]

    # make sure there really is a disjunction
    if disjunction_tree[0] != '|':
        valid_application = False
    elif negated_disjunct_tree == ['~', disjunction_tree[1]]:
        # case where the disjunct on the right of '|' is primitive
        if isinstance(disjunction_tree[2], str):
            conclusion = disjunction_tree[2]
        else:
            conclusion = logicparser.recover_formula(disjunction_tree[2])
    elif negated_disjunct_tree == ['~', disjunction_tree[2]]:
        # case where disjunct on the left side of '|' is primitive
        if isinstance(disjunction_tree[1], str):
            conclusion = disjunction_tree[1]
        else:
            conclusion = logicparser.recover_formula(disjunction_tree[1])
    else:
        valid_application = False

    if valid_application:
        return conclusion
    else:
        raise Exception("disjunction elimination does not apply to %s and %s." % (premise1, premise2))

def is_disjunction_elim(premise1, premise2, conclusion):
    r"""
    Determine if conclusion follows from the premises by disjunction elimination.

    INPUT:

    - ``premise1`` -- a string or :class:`BooleanFormula` instance.

    - ``premise2`` -- a string or :class:`BooleanFormula` instance.

    - ``conclusion`` -- a string or :class:`BooleanFormula` instance.
      This is supposed to follow from the premises.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by disjunction elimination

    False - if ``conclusion`` does not follow from the premises by disjunction elimination

    EXAMPLES:

    This example illustrates checking if one formula follows from others by disjunction elimination.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(~a&b)|c")
        sage: g = propcalc.formula("~c")
        sage: r = propcalc.formula("~a&b")
        sage: rule.is_disjunction_elim(f, g, r)
        True

    ::

        sage: h = "~(p|q)|(c<->d)"
        sage: j = "~(c<->d)"
        sage: r = "~(p|q)"
        sage: rule.is_disjunction_elim(h, j, r)
        True

    ::

        sage: i = propcalc.formula("a|b")
        sage: k = propcalc.formula("b")
        sage: r = propcalc.formula("a")
        sage: rule.is_disjunction_elim(i, k, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-09)
    """
    conclusion_tree = []
    actual_conclusion = ''

    try:
        # get parse tree of entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try to do disjunction elimination on the premises
        actual_conclusion = disjunction_elim(premise1, premise2)
    except SyntaxError:
        raise
    # raised by disjunction_elim when rule does not apply to premises
    except Exception:
        pass

    # determine if entered conclusion is same as actual conclusion and return answer
    return actual_conclusion == logicparser.recover_formula(conclusion_tree)

def disjunction_intro(premise1, statement, side = 'right'):
    r"""
    Add the statement to the premise by disjunction introduction

    INPUT:

    - ``premise1`` -- string or instance of :class:`BooleanFormula`.
      This is the statement that is being added to.

    - ``statement`` -- string of instance of "class"`BooleanFormula`.
      This is the statement that is being added

    - ``side`` -- (default: right) string. value is either 'right' or 'left'.
      This tells the function to which side of ``premise1`` it should add ``statement``.

    OUTPUT:

    The conclusion as a string.

    EXAMPLES:

    This example illustrates adding a statement to aother with disjunction introduction.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("a->b")
        sage: g = propcalc.formula("~c")
        sage: rule.disjunction_intro(f, g)
        '(a->b)|~c'

    ::

        sage: h = "p<->~q"
        sage: i = "p&r"
        sage: rule.disjunction_intro(h, i)
        '(p<->~q)|(p&r)'

    We can add the statement to the left instead of the right.

    ::

        sage: rule.disjunction_intro(h, i, 'left')
        '(p&r)|(p<->~q)'

    AUTHORS:

    - Paul Scurek (2013-08-09)
    """
    trees = []
    conclusion = ''
    premise1_tree = []
    statement_tree = []

    try:
        premise1_tree, statement_tree = logicparser.get_trees(premise1, statement)
    except SyntaxError:
        raise
    if not (side == 'right' or side == 'left'):
        raise ValueError("``side`` can only take values 'right' or 'left'")

    # check if premise1 is primitive or a negation
    if len(premise1_tree) < 3:
        premise1 = logicparser.recover_formula(premise1_tree)
    else:
        premise1 = '(' + logicparser.recover_formula(premise1_tree) + ')'

    # check if statement is primitive or a negation
    if len(statement_tree) < 3:
        statement = logicparser.recover_formula(statement_tree)
    else:
        statement = '(' + logicparser.recover_formula(statement_tree) + ')'

    if side == 'left':
        conclusion = statement + '|' + premise1
    else:
        conclusion = premise1 + '|' + statement

    return conclusion

def is_disjunction_intro(premise1, conclusion):
    r"""
    Determine if the conclusion follows from the premise by disjunction introduction

    INPUT:

    - ``premise1`` -- a string or instance of :class:`BooleanFormula`.

    - ``conclusion`` -- a string or instance of :class:`BooleanFormula`.
      This is supposed to follow from the premise.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from ``premise1`` by disjunction introduction

    False - if ``conclusion`` does not follow from ``premise1`` by disjunction introduction

    EXAMPLES:

    This example illustrates checking if a formula follows from another by disjunction introduction.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a->~b)")
        sage: g = propcalc.formula("(a->~b)|(d&e)")
        sage: rule.is_disjunction_intro(f, g)
        True

    ::

        sage: h = "~(p&q)"
        sage: i = "(p->~q)|~(p&q)"
        sage: rule.is_disjunction_intro(h, i)
        True

    ::

        sage: j = propcalc.formula("~(p&q)")
        sage: k = "~((p&q)|r)"
        sage: rule.is_disjunction_intro(j, k)
        False

    AUTHORS:

    - Paul Scurek (2013-08-09)
    """
    conclusion_tree = []
    premise1_tree = []
    # keeps track of whether premise and conclusion are of right form for rule
    valid_application = True

    try:
        premise1_tree, conclusion_tree = logicparser.get_trees(premise1, conclusion)
    except SyntaxError:
        raise

    # case where the premise is primitive
    if len(premise1_tree) == 1:
        premise1_tree = premise1_tree[0]

    # make sure coclusion is a disjunction
    if conclusion_tree[0] != '|':
        valid_application = False
    elif conclusion_tree == ['|', premise1_tree, conclusion_tree[2]] or conclusion_tree == ['|', conclusion_tree[1], premise1_tree]:
        # valid_application remains True
        pass
    else:
        valid_application = False

    return valid_application

def conjunction_elim(premise1, side):
    r"""
    Apply conjunction elimination rule to the premise

    INPUT:

    - ``premise1`` -- string or :class:`BooleanFormula` instance.

    - ``side`` -- a string. This determines which side of the
      conjunction to return.

    OUTPUT:

    The conclusion as a string

    EXAMPLES:

    This example illustrates applying conjunction elimination to a formula.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a&c)&~d")
        sage: rule.conjunction_elim(f, 'right')
        '~d'

    ::

        sage: g = "~(d|c)&(p&~q)"
        sage: rule.conjunction_elim(g, 'left')
        '~(d|c)'

    ::

        sage: h = "a&b"
        sage: rule.conjunction_elim(h, 'right')
        'b'

    AUTHORS:

    - Paul Scurek (2013-08-12)
    """
    conjunction_tree = []
    conclusion = ''
    # keeps track of whether premise is of the right form for rule
    valid_application = True

    try:
        conjunction_tree = logicparser.get_trees(premise1)[0]
    except SyntaxError:
        raise
    if side != 'right' and side != 'left':
        raise ValueError("side only takes the values 'right' and 'left'")

    # determine if the premise is a conjunction
    if conjunction_tree[0] != '&':
        valid_application = False
    elif side == 'right':
        # case where right side of premise is primitive
        if isinstance(conjunction_tree[2], str):
            conclusion = conjunction_tree[2]
        else:
            conclusion = logicparser.recover_formula(conjunction_tree[2])
    else:
        # case where left side of premise is primitive
        if isinstance(conjunction_tree[1], str):
            conclusion = conjunction_tree[1]
        else:
            conclusion = logicparser.recover_formula(conjunction_tree[1])

    if valid_application:
        return conclusion
    else:
        raise Exception("conjunction elimination does not apply to %s." % (premise1))

def is_conjunction_elim(premise1, conclusion):
    r"""
    Determine if the conclusion follows from the premise by conjunction elimination

    INPUT:

    - ``premise1`` -- a string or instance of :class:`BooleanFormula`.

    - ``conclusion`` -- a string or instance of :class:`BooleanFormula`.
      This is supposed to follow from the premise.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from ``premise1`` by conjunction elimination

    False - if ``conclusion`` does not follow from ``premise1`` by conjunction elimination

    EXAMPLES:

    This example illustrates checking if a formula follows from another by conjunction elimination.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a->~b)&(d&e)")
        sage: r = propcalc.formula("(a->~b)")
        sage: rule.is_conjunction_elim(f, r)
        True

    ::

        sage: g = "(p->~q)&~(p&q)"
        sage: r = "~(p&q)"
        sage: rule.is_conjunction_elim(g, r)
        True

    ::

        sage: h = "~((p&q)&r)"
        sage: r = "~r"
        sage: rule.is_disjunction_intro(h, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-12)
    """
    conclusion_tree = []
    actual_conclusion1 = ''
    actual_conclusion2 = ''

    try:
        # get the parse tree for entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try doing conjunction elim on the premise
        actual_conclusion1 = conjunction_elim(premise1, 'right')
        actual_conclusion2 = conjunction_elim(premise1, 'left')
    except SyntaxError:
        raise
    # raised by conjunction_elim when rule does not apply
    except Exception:
        pass

    conclusion = logicparser.recover_formula(conclusion_tree)

    # determine if entered conclusion is same as actual conclusion and return answer
    return actual_conclusion1 == conclusion or actual_conclusion2 == conclusion

def conjunction_intro(premise1, premise2):
    r"""
    conjoin the premises by conjunction introduction

    INPUT:

    - ``premise1`` -- string or instance of :class:`BooleanFormula`.
      This will be on the left of the conjunction.

    - ``premise2`` -- string of instance of "class"`BooleanFormula`.
      This will be on the right of the conjunction

    OUTPUT:

    The conclusion as a string in the form ``premise1`` & ``premise2``.

    EXAMPLES:

    This example illustrates two formulas with conjunction introduction.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("a->b")
        sage: g = propcalc.formula("~c")
        sage: rule.conjunction_intro(f, g)
        '(a->b)&~c'

    ::

        sage: h = "p<->~q"
        sage: i = "p&r"
        sage: rule.conjunction_intro(h, i)
        '(p<->~q)&(p&r)'

    We can conjoin the formulas in the opposite order by changing the order in which
    they are passed as arguments.

    ::

        sage: rule.conjunction_intro(i, h)
        '(p&r)&(p<->~q)'

    AUTHORS:

    - Paul Scurek (2013-08-12)
    """
    trees = []
    premise1_tree = []
    premise2_tree = []

    try:
        premise1_tree, premise2_tree = logicparser.get_trees(premise1, premise2)
    except SyntaxError:
        raise

    return logicparser.recover_formula(['&', premise1_tree, premise2_tree])

def is_conjunction_intro(premise1, premise2, conclusion):
    r"""
    Determine if the conclusion follows from the premises by conjunction introduction

    INPUT:

    - ``premise1`` -- a string or instance of :class:`BooleanFormula`.

    - ``premise2`` -- a string or instance of :class:`BooleanFormula`.

    - ``conclusion`` -- a string or instance of :class:`BooleanFormula`.
      This is supposed to follow from the premise.

    OUTPUT:

    A boolean value to be determined as follows:

    True - if ``conclusion`` follows from the premises by conjunction introduction

    False - if ``conclusion`` does not follow from premises by conjunction introduction

    EXAMPLES:

    This example illustrates checking if a formula follows from others by conjunction introduction.

    ::

        sage: import sage.logic.propcalc as propcalc
        sage: import sage.logic.rule as rule
        sage: f = propcalc.formula("(a->~b)")
        sage: g = propcalc.formula("(d&e)")
        sage: r = propcalc.formula("(a->~b)&(d&e)")
        sage: rule.is_conjunction_intro(f, g, r)
        True

    ::

        sage: h = "~(p&q)"
        sage: i = "p->~q"
        sage: r = "(p->~q)&~(p&q)"
        sage: rule.is_conjunction_intro(h, i, r)
        True

    ::

        sage: j = propcalc.formula("~(p&q)")
        sage: k = "r"
        sage: r = "~((p&q)&r)"
        sage: rule.is_conjunction_intro(j, k, r)
        False

    AUTHORS:

    - Paul Scurek (2013-08-12)
    """
    conclusion_tree = []
    actual_conclusion1 = ''
    actual_conclusion2 = ''

    try:
        # get the tree for the entered conclusion
        conclusion_tree = logicparser.get_trees(conclusion)[0]
        # try do apply conjunction_intro to the premises
        actual_conclusion1 = conjunction_intro(premise1, premise2)
        actual_conclusion2 = conjunction_intro(premise2, premise1)
    except SyntaxError:
        raise

    conclusion = logicparser.recover_formula(conclusion_tree)

    # check if entered conclusion is same as actual conclusion
    return actual_conclusion1 == conclusion or actual_conclusion2 == conclusion
