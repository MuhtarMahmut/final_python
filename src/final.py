from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random


class Not_unifiable(Exception):
    pass


'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''


class Interpreter:
    def __init__(self):
        pass

    '''
    Example
    occurs_check (v, t) where v is of type Variable, t is of type Term.
    occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
    Please see the lecture note Control in Prolog to revisit the concept of
    occurs-check.
    '''

    def occurs_check(self, v: Variable, t: Term) -> bool:
        if isinstance(t, Variable):
            return v == t
        elif isinstance(t, Function):
            for t in t.terms:
                if self.occurs_check(v, t):
                    return True
            return False
        return False

    '''
    Problem 1
    variables_of_term (t) where t is of type Term.
    variables_of_clause (c) where c is of type Rule.

    The function should return the Variables contained in a term or a rule
    using Python set.

    The result must be saved in a Python set. The type of each element (a Prolog Variable)
    in the set is Variable.
    '''

    def variables_of_term(self, t: Term) -> set:
        set1 = set() # new empty set1
        set2 = set() # new empty set2

        if isinstance(t, Variable):  # if the given arg t is an instance of Variable class
            set1.add(t) # add the given arg to the set1

        elif isinstance(t, Function):  # if the given arg t is not an instance of Variable class but the instance of Function class

            for t in t.terms:  # to iterate all terms one by one

                if isinstance(t, Variable):
                    set2.add(t)
                elif isinstance(t, Function):
                    set1 = self.variables_of_term(t) # if term is an instance of Function class, then we reset the set1

                self.variables_of_term(t) # method recursion to rerun the method for same arg t

        return set1.union(set2)  # To return combination of set1 & set2


    def variables_of_clause(self, c: Rule) -> set:
        set1 = set()  # new empty set1
        set2 = set()  # new empty set2
        list1 = c.body

        for each in c.head.terms:  # access the list of terms (each element of list)
            if isinstance(each, Variable):  # to find the once that are the instance of Variable class
                set1.add(each)

        for b in list1.terms:
            if isinstance(b, Variable):
                set2.add(b)

        return set1.union(set2)  # To return combination of set1 & set2

    '''
    Problem 2
    substitute_in_term (s, t) where s is of type dictionary and t is of type Term
    substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

    The value of type dict should be a Python dictionary whose keys are of type Variable
    and values are of type Term. It is a map from variables to terms.

    The function should return t_ obtained by applying substitution s to t.

    Please use Python dictionary to represent a subsititution map.
    '''

    def substitute_in_term(self, s: dict, t: Term) -> Term:
        result = set()  # to return the final values as a set (avoids dup)
        if isinstance(t, Function):
            new_terms = []
            for term in t.terms:
                new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)

            result = Function(t.relation, new_terms)
        else:
            if t in s.keys():  # to see if the term in exist in the dictionary's keys
                result = s.get(t)
            else: # if it's not included in
                result = t

        return result

    def substitute_in_clause(self, s: dict, c: Rule) -> Rule:
        set1 = set()
        list1 = []

        if isinstance(c.head, Function): # check if Rule.head is an instance of Function

            new_terms = [] # new empty list (for now)

            for term in c.head.terms:
                new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)

            set1 = Function(c.head.relation, new_terms) # readjust set1

        elif isinstance(c.head, Variable):
            set1 = Function(c.head.relation, s.get(c.head))

        if isinstance(c.body, Function):

            new_terms = []
            for term in c.body.terms:
                new_terms.append(s.get(term)) if term in s.keys() else new_terms.append(term)

            list1 = Function(c.body.relation, new_terms)

        elif isinstance(c.body.terms, Variable):
            list1 = Function(c.body.relation, s.get(c.body))

        result = None

        if not list1:
            result = Rule(set1, c.body)
        else:
            result = Rule(set1, RuleBody(list1))

        return result

    '''
    Problem 3
    unify (t1, t2) where t1 is of type term and t2 is of type Term.
    The function should return a substitution map of type dict,
    which is a unifier of the given terms. You may find the pseudocode
    of unify in the lecture note Control in Prolog useful.

    The function should raise the exception raise Not_unfifiable (),
    if the given terms are not unifiable.

    Please use Python dictionary to represent a subsititution map.
    '''

    def unify(self, t1: Term, t2: Term) -> dict:
        def unification(t1: Term, t2: Term, dictionary1: dict):
            st1 = self.substitute_in_term(dictionary1, t1)
            st2 = self.substitute_in_term(dictionary1, t2)
            if isinstance(st1, Variable) and (not self.occurs_check(st1, st2)):
                for each in dictionary1.keys():
                    dictionary1[each] = self.substitute_in_term({st1: st2}, dictionary1[each])
                dictionary1[st1] = st2
                return dictionary1
            elif isinstance(st2, Variable) and not self.occurs_check(st2, st1):
                for each in dictionary1.keys():
                    dictionary1[each] = self.substitute_in_term({st2: st1}, dictionary1[each])
                dictionary1[st2] = st1
                return dictionary1
            elif st1 == st2:
                return dictionary1
            elif isinstance(st1, Function) and isinstance(st2, Function):
                if len(st1.terms) != len(st2.terms):
                    raise Not_unifiable()
                else:
                    for tx, ty in zip(st1.terms, st2.terms):
                        res = unification(tx, ty, dictionary1)
                    return res

            else:
                raise Not_unifiable()

        return unification(t1, t2, {})


    fresh_counter = 0

    def fresh(self) -> Variable:
        self.fresh_counter += 1
        return Variable("_G" + str(self.fresh_counter))

    def freshen(self, c: Rule) -> Rule:
        c_vars = self.variables_of_clause(c)
        theta = {}
        for c_var in c_vars:
            theta[c_var] = self.fresh()

        return self.substitute_in_clause(theta, c)

    '''
    Problem 4
    Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
    a nondeterministic Prolog interpreter.

    nondet_query (program, goal) where
        the first argument is a program which is a list of Rules.
        the second argument is a goal which is a list of Terms.

    The function returns a list of Terms (results), which is an instance of the original goal and is
    a logical consequence of the program. See the tests cases (in src/main.py) as examples.
    '''

    def nondet_query(self, program: List[Rule], pgoal: List[Term]) -> List[Term]:
        result = []
        while True:
            result = pgoal
            temp = result

            while len(temp) >= 0:
                selection = random.randint(0, len(result))
                rand_rule = random.randint(0, len(program))
                rand_rule = self.freshen(rand_rule)

                try:
                    sig = self.unify(selection, rand_rule.head)
                except:
                    break

                temp.remove(selection)

                for term in rand_rule.body.terms:
                    temp.append(term)

                dictionary1 = {}
                for term in temp:
                    dictionary1[term] = self.substitute_in_term(sig, term)
                temp = dictionary1

                dictionary2 = {}
                for term in result:
                    dictionary2[term] = self.substitute_in_term(sig, term)
                result = dictionary2

                if temp: # skip that iteration
                    continue
                else:
                    break # exit the loop
        return result

    '''
    Challenge Problem

    det_query (program, goal) where
        the first argument is a program which is a list of Rules.
        the second argument is a goal which is a list of Terms.

    The function returns a list of term lists (results). Each of these results is
    an instance of the original goal and is a logical consequence of the program.
    If the given goal is not a logical consequence of the program, then the result
    is an empty list. See the test cases (in src/main.py) as examples.
    '''

    def det_query(self, program: List[Rule], pgoal: List[Term]) -> List[List[Term]]:
        return [pgoal]
