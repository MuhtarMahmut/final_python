# Data structures to represent Prolog terms.

# Every clause in a prolog program is encoded as a rule
# A fact is a rule with empty body.
class Rule:
    # head is a function
    # body is a *list* of functions (see RuleBody)
    def __init__(self, head, body):
        assert isinstance(body, RuleBody)
        self.head = head
        self.body = body

    def __str__(self):
        return str(self.head) + ' :- ' + str(self.body)

    def __eq__(self, other):
        if not isinstance(other, Rule):
            return NotImplemented
        return self.head == other.head and self.body == other.body

    def __hash__(self):
        return hash(self.head) + hash(self.body)


# Rule body is a list of functions (terms).
class RuleBody:
    def __init__(self, terms):
        assert isinstance(terms, list)
        self.terms = terms

    def separator(self):
        return ','

    def __str__(self):
        return '(' + (self.separator() + ' ').join(
            list(map(str, self.terms))) + ')'

    def __eq__(self, other):
        if not isinstance(other, RuleBody):
            return NotImplemented
        return self.terms == other.terms

    def __hash__(self):
        return hash(self.terms)


class Term:
    pass

# A function is, for example, father(rickard, ned).
class Function(Term):
    def __init__(self, relation, terms):
        self.relation = relation  # function name
        self.terms = terms  # funcion parameters

    def __str__(self):
        str_rel = str(self.relation)
        if not self.terms:
            # print (f'function {str_rel}')
            return str_rel
        # print (f'Function {str_rel}')
        return str_rel + '(' + ', '.join(map(str, self.terms)) + ')'

    def __eq__(self, other):
        if not isinstance(other, Function):
            return NotImplemented
        return self.relation == other.relation and self.terms == other.terms

    def __hash__(self):
        return hash(self.relation) + hash(self.terms)


# Prolog Variables, e.g. X, Y, ...
class Variable(Term):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        # print (f"Variable: {self.value} type {type(self.value)}")
        return self.value

    def is_anonym(self):
        return self.value[0] == '_'

    def __eq__(self, other):
        if not isinstance(other, Variable):
            return NotImplemented
        return self.value == other.value

    def __hash__(self):
        return hash(self.value)


class Constant(Term):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        if not isinstance(other, Constant):
            return NotImplemented
        return self.value == other.value

    def __hash__(self):
        return hash(self.value)


# Prolog Atoms, e.g. rickard, ned, ...
class Atom(Constant):
    def __init__(self, value):
        super().__init__(value)

    def __str__(self):
        # print (f"Atom: {self.value} type {type(self.value)}")
        return str(self.value)

    pass


# Prolog Numbers, e.g. 1, 2, ...
class Number(Constant):
    def __init__(self, value):
        super().__init__(int(value))

    def __str__(self):
        # print (f"Number: {self.value} type {type(self.value)}")
        return str(self.value)

    pass
