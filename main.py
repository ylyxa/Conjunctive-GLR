import re
from collections import defaultdict
from enum import Enum
from copy import deepcopy
import argparse
from time import time
import networkx as nx
from itertools import count
import matplotlib.pyplot as plt
import semantic



class Terminal:
    def __init__(self, s):
        self.str = s

    def __hash__(self):
        return hash(self.str)

    def __eq__(self, other):
        if isinstance(other, str):
            return self.str == other
        if not isinstance(other, Terminal):
            return NotImplemented
        return self.str == other.str

    def __str__(self):
        return self.str

    @classmethod
    def endsymbol(cls):
        return Terminal('$')


class Nonterminal:
    def __init__(self, s):
        self.str = s

    def __eq__(self, other):
        if isinstance(other, str):
            return self.str == other
        if not isinstance(other, Nonterminal):
            return NotImplemented
        return self.str == other.str

    def __hash__(self):
        return hash(self.str)

    def __str__(self):
        return self.str

    @classmethod
    def generate_with_regex_check(cls, s):
        NONTERM_REGEX = r'[A-Z][a-zA-Z0-9]*'
        if re.match(NONTERM_REGEX, s):
            return Nonterminal(s)
        else:
            raise Exception(f'Invalid symbol in rule: {s}')


def generate_symbol(s: str, check=False):
    TERM_REGEX = r'[a-z][a-zA-Z0-9]*'
    NONTERM_REGEX = r'[A-Z][a-zA-Z0-9]*'
    CONJUNCT_REGEX = r'C_[0-9]*'
    if re.match(TERM_REGEX, s):
        return Terminal(s)
    elif re.match(NONTERM_REGEX, s) or re.match(CONJUNCT_REGEX, s):
        return Nonterminal(s)
    else:
        raise Exception(f'Invalid symbol in rule: {s}')


class Rule:
    NONTERM_REGEX = r'[A-Z][a-zA-Z0-9]*'
    def __init__(self, s: str, check_lhs=True):
        self.s = s
        SPLIT_OPERATOR = '|'
        ASSIGN_OPERATOR = '::='
        r, semantic = s.split(SPLIT_OPERATOR)
        lhs_rhs = r.split(ASSIGN_OPERATOR)
        rhs_as_strings = lhs_rhs[1].lstrip().split(' ')
        self.lhs = Nonterminal.generate_with_regex_check(lhs_rhs[0].rstrip()) if check_lhs else Nonterminal(lhs_rhs[0].rstrip())
        self.rhs = list(map(generate_symbol, rhs_as_strings))
        self.semantic = semantic

    def __hash__(self):
        return hash((self.lhs, tuple(self.rhs)))

    def __eq__(self, other):
        if not isinstance(other, Rule):
            return NotImplemented
        return self.lhs == other.lhs and self.rhs == other.rhs

    def __str__(self):
        return self.s

    @classmethod
    def augmented(cls):
        return Rule('S\' ::= S|pass_through')


class Item:
    def __init__(self, rule: Rule, i: int):
        if i > len(rule.rhs):
            raise Exception('Out of bounds for item!')
        self.rule = rule
        self.i = i

    def is_final(self):
        return self.i == len(self.rule.rhs)

    def next_is_final(self):
        return self.i + 1 == len(self.rule.rhs)

    def locus(self):
        return None if self.is_final() else self.rule.rhs[self.i]

    def next_locus(self):
        return None if self.next_is_final() else self.rule.rhs[self.i + 1]

    def __hash__(self):
        return hash((self.rule, self.i))

    def __eq__(self, other):
        if not isinstance(other, Item):
            return NotImplemented
        return self.rule == other.rule and self.i == other.i


class State:
    def __init__(self, items: set):
        self.items = items

    def __hash__(self):
        return hash(self.items)

    def __eq__(self, other):
        if not isinstance(other, State):
            return NotImplemented
        return self.items == other.items


class Grammar:
    class Actions(Enum):
        SHIFT = 0
        REDUCE = 1
        ACCEPT = 2
        ERROR = 3

    def __init__(self, s: str):
        counter = count()
        rules_as_strs = s.split('\n')
        self.rules = []
        self.conjs = defaultdict(set)
        for i, rule in enumerate(rules_as_strs):
            if '&' not in rule:
                self.rules.append(Rule(rule))
            else:
                SPLIT_OPERATOR = '|'
                ASSIGN_OPERATOR = '::='
                r, semantic = rule.split(SPLIT_OPERATOR)
                r = r.rstrip()
                semantic = semantic.lstrip()
                lhs, rhs = r.split(ASSIGN_OPERATOR)
                rhs_split = rhs.split('&')
                bottom_rules = []
                top_rules = []
                conjs = []
                for conj in rhs_split:
                    nonterm = f'C_{next(counter)}'
                    new_rule = f'{nonterm} ::= {conj.rstrip().lstrip()}|{semantic}'
                    new_higher_rule = f'{lhs} ::= {nonterm}|pass_through'
                    bottom_rules.append(Rule(new_rule, check_lhs=False))
                    top_rules.append(new_higher_rule)
                    conjs.append(Nonterminal(nonterm))
                for rule in bottom_rules:
                    self.rules.append(rule)
                for rule in top_rules:
                    self.rules.append((Rule(rule, check_lhs=False)))
                for conj in conjs:
                    self.conjs[conj] = conjs
        self.terminals = {Terminal.endsymbol()}
        self.nonterminals = set()
        for rule in self.rules:
            self.nonterminals.add(rule.lhs)
            for symbol in rule.rhs:
                if isinstance(symbol, Terminal):
                    self.terminals.add(symbol)
        self.rules.append(Rule.augmented())
        self.items = set()
        self.first = defaultdict(set)
        self.follow = defaultdict(set)
        self.states = set()
        self.states_list = []
        self.action = defaultdict(None)
        self.goto = defaultdict(None)
        self.generate_items()
        self.generate_first()
        self.generate_follow()
        self.generate_i0()
        self.generate_tables()

    def generate_first(self):
        changed = True
        while changed:
            changed = False
            for i in self.rules:
                first_symbol = i.rhs[0]
                if isinstance(first_symbol, Terminal) and first_symbol not in self.first[i.lhs]:
                    changed = True
                    self.first[i.lhs].add(first_symbol)
                elif isinstance(first_symbol, Nonterminal) and not self.first[first_symbol].issubset(self.first[i.lhs]):
                    changed = True
                    self.first[i.lhs].update(self.first[first_symbol])

    def generate_follow(self):
        self.follow[Rule.augmented().lhs].add(Terminal.endsymbol())
        changed = True
        while changed:
            changed = False
            for item in self.items:
                locus = item.locus()
                if isinstance(locus, Nonterminal):
                    next_locus = item.next_locus()
                    if isinstance(next_locus, Terminal) and next_locus not in self.follow[locus]:
                        changed = True
                        self.follow[locus].add(next_locus)
                    elif isinstance(next_locus, Nonterminal) and not self.first[next_locus].issubset(
                            self.follow[locus]):
                        changed = True
                        self.follow[locus].update(self.first[next_locus])
                    elif next_locus is None and not self.follow[item.rule.lhs].issubset(self.follow[locus]):
                        changed = True
                        self.follow[locus].update(self.follow[item.rule.lhs])

    def generate_items(self):
        for rule in self.rules:
            for i in range(len(rule.rhs) + 1):
                self.items.add(Item(rule, i))

    def closure(self, state: State):
        changed = True
        while changed:
            changed = False
            items = state.items
            for item in state.items.copy():
                locus = item.locus()
                if isinstance(locus, Nonterminal):
                    initial_items = set(filter(lambda item_: item_.rule.lhs == locus and item_.i == 0, self.items))
                    if not initial_items.issubset(state.items):
                        changed = True
                        state.items.update(initial_items)
        state.items = frozenset(state.items)
        return state

    def generate_i0(self):
        initial_item = {Item(Rule.augmented(), 0)}
        i0 = State(initial_item)
        i0 = self.closure(i0)
        self.states.add(i0)
        self.states_list.append(i0)

    def generate_tables(self):
        i = 0
        while True:
            try:
                state = self.states_list[i]
                self.action[i] = defaultdict(list)
                self.goto[i] = defaultdict(list)

                for terminal in self.terminals:
                    state_seed = State(set(
                        map(lambda item: Item(item.rule, item.i + 1),
                            filter(lambda item: item.locus() == terminal, state.items))))
                    if state_seed.items:
                        state_to_add = self.closure(state_seed)
                        if state_to_add not in self.states:
                            new_index = len(self.states)
                            self.states.add(state_to_add)
                            self.states_list.append(state_to_add)
                        else:
                            new_index = self.states_list.index(state_to_add)
                        self.action[i][terminal].append((self.Actions.SHIFT, None))
                        self.goto[i][terminal].append(new_index)

                for nonterminal in self.nonterminals:
                    state_seed = State(set(
                        map(lambda item: Item(item.rule, item.i + 1),
                            filter(lambda item: item.locus() == nonterminal, state.items))))
                    if state_seed.items:
                        state_to_add = self.closure(state_seed)
                        if state_to_add not in self.states:
                            new_index = len(self.states)
                            self.states.add(state_to_add)
                            self.states_list.append(state_to_add)
                        else:
                            new_index = self.states_list.index(state_to_add)
                        self.goto[i][nonterminal].append(new_index)

                for item in filter(lambda item_: item_.is_final(), state.items):
                    for symbol in self.follow[item.rule.lhs]:
                        self.action[i][symbol].append((self.Actions.REDUCE, item.rule))
                    # self.action[i][item.rule.lhs].append((self.Actions.REDUCE, item.rule))
                i += 1
            except IndexError:
                break


class GLR_parser:
    class Node_Type(Enum):
        STATE = 0
        SYMBOL = 1

    class Vertex:
        def __init__(self, node_type, pointer_number=None, state_number=None, symbol=None, actions=None, next_state=None, temp=False, semantic=None, start=None, end=None):
            self.node_type = node_type
            self.pointer_number = pointer_number
            self.state_number = state_number
            self.actions = actions
            self.reduces_done = False
            self.symbol = symbol
            self.next_state = next_state
            self.temp = temp
            self.semantic = semantic
            self.start = start
            self.end = end

        def __eq__(self, other):
            return \
                self.node_type == other.node_type \
                and self.pointer_number == other.pointer_number \
                and self.state_number == other.state_number \
                and self.next_state == other.next_state \
                and self.temp == other.temp

        def __hash__(self):
            try:
                return hash((self.node_type, self.pointer_number, self.state_number, self.next_state, self.temp))
            except TypeError:
                msg = f'Wrong type(s): {(self.node_type, self.pointer_number, self.state_number, self.next_state, self.temp)}'
                print(msg)
                exit(1)

        def __str__(self):
            return str(self.state_number) if self.node_type == GLR_parser.Node_Type.STATE else f'({self.symbol}, {self.semantic})'

        def to_forest(self):
            return GLR_parser.Forest_Node(self)

    class Forest_Node:
        def __init__(self, v):
            self.symbol = v.symbol
            self.semantic = v.semantic
            self.start = v.start
            self.end = v.end

        def __eq__(self, other):
            return \
                self.semantic == other.semantic \
                and self.start == other.start \
                and self.end == other.end \
                and self.symbol == other.symbol

        def __hash__(self):
            try:
                return hash((self.semantic, self.start, self.end, self.symbol))
            except TypeError:
                msg = f'Wrong type(s): {(self.symbol, self.semantic, self.start, self.end)}'
                print(msg)
                exit(1)

        def __str__(self):
            return f'({self.symbol}, {self.semantic})'

    class Head:
        def __init__(self, node_stack, state_stack, action_on_head, pos):
            self.node_stack = deepcopy(node_stack)
            self.state_stack = deepcopy(state_stack)
            self.action_on_head = action_on_head
            self.pos = pos

        @classmethod
        def from_head(cls, head):
            return GLR_parser.Head(head.node_stack, head.state_stack, head.action_on_head, head.pos)

    def __init__(self, g: Grammar):
        self.g = g
        self.active_vertices = [self.Vertex(self.Node_Type.STATE, set())]

    def prune(self, stack: nx.DiGraph, vertex: Vertex):
        if vertex.state_number == 0:
            return
        for v in list(stack.predecessors(vertex)):
            if len(list(stack.successors(v))) == 1:
                self.prune(stack, v)
        stack.remove_node(vertex)

    def parse(self, s: list):
        symbol_counter = count()
        i = next(symbol_counter)
        symbol = s[i]
        forest = nx.DiGraph()
        stack = nx.MultiDiGraph()
        counter = count()
        root_vertex = self.Vertex(self.Node_Type.STATE, state_number=i, actions=self.g.action[0][symbol])
        stack.add_node(root_vertex)
        active_vertices = {root_vertex}
        point = None
        while active_vertices:
            reduces_found = True
            while reduces_found:
                reduces_found = False
                for vertex in active_vertices.copy():
                    if not vertex.reduces_done:
                        reduces = list(filter(lambda x: x[0] == Grammar.Actions.REDUCE, vertex.actions))
                        for reduce in reduces:
                            vertex.actions.remove(reduce)
                            reduces_found = True
                            rule = reduce[1]
                            paths = [[vertex]]
                            for j, sym in enumerate(reversed(rule.rhs)):
                                for _ in range(len(paths)):
                                    path = paths.pop(0)
                                    v = path[-1]
                                    for sym_to_compare in stack.predecessors(v):
                                        if sym_to_compare.symbol == sym:
                                            new_path = path.copy()
                                            new_path.append(sym_to_compare)
                                            paths.append(new_path)
                                for _ in range(len(paths)):
                                    path = paths.pop(0)
                                    last = path[-1]
                                    for v in stack.predecessors(last):
                                        new_path = path.copy()
                                        new_path.append(v)
                                        paths.append(new_path)
                            point = next(counter)
                            for path in paths:
                                v = path.pop()
                                semantic_arg = list(map(lambda x: x.semantic, list(reversed(path[1::2]))))
                                semantic_func = getattr(semantic, rule.semantic)
                                semantic_result = semantic_func(semantic_arg)
                                symbol = rule.lhs
                                if symbol == 'S\'':
                                    stack.add_edge(v, 'S\'')
                                else:
                                    next_state = self.g.goto[v.state_number][symbol][0]
                                    symbol_vertex = self.Vertex(self.Node_Type.SYMBOL, pointer_number=point,
                                                                symbol=symbol, next_state=next_state, semantic=semantic_result,
                                                                start=path[-1].start, end=path[1].end)
                                    forest.add_node(symbol_vertex.to_forest())
                                    symbols = list(filter(lambda x: x.node_type == self.Node_Type.SYMBOL, path))
                                    for sym in symbols:
                                        forest.add_edge(symbol_vertex.to_forest(), sym.to_forest())
                                    next_state_vertex = self.Vertex(self.Node_Type.STATE, state_number=next_state,
                                                                    pointer_number=i,
                                                                    actions=self.g.action[next_state][s[i]].copy(),
                                                                    temp=True)
                                    stack.add_node(next_state_vertex)
                                    stack.add_edge(v, symbol_vertex)
                                    stack.add_edge(symbol_vertex, next_state_vertex)
                                    # color_map = ['g' if node in active_vertices else 'r' for node in stack]
                                    # nx.draw_networkx(stack, with_labels=True, node_color=color_map)
                                    # nx.draw_networkx(forest, with_labels=True)
                                    # plt.show()

                        vertex.reduces_done = True
                        if not list(filter(lambda x: x[0] == Grammar.Actions.SHIFT, vertex.actions)):
                            active_vertices.remove(vertex)
                            self.prune(stack, vertex)
                        for v in list(stack.nodes):
                            if isinstance(v, str):
                                continue
                            if v.temp:
                                new_v = self.Vertex(v.node_type, v.pointer_number, v.state_number, v.symbol, v.actions,
                                                    v.next_state, False)
                                pred = stack.predecessors(v)
                                stack.remove_node(v)
                                stack.add_node(new_v)
                                active_vertices.add(new_v)
                                for e in pred:
                                    stack.add_edge(e, new_v)
                        # color_map = ['g' if node in active_vertices else 'r' for node in stack]
                        # nx.draw_networkx(stack, with_labels=True, node_color=color_map)
                        # nx.draw_networkx(forest, with_labels=True)
                        # plt.show()
            point = next(counter)
            for vertex in active_vertices.copy():
                next_state = self.g.goto[vertex.state_number][s[i]][0]
                symbol_vertex = self.Vertex(self.Node_Type.SYMBOL, pointer_number=point, symbol=s[i],
                                            next_state=next_state, semantic=s[i].str,
                                            start=i, end=i)
                forest.add_node(symbol_vertex.to_forest())
                next_state_vertex = self.Vertex(self.Node_Type.STATE, state_number=next_state, pointer_number=i, actions=self.g.action[next_state][s[i+1]].copy())
                stack.add_node(next_state_vertex)
                stack.add_edge(vertex, symbol_vertex)
                stack.add_edge(symbol_vertex, next_state_vertex)
                active_vertices.add(next_state_vertex)
                active_vertices.remove(vertex)
                # color_map = ['g' if node in active_vertices else 'r' for node in stack]
                # nx.draw_networkx(stack, with_labels=True, node_color=color_map)
                # nx.draw_networkx(forest, with_labels=True)
                # plt.show()
            i = next(symbol_counter)
        return forest


def main():
    args_parser = argparse.ArgumentParser()
    args_parser.add_argument('grammar', type=argparse.FileType('r'), help='Grammar file')
    args_parser.add_argument('input', type=argparse.FileType('r'), help='Input file')
    args = args_parser.parse_args()

    g = Grammar(args.grammar.read())
    s = args.input.read().rstrip().replace('\n', ' ')
    list_of_symbols = [Terminal(x) for x in s.split(' ')]
    list_of_symbols.append(Terminal.endsymbol())
    parser = GLR_parser(g)

    start = time()
    forest = parser.parse(list_of_symbols)
    colors = ['b' for _ in forest]
    for i, node in enumerate(forest):
        CONJUNCT_REGEX = r'C_[0-9]*'
        if re.match(CONJUNCT_REGEX, str(node.symbol)):
            correct = True
            for pred in forest.predecessors(node):
                for conjunct in g.conjs[node.symbol]:
                    if conjunct not in map(lambda x: x.symbol, forest.successors(pred)):
                        correct = False
            if not correct:
                colors[i] = 'r'
    nx.draw_networkx(forest, with_labels=True, node_color=colors)
    plt.show()
    end = time()
    print(f'Done in {(end - start)*1000} ms')


if __name__ == '__main__':
    main()
