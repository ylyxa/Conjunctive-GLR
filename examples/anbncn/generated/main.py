import argparse
import re
from collections import defaultdict
from copy import deepcopy
from enum import Enum
from itertools import count
from time import time
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib import pylab
import semantic
from lexer import lexer
import reconfigure


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

    @classmethod
    def empty(cls):
        return Terminal('_')


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
    TERM_REGEX = r'[_a-z][a-zA-Z0-9]*'
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
        SPLIT_OPERATOR = ';'
        ASSIGN_OPERATOR = '::='
        r, semantic = s.split(SPLIT_OPERATOR)
        lhs_rhs = r.split(ASSIGN_OPERATOR)
        rhs_as_strings = lhs_rhs[1].lstrip().split(' ')
        self.lhs = Nonterminal.generate_with_regex_check(
            lhs_rhs[0].rstrip()) if check_lhs else Nonterminal(
            lhs_rhs[0].rstrip())
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
        return Rule('S\' ::= S;pass_through')


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
        return None if self.next_is_final() else self.rule.rhs[
            self.i + 1]

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
                SPLIT_OPERATOR = ';'
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
                    new_rule = \
                        f'{nonterm} ::= {conj.rstrip().lstrip()};{semantic}'
                    new_higher_rule = f'{lhs} ::= {nonterm};pass_through'
                    bottom_rules.append(
                        Rule(new_rule, check_lhs=False))
                    top_rules.append(new_higher_rule)
                    conjs.append(Nonterminal(nonterm))
                for rule in bottom_rules:
                    self.rules.append(rule)
                for rule in top_rules:
                    self.rules.append((Rule(rule, check_lhs=False)))
                for conj in conjs:
                    self.conjs[conj] = conjs
        self.terminals = {Terminal.endsymbol(), Terminal.empty()}
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

    def F(self, chain):
        if not chain:
            return {Terminal.empty()}
        symbol = chain[0]
        if isinstance(symbol, Terminal):
            return {symbol}
        elif isinstance(symbol, Nonterminal):
            if Terminal.empty() not in self.first[symbol]:
                return self.first[symbol]
            else:
                to_add = self.first[symbol].copy()
                to_add.remove(Terminal.empty())
                to_add.update(self.F(chain[1:]))
                return to_add

    def generate_first(self):
        changed = True
        while changed:
            changed = False
            for rule in self.rules:
                f = self.F(rule.rhs)
                if not f.issubset(self.first[rule.lhs]):
                    changed = True
                    self.first[rule.lhs].update(f)

    def generate_follow(self):
        self.follow[Rule.augmented().lhs].add(Terminal.endsymbol())
        changed = True
        while changed:
            changed = False
            for item in self.items:
                locus = item.locus()
                if isinstance(locus, Nonterminal):
                    next_locus = item.next_locus()
                    if isinstance(next_locus, Terminal) \
                            and next_locus != Terminal.empty() \
                            and next_locus not in self.follow[locus]:
                        changed = True
                        self.follow[locus].add(next_locus)
                    next_first = self.first[next_locus].copy()
                    next_first_has_empty = False
                    if Terminal.empty() in next_first:
                        next_first.remove(Terminal.empty())
                        next_first_has_empty = True
                    if isinstance(next_locus, Nonterminal) \
                            and not next_first.issubset(
                        self.follow[locus]):
                        changed = True
                        self.follow[locus].update(next_first)
                    if (next_locus is None or next_first_has_empty) \
                            and not self.follow[
                        item.rule.lhs].issubset(
                        self.follow[locus]):
                        changed = True
                        self.follow[locus].update(
                            self.follow[item.rule.lhs])

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
                    initial_items = set(filter(lambda item_:
                                               item_.rule.lhs == locus
                                               and item_.i == 0,
                                               self.items))
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
                            filter(lambda item: item.locus() ==
                                                terminal,
                                   state.items))))
                    if state_seed.items:
                        state_to_add = self.closure(state_seed)
                        if state_to_add not in self.states:
                            new_index = len(self.states)
                            self.states.add(state_to_add)
                            self.states_list.append(state_to_add)
                        else:
                            new_index = self.states_list.index(
                                state_to_add)
                        self.action[i][terminal].append((
                            self.Actions.SHIFT, None))
                        self.goto[i][terminal].append(new_index)

                for nonterminal in self.nonterminals:
                    state_seed = State(set(
                        map(lambda item: Item(item.rule, item.i + 1),
                            filter(lambda item: item.locus() ==
                                                nonterminal,
                                   state.items))))
                    if state_seed.items:
                        state_to_add = self.closure(state_seed)
                        if state_to_add not in self.states:
                            new_index = len(self.states)
                            self.states.add(state_to_add)
                            self.states_list.append(state_to_add)
                        else:
                            new_index = self.states_list.index(
                                state_to_add)
                        self.goto[i][nonterminal].append(new_index)

                for item in filter(lambda item_:
                                   item_.is_final(), state.items):
                    for symbol in self.follow[item.rule.lhs]:
                        self.action[i][symbol].append((
                            self.Actions.REDUCE, item.rule))
                i += 1
            except IndexError:
                break


class GLR_parser:
    class Node_Type(Enum):
        STATE = 0
        SYMBOL = 1

    class Vertex:
        def __init__(self, node_type, pointer_number=None,
                     state_number=None, symbol=None, actions=None,
                     next_state=None, prev_state=None, temp=False,
                     semantic=None, start=None, end=None,
                     shift_empty=False):
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
            self.shift_empty = shift_empty
            self.prev_state = prev_state

        def __eq__(self, other):
            return \
                self.node_type == other.node_type \
                and self.pointer_number == other.pointer_number \
                and self.state_number == other.state_number \
                and self.next_state == other.next_state \
                and self.prev_state == other.prev_state \
                and self.start == other.start \
                and self.end == other.end \
                and self.temp == other.temp

        def __hash__(self):
            try:
                return hash((self.node_type, self.pointer_number,
                             self.state_number, self.next_state,
                             self.prev_state,
                             self.temp, self.start, self.end))
            except TypeError:
                msg = f'Wrong type(s)'
                print(msg)
                exit(1)

        def __str__(self):
            return f'({self.state_number})' if self.node_type == \
                                    GLR_parser.Node_Type.STATE else \
                f'({self.symbol}, {self.start}, {self.end})'

        def to_forest(self):
            return GLR_parser.Forest_Node(self)

    class Forest_Node:
        def __init__(self, v):
            self.symbol = v.symbol
            self.semantic = v.semantic
            self.start = v.start
            self.end = v.end
            self.rules = []

        def __eq__(self, other):
            return self.__hash__() == other.__hash__()

        def __hash__(self):
            try:
                return hash((self.start, self.end, self.symbol))
            except TypeError:
                msg = \
                    f'Wrong type(s): {(self.symbol, self.start, self.end)}'
                print(msg)
                exit(1)

        def __str__(self):
            return f'({self.symbol}, {self.start}, {self.end})'

    def __init__(self, g: Grammar):
        self.g = g

    def prune(self, stack: nx.DiGraph, vertex: Vertex,
              active_vertices):
        if vertex.state_number == 0 or vertex in active_vertices:
            return
        for v in list(stack.predecessors(vertex)):
            if len(list(stack.successors(v))) == 1:
                self.prune(stack, v, active_vertices)
        stack.remove_node(vertex)

    def draw_stack(self, stack, color_map):
        # nx.draw_networkx(stack, with_labels=True, node_color=color_map)
        H = nx.convert_node_labels_to_integers(stack,
                                               label_attribute="node_label")
        H_layout = nx.nx_agraph.pygraphviz_layout(H, prog="dot")
        G_layout = {H.nodes[n]["node_label"]: p for n, p in
                    H_layout.items()}
        pos = nx.nx_agraph.graphviz_layout(stack, prog="dot")
        nx.draw_networkx_nodes(stack, G_layout, node_color=color_map)
        nx.draw_networkx_edges(stack, G_layout)
        nx.draw_networkx_labels(stack, G_layout)
        plt.show()
        pass

    def parse(self, s: list):
        symbol_counter = count()
        i = next(symbol_counter)
        symbol = s[i]
        forest = nx.DiGraph()
        stack = nx.MultiDiGraph()
        counter = count()
        root_vertex = self.Vertex(self.Node_Type.STATE,
                                  state_number=i,
                                  actions=self.g.action[0][symbol],
                                  shift_empty=len(self.g.action[0][
                                            Terminal.empty()]) > 0)
        stack.add_node(root_vertex)
        active_vertices = {root_vertex}
        point = 0
        while active_vertices:
            color_map = ['g' if node in active_vertices else 'r' for
                         node in stack]
            # if i == 5:
            #     self.draw_stack(stack, color_map)
            to_shift_empty = True
            while to_shift_empty:
                to_shift_empty = False
                for vertex in active_vertices.copy():
                    if vertex.shift_empty:
                        vertex.shift_empty = False
                        next_state = self.g.goto[vertex.state_number][
                            Terminal.empty()][0]
                        symbol_vertex = self.Vertex(
                            self.Node_Type.SYMBOL,
                            pointer_number=point, symbol='_',
                            next_state=next_state,
                            prev_state=vertex.state_number,
                            semantic='',
                            start=i, end=i)
                        forest.add_node(symbol_vertex.to_forest())
                        next_state_vertex = self.Vertex(
                            self.Node_Type.STATE,
                            state_number=next_state, pointer_number=i,
                            actions=self.g.action[next_state][
                                s[i]].copy(),
                            shift_empty=len(
                                self.g.action[next_state][
                                    Terminal.empty()]) > 0)
                        if next_state_vertex.shift_empty:
                            to_shift_empty = True
                        stack.add_node(next_state_vertex)
                        stack.add_node(symbol_vertex)
                        stack.add_edge(vertex, symbol_vertex)
                        stack.add_edge(symbol_vertex,
                                       next_state_vertex)
                        active_vertices.add(next_state_vertex)
                        if not vertex.actions:
                            active_vertices.remove(vertex)
                        color_map = [
                            'g' if node in active_vertices else 'r'
                            for node in stack]
                        # self.draw_stack(stack, color_map)
                reduces_found = True
                while reduces_found:
                    reduces_found = False
                    for vertex in active_vertices.copy():
                        if not vertex.reduces_done:
                            reduces = list(filter(lambda x: x[0] ==
                                                Grammar.Actions.REDUCE,
                                                  vertex.actions))
                            for reduce in reduces:
                                vertex.actions.remove(reduce)
                                reduces_found = True
                                rule = reduce[1]
                                paths = [[vertex]]
                                for j, sym in enumerate(
                                        reversed(rule.rhs)):
                                    for _ in range(len(paths)):
                                        path = paths.pop(0)
                                        v = path[-1]
                                        for sym_to_compare in \
                                                stack.predecessors(
                                                v):
                                            if sym_to_compare.symbol == sym:
                                                new_path = path.copy()
                                                new_path.append(
                                                    sym_to_compare)
                                                paths.append(new_path)
                                    for _ in range(len(paths)):
                                        path = paths.pop(0)
                                        last = path[-1]
                                        for v in stack.predecessors(
                                                last):
                                            new_path = path.copy()
                                            new_path.append(v)
                                            paths.append(new_path)
                                point = next(counter)
                                for path in paths:
                                    v = path.pop()
                                    semantic_arg = list(
                                        map(lambda x: x.semantic,
                                            list(reversed(
                                                path[1::2]))))
                                    semantic_func = getattr(semantic,
                                                            rule.semantic)
                                    semantic_result = semantic_func(
                                        semantic_arg)
                                    symbol = rule.lhs
                                    if symbol == 'S\'':
                                        stack.add_edge(v, 'S\'')
                                    else:
                                        next_state = \
                                        self.g.goto[v.state_number][
                                            symbol][0]
                                        symbol_vertex = self.Vertex(
                                            self.Node_Type.SYMBOL,
                                            pointer_number=point,
                                            symbol=symbol,
                                            next_state=next_state,
                                            prev_state=v.state_number,
                                            semantic=semantic_result,
                                            start=path[-1].start,
                                            end=path[1].end)
                                        if symbol_vertex.to_forest() \
                                                not in forest:
                                            forest.add_node(
                                                symbol_vertex.to_forest())
                                        for cand in filter(
                                                lambda x: x == \
                                                    symbol_vertex\
                                                        .to_forest(),
                                                forest):
                                            cand.rules.append(rule)
                                        symbols = list(filter(lambda x:
                                                x.node_type ==
                                                    self.Node_Type.SYMBOL,
                                                              path))
                                        for sym in symbols:
                                            forest.add_edge(
                                                symbol_vertex.to_forest(),
                                                sym.to_forest())
                                        next_state_vertex = self.Vertex(
                                            self.Node_Type.STATE,
                                            state_number=next_state,
                                            pointer_number=i,
                                            actions=
                                            self.g.action[next_state][
                                                s[i]].copy(),
                                            shift_empty=len(
                                                self.g.action[
                                                    next_state][
                                                    Terminal.empty()]) > 0,
                                            temp=True)
                                        if next_state_vertex.shift_empty:
                                            to_shift_empty = True
                                        stack.add_node(
                                            next_state_vertex)
                                        stack.add_node(symbol_vertex)
                                        stack.add_edge(v,
                                                       symbol_vertex)
                                        stack.add_edge(symbol_vertex,
                                                       next_state_vertex)
                                        color_map = [
                                            'g' if node in \
                                                active_vertices else 'r'
                                            for node in stack]

                            vertex.reduces_done = True
                            if not list(filter(lambda x: x[0] ==
                                                Grammar.Actions.SHIFT,
                                               vertex.actions)) and not \
                                    vertex.shift_empty:
                                active_vertices.remove(vertex)
                                if not list(stack.successors(vertex)):
                                    self.prune(stack, vertex,
                                               active_vertices)
                            for v in list(stack.nodes):
                                if isinstance(v, str):
                                    continue
                                if v.temp:
                                    new_v = self.Vertex(v.node_type,
                                                        v.pointer_number,
                                                        v.state_number,
                                                        v.symbol,
                                                        v.actions,
                                                        v.next_state,
                                                        v.prev_state,
                                                        False,
                                                        shift_empty=
                                                        v.shift_empty)
                                    pred = stack.predecessors(v)
                                    succ = stack.successors(v)
                                    stack.remove_node(v)
                                    stack.add_node(new_v)
                                    active_vertices.add(new_v)
                                    for e in pred:
                                        stack.add_edge(e, new_v)
                                    for e in succ:
                                        stack.add_edge(new_v, e)
                            color_map = [
                                'g' if node in active_vertices else 'r'
                                for node in stack]
                            # if i == 5:
                            #     self.draw_stack(stack, color_map)
            point = next(counter)
            for vertex in active_vertices.copy():
                next_state = self.g.goto[vertex.state_number][s[i]][0]
                symbol_vertex = self.Vertex(self.Node_Type.SYMBOL,
                                            pointer_number=point,
                                            symbol=s[i],
                                            next_state=next_state,
                                            prev_state=vertex.state_number,
                                            semantic=s[i].value,
                                            start=i, end=i + 1)
                forest.add_node(symbol_vertex.to_forest())
                next_state_vertex = self.Vertex(self.Node_Type.STATE,
                                                state_number=next_state,
                                                pointer_number=i,
                                                actions=self.g.action[
                                                    next_state][
                                                    s[i + 1]].copy(),
                                                shift_empty=len(
                                                    self.g.action[
                                                        next_state][
                                                        Terminal
                                                        .empty()]) > 0)
                if next_state_vertex.shift_empty:
                    to_shift_empty = True
                stack.add_node(next_state_vertex)
                stack.add_node(symbol_vertex)
                stack.add_edge(vertex, symbol_vertex)
                stack.add_edge(symbol_vertex, next_state_vertex)
                active_vertices.add(next_state_vertex)
                active_vertices.remove(vertex)
                color_map = ['g' if node in active_vertices else 'r'
                             for node in stack]
            i = next(symbol_counter)
        return forest


def save_graph(graph, file_name, colors=None):
    plt.figure(num=None, figsize=(20, 20), dpi=80)
    plt.axis('off')
    fig = plt.figure(1)
    pos = nx.nx_agraph.graphviz_layout(graph, prog="dot")
    nx.draw_networkx_nodes(graph, pos, node_color=colors)
    nx.draw_networkx_edges(graph, pos)
    nx.draw_networkx_labels(graph, pos)

    plt.savefig(file_name, bbox_inches="tight")
    pylab.close()
    del fig


def prune_up(stack: nx.DiGraph, vertex: GLR_parser.Vertex):
    if vertex not in stack:
        return
    predecessors = list(stack.predecessors(vertex))
    stack.remove_node(vertex)
    for v in stack.copy():
        if v not in predecessors:
            continue
        if not list(filter(lambda x: x.symbol == vertex.symbol,
                           stack.successors(v))):
            for r in v.rules.copy():
                if vertex.symbol in r.rhs:
                    v.rules.remove(r)
        if len(v.rules) == 0:
            prune_up(stack, v)


def prune_down(stack: nx.DiGraph, vertex: GLR_parser.Vertex):
    if vertex not in stack:
        return
    for v in list(stack.successors(vertex)):
        if len(list(stack.predecessors(v))) == 1:
            prune_down(stack, v)
    stack.remove_node(vertex)


def main():
    args_parser = argparse.ArgumentParser()
    args_parser.add_argument('grammar', type=argparse.FileType('r'),
                             help='Grammar file')
    args_parser.add_argument('input', type=argparse.FileType('r'),
                             help='Input file')
    args_parser.add_argument('-d', '--debug', action='store_true',
                             help='Show the debug forest')
    args = args_parser.parse_args()

    g = Grammar(args.grammar.read())
    s = args.input.read()
    lexer.input(s)
    list_of_symbols = []
    while True:
        tok = lexer.token()
        if not tok:
            break
        new_term = Terminal(tok.type)
        new_term.value = tok.value
        list_of_symbols.append(new_term)
    list_of_symbols.append(Terminal.endsymbol())
    parser = GLR_parser(g)

    start = time()
    forest = parser.parse(list_of_symbols)
    end = time()
    save_graph(forest, "my_graph_before.pdf")
    if args.debug:
        color_map = ['g' for _ in forest]
        changed = True
        while changed:
            changed = False
            forest_copy = deepcopy(forest)
            for i, node in enumerate(forest_copy):
                CONJUNCT_REGEX = r'C_[0-9]*'
                if re.match(CONJUNCT_REGEX, str(node.symbol)):
                    for pred in forest_copy.predecessors(node):
                        for conjunct in g.conjs[node.symbol]:
                            if conjunct not in map(lambda x: x.symbol,
                                                   forest_copy.successors(
                                                           pred)):
                                color_map[i] = 'r'
                    if color_map[i] == 'g':
                        color_map[i] = 'b'
        save_graph(forest, "my_graph.pdf", colors=color_map)
    else:
        changed = True
        while changed:
            changed = False
            forest_copy = deepcopy(forest)
            for i, node in enumerate(forest_copy):
                CONJUNCT_REGEX = r'C_[0-9]*'
                if re.match(CONJUNCT_REGEX, str(node.symbol)):
                    for pred in forest_copy.predecessors(node):
                        for conjunct in g.conjs[node.symbol]:
                            if conjunct not in map(lambda x: x.symbol,
                                                   forest_copy.successors(
                                                           pred)):
                                prune_up(forest, node)
                                changed = True

        forest_copy = deepcopy(forest)
        found_s = False
        old = s
        new = None
        axiom = None
        for i, node in enumerate(forest_copy):
            if node in forest and node.symbol != 'S' and not list(
                    forest.predecessors(node)):
                prune_down(forest, node)
            if node.symbol == 'S':
                found_s = True
                axiom = node.semantic
                print(f'Graph has {len(forest.nodes)} nodes and {len(forest.edges)} edges')
                print(f'Semantic result: {axiom}')
        if found_s:
            print('Started reconfigure loop')
            new = reconfigure.reconfigure(axiom)
            print(f'Reconfigured {axiom} to {new}')
            save_graph(forest, "graph_before_reconfigure_loop.pdf")
            while old != new:
                old = new
                lexer.input(new)
                list_of_symbols = []
                while True:
                    tok = lexer.token()
                    if not tok:
                        break
                    new_term = Terminal(tok.type)
                    new_term.value = tok.value
                    list_of_symbols.append(new_term)
                list_of_symbols.append(Terminal.endsymbol())
                forest = parser.parse(list_of_symbols)
                forest_copy = deepcopy(forest)
                for i, node in enumerate(forest_copy):
                    if node.symbol == 'S':
                        new = reconfigure.reconfigure(node.semantic)
                        print(f'Reconfigured {node.semantic} to {new}')
            print('Ended reconfigure loop')
            save_graph(forest, "graph.pdf", colors=None)
        else:
            print('Syntax error!')

    print(f'Done in {(end - start) * 1000} ms')


if __name__ == '__main__':
    main()
