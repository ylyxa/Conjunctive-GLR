import re
import argparse
from itertools import count


def main():
    args_parser = argparse.ArgumentParser()
    args_parser.add_argument('grammar', type=argparse.FileType('r'), help='Grammar file')
    args = args_parser.parse_args()

    s = args.grammar.read()
    counter = count()
    rules_as_strs = s.split('\n')
    rules = []
    TERM_REGEX = r'[a-z][a-zA-Z0-9]*'
    NONTERM_REGEX = r'[A-Z][a-zA-Z0-9]*'
    start = 'import ply.lex as lex\n\n\n'
    lexer = ''
    tokens = 'tokens = ('
    grammar = ''
    for i, rule in enumerate(rules_as_strs):
        lhs, rhs = rule.split('::=')
        lhs = lhs.rstrip()
        if re.match(TERM_REGEX, lhs):
            rhs = rhs.lstrip()
            lexer += f't_{lhs} = r\'{rhs}\'\n'
            tokens += f'\'{lhs}\','
        elif '|' in rule:
            SPLIT_OPERATOR = ';'
            ASSIGN_OPERATOR = '::='
            r, semantic = rule.split(SPLIT_OPERATOR)
            r = r.rstrip()
            semantic = semantic.lstrip()
            lhs, rhs = r.split(ASSIGN_OPERATOR)
            rhs_split = rhs.split('|')
            for disj in rhs_split:
                new_rule = f'{lhs} ::= {disj.rstrip().lstrip()};{semantic}\n'
                grammar += new_rule
        else:
            grammar += rule + '\n'

    tokens += ')\n\n'
    lexer = start + tokens + lexer + '\nlexer = lex.lex()\n'
    with open("lexer.py", "w") as lex:
        lex.write(lexer)
    with open("generated_grammar", "w") as g:
        g.write(grammar.rstrip())


if __name__ == '__main__':
    main()
