import re
import argparse
import os
import shutil
from itertools import count


def main():
    args_parser = argparse.ArgumentParser()
    args_parser.add_argument('grammar', type=argparse.FileType('r'),
                             help='Grammar file')
    args = args_parser.parse_args()
    if os.path.isdir('generated'):
        shutil.rmtree('generated')
    os.mkdir('generated')
    shutil.copyfile('main.py', 'generated/main.py')
    shutil.copyfile('semantic.py', 'generated/semantic.py')
    shutil.copyfile('reconfigure.py', 'generated/reconfigure.py')

    s = args.grammar.read()
    rules_as_strs = s.split('\n')
    TERM_REGEX = r'[a-z][a-zA-Z0-9]*'
    start = 'import ply.lex as lex\n\n\n'
    lexer = ''
    tokens = 'tokens = ('
    grammar = ''
    for i, rule in enumerate(rules_as_strs):
        if '::=' not in rule:
            continue
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
                new_rule = \
                    f'{lhs}::= {disj.rstrip().lstrip()};{semantic}\n'
                grammar += new_rule
        else:
            grammar += rule + '\n'

    tokens += ')\n\n'
    lexer = start + tokens + lexer + '\nlexer = lex.lex()\n'
    with open("generated/lexer.py", "w") as lex:
        lex.write(lexer)
    with open("generated/generated_grammar", "w") as g:
        g.write(grammar.rstrip())


if __name__ == '__main__':
    main()
