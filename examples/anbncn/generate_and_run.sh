#!/bin/sh
python3 ./generator.py ./grammar
python3 ./generated/main.py ./generated/generated_grammar ./input

start "" /max "./graph.pdf"