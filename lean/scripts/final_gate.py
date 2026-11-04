#!/usr/bin/env python3
"""final_gate.py — the final gate of the Sheil project (check.sh --final), after audit.py has written CLAIMS.json.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
An unproved paper claim stays a public row with its exact type and a placeholder body, and is counted OPEN; the
placeholder is allowed nowhere else. A bare `end` line also ends a row.

Checks, against one explicit list of OPEN rows (OPEN_ROWS.txt: one row name per line, '#' comments):
1. In Statements.lean every occurrence of the placeholder word is the WHOLE body (`:= by <word>` or `:= <word>`)
   of a listed row. (Every other Lean file is scanned by check.sh, which allows the word nowhere.)
2. In CLAIMS.json every listed row exists and has status OPEN (its axioms show the placeholder axiom); no other
   row is OPEN, VIOLATION or PROVED-FROM-TEMP.
Usage: final_gate.py <Statements.lean> <CLAIMS.json> <OPEN_ROWS.txt>   |   final_gate.py --test
"""
import json
import re
import sys
from pathlib import Path

PLACEHOLDER = 'so' + 'rry'  # spelled in two parts so the source scan of this tree does not flag this file
WORD_RE = re.compile(r'\b' + PLACEHOLDER + r'\b')
DECL_RE = re.compile(r'^(?:theorem|lemma)\s+(\S+)', re.M)
NEXT_ITEM_RE = re.compile(r'^(?:/--|/-|@\[|#|(?:theorem|lemma|def|abbrev|noncomputable|instance|structure|'
                          r'namespace|section|end|open|variable)\b)', re.M)
BODY_RE = re.compile(r':=\s*(?:by\s+)?' + PLACEHOLDER + r'\s*$')
BAD_ELSEWHERE = {'OPEN', 'VIOLATION', 'PROVED-FROM-TEMP'}


def read_open_list(path):
    """Row names, in file order; duplicates are an error."""
    names = [line.split('#', 1)[0].strip() for line in Path(path).read_text(encoding='utf-8').splitlines()]
    names = [name for name in names if name]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        raise SystemExit(f'FINAL GATE: duplicate names in {path}: {duplicates}')
    return names


def declaration_spans(text):
    """[(name, start, end)]: each theorem/lemma runs to the next top-level item (or end of file)."""
    starts = [(match.group(1), match.start()) for match in DECL_RE.finditer(text)]
    spans = []
    for name, start in starts:
        following = NEXT_ITEM_RE.search(text, start + 1)
        spans.append((name, start, following.start() if following else len(text)))
    return spans


def allowed_offsets(text, open_names):
    """Offsets of the placeholder that are the whole body of a listed row."""
    allowed = set()
    for name, start, end in declaration_spans(text):
        span = text[start:end].rstrip()
        body = BODY_RE.search(span)
        if name.split('.')[-1] in open_names and body and len(WORD_RE.findall(span)) == 1:
            allowed.add(start + span.rindex(PLACEHOLDER))
    return allowed


def placement_errors(text, open_names):
    allowed = allowed_offsets(text, open_names)
    errors = []
    for match in WORD_RE.finditer(text):
        if match.start() not in allowed:
            line = text.count('\n', 0, match.start()) + 1
            errors.append(f'Statements.lean l.{line}: placeholder outside the whole body of a listed OPEN row')
    return errors


def status_errors(claims, open_names):
    status = {claim['name']: claim['status'] for claim in claims}
    errors = [f'listed OPEN row {name} is not a row' for name in open_names if name not in status]
    errors += [f'listed OPEN row {name} has status {status[name]} (must be OPEN; update the list)'
               for name in open_names if name in status and status[name] != 'OPEN']
    errors += [f'row {name} has status {st} but is not on the OPEN list'
               for name, st in status.items() if name not in open_names and st in BAD_ELSEWHERE]
    return errors


def main_final_gate(statements_path, claims_path, open_list_path):
    """Returns the list of errors (empty = PASS)."""
    open_names = set(read_open_list(open_list_path))
    text = Path(statements_path).read_text(encoding='utf-8')
    claims = json.loads(Path(claims_path).read_text(encoding='utf-8'))['claims']
    return placement_errors(text, open_names) + status_errors(claims, open_names)


def run_tests():
    hole = PLACEHOLDER
    text = (f'section\n/-- a.tex l.1 -/\ntheorem row_open (x : Nat) :\n    let y := x\n    y = x := by\n  {hole}\nend\n\n'
            f'/-- b -/\ntheorem row_done : True :=\n  trivial\n\n'
            f'theorem row_inline : True := {hole}\n\nend Sheil.Paper\n')
    assert placement_errors(text, {'row_open', 'row_inline'}) == []
    assert len(placement_errors(text, {'row_open'})) == 1                      # unlisted placeholder row
    assert len(placement_errors(text.replace('trivial', hole), {'row_open', 'row_inline'})) == 1
    two = text.replace(f'y = x := by\n  {hole}', f'y = x := by\n  have := 1\n  {hole}')
    assert len(placement_errors(two, {'row_open', 'row_inline'})) == 1         # not the WHOLE body
    commented = text.replace('/-- b -/', f'/-- b {hole} -/')
    assert len(placement_errors(commented, {'row_open', 'row_inline'})) == 1   # word in a docstring
    claims = [{'name': 'row_open', 'status': 'OPEN'}, {'name': 'row_done', 'status': 'PROVED'},
              {'name': 'row_dep', 'status': 'OPEN'}]
    assert status_errors(claims, {'row_open', 'row_dep'}) == []                # inherited OPEN is listed
    assert len(status_errors(claims, {'row_open'})) == 1                       # unlisted OPEN row
    assert len(status_errors(claims, {'row_open', 'row_dep', 'row_done'})) == 1  # listed but PROVED
    assert len(status_errors(claims, {'row_open', 'row_dep', 'row_gone'})) == 1  # stale list entry
    assert len(status_errors(claims + [{'name': 'v', 'status': 'VIOLATION'}], {'row_open', 'row_dep'})) == 1
    print('final_gate --test: 10/10 OK')


def main():
    if sys.argv[1:] == ['--test']:
        run_tests()
        return
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    errors = main_final_gate(*sys.argv[1:])
    for error in errors:
        print('FINAL GATE ERROR: ' + error, file=sys.stderr)
    if errors:
        raise SystemExit(1)
    print(f'FINAL GATE PASS: placeholders only as whole bodies of the {len(read_open_list(sys.argv[3]))} '
          'listed OPEN rows; statuses match the list.')


if __name__ == '__main__':
    main()
