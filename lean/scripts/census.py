#!/usr/bin/env python3
"""census.py — the claim census: the status of every printed claim, from CLAIM_MAP.tsv and CLAIMS.json.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
A claim's status is the worst status of its REQUIRED rows; every row of Statements.lean must be mapped.
Usage: scripts/census.py            (prints the census table; fails loudly on an unknown or unmapped row)
       scripts/census.py --test     (self-test, no files read)
Run scripts/audit.py first: it writes CLAIMS.json. No Lean process here.
"""
import json
from pathlib import Path
import sys

PROJECT = Path(__file__).resolve().parent.parent
RANK = {"PROVED": 0, "PROVED-FROM-CITED": 1, "CITED": 2, "OPEN": 3}


def fail(message):
    raise SystemExit("CENSUS FAILED: " + message)


def parse_map(text):
    """CLAIM_MAP.tsv lines -> list of (claim id, description, required rows, support rows)."""
    claims = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        cells = line.split("\t") + ["", ""]
        required = [row for row in cells[2].split(",") if row]
        support = [row for row in cells[3].split(",") if row]
        if not required:
            fail("claim " + cells[0] + " has no REQUIRED row")
        claims.append((cells[0], cells[1], required, support))
    return claims


def claim_status(required, row_status):
    """The worst REQUIRED row decides."""
    for row in required:
        if row not in row_status:
            fail("unknown row " + row)
        if row_status[row] not in RANK:
            fail("row " + row + " has status " + row_status[row])
    return max((row_status[row] for row in required), key=RANK.get)


def check_all_mapped(claims, row_status):
    mapped = {row for _, _, required, support in claims for row in required + support}
    unmapped = sorted(set(row_status) - mapped)
    if unmapped:
        fail("rows not in CLAIM_MAP: " + ", ".join(unmapped))


def main_census():
    claims = parse_map((PROJECT / "CLAIM_MAP.tsv").read_text())
    rows = json.loads((PROJECT / "CLAIMS.json").read_text())["claims"]
    row_status = {row["name"]: row["status"] for row in rows}
    check_all_mapped(claims, row_status)
    counts = {}
    for claim_id, description, required, _ in claims:
        status = claim_status(required, row_status)
        counts[status] = counts.get(status, 0) + 1
        print(f"{claim_id}\t{status}\t{description[:90]}")
    print("CENSUS:", len(claims), "claims", json.dumps(counts, sort_keys=True))


def main_test():
    text = "# c\nX1\td\ta,b\tc\nX2\td\tc\t\n"
    claims = parse_map(text)
    status = {"a": "PROVED", "b": "OPEN", "c": "CITED"}
    assert claim_status(claims[0][2], status) == "OPEN"
    assert claim_status(claims[1][2], status) == "CITED"
    check_all_mapped(claims, status)
    for bad in [lambda: check_all_mapped(claims, {**status, "d": "PROVED"}),
                lambda: claim_status(["zz"], status), lambda: parse_map("X\td\t\t\n")]:
        try:
            bad()
        except SystemExit:
            continue
        raise AssertionError("a bad case passed")
    print("census --test: PASS")


def main():
    if sys.argv[1:] == ["--test"]:
        main_test()
    elif not sys.argv[1:]:
        main_census()
    else:
        fail("usage: scripts/census.py [--test]")


if __name__ == "__main__":
    main()
