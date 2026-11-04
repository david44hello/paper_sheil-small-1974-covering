#!/usr/bin/env python3
"""audit.py — the Sheil claim audit: Lean's own `#print axioms` for every row of Sheil/Paper/Statements.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Usage: python3 scripts/audit.py          writes Sheil/Audit.lean, runs `lake build Sheil.Audit` (one Lean thread),
                                         writes AUDIT.md and CLAIMS.json (the same bytes on every run of the same tree)
       python3 scripts/audit.py --test   self-test, no Lean
The cited inputs it accepts are listed in scripts/cited_inputs.json. The generated audit never changes a paper
statement or assumes a check. Its raw Lean output goes to scripts/audit_output.log (ignored by Git).
"""
import json
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent.parent
LIB = "Sheil"
NAMESPACE = LIB + ".Paper"
CITED = LIB + ".Cited."
CHECKS = LIB + ".ComputerChecked."
AUDIT_NAMESPACE = LIB + "Audit"   # the namespace of scripts/audit_checks.lean.inc
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
STATEMENTS = PROJECT / LIB / "Paper/Statements.lean"
# The one Lean process runs with one Lean thread.
LEAN_ENV = ["env", "LEAN_NUM_THREADS=1"]


def fail(message):
    raise SystemExit("AUDIT FAILED: " + message)


def mask_comments(text):
    """Preserve offsets/newlines while removing nested Lean comments and strings."""
    chars = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                chars[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                chars[i:i+2] = "  "; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                if text[i] == '"': string = False
                i += 1
        elif text.startswith("/-", i):
            chars[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            chars[i:end] = " " * (end-i); i = end
        elif text[i] == '"':
            chars[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string:
        fail("unterminated comment/string")
    return "".join(chars)


def doc_before(text, offset):
    match = re.search(r"/--((?:(?!-/).)*)-/\s*\Z", text[:offset], re.S)
    return " ".join(match.group(1).split()) if match else ""


def parse_statements(text):
    """Plain, line-start theorem declarations, as required by Statements contract."""
    clean = mask_comments(text)
    heads = list(re.finditer(r"^theorem\s+([A-Za-z_][\w']*)(?=\s)", clean, re.M))
    if len(heads) != len(re.findall(r"\btheorem\b", clean)):
        fail("unsupported theorem syntax; use plain line-start theorem declarations")
    if re.search(r"\b(?:lemma|example|axiom|opaque|def|abbrev|constant)\b", clean):
        fail("Statements may contain only theorem rows, imports, namespaces and registry comments")
    items = []
    for i, head in enumerate(heads):
        stop = heads[i+1].start() if i+1 < len(heads) else len(clean)
        block = clean[head.end():stop]
        assignment = re.search(r":=", block)
        if not assignment: fail("missing := for " + head.group(1))
        body = block[assignment.end():]
        body = re.split(r"^end\b|^#", body, maxsplit=1, flags=re.M)[0].strip()
        direct = re.fullmatch(r"(?:by\s+exact\s+)?((?:" + re.escape(LIB) + r"\.)?Cited\.[\w.']+)(?:\s+[\w']+)*", body)
        cited = direct.group(1) if direct else None
        if cited and cited.startswith("Cited."): cited = LIB + "." + cited
        items.append({"name": head.group(1), "doc": doc_before(text, head.start()),
                      "line": text[:head.start()].count("\n")+1, "direct_cited_input": cited})
    names = [item["name"] for item in items]
    if not names or len(names) != len(set(names)):
        fail("empty or duplicate theorem inventory")
    return items


def parse_checks(text):
    clean = mask_comments(text)
    items = []
    for match in re.finditer(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w']*)(.*?):=", clean, re.S | re.M):
        name, signature = match.group(1), match.group(2)
        doc = doc_before(text, match.start())
        if name.startswith("Check") or "COMPUTER-CHECKED" in doc:
            if not name.startswith("Check") or not re.fullmatch(r"\s*:\s*Prop\s*", signature):
                fail("computer check must be def Check... : Prop (no parameters): " + name)
            if "COMPUTER-CHECKED" not in doc or "NOT proved in Lean" not in doc:
                fail("computer check lacks COMPUTER-CHECKED / NOT proved in Lean docstring: " + name)
            items.append({"name": CHECKS + name, "doc": doc})
    if len(items) != len(set(item["name"] for item in items)):
        fail("duplicate computer check definition")
    return items


def parse_not_stated(text):
    blocks = re.findall(r"/-!\s*## NOT stated[^\n]*\n(.*?)-/", text, re.S)
    if len(blocks) != 1: fail("need exactly one /-! ## NOT stated registry (empty is allowed)")
    body = blocks[0]
    items = [{"name": m.group(1), "kind": m.group(2), "reason": " ".join(m.group(3).split()),
              "status": "NOT-FORMALIZED"}
             for m in re.finditer(r"^\((N\w+)\)\s*\[([^\]]+)\]\s*(.*?)(?=^\(N\w+\)|\Z)", body, re.S | re.M)]
    if len(items) != len(re.findall(r"^\(N\w+\)", body, re.M)):
        fail("NOT stated registry entry lacks [kind]")
    if len(items) != len(set(item["name"] for item in items)) or any(not item["reason"] for item in items):
        fail("empty reason or duplicate NOT stated label")
    return items


def parse_axioms(output, names):
    result = {}
    for match in re.finditer(r"'([\w.']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", output, re.S):
        if not match.group(1).startswith(NAMESPACE + "."): continue
        name = match.group(1).removeprefix(NAMESPACE + ".")
        if name in result: fail("duplicate axiom output for " + name)
        result[name] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
    if set(names) != set(result): fail("missing/unexpected axiom rows: " + str(set(names) ^ set(result)))
    return result


def parse_dependencies(output, names, checks):
    result = {}
    for match in re.finditer(r"GKCHECK\|([\w']+)\|([^|\n]*)\|([^|\n]*)\|END", output):
        name = match.group(1)
        all_checks = set(filter(None, match.group(2).split(",")))
        hypotheses = set(filter(None, match.group(3).split(",")))
        if name in result: fail("duplicate type inspection for " + name)
        if (all_checks | hypotheses) - checks: fail("unregistered computer check in " + name)
        result[name] = (all_checks, hypotheses)
    if set(result) != set(names): fail("missing/unexpected type inspections: " + str(set(names) ^ set(result)))
    return result


def parse_direct_inputs(output, names):
    result = {}
    for match in re.finditer(r"GKDIRECT\|([\w']+)\|([^|\n]*)\|END", output):
        name, cited = match.groups()
        if name in result or (cited and not cited.startswith(CITED)):
            fail("invalid direct-input inspection for " + name)
        result[name] = cited or None
    if set(result) != set(names): fail("missing/unexpected direct-input inspections")
    return result


def classify(axioms, reviewed, direct_input=None, dependencies=(frozenset(), frozenset())):
    extra = axioms - STANDARD
    if extra - reviewed - {"sorryAx"}: return "VIOLATION"
    if "sorryAx" in axioms: return "OPEN"
    all_checks, hypotheses = dependencies
    if all_checks - hypotheses: return "VIOLATION"  # check in conclusion/alias without explicit hypothesis
    if hypotheses: return "PROVED-GIVEN " + ", ".join(sorted(hypotheses))
    if direct_input:
        return "CITED" if extra == {direct_input} and direct_input in reviewed else "VIOLATION"
    return "PROVED-FROM-CITED" if extra else "PROVED"


def load_reviewed(path):
    data = json.loads(path.read_text())
    if not isinstance(data, dict) or not isinstance(data.get("inputs"), list): fail("bad cited_inputs.json schema")
    names = []
    for item in data["inputs"]:
        if not isinstance(item, dict) or not item.get("name", "").startswith(CITED) or \
           not item.get("source") or not item.get("review") or item.get("status") not in {"refereed", "UNREFEREED"}:
            fail("each citation needs exact name, source, review evidence and refereed/UNREFEREED status")
        if item["name"].startswith(CITED + "Temp."): fail("temporary own-paper assumptions are forbidden")
        names.append(item["name"])
    if len(names) != len(set(names)): fail("duplicate reviewed cited input")
    return set(names)


def audit_lean(names, checks):
    helper = (PROJECT / "scripts/audit_checks.lean.inc").read_text()
    lines = ["-- Generated by scripts/audit.py; do not edit.", f"import {NAMESPACE}.Statements", "import Lean", helper]
    lines += [f"#check ({name} : Prop)" for name in sorted(checks)]
    for name in names:
        lines += [f"#print axioms {NAMESPACE}.{name}",
                  f'run_cmd {AUDIT_NAMESPACE}.inspect ``{NAMESPACE}.{name} "{name}"']
    return "\n".join(lines) + "\n"


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def status_notes(rows, checks):
    """The legend under the counts: it explains only the statuses and checks that this project has."""
    legend = []
    if any(row["status"].startswith("PROVED-GIVEN") for row in rows):
        legend.append("PROVED-GIVEN rows retain the named explicit computer-check hypotheses. A kernel-discharged proposition is removed from those public premises and identified in the check registry. Cited axioms remain listed even on conditional rows.")
    legend.append("CITED is a direct external restatement; PROVED-FROM-CITED is internally derived. OPEN and VIOLATION fail the final check.")
    inspection = ["Type inspection follows project definition aliases and structure constructor types."]
    if checks:
        inspection.append("Any check occurrence in a signature is conservatively treated as conditional and must occur in a binder type.")
    inspection.append("Semantic equivalence, source fidelity, non-vacuity and completeness still require the independent foundations review.")
    return " ".join(legend) + "\n\n" + " ".join(inspection) + "\n\n"


def check_section(checks):
    """The computer-check table, only when the project has computer-check propositions."""
    if not checks:
        return []
    return (["", "## Computer-check propositions and proof status", "",
             "These are ordinary propositions, never project axioms. Per-entry descriptions distinguish external checks from kernel-proved compatibility interfaces. The public mathematical certificate row records a discharged check; this audit does not execute or certify external programs.", "",
             "| Lean Prop | Description and external check evidence |", "|---|---|"] +
            [f'| `{row["name"]}` | {cell(row["doc"])} |' for row in checks])


def render(rows, checks, omitted):
    counts = {}
    for row in rows + omitted: counts[row["status"]] = counts.get(row["status"], 0) + 1
    table = ["| # | Lean name | Paper claim | Status | Cited axioms used |", "|---|---|---|---|---|"]
    for i, row in enumerate(rows, 1):
        cited = ", ".join(a for a in row["axioms"] if a.startswith(CITED)) or "—"
        table.append(f'| {i} | `{row["name"]}` | {cell(row["doc"])} | {cell(row["status"])} | {cell(cited)} |')
    table += check_section(checks)
    table += ["", "## NOT-FORMALIZED registry", "",
              "Every registered omission is counted separately, including background/method entries. An entry is not a proved theorem. Empty registry means no declared omissions, not automatic completeness of the paper inventory.", "",
              "| # | Kind | Reason and paper location | Status |", "|---|---|---|---|"]
    table += [f'| {row["name"]} | {cell(row["kind"])} | {cell(row["reason"])} | NOT-FORMALIZED |' for row in omitted]
    text = ("# Claim audit of Sheil/Paper/Statements.lean\nGenerated from Lean output by scripts/audit.py.\n\n" +
            ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + ".\n\n" +
            status_notes(rows, checks) + "\n".join(table) + "\n")
    return text, counts


def main_audit():
    text = STATEMENTS.read_text()
    items = parse_statements(text)
    omitted = parse_not_stated(text)
    check_file = PROJECT / LIB / "ComputerChecked.lean"
    checks = parse_checks(check_file.read_text()) if check_file.exists() else []
    names = [item["name"] for item in items]
    check_names = {item["name"] for item in checks}
    reviewed = load_reviewed(PROJECT / "scripts/cited_inputs.json")
    content = audit_lean(names, check_names)
    path = PROJECT / LIB / "Audit.lean"
    if not path.exists() or path.read_text() != content: path.write_text(content)
    proc = subprocess.run(LEAN_ENV + ["lake", "build", LIB + ".Audit"], cwd=PROJECT,
                          capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    (PROJECT / "scripts/audit_output.log").write_text(output)
    if proc.returncode: fail("Lean failed; see scripts/audit_output.log\n" + output)
    axioms = parse_axioms(output, names)
    dependencies = parse_dependencies(output, names, check_names)
    direct = parse_direct_inputs(output, names)
    for item in items: item["direct_cited_input"] = direct[item["name"]]
    rows = [dict(item, qualified_name=NAMESPACE + "." + item["name"], file=str(STATEMENTS.relative_to(PROJECT)),
                 axioms=sorted(axioms[item["name"]]),
                 checks=sorted(dependencies[item["name"]][1]),
                 status=classify(axioms[item["name"]], reviewed, item["direct_cited_input"], dependencies[item["name"]]))
            for item in items]
    report, counts = render(rows, checks, omitted)
    (PROJECT / "AUDIT.md").write_text(report)
    (PROJECT / "CLAIMS.json").write_text(json.dumps({"version": "0.30", "project": "025", "namespace": NAMESPACE,
        "counts": counts, "claims": rows, "computer_checks": checks, "not_formalized": omitted}, indent=2) + "\n")
    print("AUDIT: " + json.dumps(counts, sort_keys=True))
    if counts.get("VIOLATION"): fail("VIOLATION rows present")


def main_test():
    sample = "/-- Formula | bound. -/\ntheorem foo' : True := by trivial\n/-- external. -/\ntheorem quote : True := Cited.input\n/-! ## NOT stated\n(N1) [library] x.tex:3 no operator library; workaround considered.\n-/\nend " + NAMESPACE + "\n"
    rows = parse_statements(sample)
    assert [r["name"] for r in rows] == ["foo'", "quote"]
    assert rows[1]["direct_cited_input"] == CITED + "input"
    assert parse_not_stated(sample)[0]["status"] == "NOT-FORMALIZED"
    cc = '/-- COMPUTER-CHECKED: p.py/log. NOT proved in Lean. -/\ndef CheckA : Prop := True\n'
    assert parse_checks(cc)[0]["name"] == CHECKS + "CheckA"
    names = ["foo'", "quote"]
    out = (f"'{NAMESPACE}.foo'' depends on axioms: [propext,\n Classical.choice]\n"
           f"'{NAMESPACE}.quote' depends on axioms: [{CITED}input]")
    got = parse_axioms(out, names)
    allow = {CITED + "input"}
    assert classify(got["foo'"], allow) == "PROVED"
    assert classify(got["quote"], allow, CITED + "input") == "CITED"
    assert classify(got["quote"], allow) == "PROVED-FROM-CITED"
    check = CHECKS + "CheckA"
    assert classify({"propext"}, allow, dependencies=({check}, {check})) == "PROVED-GIVEN " + check
    assert classify({CITED + "input"}, allow, dependencies=({check}, {check})).startswith("PROVED-GIVEN ")
    assert classify(set(), allow, dependencies=({check}, set())) == "VIOLATION"
    for bad in ({"evil"}, {"evil", "sorryAx"}, {CITED + "not_reviewed"}, {CITED + "Temp.x"}):
        assert classify(bad, allow) == "VIOLATION"
    assert classify({"sorryAx"}, allow) == "OPEN"
    parsed = parse_dependencies("GKCHECK|foo'|||END\nGKCHECK|quote|"+check+"|"+check+"|END", names, {check})
    assert parsed["quote"] == ({check}, {check})
    assert "theorem" not in mask_comments('/- outer /- theorem -/ more -/ "theorem"')
    for bad in ["/-! ## NOT stated\n(N1) missing kind\n-/", "no registry"]:
        try: parse_not_stated(bad)
        except SystemExit: pass
        else: raise AssertionError("bad registry accepted")
    for bad in ['theorem foo : True := by trivial\n theorem hidden : True := by trivial',
                'lemma hidden : True := by trivial']:
        try: parse_statements(bad)
        except SystemExit: pass
        else: raise AssertionError("unsupported declaration accepted")
    for row in rows: row.update(status="PROVED", axioms=[])
    report, counts = render(rows, [], parse_not_stated(sample))
    assert "Formula \\| bound." in report and counts["NOT-FORMALIZED"] == 1
    assert "PROVED-GIVEN" not in report and "Computer-check" not in report and "check occurrence" not in report
    rows[0]["status"] = "PROVED-GIVEN " + check
    report, counts = render(rows, parse_checks(cc), [])
    assert "PROVED-GIVEN rows retain" in report and "## Computer-check propositions" in report
    assert "check occurrence" in report and CHECKS + "CheckA" in report
    print("PASS: audit parser, statuses, check metadata, citation rejection, registry and Markdown cells")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]: main_test()
    elif not sys.argv[1:]: main_audit()
    else: fail("usage: scripts/audit.py [--test]")
