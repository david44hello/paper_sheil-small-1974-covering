# Sheil-Small's (1974) covering problem has a positive answer — Lean 4 proof

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_sheil-small-1974-covering).

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch v3.20 --single-branch https://github.com/david44hello/paper_sheil-small-1974-covering.git
cd paper_sheil-small-1974-covering/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; statuses match the list.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The proof takes one published result as given: the coefficient bound of Theorem 3.4 (O'Hara and Rodriguez, Saff and Sheil-Small, Kristiansen), stated in Sheil/Cited/CoefHalfMax.lean; [AUDIT.md](AUDIT.md) and [AUDIT_NOTES.md](AUDIT_NOTES.md) show where it is used.

Copyright (C) Dave Goel 2026--now. All rights reserved.
