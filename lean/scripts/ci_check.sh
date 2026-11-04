#!/usr/bin/env bash
# ci_check.sh - the check GitHub runs for this folder: the final gate of check.sh (only the rows in OPEN_ROWS.txt may stay open).
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
exec bash scripts/check.sh --final
