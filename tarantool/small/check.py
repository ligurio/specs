#!/usr/bin/env python3
"""Check the Alloy receipts produced by ``alloy exec``.

Usage: ``check.py RECEIPT [RECEIPT ...]``.

A ``check`` is expected to find no counterexample, a ``run`` to find an
instance; an explicit ``expect`` clause overrides this. Prints a verdict
per command and per receipt; exits 0 when everything passed, 1 when a
command failed, 2 on a usage/read error.
"""

import json
import sys
from pathlib import Path


def model_name(receipt: Path) -> str:
    if receipt.name.endswith(".json"):
        return receipt.name[: -len(".json")] + ".als"
    return receipt.name


def check_receipt(receipt: Path) -> bool:
    name = model_name(receipt)
    try:
        commands = json.loads(receipt.read_text()).get("commands", {})
    except (OSError, ValueError) as exc:
        print(f"[FAIL] {name}: cannot read {receipt}: {exc}")
        return False

    if not commands:
        print(f"[FAIL] {name}: no commands found")
        return False

    failed = 0
    for cmd, info in commands.items():
        ctype = info.get("type", "?")
        instances = sum(
            len(sol.get("instances", [])) for sol in info.get("solution", [])
        )
        expects = info.get("expects", -1)
        expected = expects if expects >= 0 else (0 if ctype == "check" else 1)
        want = 1 if expected > 0 else 0
        got = 1 if instances > 0 else 0
        if got == want:
            print(f"[ ok ] {name} :: {cmd} ({ctype}, instances={instances})")
        else:
            print(
                f"[FAIL] {name} :: {cmd} "
                f"({ctype}, instances={instances}, expected>0={want})"
            )
            failed += 1

    if failed:
        print(f"[FAIL] {name}: {failed} command(s) failed")
        return False
    print(f"[ ok ] {name}: {len(commands)} command(s)")
    return True


def main(argv: list[str]) -> int:
    if not argv:
        print("usage: check.py RECEIPT [RECEIPT ...]", file=sys.stderr)
        return 2

    ok = True
    for arg in argv:
        if not check_receipt(Path(arg)):
            ok = False

    if not ok:
        print("FAILED")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
