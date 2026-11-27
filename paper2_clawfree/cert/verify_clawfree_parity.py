#!/usr/bin/env python3
"""
Standalone Zero-Float Parity & Hygiene Auditor for Flagship Paper 2 (`paper2_clawfree`).

Pure Python 3 standard library ONLY:
  - ZERO floats, ZERO complex literals, ZERO `float()` calls, ZERO `/` true-division
    (self-audited via Python `ast` on BOTH `verify_clawfree_eg.py` and this script).
  - ZERO imports from `research/`.
  - Hardened against `python3 -O` / `-OB`: explicit `__debug__` guard AND zero bare `assert`
    statements (uses `require(...)` raising `RuntimeError` so checks can NEVER be bypassed).

Checks performed:
  1. AST Zero-Float, Zero-`/`, and Zero-`research` Import Audit on `cert/verify_clawfree_eg.py`
     and `cert/verify_clawfree_parity.py`.
  2. Lean 4 Trust-Token & Axiom Coverage Audit across ALL `lean/**/*.lean` (INCLUDING `AxiomCheck.lean`):
     - ZERO `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`,
       `extern`, `partial`, or `set_option` outside comments (`#print axioms` lines permitted in
       `AxiomCheck.lean`);
     - 1-to-1 bijection between every public `theorem`/`lemma` in `lean/ClawFreeEG/*.lean` and
       `#print axioms` entries in `lean/AxiomCheck.lean` (zero missing, zero stale);
     - Optional `--check-axioms <lean-bin-dir>` live execution of `lake env lean AxiomCheck.lean`
       verifying every output line depends ONLY on `{propext, Classical.choice, Quot.sound}`.
  3. 1-to-1 Literal Data Parity (Lean <-> JSON <-> Python):
     - `F19` 210 lower-triangular stored entries (symmetric 20x20 extension, same-parity no-diagonal
       `|u1 - u2| != |v1 - v2|` domain: `DyadicPackingData.lean` <-> `dyadic_packing_2d.json`);
     - ALL `813` Case B simple-orbit quad-tree leaf coordinates (`0000:78, 1000:78, 1100:132,
       1010:126, 1110:249, 1111:150`) AND strictly-positive packed subdivision parameters for
       `1110` and `1111` (`DyadicCaseBData.lean` <-> `dyadic_packing_2d.json`);
     - Exact `IBoxTree` leaf counts (`46 = 19+11+9+7` Fourfold, `61 = 22+23+16` Equal-Med) in
       `TwoCycleData.lean`;
     - `equalTailBoxes16` (`TwoCycleData.lean` <-> `two_cycle_closure.json`);
     - Equal-block `k = 3, 4, 5` boxes (`PolyKData.lean` <-> `two_cycle_closure.json`);
     - `F_11`, `H_14`, `G_39` adjacency/edges/bags/tree-edges/`V4`/`C16`/`K_5`-minor branch sets
       AND all `4 + 128 + 2048 = 2180` expanded-port cycle witnesses
       (`Treewidth3Data.lean` <-> `tw3_and_g39.json`);
     - Tier-1 Hamiltonian All-Chord-`B` `39` periods & `23` open odd `(g, m)` pairs
       (`Treewidth3AndBowties.lean` <-> `hamiltonian_all_chord_b.json`).
"""

import argparse
import ast
import json
import os
import re
import subprocess
import sys
from pathlib import Path


PAPER_ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = PAPER_ROOT.joinpath("cert")
WIT_DIR = CERT_DIR.joinpath("witnesses")
LEAN_DIR = PAPER_ROOT.joinpath("lean")
MOD_DIR = LEAN_DIR.joinpath("ClawFreeEG")

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(cond, msg):
    """Unconditional check that CANNOT be stripped by `python3 -O`."""
    if not cond:
        raise RuntimeError(f"PARITY AUDIT FAILURE: {msg}")


def strip_lean_comments(src):
    """Remove Lean 4 block comments `/- ... -/` (nested) and line comments `-- ...`."""
    out = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth == 0:
            if in_str:
                out.append(ch)
                if ch == "\\" and i + 1 < n:
                    out.append(nxt)
                    i += 2
                    continue
                if ch == '"':
                    in_str = False
                i += 1
                continue
            if ch == '"':
                in_str = True
                out.append(ch)
                i += 1
                continue
            if ch == "-" and nxt == "-":
                while i < n and src[i] != "\n":
                    i += 1
                continue
            if ch == "/" and nxt == "-":
                depth = 1
                i += 2
                continue
            out.append(ch)
            i += 1
        else:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
    return "".join(out)


def audit_python_ast(path):
    """Enforce zero float/complex literals, zero float(), zero `/` ast.Div, zero research imports."""
    src = path.read_text(encoding="utf-8")
    tree = ast.parse(src, filename=str(path))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            raise RuntimeError(f"Float/complex literal in {path}:{node.lineno}: {node.value!r}")
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            raise RuntimeError(f"Forbidden `/` (ast.Div) in {path}:{node.lineno}")
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Div):
            raise RuntimeError(f"Forbidden `/=` (ast.Div) in {path}:{node.lineno}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            raise RuntimeError(f"Forbidden float() call in {path}:{node.lineno}")
        if isinstance(node, ast.Import):
            for alias in node.names:
                if "research" in alias.name:
                    raise RuntimeError(f"Forbidden research import in {path}:{node.lineno}")
        if isinstance(node, ast.ImportFrom):
            if node.module and "research" in node.module:
                raise RuntimeError(f"Forbidden research import in {path}:{node.lineno}")


def audit_lean_trust_and_axioms():
    """Verify zero forbidden trust tokens (including AxiomCheck.lean) and exact 1-to-1 AxiomCheck coverage."""
    forbidden_re = re.compile(
        r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|partial|set_option)\b"
    )
    lean_files = sorted(LEAN_DIR.rglob("*.lean"))
    lean_files = [p for p in lean_files if ".lake" not in p.parts]
    require(bool(lean_files), "No Lean files found!")

    axiom_check_path = LEAN_DIR.joinpath("AxiomCheck.lean")
    require(axiom_check_path.exists(), "AxiomCheck.lean missing!")
    axiom_raw = axiom_check_path.read_text(encoding="utf-8")
    axiom_cleaned = strip_lean_comments(axiom_raw)
    axiom_no_str = re.sub(r'"(?:\\.|[^"\\])*"', '""', axiom_cleaned)

    # Scan AxiomCheck.lean too! Permit `#print axioms <ident>` lines, forbid all trust tokens & `axiom` decls.
    for lineno, line in enumerate(axiom_no_str.splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("import "):
            continue
        if re.match(r"^#print\s+axioms\s+[A-Za-z0-9_.']+$", stripped):
            continue
        m = forbidden_re.search(stripped)
        require(m is None, f"Forbidden token {m.group(1) if m else ''!r} in AxiomCheck.lean:{lineno}")
        raise RuntimeError(f"Unexpected non-`#print axioms` code in AxiomCheck.lean:{lineno}: {stripped!r}")

    printed_list = re.findall(r"^#print\s+axioms\s+([A-Za-z0-9_.']+)$", axiom_no_str, re.MULTILINE)
    printed_axioms = set(printed_list)
    require(len(printed_list) == len(printed_axioms), "Duplicate `#print axioms` entries in AxiomCheck.lean!")

    ns_re = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)", re.MULTILINE)

    total_public = 0
    missing = []
    matched_printed = set()
    for path in lean_files:
        if path == axiom_check_path:
            continue
        raw = path.read_text(encoding="utf-8")
        cleaned = strip_lean_comments(raw)
        cleaned_no_str = re.sub(r'"(?:\\.|[^"\\])*"', '""', cleaned)
        m = forbidden_re.search(cleaned_no_str)
        require(m is None, f"Forbidden Lean trust token {m.group(1) if m else ''!r} in {path}")

        if path.parent != MOD_DIR:
            continue
        ns_matches = ns_re.findall(cleaned)
        prefix = ns_matches[0] if ns_matches else "ClawFreeEG"
        for line in cleaned.splitlines():
            stripped = line.strip()
            if stripped.startswith("private "):
                continue
            tm = re.match(r"^(?:@\[[^\]]+\]\s*)*(?:theorem|lemma)\s+([A-Za-z0-9_.']+)", stripped)
            if tm:
                name = tm.group(1)
                total_public += 1
                candidates = {
                    f"{prefix}.{name}",
                    f"ClawFreeEG.{name}",
                    f"ClawFreeEG.FinGraph.{name}",
                    name,
                }
                hits = candidates & printed_axioms
                if not hits:
                    missing.append((path.name, name))
                else:
                    matched_printed.update(hits)

    require(not missing, f"Public theorems missing from AxiomCheck.lean ({len(missing)}): {missing[:10]}")
    stale = sorted(printed_axioms - matched_printed)
    require(not stale, f"Stale/unmatched `#print axioms` entries in AxiomCheck.lean ({len(stale)}): {stale[:10]}")
    require(total_public == len(printed_axioms), f"Public theorem count {total_public} != printed axioms {len(printed_axioms)}")
    return len(lean_files), total_public, len(printed_axioms)


def run_live_axiom_check(lean_sysroot, expected_count):
    """Optionally run `lake env lean AxiomCheck.lean` and verify every theorem's axioms."""
    lake_bin = Path(lean_sysroot).joinpath("bin", "lake")
    require(lake_bin.exists(), f"lake binary not found at {lake_bin}")
    env = dict(os.environ)
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_SYSROOT"] = str(lean_sysroot)
    proc = subprocess.run(
        [str(lake_bin), "env", "lean", "AxiomCheck.lean"],
        cwd=str(LEAN_DIR),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    require(proc.returncode == 0, f"AxiomCheck.lean failed (exit {proc.returncode}): {proc.stderr or proc.stdout}")
    lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
    require(len(lines) == expected_count, f"Expected {expected_count} axiom lines, got {len(lines)}")
    for ln in lines:
        if ln.endswith("does not depend on any axioms"):
            continue
        m = re.match(r"^'[^']+' depends on axioms: \[([^\]]*)\]$", ln)
        require(m is not None, f"Unexpected AxiomCheck output line: {ln!r}")
        axioms = {tok.strip() for tok in m.group(1).split(",") if tok.strip()}
        disallowed = axioms - ALLOWED_AXIOMS
        require(not disallowed, f"Disallowed axioms {disallowed} in line: {ln!r}")
    return len(lines)


def extract_lean_def_block(src, def_name):
    """Extract the right-hand side of a top-level `def <def_name> ... := ...` until next top-level decl."""
    pat = re.compile(rf"^def\s+{re.escape(def_name)}\b[^\n]*?:=\s*", re.MULTILINE)
    m = pat.search(src)
    require(m is not None, f"Could not find `def {def_name}`")
    start = m.end()
    end_pat = re.compile(r"\n(?:def|theorem|private|/--|/-!|end\s)", re.MULTILINE)
    em = end_pat.search(src, start)
    return src[start:em.start()] if em else src[start:]


def parse_nat_list_list(text):
    """Parse Lean `[[1, 2], [3, 4]]` literal into Python list of lists of ints."""
    i = text.find("[")
    require(i >= 0, "Expected `[` in list-of-lists literal")
    depth = 0
    end = -1
    for j in range(i, len(text)):
        if text[j] == "[":
            depth += 1
        elif text[j] == "]":
            depth -= 1
            if depth == 0:
                end = j + 1
                break
    require(end > i, "Unterminated list-of-lists literal")
    return ast.literal_eval(text[i:end])


def parse_pair_list(text):
    """Parse Lean `[(a, b), ...]` literal into Python list of `[a, b]`."""
    i = text.find("[")
    require(i >= 0, "Expected `[` in pair-list literal")
    j = text.find("]", i)
    require(j > i, "Unterminated pair-list literal")
    return [list(p) for p in ast.literal_eval(text[i:j + 1])]


def parse_tail_boxes(text):
    """Parse Lean `List TailBox` literal `⟨reg, n, k, ⟨xln, xld⟩, ⟨xhn, xhd⟩, ⟨yln, yld⟩, ⟨yhn, yhd⟩⟩`."""
    pat = re.compile(
        r"⟨\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,"
        r"\s*⟨\s*(\d+)\s*,\s*(\d+)\s*⟩\s*,"
        r"\s*⟨\s*(\d+)\s*,\s*(\d+)\s*⟩\s*,"
        r"\s*⟨\s*(\d+)\s*,\s*(\d+)\s*⟩\s*,"
        r"\s*⟨\s*(\d+)\s*,\s*(\d+)\s*⟩\s*⟩"
    )
    boxes = []
    for m in pat.finditer(text):
        vals = [int(g) for g in m.groups()]
        boxes.append({
            "regime": vals[0],
            "n": vals[1],
            "k": vals[2],
            "xlo": [vals[3], vals[4]],
            "xhi": [vals[5], vals[6]],
            "ylo": [vals[7], vals[8]],
            "yhi": [vals[9], vals[10]],
        })
    return boxes


def parse_ntree(text):
    """Parse Lean `NTree` literal `(.n a b)` / `(.l v)` into nested tuples / ints."""
    tokens = re.findall(r"\(|\)|\.n|\.l|\d+", text)
    pos = 0

    def parse():
        nonlocal pos
        tok = tokens[pos]
        if tok == "(":
            pos += 1
            res = parse()
            require(tokens[pos] == ")", f"Expected `)` in NTree, got {tokens[pos]!r}")
            pos += 1
            return res
        if tok == ".l":
            pos += 1
            val = int(tokens[pos])
            pos += 1
            return val
        if tok == ".n":
            pos += 1
            left = parse()
            right = parse()
            return (left, right)
        raise RuntimeError(f"Unexpected NTree token: {tok!r}")

    return parse()


def ntree_get(tree, idx):
    """Evaluate `NTree.get` matching `DyadicPackingData.NTree.get`."""
    while isinstance(tree, tuple):
        tree = tree[0] if (idx % 2 == 0) else tree[1]
        idx //= 2
    return tree


def parse_case_b_leaves(text):
    """Extract all `(.leaf s1l s1h s2l s2h curD k1 k2)` tuples from a CellForest Lean def."""
    pat = re.compile(r"\.leaf\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)")
    return [tuple(int(g) for g in m.groups()) for m in pat.finditer(text)]


def count_ibox_leaves(text):
    """Count `.leaf` constructor occurrences in an `IBoxTree` Lean def."""
    return len(re.findall(r"\.leaf\s+\d+\s+\d+\s+\d+\s+\d+", text))


def audit_data_parity():
    """Verify exact 1-to-1 literal data parity across Lean, JSON witnesses, and Python."""
    # 1. F19 210 lower-triangular stored entries (symmetric 20x20 extension):
    dp_json = json.loads(WIT_DIR.joinpath("dyadic_packing_2d.json").read_text(encoding="utf-8"))
    dp_lean = MOD_DIR.joinpath("DyadicPackingData.lean").read_text(encoding="utf-8")
    f19_json = dp_json["F19"]
    require(len(f19_json) == 20, f"Expected 20 F19 rows, got {len(f19_json)}")
    f19_block = extract_lean_def_block(dp_lean, "f19Tree")
    f19_tree = parse_ntree(f19_block)
    f19_checked = 0
    for w1 in range(20):
        require(len(f19_json[w1]) == w1 + 1, f"F19 row {w1} length mismatch")
        for w2 in range(w1 + 1):
            require(
                ntree_get(f19_tree, w1 * 20 + w2) == f19_json[w1][w2],
                f"F19 mismatch at ({w1}, {w2})",
            )
            f19_checked += 1
    require(f19_checked == 210, f"Expected 210 F19 stored entries, got {f19_checked}")

    # 2. All 813 Case B simple-orbit quad-tree leaf coordinates & packed subdivision guards:
    cb_lean = MOD_DIR.joinpath("DyadicCaseBData.lean").read_text(encoding="utf-8")
    expected_cb_counts = {
        "0000": (["forest0000"], 78),
        "1000": (["forest1000"], 78),
        "1100": (["forest1100"], 132),
        "1010": (["forest1010"], 126),
        "1110": ([f"forest1110_c{i}" for i in range(8)], 249),
        "1111": ([f"forest1111_c{i}" for i in range(4)], 150),
    }
    cb_total = 0
    for orbit, (def_names, exp_cnt) in expected_cb_counts.items():
        lean_leaves = []
        for dn in def_names:
            lean_leaves.extend(parse_case_b_leaves(extract_lean_def_block(cb_lean, dn)))
        require(len(lean_leaves) == exp_cnt, f"Orbit {orbit} Lean leaf count {len(lean_leaves)} != {exp_cnt}")
        # Verify strictly-positive packed subdivision parameters for 1110 and 1111:
        for s1l, s1h, s2l, s2h, curD, k1, k2 in lean_leaves:
            require(curD > 0 and 144 % curD == 0, f"Orbit {orbit} invalid denominator {curD}")
            if orbit == "1110":
                require(
                    k1 // 16 > 0 and k1 % 16 > 0 and k2 // 16 > 0 and k2 % 16 > 0,
                    f"Orbit 1110 leaf has zero packed param: {(k1, k2)}",
                )
            elif orbit == "1111":
                require(
                    k1 // 16 > 0 and k1 % 16 > 0,
                    f"Orbit 1111 leaf has zero packed param: {k1}",
                )
        lean_geom = sorted(list(t[:5]) for t in lean_leaves)
        json_geom = sorted(entry[:5] for entry in dp_json["case_b_leaves_simple"][orbit])
        require(lean_geom == json_geom, f"Orbit {orbit} leaf coordinate mismatch between Lean and JSON!")
        cb_total += len(lean_leaves)
    require(cb_total == 813, f"Expected 813 Case B simple leaves, got {cb_total}")

    # 3. Exact IBoxTree leaf counts (46 Fourfold = 19+11+9+7; 61 Equal-Med = 22+23+16) & equalTailBoxes16:
    tc_json = json.loads(WIT_DIR.joinpath("two_cycle_closure.json").read_text(encoding="utf-8"))
    tc_lean = MOD_DIR.joinpath("TwoCycleData.lean").read_text(encoding="utf-8")

    ff_expected = {32: 19, 64: 11, 128: 9, 256: 7}
    ff_total = 0
    for m1, exp in ff_expected.items():
        cnt = sum(count_ibox_leaves(extract_lean_def_block(tc_lean, f"fourfoldTree_{m1}_r{r}")) for r in range(4))
        require(cnt == exp, f"Fourfold M1={m1} IBoxTree leaf count {cnt} != {exp}")
        ff_total += cnt
    require(ff_total == 46, f"Fourfold total IBoxTree leaves {ff_total} != 46")

    em_expected = {256: 22, 512: 23, 1024: 16}
    em_total = 0
    for m_val, exp in em_expected.items():
        cnt = sum(count_ibox_leaves(extract_lean_def_block(tc_lean, f"equalMedTree_{m_val}_r{r}")) for r in range(4))
        require(cnt == exp, f"EqualMed M={m_val} IBoxTree leaf count {cnt} != {exp}")
        em_total += cnt
    require(em_total == 61, f"EqualMed total IBoxTree leaves {em_total} != 61")

    lean_tail16 = parse_tail_boxes(extract_lean_def_block(tc_lean, "equalTailBoxes16"))
    require(len(lean_tail16) == 16 and lean_tail16 == tc_json["equal_tail_boxes"], "equalTailBoxes16 parity mismatch!")

    # 4. Equal-block k = 3, 4, 5 boxes: PolyKData.lean <-> two_cycle_closure.json
    pk_lean = MOD_DIR.joinpath("PolyKData.lean").read_text(encoding="utf-8")
    for k_str, def_name, expected_cnt in (
        ("3", "equalK3Boxes17", 17),
        ("4", "equalK4Boxes17", 17),
        ("5", "equalK5Boxes16", 16),
    ):
        lean_boxes = parse_tail_boxes(extract_lean_def_block(pk_lean, def_name))
        json_boxes = tc_json["equal_k_boxes"][k_str]["boxes"]
        require(len(lean_boxes) == expected_cnt and lean_boxes == json_boxes, f"{def_name} parity mismatch!")

    # 5. G_39 / H_14 / F_11 & all 4 + 128 + 2048 port-kill witnesses: Treewidth3Data.lean <-> tw3_and_g39.json
    tw_json = json.loads(WIT_DIR.joinpath("tw3_and_g39.json").read_text(encoding="utf-8"))
    tw_lean = MOD_DIR.joinpath("Treewidth3Data.lean").read_text(encoding="utf-8")

    require(parse_pair_list(extract_lean_def_block(tw_lean, "f11Edges")) == tw_json["F11_edges"], "f11Edges mismatch")
    require(parse_nat_list_list(extract_lean_def_block(tw_lean, "f11Tw3Bags")) == tw_json["F11_tw3_bags"], "f11Tw3Bags mismatch")
    require(parse_pair_list(extract_lean_def_block(tw_lean, "f11Tw3TreeEdges")) == tw_json["F11_tw3_tree_edges"], "f11Tw3TreeEdges mismatch")
    require(parse_nat_list_list(extract_lean_def_block(tw_lean, "h14Adj")) == tw_json["H14_adj"], "h14Adj mismatch")
    require(parse_pair_list(extract_lean_def_block(tw_lean, "h14Bowties")) == tw_json["H14_bowties"], "h14Bowties mismatch")
    require(parse_nat_list_list(extract_lean_def_block(tw_lean, "h14K5BranchSets")) == tw_json["H14_k5_branch_sets"], "h14K5BranchSets mismatch")
    require(parse_nat_list_list(extract_lean_def_block(tw_lean, "g39Adj")) == tw_json["G39_adj"], "g39Adj mismatch")
    require(ast.literal_eval(extract_lean_def_block(tw_lean, "g39V4").strip()) == tw_json["G39_v4"], "g39V4 mismatch")
    require(ast.literal_eval(extract_lean_def_block(tw_lean, "g39C16").strip()) == tw_json["G39_c16"], "g39C16 mismatch")
    require(parse_nat_list_list(extract_lean_def_block(tw_lean, "g39K5BranchSets")) == tw_json["G39_k5_branch_sets"], "g39K5BranchSets mismatch")

    lean_deg3 = parse_nat_list_list(extract_lean_def_block(tw_lean, "deg3TriCycles"))
    json_deg3 = [w["cycle"] for w in tw_json["port_witnesses"]["deg3_tri"]]
    require(len(lean_deg3) == 4 and lean_deg3 == json_deg3, "deg3TriCycles mismatch")

    lean_k23 = (
        parse_nat_list_list(extract_lean_def_block(tw_lean, "k23Cycles_0"))
        + parse_nat_list_list(extract_lean_def_block(tw_lean, "k23Cycles_1"))
    )
    json_k23 = [w["cycle"] for w in tw_json["port_witnesses"]["K23"]]
    require(len(lean_k23) == 128 and lean_k23 == json_k23, "k23Cycles mismatch")

    tw_q3a = MOD_DIR.joinpath("Treewidth3Q3DataA.lean").read_text(encoding="utf-8")
    tw_q3b = MOD_DIR.joinpath("Treewidth3Q3DataB.lean").read_text(encoding="utf-8")
    lean_q3 = []
    for c in range(8):
        lean_q3.extend(parse_nat_list_list(extract_lean_def_block(tw_q3a, f"q3MinusVCycles_{c}")))
    for c in range(8, 16):
        lean_q3.extend(parse_nat_list_list(extract_lean_def_block(tw_q3b, f"q3MinusVCycles_{c}")))
    json_q3 = [w["cycle"] for w in tw_json["port_witnesses"]["Q3_minus_v"]]
    require(len(lean_q3) == 2048 and lean_q3 == json_q3, "q3MinusVCycles mismatch")

    # Independent-bowtie 120 count parity in tw3_and_g39.json
    ib120 = tw_json["independent_bowtie_120"]
    require(ib120["lifted_h_configs"] == 360612, f"Expected 360612 lifted_h_configs, got {ib120['lifted_h_configs']}")
    require(sum(ib120["extra_vertex_overlaps"].values()) == 166, "Expected 166 extra_vertex_overlaps")

    # 6. Tier-1 Hamiltonian All-Chord-B constants: Treewidth3AndBowties.lean <-> hamiltonian_all_chord_b.json
    ham_json = json.loads(WIT_DIR.joinpath("hamiltonian_all_chord_b.json").read_text(encoding="utf-8"))
    tw_main = MOD_DIR.joinpath("Treewidth3AndBowties.lean").read_text(encoding="utf-8")
    lean_periods = ast.literal_eval(extract_lean_def_block(tw_main, "tier1All39Periods").strip())
    require(len(lean_periods) == 39 and lean_periods == ham_json["all_39_periods"], "tier1All39Periods mismatch")
    lean_odd23 = parse_pair_list(extract_lean_def_block(tw_main, "tier1OddOpen23"))
    require(len(lean_odd23) == 23 and lean_odd23 == ham_json["odd_open_cases"], "tier1OddOpen23 mismatch")
    require(ham_json["arbitrary_matching_104_128_rim_hit"] == 256, "rim_hit mismatch")
    require(ham_json["arbitrary_matching_le102_leaves"] == 641, "le102_leaves mismatch")
    require(ham_json["odd_open_visits"] == 93902, "odd_open_visits mismatch")
    require(ham_json["strip_visits"]["W31_L17"] == 29357, "W31_L17 visits mismatch")
    require(
        ham_json["arbitrary_matching_130_136_visits"] == {"130": 73, "132": 236, "134": 242, "136": 723},
        "arbitrary_matching_130_136_visits mismatch",
    )

    return {
        "f19_entries": f19_checked,
        "case_b_simple_leaves": cb_total,
        "fourfold_ibox_leaves": ff_total,
        "equal_med_ibox_leaves": em_total,
        "tail_boxes": len(lean_tail16),
        "equal_k_boxes": 17 + 17 + 16,
        "port_cycles": len(lean_deg3) + len(lean_k23) + len(lean_q3),
        "tier1_periods": len(lean_periods),
        "tier1_odd_open": len(lean_odd23),
    }


def main():
    if not __debug__:
        raise RuntimeError("Refusing to run with -O (assertions disabled); parity audit cannot be bypassed.")

    parser = argparse.ArgumentParser(description="Standalone Zero-Float Parity & Hygiene Auditor for Paper 2")
    parser.add_argument(
        "--check-axioms",
        type=Path,
        default=None,
        help="Optional Lean sysroot path to execute `lake env lean AxiomCheck.lean` live and audit every axiom line",
    )
    args = parser.parse_args()

    # 1. AST zero-float / zero-`/` / zero-research audit on BOTH cert scripts
    for py_path in (CERT_DIR.joinpath("verify_clawfree_eg.py"), Path(__file__).resolve()):
        audit_python_ast(py_path)
    print("PASS [1/3] AST Zero-Float, Zero-`/`, & Zero-research Audit (verify_clawfree_eg.py & verify_clawfree_parity.py)")

    # 2. Lean trust-token (incl. AxiomCheck.lean) & exact 1-to-1 AxiomCheck coverage audit
    n_files, n_pub, n_axioms = audit_lean_trust_and_axioms()
    live_note = ""
    if args.check_axioms is not None:
        n_live = run_live_axiom_check(args.check_axioms, n_axioms)
        live_note = f", live AxiomCheck verified {n_live}/{n_live}"
    print(
        f"PASS [2/3] Lean Trust-Token & AxiomCheck Audit "
        f"({n_files} Lean files incl. AxiomCheck.lean, {n_pub} public theorems, {n_axioms} #print axioms{live_note})"
    )

    # 3. 1-to-1 literal data parity across Lean <-> JSON <-> Python
    stats = audit_data_parity()
    print(
        f"PASS [3/3] 1-to-1 Literal Data Parity (F19={stats['f19_entries']}, "
        f"CaseB={stats['case_b_simple_leaves']}, IBoxTree={stats['fourfold_ibox_leaves']}+{stats['equal_med_ibox_leaves']}, "
        f"tailBoxes={stats['tail_boxes']}, equalKBoxes={stats['equal_k_boxes']}, "
        f"portCycles={stats['port_cycles']} [4+128+2048], G39/H14/F11 exact, "
        f"Tier1Periods={stats['tier1_periods']}, oddOpen={stats['tier1_odd_open']})"
    )
    print("ALL PAPER 2 PARITY & HYGIENE CHECKS PASSED!")


if __name__ == "__main__":
    main()
