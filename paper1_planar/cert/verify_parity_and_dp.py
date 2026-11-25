#!/usr/bin/env python3
"""Standalone Zero-Float Parity, Weighted DP-Collapse, & Weld-Invariant Verifier for Paper 1.

Pure Python 3 standard library ONLY. ZERO floats, ZERO true-division `/` operator
(AST-guarded), ZERO `research/` imports, ZERO brittle line-number hooks.

Independently verifies:
  1. Lean 4 source trust-token scan (zero sorry/admit/axiom/native_decide/unsafe/extern/partial);
  2. Exact F_10 5-triangle combinatorics (252 x 123 = 30,996 pairs, 2,136 admissible, max 47/12 < 4);
  3. Full literal parity across Lean 4 data modules, `cert/witnesses/*.json`, and live replay of
     `cert/verify_planar_eg.py` (all 7 BF potentials + relaxed core, all 3 sharpness witnesses +
     119-v 1-sums, all 51 chain shift spectra, all 108 d=17 residuals, and all 6,772 strict-schema
     explicit simple dyadic-cycle weld/rim entries: 114 + 5 + 1,327 + 520 + 1,260 + 3,501 + 45);
  4. All 12 weighted forward-simulation checks linking uncollapsed C5-free (d in {9..14, 17}) and
     C6-free (d in {9, 11..14}) DPs to the packed Lean automata;
  5. Exact Lemma 3.1 boundary-regularity invariant (connected face-edge graph, e in {0, 2}, and
     e = 0 => c = 3) across all 844/844 production `enum_planar_welds` calls, plus the repaired
     hereditary pinched-triangle weld emission test;
  6. Supplemental Stage-8 manuscript subaudits:
     - Cubic `Triad-D1(X=10, Z_1=7, Z_2=6)` exact 4-edge seal welds (461 welds, 0 survivors);
     - Cubic d = 9 `((h6o or h6s) and hP)` and `(hTri and n6 >= 2)` boundary welds (87 welds, 0 surv);
     - Cubic d = 17 `6o` 112-case contact weld audit (110/112 killed outright, 2 antipodal survivors
       eliminating all remaining +1 triangle placements);
     - Cubic d = 14, 18 `6o` 1-drop from `five_i` replay (357 and 5,232 words, 0 survivors);
     - Cubic d = 17 `TP_s3` restricted `(0, 1, 2, 3)` post-sieve replay (7,924 overweight, 7,080 with
       isolated triangle, 496 post-sieve residuals, 496/496 with isolated triangle);
     - Complete C5-free Stage-3 outer-rim capacity exclusions across Case (1), Case (2), Case (4c),
       universal `(T, H_6, X in {6, 9, 10})`, `(6, 6, 9)`, and cubic/non-cubic Mini-Corannulene.

Usage:
  python3 -B publication/paper1_planar/cert/verify_parity_and_dp.py
"""

import ast
import copy
import json
import re
import resource
import sys
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from pathlib import Path
from time import monotonic_ns

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT.joinpath("lean")
CERT = ROOT.joinpath("cert")
BIAS = 65536
WEIGHT_RADIX = 131072


def check_zero_floats():
    src = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(src, filename=__file__)
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and type(node.value).__name__ in ("float", "complex"):
            raise AssertionError(f"Forbidden float/complex literal: {node.value!r}")
        if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Div):
            raise AssertionError("Forbidden true-division `/` operator (use Fraction, //, or joinpath)")
        if isinstance(node, ast.Name) and node.id == "float":
            raise AssertionError("Forbidden float identifier")


def strip_lean_comments(source):
    token = re.compile(r'/-|-/|--[^\n]*|"(?:\\.|[^"\\])*"')
    start = 0
    pieces = []
    while match := token.search(source, start):
        pieces.append(source[start:match.start()])
        start = match.end()
        if match[0] == "/-":
            depth = 1
            while depth:
                delimiter = re.compile(r'/-|-/').search(source, start)
                assert delimiter is not None, "Unclosed Lean comment"
                depth += 1 if delimiter[0] == "/-" else -1
                start = delimiter.end()
            pieces.append("\n" * source[match.start():start].count("\n"))
        elif match[0].startswith("--"):
            pass
        else:
            pieces.append(" " * len(match[0]))
    pieces.append(source[start:])
    return "".join(pieces)


def source_data():
    definitions = {}
    for path in sorted(LEAN.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        source = path.read_text(encoding="utf-8")
        code = strip_lean_comments(source)
        forbidden = re.search(
            r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|partial)\b',
            code,
        )
        assert forbidden is None, (path, forbidden)
        for option in re.findall(r'\bset_option[^\n]*', code):
            assert option.strip() in (
                "set_option maxRecDepth 4096",
                "set_option maxRecDepth 4096 in",
            ), option
        if path.parent.name != "PlanarEG":
            continue
        for match in re.finditer(
            r'^(?:private )?(?:noncomputable )?def (\w+)[^\n]*?:=\s*(\[)',
            source,
            re.M,
        ):
            pos = match.start(2)
            depth = 0
            for end in range(pos, len(source)):
                depth += (source[end] == "[") - (source[end] == "]")
                if depth == 0:
                    break
            definitions[match[1]] = source[pos:end + 1]
        for name, tree in re.findall(
            r'^noncomputable def (\w+) : NTree :=\s*([^\n]+)', source, re.M
        ):
            definitions[name] = tree
    return definitions


def literal(defs, name):
    return ast.literal_eval(defs[name])


def packed(defs, name):
    return [n for chunk in re.findall(r'\w+', defs[name]) for n in literal(defs, chunk)]


def unpack(number):
    endpoints, weight = divmod(number, WEIGHT_RADIX)
    return (*divmod(endpoints, 4096), weight - BIAS)


def tree_values(source):
    tokens = iter(re.findall(r'\.n|\.l|\d+', source))

    def parse():
        kind = next(tokens)
        if kind == ".l":
            return int(next(tokens)) - BIAS
        assert kind == ".n", kind
        return parse(), parse()

    tree = parse()
    assert next(tokens, None) is None
    return tree


def lookup(tree, node):
    while isinstance(tree, tuple):
        node, bit = divmod(node, 2)
        tree = tree[bit]
    return tree


def compare_bf(defs, bundle):
    names = {
        "cubic_d33": "d33",
        "cubic_frozen_cap": "frz",
        "c5free_d18": "c5D18",
        "c5free_frozen_cap": "c5Frz",
        "c6free_d15": "c6D15",
        "c6free_frozen_cap": "c6Frz",
    }
    for key, prefix in names.items():
        data = bundle[key]
        nodes = data["nodes"]
        ids = {node: i for i, node in enumerate(nodes)}
        edges = Counter((ids[u], ids[v], w) for u, v, w in data["edges"])
        lean = Counter(map(unpack, packed(defs, prefix + "Edges")))
        pi = tree_values(defs[prefix + "Pi"])
        assert edges == lean, key
        assert all(lookup(pi, i) == data["pi"][x] for i, x in enumerate(nodes)), key
        if key == "cubic_frozen_cap":
            core = Counter({edge: count for edge, count in edges.items() if 0 not in edge[:2]})
            relaxed = Counter(map(unpack, packed(defs, "frzRelCoreEdges")))
            initial = literal(defs, "frzRelInitPairs")
            reach = {pair // WEIGHT_RADIX for pair in initial}
            while True:
                enlarged = reach | {v for u, v, _ in core if u in reach}
                if enlarged == reach:
                    break
                reach = enlarged
            live = Counter({edge: count for edge, count in core.items() if edge[0] in reach})
            assert live == relaxed and reach == {ids[node] for node in data["relaxed_pi"]}
            pi_r = tree_values(defs["frzRelPi"])
            assert all(
                lookup(pi_r, ids[x]) == Fraction(*p) * data["scale"]
                for x, p in data["relaxed_pi"].items()
            )
    print("PASS BF Parity: all 6 packed BF models + cubic relaxed core (1,351 reachable arcs) match.")


def normalize_faces(faces):
    labels = {v: i for i, v in enumerate(sorted({v for face in faces for v in face}))}
    return tuple(tuple(labels[v] for v in face) for face in faces)


def compare_sharp(defs, sharp, verifier):
    src = LEAN.joinpath("PlanarEG", "SharpData.lean").read_text(encoding="utf-8")
    for name, prefix, length, forbidden in (
        ("G168", "g168", 32, {4, 8, 16}),
        ("C60", "c60", 16, {3, 4, 8}),
        ("TD60", "td60", 16, set(range(4, 10))),
    ):
        data = sharp[name]
        body = src.split(f"def {prefix}Nbrs ", 1)[1].split("\ndef ", 1)[0]
        rows = [
            tuple(map(int, match))
            for match in re.findall(r"^ +\((\d+), (\d+), (\d+)\)$", body, re.M)
        ]
        edges = {(u, v) for u, row in enumerate(rows) for v in row if u < v}
        assert edges == {tuple(edge) for edge in data["edges"]}, name
        faces = literal(defs, f"{prefix}Faces")
        assert faces == data["faces"] and literal(defs, f"{prefix}C{length}") == data[f"c{length}"]
        turn = defaultdict(dict)
        for face in faces:
            for i, u in enumerate(face):
                predecessor, successor = face[i - 1], face[(i + 1) % len(face)]
                assert predecessor not in turn[u]
                turn[u][predecessor] = successor
        for u, row in enumerate(rows):
            a, b, c = row
            assert set(turn[u]) == set(row)
            assert (turn[u][a], turn[u][b], turn[u][c]) in ((b, c, a), (c, a, b))
        if name != "G168":
            doubled = edges | {(0 if u == 0 else u + 59, v + 59) for u, v in edges}
            graph = verifier["make_adj_from_pairs"](119, doubled)
            assert len(graph[0]) == max(map(len, graph)) == 6 and min(map(len, graph)) == 3
            assert not verifier["bounded_cycles"](graph, forbidden)
            assert verifier["find_cycle_witness"](graph, {16})
    print("PASS Sharpness Parity: G168, C60 (+119v 1-sum), and TD60 (+119v 1-sum) match across Lean/Python/JSON.")


def lean_welds(defs, names, targets):
    rows = []
    pattern = r'⟨(\d+),\s*(\[\[.*?\]\]),\s*(\[[\d, ]+\])⟩'
    for name in names:
        assert name in defs, name
        matches = re.findall(pattern, defs[name])
        assert len(matches) == defs[name].count("⟨"), name
        for order, faces, cycle in matches:
            faces_l, cycle_l = ast.literal_eval(faces), ast.literal_eval(cycle)
            vertices = {v for face in faces_l for v in face}
            assert vertices == set(range(int(order))), name
            assert all(len(face) >= 3 and len(set(face)) == len(face) for face in faces_l), name
            edges = {
                frozenset((a, b))
                for face in faces_l
                for a, b in zip(face, face[1:] + face[:1])
            }
            assert len(cycle_l) in targets and len(set(cycle_l)) == len(cycle_l), name
            assert all(
                frozenset((a, b)) in edges
                for a, b in zip(cycle_l, cycle_l[1:] + cycle_l[:1])
            ), name
            rows.append((normalize_faces(faces_l), tuple(cycle_l)))
    return rows


def compare_multisets(label, lean_rows, python_faces):
    left = Counter(faces for faces, _ in lean_rows)
    right = Counter(normalize_faces(faces) for faces in python_faces)
    assert left == right, (label, left.total(), right.total(), (left - right).total(), (right - left).total())
    return left.total()


def collapse_max(edges):
    outgoing = defaultdict(list)
    degree = Counter({0: 0, 1: 0})
    for u, v, w in edges:
        degree.setdefault(u, 0)
        degree[v] += 1
        outgoing[u].append((v, w))
    queue = deque(u for u, count in degree.items() if count == 0)
    best = {0: 0}
    visited = 0
    while queue:
        u = queue.popleft()
        visited += 1
        for v, w in outgoing[u]:
            if u in best:
                value = best[u] + w
                best[v] = max(best.get(v, value), value)
            degree[v] -= 1
            if degree[v] == 0:
                queue.append(v)
    assert visited == len(degree)
    return best[1]


def compare_dp(defs, dp):
    for family, degrees, denom in (
        ("c3", (6, 7, 9, 10, 11, 12, 13), 20),
        ("c5", (9, 10, 11, 12, 13, 14), 120),
        ("c6", (9, 11, 12, 13, 14), 120),
    ):
        for d in degrees:
            edges = map(unpack, packed(defs, f"{family}CleanD{d}Edges"))
            collapsed = Fraction(collapse_max(edges), denom)
            row = dp[family + "free_clean"][str(d)]
            original = Fraction(*row) if family == "c3" else Fraction(row["max_in_num"], row["denom"])
            assert original <= collapsed <= d - 6, (family, d, original, collapsed)

    outgoing = defaultdict(list)
    for number in packed(defs, "c5D17BwdEdges"):
        endpoints, weight = divmod(number, WEIGHT_RADIX)
        pair, length = divmod(endpoints, 8)
        u, v = divmod(pair, 256)
        assert length > 0
        outgoing[u].append((v, length, weight - BIAS))
    rows = [dict.fromkeys(literal(defs, "c5D17StartQs"), 0)] + [{} for _ in range(17)]
    for pos, row in enumerate(rows):
        for u, value in row.items():
            for v, length, weight in outgoing[u]:
                if pos + length <= 17:
                    nxt = rows[pos + length]
                    nxt[v] = max(nxt.get(v, value + weight), value + weight)
    collapsed = max(rows[17][u] for u in literal(defs, "c5D17ClosingQs") if u in rows[17])
    original = dp["c5free_clean"]["17"]["max_in_num"]
    assert original <= collapsed <= 120 * 11
    print("PASS Packed DP Bounds: all C3 (7), C5 (6 + d=17 BWD), and C6 (5) packed DAG/BWD bounds match.")


def compare_simulation(defs, family, d, model):
    """Exact weighted forward simulation from uncollapsed DP to packed Lean automaton."""
    toks, ok, adj = model
    length_only = family == "5" and d == 17
    incoming = defaultdict(list)
    if length_only:
        for number in packed(defs, "c5D17BwdEdges"):
            endpoints, weight = divmod(number, WEIGHT_RADIX)
            pair, length = divmod(endpoints, 8)
            u, v = divmod(pair, 256)
            incoming[v].append((u, length, weight - BIAS))
        starts = set(literal(defs, "c5D17StartQs"))
        ends = frozenset(literal(defs, "c5D17ClosingQs"))
    else:
        for u, v, w in map(unpack, packed(defs, f"c{family}CleanD{d}Edges")):
            incoming[v].append((u, None, w))
        starts = {0}
        ends = frozenset({1})

    @cache
    def preimage(destinations, length, weight):
        return frozenset(
            u
            for v in destinations
            for u, ln, w in incoming[v]
            if ln == length and w >= weight
        )

    full = (1 << (max(0, 16 - d) + 1)) - 1
    forbidden = 1 << (16 - d) if d < 16 else 0

    def advance(pos, state, j):
        token = toks[j]
        length, weight = token[1], int(token[6] * 120)
        if pos + length > d:
            return None
        if length_only:
            nxt = (j, 0, 0, 0, 0)
        else:
            _, mask, tc, h6s, h6o = state
            new_mask = 0
            for shift in token[7]:
                new_mask |= (mask << shift) & full
            if new_mask & forbidden:
                return None
            if family == "5":
                tc += token[8]
                if pos and d + tc >= 16:
                    return None
                h6s, h6o = h6s or token[9], h6o or token[10]
            nxt = (j, new_mask, tc, h6s, h6o)
        return (pos + length, nxt), (length if length_only else None, weight)

    failures = []
    for first in range(len(toks)):
        @cache
        def images(pos, state):
            last, _, tc, h6s, h6o = state
            if pos == d:
                if not ok[last][first]:
                    return None
                if family == "5" and (
                    (d == 10 and ((h6o and tc > 1) or (h6s and tc > 2) or tc == 5))
                    or (d == 11 and h6s and tc > 1)
                ):
                    return None
                return ends if length_only else preimage(ends, None, 0)
            candidates = None
            for j in adj[last]:
                move = advance(pos, state, j)
                if move is None:
                    continue
                point, label = move
                targets = images(*point)
                if targets is None:
                    continue
                parents = preimage(targets, *label)
                candidates = parents if candidates is None else candidates & parents
                if not candidates:
                    break
            return candidates

        move = advance(0, (-1, 1, 0, 0, 0), first)
        if move is not None:
            point, label = move
            targets = images(*point)
            if targets is not None and not (preimage(targets, *label) & starts):
                failures.append(toks[first][0])
        images.cache_clear()
    assert not failures, (family, d, failures)


def check_f10():
    rim = range(10)

    def mask(xs):
        return sum(1 << x for x in xs)

    def choose(k, n):
        if k == 0:
            return [0]
        if n == 0:
            return []
        return [m + (1 << (n - 1)) for m in choose(k - 1, n - 1)] + choose(k, n - 1)

    def independent_path(n, prev):
        if n == 0:
            return [0]
        rest = independent_path(n - 1, False)
        if prev:
            return rest
        return [m + (1 << (n - 1)) for m in independent_path(n - 1, True)] + rest

    def rotate(m):
        return ((m << 1) | (m >> 9)) & 1023

    chosen = list(map(set, combinations(rim, 5)))
    high = [{i for i in rim if (m >> i) & 1} for m in range(1024)]
    high = [h for h in high if all((v + 1) % 10 not in h for v in h)]
    assert Counter(map(mask, chosen)) == Counter(choose(5, 10))
    assert Counter(map(mask, high)) == Counter(
        independent_path(9, False) + [512 + 2 * m for m in independent_path(7, False)]
    )
    assert {m for m in range(1024) if not (m & rotate(m))} == set(map(mask, high))
    best = feasible = 0
    for sel in chosen:
        cm = mask(sel)
        req = {v for v in sel if (v - 1) % 10 in sel}
        assert mask(req) == cm & rotate(cm)
        for h in high:
            hm = mask(h)
            assert (req <= h) == (cm & rotate(cm) & hm == cm & rotate(cm))
            if not req <= h:
                continue
            feasible += 1
            ts = {i for i in sel if i in h or (i + 1) % 10 in h}
            safe = Counter()
            for a in rim:
                before, after = (a - 1) % 10, (a + 1) % 10
                if before in sel and after in sel and a not in h and after not in h:
                    safe.update((before, after))
            score = len(ts) * 8 + sum((12, 11, 8)[safe[i]] for i in sel - ts)

            def bit(m, i):
                return (m >> (i % 10)) & 1

            def gap(a):
                return (
                    bit(cm, a - 1)
                    and bit(cm, a + 1)
                    and not bit(hm, a)
                    and not bit(hm, a + 1)
                )

            packed_score = sum(
                8 if bit(hm, i) or bit(hm, i + 1) else (12, 11, 8)[gap(i + 1) + gap(i - 1)]
                for i in rim
                if bit(cm, i)
            )
            assert score == packed_score
            best = max(best, score)
    assert len(chosen) * len(high) == 30996 and feasible == 2136 and best == 47
    print("PASS F10 Combinatorics: 30,996 pairs, 2,136 admissible, packed == exact, max = 47/12 < 4.")


def check_cubic_subaudits(verifier, source, locals_cubic, d17_6o_stats):
    """Verify supplemental Stage-8/9 cubic subaudits (Triad-D1, d=9 flags, 6o 112-case & all-3-sites 1-drop, d=17 TP_s3)."""
    surv_welds = verifier["surv_welds"]
    face_graph = verifier["face_graph"]
    bounded_cycles = verifier["bounded_cycles"]
    targets = verifier["TARGETS_CUBIC"]

    # 1. Triad-D1(X=10, Z_1=7, Z_2=6) exact face-list seal welds on all 4 free edges of Z_1=7:
    td1_base = (
        (0, 1, 2),
        (2, 1, 3, 4, 5, 6),
        (4, 3, 10, 11, 12),
        (10, 3, 1, 0, 20, 21, 22, 23, 24, 25),
        (5, 4, 12, 30, 31, 32, 33),
        (6, 5, 33, 40, 41, 42),
    )
    td1_base_sv, td1_base_tw = surv_welds(td1_base)
    assert td1_base_sv == 1 and td1_base_tw == 50
    td1_edge_faces = (
        (30, 12, 11, 50, 51, 52),
        (31, 30, 50, 51, 52, 53),
        (32, 31, 50, 51, 52, 53),
        (40, 33, 32, 50, 51, 52),
    )
    td1_counts = []
    for f6 in td1_edge_faces:
        sv, tw = surv_welds((*td1_base, f6))
        assert sv == 0, f6
        td1_counts.append(tw)
    assert td1_counts == [106, 142, 140, 73]

    # 2. Cubic d=9 global flags: ((h6o or h6s) and hP) and (hTri and n6 >= 2):
    f9 = tuple(range(9))
    tpt_a = (f9, (1, 0, 20), (2, 1, 20, 22, 21), (3, 2, 21))
    tpt_bc = (f9, (1, 0, 20), (2, 1, 20, 22, 21), (21, 22, 23))
    d9_tpt_welds = 0
    for k in (4, 5, 6, 7):
        sv, tw = surv_welds((*tpt_a, ((k + 1) % 9, k, 30, 31, 32, 33)))
        assert sv == 0
        d9_tpt_welds += tw
    for k in (3, 4, 5, 6, 7):
        sv, tw = surv_welds((*tpt_bc, ((k + 1) % 9, k, 30, 31, 32, 33)))
        assert sv == 0
        d9_tpt_welds += tw
    assert d9_tpt_welds == 9
    # Every surviving d=9 chain contains an adjacent (5-face, 6-face) pair (P, H1) on F9:
    core_ph = (f9, (1, 0, 22, 21, 20), (2, 1, 20, 23, 24, 25))
    d9_tri_welds = 0
    for h2 in (
        (3, 2, 25, 30, 31, 32),
        (0, 8, 30, 31, 32, 22),
        *((k + 1, k, 30, 31, 32, 33) for k in (3, 4, 5, 6, 7)),
    ):
        sv, tw = surv_welds((*core_ph, h2))
        assert sv == 0
        d9_tri_welds += tw
    assert d9_tri_welds == 78

    # 3. Cubic d=17 6o rim-triangle coverage & 112-case contact weld audit:
    assert d17_6o_stats == {"total": 113601, "with_rim_tri": 113601}, d17_6o_stats
    f17 = tuple(range(17))
    h6_17 = (1, 0, 20, 21, 22, 23)
    cases_112 = 0
    surv_112 = []
    for k in range(2, 16):
        for (ha, hb), (ta, tb) in (((20, 21), (22, 23)), ((22, 23), (20, 21))):
            t_h = (tb, ta, 40)
            for p_opt, p_face in enumerate(((k + 1, k, hb, ha, 30), (k + 1, k, 30, hb, ha))):
                for tp_opt in (0, 1):
                    if tp_opt == 0:
                        faces = (f17, h6_17, p_face, t_h)
                    else:
                        t_p = (30, ha, 41) if p_opt == 0 else (hb, 30, 41)
                        faces = (f17, h6_17, p_face, t_h, t_p)
                    cases_112 += 1
                    if not bounded_cycles(face_graph(faces), targets):
                        surv_112.append((k, p_opt, ha, hb, faces))
    assert cases_112 == 112 and len(surv_112) == 2 and {k for k, *_ in surv_112} == {8, 9}
    for k, p_opt, ha, hb, faces in surv_112:
        base_edges = {
            (min(f[i], f[(i + 1) % len(f)]), max(f[i], f[(i + 1) % len(f)]))
            for f in faces
            for i in range(len(f))
        }
        # Opposite spoke vertex already has degree 3 (blocking a clean triangle on that adjacent edge):
        if k == 8:
            assert p_opt == 0 and sum(1 for e in base_edges if hb in e) == 3
            spoke_tri = (k + 2, k + 1, 30)
        else:
            assert p_opt == 1 and sum(1 for e in base_edges if ha in e) == 3
            spoke_tri = (k, k - 1, 30)
        g_sp = face_graph((*faces, spoke_tri))
        assert max(len(v) for v in g_sp) == 3 and bounded_cycles(g_sp, targets)
        for m in range(2, 16):
            if m in (k - 1, k, k + 1):
                continue
            g_tri = face_graph((*faces, (m + 1, m, 50)))
            assert max(len(v) for v in g_tri) == 3 and bounded_cycles(g_tri, targets)

    # 4 & 5. Extract exact d-loop from verify_theorem1_cubic_planar_c32 via AST (zero line hooks):
    tree = ast.parse(source.read_text(encoding="utf-8"), filename=str(source))
    d_loop = None
    for fn in tree.body:
        if isinstance(fn, ast.FunctionDef) and fn.name == "verify_theorem1_cubic_planar_c32":
            for stmt in fn.body:
                if (
                    isinstance(stmt, ast.For)
                    and isinstance(stmt.target, ast.Name)
                    and stmt.target.id == "d"
                ):
                    d_loop = stmt
                    break
    assert d_loop is not None

    base_ns = dict(verifier)
    for key in (
        "chains56", "sh_X", "sh_Y", "sh_A9", "sh_A10", "sh_B9_A", "sh_B9_C",
        "sh_T1", "sh_12", "sh_11", "sh_121", "sh_TP699",
    ):
        base_ns[key] = locals_cubic[key]

    # 4. d=14 and d=18 with 6o dropping 1 token from five_i in ALL THREE eval_rem branches:
    loop_6o = copy.deepcopy(d_loop)
    loop_6o.iter = ast.parse("[14, 18]", mode="eval").body
    patched_6o_s1 = 0
    patched_6o_s2 = 0
    patched_6o_s3 = 0
    for node in ast.walk(loop_6o):
        if (
            isinstance(node, ast.If)
            and isinstance(node.test, ast.Compare)
            and isinstance(node.test.left, ast.Name)
            and node.test.left.id == "x"
            and len(node.test.comparators) == 1
            and isinstance(node.test.comparators[0], ast.Constant)
            and node.test.comparators[0].value == "6o"
        ):
            if node.orelse:
                # Site 1: direct 6o branch in eval_rem
                node.body = ast.parse(
                    "if all(run_m({k}, set(grp)) for grp in combinations(five_i, min(len(five_i), 1))): return True"
                ).body
                patched_6o_s1 += 1
            else:
                # Site 2: paired TP6 + 6o helper ok_tp
                node.body = ast.parse(
                    "return run_m({tp6_i[0], ti}) and all(run_m({tp6_i[0], ti}, set(grp)) for grp in combinations(five_i, min(len(five_i), 1)))"
                ).body
                patched_6o_s2 += 1
        elif (
            isinstance(node, ast.IfExp)
            and isinstance(node.test, ast.Compare)
            and len(node.test.comparators) == 1
            and isinstance(node.test.comparators[0], ast.Constant)
            and node.test.comparators[0].value == "6o"
        ):
            # Site 3: alternating-pair helper pair_dj (drop 1 token from five_i for each 6o)
            node.body = ast.parse("1", mode="eval").body
            patched_6o_s3 += 1
    assert (patched_6o_s1, patched_6o_s2, patched_6o_s3) == (1, 1, 2)
    ns_6o = dict(base_ns, enum_counts={}, dp_bounds={}, d17_residuals=[])
    mod_6o = ast.fix_missing_locations(ast.Module(body=[loop_6o], type_ignores=[]))
    exec(compile(mod_6o, "<subaudit_6o>", "exec"), ns_6o)
    assert ns_6o["enum_counts"] == {14: 357, 18: 5232} and not ns_6o["d17_residuals"]

    # 5. d=17 with TP_s3 restricted to pure-cluster shifts (0, 1, 2, 3):
    loop_tp = copy.deepcopy(d_loop)
    loop_tp.iter = ast.parse("[17]", mode="eval").body
    patched_sh = 0
    patched_chk = 0
    for node in ast.walk(loop_tp):
        if isinstance(node, ast.Tuple) and len(node.elts) == 4:
            if (
                isinstance(node.elts[0], ast.Constant)
                and node.elts[0].value == "TP_s3"
                and isinstance(node.elts[2], ast.IfExp)
            ):
                node.elts[2] = ast.parse("(0, 1, 2, 3)", mode="eval").body
                patched_sh += 1
        if (
            isinstance(node, ast.If)
            and isinstance(node.test, ast.UnaryOp)
            and isinstance(node.test.op, ast.Not)
            and isinstance(node.test.operand, ast.Call)
            and isinstance(node.test.operand.func, ast.Name)
            and node.test.operand.func.id == "seq_killed_conservative"
        ):
            node.test = ast.parse("'TP_s3' in seq and not seq_killed_conservative(seq)", mode="eval").body
            node.body = ast.parse(
                "tp_stats['post_sieve'] += 1\n"
                "if any(tok in ('T', 'T10', 'T_L9', 'T_R9') for tok in seq):\n"
                "    tp_stats['post_sieve_with_T'] += 1\n"
            ).body
            patched_chk += 1
        if isinstance(node, ast.If) and any(
            isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and s.target.id == "checked"
            for s in node.body
        ):
            node.body.insert(
                1,
                ast.parse(
                    "if 'TP_s3' in seq:\n"
                    "    tp_stats['overweight'] += 1\n"
                    "    if any(tok in ('T', 'T10', 'T_L9', 'T_R9') for tok in seq):\n"
                    "        tp_stats['overweight_with_T'] += 1\n"
                ).body[0],
            )
    assert patched_sh == 1 and patched_chk == 1
    tp_stats = Counter()
    ns_tp = dict(base_ns, enum_counts={}, dp_bounds={}, d17_residuals=[], tp_stats=tp_stats)
    mod_tp = ast.fix_missing_locations(ast.Module(body=[loop_tp], type_ignores=[]))
    exec(compile(mod_tp, "<subaudit_tps3>", "exec"), ns_tp)
    assert tp_stats == {
        "overweight": 7924,
        "overweight_with_T": 7080,
        "post_sieve": 496,
        "post_sieve_with_T": 496,
    }

    print(
        "PASS Cubic Subaudits: Triad-D1 4-edge seals (461w->0), d=9 flags (9+78w->0), "
        "d=17 6o rim-tri coverage (113,601/113,601) + 112-case (110 killed + 2 antipodal -> 0 cubic tri), "
        "d=14/18 6o all-3-sites 1-drop (357/5,232->0), "
        "d=17 TP_s3 (0..3) (7,924 ow -> 496 post-sieve, 496/496 with isolated T)."
    )


def check_c5_stage3_subaudits(verifier):
    """Verify complete C5-free Stage-3 outer-rim capacity exclusions across all Stage-1 branches."""
    outer_rim = verifier["outer_rim"]
    rim_quotients = verifier["rim_quotients"]
    patch_status = verifier["patch_status"]
    total_kills = 0

    def assert_killed(faces, fixed=()):
        nonlocal total_kills
        rim = outer_rim(faces)
        exp = tuple(v for v in rim if v not in fixed)
        kc = 0
        for q in rim_quotients(faces, exp):
            st = patch_status(q, 5)
            assert st != "survivor", (faces, q)
            if st == "killed":
                kc += 1
        assert kc > 0, faces
        total_kills += kc

    t0 = (0, 1, 2)
    # 1. Case (1) (F_opp=6, Fa=9, Fb in {9, 10}, La=Lb=3):
    fopp1 = (2, 1, 10, 11, 12, 20)
    fa9 = (1, 0, 35, 34, 33, 32, 31, 30, 10)
    fb9_1 = (0, 2, 20, 40, 41, 42, 43, 44, 45)
    fb10_1 = (0, 2, 20, 40, 41, 42, 43, 44, 45, 46)
    for d_va in (6, 7, 9, 11, 12):
        assert_killed((t0, fopp1, fa9, fb9_1, (11, 10, 30, *range(50, 50 + d_va - 3))), (0,))
    for d_vb in (6, 7, 11, 12):
        assert_killed((t0, fopp1, fa9, fb10_1, (40, 20, 12, *range(60, 60 + d_vb - 3))), (0,))

    # 2. Case (4c) (F_opp=Fa=6, Fb=9, Lb=3, k=4 at v=0 -> 5/4 across F_opp & Fa):
    fa = (1, 0, 13, 12, 11, 10)
    fopp = (2, 1, 10, 22, 21, 20)
    fb9 = (0, 2, 20, 30, 31, 32, 33, 34, 35)
    base_c4 = (t0, fa, fopp, fb9)
    for d_g1 in (6, 7, 9, 11, 12):
        assert_killed((*base_c4, (30, 20, 21, *range(40, 40 + d_g1 - 3))), (0,))
    for d_f4 in (6, 9, 11, 12):
        assert_killed((*base_c4, (35, 0, 13, *range(90, 90 + d_f4 - 3))), ())
    for d_v in (10, 11, 12):
        assert_killed((*base_c4, (22, 10, 11, *range(50, 50 + d_v - 3))), (0,))
    for d_g2 in (9, 11, 12):
        assert_killed((*base_c4, (21, 22, *range(60, 60 + d_g2 - 2))), (0,))
    for d_h2 in (9, 11, 12):
        assert_killed((*base_c4, (12, 13, *range(80, 80 + d_h2 - 2))), (0,))
    # Disjoint outer-face seals: (V=6, G2=6) and (F4=7, H2=6):
    assert_killed((*base_c4, (22, 10, 11, 50, 51, 52), (21, 22, 52, 60, 61, 62)), (0,))
    assert_killed((*base_c4, (35, 0, 13, 82, 90, 91, 92), (82, 13, 12, 80, 81, 83)), ())

    # 3. Universal (T, H6, X in {6, 9, 10}) [vertex 6 fixed -> covers both cubic & non-cubic T]:
    tg = (1, 0, 6)
    h6 = (0, 1, 2, 3, 4, 5)
    x6 = (6, 0, 5, 60, 61, 62)
    x9 = (6, 0, 5, 60, 80, 81, 82, 83, 84)
    x10 = (6, 0, 5, 60, 80, 81, 82, 83, 84, 85)
    # Generic O in {11, 12} and Va = 12:
    for d_o in (11, 12):
        assert_killed((tg, h6, (4, 3, *range(10, 10 + d_o - 2))), (6,))
    assert_killed((tg, h6, (3, 2, *range(10, 20))), (6,))
    # X=10 forces Vb not in {6, 7, 11, 12} -> w6o(Vb) >= 1/2:
    for d_vb in (6, 7, 11, 12):
        assert_killed((tg, h6, x10, (60, 5, 4, *range(70, 70 + d_vb - 3))), (6,))
    # X=9 forces Vb not in {7, 9, 11, 12} and all triples with cap < 3/4 killed:
    for d_vb in (7, 9, 11, 12):
        assert_killed((tg, h6, x9, (60, 5, 4, *range(70, 70 + d_vb - 3))), (6,))
    vb6_g = (60, 5, 4, 30, 70, 71)
    o6_g = (30, 4, 3, 20, 40, 41)
    o7_g = (30, 4, 3, 20, 40, 41, 42)
    assert_killed((tg, h6, x9, vb6_g, o6_g), (6,))
    for d_va in (6, 7, 11):
        assert_killed((tg, h6, x9, vb6_g, o7_g, (20, 3, 2, *range(10, 10 + d_va - 3))), (6,))
    for d_va in (6, 11):
        assert_killed((tg, h6, x9, vb6_g, (3, 2, *range(10, 10 + d_va - 2))), (6,))
        assert_killed((tg, h6, x9, (20, 3, 2, *range(10, 10 + d_va - 3)), o6_g), (6,))
    # X=6 (both H6-side and Fa-side) forces cap >= 1/2 even when shared valley V=9:
    for d_vb in (10, 11, 12):
        assert_killed((tg, h6, x6, (60, 5, 4, *range(70, 70 + d_vb - 3))), (6,))
    for d_va, d_o, d_vb in product((6, 7, 11), (6, 7), (6, 7, 11)):
        cap = (
            Fraction(0 if d_va in (6, 11) else 1, 4)
            + Fraction(0 if d_o == 6 else 1, 4)
            + Fraction(0 if d_vb in (6, 11) else 1, 4)
        )
        if cap < Fraction(1, 2):
            va_f = (20, 3, 2, *range(10, 10 + d_va - 3))
            o_f = (30, 4, 3, 20, *range(40, 40 + d_o - 4))
            vb_f = (60, 5, 4, 30, *range(70, 70 + d_vb - 4))
            assert_killed((tg, h6, x6, va_f, o_f, vb_f), (6,))
    vb9_g = (60, 5, 4, 30, 70, 71, 72, 73, 74)
    for d_va, d_o in product((6, 7, 11), (6, 7)):
        if Fraction(0 if d_va in (6, 11) else 1, 4) + Fraction(0 if d_o == 6 else 1, 4) < Fraction(1, 2):
            va_f = (20, 3, 2, *range(10, 10 + d_va - 3))
            o_f = (30, 4, 3, 20, *range(40, 40 + d_o - 4))
            assert_killed((tg, h6, x6, va_f, o_f, vb9_g), (6,))
    # Symmetric Fa-side of (T, Fa=6, Fopp=6) with high vertex v=0 fixed:
    base_fa = (t0, fa, fopp)
    for d_h1 in (11, 12):
        assert_killed((*base_fa, (11, 12, *range(60, 60 + d_h1 - 2))), (0,))
    assert_killed((*base_fa, (12, 13, *range(70, 80))), (0,))
    for d_v, d_h1, d_h2 in product((6, 7, 11), (6, 7), (6, 7, 11)):
        cap = (
            Fraction(0 if d_v in (6, 11) else 1, 4)
            + Fraction(0 if d_h1 == 6 else 1, 4)
            + Fraction(0 if d_h2 in (6, 11) else 1, 4)
        )
        if cap < Fraction(1, 2):
            v_f = (22, 10, 11, 50, *range(51, 51 + d_v - 4))
            h1_f = (50, 11, 12, 60, *range(61, 61 + d_h1 - 4))
            h2_f = (60, 12, 13, *range(70, 70 + d_h2 - 3))
            assert_killed((*base_fa, v_f, h1_f, h2_f), (0,))
    v9_fa = (22, 10, 11, 50, 51, 52, 53, 54, 55)
    for d_h1, d_h2 in product((6, 7), (6, 7, 11)):
        if Fraction(0 if d_h1 == 6 else 1, 4) + Fraction(0 if d_h2 in (6, 11) else 1, 4) < Fraction(1, 2):
            h1_f = (50, 11, 12, 60, *range(61, 61 + d_h1 - 4))
            h2_f = (60, 12, 13, *range(70, 70 + d_h2 - 3))
            assert_killed((*base_fa, v9_fa, h1_f, h2_f), (0,))

    # 4. Pure cubic (6, 6, 9) and cubic/non-cubic Mini-Corannulene (6, 6, 6):
    base_669 = (tg, h6, (2, 1, 6, 90, 91, 10), (6, 0, 5, 60, 80, 81, 82, 83, 90))
    for d_vb in (6, 7, 9, 11, 12):
        assert_killed((*base_669, (60, 5, 4, *range(70, 70 + d_vb - 3))), ())
    for d_va in (10, 11, 12):
        assert_killed((*base_669, (3, 2, 10, *range(20, 20 + d_va - 3))), ())
    for d_o in (9, 11, 12):
        assert_killed((*base_669, (4, 3, *range(40, 40 + d_o - 2))), ())
    for d_va in (6, 7, 9):
        va_f = (20, 3, 2, 10, *range(21, 21 + d_va - 4))
        for d_o in (6, 7):
            assert_killed((*base_669, va_f, (4, 3, 20, *range(40, 40 + d_o - 3))), ())
    for base_mc, fx in (
        ((tg, h6, x6, (2, 1, 6, 62, 11, 10)), ()),
        ((tg, h6, x6, (2, 1, 6, 70, 71, 10)), (6,)),
    ):
        for d_va in (9, 10, 11, 12):
            assert_killed((*base_mc, (3, 2, 10, *range(20, 20 + d_va - 3))), fx)
        for d_va, d_vb in ((6, 6), (6, 7), (7, 7)):
            assert_killed(
                (*base_mc, (3, 2, 10, *range(20, 20 + d_va - 3)), (60, 5, 4, *range(50, 50 + d_vb - 3))),
                fx,
            )
        for d_va in (6, 7):
            va_f = (20, 3, 2, 10, *range(21, 21 + d_va - 4))
            for d_o in (6, 7, 11, 12):
                assert_killed((*base_mc, va_f, (4, 3, 20, *range(40, 40 + d_o - 3))), fx)

    print(
        f"PASS C5-Free Stage-3 Capacity Subaudits: all Case (1)/(2)/(4c), universal (T,H6,X in {{6,9,10}}), "
        f"(6,6,9), & Mini-Corannulene exclusions verified ({total_kills} killed quotients, 0 survivors)."
    )


def main():
    if sys.flags.optimize:
        raise SystemExit("Run with assertions enabled (no -O).")
    t0 = monotonic_ns()
    check_zero_floats()
    defs = source_data()
    print("PASS Lean Trust Scan: zero forbidden trust tokens and allowed set_option only.")
    check_f10()
    witness_dir = CERT.joinpath("witnesses")
    bundle = {
        path.stem: json.loads(path.read_text(encoding="utf-8"))
        for path in witness_dir.glob("*.json")
    }
    compare_bf(defs, bundle["bf_potentials"])

    source = CERT.joinpath("verify_planar_eg.py")
    tree = ast.parse(source.read_text(encoding="utf-8"), filename=str(source))
    locals_cubic = {}
    automata = {}
    d17_6o_stats = Counter()
    patched_d17_6o = 0
    for func in tree.body:
        if isinstance(func, ast.FunctionDef) and func.name == "verify_theorem1_cubic_planar_c32":
            for node in ast.walk(func):
                if isinstance(node, ast.If) and any(
                    isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and s.target.id == "checked"
                    for s in node.body
                ):
                    node.body.insert(
                        1,
                        ast.parse(
                            "if d == 17 and '6o' in seq:\n"
                            "    audit_d17_6o['total'] += 1\n"
                            "    if any(\n"
                            "        tok in ('T', 'T10', 'T_L9', 'T_R9', 'T1_L', 'T1_R', 'T2',\n"
                            "                'TP_s_L', 'TP_s_R', 'TP_s3',\n"
                            "                'TPT_A', 'TPT_BC', 'TPT_A9_R', 'TPT_A9_L', 'TPT_A10_R', 'TPT_A10_L',\n"
                            "                'TPT_B9A_R', 'TPT_B9A_L', 'TPT_B9C_R', 'TPT_B9C_L',\n"
                            "                'S_X', 'S_YZ_R', 'S_YZ_L')\n"
                            "        or (tok in chain_meta and any(m in ('T1R', 'T1L', 'T2', 'TPsR', 'TPsL') for m in chain_meta[tok]))\n"
                            "        for tok in seq\n"
                            "    ):\n"
                            "        audit_d17_6o['with_rim_tri'] += 1\n"
                        ).body[0],
                    )
                    patched_d17_6o += 1
            func.body.insert(-1, ast.parse("audit_cubic(locals())").body[0])
        if isinstance(func, ast.FunctionDef) and func.name in (
            "verify_theorem3_c5free",
            "verify_theorem3_c6free",
        ):
            for loop in func.body:
                if (
                    not isinstance(loop, ast.For)
                    or not isinstance(loop.target, ast.Name)
                    or loop.target.id != "d"
                ):
                    continue
                for i, stmt in enumerate(loop.body):
                    if (
                        isinstance(stmt, ast.Assign)
                        and isinstance(stmt.targets[0], ast.Name)
                        and stmt.targets[0].id == "adj"
                    ):
                        loop.body.insert(
                            i + 1,
                            ast.parse(
                                f"audit_automata[({func.name[-5]!r}, d)] = (toks, okm, adj)"
                            ).body[0],
                        )
                        break
    assert patched_d17_6o == 1

    verifier = {
        "__file__": str(source),
        "__name__": "parity_verifier",
        "audit_cubic": locals_cubic.update,
        "audit_automata": automata,
        "audit_d17_6o": d17_6o_stats,
    }
    exec(compile(ast.fix_missing_locations(tree), str(source), "exec"), verifier)

    # Repaired P0 #4 pinched-triangle hereditary weld assertion:
    pinch = {wf for _, wf, _ in verifier["enum_planar_welds"](((0, 1, 2), (0, 3, 4)))}
    assert ((0, 1, 2), (0, 3, 1)) in pinch and ((0, 1, 2), (0, 2, 4)) in pinch
    assert verifier["weld_boundary"](((0, 1, 2), (0, 3, 4)), (0, 0, 1), (1, 4, 0)) == (
        (0, 1, 2),
        (0, 3, 1),
    )

    rim = defaultdict(list)
    bfs = defaultdict(list)
    weld_stats = {"calls": 0, "weak_ok": 0, "bicond_ok": 0}
    original_status = verifier["patch_status"]
    original_chain = verifier["test_cubic_chain_repaired"]
    original_graph = verifier["face_graph"]
    original_enum_welds = verifier["enum_planar_welds"]
    patch_data_fn = verifier["patch_data"]

    def capture_graph(faces):
        caller = sys._getframe(1)
        if (
            caller.f_code.co_name == "verify_theorem3_c5free"
            and len(faces) == 3
            and faces[0] == (0, 1, 2)
        ):
            rim[5].append(("t_frz", None, faces))
        return original_graph(faces)

    def capture_status(faces, forbidden):
        result = original_status(faces, forbidden)
        if result == "killed":
            caller = sys._getframe(1)
            rim[forbidden].append((caller.f_code.co_name, caller.f_locals.get("degs"), faces))
        return result

    def capture_chain(tokens):
        result = original_chain(tokens)
        frame = sys._getframe(1)
        seq = frame.f_locals.get("seq")
        if seq and frame.f_code.co_name == "verify_theorem1_cubic_planar_c32":
            bfs[len(seq)].append((tokens, result))
        return result

    def capture_enum_welds(initial):
        weld_stats["calls"] += 1
        data = patch_data_fn(initial)
        assert data is not None, initial
        _, corners, contacts, boundary = data
        fadj = defaultdict(set)
        for i, j in contacts:
            fadj[i].add(j)
            fadj[j].add(i)
        seen_f = {0}
        q_f = [0]
        while q_f:
            u = q_f.pop()
            for w in fadj[u]:
                if w not in seen_f:
                    seen_f.add(w)
                    q_f.append(w)
        assert len(seen_f) == len(initial), initial
        exp = Counter()
        for _, a, b in boundary:
            exp[a] += 1
            exp[b] += 1
        assert all(exp[x] in (0, 2) and (exp[x] != 0 or corners[x] == 3) for x in corners), initial
        weld_stats["weak_ok"] += 1
        if all(exp[x] in (0, 2) and ((exp[x] == 0) == (corners[x] == 3)) for x in corners):
            weld_stats["bicond_ok"] += 1
        return original_enum_welds(initial)

    verifier["face_graph"] = capture_graph
    verifier["patch_status"] = capture_status
    verifier["test_cubic_chain_repaired"] = capture_chain
    verifier["enum_planar_welds"] = capture_enum_welds

    verifier["check_zero_floats"]()
    sharp = verifier["verify_sharpness_witnesses"]()
    assert json.loads(json.dumps(sharp)) == bundle["sharp_witnesses"]
    compare_sharp(defs, sharp, verifier)

    cubic = verifier["verify_theorem1_cubic_planar_c32"](export_mode=True)
    assert weld_stats["calls"] == 844 and weld_stats["weak_ok"] == 844
    print(
        f"PASS Lemma 3.1 Weld Invariant: {weld_stats['weak_ok']}/{weld_stats['calls']} "
        f"production calls satisfy connected + e in {{0,2}} + (e=0 => c=3) "
        f"({weld_stats['bicond_ok']}/{weld_stats['calls']} satisfy stronger biconditional)."
    )

    c3, c5, c6 = (verifier[f"verify_theorem3_c{d}free"]() for d in (3, 5, 6))
    dp = {
        "cubic_chains56": cubic["chains56"],
        "cubic_clean_d31": cubic["dp_bounds"],
        "c3free_clean": c3["dp_clean"],
        "c5free_clean": c5["dp_clean"],
        "c6free_clean": c6["dp_clean"],
    }
    assert json.loads(json.dumps(dp)) == bundle["cyclic_dp_bounds"]
    bf = {
        "cubic_d33": cubic["bf_clean_d33"],
        "cubic_frozen_cap": cubic["bf_frozen_cap"],
        "c5free_d18": c5["bf_clean_d18"],
        "c5free_frozen_cap": c5["bf_frozen_cap"],
        "c6free_d15": c6["bf_clean_d15"],
        "c6free_frozen_cap": c6["bf_frozen_cap"],
    }
    assert bf == bundle["bf_potentials"]
    compare_dp(defs, dp)

    sim_count = 0
    for (family, degree), model in sorted(automata.items()):
        if degree in ((9, 10, 11, 12, 13, 14, 17) if family == "5" else (9, 11, 12, 13, 14)):
            compare_simulation(defs, family, degree, model)
            sim_count += 1
    assert sim_count == 12
    print("PASS Weighted DP-Collapse Simulations: all 12/12 (7 C5-free + 5 C6-free) verified.")

    token_names = (
        "C_T1R_TPsL", "C_TPsR_H_TPsL", "C_TPsR_T1L", "N", "R10", "T", "T10",
        "T1_L", "T1_R", "TP_s_L", "TP_s_R",
    )
    residuals = literal(defs, "r10ResidualSeqs") + [
        seq for _, _, seq in literal(defs, "orbitResidualSeqs")
    ]
    assert Counter(tuple(token_names[i] for i in seq) for seq in residuals) == Counter(
        locals_cubic["d17_residuals"]
    )
    chains = {name: shifts for name, _, _, shifts in literal(defs, "chains56Table")}
    assert chains == cubic["chains56"]

    targets = {4, 8, 16, 32}
    d17 = cubic["d17_weld_witnesses"]
    assert d17 == bundle["killed_witnesses"]["d17_12orbits_114welds"]
    total_welds = 0
    for word, records in d17.items():
        lean_r = lean_welds(defs, ["orbit_" + word], targets)
        actual = [(normalize_faces(row["faces"]), tuple(row["cycle"])) for row in records]
        assert Counter(lean_r) == Counter(actual), word
        total_welds += len(lean_r)
    total_welds += compare_multisets(
        "d17 R10 seals",
        lean_welds(defs, ["r10SealWelds"], targets),
        [r["faces"] for r in locals_cubic["seal_records"][-5:]],
    )
    total_welds += compare_multisets(
        "cubic seals",
        lean_welds(defs, [n for n in defs if re.fullmatch(r'seal\w*Welds(?:_c\d+)?', n)], targets),
        [r["faces"] for r in locals_cubic["seal_records"]],
    )
    for length in range(2, 7):
        faces = []
        for tokens, (survivors, _, _) in bfs[length]:
            if survivors or (patch := verifier["build_cubic_chain_dedup"](tokens)) is None:
                continue
            faces.extend(q for _, q, _ in original_enum_welds(patch[0]))
        names = [n for n in defs if re.fullmatch(fr'len{length}Welds(?:_c\d+)?', n)]
        total_welds += compare_multisets(
            f"pruned chains length {length}", lean_welds(defs, names, targets), faces
        )
    for forbidden in (3, 5, 6):
        names = [n for n in defs if re.fullmatch(fr'c{forbidden}\w*Welds(?:_c\d+)?', n)]
        observed = [faces for _, degs, faces in rim[forbidden] if degs != (6, 6, 6, 6, 6)]
        total_welds += compare_multisets(
            f"C{forbidden}-free rim", lean_welds(defs, names, {4, 8, 16}), observed
        )
    assert total_welds == 6772, total_welds

    # Restore unwrapped engine helpers before running supplemental Stage-8 subaudits:
    verifier["face_graph"] = original_graph
    verifier["patch_status"] = original_status
    verifier["test_cubic_chain_repaired"] = original_chain
    verifier["enum_planar_welds"] = original_enum_welds
    check_cubic_subaudits(verifier, source, locals_cubic, d17_6o_stats)
    check_c5_stage3_subaudits(verifier)

    dt_ms = (monotonic_ns() - t0) // 1_000_000
    rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert dt_ms < 60_000, f"Exceeded 60s budget: {dt_ms} ms"
    assert rss_kib < 500 * 1024, f"Exceeded 500 MiB RSS: {rss_kib} KiB"
    print(
        f"PASS ALL Paper 1 Parity, Weighted DP-Collapse (12/12), & Weld-Invariant (844/844) Checks: "
        f"{total_welds} Lean/Python weld entries matched in {dt_ms} ms "
        f"(peak RSS {rss_kib // 1024} MiB, ZERO floats, ZERO `/`!)"
    )


if __name__ == "__main__":
    main()
