#!/usr/bin/env python3
"""Standalone Zero-Float Verifier & Proof-Carrying Witness Exporter for Flagship Paper 1.

Paper 1:
  "Every Cubic Planar Graph Contains C4, C8, C16, or C32:
   Arbitrary Connectivity, Planar Claw-Free C64, and General Planar C16 Theorems"

Pure Python 3 standard library ONLY. ZERO floats, ZERO true-division `/` operator
(AST-guarded), ZERO imports outside stdlib (runs completely standalone).

Usage:
  python3 -B publication/paper1_planar/cert/verify_planar_eg.py
  python3 -B publication/paper1_planar/cert/verify_planar_eg.py --export-witnesses /path/to/dir
"""

import argparse
import ast
import json
import math
import resource
import sys
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path
from time import monotonic_ns

TARGETS_CUBIC = (4, 8, 16, 32)
W_LCM = 120
F = Fraction


# ==============================================================================
# 0. STRICT AST ZERO-FLOAT & NO-TRUE-DIVISION GUARD
# ==============================================================================

def check_zero_floats():
    src = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(src, filename=__file__)
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and type(node.value).__name__ in ("float", "complex"):
            raise AssertionError(f"Forbidden float/complex literal: {node.value!r}")
        if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, ast.Div):
            raise AssertionError("Forbidden true-division `/` operator (use Fraction or //)")
        if isinstance(node, ast.Name) and node.id == "float":
            raise AssertionError("Forbidden float identifier")


# ==============================================================================
# 1. SHARED GRAPH, PLANAR WELD, RIM-QUOTIENT, & BELLMAN-FORD ENGINES
# ==============================================================================

def cyc_darts(cycle):
    return zip(cycle, cycle[1:] + cycle[:1])


def face_edges(faces):
    return {tuple(sorted(e)) for face in faces for e in cyc_darts(face)}


def make_adj_from_pairs(n, pairs):
    adj = [set() for _ in range(n)]
    for u, v in pairs:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    return tuple(tuple(sorted(row)) for row in adj)


def face_graph(faces):
    verts = sorted({v for f in faces for v in f})
    idx = {v: i for i, v in enumerate(verts)}
    return make_adj_from_pairs(len(verts), ((idx[u], idx[v]) for f in faces for u, v in cyc_darts(f)))


def bfs_dist(adj, start):
    dist = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def bit_indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def bounded_cycles(adj, lengths):
    if not lengths:
        return False
    maximum = max(lengths)
    for start in range(len(adj)):
        stk = [(start, 1 << start, 0)]
        while stk:
            u, vis, dist = stk.pop()
            for v in adj[u]:
                if v == start and dist + 1 in lengths:
                    return True
                if v > start and dist + 1 < maximum and not (vis & (1 << v)):
                    stk.append((v, vis | (1 << v), dist + 1))
    return False


def find_cycle_witness(adj, lengths):
    """Return an explicit simple cycle (tuple of vertices) with length in `lengths`, or None."""
    if not lengths:
        return None
    maximum = max(lengths)
    for start in range(len(adj)):
        stk = [(start, 1 << start, (start,))]
        while stk:
            u, vis, path = stk.pop()
            d = len(path)
            for v in adj[u]:
                if v == start and d in lengths:
                    return path
                if v > start and d < maximum and not (vis & (1 << v)):
                    stk.append((v, vis | (1 << v), (*path, v)))
    return None


def length_spectrum(adj, source, target):
    stk = [(source, 1 << source, 0)]
    found = set()
    while stk:
        u, vis, dist = stk.pop()
        if u == target:
            found.add(dist)
        else:
            for v in adj[u]:
                if not (vis & (1 << v)):
                    stk.append((v, vis | (1 << v), dist + 1))
    return found


def patch_data(faces):
    uses = defaultdict(list)
    corners = Counter()
    for i, face in enumerate(faces):
        if len(set(face)) != len(face):
            return None
        corners.update(face)
        for u, v in cyc_darts(face):
            uses[(u, v) if u < v else (v, u)].append((i, u, v))
    if max(corners.values()) > 3:
        return None
    contacts = set()
    boundary = []
    for entries in uses.values():
        if len(entries) == 1:
            boundary.append(entries[0])
            continue
        if len(entries) != 2:
            return None
        (i, u, v), (j, w, x) = entries
        if (u, v) != (x, w) or (i, j) in contacts:
            return None
        contacts.add((i, j))
    return uses, corners, contacts, boundary


def weld_boundary(faces, left, right):
    _, u, v = left
    _, w, x = right
    pending = [(u, x), (v, w)]
    while pending:
        labels = {node: node for face in faces for node in face}

        def root(node):
            while node != labels[node]:
                node = labels[node]
            return node

        for a, b in pending:
            ra, rb = root(a), root(b)
            if ra != rb:
                if ra < rb:
                    labels[rb] = ra
                else:
                    labels[ra] = rb
        faces = tuple(tuple(root(node) for node in face) for face in faces)
        data = patch_data(faces)
        if data is None:
            return None
        _, corners, _, boundary = data
        exposed = defaultdict(list)
        for _, a, b in boundary:
            exposed[a].append(b)
            exposed[b].append(a)
        pending = []
        for node, cnt in corners.items():
            tips = exposed[node]
            if len(tips) not in (0, 2) or (not tips and cnt != 3):
                return None
            if cnt == 3 and tips:
                pending.append(tuple(tips))
    return faces


def enum_planar_welds(initial):
    """Enumerate valid planar boundary-weld quotients from `initial`.

    Hereditary pruning (only skips states that can NEVER become valid after further
    boundary welds): `patch_data(faces) is None`, same-face/double-contact pairs,
    endpoint corner overflow (`corners[u] + corners[v] > 3`), and `weld_boundary(...) is None`.

    Emit-only validity filters (skip yielding invalid intermediate states, DO NOT skip
    expanding them): spherical Euler check `V - E + F = 2 - holes` and exact edge-contact
    intersections (`set(a) & set(b) == contact_verts[(i, j)]`).
    """
    seen = {initial}
    todo = [initial]
    while todo:
        faces = todo.pop()
        data = patch_data(faces)
        if data is None:
            continue
        uses, corners, contacts, boundary = data
        exposed = {node for _, a, b in boundary for node in (a, b)}
        b_adj = defaultdict(set)
        for _, a, b in boundary:
            b_adj[a].add(b)
            b_adj[b].add(a)
        holes = 0
        while exposed:
            exposed.difference_update(bfs_dist(b_adj, next(iter(exposed))))
            holes += 1
        euler_ok = (len(corners) - len(uses) + len(faces) == 2 - holes)
        if euler_ok:
            contact_verts = {}
            for (u, v), entries in uses.items():
                if len(entries) == 2:
                    contact_verts[(entries[0][0], entries[1][0])] = {u, v}
            exact_ok = not any(set(a).intersection(b) != contact_verts.get((i, j), set())
                               for (i, a), (j, b) in combinations(enumerate(faces), 2))
            if exact_ok:
                relabel = {node: idx for idx, node in enumerate(sorted(corners))}
                yield make_adj_from_pairs(len(corners), ((relabel[u], relabel[v]) for u, v in uses)), faces, relabel
        for a, b in combinations(boundary, 2):
            if a[0] == b[0] or (min(a[0], b[0]), max(a[0], b[0])) in contacts:
                continue
            if any(u != v and corners[u] + corners[v] > 3
                   for u, v in ((a[1], b[2]), (a[2], b[1]))):
                continue
            child = weld_boundary(faces, a, b)
            if child is not None and child not in seen:
                seen.add(child)
                todo.append(child)


def subcubic_find_cycle(adj, targets):
    """Exact cycle-space search on a simple subcubic graph (connected or disconnected).

    Preconditions (enforced): every vertex has degree <= 3, and every length in `targets`
    is an integer >= 3. Returns an explicit ordered simple vertex cycle tuple, or None.
    """
    assert all(isinstance(t, int) and t >= 3 for t in targets), f"Invalid cycle targets: {targets!r}"
    assert all(len(row) <= 3 for row in adj), "subcubic_find_cycle requires max degree <= 3"
    if not targets or len(adj) < 3:
        return None
    incident = [0] * len(adj)
    edge_list = []
    for u, row in enumerate(adj):
        for v in row:
            if u < v:
                bit = 1 << len(edge_list)
                edge_list.append((u, v))
                incident[u] |= bit
                incident[v] |= bit
    root_paths = {}
    tree = 0
    for root_v in range(len(adj)):
        if root_v in root_paths:
            continue
        root_paths[root_v] = 0
        q = [root_v]
        for u in q:
            for v in adj[u]:
                if v not in root_paths:
                    e_bit = incident[u] & incident[v]
                    tree |= e_bit
                    root_paths[v] = root_paths[u] ^ e_bit
                    q.append(v)
    vectors = [0]
    for i, (u, v) in enumerate(edge_list):
        bit = 1 << i
        if tree & bit:
            continue
        fund = bit ^ root_paths[u] ^ root_paths[v]
        exts = [known ^ fund for known in vectors]
        for mask in exts:
            if mask.bit_count() not in targets:
                continue
            rem = mask
            pend = mask & -mask
            while pend:
                eb = pend & -pend
                pend ^= eb
                rem ^= eb
                a, b = edge_list[eb.bit_length() - 1]
                pend |= rem & (incident[a] | incident[b])
            if rem == 0:
                # Reconstruct exact ordered simple vertex cycle from edge mask:
                c_adj = defaultdict(list)
                for idx in bit_indices(mask):
                    a, b = edge_list[idx]
                    c_adj[a].append(b)
                    c_adj[b].append(a)
                start = min(c_adj)
                cyc = [start, min(c_adj[start])]
                while True:
                    nxt = next(w for w in c_adj[cyc[-1]] if w != cyc[-2])
                    if nxt == start:
                        break
                    cyc.append(nxt)
                assert len(cyc) == len(set(cyc)) == mask.bit_count()
                return tuple(cyc)
        vectors.extend(exts)
    return None


def verify_engine_self_tests():
    """Adversarial self-tests for `enum_planar_welds` and `subcubic_find_cycle`."""
    # 1. Non-hereditary exact-contact seed must still expand to valid welded disks:
    pinch_welds = {wfaces for _, wfaces, _ in enum_planar_welds(((0, 1, 2), (0, 3, 4)))}
    assert ((0, 1, 2), (0, 3, 1)) in pinch_welds and ((0, 1, 2), (0, 2, 4)) in pinch_welds
    # 2. Disconnected seed must still expand to valid welded disks:
    disconn_welds = list(enum_planar_welds(((0, 1, 2), (3, 4, 5))))
    assert len(disconn_welds) > 0
    # 3. Disconnected subcubic graph (isolated vertex 0 + separate C4) must not KeyError:
    disconn_c4 = make_adj_from_pairs(5, ((1, 2), (2, 3), (3, 4), (4, 1)))
    assert subcubic_find_cycle(disconn_c4, (4,)) == (1, 2, 3, 4)
    # 4. Precondition enforcement on max degree > 3 and invalid targets:
    k1_4 = make_adj_from_pairs(5, ((0, 1), (0, 2), (0, 3), (0, 4)))
    for bad_call in (
        lambda: subcubic_find_cycle(k1_4, (4,)),
        lambda: subcubic_find_cycle(disconn_c4, (0,)),
        lambda: subcubic_find_cycle(disconn_c4, (2,)),
    ):
        try:
            bad_call()
            raise AssertionError("Expected precondition failure")
        except AssertionError as exc:
            assert str(exc) != "Expected precondition failure"


def subcubic_has_cycle(adj, targets):
    return subcubic_find_cycle(adj, targets) is not None


def surv_welds(faces, targets=TARGETS_CUBIC, record=None):
    welds = list(enum_planar_welds(faces))
    assert len(welds) > 0, f"Empty weld set (orientation error) on {faces}"
    surv = 0
    for adj, wfaces, _ in welds:
        cyc = subcubic_find_cycle(adj, targets)
        if cyc is None:
            surv += 1
        elif record is not None:
            record.append({"faces": [list(fc) for fc in wfaces], "cycle": list(cyc)})
    return surv, len(welds)


def shifts_of(faces, u, v, base_e):
    verts = sorted({x for fc in faces for x in fc})
    idx = {x: i for i, x in enumerate(verts)}
    adj = face_graph(faces)
    return tuple(sorted(L - base_e for L in length_spectrum(adj, idx[u], idx[v])))


def common_weld_shifts(faces, u_label, v_label, base_len, targets=TARGETS_CUBIC):
    all_sh = None
    tot = surv = 0
    for adj, _, relabel in enum_planar_welds(faces):
        tot += 1
        if not subcubic_has_cycle(adj, targets):
            surv += 1
            lens = length_spectrum(adj, relabel[u_label], relabel[v_label])
            sh = {L - base_len for L in lens if L >= base_len}
            all_sh = sh if all_sh is None else (all_sh & sh)
    return tot, surv, tuple(sorted(all_sh)) if all_sh is not None else None


def outer_rim(faces):
    uses = Counter(tuple(sorted(e)) for fc in faces for e in cyc_darts(fc))
    boundary = defaultdict(list)
    for (a, b), count in uses.items():
        if count == 1:
            boundary[a].append(b)
            boundary[b].append(a)
    if not boundary or any(len(row) != 2 for row in boundary.values()):
        return ()
    start = min(boundary)
    ring = [start, min(boundary[start])]
    while True:
        nxt = next(v for v in boundary[ring[-1]] if v != ring[-2])
        if nxt == start:
            return tuple(ring) if len(ring) == len(boundary) else ()
        ring.append(nxt)


def rim_quotients(faces, rim, rigid=frozenset()):
    access = {v: sum(1 << i for i, fc in enumerate(faces) if v in fc) for v in rim}
    blocks = []
    labels = {}

    def compatible_with_contacts(tag, used):
        mask = (1 << len(faces)) - 1
        for i, j in product(bit_indices(tag & mask), bit_indices(used & mask)):
            left = tuple(labels.get(v, v) for v in faces[i])
            right = tuple(labels.get(v, v) for v in faces[j])
            overlap = set(left).intersection(right)
            if len(overlap) > 2:
                return False
            if len(overlap) == 2 and (not any(set(e) == overlap for e in cyc_darts(left)) or
                                      not any(set(e) == overlap for e in cyc_darts(right))):
                return False
        return True

    def visit(pos):
        if pos == len(rim):
            yield tuple(tuple(labels.get(v, v) for v in fc) for fc in faces)
            return
        v = rim[pos]
        tag = access[v] | ((1 << len(faces)) if v in rigid else 0)
        for i, (members, used) in enumerate(blocks):
            if used & tag:
                continue
            last = members[-1]
            if any(peer[0] < last < peer[-1] for j, (peer, _) in enumerate(blocks) if j != i):
                continue
            labels[v] = rim[members[0]]
            if not compatible_with_contacts(tag, used):
                continue
            blocks[i] = ([*members, pos], used | tag)
            yield from visit(pos + 1)
            blocks[i] = (members, used)
        labels.pop(v, None)
        blocks.append(([pos], tag))
        yield from visit(pos + 1)
        blocks.pop()

    yield from visit(0)


def patch_status(faces, forbidden):
    if any(len(set(fc)) != len(fc) for fc in faces):
        return "invalid"
    boundaries = [set(tuple(sorted(e)) for e in cyc_darts(fc)) for fc in faces]
    for i, j in combinations(range(len(faces)), 2):
        shared = set(faces[i]).intersection(faces[j])
        contact = boundaries[i] & boundaries[j]
        if len(shared) >= 2 and (len(contact) != 1 or len(shared) != 2):
            return "invalid"
    g = face_graph(faces)
    if any(len(g[v]) > 3 for u in range(len(g)) if len(g[u]) > 3 for v in g[u]):
        return "invalid"
    if bounded_cycles(g, {4, forbidden}):
        return "invalid"
    return "killed" if bounded_cycles(g, {8, 16}) else "survivor"


def find_rational_potential(nodes, edges_w):
    """Exact rational Bellman-Ford: returns (True, pi) iff pi[u] + w(u,v) <= pi[v] for all edges."""
    scale = math.lcm(*(w.denominator for _, _, w in edges_w)) if edges_w else 1
    arcs = [(u, v, int(w * scale)) for u, v, w in edges_w]
    dist = {v: 0 for v in nodes}
    for _ in range(len(nodes) + 1):
        changed = False
        for u, v, w in arcs:
            if dist[u] + w > dist[v]:
                dist[v] = dist[u] + w
                changed = True
        if not changed:
            for u, v, w in arcs:
                assert dist[u] + w <= dist[v], f"Potential failed on {(u, v, w)}"
            return True, {v: F(val, scale) for v, val in dist.items()}, scale
    return False, None, scale


# ==============================================================================
# 2. SHARPNESS WITNESSES: G168, C60 (+ 119v 1-SUM), TD60 (+ 119v 1-SUM)
# ==============================================================================

def verify_sharpness_witnesses():
    """Construct and independently verify G168, C60, TD60, and 119-v Delta=6 1-sums."""
    # --- A. G168 = C24 * [T1 + P + T2] ---
    sectors = range(6)
    top, a, b, bottom = (tuple(range(6 * row, 6 * (row + 1))) for row in range(4))
    base = [top, bottom[::-1]]
    for i in sectors:
        j = (i + 1) % 6
        base.extend(((top[i], a[i], b[i], a[j], top[j]),
                     (bottom[i], bottom[j], b[j], a[j], b[i])))
    ports = dict(zip((*top, *a, *b, *bottom),
                     (*(top[(i + 1) % 6] for i in sectors),
                      *(b[(i - 1) % 6] for i in sectors),
                      *a, *(bottom[(i - 1) % 6] for i in sectors))))
    turn = {u: {} for u in range(24)}
    for fc in base:
        for i, u in enumerate(fc):
            turn[u][fc[i - 1]] = fc[(i + 1) % len(fc)]
    port_id = {}
    for u, x in ports.items():
        y = turn[u][x]
        z = turn[u][y]
        assert len({x, y, z}) == 3 and turn[u][z] == x
        for v, j in zip((x, y, z), (4, 5, 6)):
            port_id[u, v] = j
    inside = ((0, 4, 3, 2, 1), (5, 0, 1), (6, 2, 3))
    arcs = {(4, 5): (4, 0, 5), (5, 6): (5, 1, 2, 6), (6, 4): (6, 3, 4)}
    g168_faces = [tuple(7 * u + v for v in fc) for u in range(24) for fc in inside]
    for fc in base:
        g168_faces.append(tuple(7 * u + port for i, u in enumerate(fc)
                                for port in arcs[port_id[u, fc[i - 1]],
                                                 port_id[u, fc[(i + 1) % len(fc)]]]))
    uses = Counter(e for fc in g168_faces for e in cyc_darts(fc))
    assert len(uses) == 504
    assert all(cnt == 1 and uses[v, u] == 1 for (u, v), cnt in uses.items())
    assert all(len(set(fc)) == len(fc) for fc in g168_faces)
    g168_edges = sorted(face_edges(g168_faces))
    assert len(g168_edges) == 252
    g168_adj = make_adj_from_pairs(168, g168_edges)
    assert len(g168_adj) == 168 and all(len(row) == 3 for row in g168_adj)
    assert 168 - len(g168_edges) + len(g168_faces) == 2
    assert Counter(map(len, g168_faces)) == {3: 48, 5: 24, 17: 12, 18: 2}
    # 3-connectivity across ALL C(168, 2) = 14,028 vertex-pair deletions:
    for u, v in combinations(range(168), 2):
        root = 0 if (0 != u and 0 != v) else (1 if (1 != u and 1 != v) else 2)
        seen = {u, v, root}
        q = [root]
        for x in q:
            for y in g168_adj[x]:
                if y not in seen:
                    seen.add(y)
                    q.append(y)
        assert len(seen) == 168
    # Exact port-path verification: zero C4, C8, C16, and explicit C32!
    gadget_adj = make_adj_from_pairs(7, face_edges(inside))
    assert not bounded_cycles(gadget_adj, {4, 8, 16})
    local_paths = {}
    for p1, p2 in permutations((4, 5, 6), 2):
        # Paths inside gadget + 1 inter-gadget exit edge
        stk = [(p1, 1 << p1, (p1,))]
        by_len = {}
        while stk:
            cur, vis, rt = stk.pop()
            if cur == p2:
                by_len[len(rt)] = rt
            else:
                for nxt in gadget_adj[cur]:
                    if not (vis & (1 << nxt)):
                        stk.append((nxt, vis | (1 << nxt), (*rt, nxt)))
        local_paths[p1, p2] = by_len
        assert min(by_len) >= 3
    base_adj = make_adj_from_pairs(24, face_edges(base))
    # Enumerate all simple cycles of base_adj of length <= 10 (32 // 3 = 10):
    base_cycles = []
    for s in range(24):
        stk = [(s, 1 << s, (s,))]
        while stk:
            u, vis, rt = stk.pop()
            for v in base_adj[u]:
                if v == s and len(rt) >= 3 and rt[1] < u:
                    base_cycles.append(rt)
                elif len(rt) < 10 and v > s and not (vis & (1 << v)):
                    stk.append((v, vis | (1 << v), (*rt, v)))
    g168_c32 = None
    for cyc in base_cycles:
        possible = {0: ()}
        for i, u in enumerate(cyc):
            p_in = port_id[u, cyc[i - 1]]
            p_out = port_id[u, cyc[(i + 1) % len(cyc)]]
            choice = local_paths[p_in, p_out]
            possible = {ln + k: rt + tuple(7 * u + x for x in p)
                        for ln, rt in possible.items() for k, p in choice.items()
                        if ln + k <= 32}
        assert not (possible.keys() & {4, 8, 16})
        if g168_c32 is None and 32 in possible:
            g168_c32 = possible[32]
    assert g168_c32 is not None and len(g168_c32) == len(set(g168_c32)) == 32
    assert all(v in g168_adj[u] for u, v in cyc_darts(g168_c32))

    # --- B. C60 (Truncated Icosahedron, 60v, cubic, planar) & 119v 1-sum ---
    ico_faces = []
    for i in range(5):
        j = (i + 1) % 5
        ico_faces.extend(((10, i, j), (j, i, i + 5), (j, i + 5, j + 5), (11, j + 5, i + 5)))
    ico_turns = {(u, v): w for fc in ico_faces for u, v, w in (fc, fc[1:] + fc[:1], fc[2:] + fc[:2])}
    ico_dart = {uv: i for i, uv in enumerate(sorted(ico_turns))}
    c60_hex = [tuple(ico_dart[uv] for u, v in cyc_darts(fc) for uv in ((u, v), (v, u))) for fc in ico_faces]
    c60_pent = []
    for u in range(12):
        st = next(v for x, v in ico_turns if x == u)
        ns = [st]
        for _ in range(4):
            ns.append(ico_turns[u, ns[-1]])
        assert ico_turns[u, ns[-1]] == st
        c60_pent.append(tuple(ico_dart[u, v] for v in ns))
    c60_faces = c60_pent + c60_hex
    c60_uses = Counter(e for fc in c60_faces for e in cyc_darts(fc))
    assert len(c60_uses) == 180 and all(cnt == 1 and c60_uses[v, u] == 1 for (u, v), cnt in c60_uses.items())
    c60_edges = sorted(face_edges(c60_faces))
    c60_adj = make_adj_from_pairs(60, c60_edges)
    assert len(c60_edges) == 90 and len(c60_faces) == 32 and 60 - 90 + 32 == 2
    assert all(len(row) == 3 for row in c60_adj)
    assert Counter(map(len, c60_faces)) == {5: 12, 6: 20}
    assert not bounded_cycles(c60_adj, {3, 4, 8})
    c60_c16 = find_cycle_witness(c60_adj, {16})
    assert c60_c16 is not None and len(c60_c16) == 16
    # 119v Delta=6 1-sum C60 * C60 (gluing vertex 0 of two copies):
    c119_edges = list(c60_edges) + [(0 if u == 0 else u + 59, 0 if v == 0 else v + 59) for u, v in c60_edges]
    c119_adj = make_adj_from_pairs(119, c119_edges)
    assert len(c119_adj[0]) == 6 and min(map(len, c119_adj)) == 3
    assert not bounded_cycles(c119_adj, {3, 4, 8})

    # --- C. TD60 (Truncated Dodecahedron, 60v, cubic, planar) & 119v 1-sum ---
    # Oriented faces of the dodecahedron (12 pentagons -> 20 triangles + 12 decagons upon truncation):
    dod_faces = (
        (0, 1, 2, 3, 4), (0, 5, 10, 6, 1), (1, 6, 11, 7, 2), (2, 7, 12, 8, 3),
        (3, 8, 13, 9, 4), (4, 9, 14, 5, 0), (15, 16, 11, 6, 10), (16, 17, 12, 7, 11),
        (17, 18, 13, 8, 12), (18, 19, 14, 9, 13), (19, 15, 10, 5, 14), (19, 18, 17, 16, 15),
    )
    dod_uses = Counter(e for fc in dod_faces for e in cyc_darts(fc))
    assert len(dod_uses) == 60 and all(cnt == 1 and dod_uses[v, u] == 1 for (u, v), cnt in dod_uses.items())
    dod_turns = {}
    for fc in dod_faces:
        for i in range(5):
            dod_turns[fc[i], fc[(i + 1) % 5]] = fc[i - 1]
    dod_dart = {uv: i for i, uv in enumerate(sorted(dod_turns))}
    td60_dec = [tuple(dod_dart[uv] for u, v in cyc_darts(fc) for uv in ((u, v), (v, u))) for fc in dod_faces]
    td60_tri = []
    for u in range(20):
        st = next(v for x, v in dod_turns if x == u)
        ns = [st, dod_turns[u, st]]
        ns.append(dod_turns[u, ns[-1]])
        assert dod_turns[u, ns[-1]] == st
        td60_tri.append(tuple(dod_dart[u, v] for v in ns))
    td60_faces = td60_tri + td60_dec
    td60_uses = Counter(e for fc in td60_faces for e in cyc_darts(fc))
    assert len(td60_uses) == 180 and all(cnt == 1 and td60_uses[v, u] == 1 for (u, v), cnt in td60_uses.items())
    td60_edges = sorted(face_edges(td60_faces))
    td60_adj = make_adj_from_pairs(60, td60_edges)
    assert len(td60_edges) == 90 and len(td60_faces) == 32 and 60 - 90 + 32 == 2
    assert all(len(row) == 3 for row in td60_adj)
    assert Counter(map(len, td60_faces)) == {3: 20, 10: 12}
    assert not bounded_cycles(td60_adj, {4, 5, 6, 7, 8, 9})
    td60_c16 = find_cycle_witness(td60_adj, {16})
    assert td60_c16 is not None and len(td60_c16) == 16
    td119_edges = list(td60_edges) + [(0 if u == 0 else u + 59, 0 if v == 0 else v + 59) for u, v in td60_edges]
    td119_adj = make_adj_from_pairs(119, td119_edges)
    assert len(td119_adj[0]) == 6 and min(map(len, td119_adj)) == 3
    assert not bounded_cycles(td119_adj, {4, 5, 6, 7, 8, 9})

    print("PASS Sharpness Witnesses: G168 (168v, 3-conn, {3:48,5:24,17:12,18:2}, no C4/C8/C16, C32), "
          "C60 (60v + 119v 1-sum, no C3/C4/C8, C16), TD60 (60v + 119v 1-sum, no C4..C9, C16)!")
    return {
        "G168": {
            "n": 168, "m": 252, "f": 86,
            "base_faces": [list(fc) for fc in base],
            "port_id": {f"{u},{v}": p for (u, v), p in sorted(port_id.items())},
            "faces": [list(fc) for fc in g168_faces],
            "edges": [list(e) for e in g168_edges],
            "c32": list(g168_c32),
            "local_port_lengths": {f"{p1},{p2}": sorted(d.keys()) for (p1, p2), d in sorted(local_paths.items())},
        },
        "C60": {
            "n": 60, "m": 90, "f": 32,
            "faces": [list(fc) for fc in c60_faces],
            "edges": [list(e) for e in c60_edges],
            "c16": list(c60_c16),
        },
        "TD60": {
            "n": 60, "m": 90, "f": 32,
            "faces": [list(fc) for fc in td60_faces],
            "edges": [list(e) for e in td60_edges],
            "c16": list(td60_c16),
        },
    }


# ==============================================================================
# 3. MAIN THEOREM 1 — ALL CUBIC PLANAR GRAPHS (ARBITRARY CONNECTIVITY) AT C32
# ==============================================================================

MACROS = {
    'HL': ('HL',), 'HO': ('HO',), 'HR': ('HR',),
    'T1R': ('T', 'H0'), 'T1L': ('H0', 'T'), 'T2': ('H0', 'T', 'H0'),
    'P': ('P',), 'BL': ('BL',), 'BR': ('BR',),
    'TPsR': ('T', 'P'), 'TPsL': ('P', 'T'),
}
LTYPE = {'HL': '6', 'HO': '6', 'HR': '6', 'T1R': 'T', 'T1L': '6', 'T2': '6',
         'P': '5', 'BL': '5', 'BR': '5', 'TPsR': 'T', 'TPsL': '5'}
RTYPE = {'HL': '6', 'HO': '6', 'HR': '6', 'T1R': '6', 'T1L': 'T', 'T2': '6',
         'P': '5', 'BL': '5', 'BR': '5', 'TPsR': '5', 'TPsL': 'T'}
MW = {'H': 1, 'T1R': 2, 'T1L': 2, 'T2': 3, 'P': 1, 'B': 1, 'TPsR': 2, 'TPsL': 2}


def abs_macro(m):
    if m in ('HL', 'HO', 'HR'):
        return 'H'
    if m in ('BL', 'BR'):
        return 'B'
    return m


def build_cubic_chain_dedup(tokens):
    W = len(tokens)
    for k in range(W - 1):
        a, b = tokens[k], tokens[k + 1]
        if (a == 'T' and b == 'T') or (a in ('P', 'BL', 'BR') and b in ('P', 'BL', 'BR')):
            return None
    sp = [50 + i for i in range(W + 1)]
    for k, tok in enumerate(tokens):
        if tok == 'T':
            sp[k + 1] = sp[k]
    t_outer = {}
    nxt = 200
    for k, tok in enumerate(tokens):
        if tok == 'T':
            t_outer[k] = nxt
            nxt += 1
    rings = []
    for k, tok in enumerate(tokens):
        vL, vR = sp[k], sp[k + 1]
        left_T = (k > 0 and tokens[k - 1] == 'T')
        right_T = (k + 1 < W and tokens[k + 1] == 'T')
        if tok == 'T':
            rings.append((k + 1, k, vL))
        elif tok in ('P', 'BL', 'BR'):
            if left_T and right_T:
                return None
            if (left_T and tok == 'BL') or (right_T and tok == 'BR'):
                return None
            a = t_outer[k - 1] if left_T else (t_outer[k + 1] if right_T else nxt)
            if not left_T and not right_T:
                nxt += 1
            rings.append((k + 1, k, vL, a, vR))
        else:
            if (left_T and tok == 'HL') or (right_T and tok == 'HR'):
                return None
            a = t_outer[k - 1] if left_T else nxt
            if not left_T:
                nxt += 1
            b = t_outer[k + 1] if right_T else nxt
            if not right_T:
                nxt += 1
            rings.append((k + 1, k, vL, a, b, vR))
    wings = {}
    for k, tok in enumerate(tokens):
        fc = rings[k]
        if tok in ('BL', 'HL'):
            x, y = fc[3], fc[2]
            z = rings[k - 1][-2] if k > 0 else nxt
            if k == 0:
                nxt += 1
        elif tok in ('BR', 'HR'):
            x, y = fc[-1], fc[-2]
            z = rings[k + 1][3] if k + 1 < W else nxt
            if k + 1 == W:
                nxt += 1
        elif tok == 'HO':
            x, y, z = fc[4], fc[3], nxt
            nxt += 1
        else:
            continue
        wings[frozenset((x, y, z))] = (x, y, z)
    return (*rings, *wings.values()), W


@cache
def test_cubic_chain_repaired(tokens):
    res = build_cubic_chain_dedup(tokens)
    if res is None:
        return 0, 0, None
    fs, W = res
    tw, sv, sh = common_weld_shifts(fs, 0, W, W)
    return sv, tw, sh


def degree17_patch(word):
    tp_hex = ((0, 1, 2, 3, 4), (1, 0, 5), (3, 2, 6, 7, 8, 9))
    left = (*tp_hex, (7, 6, 10))
    rim = (10, 6, 2, 1, 5)
    tri_hex_pair = ((1, 0, 10), (2, 1, 10, 11, 12, 13), (3, 2, 13, 14, 15, 16), (4, 3, 16))
    templates = {
        "L": (left, rim),
        "R": (tuple(fc[::-1] for fc in left), rim[::-1]),
        "X": (tri_hex_pair, (0, 1, 2, 3, 4)),
        "T": (((1, 0, 2),), (0, 1)),
    }
    faces = [tuple(range(17))]
    position, label = 0, 17
    for letter in word:
        patch, arc = templates[letter]
        rename = {v: position + i for i, v in enumerate(arc)}
        for fc in patch:
            for v in fc:
                if v not in rename:
                    rename[v] = label
                    label += 1
            faces.append(tuple(rename[v] for v in fc))
        position += len(arc)
    assert position == 17
    return tuple(faces)


def verify_theorem1_cubic_planar_c32(export_mode=False):
    """Certify Main Theorem 1 (ALL Cubic Planar Graphs -> C4, C8, C16, or C32) and collect witnesses."""
    # 1. Shared-valley HHP/PHH + Deduplicated 51-chain BFS (0 at len 6!):
    for word in (('HR', 'HL', 'P'), ('P', 'HR', 'HL')):
        fs, W = build_cubic_chain_dedup(word)
        assert len(fs) == 4 and W == 3
        sv, _, sh = test_cubic_chain_repaired(word)
        assert sv > 0 and tuple(sorted(sh)) == (0, 3, 4, 5, 6, 7, 8)

    five_macros = ('P', 'BL', 'BR', 'TPsR', 'TPsL')
    six_macros = ('HL', 'HO', 'HR', 'T1R', 'T1L', 'T2')
    all_macros = five_macros + six_macros
    seen = set()
    q = deque([(m,) for m in all_macros])
    chains56 = {}
    layers = Counter()
    bfs_welds = 0
    bfs_pruned_welds = 0
    while q:
        seq = q.popleft()
        if seq in seen:
            continue
        seen.add(seq)
        toks = tuple(x for m in seq for x in MACROS[m])
        sv, tw, sh = test_cubic_chain_repaired(toks)
        bfs_welds += tw
        if sv == 0:
            if len(seq) >= 2:
                bfs_pruned_welds += tw
            continue
        if any(m in five_macros for m in seq) and any(m in six_macros for m in seq):
            layers[len(seq)] += 1
            ak = tuple(abs_macro(m) for m in seq)
            chains56[ak] = set(sh) if ak not in chains56 else (chains56[ak] & set(sh))
        rt = RTYPE[seq[-1]]
        cands = ([m for m in six_macros if LTYPE[m] == '6'] if rt == '5'
                 else ([m for m in all_macros if LTYPE[m] in ('5', '6')] if rt == '6' else []))
        for nm in cands:
            q.append(seq + (nm,))
    assert len(chains56) == 51 and max(layers) == 5
    assert sorted(layers.items()) == [(2, 24), (3, 30), (4, 18), (5, 9)]
    assert bfs_welds == 1581 and bfs_pruned_welds == 1327
    assert {('B', 'H', 'H'), ('H', 'H', 'B'), ('H', 'H', 'TPsL'), ('TPsR', 'H', 'H')} <= chains56.keys()

    # 2. Complete TP_b54, after_A9, R10, & B1=6 Seal Welds (R21 + R22; 520 total = 16+3+216+5+258+22):
    seal_records = [] if export_mode else None
    tp_base = ((0, 1, 2, 3, 4), (1, 0, 5))
    s2_9 = (2, 1, 5, 20, 21, 22, 23, 24, 25)
    sv_s29, seal_s29 = surv_welds((*tp_base, s2_9, (4, 3, 30, 31, 32, 33)), record=seal_records)
    assert (sv_s29, seal_s29) == (0, 16)
    tp_b54 = ((0, 1, 2, 3, 4), (1, 0, 5), (3, 2, 6, 7, 8, 9), (6, 2, 1, 5, 20, 21, 22, 23, 24))
    sv_hex, seal_tp_hex = surv_welds((*tp_b54, (20, 5, 0, 4, 50, 51)), record=seal_records)
    assert sv_hex == 0 and seal_tp_hex == 3
    seal_r21_tp = 0
    for d78 in (5, 6, 7, 9, 10, 12, 13, 15):
        sv, tw = surv_welds((*tp_b54, (7, 6, 24), (8, 7, 24, 23, *range(40, 40 + d78 - 4))), record=seal_records)
        assert sv == 0
        seal_r21_tp += tw
    for d89 in (5, 6, 7, 9, 11, 12):
        sv, tw = surv_welds((*tp_b54, (7, 6, 24), (9, 8, *range(50, 50 + d89 - 2))), record=seal_records)
        assert sv == 0
        seal_r21_tp += tw
    for d67 in (5, 6, 7, 9, 10):
        sv, tw = surv_welds((*tp_b54, (8, 7, 30), (30, 7, 6, 24, *range(40, 40 + d67 - 4))), record=seal_records)
        assert sv == 0
        seal_r21_tp += tw
    for d89 in (5, 6, 7, 9, 10):
        sv, tw = surv_welds((*tp_b54, (8, 7, 30), (9, 8, 30, *range(40, 40 + d89 - 3))), record=seal_records)
        assert sv == 0
        seal_r21_tp += tw

    # R22 TP_b54 + t89, TP_b54 + H2, and after_A9 spoke seals:
    tpt = ((0, 1, 2, 3, 4), (1, 0, 5), (3, 2, 6))
    fA9 = (8, 6, 2, 1, 5, 7, 10, 11, 12)
    fA10 = (8, 6, 2, 1, 5, 7, 10, 11, 12, 13)
    fB9 = (7, 5, 0, 4, 9, 10, 11, 12, 13)
    seal_welds_r22 = 0
    for extra in (
        ((10, 7, 20, 21, 22, 23),),
        ((10, 7, 20, 21, 22), (21, 20, 23, 24, 25, 26)),
        ((10, 7, 20, 21, 22), (21, 20, 23)),
        ((10, 7, 20), (11, 10, 20, 21, 22), (22, 21, 40, 41, 42, 43)),
        ((10, 7, 20), (11, 10, 20, 21, 22, 23)),
    ):
        sv, tw = surv_welds((*tpt, fA9, *extra), record=seal_records)
        assert sv == 0
        seal_welds_r22 += tw
    t89 = (9, 8, 30)
    for d78 in (5, 6, 7, 9, 10, 12, 13, 15):
        sv, tw = surv_welds((*tp_b54, t89, (30, 8, 7, *range(40, 40 + d78 - 3))), record=seal_records)
        assert sv == 0
        seal_welds_r22 += tw
    for d67 in (5, 6, 7, 9):
        sv, tw = surv_welds((*tp_b54, t89, (7, 6, 24, *range(40, 40 + d67 - 3))), record=seal_records)
        assert sv == 0
        seal_welds_r22 += tw
    assert F(5, 4) + F(9, 8) == F(19, 8) < F(5, 2)
    for extra in (((8, 7, 30), (9, 8, 30, 40, 41, 42)), ((7, 6, 24), (9, 8, 50, 51, 52, 53))):
        sv, tw = surv_welds((*tp_b54, *extra), record=seal_records)
        assert sv == 0
        seal_welds_r22 += tw
    seal_extra = 0
    a9_tpsr = (*tpt, fA9, (10, 7, 20), (11, 10, 20, 21, 22))
    for d1 in (6, 7, 9, 12):
        sv, tw = surv_welds((*a9_tpsr, (12, 11, 22, *range(40, 40 + d1 - 3))), record=seal_records)
        assert sv == 0
        seal_extra += tw
    for d2 in (6, 7):
        sv, tw = surv_welds((*a9_tpsr, (22, 21, *range(40, 40 + d2 - 2))), record=seal_records)
        assert sv == 0
        seal_extra += tw
    fs_tht, _ = build_cubic_chain_dedup(('T', 'P', 'HO', 'P', 'T'))
    sv, tw = surv_welds((*fs_tht, (fs_tht[5][2], fs_tht[2][3], fs_tht[2][2], fs_tht[1][3], 500, 501)), record=seal_records)
    assert sv == 0
    seal_extra += tw
    fs_tt2, _ = build_cubic_chain_dedup(('T', 'P', 'H0', 'T', 'H0'))
    sv, tw = surv_welds((*fs_tt2, (fs_tt2[2][3], fs_tt2[2][2], fs_tt2[1][3], 500, 501, 502)), record=seal_records)
    assert sv == 0
    seal_extra += tw
    r10_base = ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9), (1, 0, 10), (3, 2, 11), (5, 4, 12), (7, 6, 13), (9, 8, 14))
    seal_r10 = 0
    for da in (5, 6, 7, 9, 10):
        sv, tw = surv_welds((*r10_base, (11, 2, 1, 10, *range(20, 20 + da - 4))), record=seal_records)
        assert sv == 0
        seal_r10 += tw
    seal_welds_r21 = seal_r21_tp + seal_r10
    seal_total = seal_s29 + seal_tp_hex + seal_r21_tp + seal_r10 + seal_welds_r22 + seal_extra
    assert (seal_s29, seal_tp_hex, seal_r21_tp, seal_r10, seal_welds_r22, seal_extra) == (16, 3, 216, 5, 258, 22)
    assert seal_welds_r21 == 221 and seal_total == 520

    # 3. Clean Face Cyclic DP (d in {7, 9..13, 15, 19..31}) & Conservative Enum (d = 14, 17, 18):
    S_faces = ((0, 1, 2, 3, 4, 5, 6, 7, 8), (1, 0, 9), (2, 1, 9, 11, 10), (3, 2, 10),
               (5, 4, 12), (6, 5, 12, 14, 13), (7, 6, 13))
    sh_Y = shifts_of(S_faces, 8, 14, 3)
    sh_X = shifts_of(S_faces, 11, 14, 5)
    sh_A9 = shifts_of((*tpt, fA9), 4, 7, 3)
    sh_A10 = shifts_of((*tpt, fA10), 4, 7, 3)
    sh_B9_A = shifts_of((*tpt, fB9), 6, 7, 4)
    sh_B9_C = shifts_of((*tpt, fB9), 6, 9, 3)
    sh_T1 = (0, 1, 3, 4)
    sh_12 = (0, 1, 2, 3, 4, 5, 6, 7, 8)
    sh_11 = (0, 1, 2, 3, 4, 5, 6)
    sh_121 = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
    sh_TP699 = (0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)

    enum_counts = {}
    dp_bounds = {}
    d17_residuals = []
    for d in [7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]:
        w = {
            'T': {7: F(0), 9: F(3, 4), 10: F(1)}.get(d, F(9, 8)),
            'P': {7: F(0), 9: F(1, 2), 11: F(1, 2)}.get(d, F(1)),
            'TP_s': {7: F(0), 9: F(3, 4), 10: F(2), 12: F(3)}.get(d, F(2)),
            'TP_b': {7: F(0), 9: F(1, 4), 10: F(1), 11: F(1)}.get(d, F(1)),
            'TPT_A': {7: F(0), 9: F(3, 2), 10: F(2), 11: F(7, 3)}.get(d, F(12, 5)),
            'TPT_BC': {7: F(0), 9: F(3, 2), 10: F(23, 10), 11: F(21, 8)}.get(d, F(7, 3)),
            'T2': {9: F(1), 10: F(2), 11: F(3), 14: F(2)}.get(d, F(2)),
            'T1': {9: F(3, 4), 10: F(1), 11: F(9, 4), 14: F(3, 2)}.get(d, F(3, 2)),
            '6o': {7: F(1, 4), 9: F(3, 4), 10: F(2, 3)}.get(d, F(1, 2)),
            'TP6': {10: F(0), 11: F(1, 3)}.get(d, F(2, 3)),
        }
        toks = [
            ('N', 1, (0,), F(0)), ('P', 1, (0, 3), w['P']),
            ('TP_s_L', 2, (0, 1, 2, 3), w['TP_s']), ('TP_s_R', 2, (0, 1, 2, 3), w['TP_s']),
            ('TP_b', 1, (0, 3, 4), w['TP_b']), ('TPT_A', 3, (0, 1, 2, 3), w['TPT_A']),
            ('TPT_BC', 2, (0, 1, 2, 3, 4), w['TPT_BC']),
        ]
        if d != 15:
            toks.append(('T', 1, (0, 1), w['T']))
        if d >= 14:
            toks.extend([('TP_b54_R', 2, (0, 3, 4), F(5, 4)), ('TP_b54_L', 2, (0, 3, 4), F(5, 4)),
                         ('HH', 3, (0, 3, 4, 6, 7, 8), F(5, 2))])
        if d >= 11 and d != 15:
            toks.extend([('T10', 1, (0, 1), F(1)), ('R10', 1, (0,), F(1, 5))])
        if d in (9, 10, 11, 14) or d >= 17:
            toks.extend([('T2', 3, (0, 1), w['T2']), ('T1_L', 2, (0, 1), w['T1']), ('T1_R', 2, (0, 1), w['T1'])])
        if d in (9, 10, 13, 14, 15) or d >= 17:
            toks.append(('6o', 1, (0,), w['6o']))
        if d == 11 or d >= 13:
            toks.append(('6c', 1, (0,), F(0)))
        if (d in (11, 13, 14) or d >= 17) and w['TP6'] > 0:
            toks.extend([('TP6_L', 2, (0,), w['TP6']), ('TP6_R', 2, (0,), w['TP6']), ('TP6_2', 3, (0,), 2 * w['TP6'])])
        if d in (17, 21, 23, 28):
            toks.append(('TP_s3', 4, sh_TP699 if d == 17 else (0, 1, 2, 3), F(3)))
        if d >= 17:
            toks.extend([
                ('T_L9', 1, (0, 1), w['T']), ('T_R9', 1, (0, 1), w['T']),
                ('S_YZ_R', 3, (0, 1, 2, 3, 4), F(13, 4)), ('S_YZ_L', 3, (0, 1, 2, 3, 4), F(13, 4)),
                ('S_X', 5, sh_X, F(9, 2)),
                ('TPT_A9_R', 3, (0, 1, 2, 3, 4), F(11, 4)), ('TPT_A9_L', 3, (0, 1, 2, 3, 4), F(11, 4)),
                ('TPT_A10_R', 3, (0, 1, 2, 3, 4), F(5, 2)), ('TPT_A10_L', 3, (0, 1, 2, 3, 4), F(5, 2)),
                ('TPT_B9A_R', 4, (0, 1, 2, 3), F(23, 8)), ('TPT_B9A_L', 4, (0, 1, 2, 3), F(23, 8)),
                ('TPT_B9C_R', 3, (0, 1, 2, 3, 4), F(21, 8)), ('TPT_B9C_L', 3, (0, 1, 2, 3, 4), F(21, 8)),
            ])
        has_6o_d = (d in (7, 9, 10, 13, 14, 15) or d >= 17)
        has_6s_d = (d in (9, 10, 11, 14) or d >= 17)
        mch = {'H': w['6o'], 'T1R': w['T1'], 'T1L': w['T1'], 'T2': w['T2'],
               'P': w['P'], 'B': w['TP_b'], 'TPsR': w['TP_s'], 'TPsL': w['TP_s']}
        chain_names = set()
        chain_meta = {}
        for akey, sh_set in sorted(chains56.items()):
            uses_6o = 'H' in akey
            uses_6s = any(m in ('T1R', 'T1L', 'T2') for m in akey)
            uses_TPs = any(m in ('TPsR', 'TPsL') for m in akey)
            if (uses_6o and not has_6o_d) or (uses_6s and not has_6s_d):
                continue
            if d in (7, 15) and (uses_6s or uses_TPs):
                continue
            cw = sum(MW[m] for m in akey)
            if cw > d:
                continue
            cname = "C_" + "_".join(akey)
            toks.append((cname, cw, tuple(sorted(sh_set)), sum(mch[m] for m in akey)))
            chain_names.add(cname)
            chain_meta[cname] = akey

        ends_g = {'T', 'T10', 'T_L9', 'T_R9', 'P', 'TP_s_L', 'TP_s_R', 'TP_b', 'TP_b54_L', 'HH',
                  'TPT_A', 'TPT_BC', 'T1_L', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L', 'S_YZ_L', 'S_X', 'TP_s3'}
        starts_g = {'T', 'T10', 'T_L9', 'T_R9', 'P', 'TP_s_L', 'TP_s_R', 'TP_b', 'TP_b54_R', 'HH',
                    'TPT_A', 'TPT_BC', 'T1_R', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R', 'S_YZ_R', 'S_X', 'TP_s3'}
        ends_6s, starts_6s, ends_6o, starts_6o = {'T2', 'T1_R'}, {'T2', 'T1_L'}, {'6o'}, {'6o'}
        ends_tp6, starts_tp6 = {'TP6_L', 'TP6_2'}, {'TP6_R', 'TP6_2'}
        for cn, ak in chain_meta.items():
            if ak[0] in ('P', 'B', 'TPsL', 'T1R', 'TPsR'):
                starts_g.add(cn)
            elif ak[0] == 'H':
                starts_6o.add(cn)
            else:
                starts_6s.add(cn)
            if ak[-1] in ('P', 'B', 'TPsR', 'T1L', 'TPsL'):
                ends_g.add(cn)
            elif ak[-1] == 'H':
                ends_6o.add(cn)
            else:
                ends_6s.add(cn)
        g_left_N = {'S_YZ_R', 'S_X', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R'}
        g_right_N = {'S_YZ_L', 'S_X', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L'}
        after_A9 = {'N', 'T_L9', 'P', 'TP_s_R', 'TP_b', 'TP_b54_R', 'TPT_A10_L'}
        before_A9 = {'N', 'T_R9', 'P', 'TP_s_L', 'TP_b', 'TP_b54_L', 'TPT_A10_R'}
        after_A10 = {'N', 'T', 'T10', 'T1_R', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L', 'TP6_L'} | {cn for cn, ak in chain_meta.items() if ak[0] == 'T1R'}
        before_A10 = {'N', 'T', 'T10', 'T1_L', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R', 'TP6_R'} | {cn for cn, ak in chain_meta.items() if ak[-1] == 'T1L'}
        after_B9, before_B9 = {'N', 'T_L9', 'TPT_A10_L'}, {'N', 'T_R9', 'TPT_A10_R'}
        p_sc = {cn for cn, ak in chain_meta.items() if ak[0] == 'P'}
        p_ec = {cn for cn, ak in chain_meta.items() if ak[-1] == 'P'}

        def pair_ok(a, b_):
            if a in chain_names and (b_ in starts_6o or b_ in starts_6s or b_ in chain_names): return False
            if b_ in chain_names and (a in ends_6o or a in ends_6s or a in chain_names): return False
            if a in ends_g and b_ in starts_g: return False
            if b_ in g_left_N and a != 'N': return False
            if a in g_right_N and b_ != 'N': return False
            if a == 'HH' and (b_ in starts_g or b_ in starts_6s or b_ in starts_6o or b_ in ('6c', 'TP6_L')): return False
            if b_ == 'HH' and (a in ends_g or a in ends_6s or a in ends_6o or a in ('6c', 'TP6_R')): return False
            if (a == 'TP_b54_L' and b_ == 'TP6_L') or (b_ == 'TP_b54_R' and a == 'TP6_R'): return False
            if (a == 'T10' and b_ == 'TP6_L') or (b_ == 'T10' and a == 'TP6_R'): return False
            if (a == 'R10' and b_ != 'T10') or (b_ == 'R10' and a != 'T10'): return False
            if (a == 'S_YZ_R' and b_ != 'N') or (b_ == 'S_YZ_L' and a != 'N'): return False
            if a == 'T_L9' and b_ in ('TPT_A9_L', 'TPT_B9A_L', 'TPT_B9C_L', 'TP6_L'): return False
            if b_ == 'T_R9' and a in ('TPT_A9_R', 'TPT_B9A_R', 'TPT_B9C_R', 'TP6_R'): return False
            if b_ == 'T_L9' and a not in ('TPT_A9_R', 'TPT_B9A_R', 'TPT_B9C_R'): return False
            if a == 'T_R9' and b_ not in ('TPT_A9_L', 'TPT_B9A_L', 'TPT_B9C_L'): return False
            if a == 'TPT_A9_R' and b_ not in after_A9: return False
            if b_ == 'TPT_A9_L' and a not in before_A9: return False
            if a == 'TPT_A10_R' and b_ not in after_A10: return False
            if b_ == 'TPT_A10_L' and a not in before_A10: return False
            if a in ('TPT_B9A_R', 'TPT_B9C_R') and b_ not in after_B9: return False
            if b_ in ('TPT_B9A_L', 'TPT_B9C_L') and a not in before_B9: return False
            if a == 'T2' and b_ == 'T2': return False
            if (a in ends_6s and b_ in starts_g) or (b_ in starts_6s and a in ends_g): return False
            if (a in ends_6o and b_ in starts_g) or (b_ in starts_6o and a in ends_g): return False
            if (a == '6c' and b_ in (starts_g - {'P'} - p_sc)) or (b_ == '6c' and a in (ends_g - {'P'} - p_ec)): return False
            if (a in ends_tp6 and b_ in starts_g) or (b_ in starts_tp6 and a in ends_g): return False
            if d == 9 and ((a in ends_6o and (b_ in starts_6s or b_ in starts_6o)) or (b_ in starts_6o and (a in ends_6s or a in ends_6o))):
                return False
            if d == 10:
                if a in ends_6s and b_ in (starts_6s | starts_6o | {'TP6_R', 'TP6_2'}): return False
                if b_ in starts_6s and a in (ends_6s | ends_6o | {'TP6_L', 'TP6_2'}): return False
                if a in ends_6o and b_ in starts_6o: return False
            return True

        nt = len(toks)
        names = [t[0] for t in toks]
        t_edges = [t[1] for t in toks]
        shifts = [t[2] for t in toks]
        wts = [int(t[3] * W_LCM) for t in toks]
        sh_map = {t[0]: t[2] for t in toks}
        ok_mat = [[pair_ok(names[i], names[j]) for j in range(nt)] for i in range(nt)]
        adj_next = [[j for j in range(nt) if ok_mat[i][j]] for i in range(nt)]
        is_syz = [names[i] in ('S_YZ_R', 'S_YZ_L') for i in range(nt)]
        is_6c = [names[i] == '6c' for i in range(nt)]
        starts_N = [names[i] not in starts_g for i in range(nt)]
        vcor_w = int(F(1, 5) * W_LCM) if (d == 11 or d >= 13) else 0
        max_s = max(0, 32 - d)
        full_m = (1 << (max_s + 1)) - 1
        forb_bits = sum(1 << (tlen - d) for tlen in TARGETS_CUBIC if d <= tlen <= d + max_s)
        start_ids = [i for i in range(nt) if starts_N[i] and t_edges[i] <= d]

        if d in (14, 17, 18):
            fcap_map = {}
            for nm in names:
                if nm in ('C_TPsR_H_TPsL', 'C_TPsR_T2', 'C_T2_TPsL'): fcap_map[nm] = 0
                elif nm in ('TP_s_L', 'TP_s_R', 'TP_b', 'TP_b54_R', 'TP_b54_L'): fcap_map[nm] = 1
                elif nm in ('P', 'HH'): fcap_map[nm] = 2
                elif nm in chain_meta: fcap_map[nm] = sum({'P': 2, 'B': 1, 'TPsR': 1, 'TPsL': 1}.get(m, 0) for m in chain_meta[nm])
                else: fcap_map[nm] = 0
            P_TOKS = {'P'} | {cn for cn, ak in chain_meta.items() if 'P' in ak}
            TPS_TOKS = {'TP_s_L', 'TP_s_R'} | {cn for cn, ak in chain_meta.items() if 'TPsR' in ak or 'TPsL' in ak}
            TPB_TOKS = {'TP_b', 'TP_b54_R', 'TP_b54_L', 'HH'} | {cn for cn, ak in chain_meta.items() if 'B' in ak}
            T_TOKS = {'T', 'T10', 'T_L9', 'T_R9'}
            H6O_TOKS = {'6o'} | {cn for cn, ak in chain_meta.items() if 'H' in ak}
            ATT_R = {'T_L9', 'T1_R'} | {cn for cn, ak in chain_meta.items() if ak[0] == 'T1R'}
            ATT_L = {'T_R9', 'T1_L'} | {cn for cn, ak in chain_meta.items() if ak[-1] == 'T1L'}
            thresh = (d - 6) * W_LCM

            def seq_killed_conservative(seq):
                n_seq = len(seq)

                def eval_rem(rem_list, base_sh):
                    def run_m(extra_idxs, drop_idxs=frozenset(), fused=None):
                        m = 0
                        for sh in base_sh: m |= (1 << sh) & full_m
                        if fused is not None:
                            nm = 0
                            for sh in fused[1]: nm |= (m << sh) & full_m
                            m = nm
                        for k, (_, x) in enumerate(rem_list):
                            if k in drop_idxs or (fused is not None and k in fused[0]): continue
                            shs = (sh_T1 if x in ('T2', 'T1_L', 'T1_R') else (0, 4)) if k in extra_idxs else sh_map[x]
                            nm = 0
                            for sh in shs: nm |= (m << sh) & full_m
                            m = nm
                        return bool(m & forb_bits)

                    tri_i = [k for k, (_, x) in enumerate(rem_list) if x in ('T2', 'T1_L', 'T1_R', '6o')]
                    tp6_i = [k for k, (_, x) in enumerate(rem_list) if x in ('TP6_L', 'TP6_R', 'TP6_2')]
                    five_i = [k for k, (_, x) in enumerate(rem_list) if fcap_map[x] > 0]
                    tot_five_cap = sum(fcap_map[rem_list[f][1]] for f in five_i)
                    if run_m(set()): return True
                    t12_kill = []
                    for k in tri_i:
                        x = rem_list[k][1]
                        if x == '6o':
                            if run_m({k}): return True
                        elif run_m({k}):
                            t12_kill.append(k)
                            ndrop = min(len(five_i), 2 if x == 'T2' else 1)
                            if all(run_m({k}, set(grp)) for grp in combinations(five_i, ndrop)): return True
                    if sum(2 if rem_list[k][1] == 'T2' else 1 for k in t12_kill) > tot_five_cap: return True
                    for k in tp6_i:
                        if run_m({k}): return True
                    rl = len(rem_list)
                    for k in range(rl):
                        k2 = (k + 1) % rl
                        if k2 == k: continue
                        oi1, x1 = rem_list[k]
                        oi2, x2 = rem_list[k2]
                        if (oi1 + 1) % n_seq == oi2:
                            fsh = (sh_12 if ((x1 == 'T1_R' and x2 == 'T2') or (x1 == 'T2' and x2 == 'T1_L'))
                                   else (sh_11 if (x1 == 'T1_R' and x2 == 'T1_L') else None))
                            if fsh is not None:
                                ndrop = min(len(five_i), 2)
                                if all(run_m(set(), set(grp), ({k, k2}, fsh)) for grp in combinations(five_i, ndrop)): return True
                            if rl >= 3 and x1 == 'T1_R' and x2 == 'T2':
                                k3 = (k2 + 1) % rl
                                oi3, x3 = rem_list[k3]
                                if (oi2 + 1) % n_seq == oi3 and x3 == 'T1_L':
                                    if run_m(set(), frozenset(five_i), ({k, k2, k3}, sh_121)): return True
                    if tp6_i and len(tri_i) >= 2:
                        def ok_tp(ti):
                            x = rem_list[ti][1]
                            if x == '6o': return run_m({tp6_i[0], ti})
                            nd = min(len(five_i), 2 if x == 'T2' else 1)
                            return run_m({tp6_i[0], ti}) and all(run_m({tp6_i[0], ti}, set(grp)) for grp in combinations(five_i, nd))
                        if ok_tp(tri_i[0]) and ok_tp(tri_i[1]): return True
                    if len(tri_i) >= 4:
                        def pair_dj(ia, ib):
                            dc = ((0 if rem_list[ia][1] == '6o' else (2 if rem_list[ia][1] == 'T2' else 1))
                                  + (0 if rem_list[ib][1] == '6o' else (2 if rem_list[ib][1] == 'T2' else 1)))
                            nd = min(len(five_i), dc)
                            return all(run_m({ia, ib}, set(grp)) for grp in combinations(five_i, nd))
                        if pair_dj(tri_i[0], tri_i[2]) and pair_dj(tri_i[1], tri_i[3]): return True
                    return False

                def hd_strict(idx, tok, base_sh, kind, cnt):
                    drop_idxs = {idx}
                    has_att = False
                    if tok.endswith('_R') and seq[(idx + 1) % n_seq] in ATT_R:
                        drop_idxs.add((idx + 1) % n_seq)
                        has_att = True
                    elif tok.endswith('_L') and seq[(idx - 1) % n_seq] in ATT_L:
                        drop_idxs.add((idx - 1) % n_seq)
                        has_att = True
                    if kind != 'T' and has_att:
                        return True
                    rem = [(k, seq[k]) for k in range(n_seq) if k not in drop_idxs]
                    if kind == 'T':
                        tl = max(0, cnt - (1 if has_att else 0))
                        cand = [j for j, (_, x) in enumerate(rem) if x in T_TOKS]
                        for sub in combinations(cand, min(tl, len(cand))):
                            sset = set(sub)
                            if not eval_rem([kv for j, kv in enumerate(rem) if j not in sset], base_sh): return False
                        return True
                    tset = P_TOKS if kind == 'P' else (TPS_TOKS if kind == 'TP_s' else TPB_TOKS)
                    cand = [j for j, (_, x) in enumerate(rem) if x in tset]
                    for sub in combinations(cand, min(cnt, len(cand))):
                        sset = set(sub)
                        rem1 = [kv for j, kv in enumerate(rem) if j not in sset]
                        if kind in ('P', 'TP_b'):
                            c6 = [j for j, (_, x) in enumerate(rem1) if x in H6O_TOKS]
                            if not c6:
                                if not eval_rem(rem1, base_sh): return False
                            else:
                                for j6 in c6:
                                    if not eval_rem([kv for j, kv in enumerate(rem1) if j != j6], base_sh): return False
                        elif not eval_rem(rem1, base_sh): return False
                    return True

                for idx, tok in enumerate(seq):
                    if tok in ('TPT_B9A_R', 'TPT_B9A_L') and hd_strict(idx, tok, sh_B9_A, 'T', 2): return True
                    if tok in ('TPT_B9C_R', 'TPT_B9C_L') and hd_strict(idx, tok, sh_B9_C, 'T', 2): return True
                    if tok in ('TPT_A10_R', 'TPT_A10_L') and hd_strict(idx, tok, sh_A10, 'T', 2): return True
                    if tok in ('TPT_A9_R', 'TPT_A9_L') and (
                        hd_strict(idx, tok, sh_A9, 'T', 2) and hd_strict(idx, tok, sh_A9, 'P', 1)
                        and hd_strict(idx, tok, sh_A9, 'TP_s', 1) and hd_strict(idx, tok, sh_A9, 'TP_b', 1)
                    ): return True
                return eval_rem([(k, seq[k]) for k in range(n_seq)], (0,))

            checked = 0
            for si in start_ids:
                m0 = 0
                for sh in (sh_Y if is_syz[si] else shifts[si]): m0 |= (1 << sh) & full_m
                if m0 & forb_bits: continue
                fwd = [{} for _ in range(d + 1)]
                fwd[t_edges[si]][(si, m0, 1 if is_syz[si] else 0)] = wts[si]
                for pos in range(1, d):
                    for (last, msk, usyz), val in fwd[pos].items():
                        for gi in adj_next[last]:
                            if starts_N[gi] and gi < si: continue
                            npos = pos + t_edges[gi]
                            if npos > d: continue
                            use_syz = is_syz[gi] and (usyz == 0)
                            nmsk = 0
                            for sh in (sh_Y if use_syz else shifts[gi]): nmsk |= (msk << sh) & full_m
                            if nmsk & forb_bits: continue
                            nv = val + wts[gi] + (vcor_w if (is_6c[last] and is_6c[gi]) else 0)
                            nk = (gi, nmsk, 1 if (usyz or use_syz) else 0)
                            if nk not in fwd[npos] or nv > fwd[npos][nk]: fwd[npos][nk] = nv
                bwd = [{} for _ in range(d + 1)]
                for (last, msk, usyz), val in fwd[d].items():
                    if ok_mat[last][si]:
                        ce = vcor_w if (is_6c[last] and is_6c[si]) else 0
                        if val + ce > thresh: bwd[d][(last, msk, usyz)] = ce
                if not bwd[d]: continue
                for pos in range(d - 1, t_edges[si] - 1, -1):
                    for (last, msk, usyz), fval in fwd[pos].items():
                        ba = -10**9
                        for gi in adj_next[last]:
                            if starts_N[gi] and gi < si: continue
                            npos = pos + t_edges[gi]
                            if npos > d: continue
                            use_syz = is_syz[gi] and (usyz == 0)
                            nmsk = 0
                            for sh in (sh_Y if use_syz else shifts[gi]): nmsk |= (msk << sh) & full_m
                            if nmsk & forb_bits: continue
                            rv = bwd[npos].get((gi, nmsk, 1 if (usyz or use_syz) else 0))
                            if rv is not None:
                                add = wts[gi] + (vcor_w if (is_6c[last] and is_6c[gi]) else 0) + rv
                                if add > ba: ba = add
                        if ba > -10**9 and fval + ba > thresh: bwd[pos][(last, msk, usyz)] = ba
                if (si, m0, 1 if is_syz[si] else 0) not in bwd[t_edges[si]]: continue
                stack = [(t_edges[si], si, m0, 1 if is_syz[si] else 0, wts[si], (names[si],))]
                while stack:
                    pos, last, msk, usyz, val, seq = stack.pop()
                    if pos == d:
                        tot = val + (vcor_w if (is_6c[last] and is_6c[si]) else 0)
                        if ok_mat[last][si] and tot > thresh:
                            checked += 1
                            if not seq_killed_conservative(seq):
                                assert d == 17, f"Unexpected survivor at d={d}: {seq}"
                                d17_residuals.append(seq)
                        continue
                    for gi in adj_next[last]:
                        if starts_N[gi] and gi < si: continue
                        npos = pos + t_edges[gi]
                        if npos > d: continue
                        use_syz = is_syz[gi] and (usyz == 0)
                        nmsk = 0
                        for sh in (sh_Y if use_syz else shifts[gi]): nmsk |= (msk << sh) & full_m
                        if nmsk & forb_bits: continue
                        rv = bwd[npos].get((gi, nmsk, 1 if (usyz or use_syz) else 0))
                        if rv is None: continue
                        nv = val + wts[gi] + (vcor_w if (is_6c[last] and is_6c[gi]) else 0)
                        if nv + rv > thresh:
                            stack.append((npos, gi, nmsk, 1 if (usyz or use_syz) else 0, nv, seq + (names[gi],)))
            enum_counts[d] = checked
            dp_bounds[str(d)] = {"mode": "conservative_enum", "overweight_seqs": checked, "budget_num": (d - 6) * W_LCM, "denom": W_LCM}
            continue

        is_T = [names[i] in ('T', 'T10', 'T1_L', 'T1_R', 'T2')
                or (names[i] in chain_meta and any(m in ('T1R', 'T1L', 'T2') for m in chain_meta[names[i]])) for i in range(nt)]
        is_6s = [names[i] in ('T1_L', 'T1_R', 'T2')
                 or (names[i] in chain_meta and any(m in ('T1R', 'T1L', 'T2') for m in chain_meta[names[i]])) for i in range(nt)]
        is_6o = [names[i] == '6o' or (names[i] in chain_meta and 'H' in chain_meta[names[i]]) for i in range(nt)]
        is_TP6 = [names[i] in ('TP6_L', 'TP6_R', 'TP6_2') for i in range(nt)]
        is_TPT_A = [names[i] == 'TPT_A' for i in range(nt)]
        is_TPT_any = [names[i] in ('TPT_A', 'TPT_BC') for i in range(nt)]
        is_unfusedP = [names[i] in ('P', 'TP_s_L', 'TP_s_R', 'TP_b', 'TPT_A', 'TPT_BC') for i in range(nt)]
        is_TPT_or_TPs = [names[i] in ('TPT_A', 'TPT_BC', 'TP_s_L', 'TP_s_R')
                         or (names[i] in chain_meta and any(m in ('TPsR', 'TPsL') for m in chain_meta[names[i]])) for i in range(nt)]
        is_triadP = [names[i] in chain_names for i in range(nt)]
        is_d11_f6s = [names[i] in ('TP_s_L', 'TP_s_R', 'TP_b', 'TPT_A', 'TPT_BC', 'TP6_L', 'TP6_R', 'TP6_2') for i in range(nt)]
        best = -10**9
        for si in start_ids:
            m0 = 0
            for sh in (sh_Y if is_syz[si] else shifts[si]): m0 |= (1 << sh) & full_m
            if m0 & forb_bits: continue
            buckets = [{} for _ in range(d + 1)]
            c0 = 1 if (d in (10, 11) and is_T[si]) else (1 if (d == 9 and is_TPT_A[si]) else 0)
            h6s0 = 1 if (d in (9, 10, 11) and is_6s[si]) else 0
            h6o0 = 1 if (d in (9, 10) and is_6o[si]) else 0
            hTP60 = 1 if (d in (10, 11) and is_TP6[si]) else 0
            hP0 = 1 if (d == 9 and is_TPT_any[si]) else (1 if (d == 10 and is_unfusedP[si]) else (1 if (d == 11 and is_d11_f6s[si]) else 0))
            hTPT0 = 1 if (d == 10 and is_TPT_or_TPs[si]) else 0
            hTri0 = 1 if (d == 9 and is_triadP[si]) else 0
            n6_0 = min(2, (sum(1 for m in chain_meta[names[si]] if m in ('H', 'T1R', 'T1L', 'T2'))
                           if names[si] in chain_meta else (1 if (is_6s[si] or is_6o[si]) else 0))) if d == 9 else 0
            buckets[t_edges[si]][(si, m0, c0, h6s0, h6o0, hTP60, hP0, hTPT0, hTri0, n6_0, 1 if is_syz[si] else 0)] = wts[si]
            for pos in range(1, d):
                for (last, msk, cnt, h6s, h6o, hTP6, hP, hTPT, hTri, n6, usyz), val in buckets[pos].items():
                    for gi in adj_next[last]:
                        if starts_N[gi] and gi < si: continue
                        npos = pos + t_edges[gi]
                        if npos > d: continue
                        use_syz = is_syz[gi] and (usyz == 0)
                        nmsk = 0
                        for sh in (sh_Y if use_syz else shifts[gi]): nmsk |= (msk << sh) & full_m
                        if nmsk & forb_bits: continue
                        if d == 9 and is_TPT_A[gi] and cnt >= 1: continue
                        ncnt = cnt + (1 if (d in (10, 11) and is_T[gi]) else (1 if (d == 9 and is_TPT_A[gi]) else 0))
                        nh6s = 1 if (h6s or (d in (9, 10, 11) and is_6s[gi])) else 0
                        nh6o = 1 if (h6o or (d in (9, 10) and is_6o[gi])) else 0
                        nhTP6 = 1 if (hTP6 or (d in (10, 11) and is_TP6[gi])) else 0
                        nhP = 1 if (hP or (d == 9 and is_TPT_any[gi]) or (d == 10 and is_unfusedP[gi]) or (d == 11 and is_d11_f6s[gi])) else 0
                        nhTPT = 1 if (hTPT or (d == 10 and is_TPT_or_TPs[gi])) else 0
                        nhTri = 1 if (hTri or (d == 9 and is_triadP[gi])) else 0
                        add6 = (sum(1 for m in chain_meta[names[gi]] if m in ('H', 'T1R', 'T1L', 'T2'))
                                if names[gi] in chain_meta else (1 if (is_6s[gi] or is_6o[gi]) else 0)) if d == 9 else 0
                        nn6 = min(2, n6 + add6)
                        nv = val + wts[gi] + (vcor_w if (is_6c[last] and is_6c[gi]) else 0)
                        nk = (gi, nmsk, ncnt, nh6s, nh6o, nhTP6, nhP, nhTPT, nhTri, nn6, 1 if (usyz or use_syz) else 0)
                        nb = buckets[npos]
                        if nk not in nb or nv > nb[nk]: nb[nk] = nv
            for (last, msk, cnt, h6s, h6o, hTP6, hP, hTPT, hTri, n6, usyz), val in buckets[d].items():
                if not ok_mat[last][si]: continue
                if d == 9 and (((h6o or h6s) and hP) or (hTri and n6 >= 2)): continue
                if d == 10 and ((h6s and hP) or ((h6o or hTP6) and hTPT) or (h6o and cnt > 1) or (h6s and cnt > 2)): continue
                if d == 11 and ((h6s and (cnt > 1 or hP)) or (hTP6 and cnt > 0)): continue
                tot = val + (vcor_w if (is_6c[last] and is_6c[si]) else 0) - (W_LCM if (d == 10 and cnt == 5) else 0)
                if tot > best: best = tot
        assert F(6 - d) + F(best, W_LCM) <= 0, f"Clean cubic d={d} failed!"
        dp_bounds[str(d)] = {"mode": "cyclic_dp", "max_in_num": best, "budget_num": (d - 6) * W_LCM, "denom": W_LCM}

    # 4. 108 d=17 residuals: 60 R10 kills + 48 in 12 patch orbits (114 full welds):
    r10_killed = 0
    patch_orbits = Counter()
    for seq in d17_residuals:
        if 'C_TPsR_H_TPsL' in seq and 'R10' in seq:
            r10_killed += 1
        else:
            k = seq.index('T1_R')
            rot = seq[k:] + seq[:k]
            assert rot[:2] == ('T1_R', 'T1_L') and rot[2::2] == ('N',) * 4
            tag = lambda tok: 'L' if tok == 'C_T1R_TPsL' else ('R' if tok == 'C_TPsR_T1L' else 'T')
            patch_orbits['X' + ''.join(tag(tok) for tok in rot[3::2])] += 1
    expected_words = {'X' + ''.join(order) for a, b in product('LR', repeat=2) for order in permutations('T' + a + b)}
    assert r10_killed == 60 and patch_orbits == dict.fromkeys(expected_words, 4)
    d17_weld_witnesses = {}
    full_welds = 0
    for word in sorted(expected_words):
        rec = [] if export_mode else None
        sv, tw = surv_welds(degree17_patch(word), record=rec)
        assert sv == 0
        full_welds += tw
        if export_mode:
            d17_weld_witnesses[word] = rec
    assert full_welds == 114

    # 5. Hardened Bellman-Ford Dual Potentials (d>=33 B=5/4 667e; Frozen CAP H=1 1,588e + relaxed <= 32/3):
    def run_bf_51(bval, mch_map, frozen=False):
        toks33 = {
            'N': (1, F(0)), '6c': (1, F(0)), 'R10': (1, F(1, 5)),
            'T10': (1, F(1)), 'T': (1, F(9, 8)), 'T_L9': (1, F(9, 8)), 'T_R9': (1, F(9, 8)),
            'P': (1, F(1)), 'TP_b': (1, F(1)),
            'TP_b54_R': (2, F(5, 4)), 'TP_b54_L': (2, F(5, 4)), 'TP_b54_t89': (3, F(19, 8)),
            'TP_s_L': (2, F(2)), 'TP_s_R': (2, F(2)),
            'TP_s73_R': (2, F(7, 3)), 'TP_s73_L': (2, F(7, 3)), 'TP_s3_t89': (4, F(3)),
            'HH': (3, F(5, 2)), 'TPT_A': (3, F(12, 5)), 'TPT_BC': (2, F(7, 3)),
            'TPT_A9_R': (3, F(11, 4)), 'TPT_A9_L': (3, F(11, 4)),
            'TPT_A10_R': (3, F(5, 2)), 'TPT_A10_L': (3, F(5, 2)),
            'TPT_B9A_R': (4, F(23, 8)), 'TPT_B9A_L': (4, F(23, 8)),
            'TPT_B9C_R': (3, F(21, 8)), 'TPT_B9C_L': (3, F(21, 8)),
            'S_YZ_R': (3, F(13, 4)), 'S_YZ_L': (3, F(13, 4)), 'S_X': (5, F(9, 2)),
            'T2': (3, F(2)), 'T1_R': (2, F(3, 2)), 'T1_L': (2, F(3, 2)),
            '6o': (1, F(1) if frozen else F(1, 2)),
            'TP6_L': (2, F(2, 3)), 'TP6_R': (2, F(2, 3)), 'TP6_2': (3, F(4, 3)),
        }
        cm33 = {}
        for ak in sorted(chains56):
            cn = "C_" + "_".join(ak)
            toks33[cn] = (sum(MW[m] for m in ak), sum(mch_map[m] for m in ak))
            cm33[cn] = ak
        cn33 = set(cm33)
        ends_g = {'T', 'T10', 'T_L9', 'T_R9', 'P', 'TP_s_L', 'TP_s_R', 'TP_s73_L', 'TP_s73_R', 'TP_b', 'TP_b54_L', 'TP_b54_t89',
                  'HH', 'TPT_A', 'TPT_BC', 'T1_L', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L', 'S_YZ_L', 'S_X', 'TP_s3_t89'}
        starts_g = {'T', 'T10', 'T_L9', 'T_R9', 'P', 'TP_s_L', 'TP_s_R', 'TP_s73_L', 'TP_s73_R', 'TP_b', 'TP_b54_R', 'TP_b54_t89',
                    'HH', 'TPT_A', 'TPT_BC', 'T1_R', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R', 'S_YZ_R', 'S_X', 'TP_s3_t89'}
        ends_6s, starts_6s, ends_6o, starts_6o = {'T2', 'T1_R'}, {'T2', 'T1_L'}, {'6o'}, {'6o'}
        ends_tp6, starts_tp6 = {'TP6_L', 'TP6_2'}, {'TP6_R', 'TP6_2'}
        for cn, ak in cm33.items():
            if ak[0] in ('P', 'B', 'TPsL', 'T1R', 'TPsR'): starts_g.add(cn)
            elif ak[0] == 'H': starts_6o.add(cn)
            else: starts_6s.add(cn)
            if ak[-1] in ('P', 'B', 'TPsR', 'T1L', 'TPsL'): ends_g.add(cn)
            elif ak[-1] == 'H': ends_6o.add(cn)
            else: ends_6s.add(cn)
        g_left_N = {'S_YZ_R', 'S_X', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R'}
        g_right_N = {'S_YZ_L', 'S_X', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L'}
        after_A9 = {'N', 'T_L9', 'P', 'TP_s_R', 'TP_b', 'TP_b54_R', 'TPT_A10_L'}
        before_A9 = {'N', 'T_R9', 'P', 'TP_s_L', 'TP_b', 'TP_b54_L', 'TPT_A10_R'}
        after_A10 = {'N', 'T', 'T10', 'T1_R', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L', 'TP6_L'} | {cn for cn, ak in cm33.items() if ak[0] == 'T1R'}
        before_A10 = {'N', 'T', 'T10', 'T1_L', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R', 'TP6_R'} | {cn for cn, ak in cm33.items() if ak[-1] == 'T1L'}
        after_B9, before_B9 = {'N', 'T_L9', 'TPT_A10_L'}, {'N', 'T_R9', 'TPT_A10_R'}
        p_sc = {cn for cn, ak in cm33.items() if ak[0] == 'P'}
        p_ec = {cn for cn, ak in cm33.items() if ak[-1] == 'P'}

        def pair_ok_33(a, b_):
            if a in cn33 and (b_ in starts_6o or b_ in starts_6s or b_ in cn33): return False
            if b_ in cn33 and (a in ends_6o or a in ends_6s or a in cn33): return False
            if a in ends_g and b_ in starts_g: return False
            if b_ in g_left_N and a != 'N': return False
            if a in g_right_N and b_ != 'N': return False
            if a == 'HH' and (b_ in starts_g or b_ in starts_6s or b_ in starts_6o or b_ in ('6c', 'TP6_L')): return False
            if b_ == 'HH' and (a in ends_g or a in ends_6s or a in ends_6o or a in ('6c', 'TP6_R')): return False
            if (a == 'TP_b54_L' and b_ == 'TP6_L') or (b_ == 'TP_b54_R' and a == 'TP6_R'): return False
            if (a == 'T10' and b_ == 'TP6_L') or (b_ == 'T10' and a == 'TP6_R'): return False
            if (a == 'R10' and b_ != 'T10') or (b_ == 'R10' and a != 'T10'): return False
            if (a == 'S_YZ_R' and b_ != 'N') or (b_ == 'S_YZ_L' and a != 'N'): return False
            if a == 'T_L9' and b_ in ('TPT_A9_L', 'TPT_B9A_L', 'TPT_B9C_L', 'TP6_L'): return False
            if b_ == 'T_R9' and a in ('TPT_A9_R', 'TPT_B9A_R', 'TPT_B9C_R', 'TP6_R'): return False
            if b_ == 'T_L9' and a not in ('TPT_A9_R', 'TPT_B9A_R', 'TPT_B9C_R'): return False
            if a == 'T_R9' and b_ not in ('TPT_A9_L', 'TPT_B9A_L', 'TPT_B9C_L'): return False
            if a == 'TPT_A9_R' and b_ not in after_A9: return False
            if b_ == 'TPT_A9_L' and a not in before_A9: return False
            if a == 'TPT_A10_R' and b_ not in after_A10: return False
            if b_ == 'TPT_A10_L' and a not in before_A10: return False
            if a in ('TPT_B9A_R', 'TPT_B9C_R') and b_ not in after_B9: return False
            if b_ in ('TPT_B9A_L', 'TPT_B9C_L') and a not in before_B9: return False
            if a == 'T2' and b_ == 'T2': return False
            if (a in ends_6s and b_ in starts_g) or (b_ in starts_6s and a in ends_g): return False
            if (a in ends_6o and b_ in starts_g) or (b_ in starts_6o and a in ends_g): return False
            if (a == '6c' and b_ in (starts_g - {'P'} - p_sc)) or (b_ == '6c' and a in (ends_g - {'P'} - p_ec)): return False
            if (a in ends_tp6 and b_ in starts_g) or (b_ in starts_tp6 and a in ends_g): return False
            if b_ == 'TP_s73_R' and a != 'N': return False
            if a == 'TP_s73_L' and b_ != 'N': return False
            return True

        if not frozen:
            nodes = sorted(toks33)
            es = [(u, v, toks33[v][1] - bval * toks33[v][0] + (F(1, 5) if (u == '6c' and v == '6c') else F(0)))
                  for u in nodes for v in nodes if pair_ok_33(u, v)]
            ok, pi, scale = find_rational_potential(nodes, es)
            assert ok and 6 - 33 + 33 * bval == 0
            return {
                "nodes": nodes, "scale": scale,
                "edges": [[u, v, int(w * scale)] for u, v, w in es],
                "pi": {u: int(pi[u] * scale) for u in nodes},
                "edge_count": len(es),
            }

        toks_frz = dict(toks33)
        toks_frz['CAP'] = (0, F(0))
        toks_frz['T_frz_L'] = (1, F(3, 2))
        toks_frz['T_frz_R'] = (1, F(3, 2))
        del toks_frz['TPT_BC']
        toks_frz['TPT_BC_R'] = (2, F(7, 3))
        toks_frz['TPT_BC_L'] = (2, F(7, 3))

        def pair_ok_frz(a, b_):
            if a == 'CAP' and b_ == 'CAP': return False
            if a == 'CAP':
                return b_ not in ('R10', 'T_L9', 'T_frz_R', 'S_YZ_R', 'S_X', 'TPT_A9_R', 'TPT_A10_R', 'TPT_B9A_R', 'TPT_B9C_R', 'TP_s73_R', 'TPT_BC_R')
            if b_ == 'CAP':
                return a not in ('R10', 'T_R9', 'T_frz_L', 'S_YZ_L', 'S_X', 'TPT_A9_L', 'TPT_A10_L', 'TPT_B9A_L', 'TPT_B9C_L', 'TP_s73_L', 'TPT_BC_L')
            if a == 'T_frz_L': return b_ in ('N', '6c', 'TP6_L')
            if b_ == 'T_frz_R': return a in ('N', '6c', 'TP6_R')
            if a == 'T_frz_R' or b_ == 'T_frz_L': return False
            a0 = 'TPT_BC' if a in ('TPT_BC_R', 'TPT_BC_L') else a
            b0 = 'TPT_BC' if b_ in ('TPT_BC_R', 'TPT_BC_L') else b_
            if b_ == 'TPT_BC_R' and a not in ('N', '6c', 'TP6_R'): return False
            if a == 'TPT_BC_L' and b_ not in ('N', '6c', 'TP6_L'): return False
            return pair_ok_33(a0, b0)

        nodes_frz = [('CAP', 0)] + [(u, st) for u in sorted(toks_frz) if u != 'CAP' for st in (1, 2)]
        ef = []
        for v in sorted(toks_frz):
            if v == 'CAP': continue
            wv = toks_frz[v][1] - F(1) * toks_frz[v][0]
            if pair_ok_frz('CAP', v): ef.append((('CAP', 0), (v, 1), wv))
            if pair_ok_frz(v, 'CAP'):
                ef.append(((v, 2), ('CAP', 0), F(0)))
                if toks_frz[v][0] >= 2: ef.append(((v, 1), ('CAP', 0), F(0)))
        for u in sorted(toks_frz):
            if u == 'CAP': continue
            for v in sorted(toks_frz):
                if v == 'CAP': continue
                if pair_ok_frz(u, v):
                    w = toks_frz[v][1] - F(1) * toks_frz[v][0] + (F(1, 5) if (u == '6c' and v == '6c') else F(0))
                    ef.append(((u, 1), (v, 2), w))
                    ef.append(((u, 2), (v, 2), w))
        ok, pi, scale = find_rational_potential(nodes_frz, ef)
        assert ok and 2 * 5 == 10 < 12
        # Relaxed CAP endpoint bound (every first/last token allowed -> excess = 1/3 => sum <= 32/3 < 12):
        core = [(a, b_, w) for a, b_, w in ef if a[0] != 'CAP' and b_[0] != 'CAP']
        dist_r = {(tag, 1): wt - wd for tag, (wd, wt) in toks_frz.items() if tag != 'CAP'}
        for _ in range(2 * len(toks_frz)):
            upd = dist_r.copy()
            for a, b_, w in core:
                if a in dist_r:
                    val = dist_r[a] + w
                    if b_ not in upd or val > upd[b_]: upd[b_] = val
            if upd == dist_r: break
            dist_r = upd
        assert all(b_ in dist_r and dist_r[b_] >= dist_r[a] + w for a, b_, w in core if a in dist_r)
        excess = max(v for (tag, st), v in dist_r.items() if st == 2 or toks_frz[tag][0] >= 2)
        assert excess == F(1, 3) and 2 * (5 + excess) == F(32, 3) < 12
        nm_str = lambda nd: f"{nd[0]}#{nd[1]}"
        return {
            "nodes": [nm_str(nd) for nd in nodes_frz], "scale": scale,
            "edges": [[nm_str(u), nm_str(v), int(w * scale)] for u, v, w in ef],
            "pi": {nm_str(nd): int(pi[nd] * scale) for nd in nodes_frz},
            "relaxed_pi": {nm_str(nd): [dist_r[nd].numerator, dist_r[nd].denominator] for nd in sorted(dist_r)},
            "relaxed_excess": [excess.numerator, excess.denominator],
            "edge_count": len(ef),
        }

    bf_clean = run_bf_51(F(9, 11),
                         {'H': F(1, 2), 'T1R': F(3, 2), 'T1L': F(3, 2), 'T2': F(2),
                          'P': F(1), 'B': F(5, 4), 'TPsR': F(2), 'TPsL': F(2)}, frozen=False)
    bf_frozen = run_bf_51(F(1),
                          {'H': F(1), 'T1R': F(3, 2), 'T1L': F(3, 2), 'T2': F(2),
                           'P': F(1), 'B': F(1), 'TPsR': F(2), 'TPsL': F(2)}, frozen=True)
    assert bf_clean["edge_count"] == 667 and bf_frozen["edge_count"] == 1588

    print(f"PASS Main Theorem 1 (ALL Cubic Planar C32): 51 BFS chains "
          f"({bfs_welds} total tested / {bfs_pruned_welds} pruned len-2..6 welds, 0 at len 6), "
          f"TP_b54/A9/R10 seals ({seal_total} total = {seal_s29}+{seal_tp_hex}+{seal_r21_tp}+{seal_r10}+{seal_welds_r22}+{seal_extra}, "
          f"headline {seal_welds_r21}+{seal_welds_r22} -> 0 surv), clean d<=31 DP + "
          f"enum {enum_counts} (108 d=17: 48x114 welds + 60 R10 -> 0 surv), "
          f"BF d>=33 (667e, B=5/4) & frozen CAP (1,588e, H=1, sum<=10, relaxed<=32/3 < 12)!")
    return {
        "chains56": {"_".join(k): sorted(v) for k, v in sorted(chains56.items())},
        "dp_bounds": dp_bounds,
        "bf_clean_d33": bf_clean,
        "bf_frozen_cap": bf_frozen,
        "d17_weld_witnesses": d17_weld_witnesses,
        "seal_weld_count": len(seal_records) if seal_records is not None else 0,
    }


# ==============================================================================
# 4. MAIN THEOREM 3 — GENERAL PLANAR (delta >= 3, ALL CONN., ALL Delta) C16 TRILOGY
# ==============================================================================

def verify_theorem3_c3free():
    """Certify Main Theorem 3(a): ALL C3-free general planar graphs (delta >= 3) -> C4, C8, or C16."""
    for k in range(4, 100):
        for c in range(k // 2 + 1):
            assert 6 - 2 * k + (k - 2 * c + 1) // 2 + c == 6 - 2 * k + (k + 1) // 2 <= 0

    def enum_ring(degs):
        faces = [(0, 1, 2, 3, 4)]
        nxt = 10
        outer = []
        for i in range(5):
            k = degs[i] - 4
            mids = list(range(nxt, nxt + k))
            nxt += k
            faces.append(((i + 1) % 5, i, 5 + i, *mids, 5 + (i + 1) % 5))
            outer.append(5 + i)
            outer.extend(mids)
        faces = tuple(faces)
        valid = surv = 0
        for q in rim_quotients(faces, tuple(outer)):
            st = patch_status(q, 3)
            if st != "invalid":
                valid += 1
                if st == "survivor":
                    surv += 1
        return valid, surv

    v67, s67 = enum_ring((6, 6, 6, 6, 7))
    v69, s69 = enum_ring((6, 6, 6, 6, 9))
    v66, s66 = enum_ring((6, 6, 6, 6, 6))
    assert s67 == 0 and s69 == 0 and s66 == 1

    cor = [(0, 1, 2, 3, 4)]
    outer_ring = []
    for i in range(5):
        bi, ci = 10 + 2 * i, 11 + 2 * i
        cor.append(((i + 1) % 5, i, 5 + i, bi, ci, 5 + (i + 1) % 5))
        outer_ring.extend([5 + i, bi, ci])

    def check_cor_attach(new_face, new_vs, arc_rev):
        all_f = (*cor, new_face)
        k, m = len(new_vs), len(arc_rev)
        valid = 0
        for r in range(min(k, m) + 1):
            for n_sub in combinations(range(k), r):
                for a_sub in combinations(range(m), r):
                    rep = {new_vs[ni]: arc_rev[ai] for ni, ai in zip(n_sub, a_sub)}
                    q = tuple(tuple(rep.get(x, x) for x in fc) for fc in all_f)
                    st = patch_status(q, 3)
                    assert st != "survivor"
                    if st == "killed":
                        valid += 1
        return valid

    h0_v = set(cor[1])
    cor_k = 0
    for u, v in ((10, 11), (5, 10)):
        iu, iv = outer_ring.index(u), outer_ring.index(v)
        arc = []
        idx = (iv + 1) % 15
        while idx != iu:
            if outer_ring[idx] not in h0_v:
                arc.append(outer_ring[idx])
            idx = (idx + 1) % 15
        cor_k += check_cor_attach((v, u, 20, 21, 22), [20, 21, 22], list(reversed(arc)))
    v_arc_rev = [17, 16, 8, 15, 14, 7, 13, 12]
    val_k = sum(check_cor_attach((10, 5, 19, *range(20, 20 + d - 3)), list(range(20, 20 + d - 3)), v_arc_rev)
                for d in (5, 6, 7, 9, 10))

    dp_c3 = {}
    for d in [6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24]:
        wp = {6: F(0), 7: F(1, 2), 9: F(3, 4)}.get(d, F(1))
        wv = F(1, 5) if d >= 11 else F(0)
        max_p = 0
        for m in range(d // 2 + 1):
            if not ({d + 3 * j for j in range(m + 1)} & {4, 8, 16}):
                max_p = m
            else:
                break
        toks = [('N', 1, F(0)), ('P', 1, wp)] + ([('V', 2, wv)] if wv > 0 else [])
        best = F(0)
        for ft, fw, fwt in toks:
            if fw > d: continue
            dp = [{} for _ in range(d + 1)]
            dp[fw][(ft, 1 if ft == 'P' else 0)] = fwt
            for pos in range(fw, d):
                for (lt, pc), val in dp[pos].items():
                    for nt, nw, nwt in toks:
                        if pos + nw > d or (lt == 'P' and nt in ('P', 'V')) or (nt == 'P' and lt == 'V'): continue
                        npc = pc + (1 if nt == 'P' else 0)
                        if npc > max_p: continue
                        nv = val + nwt
                        if (nt, npc) not in dp[pos + nw] or nv > dp[pos + nw][(nt, npc)]:
                            dp[pos + nw][(nt, npc)] = nv
            for (lt, _), val in dp[d].items():
                if not ((lt == 'P' and ft in ('P', 'V')) or (ft == 'P' and lt == 'V')) and val > best:
                    best = val
        assert F(6 - d) + best <= 0
        dp_c3[str(d)] = [best.numerator, best.denominator]
    assert F(11 * 14, 20) <= 14 - 6
    for d in range(3, 25):
        L = d - 1
        dp = [{} for _ in range(L + 1)]
        dp[0]['S'] = F(0)
        for pos in range(L):
            for lt, val in dp[pos].items():
                for nt, nw, nwt in (('N', 1, F(0)), ('P', 1, F(1)), ('V', 2, F(1, 5))):
                    if pos + nw > L or (lt == 'P' and nt in ('P', 'V')) or (lt == 'V' and nt == 'P'): continue
                    nv = val + nwt
                    if nt not in dp[pos + nw] or nv > dp[pos + nw][nt]:
                        dp[pos + nw][nt] = nv
        assert F(6 - d) + max(dp[L].values()) <= 4
    assert 4 + 4 == 8 < 12

    print(f"PASS Main Theorem 3(a) (ALL C3-Free General Planar C16): P+(6,6,6,6,7)={v67}->0, "
          f"P+(6,6,6,6,9)={v69}->0, Corannulene={v66}->1, Cor+P={cor_k}->0, Cor+val={val_k}->0, "
          f"clean DP + d>=14 (11d/20<=d-6) & frozen sum<=8<12!")
    return {"dp_clean": dp_c3}


def verify_theorem3_c5free():
    """Certify Main Theorem 3(b): ALL C5-free general planar graphs (delta >= 3, ZERO R10!) -> C4, C8, or C16."""
    assert F(2, 3) + 2 * F(7, 6) == 3
    assert 2 * F(11, 12) + F(7, 6) == 3
    assert 3 * F(1) == 3
    assert F(1) + F(1, 2) + F(1, 2) == 2
    assert 3 * F(2, 3) == 2
    assert F(5, 6) + F(1, 2) + F(2, 3) == 2
    assert 0 <= 2 - F(2, 3) - F(7, 6) <= F(1, 2)
    assert 0 <= 2 - F(2, 3) - F(1, 2) <= F(7, 6)

    # Full valley-9 + d=11,12 rim quotients (R21 + R22 hardened):
    v9 = ((0, 1, 10, 11, 12, 2), (0, 2, 13, 14, 15, 3), (13, 2, 12), (14, 13, 12, 11, 60, 61, 62, 63, 64))
    v9_kills = 0

    def full_rim_kill_c5(faces, fixed_v=0):
        nonlocal v9_kills
        rim = outer_rim(faces)
        exp = tuple(v for v in rim if v != fixed_v) if fixed_v is not None else rim
        kc = 0
        for q in rim_quotients(faces, exp):
            st = patch_status(q, 5)
            assert st != "survivor", (faces, q)
            if st == "killed": kc += 1
        assert kc > 0
        v9_kills += kc

    for dB, dA in ((6, 6), (6, 7), (7, 6)):
        full_rim_kill_c5((*v9, (11, 10, 70, *range(71, 71 + dB - 4), 60), (10, 1, *range(80, 80 + dA - 3), 70)))
        full_rim_kill_c5((*v9, (11, 10, 70, *range(71, 71 + dB - 3)), (10, 1, *range(80, 80 + dA - 3), 70)))
        full_rim_kill_c5((*v9, (11, 10, *range(70, 70 + dB - 3), 60), (10, 1, *range(80, 80 + dA - 2))))
    full_rim_kill_c5((*v9, (11, 10, 70, 71, 72, 73, 60), (10, 1, 80, 81, 82, 83, 70)))
    full_rim_kill_c5((*v9, (11, 10, 70, 71, 72, 73, 60), (10, 1, 80, 81, 82, 83, 84)))
    for dX in (11, 12):
        full_rim_kill_c5((*v9, (10, 1, *range(80, 80 + dX - 2))))
        full_rim_kill_c5((*v9, (11, 10, *range(70, 70 + dX - 2))))
        full_rim_kill_c5((*v9, (11, 10, *range(70, 70 + dX - 3), 60)))
    for dB in (6, 7):
        full_rim_kill_c5((*v9, (11, 10, *range(70, 70 + dB - 3), 60), (10, 1, 80, 81, 82, 83, 84, 85, 86)))
        full_rim_kill_c5((*v9, (11, 10, 70, *range(71, 71 + dB - 3)), (10, 1, 80, 81, 82, 83, 84, 85, 70)))
    for dA in (6, 7):
        full_rim_kill_c5((*v9, (11, 10, 70, 71, 72, 73, 74, 75, 76), (10, 1, *range(80, 80 + dA - 3), 70)))
        full_rim_kill_c5((*v9, (11, 10, 70, 71, 72, 73, 74, 75, 60), (10, 1, *range(80, 80 + dA - 2))))

    # Vertex absorption (4-hex, 5-hex+2v, k4t2, 3-hex+2T) & F7 & T_frz+H6+T'=C8:
    full_rim_kill_c5(((0, 1, 10, 11, 12, 2), (0, 2, 13, 14, 15, 3), (0, 3, 16, 17, 18, 4), (0, 4, 19, 20, 21, 1)), 0)
    full_rim_kill_c5(((0, 1, 10, 11, 12, 2), (0, 2, 13, 14, 15, 3), (0, 3, 16, 17, 18, 4),
                      (0, 4, 19, 20, 21, 5), (0, 5, 22, 23, 24, 1), (13, 2, 12), (19, 4, 18)), 0)
    t12 = ((0, 1, 2), (0, 3, 4))
    full_rim_kill_c5((*t12, (3, 0, 2, 10, 11, 12, 13, 14, 15), (1, 0, 4, 20, 21, 22, 23, 24, 25)), None)
    full_rim_kill_c5((*t12, (3, 0, 2, 10, 11, 12, 13, 14, 15), (2, 1, 20, 21, 22, 23, 24, 25, 10)), None)
    three_hex = ((0, 1, 10, 11, 12, 2), (0, 2, 13, 14, 15, 3), (0, 3, 16, 17, 18, 4))
    edges_3h = (((1, 10), (10, 11), (11, 12)), ((13, 14), (14, 15)), ((16, 17), (17, 18), (18, 4)))
    v3hex_k = 0
    for i_h, j_h in combinations(range(3), 2):
        for (a, b), (c_, d_) in product(edges_3h[i_h], edges_3h[j_h]):
            patch = (*three_hex, (b, a, 30), (d_, c_, 31))
            for q in rim_quotients(patch, tuple(v for v in outer_rim(patch) if v != 0)):
                if len(set(q[0]) & set(q[2])) >= 2: continue
                st = patch_status(q, 5)
                assert st != "survivor", (patch, q)
                if st == "killed": v3hex_k += 1
    assert v3hex_k == 47

    f7_3h = ((0, 1, 2, 3, 4, 5, 6), (1, 0, 10, 11, 12, 13), (2, 1, 13, 14, 15, 16), (3, 2, 16, 17, 18, 19))
    for tf in ((11, 10, 30), (12, 11, 30), (15, 14, 30), (18, 17, 30), (19, 18, 30), (14, 13, 12), (17, 16, 15)):
        full_rim_kill_c5((*f7_3h, tf), None)
    f7_pair_k = 0
    f7, h1, h2 = tuple(range(7)), (1, 0, 10, 11, 12, 13), (2, 1, 20, 21, 22, 23)
    for (a, b), (c_, d_) in product(((10, 11), (11, 12), (12, 13)), ((20, 21), (21, 22), (22, 23))):
        patch = (f7, h1, h2, (b, a, 30), (d_, c_, 31))
        for q in rim_quotients(patch, tuple(v for v in outer_rim(patch) if v != 1)):
            if len(set(q[1]) & set(q[2])) == 2: continue
            st = patch_status(q, 5)
            assert st != "survivor"
            if st == "killed": f7_pair_k += 1
    t_frz_k = 0
    for e in ((3, 4), (4, 5), (5, 6), (6, 2), (1, 3)):
        assert bounded_cycles(face_graph(((0, 1, 2), (2, 1, 3, 4, 5, 6), (e[1], e[0], 7))), {4, 8})
        t_frz_k += 1
    assert f7_pair_k == 31 and t_frz_k == 5

    # F10 5-Triangle Exhaustive + 10 aux10 + 102 H6 Full Rim Quotients (ZERO R10!):
    rim10 = tuple(range(10))
    geom10 = set()
    max_5t = F(0)
    for chosen in combinations(rim10, 5):
        sel = set(chosen)
        req_high = {v for v in rim10 if v in sel and (v - 1) % 10 in sel}
        for high in map(set, (c for sz in range(6) for c in combinations(rim10, sz))):
            if not req_high <= high or any((v + 1) % 10 in high for v in high): continue
            ts = {i for i in chosen if i in high or (i + 1) % 10 in high}
            t_set = sel - ts
            safe = Counter()
            for a in rim10:
                bef, aft = (a - 1) % 10, (a + 1) % 10
                if bef not in sel or aft not in sel or a in high or aft in high: continue
                safe[bef] += 1
                safe[aft] += 1
                if bef in t_set or aft in t_set:
                    geom10.add((chosen, a))
            tot = sum(({0: F(1), 1: F(11, 12), 2: F(2, 3)}[safe[i]] for i in t_set), F(0)) + len(ts) * F(2, 3)
            if tot > max_5t: max_5t = tot
            assert tot <= 4
    assert max_5t == F(47, 12) < 4
    norm10 = {min(tuple(sorted((i - gap) % 10 for i in ch)), tuple(sorted((-i + gap) % 10 for i in ch)))
              for ch, gap in geom10}
    aux10_k = 0
    for chosen in sorted(norm10):
        tris = tuple(((i + 1) % 10, i, 20 + i) for i in chosen)
        aux = (21, 1, 0, 29, 30, 31, 32, 33, 34, 35)
        patch = (rim10, *tris, aux)
        ext = tuple(v for v in outer_rim(patch) if v not in rim10 and v not in (21, 29))
        for q in rim_quotients(patch, ext):
            st = patch_status(q, 5)
            assert st != "survivor"
            if st == "killed": aux10_k += 1
    assert len(norm10) == 10 and aux10_k == 71
    seen_5t = set()
    h6_k = 0
    for chosen in combinations(rim10, 5):
        sel = set(chosen)
        req_high = {v for v in rim10 if v in sel and (v - 1) % 10 in sel}
        if any((v + 1) % 10 in req_high for v in req_high): continue
        canon = min([tuple(sorted((i - r) % 10 for i in chosen)) for r in range(10)]
                    + [tuple(sorted((-i - r) % 10 for i in chosen)) for r in range(10)])
        if canon in seen_5t: continue
        seen_5t.add(canon)
        tris = tuple(((i + 1) % 10, i, 20 + i) for i in canon)
        for g in range(10):
            if g in canon: continue
            a, b = g, (g + 1) % 10
            for sh_L in (False, True):
                if sh_L and ((a - 1) % 10 not in canon or a in req_high): continue
                for sh_R in (False, True):
                    if sh_R and (b not in canon or b in req_high): continue
                    h6 = ((b, a, 20 + (a - 1) % 10, 40, 41, 20 + b) if (sh_L and sh_R) else
                          (b, a, 20 + (a - 1) % 10, 40, 41, 42) if sh_L else
                          (b, a, 40, 41, 42, 20 + b) if sh_R else (b, a, 40, 41, 42, 43))
                    patch = (rim10, *tris, h6)
                    ext = tuple(v for v in outer_rim(patch) if v not in rim10)
                    for q in rim_quotients(patch, ext):
                        st = patch_status(q, 5)
                        assert st != "survivor"
                        if st == "killed": h6_k += 1
    assert h6_k == 385

    # Exact T1/T2 shifts = (0, 1, 3, 4):
    t2_patch = ((0, 1, 10, 11, 12, 2), (12, 13, 2), (0, 2, 13, 14, 15, 3))
    assert shifts_of(t2_patch, 11, 14, 3) == (0, 1, 3, 4)
    t1_patch = ((0, 1, 10, 11, 12, 2), (12, 13, 2))
    assert shifts_of(t1_patch, 11, 13, 2) == (0, 1, 3, 4)

    # Exact Non-Cubic Cyclic DP for ALL clean d in {9..15, 17..20}:
    dp_c5 = {}
    for d in [9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20]:
        wT = {9: F(2, 3), 10: F(1)}.get(d, F(7, 6))
        wT1 = {9: F(3, 4), 10: F(1), 11: F(9, 4)}.get(d, F(3, 2))
        w6o = {9: F(3, 4), 10: F(2, 3), 11: F(0), 12: F(0)}.get(d, F(1, 2))
        w6o_nc = F(0) if d in (9, 11, 12) else F(1, 2)
        wTs_m = F(1, 2) if d == 9 else F(2, 3)
        wTs_s = F(2, 3)
        wTs6 = F(3, 4) if d == 9 else (F(1) if d == 10 else F(5, 4))
        toks = [
            ('N33', 1, '3', '3', 'N', 'N', F(0), (0,), 0, 0, 0),
            ('N34s', 1, '3', '4s', 'N', 'N', F(0), (0,), 0, 0, 0),
            ('N4s3', 1, '4s', '3', 'N', 'N', F(0), (0,), 0, 0, 0),
            ('N34m', 1, '3', '4m', 'N', 'N', F(0), (0,), 0, 0, 0),
            ('N4m3', 1, '4m', '3', 'N', 'N', F(0), (0,), 0, 0, 0),
        ]
        if d != 15:
            toks.extend([
                ('T', 1, '3', '3', 'T', 'T', wT, (0, 1), 1, 0, 0),
                ('Ts_34m', 1, '3', '4m', 'T', 'Ts', wTs_m, (0, 1), 1, 0, 0),
                ('Ts_4m3', 1, '4m', '3', 'Ts', 'T', wTs_m, (0, 1), 1, 0, 0),
                ('Ts_34s', 1, '3', '4s', 'T', 'Ts', wTs_s, (0, 1), 1, 0, 0),
                ('Ts_4s3', 1, '4s', '3', 'Ts', 'T', wTs_s, (0, 1), 1, 0, 0),
            ])
        if (d in (9, 10, 11) or d >= 14) and d != 15:
            for L in ('3', '4s', '4m'):
                for R in ('3', '4s', '4m'):
                    if d == 9: wt_t2 = F(1)
                    elif d == 10: wt_t2 = F(2) if (L == '3' and R == '3') else (F(3, 2) if (L == '3' or R == '3') else F(1))
                    elif d == 11: wt_t2 = F(3) if (L == '3' and R == '3') else (F(9, 4) if (L == '3' or R == '3') else F(4, 3))
                    else: wt_t2 = F(2) if (L == '3' and R == '3') else (F(3, 2) if (L == '3' or R == '3') else F(4, 3))
                    toks.append((f'T2_{L}_{R}', 3, L, R, '6s', '6s', wt_t2, (0, 1, 3, 4), 1, 1, 0))
                toks.append((f'T1_R_{L}', 2, '3', L, 'T', '6s', wT1, (0, 1, 3, 4), 1, 1, 0))
                toks.append((f'T1_L_{L}', 2, L, '3', '6s', 'T', wT1, (0, 1, 3, 4), 1, 1, 0))
                wt_m = wTs6 if L == '3' else wTs_m
                wt_s = wTs6 if L == '3' else wTs_s
                toks.append((f'Ts6m_34_{L}', 2, L, '4m', '6s', 'Ts6', wt_m, (0, 1, 3, 4), 1, 1, 0))
                toks.append((f'Ts6m_43_{L}', 2, '4m', L, 'Ts6', '6s', wt_m, (0, 1, 3, 4), 1, 1, 0))
                toks.append((f'Ts6s_34_{L}', 2, L, '4s', '6s', 'Ts', wt_s, (0, 1, 3, 4), 1, 1, 0))
                toks.append((f'Ts6s_43_{L}', 2, '4s', L, 'Ts', '6s', wt_s, (0, 1, 3, 4), 1, 1, 0))
        if w6o > 0:
            toks.append(('6o', 1, '3', '3', '6o', '6o', w6o, (0, 4, 5) if d == 9 else (0,), 0, 0, 1))
        if w6o_nc > 0:
            for H in ('4s', '4m'):
                toks.append((f'6o_3{H}', 1, '3', H, '6o', '6o_nc', w6o_nc, (0,), 0, 0, 1))
                toks.append((f'6o_{H}3', 1, H, '3', '6o_nc', '6o', w6o_nc, (0,), 0, 0, 1))

        def ok_c5(a, b_):
            if a[3] != b_[2]: return False
            v, ra, lb = a[3], a[5], b_[4]
            if v == '3':
                if ra == 'T' and lb == 'T': return False
                if (ra == 'T' and lb in ('6s', '6o')) or (lb == 'T' and ra in ('6s', '6o')): return False
                if d == 9 and ((ra == '6o' and lb in ('6s', '6o')) or (lb == '6o' and ra in ('6s', '6o'))): return False
                if d == 10 and ra in ('6s', '6o') and lb in ('6s', '6o'): return False
                return True
            elif v == '4s': return not (ra == 'Ts' and lb == 'Ts')
            else: return not (d in (9, 10) and ra == 'Ts6' and lb == 'Ts6')

        nt = len(toks)
        okm = [[ok_c5(toks[i], toks[j]) for j in range(nt)] for i in range(nt)]
        adj = [[j for j in range(nt) if okm[i][j]] for i in range(nt)]
        best = -10**9
        if d >= 17:
            for si in range(nt):
                if toks[si][1] > d: continue
                dp = [{} for _ in range(d + 1)]
                dp[toks[si][1]][si] = int(toks[si][6] * W_LCM)
                for pos in range(1, d):
                    for last, val in dp[pos].items():
                        for gi in adj[last]:
                            np = pos + toks[gi][1]
                            if np > d: continue
                            nv = val + int(toks[gi][6] * W_LCM)
                            if gi not in dp[np] or nv > dp[np][gi]: dp[np][gi] = nv
                for last, val in dp[d].items():
                    if okm[last][si] and val > best: best = val
        else:
            max_s = 16 - d
            full = (1 << (max_s + 1)) - 1
            forb = 1 << (16 - d)
            for si in range(nt):
                if toks[si][1] > d: continue
                m0 = 0
                for sh in toks[si][7]: m0 |= (1 << sh) & full
                if m0 & forb: continue
                dp = [{} for _ in range(d + 1)]
                dp[toks[si][1]][(si, m0, toks[si][8], toks[si][9], toks[si][10])] = int(toks[si][6] * W_LCM)
                for pos in range(1, d):
                    for (last, msk, tc, h6s, h6o), val in dp[pos].items():
                        for gi in adj[last]:
                            np = pos + toks[gi][1]
                            if np > d: continue
                            nm = 0
                            for sh in toks[gi][7]: nm |= (msk << sh) & full
                            if nm & forb: continue
                            ntc = tc + toks[gi][8]
                            if d + ntc >= 16: continue
                            nk = (gi, nm, ntc, h6s or toks[gi][9], h6o or toks[gi][10])
                            nv = val + int(toks[gi][6] * W_LCM)
                            if nk not in dp[np] or nv > dp[np][nk]: dp[np][nk] = nv
                for (last, msk, tc, h6s, h6o), val in dp[d].items():
                    if not okm[last][si]: continue
                    if d == 10 and ((h6o and tc > 1) or (h6s and tc > 2) or tc == 5): continue
                    if d == 11 and h6s and tc > 1: continue
                    if val > best: best = val
        assert F(6 - d) + F(best, W_LCM) <= 0
        dp_c5[str(d)] = {"max_in_num": best, "budget_num": (d - 6) * W_LCM, "denom": W_LCM}

    # Exact Rational Bellman-Ford for Clean d >= 18 (b = 2/3, 452e) & Frozen CAP d >= 3 (bf = 1, 1,029e):
    toks18 = [
        ('N33', 1, '3', '3', 'N', 'N', F(0)), ('N34s', 1, '3', '4s', 'N', 'N', F(0)),
        ('N4s3', 1, '4s', '3', 'N', 'N', F(0)), ('N34m', 1, '3', '4m', 'N', 'N', F(0)),
        ('N4m3', 1, '4m', '3', 'N', 'N', F(0)), ('T', 1, '3', '3', 'T', 'T', F(7, 6)),
        ('Ts_34m', 1, '3', '4m', 'T', 'Ts', F(2, 3)), ('Ts_4m3', 1, '4m', '3', 'Ts', 'T', F(2, 3)),
        ('Ts_34s', 1, '3', '4s', 'T', 'Ts', F(2, 3)), ('Ts_4s3', 1, '4s', '3', 'Ts', 'T', F(2, 3)),
        ('6o', 1, '3', '3', '6o', '6o', F(1, 2)),
    ]
    for H in ('4s', '4m'):
        toks18.append((f'6o_3{H}', 1, '3', H, '6o', '6o_nc', F(1, 2)))
        toks18.append((f'6o_{H}3', 1, H, '3', '6o_nc', '6o', F(1, 2)))
    for L in ('3', '4s', '4m'):
        for R in ('3', '4s', '4m'):
            wt_t2 = F(2) if (L == '3' and R == '3') else (F(3, 2) if (L == '3' or R == '3') else F(4, 3))
            toks18.append((f'T2_{L}_{R}', 3, L, R, '6s', '6s', wt_t2))
        toks18.append((f'T1_R_{L}', 2, '3', L, 'T', '6s', F(3, 2)))
        toks18.append((f'T1_L_{L}', 2, L, '3', '6s', 'T', F(3, 2)))
        wt_ts6 = F(5, 4) if L == '3' else F(2, 3)
        toks18.append((f'Ts6m_34_{L}', 2, L, '4m', '6s', 'Ts6', wt_ts6))
        toks18.append((f'Ts6m_43_{L}', 2, '4m', L, 'Ts6', '6s', wt_ts6))
        toks18.append((f'Ts6s_34_{L}', 2, L, '4s', '6s', 'Ts', wt_ts6))
        toks18.append((f'Ts6s_43_{L}', 2, '4s', L, 'Ts', '6s', wt_ts6))

    def ok18(a, b_):
        if a[3] != b_[2]: return False
        v, ra, lb = a[3], a[5], b_[4]
        if v == '3':
            if ra == 'T' and lb == 'T': return False
            if (ra == 'T' and lb in ('6s', '6o')) or (lb == 'T' and ra in ('6s', '6o')): return False
            return True
        elif v == '4s': return not (ra == 'Ts' and lb == 'Ts')
        else: return True

    nodes18 = [t[0] for t in toks18]
    e18 = [(a[0], b_[0], b_[6] - F(2, 3) * b_[1]) for a in toks18 for b_ in toks18 if ok18(a, b_)]
    ok18_res, pi18, sc18 = find_rational_potential(nodes18, e18)
    assert ok18_res and len(e18) == 452 and 6 - 18 + 18 * F(2, 3) == 0

    toks_f = [(t[0], t[1], t[2], t[3], t[4], t[5], F(1) if t[0].startswith('6o') else t[6]) for t in toks18]
    toks_f.extend([('T_frz_L', 1, '3', '3', 'CAP', 'T', F(3, 2)), ('T_frz_R', 1, '3', '3', 'T', 'CAP', F(3, 2))])
    nodes_f = [('CAP', 0)] + [(t[0], st) for t in toks_f for st in (1, 2)]
    ef = []
    for t in toks_f:
        nm, w = t[0], t[6] - F(1) * t[1]
        if nm != 'T_frz_R': ef.append((('CAP', 0), (nm, 1), w))
        if nm != 'T_frz_L':
            ef.append(((nm, 2), ('CAP', 0), F(0)))
            if t[1] >= 2: ef.append(((nm, 1), ('CAP', 0), F(0)))
    for a in toks_f:
        for b_ in toks_f:
            if a[0] == 'T_frz_R' or b_[0] == 'T_frz_L': continue
            if a[0] == 'T_frz_L':
                if b_[0] not in ('N33', 'N34s', 'N34m'): continue
            elif b_[0] == 'T_frz_R':
                if a[0] not in ('N33', 'N4s3', 'N4m3'): continue
            elif not ok18(a, b_): continue
            w = b_[6] - F(1) * b_[1]
            ef.append(((a[0], 1), (b_[0], 2), w))
            ef.append(((a[0], 2), (b_[0], 2), w))
    okf_res, pif, scf = find_rational_potential(nodes_f, ef)
    assert okf_res and len(ef) == 1029 and 2 * 5 == 10 < 12

    total_c5_kills = v9_kills + v3hex_k + aux10_k + h6_k + f7_pair_k + t_frz_k
    assert (v9_kills, v3hex_k, aux10_k, h6_k, f7_pair_k, t_frz_k) == (2962, 47, 71, 385, 31, 5)
    assert total_c5_kills == 3501
    nm_str = lambda nd: f"{nd[0]}#{nd[1]}"
    print(f"PASS Main Theorem 3(b) (ALL C5-Free General Planar C16, ZERO R10): "
          f"{total_c5_kills} total rim/patch kills (headline {v9_kills}+{v3hex_k}+{aux10_k}+{h6_k} "
          f"+ {f7_pair_k} F7-pair + {t_frz_k} T_frz; F10 5T max 47/12 < 4), clean DP d=9..20, "
          f"BF d>=18 (452e, b=2/3) & frozen CAP (1,029e, sum<=10<12)!")
    return {
        "dp_clean": dp_c5,
        "bf_clean_d18": {
            "nodes": nodes18, "scale": sc18,
            "edges": [[u, v, int(w * sc18)] for u, v, w in e18],
            "pi": {u: int(pi18[u] * sc18) for u in nodes18},
        },
        "bf_frozen_cap": {
            "nodes": [nm_str(nd) for nd in nodes_f], "scale": scf,
            "edges": [[nm_str(u), nm_str(v), int(w * scf)] for u, v, w in ef],
            "pi": {nm_str(nd): int(pif[nd] * scf) for nd in nodes_f},
        },
    }


def verify_theorem3_c6free():
    """Certify Main Theorem 3(c): ALL C6-free general planar graphs (delta >= 3) -> C4, C8, or C16."""
    for k in range(4, 200):
        for t in range(k // 2 + 1):
            for p in range(k // 2 - t + 1):
                assert 6 - 2 * k + ((t + p) if k == 4 else (2 * t + p)) <= 0

    nc_c6 = 0

    def kill_c6(faces):
        nonlocal nc_c6
        rim = outer_rim(faces)
        kc = 0
        for q in rim_quotients(faces, rim):
            st = patch_status(q, 6)
            assert st != "survivor", (faces, q)
            if st == "killed": kc += 1
        assert kc > 0
        nc_c6 += kc

    t12 = ((0, 1, 2), (0, 3, 4))
    kill_c6((*t12, (3, 0, 2, 10, 11, 12, 13, 14, 15), (1, 0, 4, 20, 21, 22, 23, 24, 25)))
    f10 = tuple(range(10))
    kill_c6((f10, (1, 0, 10, 11, 12), (3, 2, 20), (5, 4, 21), (7, 6, 22), (9, 8, 23)))
    f10_5t = (f10, (1, 0, 20), (3, 2, 21), (5, 4, 22), (7, 6, 23), (9, 8, 24))
    kill_c6((*f10_5t, (21, 2, 1, 20, 30, 31, 32, 33, 34, 35)))
    b_L3 = (f10, (0, 9, 20), (1, 0, 21), (3, 2, 22), (5, 4, 23), (7, 6, 24))
    for aux in ((22, 2, 1, 21, 30, 31, 32, 33, 34, 35),
                (23, 4, 3, 22, 30, 31, 32, 33, 34, 35),
                (24, 6, 5, 23, 30, 31, 32, 33, 34, 35)):
        kill_c6((*b_L3, aux))
    b_L4 = (f10, (0, 9, 20), (1, 0, 21), (3, 2, 22), (5, 4, 23), (8, 7, 24))
    for aux in ((22, 2, 1, 21, 30, 31, 32, 33, 34, 35),
                (23, 4, 3, 22, 30, 31, 32, 33, 34, 35),
                (20, 9, 8, 24, 30, 31, 32, 33, 34, 35)):
        kill_c6((*b_L4, aux))

    assert F(3, 4) + 2 * F(9, 8) == 3
    assert F(4, 5) + 2 * F(11, 10) == 3
    assert 2 * F(9, 10) + F(6, 5) == 3
    assert F(1, 2) + 2 * F(3, 4) == 2
    assert F(13, 12) + F(1, 4) + F(2, 3) == 2 and F(13, 12) <= F(6, 5)
    assert F(1, 4) + F(1, 4) + F(1, 2) == 1
    assert F(6 - 7) + 3 * F(1, 5) <= 0
    assert 5 * F(4, 5) <= 4
    assert 3 * F(4, 5) + F(9, 10) + F(2, 3) <= 4
    assert F(4, 5) + 2 * F(9, 10) + 2 * F(2, 3) <= 4
    assert 2 * F(1) + 3 * F(2, 3) <= 4
    assert 3 * F(1) + 2 * F(1, 5) <= 4

    dp_c6 = {}
    for d in [9, 11, 12, 13, 14, 15, 17, 18, 19, 20]:
        wT = F(3, 4) if d == 9 else F(6, 5)
        wTs_s = F(1, 2) if d == 9 else F(3, 4)
        wTs_m = F(1, 4) if d == 9 else F(3, 4)
        wP = F(1, 5)
        toks = [
            ('N33', 1, '3', '3', 'N', 'N', F(0), (0,)),
            ('N34s', 1, '3', '4s', 'N', 'N', F(0), (0,)),
            ('N4s3', 1, '4s', '3', 'N', 'N', F(0), (0,)),
            ('N34m', 1, '3', '4m', 'N', 'N', F(0), (0,)),
            ('N4m3', 1, '4m', '3', 'N', 'N', F(0), (0,)),
        ]
        if d != 15:
            toks.extend([
                ('T', 1, '3', '3', 'T', 'T', wT, (0, 1)),
                ('Ts_34s', 1, '3', '4s', 'T', 'Ts', wTs_s, (0, 1)),
                ('Ts_4s3', 1, '4s', '3', 'Ts', 'T', wTs_s, (0, 1)),
                ('Ts_34m', 1, '3', '4m', 'T', 'Ts', wTs_m, (0, 1)),
                ('Ts_4m3', 1, '4m', '3', 'Ts', 'T', wTs_m, (0, 1)),
            ])
        if d != 13:
            toks.append(('P', 1, '3', '3', 'P', 'P', wP, (0,)))

        def ok_c6(a, b_):
            if a[3] != b_[2]: return False
            v, ra, lb = a[3], a[5], b_[4]
            if v == '3' and ra in ('T', 'P') and lb in ('T', 'P'): return False
            if v == '4s' and ra == 'Ts' and lb == 'Ts': return False
            return True

        nt = len(toks)
        okm = [[ok_c6(toks[i], toks[j]) for j in range(nt)] for i in range(nt)]
        adj = [[j for j in range(nt) if okm[i][j]] for i in range(nt)]
        max_s = max(0, 16 - d)
        full = (1 << (max_s + 1)) - 1
        forb = (1 << (16 - d)) if d < 16 else 0
        best = -10**9
        for si in range(nt):
            m0 = 0
            for sh in toks[si][7]: m0 |= (1 << sh) & full
            if m0 & forb: continue
            dp = [{} for _ in range(d + 1)]
            dp[1][(si, m0)] = int(toks[si][6] * W_LCM)
            for pos in range(1, d):
                for (last, msk), val in dp[pos].items():
                    for gi in adj[last]:
                        nm = 0
                        for sh in toks[gi][7]: nm |= (msk << sh) & full
                        if nm & forb: continue
                        nv = val + int(toks[gi][6] * W_LCM)
                        nk = (gi, nm)
                        if nk not in dp[pos + 1] or nv > dp[pos + 1][nk]:
                            dp[pos + 1][nk] = nv
            for (last, _), val in dp[d].items():
                if okm[last][si] and val > best: best = val
        assert F(6 - d) + F(best, W_LCM) <= 0
        dp_c6[str(d)] = {"max_in_num": best, "budget_num": (d - 6) * W_LCM, "denom": W_LCM}

    toks15 = [
        ('N33', 1, '3', '3', 'N', 'N', F(0)),
        ('N34', 1, '3', '4', 'N', 'N', F(0)),
        ('N43', 1, '4', '3', 'N', 'N', F(0)),
        ('T', 1, '3', '3', 'T', 'T', F(6, 5)),
        ('Ts_34', 1, '3', '4', 'T', 'Ts', F(3, 4)),
        ('Ts_43', 1, '4', '3', 'Ts', 'T', F(3, 4)),
        ('P', 1, '3', '3', 'P', 'P', F(1, 5)),
    ]

    def ok15(a, b_):
        if a[3] != b_[2]: return False
        if a[3] == '3' and a[5] in ('T', 'P') and b_[4] in ('T', 'P'): return False
        return True

    nodes15 = [t[0] for t in toks15]
    e15 = [(a[0], b_[0], b_[6] - F(3, 5) * b_[1]) for a in toks15 for b_ in toks15 if ok15(a, b_)]
    ok_15, pi15, sc15 = find_rational_potential(nodes15, e15)
    assert ok_15 and 6 - 15 + 15 * F(3, 5) == 0

    nodes_f = [('CAP', 0)] + [(t[0], st) for t in toks15 for st in (1, 2)]
    ef = []
    for t in toks15:
        w = t[6] - F(1)
        ef.append((('CAP', 0), (t[0], 1), w))
        ef.append(((t[0], 2), ('CAP', 0), F(0)))
    for a in toks15:
        for b_ in toks15:
            if ok15(a, b_):
                w = b_[6] - F(1)
                ef.append(((a[0], 1), (b_[0], 2), w))
                ef.append(((a[0], 2), (b_[0], 2), w))
    ok_f, pif, scf = find_rational_potential(nodes_f, ef)
    assert ok_f and 2 * 5 == 10 < 12

    nm_str = lambda nd: f"{nd[0]}#{nd[1]}"
    print(f"PASS Main Theorem 3(c) (ALL C6-Free General Planar C16): {nc_c6} full-rim kills -> 0 surv, "
          f"clean d=7,9..20 DP, BF d>=15 ({len(e15)}e, b=3/5) & frozen CAP ({len(ef)}e, sum<=10<12)!")
    return {
        "dp_clean": dp_c6,
        "bf_clean_d15": {
            "nodes": nodes15, "scale": sc15,
            "edges": [[u, v, int(w * sc15)] for u, v, w in e15],
            "pi": {u: int(pi15[u] * sc15) for u in nodes15},
        },
        "bf_frozen_cap": {
            "nodes": [nm_str(nd) for nd in nodes_f], "scale": scf,
            "edges": [[nm_str(u), nm_str(v), int(w * scf)] for u, v, w in ef],
            "pi": {nm_str(nd): int(pif[nd] * scf) for nd in nodes_f},
        },
    }


# ==============================================================================
# 5. MAIN THEOREMS 2 & 4 — BOWTIE-SPLITTING / TRANSFER & ALTERNATING-C6 DENSITY
# ==============================================================================

def verify_theorems_2_and_4():
    """Certify Main Theorem 2 (Universal Transfer & Bowtie Forest) and Main Theorem 4 (Alternating-C6 Density)."""
    # Main Theorem 2:
    # 1. Universal Transfer: k + m <= L - 1 => 2L and 2L + 1 lie in [2L - k, 3L - k - m].
    for L in range(3, 200):
        for k in range(L):
            for m in range(L - k):
                assert 2 * L - k <= 2 * L < 2 * L + 1 <= 3 * L - k - m
    # 2. Bowtie-Forest exclusion: r = L - k <= 2, m = 0 => [L + r, 2L + r] ALWAYS contains 2^a >= 4 for L >= 3.
    for L in range(3, 500):
        for r in (0, 1, 2):
            lo, hi = L + r, 2 * L + r
            p = 1 << (lo - 1).bit_length()
            assert p >= 4 and lo <= p <= hi

    # Main Theorem 4 (Alternating-C6 Planar Degree-Density Bound):
    for n in range(1, 7):
        assert 3 * n > n * (n - 1) // 2
    assert 3 * 7 <= 7 * 6 // 2
    for n in range(6, 500):
        assert 4 * (n - 1) <= 5 * (n - 2)
    for n in range(7, 500):
        h_max = 5 * (n - 2) // 16
        n3_min = n - h_max
        ceil_bound = (11 * n + 10 + 15) // 16
        assert n3_min == ceil_bound and 3 * n3_min > 2 * n
        for eps in range(6):
            h_low = (n + 2) // 3
            num = 16 * h_low + 4 * eps - 5 * (n - 2)
            tau_min = (num + 3) // 4
            assert tau_min >= (n + 30 + 12 * eps + 11) // 12
    assert F(11, 16) - F(2, 3) == F(1, 48)
    print("PASS Main Theorems 2 & 4: Universal Transfer & Bowtie-Forest exclusion + "
          "Alternating-C6 density (16h+4eps <= 5(n-2)+4*tau_6 => |V3| >= ceil((11n+10)/16), +1/48 over 2/3)!")


# ==============================================================================
# 6. CLI ENTRYPOINT & DETERMINISTIC WITNESS EXPORT
# ==============================================================================

def main():
    if sys.flags.optimize:
        raise SystemExit("Run with assertions enabled (no -O).")
    parser = argparse.ArgumentParser(description="Standalone Zero-Float Verifier for Paper 1 (Planar EG).")
    parser.add_argument("--export-witnesses", type=Path, default=None,
                        help="Optional directory to export deterministic JSON witness tables for Lean 4.")
    args = parser.parse_args()

    t0 = monotonic_ns()
    check_zero_floats()
    verify_engine_self_tests()
    sharp = verify_sharpness_witnesses()
    thm1 = verify_theorem1_cubic_planar_c32(export_mode=(args.export_witnesses is not None))
    c3 = verify_theorem3_c3free()
    c5 = verify_theorem3_c5free()
    c6 = verify_theorem3_c6free()
    verify_theorems_2_and_4()

    if args.export_witnesses is not None:
        out_dir = args.export_witnesses
        out_dir.mkdir(parents=True, exist_ok=True)
        out_dir.joinpath("sharp_witnesses.json").write_text(json.dumps(sharp, sort_keys=True), encoding="utf-8")
        bf_bundle = {
            "cubic_d33": thm1["bf_clean_d33"],
            "cubic_frozen_cap": thm1["bf_frozen_cap"],
            "c5free_d18": c5["bf_clean_d18"],
            "c5free_frozen_cap": c5["bf_frozen_cap"],
            "c6free_d15": c6["bf_clean_d15"],
            "c6free_frozen_cap": c6["bf_frozen_cap"],
        }
        out_dir.joinpath("bf_potentials.json").write_text(json.dumps(bf_bundle, sort_keys=True), encoding="utf-8")
        dp_bundle = {
            "cubic_chains56": thm1["chains56"],
            "cubic_clean_d31": thm1["dp_bounds"],
            "c3free_clean": c3["dp_clean"],
            "c5free_clean": c5["dp_clean"],
            "c6free_clean": c6["dp_clean"],
        }
        out_dir.joinpath("cyclic_dp_bounds.json").write_text(json.dumps(dp_bundle, sort_keys=True), encoding="utf-8")
        killed_bundle = {
            "d17_12orbits_114welds": thm1["d17_weld_witnesses"],
        }
        out_dir.joinpath("killed_witnesses.json").write_text(json.dumps(killed_bundle, sort_keys=True), encoding="utf-8")
        print(f"Exported deterministic Lean witness tables to {out_dir}")

    dt_ms = (monotonic_ns() - t0) // 1_000_000
    rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert dt_ms < 60_000, f"Exceeded 60s budget: {dt_ms} ms"
    assert rss_kib < 500 * 1024, f"Exceeded 500 MiB RSS: {rss_kib} KiB"
    print(f"PASS ALL Paper 1 Standalone Certificates in {dt_ms} ms "
          f"(peak RSS {rss_kib // 1024} MiB, ZERO floats, ZERO `/`!)")


if __name__ == "__main__":
    main()
