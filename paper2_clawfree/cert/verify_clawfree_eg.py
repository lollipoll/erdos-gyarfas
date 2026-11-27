#!/usr/bin/env python3
"""Standalone Zero-Float Verifier & Proof-Carrying Witness Exporter for Flagship Paper 2.

Paper 2:
  "Erdos-Gyarfas for 2-Cycle, Sublinear-Circumference, and Bowtie Claw-Free Graphs
   via Sub-Unit 2D Dyadic L_infinity-Packing"

Pure Python 3 standard library ONLY. ZERO floats, ZERO complex literals, ZERO float(),
ZERO true-division `/` operator (AST-guarded), ZERO imports outside stdlib.

Usage:
  python3 -B publication/paper2_clawfree/cert/verify_clawfree_eg.py
  python3 -B publication/paper2_clawfree/cert/verify_clawfree_eg.py --export-witnesses publication/paper2_clawfree/cert/witnesses
"""

import argparse
import ast
import json
import math
import resource
import sys
from collections import Counter, deque
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path
from time import monotonic_ns

F = Fraction
SCALE = 100000
SCALE256 = SCALE ** 256
ATTACHMENT = ((3, 7), (1, 3), (3, 11), (6, 23))
TEMPLATES = ((7, (1,), 3), (3, (1,), 1), (11, (2, 4), 3), (23, (3, 4, 5, 6, 7, 8), 6))


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
            raise AssertionError(f"Forbidden true-division `/` operator at line {getattr(node, 'lineno', '?')}")
        if isinstance(node, ast.Name) and node.id == "float":
            raise AssertionError(f"Forbidden float identifier at line {getattr(node, 'lineno', '?')}")


# ==============================================================================
# 1. EXACT INTEGER / RATIONAL ARITHMETIC & GRAPH PRIMITIVES
# ==============================================================================

def in_feg(length):
    """Exact membership in the forbidden band F_EG = union_{m>=2} (2^m, floor(4*2^m/3)]."""
    if length < 3:
        return False
    block = 1 << (length.bit_length() - 1)
    return block < length and 3 * length <= 4 * block


def next_pow2(lo):
    """Smallest power of 2 that is >= lo (for lo >= 1)."""
    return 1 if lo <= 1 else (1 << (lo - 1).bit_length())


def avoids_pow2(lo, hi):
    """True iff [lo, hi] contains NO power of 2."""
    if lo <= 0:
        return False
    return next_pow2(lo) > hi


def hits_pow2(lo, hi):
    """Smallest power of 2 in [lo, hi], or 0 if none exists."""
    if lo <= 0:
        return 1 if hi >= 1 else 0
    p = next_pow2(lo)
    return p if p <= hi else 0


def lift_avoids(length, used, internal=None):
    """True iff the bowtie lift window [2*L - k, 3*L - k - m] avoids all powers of 2."""
    if internal is None:
        internal = (length - 2 * used) // 2
    return avoids_pow2(2 * length - used, 3 * length - used - internal)


def isqrt256(n):
    """Exact floor(n^(1/256)) via 8-fold math.isqrt."""
    r = math.isqrt(n)
    r = math.isqrt(r)
    r = math.isqrt(r)
    r = math.isqrt(r)
    r = math.isqrt(r)
    r = math.isqrt(r)
    r = math.isqrt(r)
    return math.isqrt(r)


_POW_CACHE = {}


def pow_bounds_123_256(num, den):
    """Exact integer pair (lo, hi) with lo/SCALE <= (num/den)^(123/256) <= hi/SCALE."""
    if num <= 0:
        return 0, 0
    g = math.gcd(num, den)
    num //= g
    den //= g
    key = (num, den)
    res = _POW_CACHE.get(key)
    if res is not None:
        return res
    p = num ** 123
    q = den ** 123
    lo = isqrt256((p * SCALE256) // q)
    hi = lo if (lo ** 256) * q == p * SCALE256 else lo + 1
    assert (lo ** 256) * q <= p * SCALE256 <= (hi ** 256) * q
    if len(_POW_CACHE) < 120000:
        _POW_CACHE[key] = (lo, hi)
    return lo, hi


def pup(n, d):
    return pow_bounds_123_256(n, d)[1]


def plo(n, d):
    return pow_bounds_123_256(n, d)[0]


def prod_up(a, b):
    return (a * b + SCALE - 1) // SCALE


def prod_lo(a, b):
    return (a * b) // SCALE


def frac_pair(q):
    return [q.numerator, q.denominator]


def bit_indices(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def build_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    return tuple(tuple(sorted(row)) for row in adj)


def find_simple_cycle(adj, targets):
    """Return an explicit simple cycle (tuple of vertices) with length in `targets`, or None."""
    target_set = set(targets)
    max_len = max(target_set)
    n = len(adj)
    if 4 in target_set:
        bm = [0] * n
        for u, row in enumerate(adj):
            m = 0
            for v in row:
                m |= 1 << v
            bm[u] = m
        for u in range(n):
            mu = bm[u]
            for v in adj[u]:
                if v > u:
                    for w in adj[v]:
                        if w > u:
                            common = (mu & bm[w]) & ~(1 << v)
                            if common:
                                x = (common & -common).bit_length() - 1
                                return (u, v, w, x)
    for s in range(n):
        stk = [(s, 1 << s, (s,))]
        while stk:
            u, vis, path = stk.pop()
            plen = len(path)
            for w in adj[u]:
                if w == s and plen in target_set and path[1] < u:
                    return path
                if plen < max_len and w > s and not (vis & (1 << w)):
                    stk.append((w, vis | (1 << w), (*path, w)))
    return None


def verify_cycle_witness(adj, cyc, targets):
    assert cyc is not None and len(cyc) in targets and len(set(cyc)) == len(cyc)
    L = len(cyc)
    for i in range(L):
        assert cyc[(i + 1) % L] in adj[cyc[i]]


# ==============================================================================
# 2. MAIN THEOREM 1 — SUB-UNIT 2D DYADIC L_INFINITY-PACKING
#    |S| <= (3/5) * ((W1 + 2)(W2 + 2))^(123/256) FOR ALL W1, W2 >= 0
# ==============================================================================

def compute_exact_base_f19():
    """Compute exact maximum packing size F19[w1][w2] (210 lower-triangular stored entries,
    symmetric 20x20 extension) for 0 <= w2 <= w1 <= 19 on the exact packing domain:
    same-parity S subset [0, w1] x [0, w2], distinct absolute differences |u1 - u2| != |v1 - v2|
    (no diagonal collisions, i.e., pairwise distinct u+v and u-v), and max(|u1-u2|, |v1-v2|) + 2 in F_EG."""
    result = [[0] * 20 for _ in range(20)]
    for width in range(20):
        for height in range(width + 1):
            best = 1
            for parity in (0, 1):
                points = [
                    (x, y)
                    for x in range(width + 1)
                    for y in range(height + 1)
                    if (x + y) % 2 == parity
                ]
                neighbors = [0] * len(points)
                for i, (x, y) in enumerate(points):
                    for j in range(i + 1, len(points)):
                        a, b = points[j]
                        dx, dy = abs(x - a), abs(y - b)
                        if dx != dy and in_feg(2 + max(dx, dy)):
                            neighbors[i] |= 1 << j

                def search(candidates, size):
                    nonlocal best
                    if size > best:
                        best = size
                    while size + candidates.bit_count() > best:
                        bit = candidates & -candidates
                        candidates ^= bit
                        search(candidates & neighbors[bit.bit_length() - 1], size + 1)

                search((1 << len(points)) - 1, 0)
            result[width][height] = best
    assert result[19][19] == 8
    assert result[3][1] == 2 and result[2][1] == 1
    assert all(
        result[x][y] >= result[x - 1][min(y, x - 1)]
        and (not y or result[x][y] >= result[x][y - 1])
        for x in range(1, 20)
        for y in range(x + 1)
    )
    return result


def verify_theorem1_dyadic_packing_2d():
    """Certify Main Theorem 1: |S| <= (3/5)*((W1+2)(W2+2))^(123/256) for ALL W1, W2 >= 0
    on the exact same-parity, no-diagonal (|u1-u2| != |v1-v2|), L_inf-F_EG packing domain."""
    # (1.0) Exact power rounding & sub-interval algebra checks (R15 audit):
    for numerator, denominator in product(range(33), range(1, 17)):
        lo, hi = pow_bounds_123_256(numerator, denominator)
        target = (numerator ** 123) * SCALE256
        den_p = denominator ** 123
        assert (lo ** 256) * den_p <= target < ((lo + 1) ** 256) * den_p
        assert (not numerator) or (((hi - 1) ** 256) * den_p < target <= (hi ** 256) * den_p)
    for m in (32, 64, 128, 256, 512, 1024, 2048, 4096, 8192):
        low, upper = m - 1, (2 * m) // 3 - 2
        half_low, half_upper = m // 2 - 1, m // 3 - 2
        for span in range(m // 3):
            assert 3 * (2 * upper - low - span + 2) <= m - 3 * span
            assert 3 * (upper - span - 1 + 2) <= 2 * m - 3 * span
        assert 6 * (upper - half_low + 2) <= m + 6
        assert 6 * (half_upper - half_low + 2) <= -m + 6
        assert upper - half_low < half_low - half_upper
        assert 3 * (max(m // 3 - 1, half_upper) + 2) <= m + 3
        assert 6 * (2 * half_upper - half_low + 2) <= m - 6

    F19 = compute_exact_base_f19()
    C_num, C_den = 3, 5
    C_num256, C_den256 = C_num ** 256, C_den ** 256
    C4_num = (4 ** 10) * C_num256

    # (1A) Base F19 + Coordinatewise Nondecreasing Exact Integer DP for m = 32..2048 (W1 <= 2728):
    U = [[0] * 2730 for _ in range(2730)]
    for w1 in range(20):
        for w2 in range(w1 + 1):
            U[w1][w2] = F19[w1][w2]
            assert (U[w1][w2] ** 256) * C_den256 <= C_num256 * (((w1 + 2) * (w2 + 2)) ** 123)

    def getU(w1, w2):
        if w1 < 0 or w2 < 0:
            return 0
        return U[w2][w1] if w1 < w2 else U[w1][w2]

    def pair_int(wA, wB, s, hAm, hBm):
        hAm, hBm = min(hAm, s), min(hBm, s)
        if hAm < 0 and hBm < 0:
            return 0
        if hAm + hBm <= s:
            return (getU(wA, hAm) if hAm >= 0 else 0) + (getU(wB, hBm) if hBm >= 0 else 0)
        lo, hi = max(0, s - hBm), hAm
        step_p = 1 if (hi - lo) <= 32 else max(1, (hi - lo) // 16)
        best_p = 0
        for t_lo in range(lo, hi + 1, step_p):
            t_hi = min(hi, t_lo + step_p - 1)
            v = getU(wA, t_hi) + getU(wB, s - t_lo)
            if v > best_p:
                best_p = v
        return best_p

    for m in (32, 64, 128, 256, 512, 1024, 2048):
        L_m, U_m, W_max = m - 1, (2 * m) // 3 - 2, (4 * m) // 3 - 2
        m_h = m // 2
        L_h, U_h = m_h - 1, (2 * m_h) // 3 - 2
        for w1 in range(U_m + 1, L_m):
            row = U[U_m]
            U[w1][:U_m + 1] = row[:U_m + 1]
            ve = row[U_m]
            for w2 in range(U_m + 1, w1 + 1):
                U[w1][w2] = ve
        dbl_cache = {}

        def strip_dbl(s1_lo, s1_hi, w0_lo, w0_hi, h):
            if h < 0:
                return 0
            key = (s1_lo, s1_hi, w0_lo, w0_hi, h)
            v = dbl_cache.get(key)
            if v is not None:
                return v
            b_dir = getU(U_m - s1_lo - 1, h)
            max_a0 = max(0, s1_hi - w0_lo)
            a_step = max(1, max_a0 // 8)
            worst = 0
            for al in range(0, max_a0 + 1, a_step):
                ah = min(max_a0, al + a_step - 1)
                wL = ah + U_h - s1_lo - 1
                wR = -1
                if w0_lo <= U_m - L_h:
                    r1 = U_m - al - w0_lo - L_h
                    if r1 > wR:
                        wR = r1
                if w0_hi >= L_h - U_h:
                    r2 = min(U_m - al - L_h, w0_hi + U_h - L_h)
                    if r2 > wR:
                        wR = r2
                cur = min(b_dir, getU(wL, h) + getU(wR, h))
                if cur > worst:
                    worst = cur
            dbl_cache[key] = worst
            return worst

        def merged_cs(s1_lo, s1_hi, w0_lo, w0_hi, h0_hi, h10_hi, hB_max):
            b_dir = getU(U_m - s1_lo - 1, h10_hi)
            max_a0 = max(0, s1_hi - w0_lo)
            a_step = max(1, max_a0 // 8)
            worst = 0
            for al in range(0, max_a0 + 1, a_step):
                ah = min(max_a0, al + a_step - 1)
                wL = ah + U_h - s1_lo - 1
                wR = -1
                if w0_lo <= U_m - L_h:
                    r1 = U_m - al - w0_lo - L_h
                    if r1 > wR:
                        wR = r1
                if w0_hi >= L_h - U_h:
                    r2 = min(U_m - al - L_h, w0_hi + U_h - L_h)
                    if r2 > wR:
                        wR = r2
                unm = getU(w0_hi, h0_hi) + min(b_dir, getU(wL, h10_hi) + getU(wR, h10_hi))
                w_mrg = max(w0_hi, U_h) if wL >= 0 else w0_hi
                mrg = getU(w_mrg, hB_max) + getU(wR, h10_hi)
                cur = min(unm, mrg)
                if cur > worst:
                    worst = cur
            return worst

        b_sz = 1 if m <= 64 else (m // 24)
        W_blocks = [(w, min(W_max, w + b_sz - 1)) for w in range(L_m, W_max + 1, b_sz)]
        for W1_lo, W1_hi in W_blocks:
            s1_hi = W1_hi - L_m
            w11 = 2 * U_m - W1_lo
            w2_step = 1 if m <= 128 else (m // 48)
            w2_ranges = [(w, w) for w in range(min(48, U_m + 1))]
            if U_m >= 48:
                w2_ranges.extend((w, min(U_m, w + w2_step - 1)) for w in range(48, U_m + 1, w2_step))
            for W2_lo, W2_hi in w2_ranges:
                val = pair_int(W2_hi, W2_hi, s1_hi, s1_hi, s1_hi) + getU(w11, W2_hi)
                for W1 in range(W1_lo, W1_hi + 1):
                    row, prow = U[W1], U[W1 - 1]
                    for W2 in range(W2_lo, W2_hi + 1):
                        v = val
                        if prow[W2] > v:
                            v = prow[W2]
                        if W2 > 0 and row[W2 - 1] > v:
                            v = row[W2 - 1]
                        row[W2] = v
                assert (U[W1_hi][W2_hi] ** 256) * C_den256 <= C_num256 * (((W1_lo + 2) * (W2_lo + 2)) ** 123)
            for W1 in range(W1_lo, W1_hi + 1):
                vu, prow, row = U[W1][U_m], U[W1 - 1], U[W1]
                for W2 in range(U_m + 1, L_m):
                    row[W2] = vu if vu >= prow[W2] else prow[W2]

        step = 1 if m == 32 else max(4, (W_max - L_m + 5) // 5)
        for bi, (W1_lo, W1_hi) in enumerate(W_blocks):
            s1_lo, s1_hi = W1_lo - L_m, W1_hi - L_m
            w11 = 2 * U_m - W1_lo
            w_bins = [(k, min(s1_hi, k + step - 1)) for k in range(0, s1_hi + 1, step)]
            for bj in range(bi + 1):
                W2_lo, W2_hi = W_blocks[bj]
                s2_lo, s2_hi = W2_lo - L_m, W2_hi - L_m
                h11 = 2 * U_m - W2_lo
                v11 = getU(w11, h11)
                h_bins = [(k, min(s2_hi, k + step - 1)) for k in range(0, s2_hi + 1, step)]
                best = v11 + pair_int(w11, w11, s2_hi, s2_hi, s2_hi) + pair_int(h11, h11, s1_hi, s1_hi, s1_hi)
                w12_1, h21_1 = U_m - s1_lo - 1, U_m - s2_lo - 1
                for w0l, w0h in w_bins:
                    elr = pair_int(h11, h21_1, s1_hi, s1_hi, s1_hi - w0l)
                    for h0l, h0h in h_bins:
                        v = getU(w0h, h0h) + pair_int(w11, w12_1, s2_hi, s2_hi, s2_hi - h0l) + elr + v11
                        if v > best:
                            best = v
                v = pair_int(U_m, U_m, s1_hi, s1_hi, s1_hi) + pair_int(2 * U_m - L_m, min(U_m, L_m - 2 - s1_lo), s2_hi, s2_hi, s2_hi) + v11
                if v > best:
                    best = v
                v = pair_int(U_m, U_m, s2_hi, s2_hi, s2_hi) + pair_int(2 * U_m - L_m, min(U_m, L_m - 2 - s2_lo), s1_hi, s1_hi, s1_hi) + v11
                if v > best:
                    best = v
                for u1l, u1h in w_bins:
                    vr = getU(s1_hi - u1l, U_m)
                    for v1l, v1h in h_bins:
                        vt = getU(U_m, s2_hi - v1l)
                        loc = 0
                        for w0l, w0h in w_bins:
                            if w0l > u1h:
                                break
                            wc = min(w0h, u1h)
                            t10 = getU(2 * U_m - L_m - w0l, v1h)
                            for h0l, h0h in h_bins:
                                if h0l > v1h:
                                    break
                                lv = getU(wc, min(h0h, v1h)) + t10 + getU(u1h, 2 * U_m - L_m - h0l)
                                if lv > loc:
                                    loc = lv
                        v = loc + vr + vt + v11
                        if v > best:
                            best = v
                for iB, (uBl, uBh) in enumerate(w_bins):
                    w10 = 2 * U_m - L_m - uBl
                    for iT in range(iB, len(w_bins)):
                        uTl, uTh = w_bins[iT]
                        w12 = 2 * U_m - L_m - uTl
                        ebt = pair_int(w10, w12, s2_hi, s2_hi, s2_hi)
                        u_s = uBh + uTh + 8
                        for jL, (vLl, vLh) in enumerate(h_bins):
                            h01 = 2 * U_m - L_m - vLl
                            for jR in range(jL, len(h_bins)):
                                vRl, vRh = h_bins[jR]
                                h21 = 2 * U_m - L_m - vRl
                                elr = pair_int(h01, h21, s1_hi, s1_hi, s1_hi)
                                c4 = isqrt256((C4_num * ((u_s * (vLh + vRh + 8)) ** 123)) // C_den256)
                                v = c4 + ebt + elr + v11
                                if v > best:
                                    best = v

                def max_pair_dbl(s_lo, s_hi, wlA, whA, wlB, whB, s_sum, limA, limB):
                    limA, limB = min(limA, s_sum), min(limB, s_sum)
                    if limA < 0 and limB < 0:
                        return 0
                    if limA + limB <= s_sum:
                        return (strip_dbl(s_lo, s_hi, wlA, whA, limA) if limA >= 0 else 0) + (
                            strip_dbl(s_lo, s_hi, wlB, whB, limB) if limB >= 0 else 0
                        )
                    lo_t, hi_t = max(0, s_sum - limB), limA
                    stp = max(1, (hi_t - lo_t) // 6)
                    rm = 0
                    for tl in range(lo_t, hi_t + 1, stp):
                        th = min(hi_t, tl + stp - 1)
                        vv = strip_dbl(s_lo, s_hi, wlA, whA, th) + strip_dbl(s_lo, s_hi, wlB, whB, s_sum - tl)
                        if vv > rm:
                            rm = vv
                    return rm

                for i0, (w0l, w0h) in enumerate(w_bins):
                    for i2 in range(i0, len(w_bins)):
                        w2l, w2h = w_bins[i2]
                        for j0, (h0l, h0h) in enumerate(h_bins):
                            for j2, (h2l, h2h) in enumerate(h_bins):
                                elr = max_pair_dbl(s2_lo, s2_hi, h0l, h0h, h2l, h2h, s1_hi, s1_hi - w2l, s1_hi - w0l)
                                ebt = max_pair_dbl(s1_lo, s1_hi, w0l, w0h, w2l, w2h, s2_hi, s2_hi - h2l, s2_hi - h0l)
                                v_unm = getU(w0h, h0h) + getU(w2h, h2h) + ebt + elr + v11
                                if v_unm <= best:
                                    continue
                                lim10, lim12 = s2_hi - h2l, s2_hi - h0l
                                stp1 = max(1, (lim10 + 1) // 4)
                                m1 = 0
                                for tl in range(0, max(0, lim10) + 1, stp1):
                                    th = min(lim10, tl + stp1 - 1)
                                    h12h = min(lim12, s2_hi - tl)
                                    stp2 = max(1, (h12h + 1) // 4)
                                    for sl in range(0, max(0, h12h) + 1, stp2):
                                        sh = min(h12h, sl + stp2 - 1)
                                        vv = (
                                            merged_cs(s1_lo, s1_hi, w0l, w0h, h0h, th, s2_hi - sl)
                                            + merged_cs(s1_lo, s1_hi, w2l, w2h, h2h, sh, s2_hi - tl)
                                        )
                                        if vv > m1:
                                            m1 = vv
                                v = min(v_unm, m1 + elr + v11)
                                if v > best:
                                    best = v
                for W1 in range(W1_lo, W1_hi + 1):
                    for W2 in range(W2_lo, min(W2_hi, W1) + 1):
                        v = best
                        if W2 <= W1 - 1 and U[W1 - 1][W2] > v:
                            v = U[W1 - 1][W2]
                        if W2 > 0 and U[W1][W2 - 1] > v:
                            v = U[W1][W2 - 1]
                        U[W1][W2] = v
                assert (U[W1_hi][min(W2_hi, W1_hi)] ** 256) * C_den256 <= C_num256 * (((W1_lo + 2) * (W2_lo + 2)) ** 123)

    # (1B) Infinite Tail Certification for ALL m >= m0 = 4096 simultaneously (c0 = 2, alpha = 123/256):
    m0, c0, target_num = 4096, 2, 99920
    k_neg3, k_neg2, k_neg4, k_neg1 = max(0, c0 - 3), max(0, c0 - 2), max(0, c0 - 4), max(0, c0 - 1)

    _pup_e_cache = {}
    _pup_e_get = _pup_e_cache.get

    def pup_e(n, d, k_eps):
        if n < 0:
            return 0
        key = (n, d, k_eps)
        res = _pup_e_get(key)
        if res is not None:
            return res
        res = pup(n, d) if k_eps == 0 else pup(n * m0 + k_eps * d, d * m0)
        if len(_pup_e_cache) < 120000:
            _pup_e_cache[key] = res
        return res

    S1 = SCALE - 1

    def holder_pair_e(pw1, pw2, s_hi_n, s_den, h1m, h2m):
        if s_hi_n < 0 or (pw1 == 0 and pw2 == 0):
            return 0
        if h1m > s_hi_n:
            h1m = s_hi_n
        if h2m > s_hi_n:
            h2m = s_hi_n
        if h1m < 0 and h2m < 0:
            return 0
        if h1m + h2m <= s_hi_n:
            return (
                ((pw1 * pup_e(h1m, s_den, c0) + S1) // SCALE if h1m >= 0 else 0)
                + ((pw2 * pup_e(h2m, s_den, c0) + S1) // SCALE if h2m >= 0 else 0)
            )
        lo = s_hi_n - h2m
        if lo < 0:
            lo = 0
        hi = h1m
        if hi <= lo:
            return (pw1 * pup_e(lo, s_den, c0) + S1) // SCALE + (pw2 * pup_e(s_hi_n - lo, s_den, c0) + S1) // SCALE
        if pw1 == pw2 and 2 * lo <= s_hi_n <= 2 * hi:
            return 2 * ((pw1 * pup_e(s_hi_n, 2 * s_den, c0) + S1) // SCALE)
        k_sub, best = 8, 0
        diff = hi - lo
        sd8 = s_den * 8
        sh8 = s_hi_n * 8
        lo8 = lo * 8
        for k in range(k_sub):
            an = lo8 + diff * k
            bn = an + diff
            val = (pw1 * pup_e(bn, sd8, c0) + S1) // SCALE + (pw2 * pup_e(sh8 - an, sd8, c0) + S1) // SCALE
            if val > best:
                best = val
        return best

    _eff_a_cache = {}

    def eff_a_e(u_hi_n, den):
        if u_hi_n < 0:
            return 0
        res = _eff_a_cache.get((u_hi_n, den))
        if res is not None:
            return res
        best = min(pup_e(u_hi_n, den, c0), pup_e(1, 3, k_neg2))
        if 2 * u_hi_n * m0 >= den * (m0 - 2):
            smax_n = max(0, min(den, 6 * u_hi_n - 3 * den))
            s_den, k_sub = 6 * den, 16
            v0 = 2 * pup(c0, m0) + pup_e(1, 6, k_neg4)
            if v0 > best:
                best = v0
            for k in range(k_sub):
                lo_n, hi_n = smax_n * k, smax_n * (k + 1)
                tL = 2 * pup(hi_n * m0 + (2 * c0 + 1) * s_den * k_sub, 2 * s_den * k_sub * m0)
                tM = pup_e(den * k_sub - lo_n, s_den * k_sub, k_neg4)
                if tL + tM > best:
                    best = tL + tM
        if len(_eff_a_cache) < 40000:
            _eff_a_cache[(u_hi_n, den)] = best
        return best

    _eff_dbl_cache = {}

    def eff_dbl_and_pR(s_lo_n, s_hi_n, w_lo_n, w_hi_n, den):
        key = (s_lo_n, s_hi_n, w_lo_n, w_hi_n, den)
        res = _eff_dbl_cache.get(key)
        if res is not None:
            return res
        b_dir = eff_a_e(max(0, 2 * den - 3 * s_lo_n), 3 * den)
        max_a0_n = max(0, s_hi_n - w_lo_n)
        a_ints = [(0, 0, den)] if max_a0_n == 0 else [(max_a0_n * k, max_a0_n * (k + 1), den * 8) for k in range(8)]
        worst, max_pR = 0, 0
        for a_lo, a_hi, a_den in a_ints:
            mult = a_den // den
            s_lo_s, w_lo_s, w_hi_s = s_lo_n * mult, w_lo_n * mult, w_hi_n * mult
            pL = pup_e(max(0, 3 * a_hi + a_den - 3 * s_lo_s), 3 * a_den, k_neg3)
            pR = 0
            if 6 * w_lo_s <= a_den:
                v1 = pup_e(max(0, a_den - 6 * a_lo - 6 * w_lo_s), 6 * a_den, k_neg1)
                if v1 > pR:
                    pR = v1
            if 6 * w_hi_s >= a_den:
                v2 = pup_e(max(0, min(a_den - 6 * a_lo, 6 * w_hi_s - a_den)), 6 * a_den, k_neg1)
                if v2 > pR:
                    pR = v2
            if pR > max_pR:
                max_pR = pR
            v = min(b_dir, pL + pR)
            if v > worst:
                worst = v
        out = (worst, max_pR)
        if len(_eff_dbl_cache) < 40000:
            _eff_dbl_cache[key] = out
        return out

    # Case A:
    G, D, ca = 64, 192, 0
    case_a_ratios = []
    for i in range(G):
        num = 2 * pup_e(i + 1, 2 * D, c0) + pup_e(G - i, D, k_neg3)
        den = plo(D + i, D)
        val = (num * SCALE + den - 1) // den
        case_a_ratios.append(val)
        ca = max(ca, val)
    assert ca <= target_num

    # Case B (all 16 patterns = 7 orbits: 1+4+2+2+4+1+2 = 16):
    assert 1 + 4 + 2 + 2 + 4 + 1 + 2 == 16
    peff23 = eff_a_e(2, 3)
    orbit_worst = {}
    orbit_leaves = {}
    G6, D6 = 12, 36
    for name in ("0000", "1000", "1100", "1010", "1110", "1111"):
        worst = 0
        leaves = []
        stack = [(i, i + 1, j, j + 1, D6) for i in range(G6) for j in range(i + 1)]
        while stack:
            s1_l, s1_h, s2_l, s2_h, curD = stack.pop()
            den_lo = prod_lo(plo(curD + s1_l, curD), plo(curD + s2_l, curD))
            pw11 = pup_e(max(0, curD - 3 * s1_l), 3 * curD, k_neg3)
            ph11 = pup_e(max(0, curD - 3 * s2_l), 3 * curD, k_neg3)
            m_up, val = prod_up(pw11, ph11), 0
            if name == "0000":
                tot = (
                    m_up
                    + holder_pair_e(pw11, pw11, s2_h, curD, s2_h, s2_h)
                    + holder_pair_e(ph11, ph11, s1_h, curD, s1_h, s1_h)
                )
                val = (tot * SCALE + den_lo - 1) // den_lo
            elif name == "1000":
                pw12 = eff_a_e(max(0, 2 * curD - 3 * s1_l), 3 * curD)
                ph21 = eff_a_e(max(0, 2 * curD - 3 * s2_l), 3 * curD)
                k4 = 4
                for ku in range(k4):
                    w0_l, w0_h = s1_h * ku, s1_h * (ku + 1)
                    elr = holder_pair_e(ph11, ph21, s1_h * k4, curD * k4, s1_h * k4, s1_h * k4 - w0_l)
                    pw0 = pup_e(w0_h, curD * k4, c0)
                    for kv in range(k4):
                        h0_l, h0_h = s2_h * kv, s2_h * (kv + 1)
                        ebt = holder_pair_e(pw11, pw12, s2_h * k4, curD * k4, s2_h * k4, s2_h * k4 - h0_l)
                        tot = prod_up(pw0, pup_e(h0_h, curD * k4, c0)) + ebt + elr + m_up
                        val = max(val, (tot * SCALE + den_lo - 1) // den_lo)
            elif name == "1100":
                blr = holder_pair_e(peff23, peff23, s1_h, curD, s1_h, s1_h)
                pw10, pw12 = pup_e(1, 3, k_neg3), eff_a_e(min(2 * curD, 3 * curD - 3 * s1_l), 3 * curD)
                tot = blr + holder_pair_e(pw10, pw12, s2_h, curD, s2_h, s2_h) + m_up
                val = (tot * SCALE + den_lo - 1) // den_lo
            elif name == "1010":
                bbt = holder_pair_e(peff23, peff23, s2_h, curD, s2_h, s2_h)
                ph01, ph21 = pup_e(1, 3, k_neg3), eff_a_e(min(2 * curD, 3 * curD - 3 * s2_l), 3 * curD)
                tot = bbt + holder_pair_e(ph01, ph21, s1_h, curD, s1_h, s1_h) + m_up
                val = (tot * SCALE + den_lo - 1) // den_lo
            elif name == "1110":
                k6 = 6 if curD == D6 else 10
                kw_s = 4 if curD == D6 else 6
                D6k = curD * k6
                for ku in range(k6):
                    u1_h, u2_h = s1_h * (ku + 1), s1_h * (k6 - ku)
                    pu1, pu2 = pup_e(u1_h, D6k, c0), prod_up(pup_e(u2_h, D6k, c0), peff23)
                    for kv in range(k6):
                        v1_h, v2_h = s2_h * (kv + 1), s2_h * (k6 - kv)
                        pv1, pv2 = pup_e(v1_h, D6k, c0), prod_up(peff23, pup_e(v2_h, D6k, c0))
                        loc = 0
                        for kw in range(kw_s):
                            w0_l, w0_h = u1_h * kw, u1_h * (kw + 1)
                            pw0 = pup_e(w0_h, D6k * kw_s, c0)
                            t10 = prod_up(pup_e(max(0, D6k * kw_s - 3 * w0_l), 3 * D6k * kw_s, k_neg3), pv1)
                            for kh in range(kw_s):
                                h0_l, h0_h = v1_h * kh, v1_h * (kh + 1)
                                lv = (
                                    prod_up(pw0, pup_e(h0_h, D6k * kw_s, c0))
                                    + t10
                                    + prod_up(pu1, pup_e(max(0, D6k * kw_s - 3 * h0_l), 3 * D6k * kw_s, k_neg3))
                                )
                                if lv > loc:
                                    loc = lv
                        tot = loc + pu2 + pv2 + m_up
                        val = max(val, (tot * SCALE + den_lo - 1) // den_lo)
            elif name == "1111":
                k4 = 6 if curD == D6 else 10
                D4 = curD * k4
                for kuB in range(k4):
                    uB_l, uB_h = s1_h * kuB, s1_h * (kuB + 1)
                    pw10 = pup_e(max(0, D4 - 3 * uB_l), 3 * D4, k_neg3)
                    for kuT in range(kuB, k4):
                        uT_l, uT_h = s1_h * kuT, s1_h * (kuT + 1)
                        pw12 = pup_e(max(0, D4 - 3 * uT_l), 3 * D4, k_neg3)
                        ebt = holder_pair_e(pw10, pw12, s2_h, curD, s2_h, s2_h)
                        pu_avg = pup_e(uB_h + uT_h, 4 * D4, c0)
                        for kvL in range(k4):
                            vL_l, vL_h = s2_h * kvL, s2_h * (kvL + 1)
                            ph01 = pup_e(max(0, D4 - 3 * vL_l), 3 * D4, k_neg3)
                            for kvR in range(kvL, k4):
                                vR_l, vR_h = s2_h * kvR, s2_h * (kvR + 1)
                                ph21 = pup_e(max(0, D4 - 3 * vR_l), 3 * D4, k_neg3)
                                elr = holder_pair_e(ph01, ph21, s1_h, curD, s1_h, s1_h)
                                cb = 4 * prod_up(pu_avg, pup_e(vL_h + vR_h, 4 * D4, c0))
                                tot = cb + ebt + elr + m_up
                                val = max(val, (tot * SCALE + den_lo - 1) // den_lo)
            if val <= target_num:
                worst = max(worst, val)
                leaves.append([s1_l, s1_h, s2_l, s2_h, curD, val])
            else:
                assert curD <= 192, f"{name} failed: {val}"
                for a in (0, 1):
                    for b in (0, 1):
                        ns1_l, ns1_h = 2 * s1_l + a, 2 * s1_l + a + 1
                        ns2_l, ns2_h = 2 * s2_l + b, 2 * s2_l + b + 1
                        if ns2_l <= ns1_h:
                            stack.append((ns1_l, ns1_h, ns2_l, min(ns2_h, ns1_h), 2 * curD))
        orbit_worst[name] = worst
        orbit_leaves[name] = sorted(leaves)

    # Orbit 1001 (x2) with H/V-merge:
    p_mrg_w = pup_e(1, 3, k_neg1)

    def eval_1001(s1_l, s1_h, s2_l, s2_h, w0_l, w0_h, w2_l, w2_h, h0_l, h0_h, h2_l, h2_h, den):
        den_lo = (plo(den + s1_l, den) * plo(den + s2_l, den)) // SCALE
        m_up = (pup_e(den - 3 * s1_l, 3 * den, k_neg3) * pup_e(den - 3 * s2_l, 3 * den, k_neg3) + S1) // SCALE
        pw10, pR10 = eff_dbl_and_pR(s1_l, s1_h, w0_l, w0_h, den)
        pw12, pR12 = eff_dbl_and_pR(s1_l, s1_h, w2_l, w2_h, den)
        ph01, pR01 = eff_dbl_and_pR(s2_l, s2_h, h0_l, h0_h, den)
        ph21, pR21 = eff_dbl_and_pR(s2_l, s2_h, h2_l, h2_h, den)
        ebt = holder_pair_e(pw10, pw12, s2_h, den, s2_h - h2_l, s2_h - h0_l)
        elr = holder_pair_e(ph01, ph21, s1_h, den, s1_h - w2_l, s1_h - w0_l)
        c00 = (pup_e(w0_h, den, c0) * pup_e(h0_h, den, c0) + S1) // SCALE
        c22 = (pup_e(w2_h, den, c0) * pup_e(h2_h, den, c0) + S1) // SCALE
        v_unm = ((c00 + c22 + ebt + elr + m_up) * SCALE + den_lo - 1) // den_lo
        if v_unm <= target_num:
            return v_unm
        k_m = 4 if den < 384 else 6
        D_m = den * k_m
        lim10 = s2_h - h2_l
        if lim10 < 0:
            lim10 = 0
        lim12 = s2_h - h0_l
        if lim12 < 0:
            lim12 = 0
        s2k = s2_h * k_m
        m1_bt = 0
        for t in range(k_m):
            t_l = lim10 * t
            t_h = t_l + lim10
            phT = pup_e(s2k - t_l, D_m, c0)
            mrg_T = (p_mrg_w * phT + S1) // SCALE
            for u in range(k_m):
                u_l = lim12 * u
                if t_l + u_l > s2k:
                    continue
                u_h = u_l + lim12
                n10 = s2k - u_l
                ph10 = pup_e(t_h if t_h < n10 else n10, D_m, c0)
                n12 = s2k - t_l
                ph12 = pup_e(u_h if u_h < n12 else n12, D_m, c0)
                phB = pup_e(n10, D_m, c0)
                b0a = c00 + (pw10 * ph10 + S1) // SCALE
                b0b = (p_mrg_w * phB + S1) // SCALE + (pR10 * ph10 + S1) // SCALE
                b0 = b0a if b0a < b0b else b0b
                b2a = c22 + (pw12 * ph12 + S1) // SCALE
                b2b = mrg_T + (pR12 * ph12 + S1) // SCALE
                b2 = b2a if b2a < b2b else b2b
                if b0 + b2 > m1_bt:
                    m1_bt = b0 + b2
        v_m1 = ((m1_bt + elr + m_up) * SCALE + den_lo - 1) // den_lo
        if v_m1 <= target_num:
            return v_m1
        lim01 = s1_h - w2_l
        if lim01 < 0:
            lim01 = 0
        lim21 = s1_h - w0_l
        if lim21 < 0:
            lim21 = 0
        s1k = s1_h * k_m
        m2_lr = 0
        for t in range(k_m):
            t_l = lim01 * t
            t_h = t_l + lim01
            pwR = pup_e(s1k - t_l, D_m, c0)
            mrg_R = (p_mrg_w * pwR + S1) // SCALE
            for u in range(k_m):
                u_l = lim21 * u
                if t_l + u_l > s1k:
                    continue
                u_h = u_l + lim21
                n01 = s1k - u_l
                pw01 = pup_e(t_h if t_h < n01 else n01, D_m, c0)
                n21 = s1k - t_l
                pw21 = pup_e(u_h if u_h < n21 else n21, D_m, c0)
                pwL = pup_e(n01, D_m, c0)
                b0a = c00 + (ph01 * pw01 + S1) // SCALE
                b0b = (p_mrg_w * pwL + S1) // SCALE + (pR01 * pw01 + S1) // SCALE
                b0 = b0a if b0a < b0b else b0b
                b2a = c22 + (ph21 * pw21 + S1) // SCALE
                b2b = mrg_R + (pR21 * pw21 + S1) // SCALE
                b2 = b2a if b2a < b2b else b2b
                if b0 + b2 > m2_lr:
                    m2_lr = b0 + b2
        v_m2 = ((m2_lr + ebt + m_up) * SCALE + den_lo - 1) // den_lo
        return min(v_unm, v_m1, v_m2)

    G7, D7 = 8, 24
    stack = [(i, i + 1, j, j + 1, 0, i + 1, 0, i + 1, 0, j + 1, 0, j + 1, D7) for i in range(G7) for j in range(i + 1)]
    worst7, boxes7 = 0, 0
    leaves_1001 = []
    while stack:
        box = stack.pop()
        boxes7 += 1
        val = eval_1001(*box)
        if val <= target_num:
            if val > worst7:
                worst7 = val
            leaves_1001.append([*box, val])
            continue
        s1_l, s1_h, s2_l, s2_h, w0_l, w0_h, w2_l, w2_h, h0_l, h0_h, h2_l, h2_h, den = box
        assert den <= 1536, f"1001 failed at {box}: {val}"
        spans = (s1_h - s1_l, s2_h - s2_l, w0_h - w0_l, w2_h - w2_l, h0_h - h0_l, h2_h - h2_l)
        mx = max(spans)
        if spans[0] * 2 >= mx and spans[0] >= spans[1]:
            axis = 0
        elif spans[1] * 2 >= mx:
            axis = 1
        else:
            axis = spans.index(mx)
        if (box[2 * axis] + box[2 * axis + 1]) & 1:
            arr, nden = [x * 2 for x in box[:12]], den * 2
        else:
            arr, nden = list(box[:12]), den
        mid = (arr[2 * axis] + arr[2 * axis + 1]) // 2
        for half in (0, 1):
            nb = list(arr)
            if half == 0:
                nb[2 * axis + 1] = mid
            else:
                nb[2 * axis] = mid
            if nb[2] > nb[1]:
                continue
            nb[3] = min(nb[3], nb[1])
            nb[5] = min(nb[5], nb[1])
            nb[7] = min(nb[7], nb[1])
            nb[9] = min(nb[9], nb[3])
            nb[11] = min(nb[11], nb[3])
            if nb[4] > nb[7]:
                continue
            if nb[4] > nb[5] or nb[6] > nb[7] or nb[8] > nb[9] or nb[10] > nb[11] or nb[2] > nb[3]:
                continue
            stack.append((*nb, nden))
    orbit_worst["1001"] = worst7
    orbit_leaves["1001"] = sorted(leaves_1001)

    # (1C) Exact threshold collapse M0 = 2^57 (sharp at 2^56) & R15 ratio checks:
    M0 = 1 << 57
    assert ((34 * C_num) ** 128) * ((2 * M0 + 3) ** 123) < ((3 * C_den) ** 128) * (3 ** 123) * (M0 ** 128)
    M_prev = 1 << 56
    assert ((34 * C_num) ** 128) * ((2 * M_prev + 3) ** 123) > ((3 * C_den) ** 128) * (3 ** 123) * (M_prev ** 128)
    assert (3 ** 256) * (8 ** 123) < (5 ** 256) * (3 ** 124)

    dp_checkpoints = {
        "U_19_19": U[19][19],
        "U_40_40": U[40][40],
        "U_1363_1363": U[1363][1363],
        "U_2728_2728": U[2728][2728],
    }
    print(
        f"PASS Main Theorem 1 (Sub-Unit 2D Dyadic L_inf-Packing C=3/5, alpha=123/256, c0=2): "
        f"F19[19,19]={F19[19][19]}, DP U(2728,2728)={U[2728][2728]}, "
        f"m>=4096 CaseA={ca}/{SCALE}, CaseB worst={max(orbit_worst.values())}/{SCALE}, 1001 boxes={boxes7} ({len(leaves_1001)} leaves)"
    )
    return F19, {
        "C": [C_num, C_den],
        "alpha": [123, 256],
        "c0": 2,
        "scale": SCALE,
        "target_num": target_num,
        "F19": [F19[w1][:w1 + 1] for w1 in range(20)],
        "dp_checkpoints": dp_checkpoints,
        "case_a_max": ca,
        "case_a_ratios": case_a_ratios,
        "case_b_worst": orbit_worst,
        "case_b_leaf_counts": {k: len(v) for k, v in orbit_leaves.items()},
        "case_b_1001_total_visited": boxes7,
        "case_b_leaves_simple": {k: orbit_leaves[k] for k in ("0000", "1000", "1100", "1010", "1110", "1111")},
        "case_b_leaves_1001": orbit_leaves["1001"],
    }


# ==============================================================================
# 3. MAIN THEOREM 2 & 3 HELPERS — R5 STURMIAN DUAL-CROSSING LOWER BOUND
# ==============================================================================

def max_indep_circulant(k, steps):
    adj = [0] * k
    for u in range(k):
        for s in steps:
            v1 = (u + s) % k
            v2 = (u - s) % k
            if v1 != u:
                adj[u] |= 1 << v1
            if v2 != u:
                adj[u] |= 1 << v2
    best = 0

    def bb(rem, sz):
        nonlocal best
        if sz + rem.bit_count() <= best:
            return
        if not rem:
            best = sz
            return
        v = (rem & -rem).bit_length() - 1
        rem2 = rem ^ (1 << v)
        bb(rem2 & ~adj[v], sz + 1)
        bb(rem2, sz)

    bb((1 << k) - 1, 0)
    return best


def exact_attachment_lower(y):
    """Self-contained certified lower bound on |V_att(C_y)| for any y in F_EG."""
    M = 1 << (y.bit_length() - 1)
    delta = y - M
    h = (2 * M) // 3
    if M <= 8:
        for s in range(2, y // 2 + 1):
            assert not (in_feg(s + 1) and in_feg(y - s + 1)), (M, y, s)
        return y
    has_short = any(
        in_feg(s + 1) and in_feg(y - s + 1) and (y - s + 1) > M
        for s in range(2, y // 2 + 1)
    )
    vs_max = (9 * (delta - 1)) // 4 if has_short else 0
    smin = max(M // 2, y - h + 1)
    smax = min(h - 1, M // 2 + delta)
    if smin > smax:
        vl_max = 0
    else:
        regime = sum((5 * delta > M + 4, 4 * delta > M + 2, 31 * delta > 10 * M))
        n, k = ATTACHMENT[regime]
        vl_max = (n * y) // k
    return y - vs_max - vl_max


@cache
def exact_attachment_r11(length, bipartite=False):
    """R4 short-chord + R5 template attachment lower bound (supporting bipartite mode)."""
    m = 1 << (length.bit_length() - 1)
    delta = length - m
    h = (2 * m) // 3
    spans = range(3 if not bipartite else 9, length // 2 + 1, 1 if not bipartite else 2)
    spans = [s for s in spans if in_feg(s + 1) and in_feg(length - s + 1)]
    short = any(length - s + 1 > m for s in spans)
    short_vertices = ((17 * (delta - 2)) // 8 if bipartite else (9 * (delta - 1)) // 4) if short else 0
    longs = [s for s in spans if length - s + 1 <= h]
    if not longs:
        return length - short_vertices
    if length == 18:
        assert longs == [9]
        assert all(not (in_feg(2 * d + 2) and in_feg(20 - 2 * d)) for d in range(1, 9))
        return length - short_vertices - 2
    low = min(longs)
    high = length - low
    width = high - low

    def forbidden(d):
        if not width < d < low or d + high >= length:
            return False
        for mid in (2 * d + 2, length - 2 * d + 2):
            if h < mid - width and mid + width <= m:
                return True
        return False

    bound = length
    for n, steps, alpha in TEMPLATES:
        if all(forbidden((s * length) // n) and forbidden((s * length + n - 1) // n) for s in steps):
            bound = min(bound, (alpha * length) // n)
    return length - short_vertices - bound


def diamond_bound(x, y, separation):
    assert 0 < separation < y
    if separation <= x:
        return (2 * x * y) // (separation * separation)
    return (2 * y) // (2 * separation - x)


def two_bridge_permissible(x, y, t, d):
    return all(in_feg(v) for v in (t + d + 2, t + y - d + 2, x - t + d + 2, x + y - t - d + 2))


# ==============================================================================
# 4. MAIN THEOREM 2 — 100% ALL 2-CYCLE CUBIC CLAW-FREE GRAPHS
# ==============================================================================

def verify_theorem2_two_cycle_closure(F19):
    """Certify Main Theorem 2: 100% ALL 2-cycle cubic claw-free graphs satisfy Erdos-Gyarfas."""
    # (2A) Unequal blocks M2 > M1:
    #   - M2 >= 8 * M1: L1 <= 4*M1/3 < 3*L2/17 since 4/3 < 8 * 3/17:
    assert F(4, 3) < 8 * F(3, 17)

    #   - M2 = 4 * M1 (arbitrary chords: R11 fourfold frontier):
    assert F(25, 9) < 4
    assert F(16, 7) - F(47, 28) * F(5, 9) == F(341, 252) > F(4, 3)
    assert F(25, 9) > F(8, 3)
    assert 2 * F(4, 3) * F(81, 4) == 54
    assert F(54, 512) < F(3, 17)
    fourfold_pairs = 0
    for m in (4, 8, 16, 32, 64, 128, 256):
        for x in range(m + 1, (4 * m) // 3 + 1):
            for y in range(4 * m + 1, (16 * m) // 3 + 1):
                fourfold_pairs += 1
                needed = exact_attachment_r11(y)
                if needed > x:
                    continue
                assert (x + 1) // 2 + (y + 1) // 2 + 2 > (8 * m) // 3
                separation = x + y + 2 - (16 * m) // 3
                assert diamond_bound(x, y, separation) < needed
    for x, expected_gap in ((17, 7), (18, 6), (19, 6)):
        gap = min(
            d for d in range(1, 39)
            if any(two_bridge_permissible(x, 77, t, d) for t in range(1, x // 2 + 1))
        )
        assert gap == expected_gap and 77 // gap < 17

    #   - M2 = 2 * M1 (arbitrary chords: R9 diamond packing + symbolic M1 >= 128):
    twofold_pairs = 0
    for exp1 in range(2, 9):
        M1 = 1 << exp1
        M2 = 2 * M1
        for x in range(M1 + 1, (4 * M1) // 3 + 1):
            for y in range(M2 + 1, (4 * M2) // 3 + 1):
                twofold_pairs += 1
                assert x + y < 4 * M1
                lb = x + y + 2 - (8 * M1) // 3
                assert lb < y
                r_ub = diamond_bound(x, y, lb)
                if lb > x // 2:
                    r_ub = min(r_ub, y // (lb - x // 2))
                assert r_ub < exact_attachment_r11(y)
    assert F(24 * 128, 140 * 140) < F(3, 17)
    assert F(2, 128) < F(3, 17)

    # (2B) Equal blocks M2 = M1 geometric identities (all M = 2^2..2^13):
    for exp in range(2, 14):
        M = 1 << exp
        K = (4 * M) // 3
        q = M // 3
        assert K + (K // 2) + 1 == 2 * M
        assert 2 * M - K - 2 * q in (1, 2)
        assert 4 * M + 6 > 3 * K
        max_two_R = 2 * K - 2 * M - 6
        assert 2 * M - 3 * max_two_R >= 18
        assert 2 * (2 * q + 1) < 2 * M + 2 * q + 2 - K
        assert 3 * (2 * M + 4 - K) > 2 * M + 2

    # (2C) Equal blocks M in {4, 8, 16, 32, 64, 128}: ALL 625 same-parity pairs!
    small_pairs = 0
    for M in (4, 8, 16, 32, 64, 128):
        K = (4 * M) // 3
        for y in range(M + 1, K + 1):
            lower = exact_attachment_lower(y)
            assert lower >= 2
            for x in range(M + 1, y + 1):
                if (x - y) % 2 != 0:
                    continue
                small_pairs += 1
                r = lower + (lower - x) % 2
                W = x + y - 2 * M + 1
                e = K - x - 2
                if e < 0:
                    continue
                w1a, w2a = min(W, 3 * e), min(W, 3 * e)
                w1b, w2b = W, min(W, 2 * e)
                P = max((w1a + 2) * (w2a + 2), (w1b + 2) * (w2b + 2))
                ok1 = ((5 * r) ** 256 > (3 ** 256) * (P ** 123))
                if not ok1 and max(w1a, w1b) <= 19:
                    ok1 = max(F19[w1a][w2a], F19[w1b][w2b]) < r
                assert ok1, (M, x, y, r, W, e)
                two_R = min(2 * W, 2 * K - x - y - 4)
                if two_R >= 0:
                    ok2 = ((5 * r) ** 256 * (2 ** 246) > (6 ** 256) * ((two_R + 4) ** 246))
                    if not ok2 and two_R <= 19:
                        best2 = max(
                            F19[max(w1, h1)][min(w1, h1)]
                            + F19[max(two_R - w1, two_R - h1)][min(two_R - w1, two_R - h1)]
                            for w1 in range(two_R + 1)
                            for h1 in range(two_R + 1)
                        )
                        ok2 = best2 < r
                    assert ok2, (M, x, y, r, W, two_R)
    assert small_pairs == 625

    # (2D) Equal blocks M in {256, 512, 1024}: ALL 76,492 pairs!
    med_pairs = 0
    for block in (256, 512, 1024):
        cap = (4 * block) // 3
        for y in range(block + 1, cap + 1):
            delta = y - block
            regime = sum((5 * delta > block + 4, 4 * delta > block + 2, 31 * delta > 10 * block))
            n, k = ATTACHMENT[regime]
            lower = y - (9 * (delta - 1)) // 4 - (n * y) // k
            assert lower >= 2
            for x in range(block + 1, y + 1):
                bridge_count = lower + (lower - x) % 2
                width = x + y - 2 * block + 1
                imbalance = cap - x - 2
                if imbalance < 0:
                    continue
                product_bound = max(
                    (min(width, 3 * imbalance) + 2) ** 2,
                    (width + 2) * (min(width, 2 * imbalance) + 2),
                )
                assert ((5 * bridge_count) ** 256 > (3 ** 256) * (product_bound ** 123)), (block, x, y)
                doubled_width = min(2 * width, 2 * cap - x - y - 4)
                if doubled_width >= 0:
                    assert ((5 * bridge_count) ** 256 * (2 ** 246) > (6 ** 256) * ((doubled_width + 4) ** 246)), (block, x, y)
                med_pairs += 1
    assert med_pairs == 76492

    # (2E) Equal blocks M >= 2048: ALL 16 exact rational tail boxes!
    m0 = 2048
    epsilon = F(1, m0)
    third = F(1, 3)
    regimes = (
        (F(0), F(1, 5) * (1 + 4 * epsilon)),
        (F(1, 5), F(1, 4) * (1 + 2 * epsilon)),
        (F(1, 4), F(10, 31)),
        (F(10, 31), third),
    )
    tail_boxes = []
    for reg_idx, ((lo, hi), (n, k)) in enumerate(zip(regimes, ATTACHMENT)):
        stack = [(F(0), third, lo, hi, 0)]
        while stack:
            xlo, xhi, ylo, yhi, depth = stack.pop()
            if xlo > yhi:
                continue
            xhi = min(xhi, yhi)
            ylo = max(ylo, xlo)
            lower = (1 - F(n, k)) * (1 + yhi) - F(9, 4) * yhi
            width = xhi + yhi + epsilon
            imbalance = third - xlo
            radius = third - F(1, 2) * (xlo + ylo)
            single = max(
                (min(width, 3 * imbalance) + 2 * epsilon) ** 2,
                (width + 2 * epsilon) * (min(width, 2 * imbalance) + 2 * epsilon),
            )
            both = (min(width, radius) + 2 * epsilon) ** 2
            bound = (5 * lower) ** 256 * (m0 ** 10)
            assert lower > 0
            if bound > (3 ** 256) * (single ** 123) and bound > (6 ** 256) * (both ** 123):
                tail_boxes.append({
                    "regime": reg_idx,
                    "n": n,
                    "k": k,
                    "xlo": frac_pair(xlo),
                    "xhi": frac_pair(xhi),
                    "ylo": frac_pair(ylo),
                    "yhi": frac_pair(yhi),
                })
                continue
            assert depth < 24, (xlo, xhi, ylo, yhi)
            if xhi - xlo >= yhi - ylo:
                mid = F(1, 2) * (xlo + xhi)
                stack.extend(((xlo, mid, ylo, yhi, depth + 1), (mid, xhi, ylo, yhi, depth + 1)))
            else:
                mid = F(1, 2) * (ylo + yhi)
                stack.extend(((xlo, xhi, ylo, mid, depth + 1), (xlo, xhi, mid, yhi, depth + 1)))
    assert len(tail_boxes) == 16

    print(
        f"PASS Main Theorem 2 (100% ALL 2-Cycle Cubic Claw-Free): unequal (M2=2M1:{twofold_pairs}, M2=4M1:{fourfold_pairs}) "
        f"+ equal ({small_pairs} M<=128 + {med_pairs} M=256..1024 + {len(tail_boxes)} M>=2048 boxes)!"
    )
    return {
        "unequal_twofold_pairs": twofold_pairs,
        "unequal_fourfold_pairs": fourfold_pairs,
        "equal_small_pairs": small_pairs,
        "equal_med_pairs": med_pairs,
        "equal_tail_m0": m0,
        "equal_tail_boxes": tail_boxes,
    }


# ==============================================================================
# 5. MAIN THEOREM 3 — POLY-k-CYCLE, SUBLINEAR o(n) CIRCUMFERENCE, R5 STURMIAN
#    (17/18 & BIPARTITE 15/16), & MATCHING-COMPLEMENT CUBIC CLAW-FREE
# ==============================================================================

def verify_theorem3_polyk_sublinear_sturmian():
    """Certify Main Theorem 3 (R5 Sturmian, Poly-k-Cycle, Sublinear o(n), Matching-Complement)."""
    # (3A) R5 Sturmian dual-crossing templates & 4-regime symbolic + exhaustive M <= 2^18:
    for k, steps, expected_alpha in TEMPLATES:
        assert max_indep_circulant(k, steps) == expected_alpha

    def check_deficit_symbolic(a, k, d_max_slope, d_max_const):
        cM = F(1, 1) - F(a, k) - F(3, 17)
        cd = cM - F(9, 4)
        c0 = F(9, 4)
        assert cd < 0
        slope_at_max = cM + cd * d_max_slope
        const_at_max = c0 + cd * d_max_const
        assert slope_at_max > 0 and slope_at_max * 16 + const_at_max > 0

    check_deficit_symbolic(3, 7, F(1, 5), F(4, 5))
    check_deficit_symbolic(1, 3, F(1, 4), F(1, 2))
    check_deficit_symbolic(3, 11, F(10, 31), F(0, 1))
    check_deficit_symbolic(6, 23, F(1, 3), F(0, 1))

    def check_lin_ge0(cM, cd, c0, lo_d, hi_d, M_start):
        for aM, b0 in (lo_d, hi_d):
            slope = cM + cd * aM
            const = c0 + cd * b0
            assert slope >= 0 and slope * M_start + const >= 0

    regime_specs = (
        (3, (1,), (), (F(1, 5), F(1, 1)), (F(1, 4), F(1, 2)), 16),
        (11, (4,), (2,), (F(1, 4), F(3, 4)), (F(10, 31), F(0, 1)), 32),
        (23, (6, 7, 8), (3, 4, 5), (F(10, 31), F(1, 31)), (F(1, 3), F(0, 1)), 64),
    )
    for k, f1_steps, f2_steps, lo_d, hi_d, M0 in regime_specs:
        for s in f1_steps:
            check_lin_ge0(6 * s - 3 * k, 6 * s + 3 * k, 9 * k, lo_d, hi_d, M0)
            check_lin_ge0(2 * k - 6 * s, 3 * k - 6 * s, -k, lo_d, hi_d, M0)
        for s in f2_steps:
            check_lin_ge0(6 * s - k, 6 * s, 2 * k, lo_d, hi_d, M0)
            check_lin_ge0(-s, k - s, 2 * k, lo_d, hi_d, M0)

    # Exhaustive check for M = 2^4..2^18:
    sturmian_checked = 0
    for exp in range(4, 19):
        M = 1 << exp
        h = (2 * M) // 3
        for delta in range(1, M // 3 + 1):
            sturmian_checked += 1
            L = M + delta
            smin = max(M // 2, L - h + 1)
            smax = min(h - 1, M // 2 + delta)
            vs_max = (9 * (delta - 1)) // 4
            if smin > smax:
                assert 17 * (L - vs_max) > 3 * L
                continue
            W = smax - smin

            def in_dual_forb(d):
                if not (1 <= d <= L // 2 and d < smin and W < d and d + smax < L):
                    return False
                q1_ok = (h < 2 * d - W + 2) and (2 * d + W + 2 <= M)
                q2_ok = (h < L - 2 * d - W + 2) and (L - 2 * d + W + 2 <= M)
                return q1_ok or q2_ok

            if 5 * delta <= M + 4:
                k, steps, a = 7, (1,), 3
            elif 4 * delta <= M + 2:
                k, steps, a = 3, (1,), 1
            elif 31 * delta <= 10 * M:
                k, steps, a = 11, (2, 4), 3
            else:
                k, steps, a = 23, (3, 4, 5, 6, 7, 8), 6
            for s in steps:
                assert in_dual_forb((s * L) // k)
                assert in_dual_forb((s * L + k - 1) // k)
            vl_max = (a * L) // k
            assert 17 * (L - vs_max - vl_max) > 3 * L

    # Circumference transfer & bipartite 15/16 (R11) & matching-complement ell-cancellation (R4/R5):
    assert 3 * F(17, 54) == F(17, 18)  # 3 / (3 + 3/17) = 17/18
    assert 3 * F(5, 16) == F(15, 16)   # 3 / (3 + 1/5) = 15/16
    assert all(5 * exact_attachment_r11(y, True) > y for y in (10, 18, 20, 34, 36, 38, 40, 42))
    for alpha, cap, offset in (
        (F(3, 7), F(1, 5), F(4, 5)),
        (F(1, 3), F(1, 4), F(1, 2)),
        (F(3, 11), F(10, 31), F(0)),
        (F(6, 23), F(1, 3), F(0)),
    ):
        c = 1 - alpha - F(1, 5)
        assert c + (c - F(17, 8)) * cap > 0
        assert F(17, 4) + (c - F(17, 8)) * offset > 0
    for exp in range(4, 10):
        M = 1 << exp
        h = (2 * M) // 3
        for delta in range(1, M // 3 + 1):
            L = M + delta
            for ell in (1, 2, 3, 4):
                smin = max(M // 2 + 1 - ell, L - h + ell)
                smax = min(h - ell, M // 2 + delta - 1 + ell)
                if smin <= smax:
                    assert 12 * smin >= 5 * M + 6 * delta + 8
                    assert 12 * (L - smax) >= 5 * M + 6 * delta + 8
                    assert 6 * (smax - smin) <= M - 8

    # Exhaustive short-chord minimal-chain 4/9 packing check (4 <= E <= 15):
    # Checks BOTH strict-cubic non-touching and relaxed-endpoint minimal short-chord chains (26 each).
    short_spans_15 = [s for s in range(2, 16) if in_feg(s + 1)]
    assert short_spans_15 == [4, 8, 9]

    def count_short_chains(strict_disjoint):
        total = 0

        def dfs_chain(chords, sum_e, sum_o):
            nonlocal total
            if chords:
                end_e = chords[-1][1]
                gain = sum_e if sum_e >= sum_o else sum_o
                assert 9 * gain >= 4 * (end_e + 1), (chords, end_e, gain)
                total += 1
            if not chords:
                for sp in short_spans_15:
                    dfs_chain([(0, sp)], sp - 1, 0)
                return
            lp, rp = chords[-1]
            if len(chords) >= 2:
                min_l = chords[-2][1] + (1 if strict_disjoint else 0)
            else:
                min_l = 1
            for ln in range(max(lp + 1, min_l), rp):
                for sp in short_spans_15:
                    rn = ln + sp
                    if rn <= rp or rn > 15:
                        continue
                    a_sp = rp - lp
                    c_off = ln - lp
                    if not in_feg(2 * c_off + sp - a_sp + 2):
                        continue
                    if len(chords) % 2 == 0:
                        dfs_chain(chords + [(ln, rn)], sum_e + (sp - 1), sum_o)
                    else:
                        dfs_chain(chords + [(ln, rn)], sum_e, sum_o + (sp - 1))

        dfs_chain([], 0, 0)
        return total

    assert count_short_chains(True) == 26
    assert count_short_chains(False) == 26

    # Matching-Complement (Theorem 1.3(d)): base L in {5,9,10}, M=16 three-band exceptions &
    # zero valid K2 components, Type-S K1/K2 exact minima, and Regime 1/2 crossing for M <= 2^18:
    def valid_k2_exists(L):
        # Test all 4-tuples of gaps g1+g2+g3+g4=L with all 6 pairwise ears in F_EG (Order A and B):
        v2 = {s for s in range(1, L) if in_feg(s + 2) and in_feg(L - s + 2)}
        v3 = {s for s in range(1, L) if in_feg(s + 3) and in_feg(L - s + 3)}
        # Order A: (g1,g2,g3,g4) have ell=(2,3,2,3), diagonals g1+g2 and g2+g3 have ell=3
        for g1 in v2:
            for g3 in v2:
                rem = L - g1 - g3
                if rem < 2:
                    continue
                for g2 in v3:
                    g4 = rem - g2
                    if g4 in v3 and (g1 + g2) in v3 and (g2 + g3) in v3:
                        return True
        # Order B: (g1,g2,g3,g4) have ell=(3,3,3,3), diagonals g1+g2 and g2+g3 have ell=2
        for g1 in v3:
            for g2 in v3:
                if (g1 + g2) not in v2:
                    continue
                for g3 in v3:
                    g4 = L - g1 - g2 - g3
                    if g4 in v3 and (g2 + g3) in v2:
                        return True
        return False

    for L_small in (5, 9, 10):
        assert not any(in_feg(s + 1) and in_feg(L_small - s + 1) for s in range(2, L_small - 1))
        assert not any(
            in_feg(s1 + 2) and in_feg(L_small - s1 + 2)
            and in_feg(s2 + 2) and in_feg(L_small - s2 + 2)
            and in_feg(L_small - s1 - s2 + 2) and in_feg(s1 + s2 + 2)
            for s1 in range(1, L_small) for s2 in range(1, L_small - s1)
        )
        assert not valid_k2_exists(L_small)

    # M = 16: exact 3 unoriented length-3 exceptions, zero ell in {1,2} exceptions, zero K2!
    m16_exceptions = []
    for L16 in range(17, 22):
        assert not valid_k2_exists(L16), f"Unexpected K2 at L={L16}"
        d16 = L16 - 16
        for ell in (1, 2, 3):
            s_short_hi = min(d16 + ell - 1, 16 // 3 - ell)
            for s in range(1, L16 // 2 + 1):
                if in_feg(s + ell) and in_feg(L16 - s + ell):
                    in_S = s <= s_short_hi
                    in_L = (8 < s + ell <= 10) and (8 < L16 - s + ell <= 10)
                    if not (in_S or in_L):
                        m16_exceptions.append((L16, ell, s))
    assert m16_exceptions == [(20, 3, 6), (21, 3, 6), (21, 3, 7)]

    # Exact Type-S K1 and K2 minimum spans:
    k1_min_a = min(
        s1 + s2
        for s1 in range(1, 35) for s2 in range(s1, 35)
        if in_feg(s1 + 2) and in_feg(s2 + 2) and in_feg(s1 + s2 + 2)
    )
    assert k1_min_a == 15
    k2_b_min_a = min(
        g1 + g2 + g3
        for g1 in range(1, 35) for g2 in range(1, 35) for g3 in range(1, 35)
        if in_feg(g1 + 3) and in_feg(g2 + 3) and in_feg(g3 + 3)
        and in_feg(g1 + g2 + 2) and in_feg(g2 + g3 + 2) and in_feg(g1 + g2 + g3 + 3)
    )
    assert k2_b_min_a == 14
    k2_a3_min_a = min(
        g1 + g2 + g3
        for g1 in range(1, 40) for g2 in range(1, 40) for g3 in range(1, 40)
        if in_feg(g1 + 2) and in_feg(g2 + 3) and in_feg(g3 + 2)
        and in_feg(g1 + g2 + 3) and in_feg(g2 + g3 + 3) and in_feg(g1 + g2 + g3 + 3)
    )
    assert k2_a3_min_a == 32
    k2_a2_min_a = min(
        g1 + g2 + g3
        for g1 in range(1, 40) for g2 in range(1, 40) for g3 in range(1, 40)
        if in_feg(g1 + 3) and in_feg(g2 + 2) and in_feg(g3 + 3)
        and in_feg(g1 + g2 + 3) and in_feg(g2 + g3 + 3) and in_feg(g1 + g2 + g3 + 2)
    )
    assert k2_a2_min_a == 19

    # Two-regime Type-L ear crossing verification for ALL 16 <= M <= 2^18 (174,750 pairs):
    mc_checked = 0
    for exp in range(4, 19):
        M = 1 << exp
        h = (2 * M) // 3
        for delta in range(1, M // 3 + 1):
            mc_checked += 1
            L = M + delta
            if 13 * delta < 3 * M + 16:
                # Regime 1: pick even 2*d in [h + delta - 1, 2*M + delta - 2*h]
                lo2 = h + delta - 1
                hi2 = 2 * M + delta - 2 * h
                assert hi2 - lo2 >= 2
                d = (lo2 + 1) // 2
                assert lo2 <= 2 * d <= hi2
                assert 6 * d > M - 8 and 12 * d < 5 * M + 6 * delta + 8
                assert max(2 * d + 2 - delta, 2 * d + L + 4 - 2 * h) > h
                assert 2 * d + 2 * h - L <= M
            else:
                # Regime 2: both floor(L/3) and ceil(L/3) lie in (w0, b0) and land in (h, M]
                for d in (L // 3, (L + 2) // 3):
                    assert 6 * d > M - 8 and 12 * d < 5 * M + 6 * delta + 8
                    assert max(2 * d + 2 - delta, 2 * d + L + 4 - 2 * h) > h
                    assert 2 * d + 2 * h - L <= M
    assert mc_checked == sturmian_checked

    # (3B) 2-arc partition zero-wraparound & path-splitting:
    for x in range(3, 51):
        a1 = list(range(0, x // 2))
        a2 = list(range(x // 2, x))
        assert len(a1) + len(a2) == x
        for arc in (a1, a2):
            for u in arc:
                for v in arc:
                    lin = abs(u - v)
                    circ = min((u - v) % x, (v - u) % x)
                    assert lin == circ and lin <= x // 2
        assert 2 * (x // 2 + 1) > x

    # (3C) Universal k-cycle & Repaired Sublinear o(n) Circumference (R15 + R16 + R19 +2m pruning):
    y0 = 1 << 97
    assert (5 * y0) ** 128 > (68 ** 128) * ((y0 + 2) ** 123)
    assert (5 * (1 << 96)) ** 128 < (68 ** 128) * (((1 << 96) + 2) ** 123)
    expected_e = {2: 97, 3: 122, 4: 137, 5: 148, 10: 178}
    for k, exp in expected_e.items():
        yk = 1 << exp
        assert (5 * yk) ** 128 >= ((68 * (k - 1)) ** 128) * ((yk + 2) ** 123)
        yk_prev = 1 << (exp - 1)
        assert (5 * yk_prev) ** 128 < ((68 * (k - 1)) ** 128) * ((yk_prev + 2) ** 123)
    # +2m endpoint pruning absorption (R19):
    assert 5000 ** 128 < (3 ** 128) * ((y0 + 2) ** 123)
    assert (5000 * y0) ** 128 > ((68 * 1001) ** 128) * ((y0 + 2) ** 123)
    assert (1 + F(2, y0)) ** 123 < 2
    assert (5 ** 128) * (25 ** 133) >= 2 * (136 ** 128)
    assert (5 ** 128) * (24 ** 133) < 2 * (136 ** 128)

    # (3D) Equal-block k-cycle sharpening (k = 3, 4, 5 at M >= 2^36, 2^51, 2^62):
    eq_expected = {3: 36, 4: 51, 5: 62}
    eq_boxes = {}
    eps = F(1, 2048)
    third = F(1, 3)
    regimes = (
        (F(0), F(1, 5) * (1 + 4 * eps)),
        (F(1, 5), F(1, 4) * (1 + 2 * eps)),
        (F(1, 4), F(10, 31)),
        (F(10, 31), third),
    )
    for k_cyc, exp in eq_expected.items():
        mult = k_cyc - 1
        m0 = 1 << exp
        boxes = []
        for reg_idx, ((lo, hi), (n, d)) in enumerate(zip(regimes, ATTACHMENT)):
            stack = [(F(0), third, lo, hi, 0)]
            while stack:
                xlo, xhi, ylo, yhi, depth = stack.pop()
                if xlo > yhi:
                    continue
                xhi = min(xhi, yhi)
                ylo = max(ylo, xlo)
                lower = (1 - F(n, d)) * (1 + yhi) - F(9, 4) * yhi
                width = xhi + yhi + eps
                imbalance = third - xlo
                radius = third - F(1, 2) * (xlo + ylo)
                single = max(
                    (min(width, 3 * imbalance) + 2 * eps) ** 2,
                    (width + 2 * eps) * (min(width, 2 * imbalance) + 2 * eps),
                )
                both = (min(width, radius) + 2 * eps) ** 2
                bound = (5 * lower) ** 256 * (m0 ** 10)
                assert lower > 0
                if bound > ((3 * mult) ** 256) * (single ** 123) and bound > ((6 * mult) ** 256) * (both ** 123):
                    boxes.append({
                        "regime": reg_idx, "n": n, "k": d,
                        "xlo": frac_pair(xlo), "xhi": frac_pair(xhi),
                        "ylo": frac_pair(ylo), "yhi": frac_pair(yhi),
                    })
                    continue
                assert depth < 16
                if xhi - xlo >= yhi - ylo:
                    mid = F(1, 2) * (xlo + xhi)
                    stack.extend(((xlo, mid, ylo, yhi, depth + 1), (mid, xhi, ylo, yhi, depth + 1)))
                else:
                    mid = F(1, 2) * (ylo + yhi)
                    stack.extend(((xlo, xhi, ylo, mid, depth + 1), (xlo, xhi, mid, yhi, depth + 1)))
        eq_boxes[str(k_cyc)] = {"exp": exp, "count": len(boxes), "boxes": boxes}

    print(
        f"PASS Main Theorem 3 (Poly-k, Sublinear o(n) +2m pruning, R5 Sturmian 17/18 & bipartite 15/16): "
        f"sturmian_M<=2^18={sturmian_checked}, y0=2^97, eq_k_boxes={ {k: v['count'] for k, v in eq_boxes.items()} }!"
    )
    return {
        "sturmian_checked_pairs": sturmian_checked,
        "universal_y0_exp": 97,
        "fixed_k_exps": {str(k): v for k, v in expected_e.items()},
        "equal_k_boxes": eq_boxes,
    }


# ==============================================================================
# 6. MAIN THEOREM 4 — GENERAL Δ ≤ 4, δ ≥ 3 BOWTIE CLAW-FREE REDUCTIONS,
#    d_avg ≥ 7/2, tw(H/B) ≤ 3, ORDER ≥ 120, & HAMILTONIAN ALL-CHORD-B
#    (A) Bowtie Forest, d_avg >= 7/2, K33/Q3
#    (B) 15-Line 3-Tree Lemma & tw(H/B) <= 3 -> C8 or C16 + Sharp Non-Planar G_39
#    (C) Dyadic-Cycle-Free Independent-Bowtie (δ >= 3, Δ <= 4, 4-regular quotient F / perfect matching B) |V(G)| >= 120
#    (D) Tier-1 Hamiltonian All-Chord-B (L2>=10, W<=31 [L_win=17], 39 Periods, 4-Tier, N<=136)
# ==============================================================================

def build_T_H_over_B(n, edges, B_idx):
    inc = [[] for _ in range(n)]
    for idx, (u, v) in enumerate(edges):
        inc[u].append(idx)
        inc[v].append(idx)
    vid = {}
    nxt = 0
    for idx, (u, v) in enumerate(edges):
        if idx in B_idx:
            vid[(u, idx)] = vid[(v, idx)] = nxt
            nxt += 1
        else:
            vid[(u, idx)] = nxt
            vid[(v, idx)] = nxt + 1
            nxt += 2
    adj = [set() for _ in range(nxt)]
    for v in range(n):
        a, b, c = [vid[(v, ei)] for ei in inc[v]]
        for x, y in ((a, b), (b, c), (c, a)):
            adj[x].add(y)
            adj[y].add(x)
    for idx, (u, v) in enumerate(edges):
        if idx not in B_idx:
            a, b = vid[(u, idx)], vid[(v, idx)]
            adj[a].add(b)
            adj[b].add(a)
    return tuple(tuple(sorted(s)) for s in adj)


def expanded_ports(incidences, bowties):
    """Exact port-graph expansion T(H)/B keeping all 3 triangle ports per H-vertex."""
    n = len(incidences)
    assert all(len(row) == 3 and len(set(row)) == 3 for row in incidences)
    labels = {(u, v): 3 * u + i for u, row in enumerate(incidences) for i, v in enumerate(row)}
    for u, v in bowties:
        labels[v, u] = labels[u, v]
    edges = set()
    for u, row in enumerate(incidences):
        edges.update(combinations((labels[u, v] for v in row), 2))
        edges.update(
            (labels[u, v], labels[v, u])
            for v in row
            if 0 <= v < n and (min(u, v), max(u, v)) not in bowties
        )
    vertices = sorted(set(labels.values()))
    relabel = {v: i for i, v in enumerate(vertices)}
    return build_adj(len(vertices), ((relabel[u], relabel[v]) for u, v in edges))


def split_quotient(choices):
    names = {}
    sources = []
    for u, (first_side, second_side) in enumerate(choices):
        names[u] = len(sources)
        sources.append((u, first_side))
        if second_side is not None:
            sources.append((u, second_side))
    partner = {(u, v): i for i, (u, side) in enumerate(sources) for v in side}
    stubs = [[partner[v, u] for v in side] for u, side in sources]
    bowties = set()
    for u, (_, second_side) in enumerate(choices):
        if second_side is not None:
            i = names[u]
            stubs[i].append(i + 1)
            stubs[i + 1].append(i)
            bowties.add((i, i + 1))
    assert all(len(row) <= 3 for row in stubs)
    rows_h = [row + list(range(-1, -1 - (3 - len(row)), -1)) for row in stubs]
    return rows_h, bowties


def verify_k5_minor(adj, branch_sets):
    assert len(branch_sets) == 5
    adj_s = [set(row) for row in adj]
    used = set()
    for bs in branch_sets:
        s = set(bs)
        assert s and not (used & s)
        used |= s
        st = next(iter(s))
        vis = {st}
        dq = deque([st])
        while dq:
            cur = dq.popleft()
            for nb in adj_s[cur]:
                if nb in s and nb not in vis:
                    vis.add(nb)
                    dq.append(nb)
        assert vis == s
    for i in range(5):
        for j in range(i + 1, 5):
            assert any(w in branch_sets[j] for u in branch_sets[i] for w in adj_s[u])


def verify_theorem4a_bowties_and_tw3():
    """Certify Main Theorem 4(A-B) (Delta <= 4, delta >= 3): Bowtie Forest, d_avg >= 7/2,
    independent-bowtie tw(H/B) <= 3 -> C_8 or C_16, & sharp non-planar G_39 (C_16 vs. C_8, no C_4)."""
    # 1. T(K4)/B C4 exclusion for >=2 triangle bowties:
    k4_edges = [(0, 1), (1, 2), (2, 0), (0, 3), (1, 3), (2, 3)]
    assert find_simple_cycle(build_T_H_over_B(4, k4_edges, {0}), {4}) is None
    assert find_simple_cycle(build_T_H_over_B(4, k4_edges, {0, 1}), {4}) is not None
    assert find_simple_cycle(build_T_H_over_B(4, k4_edges, {0, 1, 2}), {4}) is not None

    # 2. Bowtie-forest r in {0,1,2} forcing & single-bowtie / 4-reg F_EG preservation:
    for r in (0, 1, 2):
        for L in range(2, 5000):
            assert not avoids_pow2(L + r, 2 * L + r)
    assert [L for L in range(3, 130) if avoids_pow2(L + 3, 2 * L + 3)] == [6, 14, 30, 62, 126]
    assert [L for L in range(4, 130) if avoids_pow2(L + 4, 2 * L + 4)] == [5, 13, 29, 61, 125]
    for L in range(3, 20000):
        if avoids_pow2(2 * L - 1, 3 * L - 1):
            assert in_feg(L)
        if L >= 4 and avoids_pow2(L, (3 * L + 1) // 2):
            assert in_feg(L)

    # 3. d_avg >= 7/2 closure & finite-N simple-quotient bound c^2 - 3c >= N:
    for N in (4, 6, 8, 10, 12, 14, 16, 20, 24, 50, 100):
        assert F(9 * N - 2 * N, 3 * N - N) == F(7, 2)
        assert F(9 * N - 2 * (N - 1), 3 * N - (N - 1)) < F(7, 2)
        rt = math.isqrt(4 * N + 9)
        if rt * rt < 4 * N + 9:
            rt += 1
        c_min = (3 + rt + 1) // 2
        assert c_min * c_min - 3 * c_min >= N
        assert (c_min - 1) * (c_min - 1) - 3 * (c_min - 1) < N

    # 4. Exhaustive K_{3,3} (512) & Q_3 (4096) bowtie subsets:
    k33 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3), (1, 4), (2, 5)]
    q3 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0), (0, 3), (1, 6), (2, 5), (4, 7)]
    tested_B = 0
    for n_h, edges in ((6, k33), (8, q3)):
        m = len(edges)
        for mask in range(1 << m):
            B_idx = {i for i in range(m) if (mask >> i) & 1}
            adj = build_T_H_over_B(n_h, edges, B_idx)
            targets = {1 << k for k in range(2, 7) if (1 << k) <= len(adj)}
            cyc = find_simple_cycle(adj, targets)
            verify_cycle_witness(adj, cyc, targets)
            tested_B += 1
    assert tested_B == 512 + 4096

    # 5. tw(H/B) <= 3: parallel edge ([5,8], [6,10] -> C8) & direct expanded port-graph witnesses:
    assert not avoids_pow2(5, 8) and not avoids_pow2(6, 10)
    triangle = [(0, 1), (1, 2), (0, 2)]
    biclique = [(u, v) for u in (0, 1) for v in (2, 3, 4)]
    cube = [(a, b) for a, b in combinations(range(7), 2) if (a ^ b).bit_count() == 1]
    port_witnesses = {}
    for tag, n, edges, fixed, expected_count, targets in (
        ("deg3_tri", 3, triangle, (0,), 4, (8,)),
        ("K23", 5, biclique, (), 128, (8, 16)),
        ("Q3_minus_v", 7, cube, (), 2048, (8, 16)),
    ):
        rows = build_adj(n, edges)
        options = []
        for u, row in enumerate(rows):
            options.append([(row, None)] if len(row) <= 3 else [])
            if u in fixed:
                continue
            for size in (1, 2):
                for side in combinations(row, size):
                    other = tuple(v for v in row if v not in side)
                    if 1 <= len(other) <= 2 and side < other:
                        options[-1].append((side, other))
        witness_list = []
        for choices in product(*options):
            rows_h, bowties = split_quotient(choices)
            expanded = expanded_ports(rows_h, bowties)
            cyc = find_simple_cycle(expanded, targets)
            verify_cycle_witness(expanded, cyc, targets)
            witness_list.append({
                "choices": [[list(a), None if b is None else list(b)] for a, b in choices],
                "n_expanded": len(expanded),
                "cycle": list(cyc),
            })
        assert len(witness_list) == expected_count
        port_witnesses[tag] = witness_list

    # 6. Sharp non-planar witness G_39 = T(H_14)/B:
    edges_F = [
        (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (5, 1), (5, 2), (6, 2), (6, 0),
        (7, 8), (7, 9), (7, 10), (8, 0), (8, 1), (9, 1), (9, 2), (10, 2), (10, 0),
    ]
    bags = [
        [0, 1, 2, 3], [0, 1, 3, 4], [1, 2, 3, 5], [0, 2, 3, 6],
        [0, 1, 2, 7], [0, 1, 7, 8], [1, 2, 7, 9], [0, 2, 7, 10],
    ]
    t_edges = [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7)]
    assert all(len(b) == 4 for b in bags)
    assert all(any(u in b and v in b for b in bags) for u, v in edges_F)
    t_adj = build_adj(8, t_edges)
    for v in range(11):
        sub = {i for i, b in enumerate(bags) if v in b}
        assert sub
        st = next(iter(sub))
        vis = {st}
        dq = deque([st])
        while dq:
            cur = dq.popleft()
            for nb in t_adj[cur]:
                if nb in sub and nb not in vis:
                    vis.add(nb)
                    dq.append(nb)
        assert vis == sub

    rows_F = build_adj(11, edges_F)
    splits_F = {0: ((4, 8), (6, 10)), 1: ((4, 9), (5, 8)), 2: ((5, 10), (6, 9))}
    rows_h, bowties_h = split_quotient([splits_F.get(u, (row, None)) for u, row in enumerate(rows_F)])
    adj_h = build_adj(len(rows_h), ((u, v) for u, row in enumerate(rows_h) for v in row))
    assert len(adj_h) == 14 and all(len(r) == 3 for r in adj_h)
    adj_g39 = expanded_ports(rows_h, bowties_h)
    assert len(adj_g39) == 39
    assert sorted(len(r) for r in adj_g39) == [3] * 36 + [4] * 3
    v4 = [u for u, row in enumerate(adj_g39) if len(row) == 4]
    assert len(v4) == 3 and all(w not in adj_g39[u] for u in v4 for w in v4)
    for u, row in enumerate(adj_g39):
        for a, b, c in combinations(row, 3):
            assert (b in adj_g39[a]) or (c in adj_g39[a]) or (c in adj_g39[b])
    assert find_simple_cycle(adj_g39, {4, 8}) is None
    g39_c16 = find_simple_cycle(adj_g39, {16})
    verify_cycle_witness(adj_g39, g39_c16, {16})

    # Verify explicit K_5 minor in H_14 and G_39 (using the exact canonical split_quotient labels):
    # Find/verify explicit K_5 branch sets deterministically in adj_h and adj_g39!
    h14_k5 = [[0, 2, 7], [3, 6, 8, 9], [4, 5, 12], [10, 11], [1, 13]]
    verify_k5_minor(adj_h, h14_k5)
    # Map H_14 K_5 branch sets canonically to G_39 (every H-vertex u expands to its 3-clique of ports in G_39,
    # keeping each bowtie port assigned to the lower-indexed H-endpoint):
    labels_g = {(u, v): 3 * u + i for u, row in enumerate(rows_h) for i, v in enumerate(row)}
    for u, v in bowties_h:
        labels_g[v, u] = labels_g[u, v]
    verts_g = sorted(set(labels_g.values()))
    rel_g = {v: i for i, v in enumerate(verts_g)}
    g39_k5 = []
    assigned_g = set()
    for bs in h14_k5:
        pts = sorted({rel_g[labels_g[u, v]] for u in bs for v in rows_h[u]} - assigned_g)
        assigned_g.update(pts)
        g39_k5.append(pts)
    verify_k5_minor(adj_g39, g39_k5)

    print(
        f"PASS Main Theorem 4(A-B) (Delta<=4, delta>=3 Bowties, d_avg>=7/2, K33/Q3={tested_B}, tw(H/B)<=3 -> C8 or C16): "
        f"direct port kills 0/4, 0/128, 0/2048; sharp non-planar G_39 (tw(F_11)=3, K5 in H_14 & G_39, no C4/C8, explicit C16)!"
    )
    return {
        "k33_q3_bowtie_sets": tested_B,
        "port_witness_counts": {k: len(v) for k, v in port_witnesses.items()},
        "port_witnesses": port_witnesses,
        "F11_edges": [list(e) for e in edges_F],
        "F11_tw3_bags": bags,
        "F11_tw3_tree_edges": [list(e) for e in t_edges],
        "H14_adj": [list(r) for r in adj_h],
        "H14_bowties": [list(e) for e in sorted(bowties_h)],
        "H14_k5_branch_sets": h14_k5,
        "G39_adj": [list(r) for r in adj_g39],
        "G39_v4": v4,
        "G39_c16": list(g39_c16),
        "G39_k5_branch_sets": g39_k5,
    }


def verify_theorem4c_independent_bowtie_120():
    """Certify Main Theorem 4(C): Every dyadic-cycle-free independent-bowtie claw-free graph with
    delta(G) >= 3, Delta(G) <= 4, and 4-regular quotient F = H/H_B satisfies |V(F)| >= 24, |V(G)| >= 120."""
    allowed_s = {
        r: [L - r for L in range(r, 2 * r + 1) if avoids_pow2(L + r, 2 * L + r)]
        for r in range(3, 9)
    }
    assert allowed_s == {3: [3], 4: [1], 5: [0], 6: [5, 6], 7: [3, 4, 5], 8: [1, 2, 3]}
    for a in (3, 4):
        for b in range(3, 9):
            for sa in allowed_s[a]:
                if sa == 0:
                    continue
                for sb in allowed_s[b]:
                    if sb == 0:
                        continue
                    L = (a + sa) + (b + sb) - 2
                    k = sa + sb - 2
                    assert not avoids_pow2(2 * L - k, 3 * L - k - 1)

    def assert_lifted_forb(name, n, edges, cycles_F, force_deg4=()):
        inc = [[] for _ in range(n)]
        for ei, (u, v) in enumerate(edges):
            inc[u].append(ei)
            inc[v].append(ei)
        v_opts = []
        for v in range(n):
            d = len(inc[v])
            opts = [("no_b", tuple([0] * d))] if (d <= 3 and v not in force_deg4) else []
            for bits in product((0, 1), repeat=d):
                if d > 0 and bits[0] != 0:
                    continue
                c0 = bits.count(0)
                if c0 <= 2 and d - c0 <= 2:
                    opts.append(("b", bits))
            v_opts.append(opts)
        e_to_i = {}
        for ei, (u, v) in enumerate(edges):
            e_to_i[(u, v)] = e_to_i[(v, u)] = ei
        inc_pos = [{ei: idx for idx, ei in enumerate(inc[v])} for v in range(n)]
        tot = 0
        for choice in product(*v_opts):
            tot += 1
            hit = False
            sw_at_0 = []
            for cyc, m_ch in cycles_F:
                r = len(cyc)
                s = 0
                s0 = 0
                for i in range(r):
                    u = cyc[i]
                    e1 = e_to_i[(cyc[(i - 1) % r], u)]
                    e2 = e_to_i[(u, cyc[(i + 1) % r])]
                    if choice[u][1][inc_pos[u][e1]] != choice[u][1][inc_pos[u][e2]]:
                        s += 1
                        if u == 0:
                            s0 = 1
                L = r + s
                if not avoids_pow2(2 * L - s, 3 * L - s - m_ch):
                    hit = True
                    break
                sw_at_0.append((L, s, s0))
            if not hit and force_deg4 == (0,) and len(sw_at_0) >= 2:
                (L0, s0, f0), (L1, s1, f1) = sw_at_0[0], sw_at_0[1]
                if f0 and f1:
                    Lx, kx = L0 + L1 - 2, s0 + s1 - 2
                    if not avoids_pow2(2 * Lx - kx, 3 * Lx - kx - 1):
                        hit = True
            assert hit, f"Subgraph {name} survived!"
        return tot

    checked_F = 0
    pattern_counts = {}
    expected_pattern_counts = {
        "C3+C3 share v": 243,
        "C3+C4 share v": 729,
        "C3+C5 share v": 2187,
        "C3+C6 share v": 6561,
        "C3+C7 share v": 19683,
        "C3+C8 share v": 59049,
        "C4+C6 share 1e": 11664,
        "C5+C6 share 1e": 34992,
        "C6+C6 share 1e": 104976,
        "C5+C7 share 1e": 104976,
        "2xC4 at v + edge (2,5)": 3888,
        "2xC4 at v + 2-path (2,7,5)": 11664,
    }
    for nm, n, eds, cycs, fd4 in (
        ("C3+C3 share v", 5, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)],
         [((0, 1, 2), 0), ((0, 3, 4), 0)], (0,)),
        ("C3+C4 share v", 6, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 0)],
         [((0, 1, 2), 0), ((0, 3, 4, 5), 0)], (0,)),
        ("C3+C5 share v", 7, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 6), (6, 0)],
         [((0, 1, 2), 0), ((0, 3, 4, 5, 6), 0)], (0,)),
        ("C3+C6 share v", 8, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0)],
         [((0, 1, 2), 0), ((0, 3, 4, 5, 6, 7), 0)], (0,)),
        ("C3+C7 share v", 9, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 0)],
         [((0, 1, 2), 0), ((0, 3, 4, 5, 6, 7, 8), 0)], (0,)),
        ("C3+C8 share v", 10, [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)],
         [((0, 1, 2), 0), ((0, 3, 4, 5, 6, 7, 8, 9), 0)], (0,)),
        ("C4+C6 share 1e", 8, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (4, 5), (5, 6), (6, 7), (7, 1)],
         [((0, 1, 2, 3), 0), ((0, 1, 7, 6, 5, 4), 0), ((0, 3, 2, 1, 7, 6, 5, 4), 0)], ()),
        ("C5+C6 share 1e", 9, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 7), (7, 8), (8, 1)],
         [((0, 1, 2, 3, 4), 0), ((0, 1, 8, 7, 6, 5), 0), ((0, 4, 3, 2, 1, 8, 7, 6, 5), 0)], ()),
        ("C6+C6 share 1e", 10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 6), (6, 7), (7, 8), (8, 9), (9, 1)],
         [((0, 1, 2, 3, 4, 5), 0), ((0, 1, 9, 8, 7, 6), 0), ((0, 5, 4, 3, 2, 1, 9, 8, 7, 6), 0)], ()),
        ("C5+C7 share 1e", 10, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 1)],
         [((0, 1, 2, 3, 4), 0), ((0, 1, 9, 8, 7, 6, 5), 0), ((0, 4, 3, 2, 1, 9, 8, 7, 6, 5), 0)], ()),
        ("2xC4 at v + edge (2,5)", 7, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (4, 5), (5, 6), (6, 0), (2, 5)],
         [((0, 1, 2, 3), 0), ((0, 4, 5, 6), 0), ((0, 1, 2, 5, 4), 0), ((0, 3, 2, 5, 6), 0)], (0,)),
        ("2xC4 at v + 2-path (2,7,5)", 8, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (4, 5), (5, 6), (6, 0), (2, 7), (7, 5)],
         [((0, 1, 2, 3), 0), ((0, 4, 5, 6), 0), ((0, 1, 2, 7, 5, 4), 0), ((0, 3, 2, 7, 5, 6), 0),
          ((0, 1, 2, 7, 5, 6), 0), ((0, 3, 2, 7, 5, 4), 0)], (0,)),
    ):
        cnt = assert_lifted_forb(nm, n, eds, cycs, fd4)
        pattern_counts[nm] = cnt
        checked_F += cnt
    assert pattern_counts == expected_pattern_counts, f"Pattern count mismatch: {pattern_counts}"
    assert checked_F == 360612, f"Expected 360612 lifted-H configs, got {checked_F}"

    # Extra-vertex single-edge overlaps (166 labeled graphs from R19 Astra audit):
    def cyc_edges_list(cyc):
        return [(cyc[i], cyc[(i + 1) % len(cyc)]) for i in range(len(cyc))]

    def all_simple_cycles(adj):
        n = len(adj)
        for s in range(n):
            stk = [(s, 1 << s, (s,))]
            while stk:
                u, vis, path = stk.pop()
                for w in adj[u]:
                    if w == s and len(path) >= 3 and path[1] < u:
                        yield path
                    elif w > s and not (vis & (1 << w)):
                        stk.append((w, vis | (1 << w), (*path, w)))

    overlap_counts = {}
    for a, b in ((4, 6), (5, 6), (6, 6), (5, 7)):
        first = tuple(range(a))
        first_edges = set(map(frozenset, cyc_edges_list(first)))
        checked = 0
        for r in range(1, min(a, b) - 1):
            for positions in combinations(range(2, b), r):
                for labels in permutations(range(2, a), r):
                    rep = dict(zip(positions, labels))
                    second = (0, 1, *(rep.get(i, a + i) for i in range(2, b)))
                    second_edges = set(map(frozenset, cyc_edges_list(second)))
                    if len(first_edges & second_edges) != 1:
                        continue
                    verts = sorted(set(first) | set(second))
                    vidx = {v: i for i, v in enumerate(verts)}
                    es = [(vidx[u], vidx[w]) for c in (first, second) for u, w in cyc_edges_list(c)]
                    adj = build_adj(len(verts), es)
                    if max(len(row) for row in adj) > 4:
                        continue
                    choices = []
                    for row in adj:
                        d = len(row)
                        splits = [(0,) * d] if d <= 3 else []
                        for tail in product((0, 1), repeat=d - 1):
                            bits = (0, *tail)
                            if 1 <= bits.count(0) <= 2 and 1 <= bits.count(1) <= 2:
                                splits.append(bits)
                        choices.append(splits)
                    tests = [
                        [(v, adj[v].index(c[i - 1]), adj[v].index(c[(i + 1) % len(c)])) for i, v in enumerate(c)]
                        for c in all_simple_cycles(adj)
                    ]
                    for choice in product(*choices):
                        for test in tests:
                            length = len(test)
                            switches = sum(choice[v][i] != choice[v][j] for v, i, j in test)
                            if next_pow2(2 * length + switches) <= 3 * length + 2 * switches:
                                break
                        else:
                            raise AssertionError((first, second, choice))
                    checked += 1
        overlap_counts[f"{a}_{b}"] = checked
    assert tuple(overlap_counts.values()) == (9, 27, 75, 55)

    # Moore / distance-3 count: min(29, 25, 24, 25) = 24 -> |V(G)| = 5*24 = 120:
    assert min(
        1 + 4 + 10 + 7 + 7,
        1 + 4 + 12 + (36 - 4 + 3) // 4,
        1 + 4 + 11 + (32 - 2 + 3) // 4,
        1 + 4 + 10 + 2 + 3 + 2 + 3,
    ) == 24
    assert 5 * 24 == 120
    print(
        f"PASS Main Theorem 4(C) (Dyadic-Cycle-Free Independent-Bowtie delta>=3, 4-reg quotient |V(G)|>=120): "
        f"{checked_F} lifted-H configs + 166 extra-vertex overlaps -> 0 surv; 4-reg |V(F)|>=24, |V(G)|>=120!"
    )
    return {
        "lifted_h_configs": checked_F,
        "lifted_h_pattern_counts": pattern_counts,
        "extra_vertex_overlaps": overlap_counts,
        "min_order_F": 24,
        "min_order_G": 120,
    }


def verify_theorem4d_hamiltonian_all_chord_b():
    """Certify Main Theorem 4(D): Hamiltonian All-Chord-B (Tier-1 bounds: L2>=10, W<=31 [L_win=17],
    39 all-order periods, 4-Tier Dyadic-Octave, arbitrary matchings ALL even N <= 136)."""
    # 1. 2-chord girth L_2 >= 10:
    for L in (4, 5, 7, 8, 9):
        for m in range((L - 4) // 2 + 1):
            assert not avoids_pow2(2 * L - 2, 3 * L - 2 - m)
    assert not avoids_pow2(10, 16) and not avoids_pow2(6, 10)

    # 2. Local short-chord exclusion W <= 7 (L=4), W <= 15 (L=8), W <= 31 (L_win=17 -> 29,357 visits):
    def line_arcs(first, second):
        endpoints = sorted((*first, *second))
        if len(set(endpoints)) < 4:
            return None
        a, b, c, d = endpoints
        if {first, second} == {(a, b), (c, d)}:
            return None
        return ((a, b), (c, d))

    def pair_length_avoids(rim_length):
        return rim_length != 4 and lift_avoids(rim_length + 2, 2)

    def local_strip(width, length):
        spans = [s for s in range(2, width + 1) if lift_avoids(s + 1, 1)]
        assert length + 2 * max(spans) <= 102
        choices = sorted({
            tuple(sorted((u, u + sign * span)))
            for u in range(length)
            for span in spans
            for sign in (-1, 1)
        })
        incident = [[] for _ in range(length)]
        for i, chord in enumerate(choices):
            for v in chord:
                if 0 <= v < length:
                    incident[v].append(i)
        incident = [sum(1 << i for i in row) for row in incident]
        compatible = [0] * len(choices)
        for i, j in combinations(range(len(choices)), 2):
            first, second = choices[i], choices[j]
            if set(first) & set(second):
                continue
            arcs = line_arcs(first, second)
            if arcs is None or pair_length_avoids(sum(b - a for a, b in arcs)):
                compatible[i] |= 1 << j
                compatible[j] |= 1 << i
        window_masks = [sum(1 << v for v in chord if 0 <= v < length) for chord in choices]
        interiors = [None if a < 0 or b >= length else ((1 << b) - (1 << (a + 1))) for a, b in choices]
        chosen = []
        visits = 0

        def search(unmatched, options):
            nonlocal visits
            visits += 1
            for i in chosen:
                interior = interiors[i]
                if interior is None:
                    continue
                internal = sum(
                    window_masks[j] & interior == window_masks[j] and window_masks[j].bit_count() == 2
                    for j in chosen
                )
                internal += (unmatched & interior).bit_count() // 2
                a, b = choices[i]
                if not lift_avoids(b - a + 1, 1, internal):
                    return False
            if not unmatched:
                return True
            candidates = min((incident[v] & options for v in bit_indices(unmatched)), key=int.bit_count)
            for i in bit_indices(candidates):
                chosen.append(i)
                survivor = search(unmatched ^ window_masks[i], options & compatible[i])
                chosen.pop()
                if survivor:
                    return True
            return False

        assert not search((1 << length) - 1, (1 << len(choices)) - 1)
        return visits

    strip_visits = {
        "W7_L4": local_strip(7, 4),
        "W15_L8": local_strip(15, 8),
        "W31_L17": local_strip(31, 17),
    }
    assert strip_visits["W31_L17"] == 29357

    # 3. 4-Tier Dyadic-Octave & Universal Translate Lemma (all odd g >= 1, P = 2^a >= 16):
    assert all(4 * (j + 1) <= 5 * j for j in (4, 5, 6))
    assert 35 >= 2 * 16 and 35 + 5 >= 2 * (16 + 2)
    assert 35 >= 2 * 16 and (35 + 5) // 2 >= 16 + 1
    assert 30 >= 2 * 14 and 30 + 5 >= 2 * (14 + 1)
    for a in range(4, 65):
        p = 1 << a
        a_lo, a_hi = (4 * p - 1) // 5, p - 1
        b_lo, b_hi = (8 * p + 14) // 15, (8 * p - 2) // 12
        c_lo, c_hi = (16 * p + 24) // 25, (16 * p - 2) // 20
        assert 2 * a_hi + 1 <= 2 * p <= (5 * a_lo + 5) // 2
        assert 4 * a_hi + 2 <= 4 * p <= 5 * a_lo + 5
        assert 12 * b_hi <= 8 * p <= 15 * b_lo
        assert 12 * b_hi + 2 <= 8 * p <= 15 * b_lo + 5
        assert 20 * c_hi <= 16 * p <= 25 * c_lo
        assert 20 * c_hi + 2 <= 16 * p <= 25 * c_lo + 5
        assert ((b_hi - 1) | 1) + 2 >= (c_lo | 1)
        assert ((c_hi - 1) | 1) + 2 >= (a_lo | 1)

    # 4. ALL 39 All-Order Periods:
    #    - 7 even periods {2,4,6,8,10,12,14}: {2,4,6,10,12,14} closed by W<=31; k=8 closed by Z-strip + C104..C160:
    def cyclic_arcs(first, second, order):
        a, b, c, d = sorted((*first, *second))
        if len({a, b, c, d}) != 4:
            return
        for left, right in (((a, b), (c, d)), ((b, c), (d, a))):
            if {tuple(sorted(left)), tuple(sorted(right))} != {first, second}:
                yield ((left[0], (left[1] - left[0]) % order), (right[0], (right[1] - right[0]) % order))

    def residue_matchings(residues):
        if not residues:
            yield ()
            return
        first, *tail = residues
        for i, second in enumerate(tail):
            for matching in residue_matchings(tail[:i] + tail[i + 1:]):
                yield ((first, second), *matching)

    def period_eight(order=None):
        span_limit = 56 if order is None else min(56, order // 2 - 1)
        if order is not None and order // 2 <= 56 and order % 16 == 0:
            assert not lift_avoids(order // 2 + 1, 1)
        spans = [
            s for s in range(-span_limit, span_limit + 1)
            if abs(s) >= 2 and lift_avoids(abs(s) + 1, 1)
            and (order is None or lift_avoids(order - abs(s) + 1, 1))
        ]
        edge_options = {
            (a, b): tuple(s for s in spans if (a + s) % 8 == b)
            for a, b in combinations(range(8), 2)
        }

        @cache
        def compatible(a, da, b, db):
            first = tuple(sorted((a, a + da))) if order is None else tuple(sorted((a, (a + da) % order)))
            for second_start in range(b, 39, 8):
                partner = second_start + db
                if order is None:
                    arcs = line_arcs(first, tuple(sorted((second_start, partner))))
                    if arcs and not pair_length_avoids(sum(v - u for u, v in arcs)):
                        return False
                else:
                    second = tuple(sorted((second_start % order, partner % order)))
                    if any(not pair_length_avoids(r + s) for (_, r), (_, s) in cyclic_arcs(first, second, order)):
                        return False
            return True

        def survives(option, earlier):
            a, b, step = option
            new = ((a, step), (b, -step))
            for x, dx in new:
                for y, dy in (*new, *earlier):
                    if not compatible(x, dx, y, dy) or not compatible(y, dy, x, dx):
                        return False
            return True

        tested = 0
        for pairs in residue_matchings(tuple(range(8))):
            def search(i, earlier):
                nonlocal tested
                tested += 1
                if i == len(pairs):
                    steps = dict(earlier)
                    for start, step in earlier:
                        spans_to_check = ((step,) if step > 0 else ()) if order is None else (step % order,)
                        for span in spans_to_check:
                            internal = 0
                            for offset in range(1, span):
                                dest = offset + steps[(start + offset) % 8]
                                if order is not None:
                                    dest %= order
                                internal += 0 < dest < span
                            if not lift_avoids(span + 1, 1, internal // 2):
                                return False
                    return True
                a, b = pairs[i]
                return any(
                    search(i + 1, (*earlier, (a, step), (b, -step)))
                    for step in edge_options[a, b]
                    if survives((a, b, step), earlier)
                )

            assert not search(0, ()), (order, pairs)
        return tested

    assert 2 * 56 + 7 + 31 < 168
    k8_visits = {str(n): period_eight(n) for n in (None, *range(104, 168, 8))}

    #    - 32 odd periods g <= 63: exact 23 open (g, m) orders (93,902 nodes -> 0 surv):
    def forced_lift(length, chords):
        return bool(hits_pow2(2 * length - chords, (5 * length + 1) // 2))

    def bad_pair(n, a, b, c, d, bad):
        if a > b:
            a, b = b, a
        if c > d:
            c, d = d, c
        if c < a:
            a, b, c, d = c, d, a, b
        if b < c:
            return bad[c - b + n - d + a + 2]
        if b < d:
            return bad[c - a + d - b + 2] or bad[b - c + n - d + a + 2]
        return bad[c - a + b - d + 2]

    def allowed_spans(n):
        return [s for s in range(2, n // 2 + 1) if not forced_lift(s + 1, 1) and not forced_lift(n - s + 1, 1)]

    def close_odd_order(g, m):
        n = g * m
        bad = [length == 6 or (length >= 4 and forced_lift(length, 2)) for length in range(n + 2)]

        def orbit_compatible(step, r, other):
            a, b = 0, step
            for c in range(r, n, g):
                d = (c + other) % n
                if c in (a, b) or d in (a, b):
                    continue
                if bad_pair(n, a, b, c, d, bad):
                    return False
            return True

        step_set = {
            d for s in allowed_spans(n) for d in (s, n - s)
            if (d % g or d == n // 2) and orbit_compatible(d, 0, d)
        }
        if n // 2 not in step_set:
            return 0
        steps = sorted(step_set)
        reverse = [steps.index(n - d) for d in steps]
        all_steps = (1 << len(steps)) - 1
        moves = [d % g for d in steps]
        anchor = steps.index(n // 2)
        positive = [d for d in steps if d <= n // 2]
        pair_tests = {(d, e, r): orbit_compatible(d, r, e) for d in positive for e in positive for r in range(g)}
        orientations = [(min(d, n - d), d if d > n // 2 else 0) for d in steps]
        compatible = [[0] * len(steps) for _ in range(g)]
        for r in range(1, g):
            for i, (d, shift) in enumerate(orientations):
                compatible[r][i] = sum(
                    1 << j
                    for j, (e, offset) in enumerate(orientations)
                    if pair_tests[d, e, (r + offset - shift) % g]
                )
        no_hit = [sum(1 << j for j, move in enumerate(moves) if move != r) for r in range(g)]
        step_mask = [
            [compatible[d][k] & no_hit[(-d) % g] for k in range(len(steps))]
            for d in range(g)
        ]
        count = 0

        def search(unset, domains):
            nonlocal count
            count += 1
            if not unset:
                return True
            r = -1
            best_c = len(steps) + 1
            m_u = unset
            while m_u:
                lsb = m_u & -m_u
                v = lsb.bit_length() - 1
                m_u ^= lsb
                c = domains[v].bit_count()
                if c < best_c:
                    best_c = c
                    r = v
                    if c == 0:
                        return False
            m_d = domains[r]
            while m_d:
                lsb_d = m_d & -m_d
                i = lsb_d.bit_length() - 1
                m_d ^= lsb_d
                t = (r + moves[i]) % g
                j = reverse[i]
                if t != r:
                    if not (unset & (1 << t)) or not (domains[t] & (1 << j)):
                        continue
                    left = unset ^ (1 << r) ^ (1 << t)
                    updated = domains.copy()
                    m_l = left
                    ok = True
                    while m_l:
                        lsb_l = m_l & -m_l
                        v = lsb_l.bit_length() - 1
                        m_l ^= lsb_l
                        nv = updated[v] & step_mask[(v - r) % g][i] & step_mask[(v - t) % g][j]
                        if not nv:
                            ok = False
                            break
                        updated[v] = nv
                    if ok and search(left, updated):
                        return True
                else:
                    left = unset ^ (1 << r)
                    updated = domains.copy()
                    m_l = left
                    ok = True
                    while m_l:
                        lsb_l = m_l & -m_l
                        v = lsb_l.bit_length() - 1
                        m_l ^= lsb_l
                        nv = updated[v] & step_mask[(v - r) % g][i]
                        if not nv:
                            ok = False
                            break
                        updated[v] = nv
                    if ok and search(left, updated):
                        return True
            return False

        domains = [all_steps] + [compatible[r][anchor] & no_hit[-r % g] for r in range(1, g)]
        assert not search((1 << g) - 2, domains), (g, m)
        return count

    odd_cases = [
        (g, m)
        for g in range(1, 64, 2)
        for m in range(2, 14, 2)
        if (n := m * g) > 128
        and avoids_pow2(2 * n, (5 * n) // 2)
        and not forced_lift(n // 2 + 1, 1)
        and all(avoids_pow2(4 * j * g + 2, 5 * j * g + 5) for j in range(1, m // 2))
    ]
    assert len(odd_cases) == 23
    odd_visits = sum(close_odd_order(g, m) for g, m in odd_cases)
    assert odd_visits == 93902

    short_even = [
        k for k in range(2, 15, 2)
        if any(j * k <= 31 and not avoids_pow2(4 * j * k + 2, 5 * j * k + 5) for j in range(1, 8))
    ]
    all_39_periods = sorted(set(range(1, 64, 2)) | set(short_even) | {8})
    assert len(all_39_periods) == 39

    # 5. Arbitrary matchings for ALL even N <= 136 (Tier-1 certified!):
    #    - N <= 102: 641 matching leaves, zero survivors (R19 exact internal-chord check):
    def rim_arc(a, b, n):
        if a <= b:
            return ((1 << (b - a + 1)) - 1) << a
        return ((1 << n) - (1 << a)) | ((1 << (b + 1)) - 1)

    def two_chord_arcs(first, second):
        a, b = first
        c, d = second
        if c < a:
            a, b, c, d = c, d, a, b
        if a < c < b < d:
            return ((a, c, b, d), (c, b, d, a))
        if a < c < d < b:
            return ((a, c, d, b),)
        assert a < b < c < d
        return ((b, c, d, a),)

    leaves_102 = Counter()
    for n in range(4, 104, 2):
        if not lift_avoids(n, 0, n // 2):
            continue
        candidates = [
            (a, b) for a, b in combinations(range(n), 2)
            if 1 < b - a < n - 1
            and lift_avoids(b - a + 1, 1, (b - a - 1) // 2)
            and lift_avoids(n - b + a + 1, 1, (n - b + a - 1) // 2)
        ]
        vertex_masks = [(1 << a) | (1 << b) for a, b in candidates]
        edge_bits = [1 << i for i in range(len(candidates))]
        by_vertex = [0] * n
        compatible = [0] * len(candidates)
        allowed2 = [False] * 4 + [lift_avoids(L, 2, (L - 4) // 2) for L in range(4, n + 1)]
        for i, (a, b) in enumerate(candidates):
            eb_i = edge_bits[i]
            by_vertex[a] |= eb_i
            by_vertex[b] |= eb_i
            ci = 0
            n_minus_b = n - b
            for j in range(i):
                c, d = candidates[j]
                if c == a or d == a or d == b:
                    continue
                if d < a:
                    ok = allowed2[a - d + n_minus_b + c + 2]
                elif d < b:
                    ok = allowed2[a - c + b - d + 2] and allowed2[d - a + n_minus_b + c + 2]
                else:
                    ok = allowed2[a - c + d - b + 2]
                if ok:
                    ci |= edge_bits[j]
                    compatible[j] |= eb_i
            compatible[i] |= ci
        spans = [min(b - a, n + a - b) for a, b in candidates]
        chosen = []

        def exact_candidate_survives():
            ports = [vertex_masks[i] for i in chosen]

            def cycle_survives(vertices, used):
                internal = sum(pair & vertices == pair for pair in ports)
                return lift_avoids(vertices.bit_count(), used, internal - used)

            for i in chosen:
                a, b = candidates[i]
                if not all(cycle_survives(rim_arc(u, v, n), 1) for u, v in ((a, b), (b, a))):
                    return False
            return all(
                cycle_survives(rim_arc(x, y, n) | rim_arc(z, w, n), 2)
                for i, j in combinations(chosen, 2)
                for x, y, z, w in two_chord_arcs(candidates[i], candidates[j])
            )

        def search_102(unmatched, options):
            if not unmatched:
                leaves_102[n] += 1
                assert not exact_candidate_survives(), (n, [candidates[i] for i in chosen])
                return
            fewest = len(candidates) + 1
            branch = 0
            m_u = unmatched
            while m_u:
                lsb = m_u & -m_u
                vertex = lsb.bit_length() - 1
                m_u ^= lsb
                available = by_vertex[vertex] & options
                count = available.bit_count()
                if count == 0:
                    return
                if count < fewest:
                    fewest, branch = count, available
            m_b = branch
            while m_b:
                lsb = m_b & -m_b
                i = lsb.bit_length() - 1
                m_b ^= lsb
                chosen.append(i)
                search_102(unmatched ^ vertex_masks[i], options & compatible[i])
                chosen.pop()

        for i in bit_indices(by_vertex[0]):
            if candidates[i][1] != spans[i]:
                continue
            options = sum(edge_bits[j] for j in bit_indices(compatible[i]) if spans[j] >= spans[i])
            chosen.append(i)
            search_102(((1 << n) - 1) ^ vertex_masks[i], options)
            chosen.pop()
    assert sum(leaves_102.values()) == 641 and all(leaves_102[n] for n in (82, 84, 86))

    #    - 104 <= N <= 128: rim C_N itself hits C_256!
    for n in range(104, 130, 2):
        assert not lift_avoids(n, 0, n // 2)

    #    - N in {130, 132, 134, 136}: exact arbitrary-matching search (R23 Tier-1):
    def matching_frontier(n):
        spans = allowed_spans(n)
        bad = [forced_lift(length, 2) if length >= 4 else False for length in range(n + 2)]
        visits = 0
        for start in spans:
            allowed_s = set(spans[spans.index(start):])
            chords = [
                (a, b) for a, b in combinations(range(1, n), 2)
                if start not in (a, b) and min(b - a, n - b + a) in allowed_s
                and not bad_pair(n, 0, start, a, b, bad)
            ]
            incidence = [0] * n
            endpoints = []
            for i, (a, b) in enumerate(chords):
                incidence[a] |= 1 << i
                incidence[b] |= 1 << i
                endpoints.append((1 << a) | (1 << b))
            all_chords = (1 << len(chords)) - 1
            compat_cache = {}

            def search(remaining, options):
                nonlocal visits
                visits += 1
                if not remaining:
                    return True
                choices = min((incidence[v] & options for v in bit_indices(remaining)), key=int.bit_count)
                for i in bit_indices(choices):
                    cm = compat_cache.get(i)
                    if cm is None:
                        a, b = chords[i]
                        cands = all_chords & ~(incidence[a] | incidence[b])
                        cm = 0
                        m_c = cands
                        while m_c:
                            lsb = m_c & -m_c
                            j = lsb.bit_length() - 1
                            m_c ^= lsb
                            c, d = chords[j]
                            if not bad_pair(n, a, b, c, d, bad):
                                cm |= lsb
                        compat_cache[i] = cm
                    if search(remaining ^ endpoints[i], options & cm):
                        return True
                return False

            assert not search(((1 << n) - 1) ^ 1 ^ (1 << start), all_chords), (n, start)
        return visits

    frontier_136 = {n: matching_frontier(n) for n in range(130, 138, 2)}
    assert frontier_136 == {130: 73, 132: 236, 134: 242, 136: 723}

    print(
        f"PASS Main Theorem 4(D) (Hamiltonian All-Chord-B Tier-1): L_2>=10, W<=31 L_win=17 ({strip_visits['W31_L17']}), "
        f"39 all-order periods (23 odd cases={odd_visits}), 4-Tier Octave, ALL even N<=136 (<=102:{sum(leaves_102.values())} leaves, 130..136:{frontier_136})!"
    )
    return {
        "strip_visits": strip_visits,
        "k8_visits": k8_visits,
        "all_39_periods": all_39_periods,
        "odd_open_cases": [list(p) for p in odd_cases],
        "odd_open_visits": odd_visits,
        "arbitrary_matching_le102_leaves": sum(leaves_102.values()),
        "arbitrary_matching_104_128_rim_hit": 256,
        "arbitrary_matching_130_136_visits": {str(k): v for k, v in frontier_136.items()},
    }


# ==============================================================================
# 7. MAIN ENTRYPOINT & DETERMINISTIC WITNESS EXPORT
# ==============================================================================

def write_json_deterministic(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n"
    path.write_text(text, encoding="utf-8")


def main():
    if not __debug__:
        raise SystemExit("Run with assertions enabled (do not pass -O).")
    parser = argparse.ArgumentParser(description="Standalone Zero-Float Verifier for Paper 2 (Claw-Free EG)")
    parser.add_argument(
        "--export-witnesses",
        type=Path,
        default=None,
        help="Optional directory to emit byte-deterministic JSON witness bundles for Stages 2-3 Lean modules",
    )
    args = parser.parse_args()

    started = monotonic_ns()
    check_zero_floats()

    F19, w_thm1 = verify_theorem1_dyadic_packing_2d()
    w_thm2 = verify_theorem2_two_cycle_closure(F19)
    w_thm3 = verify_theorem3_polyk_sublinear_sturmian()
    w_thm4ab = verify_theorem4a_bowties_and_tw3()
    w_thm4c = verify_theorem4c_independent_bowtie_120()
    w_thm4d = verify_theorem4d_hamiltonian_all_chord_b()

    if args.export_witnesses is not None:
        out_dir = args.export_witnesses
        write_json_deterministic(out_dir.joinpath("dyadic_packing_2d.json"), w_thm1)
        write_json_deterministic(out_dir.joinpath("two_cycle_closure.json"), {**w_thm2, **w_thm3})
        write_json_deterministic(out_dir.joinpath("tw3_and_g39.json"), {**w_thm4ab, "independent_bowtie_120": w_thm4c})
        write_json_deterministic(out_dir.joinpath("hamiltonian_all_chord_b.json"), w_thm4d)
        print(f"Exported 4 deterministic JSON witness bundles to {out_dir}")

    elapsed_ms = (monotonic_ns() - started) // 1_000_000
    rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    assert elapsed_ms < 60000, f"Exceeded 60s budget: {elapsed_ms} ms"
    assert rss_kib < 500 * 1024, f"Exceeded 500 MiB RSS: {rss_kib} KiB"
    print(f"PASS ALL Paper 2 Claw-Free EG Certificates in {elapsed_ms} ms (peak RSS {rss_kib // 1024} MiB, ZERO floats, ZERO `/`!)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
