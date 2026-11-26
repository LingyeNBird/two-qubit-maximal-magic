#!/usr/bin/env python3
"""Standalone zero-dependency verifier for the exact degree-8 SOS certificate.

Independently checks (using only exact integer arithmetic, without Lean):
  1. D > 0, 4 | D, c_1..c_7 > 0, and Q_1(a) = 4*a_0^3 - a_0.
  2. Exact expansion of the 1,409-term integer remainder F(a).
  3. Direct B_6^+ symmetrization sum_{h in B_6^+} F(h . a) == 0 via parity-reduced S_6 summation.
  4. Independent verification of all 1,409 explicit B_6^+ orbit-cancellation witnesses.
"""

from collections import defaultdict
from pathlib import Path
import itertools
import json
import math
import time

HERE = Path(__file__).resolve().parent
EDGES = [(i, j) for i in range(6) for j in range(i + 1, 6)]
EDGE_IDX = {e: k for k, e in enumerate(EDGES)}


def mul_poly(p, q):
    out = defaultdict(int)
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            out[tuple(sorted(m1 + m2))] += c1 * c2
    return {m: c for m, c in out.items() if c != 0}


def load_poly(entries):
    out = defaultdict(int)
    for c, m in entries:
        out[tuple(sorted(int(e) for e in m))] += int(c)
    return {m: c for m, c in out.items() if c != 0}


def perm_sign(p):
    inv = sum(1 for i in range(6) for j in range(i + 1, 6) if p[i] > p[j])
    return -1 if (inv & 1) else 1


def act_b6(p, s, m):
    assert sorted(p) == [0, 1, 2, 3, 4, 5] and all(x in (-1, 1) for x in s)
    assert perm_sign(p) * math.prod(s) == 1, "Not in B_6^+"
    sgn, img = 1, []
    for e in m:
        i, j = EDGES[e]
        pi, pj = p[i], p[j]
        sgn *= s[i] * s[j] * (1 if pi < pj else -1)
        img.append(EDGE_IDX[(min(pi, pj), max(pi, pj))])
    img.sort()
    return sgn, tuple(img)


def main(cert_path=HERE / "exact_certificate.json"):
    t0 = time.time()
    d = json.loads(Path(cert_path).read_text())

    D = int(d["D"])
    c_int = [int(x) for x in d["c_int"]]
    Q = [load_poly(q) for q in d["Q_polys"]]
    U0, U01, V01 = load_poly(d["U0"]), load_poly(d["U01"]), load_poly(d["V01"])

    assert D > 0 and D % 4 == 0 and len(c_int) == 7 and all(c > 0 for c in c_int)
    assert Q[0] == {(0, 0, 0): 4, (0,): -1}, f"Unexpected Q_1: {Q[0]}"

    # Local ideal generators for M_6
    h0 = {(0, 0): 1, (1, 1): 1, (2, 2): 1, (3, 3): 1, (4, 4): 1, (): -1}
    h01 = {(1, 5): 1, (2, 6): 1, (3, 7): 1, (4, 8): 1}
    g01 = {(0,): 1, (9, 14): -1, (10, 13): 1, (11, 12): -1}

    # Exact expansion of F(a)
    F = defaultdict(int)
    F[(0, 0, 0, 0)] += 15 * D
    F[()] -= (3 * D) // 4
    for ck, qk in zip(c_int, Q):
        for m, v in mul_poly(qk, qk).items():
            F[m] -= ck * v
    for cof, gen in ((U0, h0), (U01, h01), (V01, g01)):
        for m, v in mul_poly(cof, gen).items():
            F[m] -= v
    F = {m: v for m, v in F.items() if v != 0}
    print(f"[{time.time()-t0:.2f}s] Expanded F(a): {len(F)} nonzero monomials (D = {D})")

    # Check 1: Direct B_6^+ symmetrization (parity-reduced S_6 summation, independent of witnesses)
    pmaps = []
    for p in itertools.permutations(range(6)):
        sp = perm_sign(p)
        mp = []
        for i, j in EDGES:
            pi, pj = p[i], p[j]
            mp.append((EDGE_IDX[(min(pi, pj), max(pi, pj))], 1 if pi < pj else -1))
        pmaps.append((mp, sp))

    sym = defaultdict(int)
    for m, v in F.items():
        par = [0] * 6
        for e in m:
            i, j = EDGES[e]
            par[i] ^= 1
            par[j] ^= 1
        if any(par) and not all(par):
            continue  # averages to 0 over the 32 even sign flips
        all_odd = all(par)
        for mp, sp in pmaps:
            sgn = sp if all_odd else 1
            img = []
            for e in m:
                te, o = mp[e]
                sgn *= o
                img.append(te)
            img.sort()
            sym[tuple(img)] += 32 * v * sgn
    sym = {m: v for m, v in sym.items() if v != 0}
    assert len(sym) == 0, f"Symmetrization failed: {len(sym)} nonzero terms"
    print(f"[{time.time()-t0:.2f}s] Direct B_6^+ symmetrization: sum_{{h in B_6^+}} F(h.a) == 0 VERIFIED")

    # Check 2: Explicit per-monomial B_6^+ orbit-cancellation witnesses
    z_wits = {
        tuple(int(x) for x in k.split(",")) if k else (): v
        for k, v in d["zero_witnesses"].items()
    }
    c_wits = {
        tuple(int(x) for x in k.split(",")) if k else (): v
        for k, v in d["canon_witnesses"].items()
    }
    assert len(F) == len(z_wits) + len(c_wits)
    canon_acc = defaultdict(int)
    for m, coeff in F.items():
        if m in z_wits:
            p, s = z_wits[m]
            sgn, img = act_b6(p, s, m)
            assert sgn == -1 and img == m, f"Invalid zero witness for {m}"
        else:
            p, s, wsgn, cm = c_wits[m]
            cm = tuple(cm)
            sgn, img = act_b6(p, s, m)
            assert sgn == wsgn and img == cm, f"Invalid canon witness for {m}"
            canon_acc[cm] += wsgn * coeff
    assert all(v == 0 for v in canon_acc.values()), "Canonical orbit sums did not cancel"
    print(
        f"[{time.time()-t0:.2f}s] Witness verification: {len(z_wits)} zero + {len(c_wits)} canon "
        f"({len(canon_acc)} reps) == 0 VERIFIED"
    )


if __name__ == "__main__":
    main()
