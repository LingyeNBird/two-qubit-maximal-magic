#!/usr/bin/env python3
"""Stage 3: Compute exact rational ideal cofactors W_0, W_01, R_01 via sparse Q-elimination."""

from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import itertools
import json
import time

HERE = Path(__file__).resolve().parent

EDGES = [
    (0,1),(0,2),(0,3),(0,4),(0,5),
    (1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),
    (3,4),(3,5),
    (4,5),
]
EDGE_IDX = {}
EDGE_SGN = {}
for idx, (u, v) in enumerate(EDGES):
    EDGE_IDX[(u, v)] = idx; EDGE_SGN[(u, v)] = 1
    EDGE_IDX[(v, u)] = idx; EDGE_SGN[(v, u)] = -1

S6_edge_maps = []
for p in itertools.permutations(range(6)):
    inv = sum(1 for i in range(6) for j in range(i + 1, 6) if p[i] > p[j])
    s = [-1 if (inv & 1) else 1, 1, 1, 1, 1, 1]
    emap = tuple((EDGE_IDX[(p[u], p[v])], s[u] * s[v] * EDGE_SGN[(p[u], p[v])]) for u, v in EDGES)
    S6_edge_maps.append(emap)

canon_cache = {}


def canon_monom(m):
    if m in canon_cache:
        return canon_cache[m]
    mask = 0
    for e in m:
        u, v = EDGES[e]
        mask ^= (1 << u) ^ (1 << v)
    assert mask in (0, 63), f"Unexpected parity mask {mask} for {m}"
    best_m, best_sgn, best_pi = None, 0, -1
    seen_sgn = {}
    for pi, emap in enumerate(S6_edge_maps):
        sgn = 1
        img = []
        for e in m:
            ne, es = emap[e]
            sgn *= es
            img.append(ne)
        img.sort()
        t = tuple(img)
        if t in seen_sgn:
            if seen_sgn[t] != sgn:
                canon_cache[m] = (None, 0, -1)
                return (None, 0, -1)
        else:
            seen_sgn[t] = sgn
        if best_m is None or t < best_m:
            best_m, best_sgn, best_pi = t, sgn, pi
    res = (best_m, best_sgn, best_pi)
    canon_cache[m] = res
    return res


def mul_polys(p1, p2):
    out = defaultdict(Fraction)
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            out[tuple(sorted(m1 + m2))] += c1 * c2
    return {m: c for m, c in out.items() if c != 0}


def orbit_compress(poly):
    out = defaultdict(Fraction)
    for m, c in poly.items():
        if c == 0:
            continue
        cm, sgn, _ = canon_monom(m)
        if cm is not None:
            out[cm] += sgn * c
    return {m: c for m, c in out.items() if c != 0}


def gen_monoms(maxdeg, allowed_masks):
    res = []
    def dfs(start_e, rem, mask, cur):
        if mask in allowed_masks:
            res.append(cur)
        if rem == 0:
            return
        for e in range(start_e, 15):
            u, v = EDGES[e]
            dfs(e, rem - 1, mask ^ (1 << u) ^ (1 << v), cur + (e,))
    dfs(0, maxdeg, 0, ())
    return res


def solve_cofactors(polys_path=HERE / "cert_polys.txt", weights_path=HERE / "exact_weights.json"):
    t0 = time.time()
    polys = []
    with open(polys_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            p = {}
            for part in line.split(";"):
                part = part.strip()
                if not part:
                    continue
                c_str, m_str = part.split()
                m = tuple(sorted(int(x) for x in m_str.split(",")))
                p[m] = Fraction(int(c_str))
            polys.append(p)

    with open(weights_path) as f:
        c_exact = [Fraction(int(num), int(den)) for num, den in json.load(f)]

    target_un = {(0, 0, 0, 0): Fraction(15), (): Fraction(-3, 4)}
    R_orb = defaultdict(Fraction, orbit_compress(target_un))
    for k, poly in enumerate(polys):
        q2_orb = orbit_compress(mul_polys(poly, poly))
        for cm, val in q2_orb.items():
            R_orb[cm] -= c_exact[k] * val
    R_orb = {cm: val for cm, val in R_orb.items() if val != 0}
    print(f"[{time.time()-t0:.2f}s] R_orb has {len(R_orb)} nonzero canonical orbits")

    h0 = {(0, 0): Fraction(1), (1, 1): Fraction(1), (2, 2): Fraction(1), (3, 3): Fraction(1), (4, 4): Fraction(1), (): Fraction(-1)}
    h01 = {(1, 5): Fraction(1), (2, 6): Fraction(1), (3, 7): Fraction(1), (4, 8): Fraction(1)}
    g01 = {(0,): Fraction(1), (9, 14): Fraction(-1), (10, 13): Fraction(1), (11, 12): Fraction(-1)}

    m_h0 = gen_monoms(6, {0, 63})
    m_h01 = gen_monoms(6, {3, 60})
    print(f"[{time.time()-t0:.2f}s] Candidate cofactors: deg<=6 mask {{0,63}} = {len(m_h0)}, mask {{3,60}} = {len(m_h01)}")

    col_vecs, col_desc, seen_vecs = [], [], set()
    for gname, gpoly, mlist in [("h0", h0, m_h0), ("h01", h01, m_h01), ("g01", g01, m_h01)]:
        for m in mlist:
            oc = orbit_compress(mul_polys({m: Fraction(1)}, gpoly))
            if not oc:
                continue
            items = sorted(oc.items())
            sgn = 1 if items[0][1] > 0 else -1
            key = tuple((cm, sgn * val) for cm, val in items)
            if key not in seen_vecs:
                seen_vecs.add(key)
                col_vecs.append(oc)
                col_desc.append((gname, m))

    all_orbs = sorted(set(R_orb.keys()) | set(cm for v in col_vecs for cm in v.keys()))
    orb_to_row = {cm: i for i, cm in enumerate(all_orbs)}
    order = sorted(range(len(col_vecs)), key=lambda j: (len(col_desc[j][1]), len(col_vecs[j])))

    pivots = {}
    for j in order:
        v = dict(col_vecs[j])
        comb = {j: Fraction(1)}
        while v:
            r = min(v.keys(), key=lambda cm: orb_to_row[cm])
            if r in pivots:
                pv, pcomb = pivots[r]
                f = v[r]
                for cm, val in pv.items():
                    nv = v.get(cm, Fraction(0)) - f * val
                    if nv == 0:
                        v.pop(cm, None)
                    else:
                        v[cm] = nv
                for cj, val in pcomb.items():
                    nc = comb.get(cj, Fraction(0)) - f * val
                    if nc == 0:
                        comb.pop(cj, None)
                    else:
                        comb[cj] = nc
            else:
                inv = Fraction(1) / v[r]
                pivots[r] = ({cm: val * inv for cm, val in v.items()}, {cj: val * inv for cj, val in comb.items()})
                break

    rem = dict(R_orb)
    sol = defaultdict(Fraction)
    while rem:
        r = min(rem.keys(), key=lambda cm: orb_to_row[cm])
        assert r in pivots, f"Orbit {r} not in ideal span"
        pv, pcomb = pivots[r]
        f = rem[r]
        for cm, val in pv.items():
            nv = rem.get(cm, Fraction(0)) - f * val
            if nv == 0:
                rem.pop(cm, None)
            else:
                rem[cm] = nv
        for cj, val in pcomb.items():
            sol[cj] += f * val

    sol = {cj: val for cj, val in sol.items() if val != 0}
    check = defaultdict(Fraction, R_orb)
    for cj, coeff in sol.items():
        for cm, val in col_vecs[cj].items():
            check[cm] -= coeff * val
    assert all(v == 0 for v in check.values()), "Exact reconstruction failed"

    by_gen = defaultdict(int)
    for cj in sol:
        by_gen[col_desc[cj][0]] += 1
    print(f"[{time.time()-t0:.2f}s] Exact zero-remainder ideal identity verified (cofactor terms: {dict(by_gen)})")
    return polys, c_exact, sol, col_desc


if __name__ == "__main__":
    solve_cofactors()
