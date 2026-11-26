#!/usr/bin/env python3
"""Stage 4: Clear common denominator D, build B_6^+ orbit-cancellation witnesses, export JSON."""

from collections import defaultdict
from pathlib import Path
import itertools
import json
import math

import compute_cofactors as cc

HERE = Path(__file__).resolve().parent
EDGES, EDGE_IDX, EDGE_SGN = cc.EDGES, cc.EDGE_IDX, cc.EDGE_SGN

B6_720 = []
for p in itertools.permutations(range(6)):
    inv = sum(1 for i in range(6) for j in range(i + 1, 6) if p[i] > p[j])
    s = (-1 if (inv & 1) else 1, 1, 1, 1, 1, 1)
    assert ((-1 if (inv & 1) else 1) * math.prod(s)) == 1
    emap = tuple((EDGE_IDX[(p[u], p[v])], s[u] * s[v] * EDGE_SGN[(p[u], p[v])]) for u, v in EDGES)
    B6_720.append((p, s, emap))


def act_monom(emap, m):
    sgn, img = 1, []
    for e in m:
        ne, es = emap[e]
        sgn *= es
        img.append(ne)
    img.sort()
    return sgn, tuple(img)


def det_B6(g):
    p, s = g
    inv = sum(1 for i in range(6) for j in range(i + 1, 6) if p[i] > p[j])
    return (-1 if (inv & 1) else 1) * math.prod(s)


def compose_B6(g1, g2):
    p1, s1 = g1
    p2, s2 = g2
    return tuple(p2[p1[i]] for i in range(6)), tuple(s1[i] * s2[p1[i]] for i in range(6))


def inv_B6(g):
    p, s = g
    pinv = [0] * 6
    for i in range(6):
        pinv[p[i]] = i
    pinv = tuple(pinv)
    return pinv, tuple(s[pinv[i]] for i in range(6))


def emap_of(g):
    p, s = g
    return tuple((EDGE_IDX[(p[u], p[v])], s[u] * s[v] * EDGE_SGN[(p[u], p[v])]) for u, v in EDGES)


def main():
    polys, c_exact, sol, col_desc = cc.solve_cofactors()
    denoms = [4] + [c.denominator for c in c_exact] + [v.denominator for v in sol.values()]
    D = math.lcm(*denoms)
    c_int = [int(c * D) for c in c_exact]
    assert all(x > 0 for x in c_int) and (3 * D) % 4 == 0

    U0_int, U01_int, V01_int = [], [], []
    for cj, coef in sorted(sol.items()):
        gname, m_cof = col_desc[cj]
        ci = int(coef * D)
        if gname == "h0":
            U0_int.append((ci, m_cof))
        elif gname == "h01":
            U01_int.append((ci, m_cof))
        elif gname == "g01":
            V01_int.append((ci, m_cof))

    F_int = defaultdict(int)
    F_int[(0, 0, 0, 0)] += 15 * D
    F_int[()] -= (3 * D) // 4
    for k, poly in enumerate(polys):
        for m1, c1 in poly.items():
            for m2, c2 in poly.items():
                F_int[tuple(sorted(m1 + m2))] -= c_int[k] * int(c1) * int(c2)

    gen_int = {
        "h0": [((0, 0), 1), ((1, 1), 1), ((2, 2), 1), ((3, 3), 1), ((4, 4), 1), ((), -1)],
        "h01": [((1, 5), 1), ((2, 6), 1), ((3, 7), 1), ((4, 8), 1)],
        "g01": [((0,), 1), ((9, 14), -1), ((10, 13), 1), ((11, 12), -1)],
    }
    for gname, lst in [("h0", U0_int), ("h01", U01_int), ("g01", V01_int)]:
        for ci, m_cof in lst:
            for mg, cg in gen_int[gname]:
                F_int[tuple(sorted(m_cof + mg))] -= ci * cg

    F_int = {m: v for m, v in F_int.items() if v != 0}
    print(f"Exact integer F_int has {len(F_int)} nonzero terms. D = {D}")

    zero_witnesses, canon_witnesses = {}, {}
    orb_sums = defaultdict(int)
    for m, coeff in sorted(F_int.items()):
        seen = {}
        z_wit = None
        best_t, best_sgn, best_g = None, 0, None
        for p, s, emap in B6_720:
            sgn, img = act_monom(emap, m)
            if img in seen:
                prev_sgn, prev_g = seen[img]
                if prev_sgn != sgn:
                    g_neg = compose_B6((p, s), inv_B6(prev_g))
                    assert det_B6(g_neg) == 1
                    csgn, cimg = act_monom(emap_of(g_neg), m)
                    assert csgn == -1 and cimg == m
                    z_wit = g_neg
                    break
            else:
                seen[img] = (sgn, (p, s))
            if best_t is None or img < best_t:
                best_t, best_sgn, best_g = img, sgn, (p, s)
        if z_wit is not None:
            zero_witnesses[m] = z_wit
        else:
            assert det_B6(best_g) == 1
            csgn, cimg = act_monom(emap_of(best_g), m)
            assert csgn == best_sgn and cimg == best_t
            canon_witnesses[m] = (best_g, best_sgn, best_t)
            orb_sums[best_t] += best_sgn * coeff

    assert all(v == 0 for v in orb_sums.values())
    print(f"Verified witnesses: {len(zero_witnesses)} zero + {len(canon_witnesses)} canon across {len(orb_sums)} reps")

    cert_data = {
        "D": str(D),
        "c_int": [str(x) for x in c_int],
        "Q_polys": [[(int(c), list(m)) for m, c in sorted(p.items())] for p in polys],
        "U0": [(str(c), list(m)) for c, m in U0_int],
        "U01": [(str(c), list(m)) for c, m in U01_int],
        "V01": [(str(c), list(m)) for c, m in V01_int],
        "zero_witnesses": {",".join(map(str, m)): [list(g[0]), list(g[1])] for m, g in zero_witnesses.items()},
        "canon_witnesses": {",".join(map(str, m)): [list(g[0]), list(g[1]), sgn, list(cm)] for m, (g, sgn, cm) in canon_witnesses.items()},
    }
    out_path = HERE / "exact_certificate.json"
    with open(out_path, "w") as f:
        json.dump(cert_data, f)
    print(f"Saved {out_path}")


if __name__ == "__main__":
    main()
