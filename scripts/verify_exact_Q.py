#!/usr/bin/env python3
"""Stage 2: Solve exact rational weights c_1..c_7 in Q_{>0} for Q_1..Q_7."""

from fractions import Fraction
from pathlib import Path
import itertools
import json

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


def load_cert_polys(path=HERE / "cert_polys.txt"):
    polys = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            terms = []
            for part in line.split(";"):
                part = part.strip()
                if not part:
                    continue
                c_str, m_str = part.split()
                terms.append((int(c_str), tuple(int(x) for x in m_str.split(","))))
            polys.append(terms)
    return polys


def householder(v):
    n2 = sum(x * x for x in v)
    return [
        [(Fraction(1) if i == j else Fraction(0)) - Fraction(2 * v[i] * v[j], n2) for j in range(6)]
        for i in range(6)
    ]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(6)) for j in range(6)] for i in range(6)]


def trans(A):
    return [[A[j][i] for j in range(6)] for i in range(6)]


J = [[Fraction(0)] * 6 for _ in range(6)]
for k in range(3):
    J[2 * k][2 * k + 1] = Fraction(1)
    J[2 * k + 1][2 * k] = Fraction(-1)


def pf4(A, a, b, c, d):
    return A[a][b] * A[c][d] - A[a][c] * A[b][d] + A[a][d] * A[b][c]


def pf6(A):
    s = Fraction(0)
    for j in range(1, 6):
        rem = [k for k in range(1, 6) if k != j]
        s += (1 if j % 2 == 1 else -1) * A[0][j] * pf4(A, *rem)
    return s


def make_rat_A(vecs):
    Q = [[Fraction(1 if i == j else 0) for j in range(6)] for i in range(6)]
    for v in vecs:
        Q = mm(householder(v), Q)
    A = mm(mm(Q, J), trans(Q))
    assert pf6(A) == 1
    return A


def compute_exact_weights(polys):
    test_As = [
        J,
        make_rat_A([[1, 2, 1, 0, 0, 0], [0, 1, 3, 1, 0, 1]]),
        make_rat_A([[1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0]]),
        make_rat_A([[1, 2, 0, 1, 0, 0], [0, 1, 2, 0, 1, 0]]),
        make_rat_A([[1, 1, 1, 1, 0, 0], [1, -1, 0, 1, 2, 0]]),
        make_rat_A([[1, 0, 2, 1, 0, 1], [2, 1, 0, -1, 1, 0]]),
        make_rat_A([[1, 2, 3, 0, 1, 0], [0, 1, -1, 2, 0, 1]]),
        make_rat_A([[2, 1, 1, 1, 1, 0], [1, -2, 0, 1, -1, 1]]),
        make_rat_A([[1, 1, 0, 2, 1, 1], [1, 0, -1, 1, 2, -1]]),
    ]

    S6_edge_maps = []
    for p in itertools.permutations(range(6)):
        inv = sum(1 for i in range(6) for j in range(i + 1, 6) if p[i] > p[j])
        s = [-1 if (inv & 1) else 1, 1, 1, 1, 1, 1]
        emap = []
        for e in range(15):
            u, v = EDGES[e]
            pu, pv = p[u], p[v]
            emap.append((EDGE_IDX[(pu, pv)], s[u] * s[v] * EDGE_SGN[(pu, pv)]))
        S6_edge_maps.append(emap)

    def eval_S6_avg(poly, A_edges):
        tot = Fraction(0)
        for emap in S6_edge_maps:
            val = Fraction(0)
            for c, m in poly:
                t = Fraction(c)
                for e in m:
                    ne, sgn = emap[e]
                    t *= sgn * A_edges[ne]
                val += t
            tot += val * val
        return tot / 720

    M, rhs = [], []
    for idx, A in enumerate(test_As):
        A_edges = [A[u][v] for u, v in EDGES]
        target = sum(x ** 4 for x in A_edges) - Fraction(3, 4)
        row = [eval_S6_avg(p, A_edges) for p in polys]
        M.append(row)
        rhs.append(target)
        print(f"Evaluated exact rational test {idx} (target = {float(target):.6f})")

    n = len(polys)
    aug = [M[i][:] + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if aug[r][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = Fraction(1, 1) / aug[col][col]
        aug[col] = [x * inv for x in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [aug[r][j] - f * aug[col][j] for j in range(n + 1)]

    c_exact = [aug[i][n] for i in range(n)]
    for i, c in enumerate(c_exact):
        assert c > 0, f"c_{i+1} not positive: {c}"
        print(f"  c_{i+1} = {c}  ({float(c):.10f})")

    for idx in range(n, len(test_As)):
        diff = sum(c_exact[k] * M[idx][k] for k in range(n)) - rhs[idx]
        assert diff == 0, f"Nonzero residual on test {idx}: {diff}"
        print(f"  Extra rational test {idx}: exact residual = 0")

    return c_exact


if __name__ == "__main__":
    polys = load_cert_polys()
    print(f"Loaded {len(polys)} exact integer polynomials:")
    for idx, p in enumerate(polys):
        print(f"  Q_{idx+1}: {len(p)} terms, max|coef|={max(abs(c) for c, _ in p)}")
    c_exact = compute_exact_weights(polys)
    out = HERE / "exact_weights.json"
    with open(out, "w") as f:
        json.dump([[str(c.numerator), str(c.denominator)] for c in c_exact], f, indent=2)
    print(f"Saved exact rational weights to {out}")
