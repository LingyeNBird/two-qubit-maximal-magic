#!/usr/bin/env python3
"""Stage 5: Emit TwoQubitMaximalMagic/CertificateData.lean from exact_certificate.json."""

from collections import defaultdict
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
REPO = HERE.parent


def pack_monom(m):
    val = 0
    for e in m:
        val += 16 ** e
    return val


def unpack_check(val, m):
    counts = [0] * 15
    for e in m:
        counts[e] += 1
    for e in range(15):
        assert (val // (16 ** e)) % 16 == counts[e]


def poly_from_json(lst):
    out = defaultdict(int)
    for c, m in lst:
        pm = pack_monom(m)
        unpack_check(pm, m)
        out[pm] += int(c)
    return sorted((pm, c) for pm, c in out.items() if c != 0)


def mul_packed(p1, p2):
    out = defaultdict(int)
    for m1, c1 in p1:
        for m2, c2 in p2:
            out[m1 + m2] += c1 * c2
    return sorted((m, c) for m, c in out.items() if c != 0)


def fmt_poly_chunk(p, indent="  "):
    items = [f"({c}, {m})" for m, c in p]
    lines = [indent + ", ".join(items[i : i + 4]) for i in range(0, len(items), 4)]
    return "[\n" + ",\n".join(lines) + "\n]"


def emit_poly(out, name, p, max_chunk=120):
    if len(p) <= max_chunk:
        out.append(f"def {name} : Poly := {fmt_poly_chunk(p)}")
    else:
        parts = [p[i : i + max_chunk] for i in range(0, len(p), max_chunk)]
        for idx, part in enumerate(parts):
            out.append(f"private def {name}_{idx+1} : Poly := {fmt_poly_chunk(part)}")
        concat = " ++ ".join(f"{name}_{idx+1}" for idx in range(len(parts)))
        out.append(f"def {name} : Poly := {concat}")


def fmt_b6wit(p, s):
    s_bool = ["true" if x == -1 else "false" for x in s]
    return f"B6Wit.mk {p[0]} {p[1]} {p[2]} {p[3]} {p[4]} {p[5]} {' '.join(s_bool)}"


def render_lean(cert_path=HERE / "exact_certificate.json"):
    with open(cert_path) as f:
        d = json.load(f)

    D = int(d["D"])
    assert (3 * D) % 4 == 0
    c_int = [int(x) for x in d["c_int"]]
    assert all(x > 0 for x in c_int)

    Q_polys = [poly_from_json(q) for q in d["Q_polys"]]
    Q_sqs = [mul_packed(q, q) for q in Q_polys]

    H0 = sorted([(0, -1), (2, 1), (2 * 16, 1), (2 * 16 ** 2, 1), (2 * 16 ** 3, 1), (2 * 16 ** 4, 1)])
    H01 = sorted([(16 + 16 ** 5, 1), (16 ** 2 + 16 ** 6, 1), (16 ** 3 + 16 ** 7, 1), (16 ** 4 + 16 ** 8, 1)])
    G01 = sorted([(1, 1), (16 ** 9 + 16 ** 14, -1), (16 ** 10 + 16 ** 13, 1), (16 ** 11 + 16 ** 12, -1)])

    U0 = poly_from_json(d["U0"])
    U01 = poly_from_json(d["U01"])
    V01 = poly_from_json(d["V01"])
    U0H0, U01H01, V01G01 = mul_packed(U0, H0), mul_packed(U01, H01), mul_packed(V01, G01)

    F_packed = defaultdict(int)
    F_packed[0] -= (3 * D) // 4
    F_packed[4] += 15 * D
    for k in range(7):
        for m, c in Q_sqs[k]:
            F_packed[m] -= c_int[k] * c
    for prod in (U0H0, U01H01, V01G01):
        for m, c in prod:
            F_packed[m] -= c
    F_sorted = sorted((m, c) for m, c in F_packed.items() if c != 0)

    zero_wits = {
        pack_monom([] if m_str == "" else [int(x) for x in m_str.split(",")]): g
        for m_str, g in d["zero_witnesses"].items()
    }
    canon_wits = {
        pack_monom([] if m_str == "" else [int(x) for x in m_str.split(",")]): (p, s, sgn, pack_monom(cm))
        for m_str, (p, s, sgn, cm) in d["canon_witnesses"].items()
    }
    assert len(F_sorted) == len(zero_wits) + len(canon_wits)
    for pm, _ in F_sorted:
        assert (pm in zero_wits) ^ (pm in canon_wits)

    out = [
        "import TwoQubitMaximalMagic.PolyEngine",
        "",
        "/-!",
        "# Exact Integer Degree-8 SOS Certificate Data for Open Quantum Problem E28",
        "",
        "Auto-generated exact integer polynomials `Q₁..Q₇`, positive integer weights `c₁..c₇`,",
        "common denominator `D`, ideal cofactors `U₀, U₀₁, V₀₁`, and the 1,409 verified `B₆⁺`",
        "orbit-cancellation witnesses.",
        "-/",
        "",
        "namespace TwoQubitMaximalMagic",
        "",
        f"def certD : ℤ := {D}",
    ]
    for k in range(7):
        out.append(f"def certC{k+1} : ℤ := {c_int[k]}")
    out.append("")
    emit_poly(out, "polyH0", H0)
    emit_poly(out, "polyH01", H01)
    emit_poly(out, "polyG01", G01)
    out.append("")
    for k in range(7):
        emit_poly(out, f"polyQ{k+1}", Q_polys[k])
    out.append("")
    for k in range(7):
        emit_poly(out, f"polyQ{k+1}Sq", Q_sqs[k])
    out.append("")
    emit_poly(out, "polyU0", U0)
    emit_poly(out, "polyU01", U01)
    emit_poly(out, "polyV01", V01)
    out.append("")
    emit_poly(out, "polyU0H0", U0H0)
    emit_poly(out, "polyU01H01", U01H01)
    emit_poly(out, "polyV01G01", V01G01)
    out.append("")

    chunks = [F_sorted[i : i + 100] for i in range(0, len(F_sorted), 100)]
    for idx, chunk in enumerate(chunks):
        lines = []
        for pm, c in chunk:
            if pm in zero_wits:
                p, s = zero_wits[pm]
                wit_str = f"OrbitWit.zero ({fmt_b6wit(p, s)})"
            else:
                p, s, sgn, pcm = canon_wits[pm]
                wit_str = f"OrbitWit.canon ({fmt_b6wit(p, s)}) ({sgn}) {pcm}"
            lines.append(f"  ({c}, {pm}, {wit_str})")
        out.append(f"def certEntries{idx+1} : List (ℤ × ℕ × OrbitWit) := [\n" + ",\n".join(lines) + "\n]")
        out.append("")

    concat_expr = " ++ ".join(f"certEntries{i+1}" for i in range(len(chunks)))
    out.append(f"def certEntries : List (ℤ × ℕ × OrbitWit) := {concat_expr}")
    out.append("")
    out.append("end TwoQubitMaximalMagic")
    out.append("")
    return "\n".join(out)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="Verify byte-for-byte match with CertificateData.lean without overwriting")
    args = ap.parse_args()
    content = render_lean()
    target = REPO / "TwoQubitMaximalMagic" / "CertificateData.lean"
    if args.check:
        assert target.read_text() == content, "Mismatch with existing CertificateData.lean"
        print(f"OK: generated output matches {target} byte-for-byte ({len(content.splitlines())} lines)")
    else:
        target.write_text(content)
        print(f"Wrote {target} ({len(content.splitlines())} lines)")
