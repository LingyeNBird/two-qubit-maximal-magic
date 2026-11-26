# Formal Proof of the Two-Qubit Maximal Magic Conjecture (Two-Qubit Case of Open Quantum Problem E28)

[![Lean 4 CI](https://github.com/LingyeNBird/two-qubit-maximal-magic/actions/workflows/lean_ci.yml/badge.svg)](https://github.com/LingyeNBird/two-qubit-maximal-magic/actions/workflows/lean_ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24565157.svg)](https://doi.org/10.5281/zenodo.24565157)

A complete, pure-kernel **Lean 4** (`v4.36.0` + Mathlib4) proof of the **two-qubit ($n = 2$) maximal magic conjecture** of Q. Liu, I. Low, and Z. Yin (*"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035, 2026; [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550)), which resolves the two-qubit $\max M_2 = \ln(16/7)$ subproblem of [Open Quantum Problem E28](https://openquantumproblems.com/p/E28) and extends it to all Rényi orders $\alpha \ge 2$, together with a complete formal characterization of all **480** maximal-magic states and their entanglement (concurrence) distribution.

- **Zero `sorry`**
- **Zero `native_decide`** (all polynomial normalizations, multiplications, and 1,409 group-orbit witnesses are verified inside Lean 4's pure kernel by definitional equality `rfl`)
- **Standard axioms only**: all 32 audited declarations depend solely on `[propext, Classical.choice, Quot.sound]`
- **Reproducible discovery & Lean-free verification**: complete zero-dependency C++17/Python discovery pipeline and a standalone exact-integer Python verifier (`scripts/verify_certificate.py`, `< 1 s`) are included in `scripts/`

---

## Scope & Limitations

To make the exact scope of the formalization transparent:

- **What IS formally proved here**:
  1. The sharp upper bound on the Stabilizer Rényi Entropy $M_\alpha(|\psi\rangle)$ for **all pure two-qubit ($n = 2$) states** and **all Rényi orders $\alpha \ge 2$**, including $\max M_2 = \ln(16/7)$.
  2. Exact attainment by $|\psi_{\mathrm{MUB}}\rangle = \frac{1}{2}(1, 1, 1, i)$.
  3. Complete formal characterization of **all** maximizers (for every $\alpha \ge 2$):
     - Pauli spectrum $|\langle\psi|P|\psi\rangle| \in \{0, \frac{1}{2}\}$ for all 15 non-identity Paulis;
     - The 3 vanishing non-identity Pauli expectations form a **maximal pairwise-commuting Pauli triple** (explicitly proved equivalent to a perfect matching in $K_6$ via Pauli commutation $\iff$ edge disjointness);
     - The maximizers form a **single two-qubit Clifford orbit** of $|\psi_{\mathrm{MUB}}\rangle$ (up to global phase), using the textbook definition `IsClifford2` of the two-qubit Clifford group;
     - The set of maximizer pure-state density matrices $\{|\psi\rangle\langle\psi|\}$ is finite and has **exact cardinality 480**;
     - A normalized pure two-qubit state maximizes $M_\alpha$ ($\alpha \ge 2$) **if and only if** it is a **two-qubit Pauli (multi-qubit Weyl–Heisenberg) 5-MUB fiducial state** (its 16-state two-qubit Pauli orbit partitions into 4 orthonormal bases extending to a complete set of $d+1 = 5$ mutually unbiased bases in $\mathbb{C}^4$).
  4. **Exact entanglement (concurrence) dichotomy & counts**: Every maximizer has Wootters concurrence strictly in $\{1/2, 1/\sqrt{2}\}$ (hence **none** is maximally entangled and **none** is separable), with **exactly 192** maximizers having $C = 1/2$ and **exactly 288** having $C = 1/\sqrt{2}$.
- **What is NOT addressed here**:
  1. **Higher dimensions of Open Quantum Problem E28**: While $n = 1$ (tetrahedron states) and $n = 3$ (Hoggar lines) admit $\mathcal{P}_n$-covariant SIC-POVMs saturating $M_\alpha^{\mathrm{SIC}}(2^n)$, E28 asks more generally about characterizing maximal magic states in dimensions where Weyl–Heisenberg SIC-POVMs do not exist (including $n \ge 4$ multi-qubit systems). Determining the exact global maxima for $n \ge 4$ remains open and is **not** formalized here (in the companion Lean 4 repository [`multi-qubit-mub-nonexistence`](https://github.com/LingyeNBird/multi-qubit-mub-nonexistence), Zenodo DOI [`10.5281/zenodo.24566134`](https://doi.org/10.5281/zenodo.24566134), we separately prove that no multi-qubit Pauli-covariant MUB fiducial state exists for any $n \ge 3$, ruling out Liu–Low–Yin's conjectured WH-MUB mechanism for $n \ge 4$).
  2. **Weyl–Heisenberg convention in $d = 4$**: Following multi-qubit quantum information convention, the Weyl–Heisenberg (displacement) group used in `IsPauliMUBFiducial` is the **two-qubit Pauli group** $\mathcal{P}_2 = \{I, X, Y, Z\}^{\otimes 2}$ (not the cyclic $\mathbb{Z}_4$ clock–shift group).

---

## Main Results

Let $|\psi\rangle \in \mathbb{C}^4$ be any normalized pure two-qubit state ($\sum_{i=0}^3 |\psi_i|^2 = 1$), and let $\mathcal{P}_2 = \{I, X, Y, Z\}^{\otimes 2}$ be the 16 two-qubit Pauli matrices. For every Rényi order $\alpha \ge 2$, the Stabilizer Rényi Entropy (SRE)
$$M_\alpha(|\psi\rangle) = \frac{1}{1-\alpha}\ln\!\left(\frac{1}{4}\sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{2\alpha}\right)$$
satisfies the sharp upper bound (`sre_upper_bound_all_alpha`, `pauli_moment_lower_bound_all_alpha`):
$$M_\alpha(|\psi\rangle) \le \frac{1}{1-\alpha}\ln\!\left(\frac{1 + 3 \cdot 4^{1-\alpha}}{4}\right) \;\Longleftrightarrow\; \sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{2\alpha} \ge 1 + 3 \cdot 4^{1-\alpha} \qquad (\forall\, \alpha \ge 2).$$

In particular, for $\alpha = 2$ (`sre2_upper_bound`, `pauli_fourth_moment_lower_bound`):
$$M_2(|\psi\rangle) \le \ln\!\left(\frac{16}{7}\right) \;\Longleftrightarrow\; \sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{4} \ge \frac{7}{4}.$$

Furthermore, for every $\alpha \ge 2$:
1. **Attainment** (`mub_fiducial_attains_moment`, `mub_fiducial_attains_sre`, `mub_fiducial_attains_sre2`): The state $|\psi_{\mathrm{MUB}}\rangle = \frac{1}{2}(1, 1, 1, i)$ achieves exact equality.
2. **Pauli Spectrum & Maximal Commuting Triple** (`maximizer_iff_mub_spectrum`, `maximizer_matching_counts`, `pauli_commute_iff_edgeDisjoint`, `maximizer_zero_paulis_maximal_commuting`): Equality holds iff $|\langle\psi|P|\psi\rangle| \in \{0, \frac{1}{2}\}$ for all non-identity $P \in \mathcal{P}_2$, in which case the 3 vanishing non-identity Paulis form a maximal pairwise-commuting triple (corresponding to a perfect matching in $K_6$) and the other 12 have magnitude $\frac{1}{2}$.
3. **Single Clifford Orbit** (`clifford_lift_b6Plus`, `maximizer_iff_clifford_orbit`, `maximizer_iff_clifford_densityMatrix`): Equality holds iff $|\psi\rangle = \theta U |\psi_{\mathrm{MUB}}\rangle$ for some unit phase $|\theta| = 1$ and some two-qubit Clifford unitary $U$ (`IsClifford2 U`), equivalently $|\psi\rangle\langle\psi| = U |\psi_{\mathrm{MUB}}\rangle\langle\psi_{\mathrm{MUB}}| U^\dagger$.
4. **Exact Cardinality 480** (`maximizer_densityMatrix_ncard_eq_480`): The set of pure-state density matrices $|\psi\rangle\langle\psi|$ of all maximizers is finite and has exact cardinality **480** ($15$ perfect matchings $\times$ $32$ sign/orientation classes).
5. **5-MUB Fiducial Equivalence** (`mubFiducial_isPauliMUBFiducial`, `maximizer_iff_pauli_mub_fiducial`): Equality holds iff $|\psi\rangle$ is a two-qubit Pauli (multi-qubit Weyl–Heisenberg) MUB fiducial state (`IsPauliMUBFiducial ψ`), meaning $\{P|\psi\rangle : P \in \mathcal{P}_2\}$ partitions into 4 orthonormal bases extending to a complete set of $d+1 = 5$ mutually unbiased bases in $\mathbb{C}^4$.
6. **Entanglement (Concurrence) Dichotomy & 192 / 288 Split** (`concurrence_eq_wootters`, `concurrence_sq_eq_linear_entropyA`, `maximizer_concurrence_dichotomy`, `maximizer_not_maximally_entangled_and_not_separable`, `maximizer_concurrence_distribution`): For every maximizer, the Wootters concurrence $C(|\psi\rangle) = 2|\psi_0\psi_3 - \psi_1\psi_2| = |\langle\psi^*|Y\otimes Y|\psi\rangle| = \sqrt{2(1 - \mathrm{Tr}(\rho_A^2))}$ takes only the two values $C \in \{1/2, 1/\sqrt{2}\}$ (so $0 < C < 1$: no maximizer is separable or maximally entangled). Among the 480 maximizer density matrices, **exactly 192** have $C = 1/2$ and **exactly 288** (including $|\psi_{\mathrm{MUB}}\rangle$) have $C = 1/\sqrt{2}$.

*(Note: `sre` uses the natural logarithm `Real.log`. Dividing both sides by $\ln 2$ immediately yields the base-2 convention $\log_2(16/7)$, and the underlying core bound `pauli_moment_lower_bound_all_alpha` is independent of the logarithm base.)*

---

## Proof Architecture

1. **$\mathfrak{su}(4) \cong \mathfrak{so}(6)$ Reduction (`TwoQubitMaximalMagic/SO6Reduction.lean`)**:
   Under the Hodge-real isomorphism $\Lambda^2 \mathbb{C}^4 \cong \mathbb{R}^6$, the 15 signed non-identity Pauli expectations of any normalized state $|\psi\rangle \in \mathbb{C}^4$ form the upper-triangular entries $a = (a_0, \dots, a_{14}) \in \mathbb{R}^{15}$ of a real $6\times 6$ skew-symmetric orthogonal matrix $A = \mathrm{toSkewMat}(a) \in SO(6)$ satisfying:
   - $A^T = -A$,
   - $A^2 = -I_6$ (in particular $\sum_{e=0}^{14} a_e^2 = 3$),
   - Orientation (Pfaffian) condition ($\mathrm{Pf}(A) = +1$): $\Phi(A)_{ij} := \sum_{\sigma \in S_6,\; \sigma(0)=i,\; \sigma(1)=j} \operatorname{sgn}(\sigma) A_{\sigma(2)\sigma(3)} A_{\sigma(4)\sigma(5)} = 8 A_{ij}$.

   The finite determinant-$+1$ signed-permutation group $B_6^+ \subset SO(6)$ (order $6!\cdot 2^5 = 23,040$) acts on $\mathbb{R}^{15}$, preserves `IsSkewOrth6`, and acts transitively (up to sign) on all 15 edges.

2. **Exact Degree-8 Rational SOS Certificate (`TwoQubitMaximalMagic/PolyEngine.lean`, `CertificateData.lean`, `Certificate.lean`)**:
   We exhibit 7 exact integer polynomials $Q_1, \dots, Q_7 \in \mathbb{Z}[a_0, \dots, a_{14}]$ (with $Q_1(a) = 4 a_0^3 - a_0$), strictly positive integer weights $c_1, \dots, c_7 > 0$, common denominator $D = 99306669273543317922264843564$, and 70 ideal cofactor terms $U_0, U_{01}, V_{01}$ for the local generators $h_0, h_{01}, g_{01}$ vanishing on `IsSkewOrth6`, such that the un-symmetrized remainder
   $$F(a) = D\!\left(15 a_0^4 - \frac{3}{4}\right) - \sum_{k=1}^7 c_k Q_k(a)^2 - \big(U_0 h_0 + U_{01} h_{01} + V_{01} g_{01}\big)$$
   has 1,409 nonzero monomials whose $B_6^+$-symmetrization vanishes identically over $\mathbb{Z}[a_0,\dots,a_{14}]$:
   - 274 monomials carry an explicit $g \in B_6^+$ witnessing $g^* m = -m$;
   - 1,135 monomials carry an explicit $g \in B_6^+$ mapping them to 77 canonical orbit representatives whose signed integer sums all cancel to `0`.

   Summing over $B_6^+$ on `IsSkewOrth6 a` yields the exact identity:
   $$D \cdot |B_6^+| \left(\sum_{e=0}^{14} a_e^4 - \frac{3}{4}\right) = \sum_{h \in B_6^+} \sum_{k=1}^7 c_k Q_k(h \cdot a)^2 \ge 0.$$

3. **Extension to All $\alpha \ge 2$ (`TwoQubitMaximalMagic/MainTheorem.lean`)**:
   Setting $y_e = a_e^2 \ge 0$, $\sum y_e = 3$, and $\sum y_e^2 \ge 3/4$, Hölder's inequality with conjugate exponents $p = \alpha - 1$ and $q = \frac{\alpha - 1}{\alpha - 2}$ yields
   $$\left(\frac{3}{4}\right)^{\alpha - 1} \le \left(\sum_{e=0}^{14} y_e^2\right)^{\alpha - 1} \le 3^{\alpha - 2} \sum_{e=0}^{14} y_e^\alpha \implies \sum_{e=0}^{14} |a_e|^{2\alpha} \ge 3 \cdot 4^{1-\alpha}.$$
   Equality at any $\alpha \ge 2$ forces $\sum a_e^4 = 3/4$, hence $Q_1(h\cdot a) = 4(h\cdot a)_0^3 - (h\cdot a)_0 = 0$ for all $h \in B_6^+$, hence $|a_e| \in \{0, 1/2\}$ for all 15 edges, and $(A^2)_{ii} = -1$ forces the 3 zero edges to form a perfect matching of $K_6$.

4. **Complete Maximizer Characterization (`TwoQubitMaximalMagic/Maximizers.lean`)**:
   - Proves two distinct non-identity Paulis commute iff their $K_6$ edges are vertex-disjoint (and anticommute iff they share a vertex), translating the $K_6$ perfect matching into a maximal pairwise-commuting Pauli triple.
   - Proves Pauli tomography $|\psi\rangle\langle\psi| = \frac{1}{4}\sum_{P\in\mathcal{P}_2} \langle\psi|P|\psi\rangle P$, hence pure states agree up to global phase iff they have identical `so6Edge` vectors.
   - Lifts the 5 adjacent $90^\circ$ signed-swap generators of $B_6^+$ to 5 explicit $\pi/2$ Pauli-rotation Clifford unitaries $U_k = \frac{1}{\sqrt{2}}(I + i P_{(k,k+1)}) \in \mathrm{Cl}_2$, proving that every element of $B_6^+$ is realized by a textbook two-qubit Clifford unitary (`IsClifford2`) (equivalently, the induced action of the Clifford group on `so6Edge` surjects onto $B_6^+$).
   - Constructs an explicit algebraic bijection between all maximizers on `IsSkewOrth6` and `Fin 15 × Bool⁵` ($15 \times 32 = 480$), yielding both the single Clifford orbit theorem and `ncard = 480`.
   - Verifies that the 4 Pauli cosets of $\{II, ZI, IZ, ZZ\}$ acting on $|\psi_{\mathrm{MUB}}\rangle$ together with the computational basis form a complete set of 5 MUBs in $\mathbb{C}^4$, and uses Clifford covariance to establish the full equivalence `maximizer_iff_pauli_mub_fiducial`.

5. **Entanglement / Concurrence Dichotomy (`TwoQubitMaximalMagic/Entanglement.lean`)**:
   - Proves the exact identity $C(|\psi\rangle)^2 = 1 - (a_0^2 + a_4^2 + a_8^2) = 1 - (\langle XI\rangle^2 + \langle YI\rangle^2 + \langle ZI\rangle^2) = 2(1 - \mathrm{Tr}(\rho_A^2))$, where edges $\{0, 4, 8\}$ form the triangle $\{0, 1, 5\}$ in $K_6$.
   - Any perfect matching of $K_6$ intersects the triangle $\{0, 1, 5\}$ in either **0** edges (6 bipartite matchings $\implies a_0^2+a_4^2+a_8^2 = 3/4 \implies C = 1/2$, $6 \times 32 = 192$ states) or **1** edge (9 matchings $\implies a_0^2+a_4^2+a_8^2 = 1/2 \implies C = 1/\sqrt{2}$, $9 \times 32 = 288$ states).

---

## Repository Structure

| File | Description |
|---|---|
| `TwoQubitMaximalMagic/Defs.lean` | Transparent, self-contained definitions of `State`, `IsNormalized`, `pauli1`, `pauli2`, `pauliExp`, `pauliMoment`, and `sre` |
| `TwoQubitMaximalMagic/SO6Reduction.lean` | `so6Edge`, `IsSkewOrth6`, `B6Plus`, invariance proofs, and `so6Edge_isSkewOrth6` |
| `TwoQubitMaximalMagic/PolyEngine.lean` | Base-16 packed sparse polynomial engine, pure `List.rec` merge-sort normalizer, computable `B6Wit`, and `sum_B6Plus_evalPoly_eq_zero_of_verify` |
| `TwoQubitMaximalMagic/CertificateData.lean` | Exact integer polynomials `polyQ1..7`, weights `certC1..7`, `certD`, cofactors `polyU0/U01/V01`, and 1,409 `B6Plus` orbit witnesses |
| `TwoQubitMaximalMagic/Certificate.lean` | Pure-kernel `rfl` certificate verification and `so6_fourth_power_bound`, `so6_equality_iff_spectrum`, `so6_equality_matching_counts` |
| `TwoQubitMaximalMagic/MainTheorem.lean` | Sharp bounds for all $\alpha \ge 2$, attainment by `mubFiducial`, and Pauli-spectrum criterion |
| `TwoQubitMaximalMagic/Maximizers.lean` | Maximal commuting Pauli triple, Pauli tomography, `IsClifford2` realization of $B_6^+$, single Clifford orbit, exact cardinality `480`, and 5-MUB fiducial equivalence |
| `TwoQubitMaximalMagic/Entanglement.lean` | Wootters concurrence, reduced density matrices, strict $C \in \{1/2, 1/\sqrt{2}\}$ dichotomy, no maximally entangled / separable maximizers, and exact `192 / 288` split |
| `TwoQubitMaximalMagic.lean` | Root library export |
| `Audit.lean` | Standalone `#check` and `#print axioms` audit script (32 audited declarations) |
| `scripts/exact_certificate.json` | Machine-readable exact integer SOS certificate ($D, c_k, Q_k$, cofactors, and 1,409 $B_6^+$ witnesses) |
| `scripts/verify_certificate.py` | Standalone zero-dependency Python verifier (`< 1 s`, checks direct $B_6^+$ symmetrization and all 1,409 witnesses without Lean) |
| `scripts/extract_int_cert.cpp`, `verify_exact_Q.py`, `compute_cofactors.py`, `build_witness_table.py`, `gen_lean_cert.py` | Complete 5-stage reproducible discovery pipeline reproducing `exact_certificate.json` and `CertificateData.lean` byte-for-byte |
| `paper/main.tex`, `paper/references.bib`, `paper/main.pdf` | Full manuscript source, bibliography, and compiled PDF |
| `.github/workflows/lean_ci.yml` | Automated GitHub Actions CI compiling the full proof and checking `Audit.lean` axioms |

---

## How to Verify Independently

### Option A: Standalone Python Check of the Exact SOS Certificate (No Lean Required, `< 1 s`)

Requires only Python 3 standard library:

```bash
python3 scripts/verify_certificate.py
```

To also reproduce the entire certificate discovery from scratch (requires `g++` with C++17 and Python 3):

```bash
cd scripts
g++ -O3 -std=c++17 extract_int_cert.cpp -o extract_int_cert
./extract_int_cert cert_polys.txt
python3 verify_exact_Q.py
python3 build_witness_table.py   # imports and runs compute_cofactors.py automatically
python3 gen_lean_cert.py --check
```

### Option B: Full End-to-End Lean 4 Pure-Kernel Verification

Requirements: [elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager; installs `leanprover/lean4:v4.36.0` automatically from `lean-toolchain`). You can also inspect automated public build and axiom-audit logs directly in the **Actions** tab of this repository.

```bash
git clone https://github.com/LingyeNBird/two-qubit-maximal-magic.git
cd two-qubit-maximal-magic
lake exe cache get
lake build
lake env lean Audit.lean
```

### Reviewer Audit Checklist
1. **Audit the definitions**:
   - Core SRE definitions in `TwoQubitMaximalMagic/Defs.lean`: `State`, `normSq`, `IsNormalized`, `pauli1`, `pauli2`, `pauliExp`, `pauliMoment`, `sre`.
   - Maximizer definitions in `TwoQubitMaximalMagic/Maximizers.lean`: `densityMatrix`, `IsClifford2`, `innerState`, `IsCompleteMUB`, `IsPauliMUBFiducial`.
   - Entanglement definitions in `TwoQubitMaximalMagic/Entanglement.lean`: `concurrence`, `reducedDensityA`, `reducedDensityB`.
2. **Verify zero shortcuts** (output should contain only doc comments):
   ```bash
   grep -rnE '\b(sorry|axiom|native_decide|unsafe|implemented_by|extern)\b' TwoQubitMaximalMagic.lean TwoQubitMaximalMagic/
   ```
3. **Verify axioms** via `lake env lean Audit.lean`: every one of the 32 printed theorems must depend **only** on `[propext, Classical.choice, Quot.sound]`.

---

## Author & AI Transparency Statement

- **Author**: Zhaoting Ye (Independent Researcher; ORCID: [0009-0006-8457-0482](https://orcid.org/0009-0006-8457-0482); Email: `lingyenbird@qq.com`)
- **Archival DOI (Zenodo)**: [`10.5281/zenodo.24565157`](https://doi.org/10.5281/zenodo.24565157) (all versions) / [`10.5281/zenodo.24565158`](https://doi.org/10.5281/zenodo.24565158) (`v1.1`)
- **AI Assistance & Independent Verification**: In the interest of full transparency, the bulk of the technical work in this repository—including mathematical proof discovery, construction of the SOS optimization and certificate-extraction pipeline, Lean 4 formalization, and manuscript drafting—was carried out using AI systems under the author's problem selection, direction, and oversight. The mathematical validity of every result does not rely on trusting any AI system or human check: the algebraic SOS identity is independently verified in exact integer arithmetic by `scripts/verify_certificate.py` (`< 1 s`), and all 32 audited declarations are machine-checked end-to-end inside Lean 4's pure kernel (`Audit.lean`, zero `sorry`, zero `native_decide`, standard foundational axioms only).

---

## References

- Q. Liu, I. Low, Z. Yin, *"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035 (2026), [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550).
- Open Quantum Problems, Problem E28 (two-qubit subproblem): [https://openquantumproblems.com/p/E28](https://openquantumproblems.com/p/E28).
- L. Leone, S. F. E. Oliviero, A. Hamma, *"Stabilizer Rényi Entropy"*, *Phys. Rev. Lett.* **128**, 050402 (2022).
- W. K. Wootters, *"Entanglement of Formation of an Arbitrary State of Two Qubits"*, *Phys. Rev. Lett.* **80**, 2245 (1998).
