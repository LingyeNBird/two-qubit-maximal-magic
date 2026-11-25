# Formal Proof of the Two-Qubit Maximal Magic Conjecture (Two-Qubit Case of Open Quantum Problem E28)

[![Lean 4 CI](https://github.com/LingyeNBird/two-qubit-maximal-magic/actions/workflows/lean_ci.yml/badge.svg)](https://github.com/LingyeNBird/two-qubit-maximal-magic/actions/workflows/lean_ci.yml)

A complete, pure-kernel **Lean 4** (`v4.36.0` + Mathlib4) proof of the **two-qubit ($n = 2$) maximal magic conjecture** of Q. Liu, I. Low, and Z. Yin (*"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035, 2026; [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550)), which resolves the two-qubit $\max M_2 = \ln(16/7)$ subproblem of [Open Quantum Problem E28](https://openquantumproblems.com/p/E28) and extends it to all Rényi orders $\alpha \ge 2$, together with a complete formal characterization of all **480** maximal-magic states.

- **Zero `sorry`**
- **Zero `native_decide`** (all polynomial normalizations, multiplications, and 1,409 group-orbit witnesses are verified inside Lean 4's pure kernel by definitional equality `rfl`)
- **Standard axioms only**: all 24 audited theorems depend solely on `[propext, Classical.choice, Quot.sound]`

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
- **What is NOT addressed here**:
  1. **Higher dimensions of Open Quantum Problem E28**: E28 asks more generally about characterizing maximal magic states in dimensions where Weyl–Heisenberg SIC-POVMs do not exist (including $n \ge 4$ multi-qubit systems), and Liu–Low–Yin also conjecture a generalization for $n$-qubit states ($n \neq 1, 3$). Those higher-dimensional cases ($n \ge 3$) remain open and are **not** formalized here.
  2. **Entanglement / concurrence distribution**: The auxiliary observation in Liu–Low–Yin that the concurrence of the 480 maximizers takes values in $\{1/2, 1/\sqrt{2}\}$ is not currently formalized.
  3. **Weyl–Heisenberg convention in $d = 4$**: Following multi-qubit quantum information convention, the Weyl–Heisenberg (displacement) group used in `IsPauliMUBFiducial` is the **two-qubit Pauli group** $\mathcal{P}_2 = \{I, X, Y, Z\}^{\otimes 2}$ (not the cyclic $\mathbb{Z}_4$ clock–shift group).

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

*(Note: `sre` uses the natural logarithm `Real.log`. Dividing both sides by $\ln 2$ immediately yields the base-2 convention $\log_2(16/7)$, and the underlying core bound `pauli_moment_lower_bound_all_alpha` is independent of the logarithm base.)*

---

## Proof Architecture

1. **$\mathfrak{su}(4) \cong \mathfrak{so}(6)$ Reduction (`TwoQubitMaximalMagic/SO6Reduction.lean`)**:
   Under the Hodge-real isomorphism $\Lambda^2 \mathbb{C}^4 \cong \mathbb{R}^6$, the 15 signed non-identity Pauli expectations of any normalized state $|\psi\rangle \in \mathbb{C}^4$ form the upper-triangular entries $a = (a_0, \dots, a_{14}) \in \mathbb{R}^{15}$ of a real $6\times 6$ skew-symmetric orthogonal matrix $A = \mathrm{toSkewMat}(a) \in SO(6)$ satisfying:
   - $A^T = -A$,
   - $A^2 = -I_6$ (in particular $\sum_{e=0}^{14} a_e^2 = 3$),
   - Hodge self-duality ($\mathrm{Pf}(A) = +1$): $\Phi(A)_{ij} := \sum_{\sigma \in S_6,\; \sigma(0)=i,\; \sigma(1)=j} \operatorname{sgn}(\sigma) A_{\sigma(2)\sigma(3)} A_{\sigma(4)\sigma(5)} = 8 A_{ij}$.

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
   - Lifts the 5 adjacent $90^\circ$ signed-swap generators of $B_6^+$ to 5 explicit $\pi/2$ Pauli-rotation Clifford unitaries $U_k = \frac{1}{\sqrt{2}}(I + i P_{(k,k+1)}) \in \mathrm{Cl}_2$, proving that all of $B_6^+$ lifts surjectively into the textbook two-qubit Clifford group (`IsClifford2`).
   - Constructs an explicit algebraic bijection between all maximizers on `IsSkewOrth6` and `Fin 15 × Bool⁵` ($15 \times 32 = 480$), yielding both the single Clifford orbit theorem and `ncard = 480`.
   - Verifies that the 4 Pauli cosets of $\{II, ZI, IZ, ZZ\}$ acting on $|\psi_{\mathrm{MUB}}\rangle$ together with the computational basis form a complete set of 5 MUBs in $\mathbb{C}^4$, and uses Clifford covariance to establish the full equivalence `maximizer_iff_pauli_mub_fiducial`.

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
| `TwoQubitMaximalMagic/Maximizers.lean` | Maximal commuting Pauli triple, Pauli tomography, `IsClifford2` lift of $B_6^+$, single Clifford orbit, exact cardinality `480`, and 5-MUB fiducial equivalence |
| `TwoQubitMaximalMagic.lean` | Root library export |
| `Audit.lean` | Standalone `#check` and `#print axioms` audit script (24 theorems) |
| `.github/workflows/lean_ci.yml` | Automated GitHub Actions CI compiling the full proof and checking `Audit.lean` axioms |

---

## How to Verify Independently

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
2. **Verify zero shortcuts** (output should contain only doc comments):
   ```bash
   grep -rnE '\b(sorry|axiom|native_decide|unsafe|implemented_by|extern)\b' TwoQubitMaximalMagic.lean TwoQubitMaximalMagic/
   ```
3. **Verify axioms** via `lake env lean Audit.lean`: every one of the 24 printed theorems must depend **only** on `[propext, Classical.choice, Quot.sound]`.

---

## References

- Q. Liu, I. Low, Z. Yin, *"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035 (2026), [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550).
- Open Quantum Problems, Problem E28 (two-qubit subproblem): [https://openquantumproblems.com/p/E28](https://openquantumproblems.com/p/E28).
- L. Leone, S. F. E. Oliviero, A. Hamma, *"Stabilizer Rényi Entropy"*, *Phys. Rev. Lett.* **128**, 050402 (2022).
