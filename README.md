# Formal Proof of the Two-Qubit Maximal Magic Conjecture (Open Quantum Problem E28)

A complete, pure-kernel **Lean 4** (`v4.36.0` + Mathlib4) proof of the **Two-Qubit Maximal Magic Conjecture** ([Open Quantum Problem E28](https://openquantumproblems.com/p/E28)), conjectured by Q. Liu, I. Low, and Z. Yin in *"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035 (2026), [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550).

- **Zero `sorry`**
- **Zero `native_decide`** (all polynomial normalizations, multiplications, and 1,409 group-orbit witnesses are verified inside Lean 4's pure kernel by definitional equality `rfl`)
- **Standard axioms only**: every main theorem depends solely on `[propext, Classical.choice, Quot.sound]`

---

## Main Result

Let $|\psi\rangle \in \mathbb{C}^4$ be any normalized pure two-qubit state ($\sum_{i=0}^3 |\psi_i|^2 = 1$), and let $\mathcal{P}_2 = \{I, X, Y, Z\}^{\otimes 2}$ be the 16 two-qubit Pauli matrices. For every Rényi order $\alpha \ge 2$, the Stabilizer Rényi Entropy (SRE)
$$M_\alpha(|\psi\rangle) = \frac{1}{1-\alpha}\ln\!\left(\frac{1}{4}\sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{2\alpha}\right)$$
satisfies the sharp upper bound:
$$M_\alpha(|\psi\rangle) \le \frac{1}{1-\alpha}\ln\!\left(\frac{1 + 3 \cdot 4^{1-\alpha}}{4}\right) \qquad (\forall\, \alpha \ge 2),$$
equivalently
$$\sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{2\alpha} \ge 1 + 3 \cdot 4^{1-\alpha}.$$

In particular, for $\alpha = 2$:
$$M_2(|\psi\rangle) \le \ln\!\left(\frac{16}{7}\right) \;\Longleftrightarrow\; \sum_{P \in \mathcal{P}_2} |\langle\psi|P|\psi\rangle|^{4} \ge \frac{7}{4}.$$

Furthermore:
1. **Attainment**: The Weyl–Heisenberg MUB fiducial state $|\psi_{\mathrm{MUB}}\rangle = \frac{1}{2}(1, 1, 1, i)$ achieves exact equality for all $\alpha \ge 2$.
2. **Complete Characterization of Maximizers**: For any $\alpha \ge 2$, equality holds **if and only if** every non-identity Pauli expectation satisfies $|\langle\psi|P|\psi\rangle| \in \{0, \frac{1}{2}\}$, in which case **exactly 3** non-identity Pauli expectations vanish (forming a perfect matching in $K_6$, i.e., a maximal commuting Pauli triple) and **exactly 12** have magnitude $\frac{1}{2}$.

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

3. **Extension to All $\alpha \ge 2$ & Uniqueness (`TwoQubitMaximalMagic/MainTheorem.lean`)**:
   Setting $y_e = a_e^2 \ge 0$, $\sum y_e = 3$, and $\sum y_e^2 \ge 3/4$, Hölder's inequality with conjugate exponents $p = \alpha - 1$ and $q = \frac{\alpha - 1}{\alpha - 2}$ yields
   $$\left(\frac{3}{4}\right)^{\alpha - 1} \le \left(\sum_{e=0}^{14} y_e^2\right)^{\alpha - 1} \le 3^{\alpha - 2} \sum_{e=0}^{14} y_e^\alpha \implies \sum_{e=0}^{14} |a_e|^{2\alpha} \ge 3 \cdot 4^{1-\alpha}.$$
   Equality at any $\alpha \ge 2$ forces $\sum a_e^4 = 3/4$, hence $Q_1(h\cdot a) = 4(h\cdot a)_0^3 - (h\cdot a)_0 = 0$ for all $h \in B_6^+$, hence $|a_e| \in \{0, 1/2\}$ for all 15 edges, and $(A^2)_{ii} = -1$ forces every vertex of $K_6$ to have degree 1 in the zero-edge subgraph (3 vanishing edges forming a perfect matching and 12 edges of magnitude $1/2$).

---

## Repository Structure

| File | Description |
|---|---|
| `TwoQubitMaximalMagic/Defs.lean` | Transparent, self-contained definitions of `State`, `IsNormalized`, `pauli1`, `pauli2`, `pauliExp`, `pauliMoment`, and `sre` (~25 lines of core definitions for easy auditing) |
| `TwoQubitMaximalMagic/SO6Reduction.lean` | `so6Edge`, `IsSkewOrth6`, `B6Plus`, invariance proofs, and `so6Edge_isSkewOrth6` |
| `TwoQubitMaximalMagic/PolyEngine.lean` | Base-16 packed sparse polynomial engine, pure `List.rec` merge-sort normalizer, computable `B6Wit`, and `sum_B6Plus_evalPoly_eq_zero_of_verify` |
| `TwoQubitMaximalMagic/CertificateData.lean` | Exact integer polynomials `polyQ1..7`, weights `certC1..7`, `certD`, cofactors `polyU0/U01/V01`, and 1,409 `B6Plus` orbit witnesses |
| `TwoQubitMaximalMagic/Certificate.lean` | Pure-kernel `rfl` certificate verification and `so6_fourth_power_bound`, `so6_equality_iff_spectrum`, `so6_equality_matching_counts` |
| `TwoQubitMaximalMagic/MainTheorem.lean` | Main theorems for all $\alpha \ge 2$, MUB fiducial attainment, and maximizer characterization |
| `TwoQubitMaximalMagic.lean` | Root library export |
| `Audit.lean` | Standalone `#check` and `#print axioms` audit script |

---

## How to Verify Independently

Requirements: [elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager; installs `leanprover/lean4:v4.36.0` automatically from `lean-toolchain`).

```bash
git clone https://github.com/LingyeNBird/two-qubit-maximal-magic.git
cd two-qubit-maximal-magic
lake exe cache get
lake build
lake env lean Audit.lean
```

### Reviewer Audit Checklist
1. **Audit the definitions**: Read the ~25 lines of core definitions in `TwoQubitMaximalMagic/Defs.lean` (`State`, `normSq`, `IsNormalized`, `pauli1`, `pauli2`, `pauliExp`, `pauliMoment`, `sre`).
2. **Verify zero shortcuts** (output should contain only doc comments):
   ```bash
   grep -rnE '\b(sorry|axiom|native_decide|unsafe|implemented_by|extern)\b' TwoQubitMaximalMagic.lean TwoQubitMaximalMagic/
   ```
3. **Verify axioms** via `lake env lean Audit.lean`. Expected output:
   ```text
   'TwoQubitMaximalMagic.so6_fourth_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.so6_equality_iff_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.so6_equality_matching_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.pauli_fourth_moment_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.sre2_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.pauli_moment_lower_bound_all_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.sre_upper_bound_all_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.mub_fiducial_attains_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.mub_fiducial_attains_sre' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.mub_fiducial_attains_sre2' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.maximizer_iff_mub_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'TwoQubitMaximalMagic.maximizer_matching_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

---

## References

- Q. Liu, I. Low, Z. Yin, *"Maximal Magic for Two-qubit States"*, *Quantum Sci. Technol.* **11**, 015035 (2026), [`arXiv:2502.17550`](https://arxiv.org/abs/2502.17550).
- Open Quantum Problems, Problem E28: [https://openquantumproblems.com/p/E28](https://openquantumproblems.com/p/E28).
- L. Leone, S. F. E. Oliviero, A. Hamma, *"Stabilizer Rényi Entropy"*, *Phys. Rev. Lett.* **128**, 050402 (2022).
