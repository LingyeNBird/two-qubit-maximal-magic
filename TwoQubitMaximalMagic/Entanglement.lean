import TwoQubitMaximalMagic.Maximizers
import Mathlib.Tactic

open scoped Matrix

/-!
# Entanglement (Concurrence) of All 480 Two-Qubit Maximal Magic States

This file formalizes the entanglement-magic interplay discovered by Liu, Low, and Yin
(*Quantum Sci. Technol.* **11**, 015035, 2026; `arXiv:2502.17550`) for all two-qubit maximal
magic states (for every Rényi order `α ≥ 2`):

1. **Textbook definitions & equivalence** (`concurrence`, `reducedDensityA`, `reducedDensityB`,
   `concurrence_eq_wootters`, `concurrence_sq_eq_one_sub_localA`,
   `concurrence_sq_eq_one_sub_localB`, `concurrence_sq_eq_linear_entropyA`):
   We define the pure-state concurrence `C(|ψ⟩) = 2 |ψ₀ ψ₃ - ψ₁ ψ₂|` and prove its exact
   equivalence with Wootters' spin-flip formula `|⟨ψ^* | Y ⊗ Y | ψ⟩|`, the local Bloch vector
   length `1 - (⟨XI⟩² + ⟨YI⟩² + ⟨ZI⟩²)`, and the reduced-state linear entropy
   `2 (1 - Tr(ρ_A²))`.

2. **Strict dichotomy `C(|ψ⟩) ∈ {1/2, 1/√2}`** (`maximizer_concurrence_dichotomy`,
   `maximizer_not_maximally_entangled_and_not_separable`):
   Because the local qubit-A Pauli operators `{ZI, XI, YI}` correspond to the triangle
   `{0, 1, 5}` in `K₆` (edges `0, 4, 8`), any perfect matching of `K₆` contains either `0` or
   `1` edge of this triangle. Hence every maximal-magic pure two-qubit state satisfies
   `C(|ψ⟩) = 1/2` or `C(|ψ⟩) = 1/√2`; in particular, **no** maximally magical two-qubit state
   is maximally entangled (`C < 1`) or separable (`0 < C`).

3. **Exact 192 / 288 distribution among the 480 maximizers**
   (`mubFiducial_concurrence`, `maximizer_concurrence_distribution`):
   Among the 480 maximizer pure-state density matrices, **exactly 192** (`6` bipartite matchings
   × `32`) have `C(|ψ⟩) = 1/2`, and **exactly 288** (`9` triangle-hitting matchings × `32`,
   including `mubFiducial`) have `C(|ψ⟩) = 1/√2`.
-/

namespace TwoQubitMaximalMagic

/-! ### Part 1: Pure-State Concurrence and Reduced Density Matrices -/

/-- Wootters concurrence of a pure two-qubit state `|ψ⟩ ∈ ℂ⁴`:
    `C(|ψ⟩) = 2 |ψ₀ ψ₃ - ψ₁ ψ₂|`. -/
noncomputable def concurrence (ψ : State) : ℝ :=
  2 * ‖ψ 0 * ψ 3 - ψ 1 * ψ 2‖

/-- Single-qubit reduced density matrix on qubit A: `ρ_A = Tr_B(|ψ⟩⟨ψ|)`. -/
def reducedDensityA (ψ : State) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r c => ∑ b : Fin 2, ψ ⟨2 * r.val + b.val, by omega⟩ * star (ψ ⟨2 * c.val + b.val, by omega⟩)

/-- Single-qubit reduced density matrix on qubit B: `ρ_B = Tr_A(|ψ⟩⟨ψ|)`. -/
def reducedDensityB (ψ : State) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r c => ∑ a : Fin 2, ψ ⟨2 * a.val + r.val, by omega⟩ * star (ψ ⟨2 * a.val + c.val, by omega⟩)

lemma concurrence_nonneg (ψ : State) : 0 ≤ concurrence ψ := by
  unfold concurrence
  positivity

/-- Equivalence with Wootters' spin-flip formula `C(|ψ⟩) = |⟨ψ^* | (Y ⊗ Y) | ψ⟩|`. -/
theorem concurrence_eq_wootters (ψ : State) :
    concurrence ψ = ‖∑ i : Fin 4, ∑ j : Fin 4, ψ i * pauli2 2 2 i j * ψ j‖ := by
  have hsum :
      ∑ i : Fin 4, ∑ j : Fin 4, ψ i * pauli2 2 2 i j * ψ j =
        -(2 : ℂ) * (ψ 0 * ψ 3 - ψ 1 * ψ 2) := by
    simp only [Fin.sum_univ_four, pauli2, pauli1]
    simp
    ring
  rw [hsum, norm_mul, norm_neg, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  rfl

/-- Algebraic expansion of `C(|ψ⟩)²` in real and imaginary coordinates. -/
private lemma concurrence_sq_re_im (ψ : State) :
    concurrence ψ ^ 2 =
      4 * (((ψ 0).re * (ψ 3).re - (ψ 0).im * (ψ 3).im -
            ((ψ 1).re * (ψ 2).re - (ψ 1).im * (ψ 2).im)) ^ 2 +
           ((ψ 0).re * (ψ 3).im + (ψ 0).im * (ψ 3).re -
            ((ψ 1).re * (ψ 2).im + (ψ 1).im * (ψ 2).re)) ^ 2) := by
  unfold concurrence
  rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- Core `SO(6)` triangle identity: for any normalized two-qubit state `|ψ⟩`,
    `C(|ψ⟩)² = 1 - (a₀² + a₄² + a₈²)`, where `{0, 4, 8}` are the edges of the triangle
    `{0, 1, 5}` in `K₆` corresponding to `{ZI, XI, YI}`. -/
theorem concurrence_sq_eq_one_sub_so6_triangleA {ψ : State} (hψ : IsNormalized ψ) :
    concurrence ψ ^ 2 = 1 - (so6Edge ψ 0 ^ 2 + so6Edge ψ 4 ^ 2 + so6Edge ψ 8 ^ 2) := by
  have hnorm : (ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2 = 1 := by
    rw [← normSq_eq_sum_re_im]; exact hψ
  have hnorm2 : ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2) ^ 2 = 1 := by
    rw [hnorm]; ring
  rw [concurrence_sq_re_im, ← hnorm2]
  change _ = _ - (pauliExpRe ψ 3 0 ^ 2 + pauliExpRe ψ 1 0 ^ 2 + (-pauliExpRe ψ 2 0) ^ 2)
  rw [pauliExpRe_ZI, pauliExpRe_XI, pauliExpRe_YI]
  ring

/-- Local Bloch length formula on qubit A: `C(|ψ⟩)² = 1 - (⟨XI⟩² + ⟨YI⟩² + ⟨ZI⟩²)`. -/
theorem concurrence_sq_eq_one_sub_localA {ψ : State} (hψ : IsNormalized ψ) :
    concurrence ψ ^ 2 =
      1 - (‖pauliExp ψ 1 0‖ ^ 2 + ‖pauliExp ψ 2 0‖ ^ 2 + ‖pauliExp ψ 3 0‖ ^ 2) := by
  rw [concurrence_sq_eq_one_sub_so6_triangleA hψ, norm_pauliExp_sq, norm_pauliExp_sq,
    norm_pauliExp_sq]
  change 1 - (pauliExpRe ψ 3 0 ^ 2 + pauliExpRe ψ 1 0 ^ 2 + (-pauliExpRe ψ 2 0) ^ 2) = _
  ring

/-- Local Bloch length formula on qubit B: `C(|ψ⟩)² = 1 - (⟨IX⟩² + ⟨IY⟩² + ⟨IZ⟩²)`. -/
theorem concurrence_sq_eq_one_sub_localB {ψ : State} (hψ : IsNormalized ψ) :
    concurrence ψ ^ 2 =
      1 - (‖pauliExp ψ 0 1‖ ^ 2 + ‖pauliExp ψ 0 2‖ ^ 2 + ‖pauliExp ψ 0 3‖ ^ 2) := by
  have hnorm : (ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2 = 1 := by
    rw [← normSq_eq_sum_re_im]; exact hψ
  have hnorm2 : ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2) ^ 2 = 1 := by
    rw [hnorm]; ring
  rw [concurrence_sq_re_im, ← hnorm2, norm_pauliExp_sq, norm_pauliExp_sq, norm_pauliExp_sq,
    pauliExpRe_IX, pauliExpRe_IY, pauliExpRe_IZ]
  ring

/-- Linear-entropy purity formula: `C(|ψ⟩)² = 2 (1 - Tr(ρ_A²))`. -/
theorem concurrence_sq_eq_linear_entropyA {ψ : State} (hψ : IsNormalized ψ) :
    concurrence ψ ^ 2 = 2 * (1 - (Matrix.trace (reducedDensityA ψ * reducedDensityA ψ)).re) := by
  have hnorm : (ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2 = 1 := by
    rw [← normSq_eq_sum_re_im]; exact hψ
  have hnorm2 : ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2) ^ 2 = 1 := by
    rw [hnorm]; ring
  have h00 : reducedDensityA ψ 0 0 = ψ 0 * star (ψ 0) + ψ 1 * star (ψ 1) := by
    simp [reducedDensityA, Fin.sum_univ_two]
  have h01 : reducedDensityA ψ 0 1 = ψ 0 * star (ψ 2) + ψ 1 * star (ψ 3) := by
    simp [reducedDensityA, Fin.sum_univ_two]
  have h10 : reducedDensityA ψ 1 0 = ψ 2 * star (ψ 0) + ψ 3 * star (ψ 1) := by
    simp [reducedDensityA, Fin.sum_univ_two]
  have h11 : reducedDensityA ψ 1 1 = ψ 2 * star (ψ 2) + ψ 3 * star (ψ 3) := by
    simp [reducedDensityA, Fin.sum_univ_two]
  rw [concurrence_sq_re_im, ← hnorm2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    h00, h01, h10, h11, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private lemma inv_sqrt2_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

/-- Concurrence of any normalized pure two-qubit state lies in `[0, 1]`. -/
theorem concurrence_le_one {ψ : State} (hψ : IsNormalized ψ) : concurrence ψ ≤ 1 := by
  have hsq : concurrence ψ ^ 2 ≤ 1 := by
    rw [concurrence_sq_eq_one_sub_so6_triangleA hψ]
    nlinarith [sq_nonneg (so6Edge ψ 0), sq_nonneg (so6Edge ψ 4), sq_nonneg (so6Edge ψ 8)]
  nlinarith [concurrence_nonneg ψ]

/-- Pure states with the same density matrix have the same concurrence. -/
lemma concurrence_eq_of_densityMatrix_eq {ψ φ : State} (hψ : IsNormalized ψ) (hφ : IsNormalized φ)
    (hρ : densityMatrix ψ = densityMatrix φ) : concurrence ψ = concurrence φ := by
  have hso6 := (densityMatrix_eq_iff_so6Edge_eq hψ hφ).mp hρ
  have hsq : concurrence ψ ^ 2 = concurrence φ ^ 2 := by
    rw [concurrence_sq_eq_one_sub_so6_triangleA hψ, concurrence_sq_eq_one_sub_so6_triangleA hφ, hso6]
  nlinarith [concurrence_nonneg ψ, concurrence_nonneg φ]

/-- The explicit MUB fiducial state `|ψ_MUB⟩ = (1/2, 1/2, 1/2, i/2)` has concurrence `1 / √2`. -/
theorem mubFiducial_concurrence : concurrence mubFiducial = 1 / Real.sqrt 2 := by
  have hsq : concurrence mubFiducial ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
    rw [concurrence_sq_eq_one_sub_so6_triangleA mubFiducial_normalized, inv_sqrt2_sq]
    rcases mubFiducial_so6_values with ⟨h0, _, _, _, h4, _, _, _, h8, _, _, _, _, _, _⟩
    rw [h0, h4, h8]
    norm_num
  have hpos : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  nlinarith [concurrence_nonneg mubFiducial]

/-! ### Part 2: Strict Dichotomy `C(|ψ⟩) ∈ {1/2, 1/√2}` for All Maximizers -/

/-- **Concurrence Dichotomy for Maximal Magic States**:
    Every normalized pure two-qubit state `ψ` maximizing `M_α` (for any `α ≥ 2`) has concurrence
    strictly equal to either `1 / 2` or `1 / √2`. -/
theorem maximizer_concurrence_dichotomy {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α)
    (hmax : sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4)) :
    concurrence ψ = 1 / 2 ∨ concurrence ψ = 1 / Real.sqrt 2 := by
  have hspec_p := (maximizer_iff_mub_spectrum hψ hα).mp hmax
  have hdeg1 := (maximizer_matching_counts hψ hα hmax).2.2
  -- Helper: each edge `e ∈ {0, 4, 8}` satisfies `so6Edge ψ e = 0` or `so6Edge ψ e ^ 2 = 1 / 4`
  have hsq_cases : ∀ e : Fin 15, so6Edge ψ e = 0 ∨ so6Edge ψ e ^ 2 = 1 / 4 := by
    intro e
    have hp := hspec_p (edgePauliLabel e).1 (edgePauliLabel e).2 (edgePauliLabel_ne_zero e)
    rw [so6Edge_eq_pauliExpRe]
    have hs : (edgePauliSign e : ℝ) ^ 2 = 1 := by fin_cases e <;> simp [edgePauliSign]
    rcases hp with h0 | hh
    · left
      rw [norm_pauliExp, abs_eq_zero] at h0
      rw [h0, mul_zero]
    · right
      rw [mul_pow, hs, one_mul, ← norm_pauliExp_sq, hh]
      norm_num
  -- Helper: unique zero-neighbor at any vertex `u` forbids two distinct incident zero edges
  have hno_pair : ∀ u v w : Fin 6, v ≠ u → w ≠ u → v ≠ w →
      toSkewMat (so6Edge ψ) u v = 0 → toSkewMat (so6Edge ψ) u w = 0 → False := by
    intro u v w hvu hwu hvw huv huw
    rcases Finset.card_eq_one.mp (hdeg1 u) with ⟨x, hx⟩
    have hv : v ∈ Finset.univ.filter (fun j : Fin 6 => j ≠ u ∧ toSkewMat (so6Edge ψ) u j = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, huv⟩
    have hw : w ∈ Finset.univ.filter (fun j : Fin 6 => j ≠ u ∧ toSkewMat (so6Edge ψ) u j = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwu, huw⟩
    rw [hx, Finset.mem_singleton] at hv hw
    exact hvw (hv.trans hw.symm)
  -- The 3 edges `0 = (0,1)`, `4 = (0,5)`, `8 = (1,5)` form a triangle on `{0, 1, 5}`,
  -- so no two of them can both vanish!
  have h04 : ¬ (so6Edge ψ 0 = 0 ∧ so6Edge ψ 4 = 0) := by
    rintro ⟨h0, h4⟩
    exact hno_pair 0 1 5 (by decide) (by decide) (by decide)
      (by simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 0).trans h0)
      (by simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 4).trans h4)
  have h08 : ¬ (so6Edge ψ 0 = 0 ∧ so6Edge ψ 8 = 0) := by
    rintro ⟨h0, h8⟩
    have h10 : toSkewMat (so6Edge ψ) 1 0 = 0 := by
      rw [toSkewMat_swap]
      have h01 : toSkewMat (so6Edge ψ) 0 1 = 0 := by
        simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 0).trans h0
      rw [h01, neg_zero]
    exact hno_pair 1 0 5 (by decide) (by decide) (by decide) h10
      (by simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 8).trans h8)
  have h48 : ¬ (so6Edge ψ 4 = 0 ∧ so6Edge ψ 8 = 0) := by
    rintro ⟨h4, h8⟩
    have h50 : toSkewMat (so6Edge ψ) 5 0 = 0 := by
      rw [toSkewMat_swap]
      have h05 : toSkewMat (so6Edge ψ) 0 5 = 0 := by
        simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 4).trans h4
      rw [h05, neg_zero]
    have h51 : toSkewMat (so6Edge ψ) 5 1 = 0 := by
      rw [toSkewMat_swap]
      have h15 : toSkewMat (so6Edge ψ) 1 5 = 0 := by
        simpa [edgePairs] using (toSkewMat_edge (so6Edge ψ) 8).trans h8
      rw [h15, neg_zero]
    exact hno_pair 5 0 1 (by decide) (by decide) (by decide) h50 h51
  have hcsq := concurrence_sq_eq_one_sub_so6_triangleA hψ
  have hnn := concurrence_nonneg ψ
  have hsqrt2 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := inv_sqrt2_sq
  have hsqrt2_nn : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  rcases hsq_cases 0 with hz0 | hs0 <;>
    rcases hsq_cases 4 with hz4 | hs4 <;>
    rcases hsq_cases 8 with hz8 | hs8
  · exact absurd ⟨hz0, hz4⟩ h04
  · exact absurd ⟨hz0, hz4⟩ h04
  · exact absurd ⟨hz0, hz8⟩ h08
  · right
    rw [hz0, hs4, hs8] at hcsq
    nlinarith
  · exact absurd ⟨hz4, hz8⟩ h48
  · right
    rw [hs0, hz4, hs8] at hcsq
    nlinarith
  · right
    rw [hs0, hs4, hz8] at hcsq
    nlinarith
  · left
    rw [hs0, hs4, hs8] at hcsq
    nlinarith

/-- No maximally magical two-qubit pure state is separable (`C = 0`) or maximally entangled (`C = 1`). -/
theorem maximizer_not_maximally_entangled_and_not_separable {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α)
    (hmax : sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4)) :
    0 < concurrence ψ ∧ concurrence ψ < 1 := by
  rcases maximizer_concurrence_dichotomy hψ hα hmax with h1 | h2
  · rw [h1]; norm_num
  · rw [h2]
    have hgt1 : (1 : ℝ) < Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr hgt1

/-! ### Part 3: Exact 192 / 288 Distribution Among the 480 Maximizers -/

/-- The 6 bipartite matchings between `{0, 1, 5}` and `{2, 3, 4}` (zero edges inside triangle
    `{0, 1, 5}`), corresponding to maximizers with `C(|ψ⟩) = 1 / 2`. -/
def isHalfMatching (m : Fin 15) : Bool :=
  m == 3 || m == 4 || m == 6 || m == 7 || m == 9 || m == 10

private lemma isHalfMatching_iff_no_triangleA_zero (m : Fin 15) :
    isHalfMatching m = true ↔
      (edgeImgFun (matchPerm15 m)⁻¹ 0 ≠ 0 ∧ edgeImgFun (matchPerm15 m)⁻¹ 0 ≠ 9 ∧
       edgeImgFun (matchPerm15 m)⁻¹ 0 ≠ 14 ∧
       edgeImgFun (matchPerm15 m)⁻¹ 4 ≠ 0 ∧ edgeImgFun (matchPerm15 m)⁻¹ 4 ≠ 9 ∧
       edgeImgFun (matchPerm15 m)⁻¹ 4 ≠ 14 ∧
       edgeImgFun (matchPerm15 m)⁻¹ 8 ≠ 0 ∧ edgeImgFun (matchPerm15 m)⁻¹ 8 ≠ 9 ∧
       edgeImgFun (matchPerm15 m)⁻¹ 8 ≠ 14) := by
  revert m; decide

private lemma fixedElem_preserves_zero_tri (b : Bool × Bool × Bool × Bool × Bool) (e : Fin 15) :
    (edgeImgFun (fixedElem b) e = 0 ∨ edgeImgFun (fixedElem b) e = 9 ∨
     edgeImgFun (fixedElem b) e = 14) ↔ (e = 0 ∨ e = 9 ∨ e = 14) := by
  rcases b with ⟨sw0, s2, s3, s4, s5⟩
  revert e
  cases sw0 <;> cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;> decide

private lemma edgeImgFun_mul_eq (g1 g2 : B6Plus) (e : Fin 15) :
    edgeImgFun (g1 * g2) e = edgeImgFun g2 (edgeImgFun g1 e) := by
  have h1 : ∀ u v : Fin 6, u ≠ v →
      (edgePairs (edgeLookup u v).1 = (u, v) ∨ edgePairs (edgeLookup u v).1 = (v, u)) := by
    decide
  have hne1 : g1.perm (edgePairs e).1 ≠ g1.perm (edgePairs e).2 := by
    intro he; have := g1.perm.injective he; fin_cases e <;> simp [edgePairs] at this
  have hlu_sym : ∀ u v : Fin 6, (edgeLookup u v).1 = (edgeLookup v u).1 := by decide
  rcases h1 _ _ hne1 with hp | hp
  · change (edgeLookup (g2.perm (g1.perm (edgePairs e).1))
      (g2.perm (g1.perm (edgePairs e).2))).1 =
      (edgeLookup (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e).1)
        (g1.perm (edgePairs e).2)).1).1)
      (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e).1)
        (g1.perm (edgePairs e).2)).1).2)).1
    rw [hp]
  · change (edgeLookup (g2.perm (g1.perm (edgePairs e).1))
      (g2.perm (g1.perm (edgePairs e).2))).1 =
      (edgeLookup (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e).1)
        (g1.perm (edgePairs e).2)).1).1)
      (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e).1)
        (g1.perm (edgePairs e).2)).1).2)).1
    rw [hp, hlu_sym]

/-- For a maximizer parameterized by `mb = (m, b)`, its concurrence equals `1 / 2` iff
    `isHalfMatching m = true`, and equals `1 / √2` iff `isHalfMatching m = false`. -/
lemma concurrence_of_maximizerParam {ψ : State} (hψ : IsNormalized ψ)
    (mb : Fin 15 × (Bool × Bool × Bool × Bool × Bool))
    (hso6 : so6Edge ψ = actB6Vec (maximizerParam mb) (so6Edge mubFiducial)) :
    (concurrence ψ = 1 / 2 ↔ isHalfMatching mb.1 = true) ∧
    (concurrence ψ = 1 / Real.sqrt 2 ↔ isHalfMatching mb.1 = false) := by
  have hnz : ∀ e : Fin 15,
      so6Edge ψ e ≠ 0 ↔
        edgeImgFun (matchPerm15 mb.1)⁻¹ e ≠ 0 ∧
        edgeImgFun (matchPerm15 mb.1)⁻¹ e ≠ 9 ∧
        edgeImgFun (matchPerm15 mb.1)⁻¹ e ≠ 14 := by
    intro e
    rw [hso6, actB6Vec_apply]
    have hsne : (edgeSgnFun (maximizerParam mb) e : ℝ) ≠ 0 := by
      intro h0; have := edgeSgnFun_sq (maximizerParam mb) e; rw [h0] at this; norm_num at this
    rw [ne_eq, mul_eq_zero, or_iff_right hsne, ← abs_eq_zero, mubFiducial_so6_abs]
    have hiff :
        (edgeImgFun (maximizerParam mb) e = 0 ∨ edgeImgFun (maximizerParam mb) e = 9 ∨
         edgeImgFun (maximizerParam mb) e = 14) ↔
        (edgeImgFun (matchPerm15 mb.1)⁻¹ e = 0 ∨ edgeImgFun (matchPerm15 mb.1)⁻¹ e = 9 ∨
         edgeImgFun (matchPerm15 mb.1)⁻¹ e = 14) := by
      dsimp only [maximizerParam]
      rw [edgeImgFun_mul_eq, fixedElem_preserves_zero_tri]
    split_ifs with h
    · constructor
      · intro h0; exact absurd rfl h0
      · intro ⟨h0, h9, h14⟩
        exfalso
        rcases hiff.mp h with hc | hc | hc <;> [exact h0 hc; exact h9 hc; exact h14 hc]
    · constructor
      · intro _
        have hnot := mt hiff.mpr h
        push Not at hnot
        exact hnot
      · intro _; norm_num
  have hmax : sre ψ 2 = (1 / (1 - (2 : ℝ))) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - (2 : ℝ))) / 4) := by
    rw [maximizer_iff_mub_spectrum hψ (le_refl 2)]
    intro a b hab
    rcases edgePauliLabel_surj hab with ⟨e, he⟩
    have ha_eq : a = (edgePauliLabel e).1 := (Prod.mk.inj he).1.symm
    have hb_eq : b = (edgePauliLabel e).2 := (Prod.mk.inj he).2.symm
    subst ha_eq; subst hb_eq
    have habs : ‖pauliExp ψ (edgePauliLabel e).1 (edgePauliLabel e).2‖ = |so6Edge ψ e| := by
      rw [so6Edge_eq_pauliExpRe, abs_mul, ← norm_pauliExp]
      have hs : |(edgePauliSign e : ℝ)| = 1 := by fin_cases e <;> simp [edgePauliSign]
      rw [hs, one_mul]
    rw [habs, hso6, actB6Vec_apply, abs_mul]
    have hs : |(edgeSgnFun (maximizerParam mb) e : ℝ)| = 1 := by
      have hsq := edgeSgnFun_sq (maximizerParam mb) e
      rw [← sq_abs] at hsq
      nlinarith [abs_nonneg (edgeSgnFun (maximizerParam mb) e : ℝ)]
    rw [hs, one_mul, mubFiducial_so6_abs]
    split_ifs <;> [left; right] <;> rfl
  have hsq_half_if_nz : ∀ e : Fin 15, so6Edge ψ e ≠ 0 → so6Edge ψ e ^ 2 = 1 / 4 := by
    intro e hne
    have habs : |so6Edge ψ e| = 1 / 2 := by
      rw [hso6, actB6Vec_apply] at hne ⊢
      rw [abs_mul]
      have hs : |(edgeSgnFun (maximizerParam mb) e : ℝ)| = 1 := by
        have hsq := edgeSgnFun_sq (maximizerParam mb) e
        rw [← sq_abs] at hsq
        nlinarith [abs_nonneg (edgeSgnFun (maximizerParam mb) e : ℝ)]
      rw [hs, one_mul, mubFiducial_so6_abs]
      split_ifs with h
      · exfalso; apply hne
        have : |so6Edge mubFiducial (edgeImgFun (maximizerParam mb) e)| = 0 := by
          rw [mubFiducial_so6_abs]; simp [h]
        rw [abs_eq_zero.mp this, mul_zero]
      · rfl
    rw [← sq_abs, habs]; norm_num
  have hne_vals : (1 / 2 : ℝ) ≠ 1 / Real.sqrt 2 := by
    intro heq
    have hsq := congrArg (fun x : ℝ => x ^ 2) heq
    rw [inv_sqrt2_sq] at hsq
    norm_num at hsq
  have hhalf : concurrence ψ = 1 / 2 ↔ isHalfMatching mb.1 = true := by
    rw [isHalfMatching_iff_no_triangleA_zero]
    constructor
    · intro hc
      have hcsq := concurrence_sq_eq_one_sub_so6_triangleA hψ
      rw [hc] at hcsq
      have hle : ∀ e : Fin 15, so6Edge ψ e ^ 2 ≤ 1 / 4 := fun e => by
        by_cases h0 : so6Edge ψ e = 0
        · rw [h0]; norm_num
        · rw [hsq_half_if_nz e h0]
      have h0ne : so6Edge ψ 0 ≠ 0 := fun h0 => by rw [h0] at hcsq; linarith [hle 4, hle 8]
      have h4ne : so6Edge ψ 4 ≠ 0 := fun h4 => by rw [h4] at hcsq; linarith [hle 0, hle 8]
      have h8ne : so6Edge ψ 8 ≠ 0 := fun h8 => by rw [h8] at hcsq; linarith [hle 0, hle 4]
      rcases (hnz 0).mp h0ne with ⟨a1, a2, a3⟩
      rcases (hnz 4).mp h4ne with ⟨b1, b2, b3⟩
      rcases (hnz 8).mp h8ne with ⟨c1, c2, c3⟩
      exact ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3⟩
    · rintro ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3⟩
      have h0sq := hsq_half_if_nz 0 ((hnz 0).mpr ⟨a1, a2, a3⟩)
      have h4sq := hsq_half_if_nz 4 ((hnz 4).mpr ⟨b1, b2, b3⟩)
      have h8sq := hsq_half_if_nz 8 ((hnz 8).mpr ⟨c1, c2, c3⟩)
      have hcsq := concurrence_sq_eq_one_sub_so6_triangleA hψ
      rw [h0sq, h4sq, h8sq] at hcsq
      nlinarith [concurrence_nonneg ψ]
  refine ⟨hhalf, ?_⟩
  rcases maximizer_concurrence_dichotomy hψ (le_refl 2) hmax with hc1 | hc2
  · have ht : isHalfMatching mb.1 = true := hhalf.mp hc1
    rw [hc1, ht]
    exact ⟨fun h => absurd h hne_vals, fun h => by cases h⟩
  · have hf : isHalfMatching mb.1 = false := by
      cases h : isHalfMatching mb.1
      · rfl
      · exfalso; exact hne_vals ((hhalf.mpr h).symm.trans hc2)
    rw [hc2, hf]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Exact 192 / 288 Entanglement Distribution Among All 480 Maximizers**:
    For every Rényi order `α ≥ 2`, among the 480 pure-state density matrices achieving maximal
    magic `M_α`, **exactly 192** have concurrence `1 / 2` and **exactly 288** have concurrence
    `1 / √2`. -/
theorem maximizer_concurrence_distribution {α : ℝ} (hα : 2 ≤ α) :
    let S_half : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
      {ρ | ∃ ψ : State, IsNormalized ψ ∧
        sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ∧
        concurrence ψ = 1 / 2 ∧ ρ = densityMatrix ψ}
    let S_invsqrt2 : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
      {ρ | ∃ ψ : State, IsNormalized ψ ∧
        sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ∧
        concurrence ψ = 1 / Real.sqrt 2 ∧ ρ = densityMatrix ψ}
    (S_half.Finite ∧ S_half.ncard = 192) ∧
    (S_invsqrt2.Finite ∧ S_invsqrt2.ncard = 288) := by
  intro S_half S_invsqrt2
  have hlift : ∀ mb : Fin 15 × (Bool × Bool × Bool × Bool × Bool),
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
        ∀ ψ : State, so6Edge (U *ᵥ ψ) = actB6Vec (maximizerParam mb) (so6Edge ψ) :=
    fun mb => clifford_lift_b6Plus (maximizerParam mb)
  choose Uf hUf hactUf using hlift
  let f : Fin 15 × (Bool × Bool × Bool × Bool × Bool) → Matrix (Fin 4) (Fin 4) ℂ :=
    fun mb => densityMatrix (Uf mb *ᵥ mubFiducial)
  have hf_inj : Function.Injective f := by
    intro mb₁ mb₂ heq
    have hn1 : IsNormalized (Uf mb₁ *ᵥ mubFiducial) :=
      (hUf mb₁).preserves_isNormalized mubFiducial_normalized
    have hn2 : IsNormalized (Uf mb₂ *ᵥ mubFiducial) :=
      (hUf mb₂).preserves_isNormalized mubFiducial_normalized
    have hso6 := (densityMatrix_eq_iff_so6Edge_eq hn1 hn2).mp heq
    rw [hactUf mb₁, hactUf mb₂] at hso6
    have ha1 : IsSkewOrth6 (actB6Vec (maximizerParam mb₁) (so6Edge mubFiducial)) :=
      isSkewOrth6_actB6 _ (so6Edge_isSkewOrth6 mubFiducial_normalized)
    have hspec1 : ∀ e : Fin 15,
        |actB6Vec (maximizerParam mb₁) (so6Edge mubFiducial) e| = 0 ∨
        |actB6Vec (maximizerParam mb₁) (so6Edge mubFiducial) e| = 1 / 2 := by
      intro e
      rw [actB6Vec_apply, abs_mul]
      have hs : |(edgeSgnFun (maximizerParam mb₁) e : ℝ)| = 1 := by
        have hsq := edgeSgnFun_sq (maximizerParam mb₁) e
        rw [← sq_abs] at hsq
        nlinarith [abs_nonneg (edgeSgnFun (maximizerParam mb₁) e : ℝ)]
      rw [hs, one_mul, mubFiducial_so6_abs]
      split_ifs <;> [left; right] <;> rfl
    rcases so6_maximizer_exists_unique_param ha1 hspec1 with ⟨mb₀, _, huniq⟩
    exact (huniq mb₁ rfl).trans (huniq mb₂ hso6).symm
  have hparam_of_max : ∀ {ψ : State}, IsNormalized ψ →
      sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) →
      ∃ mb, so6Edge ψ = actB6Vec (maximizerParam mb) (so6Edge mubFiducial) ∧
        f mb = densityMatrix ψ := by
    intro ψ hψ hmax
    have hspec_p := (maximizer_iff_mub_spectrum hψ hα).mp hmax
    have hspec : ∀ e : Fin 15, |so6Edge ψ e| = 0 ∨ |so6Edge ψ e| = 1 / 2 := by
      intro e
      have hp := hspec_p (edgePauliLabel e).1 (edgePauliLabel e).2 (edgePauliLabel_ne_zero e)
      rw [so6Edge_eq_pauliExpRe, abs_mul, ← norm_pauliExp]
      have hs : |(edgePauliSign e : ℝ)| = 1 := by fin_cases e <;> simp [edgePauliSign]
      rw [hs, one_mul]; exact hp
    rcases (so6_maximizer_exists_unique_param (so6Edge_isSkewOrth6 hψ) hspec).exists with ⟨mb, hmb⟩
    refine ⟨mb, hmb, ?_⟩
    have hn : IsNormalized (Uf mb *ᵥ mubFiducial) :=
      (hUf mb).preserves_isNormalized mubFiducial_normalized
    exact (densityMatrix_eq_iff_so6Edge_eq hn hψ).mpr ((hactUf mb mubFiducial).trans hmb.symm)
  -- Subtype 1: 6 × 32 = 192 parameters for `C = 1/2`
  let f_half : {m : Fin 15 // isHalfMatching m = true} × (Bool × Bool × Bool × Bool × Bool) →
      Matrix (Fin 4) (Fin 4) ℂ := fun x => f (x.1.1, x.2)
  have hf_half_inj : Function.Injective f_half := by
    intro x y hxy
    have h := hf_inj hxy
    exact Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2
  have hrange_half : Set.range f_half = S_half := by
    ext ρ
    constructor
    · rintro ⟨⟨⟨m, hm⟩, b⟩, rfl⟩
      have hn : IsNormalized (Uf (m, b) *ᵥ mubFiducial) :=
        (hUf (m, b)).preserves_isNormalized mubFiducial_normalized
      have hc := (concurrence_of_maximizerParam hn (m, b) (hactUf (m, b) mubFiducial)).1.mpr hm
      exact ⟨Uf (m, b) *ᵥ mubFiducial, hn,
        by rw [(hUf (m, b)).preserves_sre]; exact mub_fiducial_attains_sre hα, hc, rfl⟩
    · rintro ⟨ψ, hψ, hmax, hc, rfl⟩
      rcases hparam_of_max hψ hmax with ⟨⟨m, b⟩, hmb, hfmb⟩
      have hm : isHalfMatching m = true := (concurrence_of_maximizerParam hψ (m, b) hmb).1.mp hc
      exact ⟨⟨⟨m, hm⟩, b⟩, hfmb⟩
  -- Subtype 2: 9 × 32 = 288 parameters for `C = 1/√2`
  let f_inv : {m : Fin 15 // isHalfMatching m = false} × (Bool × Bool × Bool × Bool × Bool) →
      Matrix (Fin 4) (Fin 4) ℂ := fun x => f (x.1.1, x.2)
  have hf_inv_inj : Function.Injective f_inv := by
    intro x y hxy
    have h := hf_inj hxy
    exact Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2
  have hrange_inv : Set.range f_inv = S_invsqrt2 := by
    ext ρ
    constructor
    · rintro ⟨⟨⟨m, hm⟩, b⟩, rfl⟩
      have hn : IsNormalized (Uf (m, b) *ᵥ mubFiducial) :=
        (hUf (m, b)).preserves_isNormalized mubFiducial_normalized
      have hc := (concurrence_of_maximizerParam hn (m, b) (hactUf (m, b) mubFiducial)).2.mpr hm
      exact ⟨Uf (m, b) *ᵥ mubFiducial, hn,
        by rw [(hUf (m, b)).preserves_sre]; exact mub_fiducial_attains_sre hα, hc, rfl⟩
    · rintro ⟨ψ, hψ, hmax, hc, rfl⟩
      rcases hparam_of_max hψ hmax with ⟨⟨m, b⟩, hmb, hfmb⟩
      have hm : isHalfMatching m = false := (concurrence_of_maximizerParam hψ (m, b) hmb).2.mp hc
      exact ⟨⟨⟨m, hm⟩, b⟩, hfmb⟩
  have hcard6 : Fintype.card {m : Fin 15 // isHalfMatching m = true} = 6 := by decide
  have hcard9 : Fintype.card {m : Fin 15 // isHalfMatching m = false} = 9 := by decide
  constructor
  · rw [← hrange_half]
    refine ⟨Set.finite_range f_half, ?_⟩
    rw [Set.ncard_range_of_injective hf_half_inj, Nat.card_eq_fintype_card, Fintype.card_prod, hcard6]
    norm_num
  · rw [← hrange_inv]
    refine ⟨Set.finite_range f_inv, ?_⟩
    rw [Set.ncard_range_of_injective hf_inv_inj, Nat.card_eq_fintype_card, Fintype.card_prod, hcard9]
    norm_num

end TwoQubitMaximalMagic
