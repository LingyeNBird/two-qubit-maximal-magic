module

public import TwoQubitMaximalMagic.MainTheorem
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Complete Characterization of All 480 Two-Qubit Maximal Magic States

Building on the sharp upper bound `sre_upper_bound_all_alpha` and Pauli-spectrum criterion
`maximizer_iff_mub_spectrum` in `MainTheorem.lean`, this file formally proves all structural
characterizations of the two-qubit maximal magic states:

1. **Pauli commutation ↔ `K₆` edge disjointness & maximal commuting triple**
   (`pauli_commute_iff_edgeDisjoint`, `pauli_anticommute_iff_not_edgeDisjoint`,
   `maximizer_zero_paulis_maximal_commuting`):
   Two distinct non-identity two-qubit Pauli operators commute iff their `K₆` edges are
   vertex-disjoint (and anticommute iff they share a vertex). Consequently, for every maximizer
   `ψ` of `M_α` (`α ≥ 2`), the 3 vanishing non-identity Pauli expectations form a maximal
   pairwise-commuting triple of non-identity two-qubit Pauli operators.

2. **Density-matrix reconstruction & global-phase equivalence**
   (`densityMatrix_eq_pauli_expansion`, `densityMatrix_eq_iff_so6Edge_eq`,
   `densityMatrix_eq_iff_phase`):
   Two normalized pure states define the same density matrix `|ψ⟩⟨ψ|` iff they agree up to a
   unit global phase iff they have identical `so6Edge` vectors.

3. **Two-qubit Clifford group & Clifford realization of `B₆⁺`**
   (`IsClifford2`, `clifford_lift_b6Plus`):
   Using the textbook definition of the two-qubit Clifford group (`Uᴴ * U = 1` normalizing
   `{±1, ±i} · P₂`), every signed permutation `g ∈ B₆⁺` lifts to a Clifford unitary `U` whose
   action on pure states induces `actB6Vec g` on `so6Edge`.

4. **Single Clifford orbit & exact cardinality 480**
   (`maximizer_iff_clifford_orbit`, `maximizer_iff_clifford_densityMatrix`,
   `maximizer_densityMatrix_ncard_eq_480`):
   A normalized pure two-qubit state maximizes `M_α` (`α ≥ 2`) iff it lies in the two-qubit
   Clifford orbit of `mubFiducial` (up to global phase). Moreover, the set of maximizer density
   matrices `|ψ⟩⟨ψ|` is finite and has exact cardinality `480` (`15` matchings × `32` sign/orientation
   classes).

5. **Two-qubit Weyl–Heisenberg (Pauli) MUB fiducial characterization**
   (`IsCompleteMUB`, `IsPauliMUBFiducial`, `mubFiducial_isPauliMUBFiducial`,
   `maximizer_iff_pauli_mub_fiducial`):
   A normalized pure two-qubit state maximizes `M_α` (`α ≥ 2`) iff its 16-state two-qubit
   Weyl–Heisenberg (Pauli) orbit `{P_{a,b}|ψ⟩}` partitions into 4 orthonormal bases that extend
   to a complete set of `d + 1 = 5` mutually unbiased bases (MUBs) in `ℂ⁴`.
-/

@[expose] public section

open scoped Matrix

namespace TwoQubitMaximalMagic

private lemma mul_star_self_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, mul_star_self_eq_norm_sq]

/-! ### Part 1: Pauli Commutation ↔ `K₆` Edge Disjointness and Maximal Commuting Triple -/

/-- The non-identity two-qubit Pauli label `(a, b)` attached to each edge `e : Fin 15` of `K₆`. -/
def edgePauliLabel : Fin 15 → Fin 4 × Fin 4
  | 0  => (3, 0) -- ZI
  | 1  => (2, 1) -- YX
  | 2  => (2, 2) -- YY
  | 3  => (2, 3) -- YZ
  | 4  => (1, 0) -- XI
  | 5  => (1, 1) -- XX
  | 6  => (1, 2) -- XY
  | 7  => (1, 3) -- XZ
  | 8  => (2, 0) -- YI
  | 9  => (0, 3) -- IZ
  | 10 => (0, 2) -- IY
  | 11 => (3, 1) -- ZX
  | 12 => (0, 1) -- IX
  | 13 => (3, 2) -- ZY
  | 14 => (3, 3) -- ZZ

/-- The orientation sign `±1` attached to each edge `e : Fin 15` in `so6Edge`. -/
def edgePauliSign : Fin 15 → ℤ
  | 0  =>  1
  | 1  => -1
  | 2  =>  1
  | 3  =>  1
  | 4  =>  1
  | 5  => -1
  | 6  =>  1
  | 7  =>  1
  | 8  => -1
  | 9  =>  1
  | 10 => -1
  | 11 => -1
  | 12 => -1
  | 13 =>  1
  | 14 =>  1

/-- The signed two-qubit Pauli matrix `s_e · P_{a_e, b_e}` corresponding to edge `e : Fin 15`. -/
def edgeSignedPauli (e : Fin 15) : Matrix (Fin 4) (Fin 4) ℂ :=
  (edgePauliSign e : ℂ) • pauli2 (edgePauliLabel e).1 (edgePauliLabel e).2

lemma edgePauliLabel_ne_zero (e : Fin 15) :
    (edgePauliLabel e).1 ≠ 0 ∨ (edgePauliLabel e).2 ≠ 0 := by
  fin_cases e <;> decide

lemma edgePauliLabel_injective : Function.Injective edgePauliLabel := by
  decide

lemma edgePauliLabel_surj {a b : Fin 4} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ e : Fin 15, edgePauliLabel e = (a, b) := by
  revert a b hab; decide

lemma so6Edge_eq_pauliExpRe (ψ : State) (e : Fin 15) :
    so6Edge ψ e = (edgePauliSign e : ℝ) * pauliExpRe ψ (edgePauliLabel e).1 (edgePauliLabel e).2 := by
  fin_cases e <;> simp [so6Edge, edgePauliSign, edgePauliLabel]

lemma pauliExp_edgeLabel_eq_zero_iff (ψ : State) (e : Fin 15) :
    pauliExp ψ (edgePauliLabel e).1 (edgePauliLabel e).2 = 0 ↔ so6Edge ψ e = 0 := by
  rw [pauliExp_eq_ofReal, Complex.ofReal_eq_zero, so6Edge_eq_pauliExpRe]
  fin_cases e <;> simp [edgePauliSign]

/-- Two edges in `K₆` are vertex-disjoint. -/
def edgeDisjoint (e₁ e₂ : Fin 15) : Prop :=
  (edgePairs e₁).1 ≠ (edgePairs e₂).1 ∧
  (edgePairs e₁).1 ≠ (edgePairs e₂).2 ∧
  (edgePairs e₁).2 ≠ (edgePairs e₂).1 ∧
  (edgePairs e₁).2 ≠ (edgePairs e₂).2

instance (e₁ e₂ : Fin 15) : Decidable (edgeDisjoint e₁ e₂) := by
  unfold edgeDisjoint; infer_instance

/-- Single-qubit Pauli commutation predicate (`true` iff `pauli1 a` and `pauli1 b` commute). -/
def pauli1CommBool (a b : Fin 4) : Bool :=
  a == 0 || b == 0 || a == b

/-- Two-qubit Pauli commutation predicate (`true` iff `pauli2 a₁ b₁` and `pauli2 a₂ b₂` commute). -/
def pauli2CommBool (p q : Fin 4 × Fin 4) : Bool :=
  (pauli1CommBool p.1 q.1) == (pauli1CommBool p.2 q.2)

lemma pauli1_mul_comm_or_anticomm (a b : Fin 4) :
    pauli1 a * pauli1 b =
      (if pauli1CommBool a b then (1 : ℂ) else -1) • (pauli1 b * pauli1 a) := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli1CommBool, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauli2_mul_apply_kron (a₁ b₁ a₂ b₂ : Fin 4) (i j : Fin 4) :
    (pauli2 a₁ b₁ * pauli2 a₂ b₂) i j =
      (pauli1 a₁ * pauli1 a₂) ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
      (pauli1 b₁ * pauli1 b₂) ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩ := by
  simp only [Matrix.mul_apply, pauli2, Fin.sum_univ_four, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> (norm_num; ring)

lemma pauli2_mul_comm_or_anticomm (p q : Fin 4 × Fin 4) :
    pauli2 p.1 p.2 * pauli2 q.1 q.2 =
      (if pauli2CommBool p q then (1 : ℂ) else -1) • (pauli2 q.1 q.2 * pauli2 p.1 p.2) := by
  ext i j
  rw [pauli2_mul_apply_kron, Matrix.smul_apply, smul_eq_mul, pauli2_mul_apply_kron]
  have h1 := congrFun (congrFun (pauli1_mul_comm_or_anticomm p.1 q.1)
    ⟨i.val / 2, by omega⟩) ⟨j.val / 2, by omega⟩
  have h2 := congrFun (congrFun (pauli1_mul_comm_or_anticomm p.2 q.2)
    ⟨i.val % 2, by omega⟩) ⟨j.val % 2, by omega⟩
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2]
  unfold pauli2CommBool
  cases pauli1CommBool p.1 q.1 <;> cases pauli1CommBool p.2 q.2 <;> simp

lemma pauli1_sq (a : Fin 4) : pauli1 a * pauli1 a = 1 := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauli2_sq (a b : Fin 4) : pauli2 a b * pauli2 a b = 1 := by
  ext i j
  rw [pauli2_mul_apply_kron, pauli1_sq, pauli1_sq]
  fin_cases i <;> fin_cases j <;> simp

lemma pauli2_mul_ne_zero (p q : Fin 4 × Fin 4) : pauli2 p.1 p.2 * pauli2 q.1 q.2 ≠ 0 := by
  intro h
  have h1 : pauli2 p.1 p.2 * (pauli2 p.1 p.2 * pauli2 q.1 q.2) * pauli2 q.1 q.2 = 0 := by
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have h2 : pauli2 p.1 p.2 * (pauli2 p.1 p.2 * pauli2 q.1 q.2) * pauli2 q.1 q.2 = 1 := by
    calc pauli2 p.1 p.2 * (pauli2 p.1 p.2 * pauli2 q.1 q.2) * pauli2 q.1 q.2
        = (pauli2 p.1 p.2 * pauli2 p.1 p.2) * (pauli2 q.1 q.2 * pauli2 q.1 q.2) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * 1 := by rw [pauli2_sq, pauli2_sq]
      _ = 1 := by simp
  rw [h2] at h1
  have h00 := congrFun (congrFun h1 0) 0
  simp at h00

lemma pauli2_commute_iff_bool (p q : Fin 4 × Fin 4) :
    pauli2 p.1 p.2 * pauli2 q.1 q.2 = pauli2 q.1 q.2 * pauli2 p.1 p.2 ↔
      pauli2CommBool p q = true := by
  have h := pauli2_mul_comm_or_anticomm p q
  cases hb : pauli2CommBool p q
  · rw [hb] at h
    simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul] at h
    constructor
    · intro hcomm
      exfalso
      have h2 : (2 : ℂ) • (pauli2 q.1 q.2 * pauli2 p.1 p.2) = 0 := by
        ext i j
        have hij := congrFun (congrFun (hcomm.symm.trans h) i) j
        simp only [Matrix.neg_apply] at hij
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
        linear_combination hij
      have hne := pauli2_mul_ne_zero q p
      apply hne
      ext i j
      have hij := congrFun (congrFun h2 i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
      exact (mul_eq_zero.mp hij).resolve_left (by norm_num)
    · intro hc; cases hc
  · rw [hb] at h
    simp only [↓reduceIte, one_smul] at h
    exact ⟨fun _ => rfl, fun _ => h⟩

lemma pauli2_anticommute_iff_bool (p q : Fin 4 × Fin 4) :
    pauli2 p.1 p.2 * pauli2 q.1 q.2 = -(pauli2 q.1 q.2 * pauli2 p.1 p.2) ↔
      pauli2CommBool p q = false := by
  have h := pauli2_mul_comm_or_anticomm p q
  cases hb : pauli2CommBool p q
  · rw [hb] at h
    simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul] at h
    exact ⟨fun _ => rfl, fun _ => h⟩
  · rw [hb] at h
    simp only [↓reduceIte, one_smul] at h
    constructor
    · intro hanti
      exfalso
      have hne := pauli2_mul_ne_zero q p
      apply hne
      ext i j
      have hij := congrFun (congrFun (h.symm.trans hanti) i) j
      simp only [Matrix.neg_apply, Matrix.zero_apply] at hij ⊢
      linear_combination (1 / 2 : ℂ) * hij
    · intro hc; cases hc

lemma edgeDisjoint_iff_pauli2CommBool (e₁ e₂ : Fin 15) (hne : e₁ ≠ e₂) :
    edgeDisjoint e₁ e₂ ↔ pauli2CommBool (edgePauliLabel e₁) (edgePauliLabel e₂) = true := by
  revert e₁ e₂ hne; decide

/-- Two distinct non-identity two-qubit Pauli operators commute iff their `K₆` edges are
    vertex-disjoint. -/
theorem pauli_commute_iff_edgeDisjoint (e₁ e₂ : Fin 15) (hne : e₁ ≠ e₂) :
    pauli2 (edgePauliLabel e₁).1 (edgePauliLabel e₁).2 *
      pauli2 (edgePauliLabel e₂).1 (edgePauliLabel e₂).2 =
    pauli2 (edgePauliLabel e₂).1 (edgePauliLabel e₂).2 *
      pauli2 (edgePauliLabel e₁).1 (edgePauliLabel e₁).2 ↔ edgeDisjoint e₁ e₂ := by
  rw [pauli2_commute_iff_bool, edgeDisjoint_iff_pauli2CommBool e₁ e₂ hne]

/-- Two distinct non-identity two-qubit Pauli operators anticommute iff their `K₆` edges share
    a vertex. -/
theorem pauli_anticommute_iff_not_edgeDisjoint (e₁ e₂ : Fin 15) (hne : e₁ ≠ e₂) :
    pauli2 (edgePauliLabel e₁).1 (edgePauliLabel e₁).2 *
      pauli2 (edgePauliLabel e₂).1 (edgePauliLabel e₂).2 =
    -(pauli2 (edgePauliLabel e₂).1 (edgePauliLabel e₂).2 *
      pauli2 (edgePauliLabel e₁).1 (edgePauliLabel e₁).2) ↔ ¬ edgeDisjoint e₁ e₂ := by
  rw [pauli2_anticommute_iff_bool, edgeDisjoint_iff_pauli2CommBool e₁ e₂ hne]
  cases pauli2CommBool (edgePauliLabel e₁) (edgePauliLabel e₂) <;> simp

/-- For every maximizer `ψ` of `M_α` (`α ≥ 2`), the set of vanishing non-identity Pauli
    operators has cardinality 3, is pairwise commuting, and is maximal among commuting sets of
    non-identity two-qubit Pauli operators. -/
theorem maximizer_zero_paulis_maximal_commuting {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α)
    (hmax : sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4)) :
    let Z := Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
      (p.1 ≠ 0 ∨ p.2 ≠ 0) ∧ pauliExp ψ p.1 p.2 = 0)
    Z.card = 3 ∧
    (∀ p ∈ Z, ∀ q ∈ Z, pauli2 p.1 p.2 * pauli2 q.1 q.2 = pauli2 q.1 q.2 * pauli2 p.1 p.2) ∧
    (∀ p : Fin 4 × Fin 4, (p.1 ≠ 0 ∨ p.2 ≠ 0) →
      (∀ q ∈ Z, pauli2 p.1 p.2 * pauli2 q.1 q.2 = pauli2 q.1 q.2 * pauli2 p.1 p.2) →
      p ∈ Z) := by
  intro Z
  have hmc := maximizer_matching_counts hψ hα hmax
  rcases hmc with ⟨hcard3, _, hdeg1⟩
  let E0 := Finset.univ.filter (fun e : Fin 15 => so6Edge ψ e = 0)
  have hZ_eq : Z = E0.image edgePauliLabel := by
    ext p
    simp only [Z, E0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hp_ne, hp_zero⟩
      rcases edgePauliLabel_surj hp_ne with ⟨e, he⟩
      refine ⟨e, ?_, he⟩
      rw [← pauliExp_edgeLabel_eq_zero_iff, he]
      exact hp_zero
    · rintro ⟨e, he0, rfl⟩
      refine ⟨edgePauliLabel_ne_zero e, ?_⟩
      exact (pauliExp_edgeLabel_eq_zero_iff ψ e).mpr he0
  have hzero_disj : ∀ e₁ ∈ E0, ∀ e₂ ∈ E0, e₁ ≠ e₂ → edgeDisjoint e₁ e₂ := by
    intro e₁ he₁ e₂ he₂ hne
    have hz1 : so6Edge ψ e₁ = 0 := (Finset.mem_filter.mp he₁).2
    have hz2 : so6Edge ψ e₂ = 0 := (Finset.mem_filter.mp he₂).2
    have hlt1 : (edgePairs e₁).1 < (edgePairs e₁).2 := by fin_cases e₁ <;> decide
    have hlt2 : (edgePairs e₂).1 < (edgePairs e₂).2 := by fin_cases e₂ <;> decide
    have hmat1 : toSkewMat (so6Edge ψ) (edgePairs e₁).1 (edgePairs e₁).2 = 0 := by
      rw [toSkewMat_edge]; exact hz1
    have hmat2 : toSkewMat (so6Edge ψ) (edgePairs e₂).1 (edgePairs e₂).2 = 0 := by
      rw [toSkewMat_edge]; exact hz2
    have huniq : ∀ u v w : Fin 6, v ≠ u → w ≠ u →
        toSkewMat (so6Edge ψ) u v = 0 → toSkewMat (so6Edge ψ) u w = 0 → v = w := by
      intro u v w hvu hwu huv huw
      have hcard := hdeg1 u
      have hv : v ∈ Finset.univ.filter (fun j : Fin 6 => j ≠ u ∧ toSkewMat (so6Edge ψ) u j = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, huv⟩
      have hw : w ∈ Finset.univ.filter (fun j : Fin 6 => j ≠ u ∧ toSkewMat (so6Edge ψ) u j = 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwu, huw⟩
      rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
      rw [hx, Finset.mem_singleton] at hv hw
      exact hv.trans hw.symm
    have hpair_inj : ∀ x y : Fin 15, edgePairs x = edgePairs y → x = y := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h11
      have h22 := huniq (edgePairs e₁).1 (edgePairs e₁).2 (edgePairs e₂).2
        (ne_of_gt hlt1) (by rw [h11]; exact ne_of_gt hlt2) hmat1 (by rw [h11]; exact hmat2)
      exact hne (hpair_inj e₁ e₂ (Prod.ext h11 h22))
    · intro h12
      have hsw2 : toSkewMat (so6Edge ψ) (edgePairs e₂).2 (edgePairs e₂).1 = 0 := by
        rw [toSkewMat_swap, hmat2, neg_zero]
      have h21 := huniq (edgePairs e₁).1 (edgePairs e₁).2 (edgePairs e₂).1
        (ne_of_gt hlt1) (by rw [h12]; exact ne_of_lt hlt2) hmat1 (by rw [h12]; exact hsw2)
      omega
    · intro h21
      have hsw1 : toSkewMat (so6Edge ψ) (edgePairs e₁).2 (edgePairs e₁).1 = 0 := by
        rw [toSkewMat_swap, hmat1, neg_zero]
      have h12 := huniq (edgePairs e₁).2 (edgePairs e₁).1 (edgePairs e₂).2
        (ne_of_lt hlt1) (by rw [h21]; exact ne_of_gt hlt2) hsw1 (by rw [h21]; exact hmat2)
      omega
    · intro h22
      have hsw1 : toSkewMat (so6Edge ψ) (edgePairs e₁).2 (edgePairs e₁).1 = 0 := by
        rw [toSkewMat_swap, hmat1, neg_zero]
      have hsw2 : toSkewMat (so6Edge ψ) (edgePairs e₂).2 (edgePairs e₂).1 = 0 := by
        rw [toSkewMat_swap, hmat2, neg_zero]
      have h11 := huniq (edgePairs e₁).2 (edgePairs e₁).1 (edgePairs e₂).1
        (ne_of_lt hlt1) (by rw [h22]; exact ne_of_lt hlt2) hsw1 (by rw [h22]; exact hsw2)
      exact hne (hpair_inj e₁ e₂ (Prod.ext h11 h22))
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ_eq, Finset.card_image_of_injective _ edgePauliLabel_injective]
    exact hcard3
  · intro p hp q hq
    rw [hZ_eq, Finset.mem_image] at hp hq
    rcases hp with ⟨e₁, he₁, rfl⟩
    rcases hq with ⟨e₂, he₂, rfl⟩
    by_cases hne : e₁ = e₂
    · subst hne; rfl
    · exact (pauli_commute_iff_edgeDisjoint e₁ e₂ hne).mpr (hzero_disj e₁ he₁ e₂ he₂ hne)
  · rintro ⟨a, b⟩ hp_ne hcomm_all
    rcases edgePauliLabel_surj hp_ne with ⟨e, he⟩
    have ha : a = (edgePauliLabel e).1 := (Prod.mk.inj he).1.symm
    have hb : b = (edgePauliLabel e).2 := (Prod.mk.inj he).2.symm
    subst ha; subst hb
    rw [hZ_eq, Finset.mem_image]
    by_contra hnot
    have he_notin : e ∉ E0 := fun hmem => hnot ⟨e, hmem, rfl⟩
    set u : Fin 6 := (edgePairs e).1
    rcases Finset.card_eq_one.mp (hdeg1 u) with ⟨v, hv⟩
    have hv_mem : v ∈ Finset.univ.filter (fun j : Fin 6 => j ≠ u ∧ toSkewMat (so6Edge ψ) u j = 0) := by
      rw [hv]; exact Finset.mem_singleton_self v
    rcases (Finset.mem_filter.mp hv_mem).2 with ⟨hvu, huv0⟩
    have hex_edge : ∃ e' : Fin 15, (edgePairs e' = (u, v) ∨ edgePairs e' = (v, u)) := by
      rcases lt_or_gt_of_ne hvu with hlt | hgt
      · rcases edgePairs_surj_lt hlt with ⟨e', he'⟩; exact ⟨e', Or.inr he'⟩
      · rcases edgePairs_surj_lt hgt with ⟨e', he'⟩; exact ⟨e', Or.inl he'⟩
    rcases hex_edge with ⟨e', he'⟩
    have he'_zero : so6Edge ψ e' = 0 := by
      rcases he' with h1 | h1
      · have h := toSkewMat_edge (so6Edge ψ) e'
        rw [h1] at h; rw [← h]; exact huv0
      · have h := toSkewMat_edge (so6Edge ψ) e'
        rw [h1, toSkewMat_swap] at h
        have : -toSkewMat (so6Edge ψ) u v = 0 := by rw [huv0, neg_zero]
        exact h.symm.trans this
    have he'_mem : e' ∈ E0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'_zero⟩
    have hne : e ≠ e' := fun h => he_notin (h ▸ he'_mem)
    have hcomm := hcomm_all (edgePauliLabel e') (by rw [hZ_eq]; exact Finset.mem_image_of_mem _ he'_mem)
    have hdisj := (pauli_commute_iff_edgeDisjoint e e' hne).mp hcomm
    rcases he' with h1 | h1
    · exact hdisj.1 (by rw [h1])
    · exact hdisj.2.1 (by rw [h1])

/-! ### Part 2: Density Matrix Reconstruction and Global-Phase Equivalence -/

/-- Pure-state density matrix `ρ_ψ = |ψ⟩⟨ψ|`. -/
def densityMatrix (ψ : State) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ψ i * star (ψ j)

lemma pauli1_completeness (r s t u : Fin 2) :
    ∑ a : Fin 4, pauli1 a r s * pauli1 a t u = if r = u ∧ s = t then 2 else 0 := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;> fin_cases u <;>
    simp [pauli1, Fin.sum_univ_four, one_add_one_eq_two]

lemma pauli2_completeness (r s t u : Fin 4) :
    ∑ a : Fin 4, ∑ b : Fin 4, pauli2 a b r s * pauli2 a b t u =
      if r = u ∧ s = t then 4 else 0 := by
  have hfact : ∑ a : Fin 4, ∑ b : Fin 4, pauli2 a b r s * pauli2 a b t u =
      (∑ a : Fin 4, pauli1 a ⟨r.val / 2, by omega⟩ ⟨s.val / 2, by omega⟩ *
        pauli1 a ⟨t.val / 2, by omega⟩ ⟨u.val / 2, by omega⟩) *
      (∑ b : Fin 4, pauli1 b ⟨r.val % 2, by omega⟩ ⟨s.val % 2, by omega⟩ *
        pauli1 b ⟨t.val % 2, by omega⟩ ⟨u.val % 2, by omega⟩) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold pauli2; ring
  rw [hfact, pauli1_completeness, pauli1_completeness]
  have heq : (r = u ∧ s = t) ↔
      ((⟨r.val / 2, by omega⟩ : Fin 2) = ⟨u.val / 2, by omega⟩ ∧
       (⟨s.val / 2, by omega⟩ : Fin 2) = ⟨t.val / 2, by omega⟩) ∧
      ((⟨r.val % 2, by omega⟩ : Fin 2) = ⟨u.val % 2, by omega⟩ ∧
       (⟨s.val % 2, by omega⟩ : Fin 2) = ⟨t.val % 2, by omega⟩) := by
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      simp only [Fin.mk.injEq] at h1 h2 h3 h4
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  by_cases h : r = u ∧ s = t
  · rcases h with ⟨rfl, rfl⟩
    simp only [and_self, ite_true]
    norm_num
  · simp only [h, ite_false]
    by_cases h1 : (⟨r.val / 2, by omega⟩ : Fin 2) = ⟨u.val / 2, by omega⟩ ∧
        (⟨s.val / 2, by omega⟩ : Fin 2) = ⟨t.val / 2, by omega⟩
    · have h2 : ¬ ((⟨r.val % 2, by omega⟩ : Fin 2) = ⟨u.val % 2, by omega⟩ ∧
          (⟨s.val % 2, by omega⟩ : Fin 2) = ⟨t.val % 2, by omega⟩) :=
        fun h2 => h (heq.mpr ⟨h1, h2⟩)
      simp only [h1, h2, ite_false, mul_zero]
    · simp only [h1, ite_false, zero_mul]

private lemma sum4_swap_pauli (f : Fin 4 → Fin 4 → ℂ) (g : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (h : Fin 4 → Fin 4 → ℂ) :
    ∑ a : Fin 4, ∑ b : Fin 4, (∑ r : Fin 4, ∑ s : Fin 4, f r s * g a b r s) * h a b =
    ∑ r : Fin 4, ∑ s : Fin 4, f r s * (∑ a : Fin 4, ∑ b : Fin 4, g a b r s * h a b) := by
  calc ∑ a : Fin 4, ∑ b : Fin 4, (∑ r : Fin 4, ∑ s : Fin 4, f r s * g a b r s) * h a b
      = ∑ a : Fin 4, ∑ b : Fin 4, ∑ r : Fin 4, ∑ s : Fin 4, f r s * g a b r s * h a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_mul _ _ _
    _ = ∑ a : Fin 4, ∑ r : Fin 4, ∑ b : Fin 4, ∑ s : Fin 4, f r s * g a b r s * h a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ r : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, ∑ s : Fin 4, f r s * g a b r s * h a b :=
        Finset.sum_comm
    _ = ∑ r : Fin 4, ∑ a : Fin 4, ∑ s : Fin 4, ∑ b : Fin 4, f r s * g a b r s * h a b :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ r : Fin 4, ∑ s : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, f r s * g a b r s * h a b :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ r : Fin 4, ∑ s : Fin 4, f r s * (∑ a : Fin 4, ∑ b : Fin 4, g a b r s * h a b) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- Exact Pauli tomography identity: `|ψ⟩⟨ψ| = (1/4) ∑_{a,b} ⟨ψ|P_{a,b}|ψ⟩ P_{a,b}`. -/
theorem densityMatrix_eq_pauli_expansion (ψ : State) :
    densityMatrix ψ =
      (1 / 4 : ℂ) • ∑ a : Fin 4, ∑ b : Fin 4, pauliExp ψ a b • pauli2 a b := by
  ext i j
  simp only [densityMatrix, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, pauliExp]
  have hreord :
      ∑ a : Fin 4, ∑ b : Fin 4,
        (∑ r : Fin 4, ∑ s : Fin 4, star (ψ r) * pauli2 a b r s * ψ s) * pauli2 a b i j =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (∑ r : Fin 4, ∑ s : Fin 4, (star (ψ r) * ψ s) * pauli2 a b r s) * pauli2 a b i j := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  rw [hreord, sum4_swap_pauli (fun r s => star (ψ r) * ψ s)
    (fun a b r s => pauli2 a b r s) (fun a b => pauli2 a b i j)]
  simp_rw [pauli2_completeness]
  have hsum :
      ∑ r : Fin 4, ∑ s : Fin 4, star (ψ r) * ψ s * (if r = j ∧ s = i then (4 : ℂ) else 0) =
      star (ψ j) * ψ i * 4 := by
    have hinner : ∀ r : Fin 4,
        ∑ s : Fin 4, star (ψ r) * ψ s * (if r = j ∧ s = i then (4 : ℂ) else 0) =
        if r = j then star (ψ r) * ψ i * 4 else 0 := by
      intro r
      by_cases hr : r = j
      · subst hr; simp [Finset.sum_ite_eq']
      · simp [hr]
    simp_rw [hinner]
    simp [Finset.sum_ite_eq']
  rw [hsum]
  ring

/-- Two normalized pure states have the same density matrix iff they have identical `so6Edge` vectors. -/
theorem densityMatrix_eq_iff_so6Edge_eq {ψ φ : State} (hψ : IsNormalized ψ) (hφ : IsNormalized φ) :
    densityMatrix ψ = densityMatrix φ ↔ so6Edge ψ = so6Edge φ := by
  constructor
  · intro hρ
    have htr : ∀ a b : Fin 4, pauliExp ψ a b = pauliExp φ a b := by
      intro a b
      have h1 : ∀ χ : State, pauliExp χ a b =
          ∑ i : Fin 4, ∑ j : Fin 4, pauli2 a b i j * densityMatrix χ j i := by
        intro χ
        unfold pauliExp densityMatrix
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h1 ψ, h1 φ, hρ]
    ext e
    rw [so6Edge_eq_pauliExpRe, so6Edge_eq_pauliExpRe]
    congr 1
    unfold pauliExpRe
    rw [htr]
  · intro hso6
    have hexp : ∀ a b : Fin 4, pauliExp ψ a b = pauliExp φ a b := by
      intro a b
      rw [pauliExp_eq_ofReal ψ, pauliExp_eq_ofReal φ]
      congr 1
      by_cases hab : a = 0 ∧ b = 0
      · rcases hab with ⟨rfl, rfl⟩
        rw [pauliExpRe_II, pauliExpRe_II, hψ, hφ]
      · have hne : a ≠ 0 ∨ b ≠ 0 := by
          by_contra h; push Not at h; exact hab h
        rcases edgePauliLabel_surj hne with ⟨e, he⟩
        have heq := congrFun hso6 e
        have ha_eq : (edgePauliLabel e).1 = a := congrArg Prod.fst he
        have hb_eq : (edgePauliLabel e).2 = b := congrArg Prod.snd he
        rw [so6Edge_eq_pauliExpRe, so6Edge_eq_pauliExpRe, ha_eq, hb_eq] at heq
        have hs : (edgePauliSign e : ℝ) = 1 ∨ (edgePauliSign e : ℝ) = -1 := by
          fin_cases e <;> simp [edgePauliSign]
        rcases hs with h | h <;> rw [h] at heq <;> linarith
    rw [densityMatrix_eq_pauli_expansion ψ, densityMatrix_eq_pauli_expansion φ]
    simp_rw [hexp]

/-- Two normalized pure states have the same density matrix iff they differ by a unit global phase. -/
theorem densityMatrix_eq_iff_phase {ψ φ : State} (hψ : IsNormalized ψ) (_hφ : IsNormalized φ) :
    densityMatrix ψ = densityMatrix φ ↔ ∃ θ : ℂ, ‖θ‖ = 1 ∧ φ = θ • ψ := by
  constructor
  · intro hρ
    have hex : ∃ k : Fin 4, ψ k ≠ 0 := by
      by_contra h
      push Not at h
      have hz : normSq ψ = 0 := by
        unfold normSq
        exact Finset.sum_eq_zero fun i _ => by simp [h i]
      rw [hψ] at hz
      norm_num at hz
    rcases hex with ⟨k, hk⟩
    have hkk : ψ k * star (ψ k) = φ k * star (φ k) := congrFun (congrFun hρ k) k
    have hnorm_eq : ‖φ k‖ = ‖ψ k‖ := by
      have hsq : ‖ψ k‖ ^ 2 = ‖φ k‖ ^ 2 := by
        have hc : ((‖ψ k‖ ^ 2 : ℝ) : ℂ) = ((‖φ k‖ ^ 2 : ℝ) : ℂ) := by
          rw [← mul_star_self_eq_norm_sq, ← mul_star_self_eq_norm_sq, hkk]
        exact Complex.ofReal_injective hc
      nlinarith [norm_nonneg (ψ k), norm_nonneg (φ k)]
    refine ⟨φ k / ψ k, ?_, ?_⟩
    · rw [norm_div, hnorm_eq, div_self (norm_ne_zero_iff.mpr hk)]
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      have hik : ψ i * star (ψ k) = φ i * star (φ k) := congrFun (congrFun hρ i) k
      have hmul : φ i * (φ k * star (φ k)) = (φ k / ψ k * ψ i) * (ψ k * star (ψ k)) := by
        calc φ i * (φ k * star (φ k))
            = (φ i * star (φ k)) * φ k := by ring
          _ = (ψ i * star (ψ k)) * φ k := by rw [← hik]
          _ = (φ k / ψ k * ψ i) * (ψ k * star (ψ k)) := by field_simp [hk]
      rw [← hkk] at hmul
      have hpk_ne : ψ k * star (ψ k) ≠ 0 := mul_ne_zero hk (star_ne_zero.mpr hk)
      exact mul_right_cancel₀ hpk_ne hmul
  · rintro ⟨θ, hθ, rfl⟩
    ext i j
    simp only [densityMatrix, Pi.smul_apply, smul_eq_mul, star_mul]
    have hθmul : θ * star θ = 1 := by
      rw [mul_star_self_eq_norm_sq, hθ]; norm_num
    rw [show ψ i * star (ψ j) = (θ * star θ) * (ψ i * star (ψ j)) by rw [hθmul, one_mul]]
    ring

/-! ### Part 3: The Two-Qubit Clifford Group and Realizing `B₆⁺` via Clifford Unitaries -/

private lemma mat_mul_eq_one_comm {A B : Matrix (Fin 4) (Fin 4) ℂ} (h : A * B = 1) :
    B * A = 1 := by
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr fun h0 => by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h1
    exact one_ne_zero h1.symm
  have hinv : B⁻¹ = A := Matrix.inv_eq_left_inv h
  rw [← hinv]
  exact Matrix.mul_nonsing_inv B hdet

/-- Textbook definition of the two-qubit Clifford group: a `4 × 4` complex unitary matrix
    normalizing the two-qubit Pauli group `{±1, ±i} · P₂`. -/
def IsClifford2 (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Uᴴ * U = 1 ∧
  ∀ a b : Fin 4, ∃ c d : Fin 4, ∃ k : Fin 4,
    U * pauli2 a b * Uᴴ = (Complex.I ^ k.val) • pauli2 c d

lemma IsClifford2.mul_conjTranspose {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U) :
    U * Uᴴ = 1 :=
  mat_mul_eq_one_comm hU.1

lemma IsClifford2.one : IsClifford2 (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨by simp, fun a b => ⟨a, b, 0, by simp⟩⟩

lemma pow_I_mod4 (n : ℕ) : (Complex.I : ℂ) ^ n = Complex.I ^ (n % 4) := by
  have h4 : (Complex.I : ℂ) ^ 4 = 1 := by
    calc (Complex.I : ℂ) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by rw [Complex.I_sq]
      _ = 1 := by norm_num
  conv_lhs => rw [← Nat.div_add_mod n 4]
  rw [pow_add, pow_mul, h4, one_pow, one_mul]

lemma IsClifford2.mul {U V : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U) (hV : IsClifford2 V) :
    IsClifford2 (U * V) := by
  refine ⟨?_, ?_⟩
  · calc (U * V)ᴴ * (U * V)
        = Vᴴ * (Uᴴ * U) * V := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Vᴴ * 1 * V := by rw [hU.1]
      _ = 1 := by simpa using hV.1
  · intro a b
    rcases hV.2 a b with ⟨c₁, d₁, k₁, h1⟩
    rcases hU.2 c₁ d₁ with ⟨c₂, d₂, k₂, h2⟩
    refine ⟨c₂, d₂, ⟨(k₁.val + k₂.val) % 4, Nat.mod_lt _ (by omega)⟩, ?_⟩
    calc (U * V) * pauli2 a b * (U * V)ᴴ
        = U * (V * pauli2 a b * Vᴴ) * Uᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = U * ((Complex.I ^ k₁.val) • pauli2 c₁ d₁) * Uᴴ := by rw [h1]
      _ = (Complex.I ^ k₁.val) • (U * pauli2 c₁ d₁ * Uᴴ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (Complex.I ^ k₁.val) • ((Complex.I ^ k₂.val) • pauli2 c₂ d₂) := by rw [h2]
      _ = (Complex.I ^ ((k₁.val + k₂.val) % 4)) • pauli2 c₂ d₂ := by
          rw [smul_smul, ← pow_add, pow_I_mod4]

lemma pauli1_trace_mul (a b : Fin 4) :
    Matrix.trace (pauli1 a * pauli1 b) = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli1, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]

lemma pauli2_trace_mul (a₁ b₁ a₂ b₂ : Fin 4) :
    Matrix.trace (pauli2 a₁ b₁ * pauli2 a₂ b₂) = if a₁ = a₂ ∧ b₁ = b₂ then 4 else 0 := by
  have htr : Matrix.trace (pauli2 a₁ b₁ * pauli2 a₂ b₂) =
      Matrix.trace (pauli1 a₁ * pauli1 a₂) * Matrix.trace (pauli1 b₁ * pauli1 b₂) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_four, Fin.sum_univ_two,
      pauli2_mul_apply_kron]
    norm_num
    ring
  rw [htr, pauli1_trace_mul, pauli1_trace_mul]
  by_cases ha : a₁ = a₂
  · by_cases hb : b₁ = b₂
    · simp only [ha, hb, and_self, ite_true]; norm_num
    · simp [ha, hb]
  · simp [ha]

lemma norm_pow_I (k : ℕ) : ‖(Complex.I : ℂ) ^ k‖ = 1 := by
  rw [norm_pow, Complex.norm_I, one_pow]

/-- Every Clifford conjugation permutes the 16 Pauli labels bijectively. -/
lemma IsClifford2.pauli_perm {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U) :
    ∃ (σ : Equiv.Perm (Fin 4 × Fin 4)) (k : Fin 4 × Fin 4 → Fin 4),
      ∀ p : Fin 4 × Fin 4,
        U * pauli2 p.1 p.2 * Uᴴ = (Complex.I ^ (k p).val) • pauli2 (σ p).1 (σ p).2 := by
  have hchoice : ∀ p : Fin 4 × Fin 4, ∃ q : Fin 4 × Fin 4, ∃ k : Fin 4,
      U * pauli2 p.1 p.2 * Uᴴ = (Complex.I ^ k.val) • pauli2 q.1 q.2 :=
    fun p => by
      rcases hU.2 p.1 p.2 with ⟨c, d, k, hk⟩
      exact ⟨(c, d), k, hk⟩
  choose f k hfk using hchoice
  have hinj : Function.Injective f := by
    intro p₁ p₂ heq
    by_contra hne
    have htr1 : Matrix.trace ((U * pauli2 p₁.1 p₁.2 * Uᴴ) * (U * pauli2 p₂.1 p₂.2 * Uᴴ)) = 0 := by
      have hmul : (U * pauli2 p₁.1 p₁.2 * Uᴴ) * (U * pauli2 p₂.1 p₂.2 * Uᴴ) =
          U * (pauli2 p₁.1 p₁.2 * pauli2 p₂.1 p₂.2) * Uᴴ := by
        calc (U * pauli2 p₁.1 p₁.2 * Uᴴ) * (U * pauli2 p₂.1 p₂.2 * Uᴴ)
            = U * pauli2 p₁.1 p₁.2 * (Uᴴ * U) * pauli2 p₂.1 p₂.2 * Uᴴ := by
              simp only [Matrix.mul_assoc]
          _ = U * pauli2 p₁.1 p₁.2 * 1 * pauli2 p₂.1 p₂.2 * Uᴴ := by rw [hU.1]
          _ = U * (pauli2 p₁.1 p₁.2 * pauli2 p₂.1 p₂.2) * Uᴴ := by simp [Matrix.mul_assoc]
      rw [hmul, Matrix.trace_mul_cycle, hU.1, Matrix.one_mul, pauli2_trace_mul]
      have hnot : ¬ (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
      simp [hnot]
    rw [hfk p₁, hfk p₂, heq, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      pauli2_trace_mul] at htr1
    simp only [and_self, ite_true] at htr1
    have hne0 : (Complex.I ^ (k p₁).val : ℂ) * ((Complex.I ^ (k p₂).val : ℂ) * 4) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      apply mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      norm_num
    exact hne0 htr1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), k, hfk⟩

lemma IsClifford2.conjTranspose {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U) :
    IsClifford2 Uᴴ := by
  refine ⟨by simpa using hU.mul_conjTranspose, ?_⟩
  rcases hU.pauli_perm with ⟨σ, k, hσ⟩
  intro a b
  set p := σ.symm (a, b)
  have hp : σ p = (a, b) := σ.apply_symm_apply (a, b)
  have h1 := hσ p
  rw [hp] at h1
  refine ⟨p.1, p.2, ⟨(4 - (k p).val) % 4, Nat.mod_lt _ (by omega)⟩, ?_⟩
  have hinv : Uᴴ * (U * pauli2 p.1 p.2 * Uᴴ) * U = pauli2 p.1 p.2 := by
    calc Uᴴ * (U * pauli2 p.1 p.2 * Uᴴ) * U
        = (Uᴴ * U) * pauli2 p.1 p.2 * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = 1 * pauli2 p.1 p.2 * 1 := by rw [hU.1]
      _ = pauli2 p.1 p.2 := by simp
  rw [h1, Matrix.mul_smul, Matrix.smul_mul] at hinv
  have hc : (Complex.I : ℂ) ^ ((4 - (k p).val) % 4) * Complex.I ^ (k p).val = 1 := by
    rw [← pow_I_mod4, ← pow_add]
    have hle : (k p).val ≤ 4 := by omega
    rw [Nat.sub_add_cancel hle, pow_I_mod4]
    norm_num
  calc Uᴴ * pauli2 a b * Uᴴᴴ
      = Uᴴ * pauli2 a b * U := by simp
    _ = ((Complex.I : ℂ) ^ ((4 - (k p).val) % 4) * Complex.I ^ (k p).val) • (Uᴴ * pauli2 a b * U) := by
        rw [hc, one_smul]
    _ = (Complex.I ^ ((4 - (k p).val) % 4)) • ((Complex.I ^ (k p).val) • (Uᴴ * pauli2 a b * U)) := by
        rw [smul_smul]
    _ = (Complex.I ^ ((4 - (k p).val) % 4)) • pauli2 p.1 p.2 := by rw [hinv]

/-- Complex inner product `⟨u | v⟩ = ∑_i conj(u_i) v_i` on `State = Fin 4 → ℂ`. -/
def innerState (u v : State) : ℂ :=
  ∑ i : Fin 4, star (u i) * v i

lemma innerState_self_eq_normSq (ψ : State) :
    innerState ψ ψ = ((normSq ψ : ℝ) : ℂ) := by
  unfold innerState normSq
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact star_mul_self_eq_norm_sq (ψ i)

lemma innerState_mulVec_left (M : Matrix (Fin 4) (Fin 4) ℂ) (u v : State) :
    innerState (M *ᵥ u) v = innerState u (Mᴴ *ᵥ v) := by
  unfold innerState
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma innerState_unitary {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : Uᴴ * U = 1) (u v : State) :
    innerState (U *ᵥ u) (U *ᵥ v) = innerState u v := by
  rw [innerState_mulVec_left, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

lemma pauliExp_eq_innerState (ψ : State) (a b : Fin 4) :
    pauliExp ψ a b = innerState ψ (pauli2 a b *ᵥ ψ) := by
  unfold pauliExp innerState
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma pauliExp_mulVec (U : Matrix (Fin 4) (Fin 4) ℂ) (ψ : State) (a b : Fin 4) :
    pauliExp (U *ᵥ ψ) a b = innerState ψ ((Uᴴ * pauli2 a b * U) *ᵥ ψ) := by
  rw [pauliExp_eq_innerState, innerState_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

lemma IsClifford2.preserves_isNormalized {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U)
    {ψ : State} (hψ : IsNormalized ψ) : IsNormalized (U *ᵥ ψ) := by
  unfold IsNormalized
  have h := innerState_unitary hU.1 ψ ψ
  rw [innerState_self_eq_normSq, innerState_self_eq_normSq] at h
  exact (Complex.ofReal_injective h).trans hψ

lemma IsClifford2.densityMatrix_mulVec (U : Matrix (Fin 4) (Fin 4) ℂ) (ψ : State) :
    densityMatrix (U *ᵥ ψ) = U * densityMatrix ψ * Uᴴ := by
  ext i j
  simp only [densityMatrix, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma IsClifford2.preserves_pauliMoment {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U)
    (ψ : State) (α : ℝ) : pauliMoment (U *ᵥ ψ) α = pauliMoment ψ α := by
  rcases hU.conjTranspose.pauli_perm with ⟨σ, k, hσ⟩
  unfold pauliMoment
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv σ _ _ fun p => ?_
  have h1 : Uᴴ * pauli2 p.1 p.2 * U = (Complex.I ^ (k p).val) • pauli2 (σ p).1 (σ p).2 := by
    simpa using hσ p
  rw [pauliExp_mulVec, h1, Matrix.smul_mulVec]
  have hlin : innerState ψ ((Complex.I ^ (k p).val) • (pauli2 (σ p).1 (σ p).2 *ᵥ ψ)) =
      (Complex.I ^ (k p).val) * pauliExp ψ (σ p).1 (σ p).2 := by
    rw [pauliExp_eq_innerState]
    unfold innerState
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlin, norm_mul, norm_pow_I, one_mul]

lemma IsClifford2.preserves_sre {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U)
    (ψ : State) (α : ℝ) : sre (U *ᵥ ψ) α = sre ψ α := by
  unfold sre
  rw [hU.preserves_pauliMoment]

lemma phase_preserves_isNormalized {θ : ℂ} (hθ : ‖θ‖ = 1) {ψ : State} (hψ : IsNormalized ψ) :
    IsNormalized (θ • ψ) := by
  unfold IsNormalized normSq at hψ ⊢
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hθ, one_mul]
  exact hψ

lemma phase_preserves_sre {θ : ℂ} (hθ : ‖θ‖ = 1) (ψ : State) (α : ℝ) :
    sre (θ • ψ) α = sre ψ α := by
  have hexp : ∀ a b : Fin 4, pauliExp (θ • ψ) a b = pauliExp ψ a b := by
    intro a b
    have hθmul : star θ * θ = 1 := by
      rw [star_mul_self_eq_norm_sq, hθ]; norm_num
    unfold pauliExp
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul]
    have hrew : star (ψ i) * star θ * pauli2 a b i j * (θ * ψ j) =
        (star θ * θ) * (star (ψ i) * pauli2 a b i j * ψ j) := by ring
    rw [hrew, hθmul, one_mul]
  unfold sre pauliMoment
  simp_rw [hexp]

/-! #### Explicit 5-Generator Clifford Lift of `B₆⁺` -/

/-- The 5 adjacent edges `(k, k+1)` in `K₆`: `0 ↦ (0,1)`, `1 ↦ (1,2)`, `2 ↦ (2,3)`,
    `3 ↦ (3,4)`, `4 ↦ (4,5)`. -/
def adjEdge : Fin 5 → Fin 15
  | 0 => 0
  | 1 => 5
  | 2 => 9
  | 3 => 12
  | 4 => 14

/-- The 5 adjacent `90°` signed-swap generators of `B₆⁺`. -/
def b6Gen (k : Fin 5) : B6Plus :=
  let i : Fin 6 := ⟨k.val, by omega⟩
  let j : Fin 6 := ⟨k.val + 1, by omega⟩
  ⟨Equiv.swap i j,
   fun r => decide (r = i),
   by fin_cases k <;> decide⟩

/-- The 5 explicit `π/2` Pauli-rotation Clifford matrices lifting `b6Gen 0..4`. -/
noncomputable def cliffGen (k : Fin 5) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 + Complex.I • edgeSignedPauli (adjEdge k))

lemma edgeSignedPauli_conjTranspose (e : Fin 15) : (edgeSignedPauli e)ᴴ = edgeSignedPauli e := by
  unfold edgeSignedPauli
  rw [Matrix.conjTranspose_smul, pauli2_conjTranspose]
  simp

lemma edgeSignedPauli_sq (e : Fin 15) : edgeSignedPauli e * edgeSignedPauli e = 1 := by
  unfold edgeSignedPauli
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli2_sq]
  have hs : ((edgePauliSign e : ℂ) * (edgePauliSign e : ℂ)) = 1 := by
    fin_cases e <;> simp [edgePauliSign]
  rw [hs, one_smul]

/-- Generic conjugation formula for a `π/2` rotation `U = (1/√2)(1 + i P)` with `Pᴴ = P, P² = 1`. -/
lemma pi_half_rot_unitary {P : Matrix (Fin 4) (Fin 4) ℂ} (hH : Pᴴ = P) (hsq : P * P = 1) :
    let U := ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 + Complex.I • P)
    Uᴴ * U = 1 := by
  intro U
  have hUdag : Uᴴ = ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 - Complex.I • P) := by
    dsimp only [U]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hH]
    simp [sub_eq_add_neg]
  rw [hUdag, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    have hr : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, hr]; norm_num
  have hI2 : Complex.I * Complex.I = -1 := by simp [← sq]
  have hprod : (1 - Complex.I • P) * (1 + Complex.I • P) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simp only [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, hI2]
    ext i j; simp; ring
  rw [hc, hprod, smul_smul]
  norm_num

lemma pi_half_rot_conj_comm {P Q : Matrix (Fin 4) (Fin 4) ℂ}
    (hH : Pᴴ = P) (hsq : P * P = 1) (hcomm : P * Q = Q * P) :
    let U := ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 + Complex.I • P)
    U * Q * Uᴴ = Q ∧ Uᴴ * Q * U = Q := by
  intro U
  have hunit := pi_half_rot_unitary hH hsq
  have hunit2 : U * Uᴴ = 1 := mat_mul_eq_one_comm hunit
  have hUQ : U * Q = Q * U := by
    dsimp only [U]
    simp [Matrix.add_mul, Matrix.mul_add, hcomm]
  have hUdagQ : Uᴴ * Q = Q * Uᴴ := by
    have hUdag : Uᴴ = ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 - Complex.I • P) := by
      dsimp only [U]
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
        Matrix.conjTranspose_smul, hH]
      simp [sub_eq_add_neg]
    rw [hUdag]
    simp [Matrix.sub_mul, Matrix.mul_sub, hcomm]
  constructor
  · rw [hUQ, Matrix.mul_assoc, hunit2, Matrix.mul_one]
  · rw [hUdagQ, Matrix.mul_assoc, hunit, Matrix.mul_one]

lemma pi_half_rot_conj_anticomm {P Q : Matrix (Fin 4) (Fin 4) ℂ}
    (hH : Pᴴ = P) (hsq : P * P = 1) (hanti : P * Q = -(Q * P)) :
    let U := ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 + Complex.I • P)
    U * Q * Uᴴ = Complex.I • (P * Q) ∧ Uᴴ * Q * U = (-Complex.I) • (P * Q) := by
  intro U
  have hUdag : Uᴴ = ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 - Complex.I • P) := by
    dsimp only [U]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hH]
    simp [sub_eq_add_neg]
  have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    have hr : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, hr]; norm_num
  have hQP : Q * P = -(P * Q) := by rw [hanti, neg_neg]
  have hPQP : P * Q * P = -Q := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_neg, ← Matrix.mul_assoc, hsq, Matrix.one_mul]
  have hI2 : Complex.I * Complex.I = -1 := by simp [← sq]
  constructor
  · dsimp only [U]; rw [hUdag]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hc]
    have hcalc : (1 + Complex.I • P) * Q * (1 - Complex.I • P) = (2 * Complex.I) • (P * Q) := by
      simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQP, hPQP, hI2]
      ext i j; simp; ring
    rw [hcalc, smul_smul]
    congr 1; ring
  · dsimp only [U]; rw [hUdag]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hc]
    have hcalc : (1 - Complex.I • P) * Q * (1 + Complex.I • P) = (-2 * Complex.I) • (P * Q) := by
      simp only [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQP, hPQP, hI2]
      ext i j; simp; ring
    rw [hcalc, smul_smul]
    congr 1; ring

/-- Product of any two single-qubit Pauli matrices is a `±1, ±i` multiple of a single-qubit Pauli. -/
def pauli1MulLabel : Fin 4 → Fin 4 → Fin 4
  | 0, b => b
  | a, 0 => a
  | 1, 1 => 0 | 1, 2 => 3 | 1, 3 => 2
  | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1
  | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0
  | _, _ => 0

def pauli1MulPow : Fin 4 → Fin 4 → Fin 4
  | 1, 2 => 1 | 2, 3 => 1 | 3, 1 => 1
  | 2, 1 => 3 | 3, 2 => 3 | 1, 3 => 3
  | _, _ => 0

lemma pauli1_mul_eq (a b : Fin 4) :
    pauli1 a * pauli1 b = (Complex.I ^ (pauli1MulPow a b).val) • pauli1 (pauli1MulLabel a b) := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli1MulLabel, pauli1MulPow, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

lemma pauli2_mul_eq (a₁ b₁ a₂ b₂ : Fin 4) :
    pauli2 a₁ b₁ * pauli2 a₂ b₂ =
      (Complex.I ^ (((pauli1MulPow a₁ a₂).val + (pauli1MulPow b₁ b₂).val) % 4)) •
        pauli2 (pauli1MulLabel a₁ a₂) (pauli1MulLabel b₁ b₂) := by
  ext i j
  rw [pauli2_mul_apply_kron, pauli1_mul_eq, pauli1_mul_eq]
  simp only [Matrix.smul_apply, smul_eq_mul, pauli2]
  rw [← pow_I_mod4, pow_add]
  ring

/-- Each of the 5 generators `cliffGen k` belongs to the two-qubit Clifford group. -/
theorem isClifford2_cliffGen (k : Fin 5) : IsClifford2 (cliffGen k) := by
  set e₀ := adjEdge k
  set P := edgeSignedPauli e₀
  have hH : Pᴴ = P := edgeSignedPauli_conjTranspose e₀
  have hsq : P * P = 1 := edgeSignedPauli_sq e₀
  refine ⟨pi_half_rot_unitary hH hsq, ?_⟩
  intro a b
  set p₀ := edgePauliLabel e₀
  set s₀ : Fin 4 := if edgePauliSign e₀ = 1 then 0 else 2
  have hs₀ : (edgePauliSign e₀ : ℂ) = Complex.I ^ s₀.val := by
    dsimp only [s₀, e₀]
    fin_cases k <;> simp [adjEdge, edgePauliSign, Complex.I_sq]
  cases hb : pauli2CommBool p₀ (a, b)
  · have hantiQ : pauli2 p₀.1 p₀.2 * pauli2 a b = -(pauli2 a b * pauli2 p₀.1 p₀.2) :=
      (pauli2_anticommute_iff_bool p₀ (a, b)).mpr hb
    have hanti : P * pauli2 a b = -(pauli2 a b * P) := by
      dsimp only [P, edgeSignedPauli]
      rw [Matrix.smul_mul, Matrix.mul_smul, hantiQ, smul_neg]
    have hconj := (pi_half_rot_conj_anticomm hH hsq hanti).1
    refine ⟨pauli1MulLabel p₀.1 a, pauli1MulLabel p₀.2 b,
      ⟨(1 + s₀.val + (pauli1MulPow p₀.1 a).val + (pauli1MulPow p₀.2 b).val) % 4,
        Nat.mod_lt _ (by omega)⟩, ?_⟩
    dsimp only [cliffGen]
    rw [hconj]
    dsimp only [P, edgeSignedPauli]
    rw [Matrix.smul_mul, hs₀, pauli2_mul_eq, smul_smul, smul_smul]
    congr 1
    rw [← pow_I_mod4 ((pauli1MulPow p₀.1 a).val + (pauli1MulPow p₀.2 b).val),
      ← pow_I_mod4 (1 + s₀.val + (pauli1MulPow p₀.1 a).val + (pauli1MulPow p₀.2 b).val)]
    simp only [pow_add, pow_one]
    ring
  · have hcommQ : pauli2 p₀.1 p₀.2 * pauli2 a b = pauli2 a b * pauli2 p₀.1 p₀.2 :=
      (pauli2_commute_iff_bool p₀ (a, b)).mpr hb
    have hcomm : P * pauli2 a b = pauli2 a b * P := by
      dsimp only [P, edgeSignedPauli]
      rw [Matrix.smul_mul, Matrix.mul_smul, hcommQ]
    have hconj := (pi_half_rot_conj_comm hH hsq hcomm).1
    refine ⟨a, b, 0, ?_⟩
    simpa [cliffGen] using hconj

private lemma cliffGen_anticomm_label_check (k : Fin 5) (e : Fin 15)
    (hb : pauli2CommBool (edgePauliLabel (adjEdge k)) (edgePauliLabel e) = false) :
    pauli1MulLabel (edgePauliLabel (adjEdge k)).1 (edgePauliLabel e).1 =
      (edgePauliLabel (edgeImgFun (b6Gen k) e)).1 ∧
    pauli1MulLabel (edgePauliLabel (adjEdge k)).2 (edgePauliLabel e).2 =
      (edgePauliLabel (edgeImgFun (b6Gen k) e)).2 := by
  revert k e hb; decide

private lemma cliffGen_anticomm_sign_check (k : Fin 5) (e : Fin 15)
    (hb : pauli2CommBool (edgePauliLabel (adjEdge k)) (edgePauliLabel e) = false) :
    (edgePauliSign (adjEdge k) * edgePauliSign e *
      (if (((pauli1MulPow (edgePauliLabel (adjEdge k)).1 (edgePauliLabel e).1).val +
           (pauli1MulPow (edgePauliLabel (adjEdge k)).2 (edgePauliLabel e).2).val) % 4) = 1
       then 1 else -1) : ℤ) =
    edgeSgnFun (b6Gen k) e * edgePauliSign (edgeImgFun (b6Gen k) e) ∧
    ((((pauli1MulPow (edgePauliLabel (adjEdge k)).1 (edgePauliLabel e).1).val +
       (pauli1MulPow (edgePauliLabel (adjEdge k)).2 (edgePauliLabel e).2).val) % 4) = 1 ∨
     (((pauli1MulPow (edgePauliLabel (adjEdge k)).1 (edgePauliLabel e).1).val +
       (pauli1MulPow (edgePauliLabel (adjEdge k)).2 (edgePauliLabel e).2).val) % 4) = 3) := by
  revert k e hb; decide

private lemma cliffGen_comm_fix_check (k : Fin 5) (e : Fin 15)
    (hb : pauli2CommBool (edgePauliLabel (adjEdge k)) (edgePauliLabel e) = true) :
    edgeImgFun (b6Gen k) e = e ∧ edgeSgnFun (b6Gen k) e = 1 := by
  revert k e hb; decide

/-- Symbolic matrix check: `(cliffGen k)ᴴ * Q(e) * (cliffGen k) = sgn * Q(e')`. -/
lemma cliffGen_conj_edgeSignedPauli (k : Fin 5) (e : Fin 15) :
    (cliffGen k)ᴴ * edgeSignedPauli e * cliffGen k =
      (edgeSgnFun (b6Gen k) e : ℂ) • edgeSignedPauli (edgeImgFun (b6Gen k) e) := by
  set e₀ := adjEdge k
  set P := edgeSignedPauli e₀
  set Q := edgeSignedPauli e
  have hH : Pᴴ = P := edgeSignedPauli_conjTranspose e₀
  have hsq : P * P = 1 := edgeSignedPauli_sq e₀
  cases hb : pauli2CommBool (edgePauliLabel e₀) (edgePauliLabel e)
  · have hanti : P * Q = -(Q * P) := by
      have h1 := (pauli2_anticommute_iff_bool (edgePauliLabel e₀) (edgePauliLabel e)).mpr hb
      dsimp only [P, Q, edgeSignedPauli]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, smul_neg]
      rw [mul_comm (edgePauliSign e₀ : ℂ)]
    have hconj := (pi_half_rot_conj_anticomm hH hsq hanti).2
    change (cliffGen k)ᴴ * Q * cliffGen k = _
    dsimp only [cliffGen]; rw [hconj]
    have hchk := cliffGen_anticomm_label_check k e hb
    rcases cliffGen_anticomm_sign_check k e hb with ⟨heq_z, hpow13⟩
    dsimp only [P, Q, edgeSignedPauli]
    rw [Matrix.smul_mul, Matrix.mul_smul, pauli2_mul_eq]
    simp only [smul_smul]
    rw [hchk.1, hchk.2]
    congr 1
    have hpow_c : (-Complex.I) * Complex.I ^
        (((pauli1MulPow (edgePauliLabel e₀).1 (edgePauliLabel e).1).val +
          (pauli1MulPow (edgePauliLabel e₀).2 (edgePauliLabel e).2).val) % 4) =
        ((if (((pauli1MulPow (edgePauliLabel e₀).1 (edgePauliLabel e).1).val +
              (pauli1MulPow (edgePauliLabel e₀).2 (edgePauliLabel e).2).val) % 4) = 1
          then (1 : ℤ) else -1) : ℂ) := by
      rcases hpow13 with h1 | h3
      · rw [h1]; simp
      · rw [h3]; simp [pow_succ]
    have hcast := congrArg (Int.cast (R := ℂ)) heq_z
    push_cast at hcast
    have hrearr :
        -Complex.I * ((edgePauliSign e₀ : ℂ) * ((edgePauliSign e : ℂ) *
          Complex.I ^ (((pauli1MulPow (edgePauliLabel e₀).1 (edgePauliLabel e).1).val +
            (pauli1MulPow (edgePauliLabel e₀).2 (edgePauliLabel e).2).val) % 4))) =
        (edgePauliSign e₀ : ℂ) * (edgePauliSign e : ℂ) *
          ((-Complex.I) * Complex.I ^
            (((pauli1MulPow (edgePauliLabel e₀).1 (edgePauliLabel e).1).val +
              (pauli1MulPow (edgePauliLabel e₀).2 (edgePauliLabel e).2).val) % 4)) := by ring
    rw [hrearr, hpow_c]
    push_cast
    exact hcast
  · have hcomm : P * Q = Q * P := by
      have h1 := (pauli2_commute_iff_bool (edgePauliLabel e₀) (edgePauliLabel e)).mpr hb
      dsimp only [P, Q, edgeSignedPauli]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1]
      rw [mul_comm (edgePauliSign e₀ : ℂ)]
    have hconj := (pi_half_rot_conj_comm hH hsq hcomm).2
    have hfix := cliffGen_comm_fix_check k e hb
    change (cliffGen k)ᴴ * Q * cliffGen k = _
    dsimp only [cliffGen]; rw [hconj, hfix.1, hfix.2]; simp [Q]

lemma so6Edge_cliffGen (k : Fin 5) (ψ : State) :
    so6Edge (cliffGen k *ᵥ ψ) = actB6Vec (b6Gen k) (so6Edge ψ) := by
  ext e
  rw [actB6Vec_apply, so6Edge_eq_pauliExpRe, so6Edge_eq_pauliExpRe]
  have hc : ((edgePauliSign e : ℂ) * pauliExp (cliffGen k *ᵥ ψ) (edgePauliLabel e).1 (edgePauliLabel e).2) =
      ((edgeSgnFun (b6Gen k) e : ℂ) * ((edgePauliSign (edgeImgFun (b6Gen k) e) : ℂ) *
        pauliExp ψ (edgePauliLabel (edgeImgFun (b6Gen k) e)).1 (edgePauliLabel (edgeImgFun (b6Gen k) e)).2)) := by
    have h1 : (edgePauliSign e : ℂ) * pauliExp (cliffGen k *ᵥ ψ) (edgePauliLabel e).1 (edgePauliLabel e).2 =
        innerState ψ (((cliffGen k)ᴴ * edgeSignedPauli e * cliffGen k) *ᵥ ψ) := by
      rw [pauliExp_mulVec]
      unfold edgeSignedPauli innerState
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [h1, cliffGen_conj_edgeSignedPauli]
    unfold edgeSignedPauli innerState
    rw [pauliExp_eq_innerState]
    unfold innerState
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hre := congrArg Complex.re hc
  rw [pauliExp_eq_ofReal (cliffGen k *ᵥ ψ), pauliExp_eq_ofReal ψ] at hre
  simpa using hre

/-- Every element of `B₆⁺` lies in the subgroup generated by the 5 adjacent generators `b6Gen 0..4`. -/
lemma b6Plus_mem_closure_b6Gen (g : B6Plus) :
    g ∈ Subgroup.closure (Set.range b6Gen) := by
  set H := Subgroup.closure (Set.range b6Gen)
  have hgen : ∀ k : Fin 5, b6Gen k ∈ H := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  -- Step 1: Adjacent double-sign-flips `(b6Gen k)^2` lie in `H`
  have hflipAdj : ∀ k : Fin 5,
      ∃ f : B6Plus, f ∈ H ∧ f.perm = 1 ∧
        ∀ i : Fin 6, f.sgn i = (decide (i.val = k.val) || decide (i.val = k.val + 1)) := by
    intro k
    refine ⟨b6Gen k * b6Gen k, H.mul_mem (hgen k) (hgen k), ?_, ?_⟩
    · fin_cases k <;> decide
    · intro i; fin_cases k <;> fin_cases i <;> decide
  -- Step 2: Any permutation `σ : Equiv.Perm (Fin 6)` is `h.perm` for some `h ∈ H`.
  have hperm_lift : ∀ σ : Equiv.Perm (Fin 6), ∃ h ∈ H, h.perm = σ := by
    have hswap_adj : ∀ k : Fin 5, ∃ h ∈ H,
        h.perm = Equiv.swap (⟨k.val, by omega⟩ : Fin 6) ⟨k.val + 1, by omega⟩ :=
      fun k => ⟨b6Gen k, hgen k, rfl⟩
    have hswap : ∀ a b : Fin 6, ∃ h ∈ H, h.perm = Equiv.swap a b := by
      have hlt : ∀ d : ℕ, ∀ a b : Fin 6, b.val - a.val = d → a < b →
          ∃ h ∈ H, h.perm = Equiv.swap a b := by
        intro d
        induction d with
        | zero =>
          intro a b h1 h2
          have hlt_v : a.val < b.val := h2
          omega
        | succ d ih =>
          intro a b hd hab
          have ha_lt : a.val < 6 := a.isLt
          have hb_lt : b.val < 6 := b.isLt
          have hab_v : a.val < b.val := hab
          by_cases h1 : d = 0
          · subst h1
            have hba : b.val = a.val + 1 := by omega
            have hb : b = ⟨a.val + 1, by omega⟩ := Fin.ext hba
            rw [hb]
            exact hswap_adj ⟨a.val, by omega⟩
          · set c : Fin 6 := ⟨b.val - 1, by omega⟩
            have hac : a < c := by show a.val < b.val - 1; omega
            have hcb : c.val + 1 = b.val := by dsimp only [c]; omega
            rcases ih a c (by dsimp only [c]; omega) hac with ⟨h1, hh1, hp1⟩
            rcases hswap_adj ⟨c.val, by dsimp only [c]; omega⟩ with ⟨h2, hh2, hp2⟩
            refine ⟨h2 * h1 * h2, H.mul_mem (H.mul_mem hh2 hh1) hh2, ?_⟩
            have hcb_eq : (⟨c.val + 1, by omega⟩ : Fin 6) = b := Fin.ext hcb
            rw [hcb_eq] at hp2
            apply Equiv.ext; intro x
            change h2.perm (h1.perm (h2.perm x)) = Equiv.swap a b x
            rw [hp1, hp2]
            have hne_ab : a ≠ b := ne_of_lt hab
            have hne_ac : a ≠ c := ne_of_lt hac
            have hne_cb : c ≠ b := by intro he; rw [he] at hcb; omega
            by_cases hx1 : x = a
            · subst hx1; simp [Equiv.swap_apply_def, hne_ab, hne_ac]
            · by_cases hx2 : x = b
              · subst hx2; simp [Equiv.swap_apply_def, hne_ab, hne_ac]
              · by_cases hx3 : x = c
                · subst hx3; simp [Equiv.swap_apply_def, hne_ab.symm, hne_ac.symm, hne_cb, hne_cb.symm]
                · simp [Equiv.swap_apply_def, hx1, hx2, hx3]
      intro a b
      rcases lt_trichotomy a b with h1 | rfl | h2
      · exact hlt (b.val - a.val) a b rfl h1
      · exact ⟨1, H.one_mem, by simp; rfl⟩
      · rcases hlt (a.val - b.val) b a rfl h2 with ⟨h, hh, hp⟩
        exact ⟨h, hh, hp.trans (Equiv.swap_comm b a)⟩
    intro σ
    refine Equiv.Perm.swap_induction_on σ ⟨1, H.one_mem, rfl⟩ ?_
    intro τ a b _ ⟨hτ, hhτ, hpτ⟩
    rcases hswap a b with ⟨hs, hhs, hps⟩
    refine ⟨hτ * hs, H.mul_mem hhτ hhs, ?_⟩
    apply Equiv.ext; intro x
    change hs.perm (hτ.perm x) = (Equiv.swap a b * τ) x
    rw [hps, hpτ]; rfl
  -- Step 3: Lift `g.perm` to `h ∈ H`, then `d := g * h⁻¹` has `d.perm = 1`!
  rcases hperm_lift g.perm with ⟨h, hh, hperm⟩
  set d : B6Plus := g * h⁻¹
  have hd_perm : d.perm = 1 := by
    apply Equiv.ext; intro x
    change h.perm.symm (g.perm x) = x
    rw [hperm]; exact g.perm.symm_apply_apply x
  have hdiag_mem : ∀ x : B6Plus, x.perm = 1 → x ∈ H := by
    intro x hx
    have hclean : ∀ (k : Fin 5) (y : B6Plus), y.perm = 1 →
        ∃ f ∈ H, f.perm = 1 ∧ (f * y).perm = 1 ∧
          (f * y).sgn ⟨k.val, by omega⟩ = false ∧
          (∀ i : Fin 6, i.val < k.val → (f * y).sgn i = y.sgn i) := by
      intro k y hy
      by_cases hk : y.sgn ⟨k.val, by omega⟩ = false
      · exact ⟨1, H.one_mem, rfl, by simpa using hy, by simpa using hk, fun _ _ => by simp⟩
      · have hkt : y.sgn ⟨k.val, by omega⟩ = true := by
          cases h : y.sgn ⟨k.val, by omega⟩ <;> [exact absurd h hk; rfl]
        rcases hflipAdj k with ⟨f, hf, hfp, hfs⟩
        refine ⟨f, hf, hfp, ?_, ?_, ?_⟩
        · apply Equiv.ext; intro i; change y.perm (f.perm i) = i; rw [hfp, hy]; rfl
        · change xor (f.sgn ⟨k.val, by omega⟩) (y.sgn (f.perm ⟨k.val, by omega⟩)) = false
          rw [hfp, Equiv.Perm.one_apply, hfs, hkt]; simp
        · intro i hi
          change xor (f.sgn i) (y.sgn (f.perm i)) = y.sgn i
          rw [hfp, Equiv.Perm.one_apply, hfs]
          have h1 : ¬ i.val = k.val := by omega
          have h2 : ¬ i.val = k.val + 1 := by omega
          simp [h1, h2]
    rcases hclean 0 x hx with ⟨f0, hf0, _, hp0, hs0, _⟩
    rcases hclean 1 (f0 * x) hp0 with ⟨f1, hf1, _, hp1, hs1, hkeep1⟩
    rcases hclean 2 (f1 * (f0 * x)) hp1 with ⟨f2, hf2, _, hp2, hs2, hkeep2⟩
    rcases hclean 3 (f2 * (f1 * (f0 * x))) hp2 with ⟨f3, hf3, _, hp3, hs3, hkeep3⟩
    rcases hclean 4 (f3 * (f2 * (f1 * (f0 * x)))) hp3 with ⟨f4, hf4, _, hp4, hs4, hkeep4⟩
    set z := f4 * (f3 * (f2 * (f1 * (f0 * x))))
    have hz0 : z.sgn 0 = false := by
      rw [hkeep4 0 (by decide), hkeep3 0 (by decide), hkeep2 0 (by decide), hkeep1 0 (by decide)]
      exact hs0
    have hz1 : z.sgn 1 = false := by
      rw [hkeep4 1 (by decide), hkeep3 1 (by decide), hkeep2 1 (by decide)]
      exact hs1
    have hz2 : z.sgn 2 = false := by
      rw [hkeep4 2 (by decide), hkeep3 2 (by decide)]
      exact hs2
    have hz3 : z.sgn 3 = false := by
      rw [hkeep4 3 (by decide)]
      exact hs3
    have hz4 : z.sgn 4 = false := hs4
    have hz5 : z.sgn 5 = false := by
      have hdet := z.det_one
      rw [hp4, map_one, Units.val_one, one_mul, Fin.prod_univ_six,
        hz0, hz1, hz2, hz3, hz4] at hdet
      cases h5 : z.sgn 5
      · rfl
      · rw [h5] at hdet; simp [sgnInt] at hdet
    have hz1_eq : z = 1 := by
      apply B6Plus.ext
      · exact hp4
      · funext i; fin_cases i <;> assumption
    have hz_mem : z ∈ H := hz1_eq ▸ H.one_mem
    have hx_eq : x = f0⁻¹ * (f1⁻¹ * (f2⁻¹ * (f3⁻¹ * (f4⁻¹ * z)))) := by
      dsimp only [z]; group
    rw [hx_eq]
    exact H.mul_mem (H.inv_mem hf0) (H.mul_mem (H.inv_mem hf1)
      (H.mul_mem (H.inv_mem hf2) (H.mul_mem (H.inv_mem hf3)
        (H.mul_mem (H.inv_mem hf4) hz_mem))))
  have hd_mem : d ∈ H := hdiag_mem d hd_perm
  have hg_eq : g = d * h := by dsimp only [d]; group
  rw [hg_eq]
  exact H.mul_mem hd_mem hh

/-- **Clifford Lift of `B₆⁺`**: Every signed permutation `g ∈ B₆⁺` is realized on
    `so6Edge` by a two-qubit Clifford unitary `U`. -/
theorem clifford_lift_b6Plus (g : B6Plus) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
      ∀ ψ : State, so6Edge (U *ᵥ ψ) = actB6Vec g (so6Edge ψ) := by
  have hmem := b6Plus_mem_closure_b6Gen g
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
      ∀ ψ : State, so6Edge (U *ᵥ ψ) = actB6Vec x (so6Edge ψ))
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩
    exact ⟨cliffGen k, isClifford2_cliffGen k, so6Edge_cliffGen k⟩
  · exact ⟨1, IsClifford2.one, fun ψ => by rw [Matrix.one_mulVec, actB6Vec_one]⟩
  · rintro x y _ _ ⟨Ux, hUx, hactx⟩ ⟨Uy, hUy, hacty⟩
    refine ⟨Ux * Uy, hUx.mul hUy, fun ψ => ?_⟩
    rw [← Matrix.mulVec_mulVec, hactx, hacty, ← actB6Vec_mul]
  · rintro x _ ⟨Ux, hUx, hactx⟩
    refine ⟨Uxᴴ, hUx.conjTranspose, fun ψ => ?_⟩
    have h1 := hactx (Uxᴴ *ᵥ ψ)
    rw [Matrix.mulVec_mulVec, hUx.mul_conjTranspose, Matrix.one_mulVec] at h1
    calc so6Edge (Uxᴴ *ᵥ ψ)
        = actB6Vec (x⁻¹ * x) (so6Edge (Uxᴴ *ᵥ ψ)) := by rw [inv_mul_cancel, actB6Vec_one]
      _ = actB6Vec x⁻¹ (actB6Vec x (so6Edge (Uxᴴ *ᵥ ψ))) := by rw [actB6Vec_mul]
      _ = actB6Vec x⁻¹ (so6Edge ψ) := by rw [← h1]

/-! ### Part 4: Single Clifford Orbit and Exact Cardinality 480 -/

/-- Exact rational values of `so6Edge mubFiducial`. -/
lemma mubFiducial_so6_values :
    so6Edge mubFiducial 0  =  0     ∧
    so6Edge mubFiducial 1  = -1 / 2 ∧
    so6Edge mubFiducial 2  =  1 / 2 ∧
    so6Edge mubFiducial 3  = -1 / 2 ∧
    so6Edge mubFiducial 4  =  1 / 2 ∧
    so6Edge mubFiducial 5  = -1 / 2 ∧
    so6Edge mubFiducial 6  =  1 / 2 ∧
    so6Edge mubFiducial 7  =  1 / 2 ∧
    so6Edge mubFiducial 8  = -1 / 2 ∧
    so6Edge mubFiducial 9  =  0     ∧
    so6Edge mubFiducial 10 = -1 / 2 ∧
    so6Edge mubFiducial 11 = -1 / 2 ∧
    so6Edge mubFiducial 12 = -1 / 2 ∧
    so6Edge mubFiducial 13 = -1 / 2 ∧
    so6Edge mubFiducial 14 =  0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [so6Edge, mubFiducial, pauliExpRe_ZI]
  · simp [so6Edge, mubFiducial, pauliExpRe_YX]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_YY]
  · simp [so6Edge, mubFiducial, pauliExpRe_YZ]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_XI]
  · simp [so6Edge, mubFiducial, pauliExpRe_XX]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_XY]
  · simp [so6Edge, mubFiducial, pauliExpRe_XZ]
  · simp [so6Edge, mubFiducial, pauliExpRe_YI]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_IZ]
  · simp [so6Edge, mubFiducial, pauliExpRe_IY]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_ZX]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_IX]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_ZY]; norm_num
  · simp [so6Edge, mubFiducial, pauliExpRe_ZZ]

/-- The 32 fixed-matching `B₆⁺` parameter elements (`perm = id` or `swap 0 1`, `s 0 = false`,
    `s 1` determined by `det = +1`). -/
def fixedElem (b : Bool × Bool × Bool × Bool × Bool) : B6Plus :=
  let (sw0, s2, s3, s4, s5) := b
  let s1 := xor sw0 (xor s2 (xor s3 (xor s4 s5)))
  ⟨if sw0 then Equiv.swap 0 1 else 1,
   fun i => match i with
     | 0 => false
     | 1 => s1
     | 2 => s2
     | 3 => s3
     | 4 => s4
     | 5 => s5,
   by
     cases sw0 <;> cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;> decide⟩

/-- The 15 canonical `B₆⁺` representatives mapping `{(0,1), (2,3), (4,5)}` to each of the
    15 perfect matchings of `K₆`. -/
def matchPerm15P : Fin 15 → Equiv.Perm (Fin 6)
  | 0  => 1
  | 1  => Equiv.swap 3 4
  | 2  => Equiv.swap 3 5 * Equiv.swap 4 5
  | 3  => Equiv.swap 1 2
  | 4  => Equiv.swap 1 2 * Equiv.swap 3 4
  | 5  => Equiv.swap 1 2 * (Equiv.swap 3 5 * Equiv.swap 4 5)
  | 6  => Equiv.swap 1 3 * Equiv.swap 2 3
  | 7  => (Equiv.swap 1 3 * Equiv.swap 2 3) * Equiv.swap 3 4
  | 8  => (Equiv.swap 1 3 * Equiv.swap 2 3) * (Equiv.swap 3 5 * Equiv.swap 4 5)
  | 9  => Equiv.swap 1 4 * (Equiv.swap 2 4 * Equiv.swap 3 4)
  | 10 => (Equiv.swap 1 4 * (Equiv.swap 2 4 * Equiv.swap 3 4)) * Equiv.swap 3 4
  | 11 => (Equiv.swap 1 4 * (Equiv.swap 2 4 * Equiv.swap 3 4)) * (Equiv.swap 3 5 * Equiv.swap 4 5)
  | 12 => Equiv.swap 1 5 * (Equiv.swap 2 5 * (Equiv.swap 3 5 * Equiv.swap 4 5))
  | 13 => (Equiv.swap 1 5 * (Equiv.swap 2 5 * (Equiv.swap 3 5 * Equiv.swap 4 5))) * Equiv.swap 3 4
  | 14 => (Equiv.swap 1 5 * (Equiv.swap 2 5 * (Equiv.swap 3 5 * Equiv.swap 4 5))) *
          (Equiv.swap 3 5 * Equiv.swap 4 5)

def matchPerm15 (m : Fin 15) : B6Plus :=
  ⟨matchPerm15P m,
   fun i => decide (i = 0) && decide (m.val % 2 = 1),
   by fin_cases m <;> decide⟩

/-- The 480-element parameter family in `B₆⁺`: `15` matchings × `32` fixed-matching elements. -/
def maximizerParam (mb : Fin 15 × (Bool × Bool × Bool × Bool × Bool)) : B6Plus :=
  (matchPerm15 mb.1)⁻¹ * fixedElem mb.2

/-- Injectivity of the 32-element fixed-matching parametrization. -/
private lemma so6_fixed_matching_inj :
    Function.Injective (fun b : Bool × Bool × Bool × Bool × Bool =>
      actB6Vec (fixedElem b) (so6Edge mubFiducial)) := by
  intro b₁ b₂ heq
  rcases mubFiducial_so6_values with
    ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14⟩
  let mubInt : Fin 15 → ℤ
    | 0  => 0  | 1  => -1 | 2  => 1  | 3  => -1 | 4  => 1
    | 5  => -1 | 6  => 1  | 7  => 1  | 8  => -1 | 9  => 0
    | 10 => -1 | 11 => -1 | 12 => -1 | 13 => -1 | 14 => 0
  have hmub_eq : ∀ e : Fin 15, so6Edge mubFiducial e = (mubInt e : ℝ) / 2 := by
    intro e; fin_cases e <;> simp [mubInt, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9,
      hm10, hm11, hm12, hm13, hm14]
  have hint_eq : ∀ e : Fin 15,
      edgeSgnFun (fixedElem b₁) e * mubInt (edgeImgFun (fixedElem b₁) e) =
      edgeSgnFun (fixedElem b₂) e * mubInt (edgeImgFun (fixedElem b₂) e) := by
    intro e
    have h := congrFun heq e
    dsimp only at h
    rw [actB6Vec_apply, actB6Vec_apply, hmub_eq, hmub_eq] at h
    have h2 : ((edgeSgnFun (fixedElem b₁) e * mubInt (edgeImgFun (fixedElem b₁) e) : ℤ) : ℝ) =
        ((edgeSgnFun (fixedElem b₂) e * mubInt (edgeImgFun (fixedElem b₂) e) : ℤ) : ℝ) := by
      push_cast; linarith
    exact Int.cast_injective h2
  let recover (v : Fin 15 → ℤ) : Bool × Bool × Bool × Bool × Bool :=
    let sw0 := decide (v 1 * v 3 * v 10 = 1)
    if sw0 then
      (true, decide (v 1 = 1), decide (v 2 = -1), decide (v 3 = -1), decide (v 4 = 1))
    else
      (false, decide (v 1 = 1), decide (v 2 = -1), decide (v 3 = 1), decide (v 4 = -1))
  have hrec : ∀ x : Bool × Bool × Bool × Bool × Bool,
      recover (fun e => edgeSgnFun (fixedElem x) e * mubInt (edgeImgFun (fixedElem x) e)) = x := by
    rintro ⟨sw0, s2, s3, s4, s5⟩
    cases sw0 <;> cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;> decide
  rw [← hrec b₁, ← hrec b₂]
  exact congrArg recover (funext hint_eq)

/-- Every fixed-matching maximizer on `IsSkewOrth6` has a unique `Bool⁵` parameter. -/
lemma so6_fixed_matching_exists_unique {w : Fin 15 → ℝ} (hw : IsSkewOrth6 w)
    (hspec : ∀ e : Fin 15, |w e| = 0 ∨ |w e| = 1 / 2)
    (hz0 : w 0 = 0) (hz9 : w 9 = 0) (hz14 : w 14 = 0) :
    ∃! b : Bool × Bool × Bool × Bool × Bool,
      w = actB6Vec (fixedElem b) (so6Edge mubFiducial) := by
  have hsq_half : ∀ e : Fin 15, e ≠ 0 → e ≠ 9 → e ≠ 14 → w e ^ 2 = 1 / 4 := by
    intro e he0 he9 he14
    have hdiag : ∀ i : Fin 6, (toSkewMat w * toSkewMat w) i i = -1 := fun i => by
      rw [hw.1]; change -((1 : Matrix (Fin 6) (Fin 6) ℝ) i i) = -1; simp
    have hle : ∀ k : Fin 15, w k ^ 2 ≤ 1 / 4 := fun k => by
      rcases hspec k with h0 | hh
      · rw [abs_eq_zero.mp h0]; norm_num
      · rw [← sq_abs, hh]; norm_num
    have h0 := hdiag 0; have h1 := hdiag 1; have h2 := hdiag 2
    have h3 := hdiag 3
    rw [toSkewMat_sq_diag] at h0 h1 h2 h3
    dsimp only at h0 h1 h2 h3
    have hz0sq : w 0 ^ 2 = 0 := by rw [hz0]; ring
    have hz9sq : w 9 ^ 2 = 0 := by rw [hz9]; ring
    revert e he0 he9 he14
    apply fin15_cases
    · intro h0 _ _; exact absurd rfl h0
    · intro _ _ _; linarith [hle 1, hle 2, hle 3, hle 4, hz0sq]
    · intro _ _ _; linarith [hle 1, hle 2, hle 3, hle 4, hz0sq]
    · intro _ _ _; linarith [hle 1, hle 2, hle 3, hle 4, hz0sq]
    · intro _ _ _; linarith [hle 1, hle 2, hle 3, hle 4, hz0sq]
    · intro _ _ _; linarith [hle 5, hle 6, hle 7, hle 8, hz0sq]
    · intro _ _ _; linarith [hle 5, hle 6, hle 7, hle 8, hz0sq]
    · intro _ _ _; linarith [hle 5, hle 6, hle 7, hle 8, hz0sq]
    · intro _ _ _; linarith [hle 5, hle 6, hle 7, hle 8, hz0sq]
    · intro _ h9 _; exact absurd rfl h9
    · intro _ _ _; linarith [hle 1, hle 5, hle 10, hle 11, hz9sq]
    · intro _ _ _; linarith [hle 1, hle 5, hle 10, hle 11, hz9sq]
    · intro _ _ _; linarith [hle 2, hle 6, hle 12, hle 13, hz9sq]
    · intro _ _ _; linarith [hle 2, hle 6, hle 12, hle 13, hz9sq]
    · intro _ _ h14; exact absurd rfl h14
  have hdiag_case : ∀ u : Fin 15 → ℝ, IsSkewOrth6 u →
      u 0 = 0 → u 9 = 0 → u 14 = 0 →
      (∀ e : Fin 15, e ≠ 0 → e ≠ 9 → e ≠ 14 → u e ^ 2 = 1 / 4) →
      u 1 * u 3 * u 10 = -1 / 8 →
      ∃ s2 s3 s4 s5 : Bool, u = actB6Vec (fixedElem (false, s2, s3, s4, s5)) (so6Edge mubFiducial) := by
    intro u hu hu0 hu9 hu14 husq hprod
    have hsq1 := husq 1 (by decide) (by decide) (by decide)
    have hsq2 := husq 2 (by decide) (by decide) (by decide)
    have hsq3 := husq 3 (by decide) (by decide) (by decide)
    have hsq4 := husq 4 (by decide) (by decide) (by decide)
    have hsq5 := husq 5 (by decide) (by decide) (by decide)
    have hoff : ∀ e : Fin 15, (toSkewMat u * toSkewMat u) (edgePairs e).1 (edgePairs e).2 = 0 := by
      intro e; rw [hu.1]
      have hne : (edgePairs e).1 ≠ (edgePairs e).2 := by fin_cases e <;> decide
      change -((1 : Matrix (Fin 6) (Fin 6) ℝ) (edgePairs e).1 (edgePairs e).2) = 0
      rw [Matrix.one_apply_ne hne, neg_zero]
    have ho2 := hoff 2; have ho3 := hoff 3
    rw [toSkewMat_sq_off] at ho2 ho3
    simp only [hu0, hu9, hu14, zero_mul, mul_zero, add_zero, zero_add, sub_zero] at ho2 ho3
    have hpf5 := hu.2 (edgePairs 5).1 (edgePairs 5).2
    rw [hodgePhi_edge_formula u 5, toSkewMat_edge] at hpf5
    dsimp only at hpf5; rw [hu14] at hpf5
    have hu5_pf : u 5 = u 4 * u 12 - u 3 * u 13 := by linarith
    have hu12 : u 12 = 2 * u 2 * u 3 := by
      have h1 : u 2 * u 3 * u 12 = 1 / 8 := by linear_combination u 3 * ho3 - hprod
      linear_combination 16 * u 2 * u 3 * h1 - 16 * u 12 * u 3 ^ 2 * hsq2 - 4 * u 12 * hsq3
    have hu13 : u 13 = -2 * u 2 * u 4 := by
      linear_combination -4 * u 4 * ho2 - 4 * u 3 * u 4 * hu12 - 8 * u 2 * u 4 * hsq3 - 4 * u 13 * hsq4
    have hdet_u : 16 * u 2 * u 3 * u 4 * u 5 = 1 := by
      rw [hu5_pf, hu12, hu13]
      linear_combination 64 * u 3 ^ 2 * u 4 ^ 2 * hsq2 + 16 * u 4 ^ 2 * hsq3 + 4 * hsq4
    let s2 : Bool := decide (0 < u 1)
    let s3 : Bool := decide (u 2 < 0)
    let s4 : Bool := decide (0 < u 3)
    let s5 : Bool := decide (u 4 < 0)
    have hpm : ∀ x : ℝ, x ^ 2 = 1 / 4 → x = 1 / 2 ∨ x = -1 / 2 := fun x hx => by
      have : (x - 1 / 2) * (x + 1 / 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
    have hs2 : sgnReal s2 = -2 * u 1 := by
      rcases hpm (u 1) hsq1 with h | h <;> simp [s2, sgnReal, h]; norm_num
    have hs3 : sgnReal s3 = 2 * u 2 := by
      rcases hpm (u 2) hsq2 with h | h <;> simp [s3, sgnReal, h]; norm_num
    have hs4 : sgnReal s4 = -2 * u 3 := by
      rcases hpm (u 3) hsq3 with h | h <;> simp [s4, sgnReal, h]; norm_num
    have hs5 : sgnReal s5 = 2 * u 4 := by
      rcases hpm (u 4) hsq4 with h | h <;> simp [s5, sgnReal, h]; norm_num
    set g := fixedElem (false, s2, s3, s4, s5)
    have hg1 : sgnReal (g.sgn 1) = 4 * u 1 * u 5 := by
      have h1 : g.sgn 1 = xor false (xor s2 (xor s3 (xor s4 s5))) := rfl
      rw [h1, Bool.false_xor, sgnReal_xor, sgnReal_xor, sgnReal_xor, hs2, hs3, hs4, hs5]
      linear_combination 4 * u 1 * u 5 * hdet_u - 64 * u 1 * u 2 * u 3 * u 4 * hsq5
    have hg0 : sgnReal (g.sgn 0) = 1 := rfl
    have hg2 : sgnReal (g.sgn 2) = -2 * u 1 := hs2
    have hg3 : sgnReal (g.sgn 3) = 2 * u 2 := hs3
    have hg4 : sgnReal (g.sgn 4) = -2 * u 3 := hs4
    have hg5 : sgnReal (g.sgn 5) = 2 * u 4 := hs5
    refine ⟨s2, s3, s4, s5, ?_⟩
    have hginv : g * g = 1 := by
      apply B6Plus.ext
      · apply Equiv.ext; intro i; rfl
      · funext i
        change xor (g.sgn i) (g.sgn i) = false
        exact Bool.xor_self _
    have hv_eq : actB6Vec g u = so6Edge mubFiducial := by
      set v := actB6Vec g u
      have hv_orth : IsSkewOrth6 v := isSkewOrth6_actB6 g hu
      have hv_apply : ∀ e : Fin 15, v e = sgnReal (g.sgn (edgePairs e).1) *
          sgnReal (g.sgn (edgePairs e).2) * u e := by
        intro e
        dsimp only [v, actB6Vec, actB6Mat]
        change sgnReal (g.sgn (edgePairs e).1) * sgnReal (g.sgn (edgePairs e).2) *
          toSkewMat u (edgePairs e).1 (edgePairs e).2 = _
        rw [toSkewMat_edge]
      have hv0 : v 0 = 0 := by rw [hv_apply 0, hu0]; ring
      have hv9 : v 9 = 0 := by rw [hv_apply 9, hu9]; ring
      have hv14 : v 14 = 0 := by rw [hv_apply 14, hu14]; ring
      have hv1 : v 1 = -1 / 2 := by
        rw [hv_apply 1]; dsimp only [edgePairs]; rw [hg0, hg2]; linear_combination -2 * hsq1
      have hv2 : v 2 = 1 / 2 := by
        rw [hv_apply 2]; dsimp only [edgePairs]; rw [hg0, hg3]; linear_combination 2 * hsq2
      have hv3 : v 3 = -1 / 2 := by
        rw [hv_apply 3]; dsimp only [edgePairs]; rw [hg0, hg4]; linear_combination -2 * hsq3
      have hv4 : v 4 = 1 / 2 := by
        rw [hv_apply 4]; dsimp only [edgePairs]; rw [hg0, hg5]; linear_combination 2 * hsq4
      have hv5 : v 5 = -1 / 2 := by
        rw [hv_apply 5]; dsimp only [edgePairs]; rw [hg1, hg2]
        linear_combination -8 * u 5 ^ 2 * hsq1 - 2 * hsq5
      have hv10 : v 10 = -1 / 2 := by
        rw [hv_apply 10]; dsimp only [edgePairs]; rw [hg2, hg4]; linear_combination 4 * hprod
      have hvoff : ∀ e : Fin 15, (toSkewMat v * toSkewMat v) (edgePairs e).1 (edgePairs e).2 = 0 := by
        intro e; rw [hv_orth.1]
        have hne : (edgePairs e).1 ≠ (edgePairs e).2 := by fin_cases e <;> decide
        change -((1 : Matrix (Fin 6) (Fin 6) ℝ) (edgePairs e).1 (edgePairs e).2) = 0
        rw [Matrix.one_apply_ne hne, neg_zero]
      have hvo0 := hvoff 0; have hvo1 := hvoff 1; have hvo3 := hvoff 3
      have hvo4 := hvoff 4; have hvo5 := hvoff 5; have hvo7 := hvoff 7
      rw [toSkewMat_sq_off] at hvo0 hvo1 hvo3 hvo4 hvo5 hvo7
      simp only [hv0, hv9, hv14, hv1, hv2, hv3, hv4, hv5, hv10] at hvo0 hvo1 hvo3 hvo4 hvo5 hvo7
      have hv11 : v 11 = -1 / 2 := by linarith
      have hv12 : v 12 = -1 / 2 := by linarith
      have hv13 : v 13 = -1 / 2 := by linarith
      rw [hv11] at hvo5; rw [hv12] at hvo7
      have hv6 : v 6 = 1 / 2 := by linarith
      rw [hv6] at hvo0
      have hv7 : v 7 = 1 / 2 := by linarith
      have hv8 : v 8 = -1 / 2 := by linarith
      rcases mubFiducial_so6_values with
        ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14⟩
      ext e
      revert e
      apply fin15_cases
      · exact hv0.trans hm0.symm
      · exact hv1.trans hm1.symm
      · exact hv2.trans hm2.symm
      · exact hv3.trans hm3.symm
      · exact hv4.trans hm4.symm
      · exact hv5.trans hm5.symm
      · exact hv6.trans hm6.symm
      · exact hv7.trans hm7.symm
      · exact hv8.trans hm8.symm
      · exact hv9.trans hm9.symm
      · exact hv10.trans hm10.symm
      · exact hv11.trans hm11.symm
      · exact hv12.trans hm12.symm
      · exact hv13.trans hm13.symm
      · exact hv14.trans hm14.symm
    calc u = actB6Vec (g * g) u := by rw [hginv, actB6Vec_one]
      _ = actB6Vec g (actB6Vec g u) := by rw [actB6Vec_mul]
      _ = actB6Vec g (so6Edge mubFiducial) := by rw [hv_eq]
  have hwsq1 := hsq_half 1 (by decide) (by decide) (by decide)
  have hwsq2 := hsq_half 2 (by decide) (by decide) (by decide)
  have hwsq3 := hsq_half 3 (by decide) (by decide) (by decide)
  have hwsq4 := hsq_half 4 (by decide) (by decide) (by decide)
  have hwsq5 := hsq_half 5 (by decide) (by decide) (by decide)
  have hwsq6 := hsq_half 6 (by decide) (by decide) (by decide)
  have hwsq7 := hsq_half 7 (by decide) (by decide) (by decide)
  have hwsq8 := hsq_half 8 (by decide) (by decide) (by decide)
  have hwsq10 := hsq_half 10 (by decide) (by decide) (by decide)
  have hprod_sq : (w 1 * w 3 * w 10) ^ 2 = (1 / 8 : ℝ) ^ 2 := by
    calc (w 1 * w 3 * w 10) ^ 2 = w 1 ^ 2 * w 3 ^ 2 * w 10 ^ 2 := by ring
      _ = (1 / 4) * (1 / 4) * (1 / 4) := by rw [hwsq1, hwsq3, hwsq10]
      _ = (1 / 8 : ℝ) ^ 2 := by norm_num
  have hprod_cases : w 1 * w 3 * w 10 = -1 / 8 ∨ w 1 * w 3 * w 10 = 1 / 8 := by
    have : (w 1 * w 3 * w 10 + 1 / 8) * (w 1 * w 3 * w 10 - 1 / 8) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
  have hex : ∃ b : Bool × Bool × Bool × Bool × Bool,
      w = actB6Vec (fixedElem b) (so6Edge mubFiducial) := by
    rcases hprod_cases with hneg | hpos
    · rcases hdiag_case w hw hz0 hz9 hz14 hsq_half hneg with ⟨s2, s3, s4, s5, heq⟩
      exact ⟨(false, s2, s3, s4, s5), heq⟩
    · set u := actB6Vec (b6Gen 0) w
      have hu : IsSkewOrth6 u := isSkewOrth6_actB6 (b6Gen 0) hw
      have hu_vals :
          u 0 = w 0 ∧ u 9 = w 9 ∧ u 14 = w 14 ∧
          u 1 = -w 5 ∧ u 3 = -w 7 ∧ u 10 = w 10 := by
        simp only [u, actB6Vec_apply]
        have hd : edgeImgFun (b6Gen 0) 0 = 0 ∧ edgeSgnFun (b6Gen 0) 0 = 1 ∧
            edgeImgFun (b6Gen 0) 9 = 9 ∧ edgeSgnFun (b6Gen 0) 9 = 1 ∧
            edgeImgFun (b6Gen 0) 14 = 14 ∧ edgeSgnFun (b6Gen 0) 14 = 1 ∧
            edgeImgFun (b6Gen 0) 1 = 5 ∧ edgeSgnFun (b6Gen 0) 1 = -1 ∧
            edgeImgFun (b6Gen 0) 3 = 7 ∧ edgeSgnFun (b6Gen 0) 3 = -1 ∧
            edgeImgFun (b6Gen 0) 10 = 10 ∧ edgeSgnFun (b6Gen 0) 10 = 1 := by decide
        rcases hd with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
        rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
        norm_num
      have hu0 : u 0 = 0 := hu_vals.1.trans hz0
      have hu9 : u 9 = 0 := hu_vals.2.1.trans hz9
      have hu14 : u 14 = 0 := hu_vals.2.2.1.trans hz14
      have husq : ∀ e : Fin 15, e ≠ 0 → e ≠ 9 → e ≠ 14 → u e ^ 2 = 1 / 4 := by
        intro e he0 he9 he14
        simp only [u, actB6Vec_apply, mul_pow, edgeSgnFun_sq, one_mul]
        have hne : edgeImgFun (b6Gen 0) e ≠ 0 ∧ edgeImgFun (b6Gen 0) e ≠ 9 ∧
            edgeImgFun (b6Gen 0) e ≠ 14 := by revert e he0 he9 he14; decide
        exact hsq_half _ hne.1 hne.2.1 hne.2.2
      have hoff : ∀ e : Fin 15, (toSkewMat w * toSkewMat w) (edgePairs e).1 (edgePairs e).2 = 0 := by
        intro e; rw [hw.1]
        have hne : (edgePairs e).1 ≠ (edgePairs e).2 := by fin_cases e <;> decide
        change -((1 : Matrix (Fin 6) (Fin 6) ℝ) (edgePairs e).1 (edgePairs e).2) = 0
        rw [Matrix.one_apply_ne hne, neg_zero]
      have ho0 := hoff 0; have ho1 := hoff 1; have ho3 := hoff 3
      have ho5 := hoff 5; have ho7 := hoff 7
      rw [toSkewMat_sq_off] at ho0 ho1 ho3 ho5 ho7
      simp only [hz0, hz9, hz14, zero_mul, mul_zero, add_zero, zero_add, sub_zero] at ho0 ho1 ho3 ho5 ho7
      have h15_eq_26 : w 1 * w 5 = w 2 * w 6 := by
        have h1 : w 1 * w 6 = w 2 * w 5 := by
          have : (w 1 * w 6 - w 2 * w 5) * w 10 = 0 := by
            linear_combination w 6 * ho3 - w 2 * ho7
          have h10ne : w 10 ≠ 0 := fun h => by rw [h] at hwsq10; norm_num at hwsq10
          linarith [(mul_eq_zero.mp this).resolve_right h10ne]
        linear_combination 4 * w 5 * w 6 * h1 - 4 * w 1 * w 5 * hwsq6 + 4 * w 2 * w 6 * hwsq5
      have h37_eq_48 : w 3 * w 7 = w 4 * w 8 := by
        have h1 : w 3 * w 8 = w 4 * w 7 := by
          have : (w 3 * w 8 - w 4 * w 7) * w 10 = 0 := by
            linear_combination -w 8 * ho1 + w 4 * ho5
          have h10ne : w 10 ≠ 0 := fun h => by rw [h] at hwsq10; norm_num at hwsq10
          linarith [(mul_eq_zero.mp this).resolve_right h10ne]
        linear_combination 4 * w 7 * w 8 * h1 - 4 * w 3 * w 7 * hwsq8 + 4 * w 4 * w 8 * hwsq7
      have h57 : w 5 * w 7 = -(w 1 * w 3) := by
        have h1537 : w 1 * w 5 + w 3 * w 7 = 0 := by linarith
        linear_combination 4 * w 1 * w 7 * h1537 - 4 * w 5 * w 7 * hwsq1 - 4 * w 1 * w 3 * hwsq7
      have huprod : u 1 * u 3 * u 10 = -1 / 8 := by
        rw [hu_vals.2.2.2.1, hu_vals.2.2.2.2.1, hu_vals.2.2.2.2.2]
        linear_combination w 10 * h57 - hpos
      rcases hdiag_case u hu hu0 hu9 hu14 husq huprod with ⟨s2, s3, s4, s5, heq⟩
      set g0 := (b6Gen 0)⁻¹ * fixedElem (false, s2, s3, s4, s5)
      set b' : Bool × Bool × Bool × Bool × Bool :=
        (true, xor (g0.sgn 0) (g0.sgn 2), xor (g0.sgn 0) (g0.sgn 3),
               xor (g0.sgn 0) (g0.sgn 4), xor (g0.sgn 0) (g0.sgn 5))
      have hact_eq : actB6Vec g0 (so6Edge mubFiducial) = actB6Vec (fixedElem b') (so6Edge mubFiducial) := by
        have hsgn_eq : ∀ e : Fin 15, edgeImgFun g0 e = edgeImgFun (fixedElem b') e ∧
            edgeSgnFun g0 e = edgeSgnFun (fixedElem b') e := by
          intro e
          dsimp only [g0, b', fixedElem, b6Gen]
          revert e
          cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;> decide
        ext e
        rw [actB6Vec_apply, actB6Vec_apply, (hsgn_eq e).1, (hsgn_eq e).2]
      refine ⟨b', ?_⟩
      calc w = actB6Vec ((b6Gen 0)⁻¹ * b6Gen 0) w := by rw [inv_mul_cancel, actB6Vec_one]
        _ = actB6Vec (b6Gen 0)⁻¹ u := by rw [actB6Vec_mul]
        _ = actB6Vec g0 (so6Edge mubFiducial) := by rw [heq, ← actB6Vec_mul]
        _ = actB6Vec (fixedElem b') (so6Edge mubFiducial) := hact_eq
  rcases hex with ⟨b, hb⟩
  exact ⟨b, hb, fun b' hb' => so6_fixed_matching_inj (hb'.symm.trans hb)⟩

private lemma fin6_unique_last {a b c d e f : Fin 6}
    (ha : f ≠ a) (hb : f ≠ b) (hc : f ≠ c) (hd : f ≠ d) (he : f ≠ e)
    {t : Fin 6} (hset : ∀ x : Fin 6, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = t) :
    f = t := by
  rcases hset f with h | h | h | h | h | h
  · exact absurd h ha
  · exact absurd h hb
  · exact absurd h hc
  · exact absurd h hd
  · exact absurd h he
  · exact h

/-- Every fixed-point-free involution on `Fin 6` corresponds to one of the 15 canonical matchings
    `matchPerm15 m`. -/
lemma exists_matchPerm15 (partner : Fin 6 → Fin 6)
    (hne : ∀ i : Fin 6, partner i ≠ i) (hinv : ∀ i : Fin 6, partner (partner i) = i) :
    ∃ m : Fin 15,
      partner ((matchPerm15 m).perm 0) = (matchPerm15 m).perm 1 ∧
      partner ((matchPerm15 m).perm 2) = (matchPerm15 m).perm 3 ∧
      partner ((matchPerm15 m).perm 4) = (matchPerm15 m).perm 5 := by
  have hlast : ∀ (a b c d t : Fin 6),
      a ≠ 0 → partner 0 = a → partner a = 0 →
      b ≠ 0 → b ≠ a → c ≠ 0 → c ≠ a → c ≠ b → partner b = c → partner c = b →
      d ≠ 0 → d ≠ a → d ≠ b → d ≠ c →
      (∀ x : Fin 6, x = 0 ∨ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = t) →
      partner d = t := by
    intro a b c d t _ h0a ha _ _ _ _ _ hbc hcb hd0 hda hdb hdc hset
    refine fin6_unique_last ?_ ?_ ?_ ?_ (hne d) hset
    · intro h; have := congrArg partner h; rw [hinv, h0a] at this; exact hda this
    · intro h; have := congrArg partner h; rw [hinv, ha] at this; exact hd0 this
    · intro h; have := congrArg partner h; rw [hinv, hbc] at this; exact hdc this
    · intro h; have := congrArg partner h; rw [hinv, hcb] at this; exact hdb this
  have hm_vals : ∀ m : Fin 15,
      (matchPerm15 m).perm 0 = 0 ∧
      ((matchPerm15 m).perm 1, (matchPerm15 m).perm 2, (matchPerm15 m).perm 3,
       (matchPerm15 m).perm 4, (matchPerm15 m).perm 5) =
      match m with
      | 0  => (1, 2, 3, 4, 5) | 1  => (1, 2, 4, 3, 5) | 2  => (1, 2, 5, 3, 4)
      | 3  => (2, 1, 3, 4, 5) | 4  => (2, 1, 4, 3, 5) | 5  => (2, 1, 5, 3, 4)
      | 6  => (3, 1, 2, 4, 5) | 7  => (3, 1, 4, 2, 5) | 8  => (3, 1, 5, 2, 4)
      | 9  => (4, 1, 2, 3, 5) | 10 => (4, 1, 3, 2, 5) | 11 => (4, 1, 5, 2, 3)
      | 12 => (5, 1, 2, 3, 4) | 13 => (5, 1, 3, 2, 4) | 14 => (5, 1, 4, 2, 3) := by
    decide
  have hmk : ∀ (m : Fin 15) (a b c d t : Fin 6),
      (matchPerm15 m).perm 0 = 0 →
      (matchPerm15 m).perm 1 = a → (matchPerm15 m).perm 2 = b → (matchPerm15 m).perm 3 = c →
      (matchPerm15 m).perm 4 = d → (matchPerm15 m).perm 5 = t →
      partner 0 = a → partner b = c → partner d = t →
      ∃ m' : Fin 15,
        partner ((matchPerm15 m').perm 0) = (matchPerm15 m').perm 1 ∧
        partner ((matchPerm15 m').perm 2) = (matchPerm15 m').perm 3 ∧
        partner ((matchPerm15 m').perm 4) = (matchPerm15 m').perm 5 :=
    fun m _ _ _ _ _ h0 h1 h2 h3 h4 h5 p0 pb pd =>
      ⟨m, by rw [h0, h1]; exact p0, by rw [h2, h3]; exact pb, by rw [h4, h5]; exact pd⟩
  have h0_ne : ∀ {x : Fin 6}, partner 0 = x → x ≠ 0 := fun hx h0 => hne 0 (hx.trans h0)
  have hsym : ∀ {x y : Fin 6}, partner x = y → partner y = x := fun h => by rw [← h, hinv]
  let Goal : Prop := ∃ m : Fin 15,
    partner ((matchPerm15 m).perm 0) = (matchPerm15 m).perm 1 ∧
    partner ((matchPerm15 m).perm 2) = (matchPerm15 m).perm 3 ∧
    partner ((matchPerm15 m).perm 4) = (matchPerm15 m).perm 5
  have h15 : ∀ a : Fin 6, partner 0 = a → Goal := by
    apply fin6_cases
    · intro h; exact absurd rfl (h0_ne h)
    · intro ha
      have hpa := hsym ha
      have hb_case : ∀ b : Fin 6, partner 2 = b → Goal := by
        apply fin6_cases
        · intro hb; have := congrArg partner hb; rw [hinv, ha] at this; exact absurd this (by decide)
        · intro hb; have := congrArg partner hb; rw [hinv, hpa] at this; exact absurd this (by decide)
        · intro hb; exact absurd hb (hne 2)
        · intro hb
          have hd := hlast 1 2 3 4 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 0
          exact hmk 0 1 2 3 4 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 1 2 4 3 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 1
          exact hmk 1 1 2 4 3 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 1 2 5 3 4 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 2
          exact hmk 2 1 2 5 3 4 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
      exact hb_case (partner 2) rfl
    · intro ha
      have hpa := hsym ha
      have hb_case : ∀ b : Fin 6, partner 1 = b → Goal := by
        apply fin6_cases
        · intro hb; have := congrArg partner hb; rw [hinv, ha] at this; exact absurd this (by decide)
        · intro hb; exact absurd hb (hne 1)
        · intro hb; have := congrArg partner hb; rw [hinv, hpa] at this; exact absurd this (by decide)
        · intro hb
          have hd := hlast 2 1 3 4 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 3
          exact hmk 3 2 1 3 4 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 2 1 4 3 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 4
          exact hmk 4 2 1 4 3 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 2 1 5 3 4 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 5
          exact hmk 5 2 1 5 3 4 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
      exact hb_case (partner 1) rfl
    · intro ha
      have hpa := hsym ha
      have hb_case : ∀ b : Fin 6, partner 1 = b → Goal := by
        apply fin6_cases
        · intro hb; have := congrArg partner hb; rw [hinv, ha] at this; exact absurd this (by decide)
        · intro hb; exact absurd hb (hne 1)
        · intro hb
          have hd := hlast 3 1 2 4 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 6
          exact hmk 6 3 1 2 4 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb; have := congrArg partner hb; rw [hinv, hpa] at this; exact absurd this (by decide)
        · intro hb
          have hd := hlast 3 1 4 2 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 7
          exact hmk 7 3 1 4 2 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 3 1 5 2 4 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 8
          exact hmk 8 3 1 5 2 4 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
      exact hb_case (partner 1) rfl
    · intro ha
      have hpa := hsym ha
      have hb_case : ∀ b : Fin 6, partner 1 = b → Goal := by
        apply fin6_cases
        · intro hb; have := congrArg partner hb; rw [hinv, ha] at this; exact absurd this (by decide)
        · intro hb; exact absurd hb (hne 1)
        · intro hb
          have hd := hlast 4 1 2 3 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 9
          exact hmk 9 4 1 2 3 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 4 1 3 2 5 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 10
          exact hmk 10 4 1 3 2 5 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb; have := congrArg partner hb; rw [hinv, hpa] at this; exact absurd this (by decide)
        · intro hb
          have hd := hlast 4 1 5 2 3 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 11
          exact hmk 11 4 1 5 2 3 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
      exact hb_case (partner 1) rfl
    · intro ha
      have hpa := hsym ha
      have hb_case : ∀ b : Fin 6, partner 1 = b → Goal := by
        apply fin6_cases
        · intro hb; have := congrArg partner hb; rw [hinv, ha] at this; exact absurd this (by decide)
        · intro hb; exact absurd hb (hne 1)
        · intro hb
          have hd := hlast 5 1 2 3 4 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 12
          exact hmk 12 5 1 2 3 4 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 5 1 3 2 4 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 13
          exact hmk 13 5 1 3 2 4 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb
          have hd := hlast 5 1 4 2 3 (by decide) ha hpa (by decide) (by decide) (by decide) (by decide) (by decide) hb (hsym hb) (by decide) (by decide) (by decide) (by decide) (by decide)
          have mv := hm_vals 14
          exact hmk 14 5 1 4 2 3 mv.1 (by simpa using congrArg Prod.fst mv.2)
            (by simpa using congrArg (fun x => x.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.1) mv.2)
            (by simpa using congrArg (fun x => x.2.2.2.1) mv.2) (by simpa using congrArg (fun x => x.2.2.2.2) mv.2)
            ha hb hd
        · intro hb; have := congrArg partner hb; rw [hinv, hpa] at this; exact absurd this (by decide)
      exact hb_case (partner 1) rfl
  exact h15 (partner 0) rfl

/-- **Exact 480-Element Bijection on `SO(6)`**: Every maximizer `a` on `IsSkewOrth6` is uniquely
    realized as `actB6Vec (maximizerParam mb) (so6Edge mubFiducial)` for a unique
    `mb : Fin 15 × Bool × Bool × Bool × Bool × Bool`. -/
theorem so6_maximizer_exists_unique_param {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a)
    (hspec : ∀ e : Fin 15, |a e| = 0 ∨ |a e| = 1 / 2) :
    ∃! mb : Fin 15 × (Bool × Bool × Bool × Bool × Bool),
      a = actB6Vec (maximizerParam mb) (so6Edge mubFiducial) := by
  have hmc := so6_equality_matching_counts ha ((so6_equality_iff_spectrum ha).mpr hspec)
  have hdeg1 := hmc.2.2
  have hex_p : ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ toSkewMat a i j = 0 := fun i => by
    rcases Finset.card_eq_one.mp (hdeg1 i) with ⟨j, hj⟩
    have hmem : j ∈ Finset.univ.filter (fun k : Fin 6 => k ≠ i ∧ toSkewMat a i k = 0) := by
      rw [hj]; exact Finset.mem_singleton_self j
    exact ⟨j, (Finset.mem_filter.mp hmem).2⟩
  choose partner hne hzero using hex_p
  have hinv : ∀ i : Fin 6, partner (partner i) = i := by
    intro i
    rcases Finset.card_eq_one.mp (hdeg1 (partner i)) with ⟨x, hx⟩
    have h1 : partner (partner i) ∈ Finset.univ.filter
        (fun k : Fin 6 => k ≠ partner i ∧ toSkewMat a (partner i) k = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne (partner i), hzero (partner i)⟩
    have h2 : i ∈ Finset.univ.filter
        (fun k : Fin 6 => k ≠ partner i ∧ toSkewMat a (partner i) k = 0) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hne i).symm, ?_⟩
      rw [toSkewMat_swap, hzero i, neg_zero]
    rw [hx, Finset.mem_singleton] at h1 h2
    exact h1.trans h2.symm
  rcases exists_matchPerm15 partner hne hinv with ⟨m, hm01, hm23, hm45⟩
  set w := actB6Vec (matchPerm15 m) a
  have hw : IsSkewOrth6 w := isSkewOrth6_actB6 (matchPerm15 m) ha
  have hw_spec : ∀ e : Fin 15, |w e| = 0 ∨ |w e| = 1 / 2 := by
    intro e
    dsimp only [w]
    rw [actB6Vec_apply, abs_mul]
    have hs1 : |(edgeSgnFun (matchPerm15 m) e : ℝ)| = 1 := by
      have hsq := edgeSgnFun_sq (matchPerm15 m) e
      rw [← sq_abs] at hsq
      nlinarith [abs_nonneg (edgeSgnFun (matchPerm15 m) e : ℝ)]
    rw [hs1, one_mul]
    exact hspec (edgeImgFun (matchPerm15 m) e)
  have hw0 : w 0 = 0 := by
    dsimp only [w, actB6Vec, actB6Mat, edgePairs]
    rw [← hm01, hzero, mul_zero]
  have hw9 : w 9 = 0 := by
    dsimp only [w, actB6Vec, actB6Mat, edgePairs]
    rw [← hm23, hzero, mul_zero]
  have hw14 : w 14 = 0 := by
    dsimp only [w, actB6Vec, actB6Mat, edgePairs]
    rw [← hm45, hzero, mul_zero]
  rcases so6_fixed_matching_exists_unique hw hw_spec hw0 hw9 hw14 with ⟨b, hb, hb_uniq⟩
  refine ⟨(m, b), ?_, ?_⟩
  · calc a = actB6Vec ((matchPerm15 m)⁻¹ * matchPerm15 m) a := by rw [inv_mul_cancel, actB6Vec_one]
      _ = actB6Vec (matchPerm15 m)⁻¹ w := by rw [actB6Vec_mul]
      _ = actB6Vec (maximizerParam (m, b)) (so6Edge mubFiducial) := by
          rw [hb, ← actB6Vec_mul]; rfl
  · rintro ⟨m', b'⟩ hmb'
    have hzero_set : ∀ (k : Fin 15) (c : Bool × Bool × Bool × Bool × Bool) (e : Fin 15),
        actB6Vec (maximizerParam (k, c)) (so6Edge mubFiducial) e = 0 ↔
          edgeImgFun (maximizerParam (k, c)) e = 0 ∨
          edgeImgFun (maximizerParam (k, c)) e = 9 ∨
          edgeImgFun (maximizerParam (k, c)) e = 14 := by
      intro k c e
      rw [actB6Vec_apply]
      have hsne : (edgeSgnFun (maximizerParam (k, c)) e : ℝ) ≠ 0 := by
        intro h0; have := edgeSgnFun_sq (maximizerParam (k, c)) e; rw [h0] at this; norm_num at this
      rw [mul_eq_zero, or_iff_right hsne, ← abs_eq_zero, mubFiducial_so6_abs]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => rfl⟩
      · exact ⟨fun h0 => absurd h0 (by norm_num), fun hc => absurd hc h⟩
    have hm_zero_iff : ∀ (k : Fin 15) (c : Bool × Bool × Bool × Bool × Bool) (e : Fin 15),
        (edgeImgFun (maximizerParam (k, c)) e = 0 ∨
         edgeImgFun (maximizerParam (k, c)) e = 9 ∨
         edgeImgFun (maximizerParam (k, c)) e = 14) ↔
        (edgeImgFun (matchPerm15 k)⁻¹ e = 0 ∨
         edgeImgFun (matchPerm15 k)⁻¹ e = 9 ∨
         edgeImgFun (matchPerm15 k)⁻¹ e = 14) := by
      intro k c e
      have hfix0 : ∀ (c' : Bool × Bool × Bool × Bool × Bool) (e' : Fin 15),
          (edgeImgFun (fixedElem c') e' = 0 ∨ edgeImgFun (fixedElem c') e' = 9 ∨
           edgeImgFun (fixedElem c') e' = 14) ↔ (e' = 0 ∨ e' = 9 ∨ e' = 14) := by
        intro c' e'
        rcases c' with ⟨sw0, s2, s3, s4, s5⟩
        revert e'
        cases sw0 <;> cases s2 <;> cases s3 <;> cases s4 <;> cases s5 <;> decide
      have himg_mul : ∀ (g1 g2 : B6Plus) (e' : Fin 15),
          edgeImgFun (g1 * g2) e' = edgeImgFun g2 (edgeImgFun g1 e') := by
        intro g1 g2 e'
        have h1 : ∀ u v : Fin 6, u ≠ v →
            (edgePairs (edgeLookup u v).1 = (u, v) ∨ edgePairs (edgeLookup u v).1 = (v, u)) := by
          decide
        have hne1 : g1.perm (edgePairs e').1 ≠ g1.perm (edgePairs e').2 := by
          intro he; have := g1.perm.injective he; fin_cases e' <;> simp [edgePairs] at this
        have hlu_sym : ∀ u v : Fin 6, (edgeLookup u v).1 = (edgeLookup v u).1 := by decide
        rcases h1 _ _ hne1 with hp | hp
        · change (edgeLookup (g2.perm (g1.perm (edgePairs e').1))
            (g2.perm (g1.perm (edgePairs e').2))).1 =
            (edgeLookup (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e').1)
              (g1.perm (edgePairs e').2)).1).1)
            (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e').1)
              (g1.perm (edgePairs e').2)).1).2)).1
          rw [hp]
        · change (edgeLookup (g2.perm (g1.perm (edgePairs e').1))
            (g2.perm (g1.perm (edgePairs e').2))).1 =
            (edgeLookup (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e').1)
              (g1.perm (edgePairs e').2)).1).1)
            (g2.perm (edgePairs (edgeLookup (g1.perm (edgePairs e').1)
              (g1.perm (edgePairs e').2)).1).2)).1
          rw [hp, hlu_sym]
      dsimp only [maximizerParam]
      rw [himg_mul, hfix0]
    have hmatch_eq : ∀ e : Fin 15,
        (edgeImgFun (matchPerm15 m')⁻¹ e = 0 ∨ edgeImgFun (matchPerm15 m')⁻¹ e = 9 ∨
         edgeImgFun (matchPerm15 m')⁻¹ e = 14) ↔
        (edgeImgFun (matchPerm15 m)⁻¹ e = 0 ∨ edgeImgFun (matchPerm15 m)⁻¹ e = 9 ∨
         edgeImgFun (matchPerm15 m)⁻¹ e = 14) := by
      intro e
      rw [← hm_zero_iff m' b' e, ← hm_zero_iff m b e, ← hzero_set m' b' e, ← hzero_set m b e]
      have ha_eq : actB6Vec (maximizerParam (m, b)) (so6Edge mubFiducial) = a := by
        calc actB6Vec (maximizerParam (m, b)) (so6Edge mubFiducial)
            = actB6Vec (matchPerm15 m)⁻¹ (actB6Vec (fixedElem b) (so6Edge mubFiducial)) := by
              rw [← actB6Vec_mul]; rfl
          _ = actB6Vec (matchPerm15 m)⁻¹ w := by rw [← hb]
          _ = actB6Vec ((matchPerm15 m)⁻¹ * matchPerm15 m) a := by rw [← actB6Vec_mul]
          _ = a := by rw [inv_mul_cancel, actB6Vec_one]
      rw [ha_eq, ← hmb']
    have hm_inj : ∀ k₁ k₂ : Fin 15,
        (∀ e : Fin 15,
          (edgeImgFun (matchPerm15 k₁)⁻¹ e = 0 ∨ edgeImgFun (matchPerm15 k₁)⁻¹ e = 9 ∨
           edgeImgFun (matchPerm15 k₁)⁻¹ e = 14) ↔
          (edgeImgFun (matchPerm15 k₂)⁻¹ e = 0 ∨ edgeImgFun (matchPerm15 k₂)⁻¹ e = 9 ∨
           edgeImgFun (matchPerm15 k₂)⁻¹ e = 14)) → k₁ = k₂ := by
      decide
    have hm_eq : m' = m := hm_inj m' m hmatch_eq
    subst hm_eq
    have hb'_eq : w = actB6Vec (fixedElem b') (so6Edge mubFiducial) := by
      dsimp only [w]
      rw [hmb']
      dsimp only [maximizerParam]
      rw [← actB6Vec_mul, ← mul_assoc, mul_inv_cancel, one_mul]
    exact Prod.ext rfl (hb_uniq b' hb'_eq)

/-- **Single Clifford Orbit Theorem**: For any normalized pure two-qubit state `ψ` and any
    Rényi order `α ≥ 2`, `ψ` maximizes `M_α` iff `ψ` lies in the two-qubit Clifford orbit of
    `mubFiducial` up to a unit global phase. -/
theorem maximizer_iff_clifford_orbit {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
        ∃ θ : ℂ, ‖θ‖ = 1 ∧ ψ = θ • (U *ᵥ mubFiducial) := by
  constructor
  · intro hmax
    have hspec_p := (maximizer_iff_mub_spectrum hψ hα).mp hmax
    have hspec : ∀ e : Fin 15, |so6Edge ψ e| = 0 ∨ |so6Edge ψ e| = 1 / 2 := by
      intro e
      have hp := hspec_p (edgePauliLabel e).1 (edgePauliLabel e).2 (edgePauliLabel_ne_zero e)
      rw [so6Edge_eq_pauliExpRe, abs_mul, ← norm_pauliExp]
      have hs : |(edgePauliSign e : ℝ)| = 1 := by fin_cases e <;> simp [edgePauliSign]
      rw [hs, one_mul]; exact hp
    rcases (so6_maximizer_exists_unique_param (so6Edge_isSkewOrth6 hψ) hspec).exists with ⟨mb, hmb⟩
    rcases clifford_lift_b6Plus (maximizerParam mb) with ⟨U, hU, hactU⟩
    have hUψ_norm : IsNormalized (U *ᵥ mubFiducial) :=
      hU.preserves_isNormalized mubFiducial_normalized
    have hso6_eq : so6Edge (U *ᵥ mubFiducial) = so6Edge ψ := by
      rw [hactU, ← hmb]
    have hρ_eq : densityMatrix (U *ᵥ mubFiducial) = densityMatrix ψ :=
      (densityMatrix_eq_iff_so6Edge_eq hUψ_norm hψ).mpr hso6_eq
    rcases (densityMatrix_eq_iff_phase hUψ_norm hψ).mp hρ_eq with ⟨θ, hθ, hψeq⟩
    exact ⟨U, hU, θ, hθ, hψeq⟩
  · rintro ⟨U, hU, θ, hθ, rfl⟩
    rw [phase_preserves_sre hθ, hU.preserves_sre]
    exact mub_fiducial_attains_sre hα

/-- Density-matrix form of the single Clifford orbit characterization. -/
theorem maximizer_iff_clifford_densityMatrix {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
        densityMatrix ψ = U * densityMatrix mubFiducial * Uᴴ := by
  rw [maximizer_iff_clifford_orbit hψ hα]
  constructor
  · rintro ⟨U, hU, θ, hθ, rfl⟩
    refine ⟨U, hU, ?_⟩
    have hUψ_norm : IsNormalized (U *ᵥ mubFiducial) :=
      hU.preserves_isNormalized mubFiducial_normalized
    have hρ := (densityMatrix_eq_iff_phase hUψ_norm (phase_preserves_isNormalized hθ hUψ_norm)).mpr
      ⟨θ, hθ, rfl⟩
    rw [← hρ, IsClifford2.densityMatrix_mulVec]
  · rintro ⟨U, hU, hρ⟩
    have hUψ_norm : IsNormalized (U *ᵥ mubFiducial) :=
      hU.preserves_isNormalized mubFiducial_normalized
    rw [← IsClifford2.densityMatrix_mulVec] at hρ
    rcases (densityMatrix_eq_iff_phase hUψ_norm hψ).mp hρ.symm with ⟨θ, hθ, hψeq⟩
    exact ⟨U, hU, θ, hθ, hψeq⟩

/-- **Exact Count of All Maximizers**: For every Rényi order `α ≥ 2`, the set of density matrices
    `|ψ⟩⟨ψ|` of all pure two-qubit states maximizing `M_α` is finite and has exact cardinality `480`. -/
theorem maximizer_densityMatrix_ncard_eq_480 {α : ℝ} (hα : 2 ≤ α) :
    let S : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
      {ρ | ∃ ψ : State, IsNormalized ψ ∧
        sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ∧
        ρ = densityMatrix ψ}
    S.Finite ∧ S.ncard = 480 := by
  intro S
  have hlift : ∀ mb : Fin 15 × (Bool × Bool × Bool × Bool × Bool),
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
        ∀ ψ : State, so6Edge (U *ᵥ ψ) = actB6Vec (maximizerParam mb) (so6Edge ψ) :=
    fun mb => clifford_lift_b6Plus (maximizerParam mb)
  choose Uf hUf hactUf using hlift
  let f : Fin 15 × (Bool × Bool × Bool × Bool × Bool) → Matrix (Fin 4) (Fin 4) ℂ :=
    fun mb => densityMatrix (Uf mb *ᵥ mubFiducial)
  have hrange : Set.range f = S := by
    ext ρ
    constructor
    · rintro ⟨mb, rfl⟩
      refine ⟨Uf mb *ᵥ mubFiducial, (hUf mb).preserves_isNormalized mubFiducial_normalized, ?_, rfl⟩
      rw [(hUf mb).preserves_sre]
      exact mub_fiducial_attains_sre hα
    · rintro ⟨ψ, hψ, hmax, rfl⟩
      have hspec_p := (maximizer_iff_mub_spectrum hψ hα).mp hmax
      have hspec : ∀ e : Fin 15, |so6Edge ψ e| = 0 ∨ |so6Edge ψ e| = 1 / 2 := by
        intro e
        have hp := hspec_p (edgePauliLabel e).1 (edgePauliLabel e).2 (edgePauliLabel_ne_zero e)
        rw [so6Edge_eq_pauliExpRe, abs_mul, ← norm_pauliExp]
        have hs : |(edgePauliSign e : ℝ)| = 1 := by fin_cases e <;> simp [edgePauliSign]
        rw [hs, one_mul]; exact hp
      rcases (so6_maximizer_exists_unique_param (so6Edge_isSkewOrth6 hψ) hspec).exists with ⟨mb, hmb⟩
      refine ⟨mb, ?_⟩
      dsimp only [f]
      have hnorm_mb : IsNormalized (Uf mb *ᵥ mubFiducial) :=
        (hUf mb).preserves_isNormalized mubFiducial_normalized
      exact (densityMatrix_eq_iff_so6Edge_eq hnorm_mb hψ).mpr ((hactUf mb mubFiducial).trans hmb.symm)
  have hinj : Function.Injective f := by
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
  rw [← hrange]
  refine ⟨Set.finite_range f, ?_⟩
  rw [Set.ncard_range_of_injective hinj]
  norm_num

/-! ### Part 5: Complete Set of 5 MUBs and Two-Qubit WH (Pauli) MUB Fiducial Characterization -/

/-- A family of 5 bases of 4 states in `ℂ⁴` forms a complete set of `d + 1 = 5` mutually unbiased
    bases (MUBs) iff each basis is orthonormal and any two vectors from distinct bases have
    overlap magnitude `1 / √4 = 1 / 2`. -/
def IsCompleteMUB (B : Fin 5 → Fin 4 → State) : Prop :=
  (∀ m : Fin 5, ∀ k₁ k₂ : Fin 4,
    innerState (B m k₁) (B m k₂) = if k₁ = k₂ then 1 else 0) ∧
  (∀ m₁ m₂ : Fin 5, m₁ ≠ m₂ → ∀ k₁ k₂ : Fin 4,
    ‖innerState (B m₁ k₁) (B m₂ k₂)‖ = 1 / 2)

/-- A state `ψ ∈ ℂ⁴` is a two-qubit Weyl–Heisenberg (Pauli) MUB fiducial state iff its 16-state
    two-qubit Pauli orbit `{P_{a,b} |ψ⟩}` partitions into 4 orthonormal bases that extend (with a
    5th orthonormal basis `B5`) to a complete set of 5 mutually unbiased bases in `ℂ⁴`. -/
def IsPauliMUBFiducial (ψ : State) : Prop :=
  ∃ (part : Fin 4 → Fin 4 → Fin 4 × Fin 4) (B5 : Fin 4 → State),
    Function.Bijective (Function.uncurry part) ∧
    IsCompleteMUB (Fin.snoc (fun m k => pauli2 (part m k).1 (part m k).2 *ᵥ ψ) B5)

/-- Explicit partition of the 16 two-qubit Pauli operators into the 4 cosets of `{II, ZI, IZ, ZZ}`. -/
def mubPauliCoset : Fin 4 → Fin 4 → Fin 4 × Fin 4
  | 0, 0 => (0, 0) | 0, 1 => (3, 0) | 0, 2 => (0, 3) | 0, 3 => (3, 3)
  | 1, 0 => (0, 1) | 1, 1 => (3, 1) | 1, 2 => (0, 2) | 1, 3 => (3, 2)
  | 2, 0 => (1, 0) | 2, 1 => (2, 0) | 2, 2 => (1, 3) | 2, 3 => (2, 3)
  | 3, 0 => (1, 1) | 3, 1 => (2, 1) | 3, 2 => (1, 2) | 3, 3 => (2, 2)

/-- Standard computational basis of `ℂ⁴`. -/
def compBasis (k : Fin 4) : State :=
  fun i => if i = k then 1 else 0

lemma mubPauliCoset_bijective : Function.Bijective (Function.uncurry mubPauliCoset) := by
  have hinj : Function.Injective (Function.uncurry mubPauliCoset) := by decide
  exact Finite.injective_iff_bijective.mp hinj

private lemma pauli1_row_monomial (a : Fin 4) (r : Fin 2) :
    ∃ (c : ℂ) (s : Fin 2), ‖c‖ = 1 ∧ ∀ t : Fin 2, pauli1 a r t = if t = s then c else 0 := by
  fin_cases a <;> fin_cases r
  · exact ⟨1, 0, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨1, 1, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨1, 1, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨1, 0, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨-Complex.I, 1, by rw [norm_neg, Complex.norm_I], fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨Complex.I, 0, Complex.norm_I, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨1, 0, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩
  · exact ⟨-1, 1, by norm_num, fun t => by fin_cases t <;> simp [pauli1]⟩

private lemma pauli2_mulVec_entry (a b : Fin 4) (ψ : State) (k : Fin 4) :
    ∃ (c : ℂ) (j : Fin 4), ‖c‖ = 1 ∧ (pauli2 a b *ᵥ ψ) k = c * ψ j := by
  rcases pauli1_row_monomial a ⟨k.val / 2, by omega⟩ with ⟨c₁, s₁, hc₁, h1⟩
  rcases pauli1_row_monomial b ⟨k.val % 2, by omega⟩ with ⟨c₂, s₂, hc₂, h2⟩
  set j : Fin 4 := ⟨2 * s₁.val + s₂.val, by omega⟩
  refine ⟨c₁ * c₂, j, by rw [norm_mul, hc₁, hc₂, one_mul], ?_⟩
  simp only [Matrix.mulVec, dotProduct, pauli2]
  have hterm : ∀ t : Fin 4,
      pauli1 a ⟨k.val / 2, by omega⟩ ⟨t.val / 2, by omega⟩ *
      pauli1 b ⟨k.val % 2, by omega⟩ ⟨t.val % 2, by omega⟩ * ψ t =
      if t = j then c₁ * c₂ * ψ t else 0 := by
    intro t
    rw [h1, h2]
    have hiff : (t = j) ↔ ((⟨t.val / 2, by omega⟩ : Fin 2) = s₁ ∧
        (⟨t.val % 2, by omega⟩ : Fin 2) = s₂) := by
      constructor
      · rintro rfl
        have hs1 := s₁.isLt; have hs2 := s₂.isLt
        exact ⟨Fin.ext (by dsimp only [j]; omega), Fin.ext (by dsimp only [j]; omega)⟩
      · rintro ⟨ha1, ha2⟩
        have h1' := congrArg Fin.val ha1
        have h2' := congrArg Fin.val ha2
        dsimp only at h1' h2'
        exact Fin.ext (by dsimp only [j]; omega)
    by_cases ht : t = j
    · subst ht
      rcases hiff.mp rfl with ⟨h1', h2'⟩
      simp only [h1', h2', ite_true]
    · simp only [ht, ite_false]
      by_cases h1' : (⟨t.val / 2, by omega⟩ : Fin 2) = s₁
      · have h2' : (⟨t.val % 2, by omega⟩ : Fin 2) ≠ s₂ := fun h => ht (hiff.mpr ⟨h1', h⟩)
        simp only [h1', h2', ite_true, ite_false, mul_zero, zero_mul]
      · simp only [h1', ite_false, zero_mul]
  simp_rw [hterm]
  simp [Finset.sum_ite_eq']

/-- Explicit proof that `mubFiducial = (1/2, 1/2, 1/2, i/2)` generates 4 mutually unbiased
    orthonormal bases via its Pauli orbit which together with the computational basis form a
    complete set of 5 MUBs in `ℂ⁴`. -/
theorem mubFiducial_isPauliMUBFiducial : IsPauliMUBFiducial mubFiducial := by
  refine ⟨mubPauliCoset, compBasis, mubPauliCoset_bijective, ?_⟩
  set B : Fin 5 → Fin 4 → State :=
    Fin.snoc (fun m k => pauli2 (mubPauliCoset m k).1 (mubPauliCoset m k).2 *ᵥ mubFiducial) compBasis
  have hpauli_ip : ∀ p q : Fin 4 × Fin 4,
      innerState (pauli2 p.1 p.2 *ᵥ mubFiducial) (pauli2 q.1 q.2 *ᵥ mubFiducial) =
        (Complex.I ^ (((pauli1MulPow p.1 q.1).val + (pauli1MulPow p.2 q.2).val) % 4)) *
          pauliExp mubFiducial (pauli1MulLabel p.1 q.1) (pauli1MulLabel p.2 q.2) := by
    intro p q
    rw [innerState_mulVec_left, pauli2_conjTranspose, Matrix.mulVec_mulVec, pauli2_mul_eq,
      Matrix.smul_mulVec]
    rw [pauliExp_eq_innerState]
    unfold innerState
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hpauli_norm : ∀ a b : Fin 4,
      ‖pauliExp mubFiducial a b‖ =
        if a = 0 ∧ b = 0 then 1
        else if (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 3) then 0
        else 1 / 2 := by
    intro a b
    by_cases h0 : a = 0 ∧ b = 0
    · rcases h0 with ⟨rfl, rfl⟩
      simp [norm_pauliExp_II mubFiducial_normalized]
    · have hne : a ≠ 0 ∨ b ≠ 0 := by by_contra hc; push Not at hc; exact h0 hc
      rcases edgePauliLabel_surj hne with ⟨e, he⟩
      have habs := mubFiducial_so6_abs e
      rw [so6Edge_eq_pauliExpRe, he, abs_mul, ← norm_pauliExp] at habs
      have hs : |(edgePauliSign e : ℝ)| = 1 := by fin_cases e <;> simp [edgePauliSign]
      rw [hs, one_mul] at habs
      rw [habs]
      fin_cases e <;> simp [edgePauliLabel] at he <;> rcases he with ⟨rfl, rfl⟩ <;> simp
  have hcomp_ip : ∀ p : Fin 4 × Fin 4, ∀ k : Fin 4,
      ‖innerState (pauli2 p.1 p.2 *ᵥ mubFiducial) (compBasis k)‖ = 1 / 2 := by
    intro p k
    have hip : innerState (pauli2 p.1 p.2 *ᵥ mubFiducial) (compBasis k) =
        star ((pauli2 p.1 p.2 *ᵥ mubFiducial) k) := by
      unfold innerState compBasis
      simp [Finset.sum_ite_eq']
    rw [hip, norm_star]
    have hmub_norm : ∀ j : Fin 4, ‖mubFiducial j‖ = 1 / 2 := by
      intro j; fin_cases j <;> simp [mubFiducial]
    rcases pauli2_mulVec_entry p.1 p.2 mubFiducial k with ⟨c, j, hc, hjk⟩
    rw [hjk, norm_mul, hc, one_mul, hmub_norm j]
  have hinner_symm : ∀ u v : State, ‖innerState u v‖ = ‖innerState v u‖ := by
    intro u v
    have h : star (innerState u v) = innerState v u := by
      unfold innerState
      rw [star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mul_comm]
    rw [← h, norm_star]
  constructor
  · intro m k₁ k₂
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · dsimp only [B]; rw [Fin.snoc_last]
      unfold innerState compBasis
      fin_cases k₁ <;> fin_cases k₂ <;> simp
    · dsimp only [B]; rw [Fin.snoc_castSucc]
      rw [hpauli_ip]
      by_cases hk : k₁ = k₂
      · subst hk
        have hself : pauli1MulLabel (mubPauliCoset m' k₁).1 (mubPauliCoset m' k₁).1 = 0 ∧
            pauli1MulLabel (mubPauliCoset m' k₁).2 (mubPauliCoset m' k₁).2 = 0 ∧
            ((pauli1MulPow (mubPauliCoset m' k₁).1 (mubPauliCoset m' k₁).1).val +
             (pauli1MulPow (mubPauliCoset m' k₁).2 (mubPauliCoset m' k₁).2).val) % 4 = 0 := by
          revert m' k₁; decide
        rw [hself.1, hself.2.1, hself.2.2, pow_zero, one_mul, pauliExp_eq_ofReal,
          pauliExpRe_II, mubFiducial_normalized]
        simp
      · have hzero_lbl :
            let a := pauli1MulLabel (mubPauliCoset m' k₁).1 (mubPauliCoset m' k₂).1
            let b := pauli1MulLabel (mubPauliCoset m' k₁).2 (mubPauliCoset m' k₂).2
            (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 3) := by
          revert m' k₁ k₂ hk; decide
        have h0 : pauliExp mubFiducial
            (pauli1MulLabel (mubPauliCoset m' k₁).1 (mubPauliCoset m' k₂).1)
            (pauli1MulLabel (mubPauliCoset m' k₁).2 (mubPauliCoset m' k₂).2) = 0 := by
          have hn := hpauli_norm
            (pauli1MulLabel (mubPauliCoset m' k₁).1 (mubPauliCoset m' k₂).1)
            (pauli1MulLabel (mubPauliCoset m' k₁).2 (mubPauliCoset m' k₂).2)
          rcases hzero_lbl with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            simp [ha, hb] at hn ⊢ <;> exact hn
        rw [h0, mul_zero]
        simp only [hk, ite_false]
  · intro m₁ m₂ hne k₁ k₂
    revert hne
    refine Fin.lastCases ?_ (fun m₁' => ?_) m₁
    · refine Fin.lastCases ?_ (fun m₂' => ?_) m₂
      · intro hne; exact absurd rfl hne
      · intro _; dsimp only [B]; rw [Fin.snoc_last, Fin.snoc_castSucc, hinner_symm]
        exact hcomp_ip (mubPauliCoset m₂' k₂) k₁
    · refine Fin.lastCases ?_ (fun m₂' => ?_) m₂
      · intro _; dsimp only [B]; rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact hcomp_ip (mubPauliCoset m₁' k₁) k₂
      · intro hne; dsimp only [B]; rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hpauli_ip, norm_mul,
          norm_pow_I, one_mul, hpauli_norm]
        have hne' : m₁' ≠ m₂' := fun h => hne (congrArg Fin.castSucc h)
        have hdiff :
            let a := pauli1MulLabel (mubPauliCoset m₁' k₁).1 (mubPauliCoset m₂' k₂).1
            let b := pauli1MulLabel (mubPauliCoset m₁' k₁).2 (mubPauliCoset m₂' k₂).2
            ¬ (a = 0 ∧ b = 0) ∧ ¬ ((a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 3)) := by
          revert m₁' m₂' hne' k₁ k₂; decide
        simp [hdiff.1, hdiff.2]

/-- `IsPauliMUBFiducial` is preserved under two-qubit Clifford unitaries and global phases. -/
lemma isPauliMUBFiducial_clifford_phase {U : Matrix (Fin 4) (Fin 4) ℂ} (hU : IsClifford2 U)
    {θ : ℂ} (hθ : ‖θ‖ = 1) {ψ : State} (hfid : IsPauliMUBFiducial ψ) :
    IsPauliMUBFiducial (θ • (U *ᵥ ψ)) := by
  rcases hfid with ⟨part, B5, hbij, hMUB⟩
  rcases hU.pauli_perm with ⟨σ, kpow, hσ⟩
  let part' : Fin 4 → Fin 4 → Fin 4 × Fin 4 := fun m k => σ (part m k)
  have hbij' : Function.Bijective (Function.uncurry part') := by
    have heq : Function.uncurry part' = σ ∘ Function.uncurry part := by
      funext ⟨m, k⟩; rfl
    rw [heq]
    exact σ.bijective.comp hbij
  refine ⟨part', fun k => U *ᵥ B5 k, hbij', ?_⟩
  set B0 : Fin 5 → Fin 4 → State :=
    Fin.snoc (fun m k => pauli2 (part m k).1 (part m k).2 *ᵥ ψ) B5
  set B1 : Fin 5 → Fin 4 → State :=
    Fin.snoc (fun m k => pauli2 (part' m k).1 (part' m k).2 *ᵥ (θ • (U *ᵥ ψ))) (fun k => U *ᵥ B5 k)
  have hphase : ∀ m : Fin 5, ∀ k : Fin 4,
      ∃ c : ℂ, ‖c‖ = 1 ∧ B1 m k = c • (U *ᵥ B0 m k) := by
    intro m k
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · refine ⟨1, by norm_num, ?_⟩
      dsimp only [B1, B0]; rw [Fin.snoc_last, Fin.snoc_last, one_smul]
    · dsimp only [B1, B0, part']
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      set p := part m' k
      set c : ℂ := θ * Complex.I ^ ((4 - (kpow p).val) % 4)
      refine ⟨c, ?_, ?_⟩
      · rw [norm_mul, hθ, norm_pow_I, one_mul]
      · have h1 := hσ p
        have hmul : pauli2 (σ p).1 (σ p).2 * U =
            (Complex.I ^ ((4 - (kpow p).val) % 4)) • (U * pauli2 p.1 p.2) := by
          have hcI : (Complex.I : ℂ) ^ ((4 - (kpow p).val) % 4) * Complex.I ^ (kpow p).val = 1 := by
            rw [← pow_I_mod4, ← pow_add]
            have hle : (kpow p).val ≤ 4 := by omega
            rw [Nat.sub_add_cancel hle, pow_I_mod4]; norm_num
          calc pauli2 (σ p).1 (σ p).2 * U
              = ((Complex.I : ℂ) ^ ((4 - (kpow p).val) % 4) * Complex.I ^ (kpow p).val) •
                  (pauli2 (σ p).1 (σ p).2 * U) := by rw [hcI, one_smul]
            _ = (Complex.I ^ ((4 - (kpow p).val) % 4)) •
                  (((Complex.I ^ (kpow p).val) • pauli2 (σ p).1 (σ p).2) * U) := by
                rw [Matrix.smul_mul, smul_smul]
            _ = (Complex.I ^ ((4 - (kpow p).val) % 4)) • ((U * pauli2 p.1 p.2 * Uᴴ) * U) := by
                rw [← h1]
            _ = (Complex.I ^ ((4 - (kpow p).val) % 4)) • (U * pauli2 p.1 p.2) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc, hU.1, Matrix.mul_one]
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec, smul_smul,
          Matrix.mulVec_mulVec]
  have hinner_smul : ∀ (c₁ c₂ : ℂ) (u v : State),
      innerState (c₁ • u) (c₂ • v) = star c₁ * c₂ * innerState u v := by
    intro c₁ c₂ u v
    unfold innerState
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring
  constructor
  · intro m k₁ k₂
    by_cases hk : k₁ = k₂
    · subst hk
      rcases hphase m k₁ with ⟨c₁, hc₁, h1⟩
      rw [h1, hinner_smul, innerState_unitary hU.1, hMUB.1 m k₁ k₁]
      simp only [ite_true, mul_one, star_mul_self_eq_norm_sq, hc₁]
      norm_num
    · rcases hphase m k₁ with ⟨c₁, _, h1⟩
      rcases hphase m k₂ with ⟨c₂, _, h2⟩
      rw [h1, h2, hinner_smul, innerState_unitary hU.1, hMUB.1 m k₁ k₂]
      simp only [hk, ite_false, mul_zero]
  · intro m₁ m₂ hne k₁ k₂
    rcases hphase m₁ k₁ with ⟨c₁, hc₁, h1⟩
    rcases hphase m₂ k₂ with ⟨c₂, hc₂, h2⟩
    rw [h1, h2, hinner_smul, innerState_unitary hU.1, norm_mul, norm_mul, norm_star,
      hc₁, hc₂, one_mul, one_mul]
    exact hMUB.2 m₁ m₂ hne k₁ k₂

/-- **Complete MUB Fiducial Characterization**: A normalized pure two-qubit state `ψ` maximizes
    the Stabilizer Rényi Entropy `M_α` (`α ≥ 2`) iff `ψ` is a two-qubit Weyl–Heisenberg (Pauli)
    MUB fiducial state (its 16-state Pauli orbit partitions into 4 orthonormal bases extending
    to a complete set of 5 mutually unbiased bases in `ℂ⁴`). -/
theorem maximizer_iff_pauli_mub_fiducial {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      IsPauliMUBFiducial ψ := by
  constructor
  · intro hmax
    rcases (maximizer_iff_clifford_orbit hψ hα).mp hmax with ⟨U, hU, θ, hθ, rfl⟩
    exact isPauliMUBFiducial_clifford_phase hU hθ mubFiducial_isPauliMUBFiducial
  · rintro ⟨part, B5, hbij, hMUB⟩
    rw [maximizer_iff_mub_spectrum hψ hα]
    set B : Fin 5 → Fin 4 → State :=
      Fin.snoc (fun m k => pauli2 (part m k).1 (part m k).2 *ᵥ ψ) B5
    rcases hbij.2 (0, 0) with ⟨⟨m₀, k₀⟩, hmk₀⟩
    have hB0 : B m₀.castSucc k₀ = ψ := by
      dsimp only [B]; rw [Fin.snoc_castSucc]
      change pauli2 (part m₀ k₀).1 (part m₀ k₀).2 *ᵥ ψ = ψ
      have hp0 : part m₀ k₀ = (0, 0) := hmk₀
      rw [hp0]
      have hI : pauli2 0 0 = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [pauli2, pauli1]
      rw [hI, Matrix.one_mulVec]
    intro a b hab
    rcases hbij.2 (a, b) with ⟨⟨m, k⟩, hmk⟩
    have hBmk : B m.castSucc k = pauli2 a b *ᵥ ψ := by
      dsimp only [B]; rw [Fin.snoc_castSucc]
      have hp : part m k = (a, b) := hmk
      rw [hp]
    rw [pauliExp_eq_innerState, ← hBmk, ← hB0]
    by_cases hm : m₀ = m
    · subst hm
      have hk : k₀ ≠ k := by
        intro heq; subst heq
        have h00 : (0, 0) = (a, b) := hmk₀.symm.trans hmk
        rcases Prod.mk.inj h00 with ⟨ha, hb⟩
        rcases hab with h1 | h1 <;> [exact h1 ha.symm; exact h1 hb.symm]
      left
      rw [hMUB.1 m₀.castSucc k₀ k]
      simp only [hk, ite_false, norm_zero]
    · right
      have hm' : m₀.castSucc ≠ m.castSucc := fun h => hm (Fin.castSucc_injective 4 h)
      exact hMUB.2 m₀.castSucc m.castSucc hm' k₀ k

end TwoQubitMaximalMagic
