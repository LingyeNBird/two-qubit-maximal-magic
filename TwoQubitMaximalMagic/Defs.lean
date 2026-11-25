import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped Matrix

/-!
# Definitions for the Two-Qubit Maximal Magic Conjecture (Two-Qubit Case of Open Quantum Problem E28)

This file defines:
- Pure two-qubit states `ψ : Fin 4 → ℂ` and normalization `IsNormalized ψ`.
- The 16 two-qubit Pauli matrices `pauli2 a b` (`a, b : Fin 4`, corresponding to `I, X, Y, Z`).
- Pauli expectation values `pauliExp ψ a b = ⟨ψ | P_{a,b} | ψ⟩` and their Hermiticity.
- The `2α`-th Pauli moment `pauliMoment ψ α = ∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α}` and
  the Stabilizer Rényi Entropy (SRE)
  `sre ψ α = (1 / (1 - α)) * Real.log ((1 / 4) * pauliMoment ψ α)`.
-/

namespace TwoQubitMaximalMagic

/-- A pure two-qubit state vector in `ℂ⁴`. -/
abbrev State := Fin 4 → ℂ

/-- Squared Euclidean norm `⟨ψ | ψ⟩ = ∑_{i=0}^3 |ψ_i|^2`. -/
noncomputable def normSq (ψ : State) : ℝ :=
  ∑ i : Fin 4, ‖ψ i‖ ^ 2

/-- A pure two-qubit state is normalized iff `∑_{i=0}^3 |ψ_i|^2 = 1`. -/
def IsNormalized (ψ : State) : Prop :=
  normSq ψ = 1

lemma normSq_eq_sum_re_im (ψ : State) :
    normSq ψ =
      (ψ 0).re ^ 2 + (ψ 0).im ^ 2 +
      (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 +
      (ψ 3).re ^ 2 + (ψ 3).im ^ 2 := by
  simp only [normSq, Fin.sum_univ_four, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Single-qubit Pauli matrices indexed by `Fin 4`: `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`. -/
def pauli1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- Two-qubit Pauli matrices `P_a ⊗ P_b` on `ℂ⁴ ≅ ℂ² ⊗ ℂ²`. -/
def pauli2 (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    pauli1 a ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
    pauli1 b ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩

lemma pauli1_conjTranspose (a : Fin 4) : (pauli1 a)ᴴ = pauli1 a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauli1, Matrix.conjTranspose]

lemma pauli2_conjTranspose (a b : Fin 4) : (pauli2 a b)ᴴ = pauli2 a b := by
  ext i j
  simp only [Matrix.conjTranspose_apply, pauli2, star_mul']
  have h1 := congrFun (congrFun (pauli1_conjTranspose a) ⟨i.val / 2, by omega⟩) ⟨j.val / 2, by omega⟩
  have h2 := congrFun (congrFun (pauli1_conjTranspose b) ⟨i.val % 2, by omega⟩) ⟨j.val % 2, by omega⟩
  simp only [Matrix.conjTranspose_apply] at h1 h2
  rw [h1, h2, mul_comm]

/-- Complex Pauli expectation value `⟨ψ | (P_a ⊗ P_b) | ψ⟩`. -/
def pauliExp (ψ : State) (a b : Fin 4) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, star (ψ i) * pauli2 a b i j * ψ j

/-- Real part of the Pauli expectation value. -/
def pauliExpRe (ψ : State) (a b : Fin 4) : ℝ :=
  (pauliExp ψ a b).re

lemma star_pauliExp (ψ : State) (a b : Fin 4) :
    star (pauliExp ψ a b) = pauliExp ψ a b := by
  unfold pauliExp
  rw [star_sum]
  conv_lhs =>
    arg 2; ext i
    rw [star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hH := congrFun (congrFun (pauli2_conjTranspose a b) i) j
  simp only [Matrix.conjTranspose_apply] at hH
  simp only [star_mul', star_star]
  rw [hH]
  ring

lemma pauliExp_im_eq_zero (ψ : State) (a b : Fin 4) :
    (pauliExp ψ a b).im = 0 := by
  have h := congrArg Complex.im (star_pauliExp ψ a b)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

lemma pauliExp_eq_ofReal (ψ : State) (a b : Fin 4) :
    pauliExp ψ a b = ((pauliExpRe ψ a b : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [pauliExpRe]
  · simp [pauliExp_im_eq_zero]

lemma norm_pauliExp (ψ : State) (a b : Fin 4) :
    ‖pauliExp ψ a b‖ = |pauliExpRe ψ a b| := by
  rw [pauliExp_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]

lemma norm_pauliExp_sq (ψ : State) (a b : Fin 4) :
    ‖pauliExp ψ a b‖ ^ 2 = (pauliExpRe ψ a b) ^ 2 := by
  rw [norm_pauliExp, sq_abs]

lemma pauliExpRe_II (ψ : State) : pauliExpRe ψ 0 0 = normSq ψ := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four, normSq_eq_sum_re_im]
  simp [Complex.mul_re]
  ring

lemma norm_pauliExp_II {ψ : State} (hψ : IsNormalized ψ) :
    ‖pauliExp ψ 0 0‖ = 1 := by
  rw [norm_pauliExp, pauliExpRe_II, hψ]
  norm_num

/-- Explicit real-coordinate formulas for all 15 non-identity two-qubit Pauli expectations. -/
lemma pauliExpRe_IX (ψ : State) :
    pauliExpRe ψ 0 1 =
      2 * ((ψ 0).re * (ψ 1).re + (ψ 0).im * (ψ 1).im +
           (ψ 2).re * (ψ 3).re + (ψ 2).im * (ψ 3).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_IY (ψ : State) :
    pauliExpRe ψ 0 2 =
      2 * ((ψ 0).re * (ψ 1).im - (ψ 0).im * (ψ 1).re +
           (ψ 2).re * (ψ 3).im - (ψ 2).im * (ψ 3).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_IZ (ψ : State) :
    pauliExpRe ψ 0 3 =
      ((ψ 0).re ^ 2 + (ψ 0).im ^ 2) - ((ψ 1).re ^ 2 + (ψ 1).im ^ 2) +
      ((ψ 2).re ^ 2 + (ψ 2).im ^ 2) - ((ψ 3).re ^ 2 + (ψ 3).im ^ 2) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_XI (ψ : State) :
    pauliExpRe ψ 1 0 =
      2 * ((ψ 0).re * (ψ 2).re + (ψ 0).im * (ψ 2).im +
           (ψ 1).re * (ψ 3).re + (ψ 1).im * (ψ 3).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_XX (ψ : State) :
    pauliExpRe ψ 1 1 =
      2 * ((ψ 0).re * (ψ 3).re + (ψ 0).im * (ψ 3).im +
           (ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_XY (ψ : State) :
    pauliExpRe ψ 1 2 =
      2 * ((ψ 0).re * (ψ 3).im - (ψ 0).im * (ψ 3).re -
           (ψ 1).re * (ψ 2).im + (ψ 1).im * (ψ 2).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_XZ (ψ : State) :
    pauliExpRe ψ 1 3 =
      2 * ((ψ 0).re * (ψ 2).re + (ψ 0).im * (ψ 2).im -
           (ψ 1).re * (ψ 3).re - (ψ 1).im * (ψ 3).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_YI (ψ : State) :
    pauliExpRe ψ 2 0 =
      2 * ((ψ 0).re * (ψ 2).im - (ψ 0).im * (ψ 2).re +
           (ψ 1).re * (ψ 3).im - (ψ 1).im * (ψ 3).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_YX (ψ : State) :
    pauliExpRe ψ 2 1 =
      2 * ((ψ 0).re * (ψ 3).im - (ψ 0).im * (ψ 3).re +
           (ψ 1).re * (ψ 2).im - (ψ 1).im * (ψ 2).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_YY (ψ : State) :
    pauliExpRe ψ 2 2 =
      2 * (-(ψ 0).re * (ψ 3).re - (ψ 0).im * (ψ 3).im +
            (ψ 1).re * (ψ 2).re + (ψ 1).im * (ψ 2).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_YZ (ψ : State) :
    pauliExpRe ψ 2 3 =
      2 * ((ψ 0).re * (ψ 2).im - (ψ 0).im * (ψ 2).re -
           (ψ 1).re * (ψ 3).im + (ψ 1).im * (ψ 3).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_ZI (ψ : State) :
    pauliExpRe ψ 3 0 =
      ((ψ 0).re ^ 2 + (ψ 0).im ^ 2) + ((ψ 1).re ^ 2 + (ψ 1).im ^ 2) -
      ((ψ 2).re ^ 2 + (ψ 2).im ^ 2) - ((ψ 3).re ^ 2 + (ψ 3).im ^ 2) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_ZX (ψ : State) :
    pauliExpRe ψ 3 1 =
      2 * ((ψ 0).re * (ψ 1).re + (ψ 0).im * (ψ 1).im -
           (ψ 2).re * (ψ 3).re - (ψ 2).im * (ψ 3).im) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

lemma pauliExpRe_ZY (ψ : State) :
    pauliExpRe ψ 3 2 =
      2 * ((ψ 0).re * (ψ 1).im - (ψ 0).im * (ψ 1).re -
           (ψ 2).re * (ψ 3).im + (ψ 2).im * (ψ 3).re) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re, Complex.mul_im]; ring

lemma pauliExpRe_ZZ (ψ : State) :
    pauliExpRe ψ 3 3 =
      ((ψ 0).re ^ 2 + (ψ 0).im ^ 2) - ((ψ 1).re ^ 2 + (ψ 1).im ^ 2) -
      ((ψ 2).re ^ 2 + (ψ 2).im ^ 2) + ((ψ 3).re ^ 2 + (ψ 3).im ^ 2) := by
  simp only [pauliExpRe, pauliExp, pauli2, pauli1, Fin.sum_univ_four]
  simp [Complex.mul_re]; ring

/-- The `2α`-th Pauli moment `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α}`. -/
noncomputable def pauliMoment (ψ : State) (α : ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ‖pauliExp ψ a b‖ ^ (2 * α)

/-- The Stabilizer Rényi Entropy (SRE) of order `α` for a two-qubit pure state `ψ`:
    `M_α(|ψ⟩) = (1 / (1 - α)) * log((1 / 4) * ∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α})`. -/
noncomputable def sre (ψ : State) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * Real.log ((1 / 4 : ℝ) * pauliMoment ψ α)

end TwoQubitMaximalMagic
