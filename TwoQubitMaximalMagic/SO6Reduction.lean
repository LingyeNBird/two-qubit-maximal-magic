import TwoQubitMaximalMagic.Defs
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

open scoped Matrix

/-!
# The `su(4) ≅ so(6)` Reduction and the Signed-Permutation Group `B₆⁺`

Every normalized two-qubit pure state `|ψ⟩ ∈ ℂ⁴` defines 15 signed Pauli expectations
`a = so6Edge ψ : Fin 15 → ℝ` forming the upper-triangular entries of a real `6 × 6`
skew-symmetric orthogonal matrix `A = toSkewMat a ∈ SO(6)` satisfying:
1. `Aᵀ = -A`,
2. `A * A = -1` (orthogonality),
3. `hodgePhi A i j = 8 * A i j` for all `i, j : Fin 6` (Hodge self-duality / `Pf(A) = +1`).

We also define the finite symmetry group `B6Plus ⊂ SO(6)` (order `6! · 2⁵ = 23,040`)
of determinant-`+1` signed permutations of `Fin 6`, prove that it acts on `Fin 15 → ℝ`
preserving `IsSkewOrth6`, and prove that `B6Plus` acts transitively (up to sign) on all 15 edges.
-/

namespace TwoQubitMaximalMagic

/-- Clean finite-sum expansion over `Fin 15` without `Fin.succ` chains. -/
lemma sum_fin15 {M : Type*} [AddCommMonoid M] (f : Fin 15 → M) :
    ∑ e : Fin 15, f e =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
      f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 := by
  have h : (Finset.univ : Finset (Fin 15)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  rw [h]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ac_rfl

/-- Case split on `Fin 6` yielding literal numerals `0, 1, 2, 3, 4, 5`. -/
lemma fin6_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (i : Fin 6) : P i := by
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5]

/-- Case split on `Fin 15` yielding literal numerals `0, ..., 14`. -/
lemma fin15_cases {P : Fin 15 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9)
    (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14) (e : Fin 15) : P e := by
  fin_cases e
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

/-- The 15 ordered edges `(i, j)` with `i < j` in `K₆`. -/
def edgePairs : Fin 15 → Fin 6 × Fin 6
  | 0  => (0, 1)
  | 1  => (0, 2)
  | 2  => (0, 3)
  | 3  => (0, 4)
  | 4  => (0, 5)
  | 5  => (1, 2)
  | 6  => (1, 3)
  | 7  => (1, 4)
  | 8  => (1, 5)
  | 9  => (2, 3)
  | 10 => (2, 4)
  | 11 => (2, 5)
  | 12 => (3, 4)
  | 13 => (3, 5)
  | 14 => (4, 5)

/-- Explicit lookup `(i, j) ↦ (edge index, orientation sign)` for `i ≠ j` in `Fin 6`. -/
def edgeLookup : Fin 6 → Fin 6 → Fin 15 × Int
  | 0, 1 => (0,  1) | 1, 0 => (0,  -1)
  | 0, 2 => (1,  1) | 2, 0 => (1,  -1)
  | 0, 3 => (2,  1) | 3, 0 => (2,  -1)
  | 0, 4 => (3,  1) | 4, 0 => (3,  -1)
  | 0, 5 => (4,  1) | 5, 0 => (4,  -1)
  | 1, 2 => (5,  1) | 2, 1 => (5,  -1)
  | 1, 3 => (6,  1) | 3, 1 => (6,  -1)
  | 1, 4 => (7,  1) | 4, 1 => (7,  -1)
  | 1, 5 => (8,  1) | 5, 1 => (8,  -1)
  | 2, 3 => (9,  1) | 3, 2 => (9,  -1)
  | 2, 4 => (10, 1) | 4, 2 => (10, -1)
  | 2, 5 => (11, 1) | 5, 2 => (11, -1)
  | 3, 4 => (12, 1) | 4, 3 => (12, -1)
  | 3, 5 => (13, 1) | 5, 3 => (13, -1)
  | 4, 5 => (14, 1) | 5, 4 => (14, -1)
  | _, _ => (0,  0)

lemma edgePairs_surj_lt {i j : Fin 6} (hlt : i < j) :
    ∃ e : Fin 15, edgePairs e = (i, j) := by
  revert i j hlt; decide

/-- The `6 × 6` real skew-symmetric matrix with upper-triangular entries `a : Fin 15 → ℝ`. -/
def toSkewMat (a : Fin 15 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => ((edgeLookup i j).2 : ℝ) * a (edgeLookup i j).1

lemma toSkewMat_transpose (a : Fin 15 → ℝ) : (toSkewMat a)ᵀ = - toSkewMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toSkewMat, edgeLookup]

lemma toSkewMat_swap (a : Fin 15 → ℝ) (i j : Fin 6) :
    toSkewMat a j i = - toSkewMat a i j := by
  have h := congrFun (congrFun (toSkewMat_transpose a) i) j
  simpa [Matrix.transpose_apply] using h

lemma toSkewMat_diag (a : Fin 15 → ℝ) (i : Fin 6) : toSkewMat a i i = 0 := by
  fin_cases i <;> simp [toSkewMat, edgeLookup]

lemma toSkewMat_edge (a : Fin 15 → ℝ) (e : Fin 15) :
    toSkewMat a (edgePairs e).1 (edgePairs e).2 = a e := by
  fin_cases e <;> simp [toSkewMat, edgePairs, edgeLookup]

/-- Invariant Hodge self-duality operator on `6 × 6` matrices:
    `Φ(A)_{i,j} = ∑_{σ ∈ S₆, σ(0)=i, σ(1)=j} sgn(σ) A_{σ(2), σ(3)} A_{σ(4), σ(5)}`. -/
noncomputable def hodgePhi (A : Matrix (Fin 6) (Fin 6) ℝ) (i j : Fin 6) : ℝ :=
  ∑ σ : Equiv.Perm (Fin 6),
    if σ 0 = i ∧ σ 1 = j then
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * A (σ 2) (σ 3) * A (σ 4) (σ 5)
    else 0

/-- A vector `a : Fin 15 → ℝ` lies on the `SO(6)` self-dual skew-orthogonal manifold `V`
    iff `A = toSkewMat a` satisfies `A^2 = -I₆` and `Φ(A) = 8 A`. -/
def IsSkewOrth6 (a : Fin 15 → ℝ) : Prop :=
  toSkewMat a * toSkewMat a = -1 ∧
  ∀ i j : Fin 6, hodgePhi (toSkewMat a) i j = 8 * toSkewMat a i j

/-! ### Explicit evaluation of `hodgePhi (toSkewMat a) 0 1` -/

/-- Explicit bijection between `Fin 3 × Bool × Bool × Bool` and `{σ ∈ S₆ | σ(0) = 0 ∧ σ(1) = 1}`. -/
def matchPerm : Fin 3 × Bool × Bool × Bool → Equiv.Perm (Fin 6)
  | (m, b1, b2, b3) =>
    let base : Equiv.Perm (Fin 6) :=
      match m with
      | 0 => 1
      | 1 => Equiv.swap 3 4
      | 2 => Equiv.swap 3 5 * Equiv.swap 4 5
    let s1 : Equiv.Perm (Fin 6) := if b1 then Equiv.swap 2 3 else 1
    let s2 : Equiv.Perm (Fin 6) := if b2 then Equiv.swap 4 5 else 1
    let s3 : Equiv.Perm (Fin 6) := if b3 then Equiv.swap 2 4 * Equiv.swap 3 5 else 1
    base * s1 * s2 * s3

lemma matchPerm_fix01 (x : Fin 3 × Bool × Bool × Bool) :
    matchPerm x 0 = 0 ∧ matchPerm x 1 = 1 := by
  revert x; decide

lemma matchPerm_injective : Function.Injective matchPerm := by
  have h : ∀ x y : Fin 3 × Bool × Bool × Bool, matchPerm x = matchPerm y → x = y := by decide
  exact h

lemma matchPerm_exists_tuple :
    ∀ v2 v3 v4 v5 : Fin 6,
      2 ≤ v2 → 2 ≤ v3 → 2 ≤ v4 → 2 ≤ v5 →
      v2 ≠ v3 → v2 ≠ v4 → v2 ≠ v5 → v3 ≠ v4 → v3 ≠ v5 → v4 ≠ v5 →
      ∃ x : Fin 3 × Bool × Bool × Bool,
        matchPerm x 2 = v2 ∧ matchPerm x 3 = v3 ∧ matchPerm x 4 = v4 ∧ matchPerm x 5 = v5 := by
  decide

lemma matchPerm_surjective (σ : Equiv.Perm (Fin 6)) (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    ∃ x : Fin 3 × Bool × Bool × Bool, matchPerm x = σ := by
  have hge2 : ∀ k : Fin 6, 2 ≤ k → 2 ≤ σ k := by
    intro k hk
    have hne0 : σ k ≠ 0 := fun h => by have := σ.injective (h.trans h0.symm); omega
    have hne1 : σ k ≠ 1 := fun h => by have := σ.injective (h.trans h1.symm); omega
    omega
  have hne : ∀ i j : Fin 6, i ≠ j → σ i ≠ σ j := fun i j hij h => hij (σ.injective h)
  rcases matchPerm_exists_tuple (σ 2) (σ 3) (σ 4) (σ 5)
      (hge2 2 (by decide)) (hge2 3 (by decide)) (hge2 4 (by decide)) (hge2 5 (by decide))
      (hne 2 3 (by decide)) (hne 2 4 (by decide)) (hne 2 5 (by decide))
      (hne 3 4 (by decide)) (hne 3 5 (by decide)) (hne 4 5 (by decide)) with
    ⟨x, hx2, hx3, hx4, hx5⟩
  refine ⟨x, Equiv.ext fun k => ?_⟩
  fin_cases k
  · exact (matchPerm_fix01 x).1.trans h0.symm
  · exact (matchPerm_fix01 x).2.trans h1.symm
  · exact hx2
  · exact hx3
  · exact hx4
  · exact hx5

lemma sign_matchPerm (x : Fin 3 × Bool × Bool × Bool) :
    (Equiv.Perm.sign (matchPerm x) : ℤ) =
      (if x.1 = 1 then -1 else 1) *
      (if x.2.1 then -1 else 1) *
      (if x.2.2.1 then -1 else 1) := by
  rcases x with ⟨m, b1, b2, b3⟩
  have hs23 : Equiv.Perm.sign (Equiv.swap (2 : Fin 6) 3) = -1 := Equiv.Perm.sign_swap (by decide)
  have hs45 : Equiv.Perm.sign (Equiv.swap (4 : Fin 6) 5) = -1 := Equiv.Perm.sign_swap (by decide)
  have hs34 : Equiv.Perm.sign (Equiv.swap (3 : Fin 6) 4) = -1 := Equiv.Perm.sign_swap (by decide)
  have hs35 : Equiv.Perm.sign (Equiv.swap (3 : Fin 6) 5) = -1 := Equiv.Perm.sign_swap (by decide)
  have hs24 : Equiv.Perm.sign (Equiv.swap (2 : Fin 6) 4) = -1 := Equiv.Perm.sign_swap (by decide)
  fin_cases m <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [matchPerm, map_mul, hs23, hs45, hs34, hs35, hs24]

lemma matchPerm_term (a : Fin 15 → ℝ) (m : Fin 3) (b1 b2 b3 : Bool) :
    ((Equiv.Perm.sign (matchPerm (m, b1, b2, b3)) : ℤ) : ℝ) *
      toSkewMat a (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3) *
      toSkewMat a (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5) =
    match m with
    | 0 => a 9 * a 14
    | 1 => -(a 10 * a 13)
    | 2 => a 11 * a 12 := by
  rw [sign_matchPerm]
  have h1 : ∀ x : Fin 3 × Bool × Bool × Bool,
      ((if x.1 = 1 then (-1 : ℤ) else 1) *
       (if x.2.1 then -1 else 1) *
       (if x.2.2.1 then -1 else 1)) *
      (edgeLookup (matchPerm x 2) (matchPerm x 3)).2 *
      (edgeLookup (matchPerm x 4) (matchPerm x 5)).2 =
      (if x.1 = 1 then -1 else 1) := by decide
  have h2 : ∀ x : Fin 3 × Bool × Bool × Bool,
      ((edgeLookup (matchPerm x 2) (matchPerm x 3)).1 = (match x.1 with | 0 => 9 | 1 => 10 | 2 => 11) ∧
       (edgeLookup (matchPerm x 4) (matchPerm x 5)).1 = (match x.1 with | 0 => 14 | 1 => 13 | 2 => 12)) ∨
      ((edgeLookup (matchPerm x 2) (matchPerm x 3)).1 = (match x.1 with | 0 => 14 | 1 => 13 | 2 => 12) ∧
       (edgeLookup (matchPerm x 4) (matchPerm x 5)).1 = (match x.1 with | 0 => 9 | 1 => 10 | 2 => 11)) := by
    decide
  have h1r :
      ((((if m = 1 then (-1 : ℤ) else 1) * (if b1 then -1 else 1) * (if b2 then -1 else 1) : ℤ) : ℝ)) *
      ((edgeLookup (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3)).2 : ℝ) *
      ((edgeLookup (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5)).2 : ℝ) =
      ((if m = 1 then (-1 : ℤ) else 1 : ℤ) : ℝ) := by
    exact_mod_cast h1 (m, b1, b2, b3)
  simp only [toSkewMat]
  have hrearr :
      ((((if m = 1 then (-1 : ℤ) else 1) * (if b1 then -1 else 1) * (if b2 then -1 else 1) : ℤ) : ℝ)) *
        (((edgeLookup (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3)).2 : ℝ) *
          a (edgeLookup (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3)).1) *
        (((edgeLookup (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5)).2 : ℝ) *
          a (edgeLookup (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5)).1) =
      (((((if m = 1 then (-1 : ℤ) else 1) * (if b1 then -1 else 1) * (if b2 then -1 else 1) : ℤ) : ℝ)) *
        ((edgeLookup (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3)).2 : ℝ) *
        ((edgeLookup (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5)).2 : ℝ)) *
      (a (edgeLookup (matchPerm (m, b1, b2, b3) 2) (matchPerm (m, b1, b2, b3) 3)).1 *
       a (edgeLookup (matchPerm (m, b1, b2, b3) 4) (matchPerm (m, b1, b2, b3) 5)).1) := by ring
  rw [hrearr, h1r]
  rcases h2 (m, b1, b2, b3) with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    (rw [hl, hr]; fin_cases m <;> norm_num <;> ring)

lemma hodgePhi_01 (a : Fin 15 → ℝ) :
    hodgePhi (toSkewMat a) 0 1 = 8 * (a 9 * a 14 - a 10 * a 13 + a 11 * a 12) := by
  unfold hodgePhi
  rw [← Finset.sum_filter]
  have himg : Finset.image matchPerm Finset.univ =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => σ 0 = 0 ∧ σ 1 = 1) := by
    ext σ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨x, rfl⟩; exact matchPerm_fix01 x
    · rintro ⟨h0, h1⟩; exact matchPerm_surjective σ h0 h1
  rw [← himg, Finset.sum_image (fun x _ y _ h => matchPerm_injective h)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, matchPerm_term]
  ring

/-! ### Ideal generators `h0`, `h01`, `g01` vanish on `IsSkewOrth6` -/

lemma h0_eq_zero {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 - 1 = 0 := by
  have h := congrFun (congrFun ha.1 0) 0
  simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply_eq, Fin.sum_univ_six,
    toSkewMat, edgeLookup, Int.cast_zero, Int.cast_one, Int.cast_neg] at h
  linarith

lemma h01_eq_zero {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    a 1 * a 5 + a 2 * a 6 + a 3 * a 7 + a 4 * a 8 = 0 := by
  have h := congrFun (congrFun ha.1 0) 1
  simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply_ne (by decide : (0 : Fin 6) ≠ 1),
    Fin.sum_univ_six, toSkewMat, edgeLookup, Int.cast_zero, Int.cast_one, Int.cast_neg] at h
  linarith

lemma g01_eq_zero {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    a 0 - a 9 * a 14 + a 10 * a 13 - a 11 * a 12 = 0 := by
  have h := ha.2 0 1
  rw [hodgePhi_01] at h
  simp only [toSkewMat, edgeLookup, Int.cast_one] at h
  linarith

lemma sum_sq_eq_three {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    ∑ e : Fin 15, (a e) ^ 2 = 3 := by
  have hr : ∀ i : Fin 6, (toSkewMat a * toSkewMat a) i i = -1 := fun i => by
    have h := congrFun (congrFun ha.1 i) i
    simpa [Matrix.one_apply_eq] using h
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2
  have h3 := hr 3; have h4 := hr 4; have h5 := hr 5
  simp only [Matrix.mul_apply, Fin.sum_univ_six, toSkewMat, edgeLookup,
    Int.cast_zero, Int.cast_one, Int.cast_neg] at h0 h1 h2 h3 h4 h5
  rw [sum_fin15]
  linarith

/-! ### The Finite Symmetry Group `B6Plus ⊂ SO(6)` -/

/-- Sign helper `false ↦ +1`, `true ↦ -1` in `ℤ`. -/
def sgnInt (b : Bool) : ℤ := if b then -1 else 1

/-- Sign helper `false ↦ +1`, `true ↦ -1` in `ℝ`. -/
def sgnReal (b : Bool) : ℝ := if b then -1 else 1

lemma sgnInt_xor (b1 b2 : Bool) : sgnInt (xor b1 b2) = sgnInt b1 * sgnInt b2 := by
  cases b1 <;> cases b2 <;> rfl

lemma sgnReal_xor (b1 b2 : Bool) : sgnReal (xor b1 b2) = sgnReal b1 * sgnReal b2 := by
  cases b1 <;> cases b2 <;> norm_num [sgnReal]

lemma sgnReal_sq (b : Bool) : sgnReal b * sgnReal b = 1 := by
  cases b <;> norm_num [sgnReal]

lemma sgnInt_cast_real (b : Bool) : (sgnInt b : ℝ) = sgnReal b := by
  cases b <;> simp [sgnInt, sgnReal]

/-- The determinant-`+1` signed-permutation group `B₆⁺ ⊂ SO(6)` of order `23,040`. -/
@[ext]
structure B6Plus where
  perm : Equiv.Perm (Fin 6)
  sgn : Fin 6 → Bool
  det_one : (Equiv.Perm.sign perm : ℤ) * (∏ i : Fin 6, sgnInt (sgn i)) = 1
  deriving DecidableEq

/-- `B6Plus` is equivalent to the subtype of `Perm (Fin 6) × (Fin 6 → Bool)` with det `+1`. -/
def b6PlusEquivSubtype :
    B6Plus ≃ { x : Equiv.Perm (Fin 6) × (Fin 6 → Bool) //
      (Equiv.Perm.sign x.1 : ℤ) * (∏ i : Fin 6, sgnInt (x.2 i)) = 1 } where
  toFun g := ⟨(g.perm, g.sgn), g.det_one⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv g := by cases g; rfl
  right_inv x := by rcases x with ⟨⟨p, s⟩, h⟩; rfl

noncomputable instance : Fintype B6Plus :=
  Fintype.ofEquiv _ b6PlusEquivSubtype.symm

lemma units_int_inv_eq (u : ℤˣ) : ((u⁻¹ : ℤˣ) : ℤ) = (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

def b6One : B6Plus :=
  ⟨1, fun _ => false, by simp [sgnInt]⟩

def b6Mul (g1 g2 : B6Plus) : B6Plus :=
  ⟨g1.perm.trans g2.perm,
   fun i => xor (g1.sgn i) (g2.sgn (g1.perm i)),
   by
     have htr : g1.perm.trans g2.perm = g2.perm * g1.perm := rfl
     rw [htr, map_mul, Units.val_mul]
     have hprod : ∏ i : Fin 6, sgnInt (xor (g1.sgn i) (g2.sgn (g1.perm i))) =
         (∏ i : Fin 6, sgnInt (g1.sgn i)) * (∏ i : Fin 6, sgnInt (g2.sgn i)) := by
       simp_rw [sgnInt_xor, Finset.prod_mul_distrib]
       congr 1
       exact Fintype.prod_equiv g1.perm _ _ (fun _ => rfl)
     rw [hprod]
     have h1 := g1.det_one
     have h2 := g2.det_one
     calc ((Equiv.Perm.sign g2.perm : ℤ) * (Equiv.Perm.sign g1.perm : ℤ)) *
            ((∏ i : Fin 6, sgnInt (g1.sgn i)) * (∏ i : Fin 6, sgnInt (g2.sgn i)))
         = ((Equiv.Perm.sign g1.perm : ℤ) * (∏ i : Fin 6, sgnInt (g1.sgn i))) *
           ((Equiv.Perm.sign g2.perm : ℤ) * (∏ i : Fin 6, sgnInt (g2.sgn i))) := by ring
       _ = 1 * 1 := by rw [h1, h2]
       _ = 1 := by ring⟩

def b6Inv (g : B6Plus) : B6Plus :=
  ⟨g.perm.symm,
   fun i => g.sgn (g.perm.symm i),
   by
     have hprod : ∏ i : Fin 6, sgnInt (g.sgn (g.perm.symm i)) =
         ∏ i : Fin 6, sgnInt (g.sgn i) :=
       Fintype.prod_equiv g.perm.symm _ _ (fun _ => rfl)
     rw [hprod]
     have hsym : Equiv.Perm.sign g.perm.symm = (Equiv.Perm.sign g.perm)⁻¹ := by
       change Equiv.Perm.sign g.perm⁻¹ = _
       exact map_inv _ _
     rw [hsym, units_int_inv_eq]
     exact g.det_one⟩

instance : Group B6Plus where
  one := b6One
  mul := b6Mul
  inv := b6Inv
  mul_assoc g1 g2 g3 := by
    apply B6Plus.ext
    · rfl
    · funext i; exact Bool.xor_assoc _ _ _
  one_mul g := by
    apply B6Plus.ext
    · rfl
    · funext i; exact Bool.false_xor _
  mul_one g := by
    apply B6Plus.ext
    · rfl
    · funext i; exact Bool.xor_false _
  inv_mul_cancel g := by
    apply B6Plus.ext
    · apply Equiv.ext; intro i; exact g.perm.apply_symm_apply i
    · funext i
      show (b6Mul (b6Inv g) g).sgn i = b6One.sgn i
      simp only [b6Mul, b6Inv, b6One]
      exact Bool.xor_self _

instance : Nonempty B6Plus := ⟨1⟩

/-- Action of `g ∈ B6Plus` on `6 × 6` matrices: `(g · A)_{i,j} = s_i s_j A_{p(i), p(j)}`. -/
def actB6Mat (g : B6Plus) (A : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => sgnReal (g.sgn i) * sgnReal (g.sgn j) * A (g.perm i) (g.perm j)

lemma actB6Mat_mul (g1 g2 : B6Plus) (A : Matrix (Fin 6) (Fin 6) ℝ) :
    actB6Mat (g1 * g2) A = actB6Mat g1 (actB6Mat g2 A) := by
  ext i j
  simp only [actB6Mat]
  have hp : ∀ k, (g1 * g2).perm k = g2.perm (g1.perm k) := fun _ => rfl
  have hs : ∀ k, (g1 * g2).sgn k = xor (g1.sgn k) (g2.sgn (g1.perm k)) := fun _ => rfl
  rw [hp i, hp j, hs i, hs j, sgnReal_xor, sgnReal_xor]
  ring

lemma actB6Mat_one (A : Matrix (Fin 6) (Fin 6) ℝ) : actB6Mat 1 A = A := by
  ext i j
  change sgnReal false * sgnReal false * A i j = A i j
  simp [sgnReal]

lemma actB6Mat_skew (g : B6Plus) (a : Fin 15 → ℝ) (i j : Fin 6) :
    actB6Mat g (toSkewMat a) j i = - actB6Mat g (toSkewMat a) i j := by
  unfold actB6Mat
  rw [toSkewMat_swap]
  ring

/-- Action of `g ∈ B6Plus` on upper-triangular edge vectors `a : Fin 15 → ℝ`. -/
def actB6Vec (g : B6Plus) (a : Fin 15 → ℝ) : Fin 15 → ℝ :=
  fun e => actB6Mat g (toSkewMat a) (edgePairs e).1 (edgePairs e).2

/-- Edge permutation induced by `g ∈ B6Plus` on `Fin 15`. -/
def edgeImgFun (g : B6Plus) (e : Fin 15) : Fin 15 :=
  (edgeLookup (g.perm (edgePairs e).1) (g.perm (edgePairs e).2)).1

/-- Edge sign induced by `g ∈ B6Plus` on `Fin 15`. -/
def edgeSgnFun (g : B6Plus) (e : Fin 15) : ℤ :=
  sgnInt (g.sgn (edgePairs e).1) * sgnInt (g.sgn (edgePairs e).2) *
  (edgeLookup (g.perm (edgePairs e).1) (g.perm (edgePairs e).2)).2

lemma actB6Vec_apply (g : B6Plus) (a : Fin 15 → ℝ) (e : Fin 15) :
    actB6Vec g a e = (edgeSgnFun g e : ℝ) * a (edgeImgFun g e) := by
  simp only [actB6Vec, actB6Mat, toSkewMat, edgeSgnFun, edgeImgFun, Int.cast_mul, sgnInt_cast_real]
  ring

lemma edgeSgnFun_sq (g : B6Plus) (e : Fin 15) : (edgeSgnFun g e : ℝ) ^ 2 = 1 := by
  have hne : g.perm (edgePairs e).1 ≠ g.perm (edgePairs e).2 := by
    intro h
    have h0 := g.perm.injective h
    fin_cases e <;> simp [edgePairs] at h0
  have hlu : ((edgeLookup (g.perm (edgePairs e).1) (g.perm (edgePairs e).2)).2 : ℝ) ^ 2 = 1 := by
    generalize g.perm (edgePairs e).1 = u at hne
    generalize g.perm (edgePairs e).2 = v at hne
    fin_cases u <;> fin_cases v <;> simp [edgeLookup] at hne ⊢
  simp only [edgeSgnFun, Int.cast_mul, sgnInt_cast_real, mul_pow]
  have hs1 : sgnReal (g.sgn (edgePairs e).1) ^ 2 = 1 := by rw [sq]; exact sgnReal_sq _
  have hs2 : sgnReal (g.sgn (edgePairs e).2) ^ 2 = 1 := by rw [sq]; exact sgnReal_sq _
  rw [hs1, hs2, hlu]; ring

lemma edgeImgFun_injective (g : B6Plus) : Function.Injective (edgeImgFun g) := by
  intro e1 e2 h
  have hpair : ∀ u v : Fin 6, u ≠ v →
      (edgePairs (edgeLookup u v).1 = (u, v) ∨ edgePairs (edgeLookup u v).1 = (v, u)) := by
    decide
  have hne1 : g.perm (edgePairs e1).1 ≠ g.perm (edgePairs e1).2 := by
    intro heq; have := g.perm.injective heq; fin_cases e1 <;> simp [edgePairs] at this
  have hne2 : g.perm (edgePairs e2).1 ≠ g.perm (edgePairs e2).2 := by
    intro heq; have := g.perm.injective heq; fin_cases e2 <;> simp [edgePairs] at this
  have hp1 := hpair _ _ hne1
  have hp2 := hpair _ _ hne2
  change (edgeLookup (g.perm (edgePairs e1).1) (g.perm (edgePairs e1).2)).1 =
         (edgeLookup (g.perm (edgePairs e2).1) (g.perm (edgePairs e2).2)).1 at h
  rw [h] at hp1
  have hlt1 : (edgePairs e1).1 < (edgePairs e1).2 := by fin_cases e1 <;> decide
  have hlt2 : (edgePairs e2).1 < (edgePairs e2).2 := by fin_cases e2 <;> decide
  have heq_pairs : edgePairs e1 = edgePairs e2 := by
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
    · have h12 := h1.symm.trans h2
      exact Prod.ext (g.perm.injective (Prod.mk.inj h12).1) (g.perm.injective (Prod.mk.inj h12).2)
    · have h12 := h1.symm.trans h2
      have ha := g.perm.injective (Prod.mk.inj h12).1
      have hb := g.perm.injective (Prod.mk.inj h12).2
      omega
    · have h12 := h1.symm.trans h2
      have ha := g.perm.injective (Prod.mk.inj h12).1
      have hb := g.perm.injective (Prod.mk.inj h12).2
      omega
    · have h12 := h1.symm.trans h2
      exact Prod.ext (g.perm.injective (Prod.mk.inj h12).2) (g.perm.injective (Prod.mk.inj h12).1)
  have hinj : ∀ x y : Fin 15, edgePairs x = edgePairs y → x = y := by decide
  exact hinj e1 e2 heq_pairs

/-- Bijection on `Fin 15` induced by `g ∈ B6Plus`. -/
noncomputable def edgeEquiv (g : B6Plus) : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (edgeImgFun g)
    ((Finite.injective_iff_bijective).mp (edgeImgFun_injective g))

lemma toSkewMat_actB6Vec (g : B6Plus) (a : Fin 15 → ℝ) :
    toSkewMat (actB6Vec g a) = actB6Mat g (toSkewMat a) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [toSkewMat_diag]
    simp only [actB6Mat, toSkewMat_diag, mul_zero]
  · by_cases hlt : i < j
    · rcases edgePairs_surj_lt hlt with ⟨e, he⟩
      have h1 : toSkewMat (actB6Vec g a) (edgePairs e).1 (edgePairs e).2 = actB6Vec g a e :=
        toSkewMat_edge (actB6Vec g a) e
      have h2 : actB6Vec g a e = actB6Mat g (toSkewMat a) (edgePairs e).1 (edgePairs e).2 := rfl
      rw [he] at h1 h2
      exact h1.trans h2
    · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      rcases edgePairs_surj_lt hgt with ⟨e, he⟩
      have h1 : toSkewMat (actB6Vec g a) (edgePairs e).1 (edgePairs e).2 =
          actB6Mat g (toSkewMat a) (edgePairs e).1 (edgePairs e).2 :=
        toSkewMat_edge (actB6Vec g a) e
      rw [he] at h1
      dsimp only at h1
      rw [toSkewMat_swap, h1, actB6Mat_skew, neg_neg]

lemma actB6Vec_mul (g1 g2 : B6Plus) (a : Fin 15 → ℝ) :
    actB6Vec (g1 * g2) a = actB6Vec g1 (actB6Vec g2 a) := by
  ext e
  simp only [actB6Vec]
  rw [toSkewMat_actB6Vec, ← actB6Mat_mul]

lemma actB6Vec_one (a : Fin 15 → ℝ) : actB6Vec 1 a = a := by
  ext e
  simp only [actB6Vec, actB6Mat_one, toSkewMat_edge]

lemma actB6Mat_sq (g : B6Plus) (A : Matrix (Fin 6) (Fin 6) ℝ) (hA : A * A = -1) :
    actB6Mat g A * actB6Mat g A = -1 := by
  ext i j
  simp only [Matrix.mul_apply, actB6Mat]
  have h1 : ∑ k : Fin 6,
      (sgnReal (g.sgn i) * sgnReal (g.sgn k) * A (g.perm i) (g.perm k)) *
      (sgnReal (g.sgn k) * sgnReal (g.sgn j) * A (g.perm k) (g.perm j)) =
      sgnReal (g.sgn i) * sgnReal (g.sgn j) *
      ∑ k : Fin 6, A (g.perm i) (g.perm k) * A (g.perm k) (g.perm j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := sgnReal_sq (g.sgn k)
    calc (sgnReal (g.sgn i) * sgnReal (g.sgn k) * A (g.perm i) (g.perm k)) *
           (sgnReal (g.sgn k) * sgnReal (g.sgn j) * A (g.perm k) (g.perm j))
        = sgnReal (g.sgn i) * sgnReal (g.sgn j) *
            (sgnReal (g.sgn k) * sgnReal (g.sgn k)) *
            (A (g.perm i) (g.perm k) * A (g.perm k) (g.perm j)) := by ring
      _ = sgnReal (g.sgn i) * sgnReal (g.sgn j) *
            (A (g.perm i) (g.perm k) * A (g.perm k) (g.perm j)) := by rw [hk]; ring
  rw [h1]
  have hsum : ∑ k : Fin 6, A (g.perm i) (g.perm k) * A (g.perm k) (g.perm j) =
      (A * A) (g.perm i) (g.perm j) := by
    rw [Matrix.mul_apply]
    exact Fintype.sum_equiv g.perm _ _ (fun _ => rfl)
  rw [hsum, hA]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.neg_apply, Matrix.one_apply_eq]
    have hi := sgnReal_sq (g.sgn i)
    linarith
  · have hpij : g.perm i ≠ g.perm j := fun h => hij (g.perm.injective h)
    have h1 : (-1 : Matrix (Fin 6) (Fin 6) ℝ) (g.perm i) (g.perm j) = 0 := by
      change -((1 : Matrix (Fin 6) (Fin 6) ℝ) (g.perm i) (g.perm j)) = 0
      rw [Matrix.one_apply_ne hpij, neg_zero]
    have h2 : (-1 : Matrix (Fin 6) (Fin 6) ℝ) i j = 0 := by
      change -((1 : Matrix (Fin 6) (Fin 6) ℝ) i j) = 0
      rw [Matrix.one_apply_ne hij, neg_zero]
    rw [h1, h2, mul_zero]

lemma hodgePhi_actB6Mat (g : B6Plus) (A : Matrix (Fin 6) (Fin 6) ℝ) (i j : Fin 6) :
    hodgePhi (actB6Mat g A) i j =
      sgnReal (g.sgn i) * sgnReal (g.sgn j) * hodgePhi A (g.perm i) (g.perm j) := by
  unfold hodgePhi
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g.perm) _ _ fun σ => ?_
  have hml : (Equiv.mulLeft g.perm) σ = g.perm * σ := rfl
  rw [hml]
  have hcond : (σ 0 = i ∧ σ 1 = j) ↔ ((g.perm * σ) 0 = g.perm i ∧ (g.perm * σ) 1 = g.perm j) := by
    simp only [Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩; exact ⟨g.perm.injective h0, g.perm.injective h1⟩
  by_cases h1 : σ 0 = i ∧ σ 1 = j
  · have h2 : (g.perm * σ) 0 = g.perm i ∧ (g.perm * σ) 1 = g.perm j := hcond.mp h1
    rw [ite_eq_left_iff.mpr (fun hn => absurd h1 hn), ite_eq_left_iff.mpr (fun hn => absurd h2 hn)]
    simp only [Equiv.Perm.mul_apply]
    rcases h1 with ⟨h0, h1'⟩
    have hprod_all :
        sgnReal (g.sgn (σ 0)) * sgnReal (g.sgn (σ 1)) * sgnReal (g.sgn (σ 2)) *
        sgnReal (g.sgn (σ 3)) * sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5)) =
        ∏ k : Fin 6, sgnReal (g.sgn k) := by
      have hp := Fintype.prod_equiv σ (fun k => sgnReal (g.sgn (σ k)))
        (fun k => sgnReal (g.sgn k)) (fun _ => rfl)
      rw [← hp, Fin.prod_univ_six]
    have hdet : ((Equiv.Perm.sign g.perm : ℤ) : ℝ) * (∏ k : Fin 6, sgnReal (g.sgn k)) = 1 := by
      have hd := congrArg (Int.cast : ℤ → ℝ) g.det_one
      simp only [Int.cast_mul, Int.cast_prod, Int.cast_one, sgnInt_cast_real] at hd
      exact hd
    have hsgnsq : ((Equiv.Perm.sign g.perm : ℤ) : ℝ) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g.perm) with h | h <;> simp [h]
    have hdet_eq : ∏ k : Fin 6, sgnReal (g.sgn k) = ((Equiv.Perm.sign g.perm : ℤ) : ℝ) := by
      calc ∏ k : Fin 6, sgnReal (g.sgn k)
          = ((Equiv.Perm.sign g.perm : ℤ) : ℝ) ^ 2 * (∏ k : Fin 6, sgnReal (g.sgn k)) := by
              rw [hsgnsq, one_mul]
        _ = ((Equiv.Perm.sign g.perm : ℤ) : ℝ) *
              (((Equiv.Perm.sign g.perm : ℤ) : ℝ) * (∏ k : Fin 6, sgnReal (g.sgn k))) := by ring
        _ = ((Equiv.Perm.sign g.perm : ℤ) : ℝ) := by rw [hdet, mul_one]
    have h4 : sgnReal (g.sgn (σ 2)) * sgnReal (g.sgn (σ 3)) *
        sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5)) =
        sgnReal (g.sgn i) * sgnReal (g.sgn j) * ((Equiv.Perm.sign g.perm : ℤ) : ℝ) := by
      rw [h0, h1'] at hprod_all
      have hi := sgnReal_sq (g.sgn i)
      have hj := sgnReal_sq (g.sgn j)
      calc sgnReal (g.sgn (σ 2)) * sgnReal (g.sgn (σ 3)) *
             sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5))
          = (sgnReal (g.sgn i) * sgnReal (g.sgn i)) *
            (sgnReal (g.sgn j) * sgnReal (g.sgn j)) *
            (sgnReal (g.sgn (σ 2)) * sgnReal (g.sgn (σ 3)) *
             sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5))) := by rw [hi, hj]; ring
        _ = sgnReal (g.sgn i) * sgnReal (g.sgn j) *
            (sgnReal (g.sgn i) * sgnReal (g.sgn j) * sgnReal (g.sgn (σ 2)) *
             sgnReal (g.sgn (σ 3)) * sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5))) := by ring
        _ = sgnReal (g.sgn i) * sgnReal (g.sgn j) * (∏ k : Fin 6, sgnReal (g.sgn k)) := by
            rw [hprod_all]
        _ = sgnReal (g.sgn i) * sgnReal (g.sgn j) * ((Equiv.Perm.sign g.perm : ℤ) : ℝ) := by
            rw [hdet_eq]
    simp only [actB6Mat, map_mul, Units.val_mul, Int.cast_mul]
    calc ((Equiv.Perm.sign σ : ℤ) : ℝ) *
           (sgnReal (g.sgn (σ 2)) * sgnReal (g.sgn (σ 3)) * A (g.perm (σ 2)) (g.perm (σ 3))) *
           (sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5)) * A (g.perm (σ 4)) (g.perm (σ 5)))
        = (sgnReal (g.sgn (σ 2)) * sgnReal (g.sgn (σ 3)) *
           sgnReal (g.sgn (σ 4)) * sgnReal (g.sgn (σ 5))) *
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          A (g.perm (σ 2)) (g.perm (σ 3)) * A (g.perm (σ 4)) (g.perm (σ 5)) := by ring
      _ = (sgnReal (g.sgn i) * sgnReal (g.sgn j) * ((Equiv.Perm.sign g.perm : ℤ) : ℝ)) *
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          A (g.perm (σ 2)) (g.perm (σ 3)) * A (g.perm (σ 4)) (g.perm (σ 5)) := by rw [h4]
      _ = _ := by ring
  · have h2 : ¬ ((g.perm * σ) 0 = g.perm i ∧ (g.perm * σ) 1 = g.perm j) := mt hcond.mpr h1
    simp only [h1, h2, ite_false, mul_zero]

lemma isSkewOrth6_actB6 (g : B6Plus) {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    IsSkewOrth6 (actB6Vec g a) := by
  constructor
  · rw [toSkewMat_actB6Vec]
    exact actB6Mat_sq g (toSkewMat a) ha.1
  · intro i j
    rw [toSkewMat_actB6Vec, hodgePhi_actB6Mat, ha.2]
    simp only [actB6Mat]
    ring

/-! ### Transitivity of `B6Plus` on all 15 edges -/

/-- Explicit permutation for `edgePerm e`, sending `(0, 1) ↦ edgePairs e`. -/
def edgePermP : Fin 15 → Equiv.Perm (Fin 6)
  | 0  => 1
  | 1  => Equiv.swap 1 2
  | 2  => Equiv.swap 1 3
  | 3  => Equiv.swap 1 4
  | 4  => Equiv.swap 1 5
  | 5  => Equiv.swap 0 1 * Equiv.swap 1 2
  | 6  => Equiv.swap 0 1 * Equiv.swap 1 3
  | 7  => Equiv.swap 0 1 * Equiv.swap 1 4
  | 8  => Equiv.swap 0 1 * Equiv.swap 1 5
  | 9  => Equiv.swap 0 2 * Equiv.swap 1 3
  | 10 => Equiv.swap 0 2 * Equiv.swap 1 4
  | 11 => Equiv.swap 0 2 * Equiv.swap 1 5
  | 12 => Equiv.swap 0 3 * Equiv.swap 1 4
  | 13 => Equiv.swap 0 3 * Equiv.swap 1 5
  | 14 => Equiv.swap 0 4 * Equiv.swap 1 5

/-- Explicit sign vector for `edgePerm e`: flips coordinate `0` iff `e ∈ {1, 2, 3, 4}`. -/
def edgePermS (e : Fin 15) (i : Fin 6) : Bool :=
  (i == 0) && (e == 1 || e == 2 || e == 3 || e == 4)

/-- Explicit `B6Plus` element sending edge `0 = (0, 1)` to edge `e` (up to sign). -/
def edgePerm (e : Fin 15) : B6Plus where
  perm := edgePermP e
  sgn := edgePermS e
  det_one := by
    have hsw : ∀ x y : Fin 6, x ≠ y → Equiv.Perm.sign (Equiv.swap x y) = -1 :=
      fun _ _ h => Equiv.Perm.sign_swap h
    fin_cases e <;>
      simp [edgePermP, edgePermS, sgnInt, map_mul, hsw]

lemma edgePerm_maps_01 (e : Fin 15) :
    (edgePerm e).perm 0 = (edgePairs e).1 ∧ (edgePerm e).perm 1 = (edgePairs e).2 := by
  fin_cases e <;> decide

lemma actB6Vec_edgePerm_zero (e : Fin 15) (a : Fin 15 → ℝ) :
    actB6Vec (edgePerm e) a 0 = sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 1) * a e := by
  simp only [actB6Vec, actB6Mat, edgePairs]
  have h := edgePerm_maps_01 e
  rw [h.1, h.2, toSkewMat_edge]

lemma actB6Vec_edgePerm_zero_sq (e : Fin 15) (a : Fin 15 → ℝ) :
    (actB6Vec (edgePerm e) a 0) ^ 2 = (a e) ^ 2 := by
  rw [actB6Vec_edgePerm_zero]
  have hs0 : sgnReal ((edgePerm e).sgn 0) ^ 2 = 1 := by rw [sq]; exact sgnReal_sq _
  have hs1 : sgnReal ((edgePerm e).sgn 1) ^ 2 = 1 := by rw [sq]; exact sgnReal_sq _
  calc (sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 1) * a e) ^ 2
      = sgnReal ((edgePerm e).sgn 0) ^ 2 * sgnReal ((edgePerm e).sgn 1) ^ 2 * a e ^ 2 := by ring
    _ = a e ^ 2 := by rw [hs0, hs1]; ring

lemma actB6Vec_edgePerm_zero_pow4 (e : Fin 15) (a : Fin 15 → ℝ) :
    (actB6Vec (edgePerm e) a 0) ^ 4 = (a e) ^ 4 := by
  have h := actB6Vec_edgePerm_zero_sq e a
  calc (actB6Vec (edgePerm e) a 0) ^ 4 = ((actB6Vec (edgePerm e) a 0) ^ 2) ^ 2 := by ring
    _ = ((a e) ^ 2) ^ 2 := by rw [h]
    _ = (a e) ^ 4 := by ring

lemma sum_pow4_actB6Vec (g : B6Plus) (a : Fin 15 → ℝ) :
    ∑ e : Fin 15, (actB6Vec g a e) ^ 4 = ∑ e : Fin 15, (a e) ^ 4 := by
  have h1 : ∀ e : Fin 15, (actB6Vec g a e) ^ 4 = (a (edgeEquiv g e)) ^ 4 := by
    intro e
    rw [actB6Vec_apply]
    have hsq := edgeSgnFun_sq g e
    calc ((edgeSgnFun g e : ℝ) * a (edgeImgFun g e)) ^ 4
        = ((edgeSgnFun g e : ℝ) ^ 2) ^ 2 * (a (edgeImgFun g e)) ^ 4 := by ring
      _ = (a (edgeImgFun g e)) ^ 4 := by rw [hsq]; ring
      _ = (a (edgeEquiv g e)) ^ 4 := rfl
  simp_rw [h1]
  exact Fintype.sum_equiv (edgeEquiv g) _ _ (fun _ => rfl)

lemma sum_B6Plus_a0_pow4 (a : Fin 15 → ℝ) :
    ∑ h : B6Plus, (15 * (actB6Vec h a 0) ^ 4 - 3 / 4) =
      (Fintype.card B6Plus : ℝ) * ((∑ e : Fin 15, (a e) ^ 4) - 3 / 4) := by
  have hconst : ∀ e : Fin 15,
      ∑ h : B6Plus, (actB6Vec h a 0) ^ 4 = ∑ h : B6Plus, (actB6Vec h a e) ^ 4 := by
    intro e
    refine (Fintype.sum_equiv (Equiv.mulLeft (edgePerm e)) _ _ fun h => ?_).symm
    change (actB6Vec h a e) ^ 4 = (actB6Vec (edgePerm e * h) a 0) ^ 4
    rw [actB6Vec_mul, actB6Vec_edgePerm_zero_pow4]
  have h15 : 15 * ∑ h : B6Plus, (actB6Vec h a 0) ^ 4 =
      (Fintype.card B6Plus : ℝ) * ∑ e : Fin 15, (a e) ^ 4 := by
    calc 15 * ∑ h : B6Plus, (actB6Vec h a 0) ^ 4
        = ∑ _e : Fin 15, ∑ h : B6Plus, (actB6Vec h a 0) ^ 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
      _ = ∑ e : Fin 15, ∑ h : B6Plus, (actB6Vec h a e) ^ 4 :=
            Finset.sum_congr rfl fun e _ => hconst e
      _ = ∑ h : B6Plus, ∑ e : Fin 15, (actB6Vec h a e) ^ 4 := Finset.sum_comm
      _ = ∑ h : B6Plus, ∑ e : Fin 15, (a e) ^ 4 :=
            Finset.sum_congr rfl fun h _ => sum_pow4_actB6Vec h a
      _ = (Fintype.card B6Plus : ℝ) * ∑ e : Fin 15, (a e) ^ 4 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h15, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ### Explicit `su(4) ≅ so(6)` Embedding of Pure Two-Qubit States -/

/-- The 15 signed non-identity Pauli expectations of `ψ`, mapped into `so(6)` edges. -/
def so6Edge (ψ : State) : Fin 15 → ℝ
  | 0  =>  pauliExpRe ψ 3 0   -- +ZI  (0,1)
  | 1  => -pauliExpRe ψ 2 1   -- -YX  (0,2)
  | 2  =>  pauliExpRe ψ 2 2   -- +YY  (0,3)
  | 3  =>  pauliExpRe ψ 2 3   -- +YZ  (0,4)
  | 4  =>  pauliExpRe ψ 1 0   -- +XI  (0,5)
  | 5  => -pauliExpRe ψ 1 1   -- -XX  (1,2)
  | 6  =>  pauliExpRe ψ 1 2   -- +XY  (1,3)
  | 7  =>  pauliExpRe ψ 1 3   -- +XZ  (1,4)
  | 8  => -pauliExpRe ψ 2 0   -- -YI  (1,5)
  | 9  =>  pauliExpRe ψ 0 3   -- +IZ  (2,3)
  | 10 => -pauliExpRe ψ 0 2   -- -IY  (2,4)
  | 11 => -pauliExpRe ψ 3 1   -- -ZX  (2,5)
  | 12 => -pauliExpRe ψ 0 1   -- -IX  (3,4)
  | 13 =>  pauliExpRe ψ 3 2   -- +ZY  (3,5)
  | 14 =>  pauliExpRe ψ 3 3   -- +ZZ  (4,5)

lemma hodgePhi_diag_eq_zero (A : Matrix (Fin 6) (Fin 6) ℝ) (i : Fin 6) :
    hodgePhi A i i = 0 := by
  unfold hodgePhi
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hne : ¬ (σ 0 = i ∧ σ 1 = i) := by
    rintro ⟨h0, h1⟩
    have := σ.injective (h0.trans h1.symm)
    omega
  simp [hne]

lemma hodgePhi_swap (A : Matrix (Fin 6) (Fin 6) ℝ) (i j : Fin 6) :
    hodgePhi A j i = - hodgePhi A i j := by
  unfold hodgePhi
  rw [← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap (0 : Fin 6) 1)) _ _ fun σ => ?_
  have hmr : (Equiv.mulRight (Equiv.swap (0 : Fin 6) 1)) σ = σ * Equiv.swap 0 1 := rfl
  rw [hmr]
  have h0 : Equiv.swap (0 : Fin 6) 1 0 = 1 := by decide
  have h1 : Equiv.swap (0 : Fin 6) 1 1 = 0 := by decide
  have h2 : Equiv.swap (0 : Fin 6) 1 2 = 2 := by decide
  have h3 : Equiv.swap (0 : Fin 6) 1 3 = 3 := by decide
  have h4 : Equiv.swap (0 : Fin 6) 1 4 = 4 := by decide
  have h5 : Equiv.swap (0 : Fin 6) 1 5 = 5 := by decide
  have hs : Equiv.Perm.sign (Equiv.swap (0 : Fin 6) 1) = -1 := Equiv.Perm.sign_swap (by decide)
  have hcond : (σ 0 = j ∧ σ 1 = i) ↔
      ((σ * Equiv.swap (0 : Fin 6) 1) 0 = i ∧ (σ * Equiv.swap (0 : Fin 6) 1) 1 = j) := by
    simp only [Equiv.Perm.mul_apply, h0, h1]
    exact and_comm
  by_cases ha : σ 0 = j ∧ σ 1 = i
  · have hb : (σ * Equiv.swap (0 : Fin 6) 1) 0 = i ∧ (σ * Equiv.swap (0 : Fin 6) 1) 1 = j := hcond.mp ha
    simp only [ha, hb, Equiv.Perm.mul_apply, h2, h3, h4, h5, map_mul, hs, Units.val_mul]
    norm_num
  · have hb : ¬ ((σ * Equiv.swap (0 : Fin 6) 1) 0 = i ∧ (σ * Equiv.swap (0 : Fin 6) 1) 1 = j) := mt hcond.mpr ha
    simp only [ha, hb, ite_false, neg_zero]

/-- Helper: express `hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2` via `edgePerm e` and `hodgePhi_01`. -/
lemma hodgePhi_edge (a : Fin 15 → ℝ) (e : Fin 15) :
    hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2 =
      8 * sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 1) *
      (actB6Vec (edgePerm e) a 9 * actB6Vec (edgePerm e) a 14 -
       actB6Vec (edgePerm e) a 10 * actB6Vec (edgePerm e) a 13 +
       actB6Vec (edgePerm e) a 11 * actB6Vec (edgePerm e) a 12) := by
  have h1 := hodgePhi_actB6Mat (edgePerm e) (toSkewMat a) 0 1
  rw [← toSkewMat_actB6Vec, hodgePhi_01] at h1
  have hm := edgePerm_maps_01 e
  rw [hm.1, hm.2] at h1
  have hs0 := sgnReal_sq ((edgePerm e).sgn 0)
  have hs1 := sgnReal_sq ((edgePerm e).sgn 1)
  calc hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2
      = (sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 0)) *
        (sgnReal ((edgePerm e).sgn 1) * sgnReal ((edgePerm e).sgn 1)) *
        hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2 := by rw [hs0, hs1]; ring
    _ = sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 1) *
        (sgnReal ((edgePerm e).sgn 0) * sgnReal ((edgePerm e).sgn 1) *
         hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2) := by ring
    _ = _ := by rw [← h1]; ring

/-- Explicit sub-Pfaffian formulas for `hodgePhi (toSkewMat a)` on all 15 ordered edges `i < j`. -/
lemma hodgePhi_edge_formula (a : Fin 15 → ℝ) (e : Fin 15) :
    hodgePhi (toSkewMat a) (edgePairs e).1 (edgePairs e).2 =
      8 * match e with
        | 0  =>  (a 9 * a 14 - a 10 * a 13 + a 11 * a 12)
        | 1  => -(a 6 * a 14 - a 7 * a 13 + a 8 * a 12)
        | 2  =>  (a 5 * a 14 - a 7 * a 11 + a 8 * a 10)
        | 3  => -(a 5 * a 13 - a 6 * a 11 + a 8 * a 9)
        | 4  =>  (a 5 * a 12 - a 6 * a 10 + a 7 * a 9)
        | 5  =>  (a 2 * a 14 - a 3 * a 13 + a 4 * a 12)
        | 6  => -(a 1 * a 14 - a 3 * a 11 + a 4 * a 10)
        | 7  =>  (a 1 * a 13 - a 2 * a 11 + a 4 * a 9)
        | 8  => -(a 1 * a 12 - a 2 * a 10 + a 3 * a 9)
        | 9  =>  (a 0 * a 14 - a 3 * a 8 + a 4 * a 7)
        | 10 => -(a 0 * a 13 - a 2 * a 8 + a 4 * a 6)
        | 11 =>  (a 0 * a 12 - a 2 * a 7 + a 3 * a 6)
        | 12 =>  (a 0 * a 11 - a 1 * a 8 + a 4 * a 5)
        | 13 => -(a 0 * a 10 - a 1 * a 7 + a 3 * a 5)
        | 14 =>  (a 0 * a 9 - a 1 * a 6 + a 2 * a 5) := by
  rw [hodgePhi_edge]
  simp_rw [actB6Vec_apply, ← sgnInt_cast_real]
  revert e
  apply fin15_cases
  · have h : sgnInt ((edgePerm 0).sgn 0) = 1 ∧ sgnInt ((edgePerm 0).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 0) 9 = 1 ∧ edgeImgFun (edgePerm 0) 9 = 9 ∧
        edgeSgnFun (edgePerm 0) 14 = 1 ∧ edgeImgFun (edgePerm 0) 14 = 14 ∧
        edgeSgnFun (edgePerm 0) 10 = 1 ∧ edgeImgFun (edgePerm 0) 10 = 10 ∧
        edgeSgnFun (edgePerm 0) 13 = 1 ∧ edgeImgFun (edgePerm 0) 13 = 13 ∧
        edgeSgnFun (edgePerm 0) 11 = 1 ∧ edgeImgFun (edgePerm 0) 11 = 11 ∧
        edgeSgnFun (edgePerm 0) 12 = 1 ∧ edgeImgFun (edgePerm 0) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num
  · have h : sgnInt ((edgePerm 1).sgn 0) = -1 ∧ sgnInt ((edgePerm 1).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 1) 9 = 1 ∧ edgeImgFun (edgePerm 1) 9 = 6 ∧
        edgeSgnFun (edgePerm 1) 14 = 1 ∧ edgeImgFun (edgePerm 1) 14 = 14 ∧
        edgeSgnFun (edgePerm 1) 10 = 1 ∧ edgeImgFun (edgePerm 1) 10 = 7 ∧
        edgeSgnFun (edgePerm 1) 13 = 1 ∧ edgeImgFun (edgePerm 1) 13 = 13 ∧
        edgeSgnFun (edgePerm 1) 11 = 1 ∧ edgeImgFun (edgePerm 1) 11 = 8 ∧
        edgeSgnFun (edgePerm 1) 12 = 1 ∧ edgeImgFun (edgePerm 1) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 2).sgn 0) = -1 ∧ sgnInt ((edgePerm 2).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 2) 9 = -1 ∧ edgeImgFun (edgePerm 2) 9 = 5 ∧
        edgeSgnFun (edgePerm 2) 14 = 1 ∧ edgeImgFun (edgePerm 2) 14 = 14 ∧
        edgeSgnFun (edgePerm 2) 10 = 1 ∧ edgeImgFun (edgePerm 2) 10 = 10 ∧
        edgeSgnFun (edgePerm 2) 13 = 1 ∧ edgeImgFun (edgePerm 2) 13 = 8 ∧
        edgeSgnFun (edgePerm 2) 11 = 1 ∧ edgeImgFun (edgePerm 2) 11 = 11 ∧
        edgeSgnFun (edgePerm 2) 12 = 1 ∧ edgeImgFun (edgePerm 2) 12 = 7 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 3).sgn 0) = -1 ∧ sgnInt ((edgePerm 3).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 3) 9 = 1 ∧ edgeImgFun (edgePerm 3) 9 = 9 ∧
        edgeSgnFun (edgePerm 3) 14 = 1 ∧ edgeImgFun (edgePerm 3) 14 = 8 ∧
        edgeSgnFun (edgePerm 3) 10 = -1 ∧ edgeImgFun (edgePerm 3) 10 = 5 ∧
        edgeSgnFun (edgePerm 3) 13 = 1 ∧ edgeImgFun (edgePerm 3) 13 = 13 ∧
        edgeSgnFun (edgePerm 3) 11 = 1 ∧ edgeImgFun (edgePerm 3) 11 = 11 ∧
        edgeSgnFun (edgePerm 3) 12 = -1 ∧ edgeImgFun (edgePerm 3) 12 = 6 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 4).sgn 0) = -1 ∧ sgnInt ((edgePerm 4).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 4) 9 = 1 ∧ edgeImgFun (edgePerm 4) 9 = 9 ∧
        edgeSgnFun (edgePerm 4) 14 = -1 ∧ edgeImgFun (edgePerm 4) 14 = 7 ∧
        edgeSgnFun (edgePerm 4) 10 = 1 ∧ edgeImgFun (edgePerm 4) 10 = 10 ∧
        edgeSgnFun (edgePerm 4) 13 = -1 ∧ edgeImgFun (edgePerm 4) 13 = 6 ∧
        edgeSgnFun (edgePerm 4) 11 = -1 ∧ edgeImgFun (edgePerm 4) 11 = 5 ∧
        edgeSgnFun (edgePerm 4) 12 = 1 ∧ edgeImgFun (edgePerm 4) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 5).sgn 0) = 1 ∧ sgnInt ((edgePerm 5).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 5) 9 = 1 ∧ edgeImgFun (edgePerm 5) 9 = 2 ∧
        edgeSgnFun (edgePerm 5) 14 = 1 ∧ edgeImgFun (edgePerm 5) 14 = 14 ∧
        edgeSgnFun (edgePerm 5) 10 = 1 ∧ edgeImgFun (edgePerm 5) 10 = 3 ∧
        edgeSgnFun (edgePerm 5) 13 = 1 ∧ edgeImgFun (edgePerm 5) 13 = 13 ∧
        edgeSgnFun (edgePerm 5) 11 = 1 ∧ edgeImgFun (edgePerm 5) 11 = 4 ∧
        edgeSgnFun (edgePerm 5) 12 = 1 ∧ edgeImgFun (edgePerm 5) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num
  · have h : sgnInt ((edgePerm 6).sgn 0) = 1 ∧ sgnInt ((edgePerm 6).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 6) 9 = -1 ∧ edgeImgFun (edgePerm 6) 9 = 1 ∧
        edgeSgnFun (edgePerm 6) 14 = 1 ∧ edgeImgFun (edgePerm 6) 14 = 14 ∧
        edgeSgnFun (edgePerm 6) 10 = 1 ∧ edgeImgFun (edgePerm 6) 10 = 10 ∧
        edgeSgnFun (edgePerm 6) 13 = 1 ∧ edgeImgFun (edgePerm 6) 13 = 4 ∧
        edgeSgnFun (edgePerm 6) 11 = 1 ∧ edgeImgFun (edgePerm 6) 11 = 11 ∧
        edgeSgnFun (edgePerm 6) 12 = 1 ∧ edgeImgFun (edgePerm 6) 12 = 3 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 7).sgn 0) = 1 ∧ sgnInt ((edgePerm 7).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 7) 9 = 1 ∧ edgeImgFun (edgePerm 7) 9 = 9 ∧
        edgeSgnFun (edgePerm 7) 14 = 1 ∧ edgeImgFun (edgePerm 7) 14 = 4 ∧
        edgeSgnFun (edgePerm 7) 10 = -1 ∧ edgeImgFun (edgePerm 7) 10 = 1 ∧
        edgeSgnFun (edgePerm 7) 13 = 1 ∧ edgeImgFun (edgePerm 7) 13 = 13 ∧
        edgeSgnFun (edgePerm 7) 11 = 1 ∧ edgeImgFun (edgePerm 7) 11 = 11 ∧
        edgeSgnFun (edgePerm 7) 12 = -1 ∧ edgeImgFun (edgePerm 7) 12 = 2 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 8).sgn 0) = 1 ∧ sgnInt ((edgePerm 8).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 8) 9 = 1 ∧ edgeImgFun (edgePerm 8) 9 = 9 ∧
        edgeSgnFun (edgePerm 8) 14 = -1 ∧ edgeImgFun (edgePerm 8) 14 = 3 ∧
        edgeSgnFun (edgePerm 8) 10 = 1 ∧ edgeImgFun (edgePerm 8) 10 = 10 ∧
        edgeSgnFun (edgePerm 8) 13 = -1 ∧ edgeImgFun (edgePerm 8) 13 = 2 ∧
        edgeSgnFun (edgePerm 8) 11 = -1 ∧ edgeImgFun (edgePerm 8) 11 = 1 ∧
        edgeSgnFun (edgePerm 8) 12 = 1 ∧ edgeImgFun (edgePerm 8) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 9).sgn 0) = 1 ∧ sgnInt ((edgePerm 9).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 9) 9 = 1 ∧ edgeImgFun (edgePerm 9) 9 = 0 ∧
        edgeSgnFun (edgePerm 9) 14 = 1 ∧ edgeImgFun (edgePerm 9) 14 = 14 ∧
        edgeSgnFun (edgePerm 9) 10 = 1 ∧ edgeImgFun (edgePerm 9) 10 = 3 ∧
        edgeSgnFun (edgePerm 9) 13 = 1 ∧ edgeImgFun (edgePerm 9) 13 = 8 ∧
        edgeSgnFun (edgePerm 9) 11 = 1 ∧ edgeImgFun (edgePerm 9) 11 = 4 ∧
        edgeSgnFun (edgePerm 9) 12 = 1 ∧ edgeImgFun (edgePerm 9) 12 = 7 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num
  · have h : sgnInt ((edgePerm 10).sgn 0) = 1 ∧ sgnInt ((edgePerm 10).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 10) 9 = 1 ∧ edgeImgFun (edgePerm 10) 9 = 2 ∧
        edgeSgnFun (edgePerm 10) 14 = 1 ∧ edgeImgFun (edgePerm 10) 14 = 8 ∧
        edgeSgnFun (edgePerm 10) 10 = 1 ∧ edgeImgFun (edgePerm 10) 10 = 0 ∧
        edgeSgnFun (edgePerm 10) 13 = 1 ∧ edgeImgFun (edgePerm 10) 13 = 13 ∧
        edgeSgnFun (edgePerm 10) 11 = 1 ∧ edgeImgFun (edgePerm 10) 11 = 4 ∧
        edgeSgnFun (edgePerm 10) 12 = -1 ∧ edgeImgFun (edgePerm 10) 12 = 6 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 11).sgn 0) = 1 ∧ sgnInt ((edgePerm 11).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 11) 9 = 1 ∧ edgeImgFun (edgePerm 11) 9 = 2 ∧
        edgeSgnFun (edgePerm 11) 14 = -1 ∧ edgeImgFun (edgePerm 11) 14 = 7 ∧
        edgeSgnFun (edgePerm 11) 10 = 1 ∧ edgeImgFun (edgePerm 11) 10 = 3 ∧
        edgeSgnFun (edgePerm 11) 13 = -1 ∧ edgeImgFun (edgePerm 11) 13 = 6 ∧
        edgeSgnFun (edgePerm 11) 11 = 1 ∧ edgeImgFun (edgePerm 11) 11 = 0 ∧
        edgeSgnFun (edgePerm 11) 12 = 1 ∧ edgeImgFun (edgePerm 11) 12 = 12 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 12).sgn 0) = 1 ∧ sgnInt ((edgePerm 12).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 12) 9 = -1 ∧ edgeImgFun (edgePerm 12) 9 = 1 ∧
        edgeSgnFun (edgePerm 12) 14 = 1 ∧ edgeImgFun (edgePerm 12) 14 = 8 ∧
        edgeSgnFun (edgePerm 12) 10 = -1 ∧ edgeImgFun (edgePerm 12) 10 = 5 ∧
        edgeSgnFun (edgePerm 12) 13 = 1 ∧ edgeImgFun (edgePerm 12) 13 = 4 ∧
        edgeSgnFun (edgePerm 12) 11 = 1 ∧ edgeImgFun (edgePerm 12) 11 = 11 ∧
        edgeSgnFun (edgePerm 12) 12 = 1 ∧ edgeImgFun (edgePerm 12) 12 = 0 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 13).sgn 0) = 1 ∧ sgnInt ((edgePerm 13).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 13) 9 = -1 ∧ edgeImgFun (edgePerm 13) 9 = 1 ∧
        edgeSgnFun (edgePerm 13) 14 = -1 ∧ edgeImgFun (edgePerm 13) 14 = 7 ∧
        edgeSgnFun (edgePerm 13) 10 = 1 ∧ edgeImgFun (edgePerm 13) 10 = 10 ∧
        edgeSgnFun (edgePerm 13) 13 = 1 ∧ edgeImgFun (edgePerm 13) 13 = 0 ∧
        edgeSgnFun (edgePerm 13) 11 = -1 ∧ edgeImgFun (edgePerm 13) 11 = 5 ∧
        edgeSgnFun (edgePerm 13) 12 = 1 ∧ edgeImgFun (edgePerm 13) 12 = 3 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring
  · have h : sgnInt ((edgePerm 14).sgn 0) = 1 ∧ sgnInt ((edgePerm 14).sgn 1) = 1 ∧
        edgeSgnFun (edgePerm 14) 9 = 1 ∧ edgeImgFun (edgePerm 14) 9 = 9 ∧
        edgeSgnFun (edgePerm 14) 14 = 1 ∧ edgeImgFun (edgePerm 14) 14 = 0 ∧
        edgeSgnFun (edgePerm 14) 10 = -1 ∧ edgeImgFun (edgePerm 14) 10 = 1 ∧
        edgeSgnFun (edgePerm 14) 13 = -1 ∧ edgeImgFun (edgePerm 14) 13 = 6 ∧
        edgeSgnFun (edgePerm 14) 11 = -1 ∧ edgeImgFun (edgePerm 14) 11 = 5 ∧
        edgeSgnFun (edgePerm 14) 12 = -1 ∧ edgeImgFun (edgePerm 14) 12 = 2 := by decide
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]; norm_num; ring

/-- Standalone expansion of diagonal entries of `(toSkewMat a)^2` (avoids unfolding `ψ`). -/
lemma toSkewMat_sq_diag (a : Fin 15 → ℝ) (i : Fin 6) :
    (toSkewMat a * toSkewMat a) i i =
      - match i with
        | 0 => a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2
        | 1 => a 0 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2
        | 2 => a 1 ^ 2 + a 5 ^ 2 + a 9 ^ 2 + a 10 ^ 2 + a 11 ^ 2
        | 3 => a 2 ^ 2 + a 6 ^ 2 + a 9 ^ 2 + a 12 ^ 2 + a 13 ^ 2
        | 4 => a 3 ^ 2 + a 7 ^ 2 + a 10 ^ 2 + a 12 ^ 2 + a 14 ^ 2
        | 5 => a 4 ^ 2 + a 8 ^ 2 + a 11 ^ 2 + a 13 ^ 2 + a 14 ^ 2 := by
  revert i
  apply fin6_cases <;>
    (simp only [Matrix.mul_apply, Fin.sum_univ_six, toSkewMat, edgeLookup,
      Int.cast_zero, Int.cast_one, Int.cast_neg]; ring)

set_option maxHeartbeats 800000 in
/-- Standalone expansion of upper-triangular entries of `(toSkewMat a)^2`. -/
lemma toSkewMat_sq_off (a : Fin 15 → ℝ) (e : Fin 15) :
    (toSkewMat a * toSkewMat a) (edgePairs e).1 (edgePairs e).2 =
      match e with
      | 0  => -(a 1 * a 5 + a 2 * a 6 + a 3 * a 7 + a 4 * a 8)
      | 1  =>   a 0 * a 5 - a 2 * a 9 - a 3 * a 10 - a 4 * a 11
      | 2  =>   a 0 * a 6 + a 1 * a 9 - a 3 * a 12 - a 4 * a 13
      | 3  =>   a 0 * a 7 + a 1 * a 10 + a 2 * a 12 - a 4 * a 14
      | 4  =>   a 0 * a 8 + a 1 * a 11 + a 2 * a 13 + a 3 * a 14
      | 5  => -(a 0 * a 1 + a 6 * a 9 + a 7 * a 10 + a 8 * a 11)
      | 6  => -(a 0 * a 2 - a 5 * a 9 + a 7 * a 12 + a 8 * a 13)
      | 7  => -(a 0 * a 3 - a 5 * a 10 - a 6 * a 12 + a 8 * a 14)
      | 8  => -(a 0 * a 4 - a 5 * a 11 - a 6 * a 13 - a 7 * a 14)
      | 9  => -(a 1 * a 2 + a 5 * a 6 + a 10 * a 12 + a 11 * a 13)
      | 10 => -(a 1 * a 3 + a 5 * a 7 - a 9 * a 12 + a 11 * a 14)
      | 11 => -(a 1 * a 4 + a 5 * a 8 - a 9 * a 13 - a 10 * a 14)
      | 12 => -(a 2 * a 3 + a 6 * a 7 + a 9 * a 10 + a 13 * a 14)
      | 13 => -(a 2 * a 4 + a 6 * a 8 + a 9 * a 11 - a 12 * a 14)
      | 14 => -(a 3 * a 4 + a 7 * a 8 + a 10 * a 11 + a 12 * a 13) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_six, toSkewMat]
  revert e
  apply fin15_cases <;>
    (dsimp only [edgePairs, edgeLookup]; simp only [Int.cast_zero, Int.cast_one, Int.cast_neg]; ring)

/-- Every normalized pure two-qubit state maps into the `SO(6)` self-dual skew-orthogonal manifold. -/
theorem so6Edge_isSkewOrth6 {ψ : State} (hψ : IsNormalized ψ) :
    IsSkewOrth6 (so6Edge ψ) := by
  have hnorm : (ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2 = 1 := by
    rw [← normSq_eq_sum_re_im]; exact hψ
  have hnorm2 : ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 + (ψ 1).re ^ 2 + (ψ 1).im ^ 2 +
      (ψ 2).re ^ 2 + (ψ 2).im ^ 2 + (ψ 3).re ^ 2 + (ψ 3).im ^ 2) ^ 2 = 1 := by
    rw [hnorm]; ring
  have ha0  : so6Edge ψ 0  =  pauliExpRe ψ 3 0 := rfl
  have ha1  : so6Edge ψ 1  = -pauliExpRe ψ 2 1 := rfl
  have ha2  : so6Edge ψ 2  =  pauliExpRe ψ 2 2 := rfl
  have ha3  : so6Edge ψ 3  =  pauliExpRe ψ 2 3 := rfl
  have ha4  : so6Edge ψ 4  =  pauliExpRe ψ 1 0 := rfl
  have ha5  : so6Edge ψ 5  = -pauliExpRe ψ 1 1 := rfl
  have ha6  : so6Edge ψ 6  =  pauliExpRe ψ 1 2 := rfl
  have ha7  : so6Edge ψ 7  =  pauliExpRe ψ 1 3 := rfl
  have ha8  : so6Edge ψ 8  = -pauliExpRe ψ 2 0 := rfl
  have ha9  : so6Edge ψ 9  =  pauliExpRe ψ 0 3 := rfl
  have ha10 : so6Edge ψ 10 = -pauliExpRe ψ 0 2 := rfl
  have ha11 : so6Edge ψ 11 = -pauliExpRe ψ 3 1 := rfl
  have ha12 : so6Edge ψ 12 = -pauliExpRe ψ 0 1 := rfl
  have ha13 : so6Edge ψ 13 =  pauliExpRe ψ 3 2 := rfl
  have ha14 : so6Edge ψ 14 =  pauliExpRe ψ 3 3 := rfl
  rw [pauliExpRe_ZI] at ha0;  rw [pauliExpRe_YX] at ha1;  rw [pauliExpRe_YY] at ha2
  rw [pauliExpRe_YZ] at ha3;  rw [pauliExpRe_XI] at ha4;  rw [pauliExpRe_XX] at ha5
  rw [pauliExpRe_XY] at ha6;  rw [pauliExpRe_XZ] at ha7;  rw [pauliExpRe_YI] at ha8
  rw [pauliExpRe_IZ] at ha9;  rw [pauliExpRe_IY] at ha10; rw [pauliExpRe_ZX] at ha11
  rw [pauliExpRe_IX] at ha12; rw [pauliExpRe_ZY] at ha13; rw [pauliExpRe_ZZ] at ha14
  constructor
  · have hsym : ∀ i j : Fin 6,
        (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ)) j i =
        (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ)) i j := by
      intro i j
      have hT : (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ))ᵀ =
          toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ) := by
        rw [Matrix.transpose_mul, toSkewMat_transpose]; simp
      exact congrFun (congrFun hT i) j
    have hdiag : ∀ i : Fin 6, (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ)) i i = -1 := by
      intro i
      rw [toSkewMat_sq_diag, ← hnorm2]
      revert i; apply fin6_cases
      · dsimp only; rw [ha0, ha1, ha2, ha3, ha4]; ring
      · dsimp only; rw [ha0, ha5, ha6, ha7, ha8]; ring
      · dsimp only; rw [ha1, ha5, ha9, ha10, ha11]; ring
      · dsimp only; rw [ha2, ha6, ha9, ha12, ha13]; ring
      · dsimp only; rw [ha3, ha7, ha10, ha12, ha14]; ring
      · dsimp only; rw [ha4, ha8, ha11, ha13, ha14]; ring
    have hoff : ∀ e : Fin 15,
        (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ)) (edgePairs e).1 (edgePairs e).2 = 0 := by
      intro e
      rw [toSkewMat_sq_off]
      revert e; apply fin15_cases
      · dsimp only; rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]; ring
      · dsimp only; rw [ha0, ha2, ha3, ha4, ha5, ha9, ha10, ha11]; ring
      · dsimp only; rw [ha0, ha1, ha3, ha4, ha6, ha9, ha12, ha13]; ring
      · dsimp only; rw [ha0, ha1, ha2, ha4, ha7, ha10, ha12, ha14]; ring
      · dsimp only; rw [ha0, ha1, ha2, ha3, ha8, ha11, ha13, ha14]; ring
      · dsimp only; rw [ha0, ha1, ha6, ha7, ha8, ha9, ha10, ha11]; ring
      · dsimp only; rw [ha0, ha2, ha5, ha7, ha8, ha9, ha12, ha13]; ring
      · dsimp only; rw [ha0, ha3, ha5, ha6, ha8, ha10, ha12, ha14]; ring
      · dsimp only; rw [ha0, ha4, ha5, ha6, ha7, ha11, ha13, ha14]; ring
      · dsimp only; rw [ha1, ha2, ha5, ha6, ha10, ha11, ha12, ha13]; ring
      · dsimp only; rw [ha1, ha3, ha5, ha7, ha9, ha11, ha12, ha14]; ring
      · dsimp only; rw [ha1, ha4, ha5, ha8, ha9, ha10, ha13, ha14]; ring
      · dsimp only; rw [ha2, ha3, ha6, ha7, ha9, ha10, ha13, ha14]; ring
      · dsimp only; rw [ha2, ha4, ha6, ha8, ha9, ha11, ha12, ha14]; ring
      · dsimp only; rw [ha3, ha4, ha7, ha8, ha10, ha11, ha12, ha13]; ring
    ext i j
    by_cases hij : i = j
    · subst hij
      change (toSkewMat (so6Edge ψ) * toSkewMat (so6Edge ψ)) i i = -((1 : Matrix (Fin 6) (Fin 6) ℝ) i i)
      rw [Matrix.one_apply_eq]
      exact hdiag i
    · have hrhs : (-1 : Matrix (Fin 6) (Fin 6) ℝ) i j = 0 := by
        change -((1 : Matrix (Fin 6) (Fin 6) ℝ) i j) = 0
        rw [Matrix.one_apply_ne hij, neg_zero]
      rw [hrhs]
      by_cases hlt : i < j
      · rcases edgePairs_surj_lt hlt with ⟨e, he⟩
        have h := hoff e
        rw [he] at h
        exact h
      · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
        rcases edgePairs_surj_lt hgt with ⟨e, he⟩
        have h := hoff e
        rw [he] at h
        rw [hsym j i]
        exact h
  · have hedge : ∀ e : Fin 15,
        hodgePhi (toSkewMat (so6Edge ψ)) (edgePairs e).1 (edgePairs e).2 =
        8 * toSkewMat (so6Edge ψ) (edgePairs e).1 (edgePairs e).2 := by
      intro e
      rw [hodgePhi_edge_formula, toSkewMat_edge]
      have hmul1 : ∀ x : ℝ, 8 * x = 8 * (x * ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 +
          (ψ 1).re ^ 2 + (ψ 1).im ^ 2 + (ψ 2).re ^ 2 + (ψ 2).im ^ 2 +
          (ψ 3).re ^ 2 + (ψ 3).im ^ 2)) := fun x => by rw [hnorm, mul_one]
      conv_rhs => rw [hmul1]
      revert e; apply fin15_cases
      · dsimp only; rw [ha0, ha9, ha10, ha11, ha12, ha13, ha14]; ring
      · dsimp only; rw [ha1, ha6, ha7, ha8, ha12, ha13, ha14]; ring
      · dsimp only; rw [ha2, ha5, ha7, ha8, ha10, ha11, ha14]; ring
      · dsimp only; rw [ha3, ha5, ha6, ha8, ha9, ha11, ha13]; ring
      · dsimp only; rw [ha4, ha5, ha6, ha7, ha9, ha10, ha12]; ring
      · dsimp only; rw [ha5, ha2, ha3, ha4, ha12, ha13, ha14]; ring
      · dsimp only; rw [ha6, ha1, ha3, ha4, ha10, ha11, ha14]; ring
      · dsimp only; rw [ha7, ha1, ha2, ha4, ha9, ha11, ha13]; ring
      · dsimp only; rw [ha8, ha1, ha2, ha3, ha9, ha10, ha12]; ring
      · dsimp only; rw [ha9, ha0, ha3, ha4, ha7, ha8, ha14]; ring
      · dsimp only; rw [ha10, ha0, ha2, ha4, ha6, ha8, ha13]; ring
      · dsimp only; rw [ha11, ha0, ha2, ha3, ha6, ha7, ha12]; ring
      · dsimp only; rw [ha12, ha0, ha1, ha4, ha5, ha8, ha11]; ring
      · dsimp only; rw [ha13, ha0, ha1, ha3, ha5, ha7, ha10]; ring
      · dsimp only; rw [ha14, ha0, ha1, ha2, ha5, ha6, ha9]; ring
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hodgePhi_diag_eq_zero, toSkewMat_diag, mul_zero]
    · by_cases hlt : i < j
      · rcases edgePairs_surj_lt hlt with ⟨e, he⟩
        have h := hedge e
        rw [he] at h
        exact h
      · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
        rcases edgePairs_surj_lt hgt with ⟨e, he⟩
        have h := hedge e
        rw [he] at h
        rw [hodgePhi_swap, toSkewMat_swap, h]
        ring

/-- For any normalized pure state, the `2α`-th Pauli moment splits as `1 + ∑_{e=0}^{14} |a_e|^{2α}`. -/
lemma pauliMoment_eq_one_add_so6 (ψ : State) (hψ : IsNormalized ψ) (α : ℝ) :
    pauliMoment ψ α = 1 + ∑ e : Fin 15, |so6Edge ψ e| ^ (2 * α) := by
  unfold pauliMoment
  simp only [Fin.sum_univ_four, norm_pauliExp]
  have h00 : |pauliExpRe ψ 0 0| = 1 := by
    rw [pauliExpRe_II, hψ]; norm_num
  rw [h00, Real.one_rpow, sum_fin15]
  simp only [so6Edge, abs_neg]
  ring

/-- For any normalized pure state, the 4th Pauli moment equals `1 + ∑_{e=0}^{14} (so6Edge ψ e)^4`. -/
lemma pauli_sum_pow4_eq_one_add_so6 {ψ : State} (hψ : IsNormalized ψ) :
    ∑ a : Fin 4, ∑ b : Fin 4, ‖pauliExp ψ a b‖ ^ 4 =
      1 + ∑ e : Fin 15, (so6Edge ψ e) ^ 4 := by
  simp only [Fin.sum_univ_four, norm_pauliExp]
  have h00 : |pauliExpRe ψ 0 0| = 1 := by
    rw [pauliExpRe_II, hψ]; norm_num
  rw [h00, sum_fin15]
  simp only [so6Edge,
    show ∀ x : ℝ, |x| ^ 4 = x ^ 4 from fun x => by
      have : |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      rw [this, sq_abs]; ring]
  ring

end TwoQubitMaximalMagic
