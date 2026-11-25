import TwoQubitMaximalMagic.SO6Reduction
import Mathlib.Tactic

/-!
# Fast Sparse Polynomial Engine & `B₆⁺` Orbit-Cancellation Kernel Verifier

This module provides a pure-kernel (zero `native_decide`) polynomial engine over
`ℤ[a₀, ..., a₁₄]` with base-16 bit-packed monomials (`m < 16^15`), structural-recursion
merge-sort normalization `normPoly`, computable `B₆⁺` witnesses `B6Wit`, and the master
orbit-cancellation theorem `sum_B6Plus_evalPoly_eq_zero_of_verify`.
-/

namespace TwoQubitMaximalMagic

/-! ### Base-16 Packed Monomials -/

/-- Extract the exponent of variable `e : Fin 15` from a base-16 packed monomial `m : ℕ`. -/
def monomDigit (m : ℕ) (e : Fin 15) : ℕ :=
  (m / 16 ^ e.val) % 16

/-- Evaluate a base-16 packed monomial `m : ℕ` at `a : Fin 15 → ℝ`. -/
def evalMonom (m : ℕ) (a : Fin 15 → ℝ) : ℝ :=
  ∏ e : Fin 15, (a e) ^ (monomDigit m e)

lemma base16_digit_sum (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i < n, f i < 16) :
    (∑ i ∈ Finset.range n, f i * 16 ^ i) < 16 ^ n ∧
    ∀ k < n, ((∑ i ∈ Finset.range n, f i * 16 ^ i) / 16 ^ k) % 16 = f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfn : f n < 16 := hf n (Nat.lt_succ_self n)
    have ⟨hS_lt, hS_dig⟩ := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    rw [Finset.sum_range_succ]
    set S := ∑ i ∈ Finset.range n, f i * 16 ^ i
    constructor
    · have h16 : 16 ^ (n + 1) = 16 ^ n + 15 * 16 ^ n := by ring
      have hmul : f n * 16 ^ n ≤ 15 * 16 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
    · intro k hk
      by_cases hkn : k = n
      · subst hkn
        have hpos : 0 < 16 ^ k := by positivity
        rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hS_lt, zero_add, Nat.mod_eq_of_lt hfn]
      · have hlt : k < n := by omega
        have hpow : 16 ^ n = (16 * 16 ^ (n - 1 - k)) * 16 ^ k := by
          have : n = 1 + (n - 1 - k) + k := by omega
          conv_lhs => rw [this]
          ring
        have hpos : 0 < 16 ^ k := by positivity
        have hrew : S + f n * 16 ^ n = S + (f n * 16 * 16 ^ (n - 1 - k)) * 16 ^ k := by
          rw [hpow]; ring
        rw [hrew, Nat.add_mul_div_right _ _ hpos]
        have hmod : (S / 16 ^ k + f n * 16 * 16 ^ (n - 1 - k)) % 16 = (S / 16 ^ k) % 16 := by
          have : f n * 16 * 16 ^ (n - 1 - k) = 16 * (f n * 16 ^ (n - 1 - k)) := by ring
          rw [this, Nat.add_mul_mod_self_left]
        rw [hmod]
        exact hS_dig k hlt

lemma monomDigit_pack (f : Fin 15 → ℕ) (hf : ∀ e : Fin 15, f e < 16) (e₀ : Fin 15) :
    monomDigit (∑ e : Fin 15, f e * 16 ^ e.val) e₀ = f e₀ := by
  let g : ℕ → ℕ := fun i => if h : i < 15 then f ⟨i, h⟩ else 0
  have hg : ∀ i < 15, g i < 16 := fun i hi => by
    simp only [g, hi, ↓reduceDIte]; exact hf ⟨i, hi⟩
  have hsum : (∑ e : Fin 15, f e * 16 ^ e.val) = ∑ i ∈ Finset.range 15, g i * 16 ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => g i * 16 ^ i)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [g, e.isLt]
  unfold monomDigit
  rw [hsum, (base16_digit_sum 15 g hg).2 e₀.val e₀.isLt]
  simp [g, e₀.isLt]

lemma base16_div_add (k m1 m2 : ℕ)
    (h : ∀ i < k, (m1 / 16 ^ i) % 16 + (m2 / 16 ^ i) % 16 < 16) :
    (m1 + m2) / 16 ^ k = m1 / 16 ^ k + m2 / 16 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hmod := h k (Nat.lt_succ_self k)
    have hpow : 16 ^ (k + 1) = 16 ^ k * 16 := by ring
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hk]
    omega

lemma monomDigit_add (m1 m2 : ℕ)
    (h : ∀ e : Fin 15, monomDigit m1 e + monomDigit m2 e < 16) (e : Fin 15) :
    monomDigit (m1 + m2) e = monomDigit m1 e + monomDigit m2 e := by
  unfold monomDigit
  have hdiv : (m1 + m2) / 16 ^ e.val = m1 / 16 ^ e.val + m2 / 16 ^ e.val := by
    apply base16_div_add
    intro i hi
    have hi15 : i < 15 := lt_trans hi e.isLt
    exact h ⟨i, hi15⟩
  rw [hdiv]
  have he := h e
  unfold monomDigit at he
  omega

lemma evalMonom_add (m1 m2 : ℕ) (a : Fin 15 → ℝ)
    (h : ∀ e : Fin 15, monomDigit m1 e + monomDigit m2 e < 16) :
    evalMonom (m1 + m2) a = evalMonom m1 a * evalMonom m2 a := by
  unfold evalMonom
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [monomDigit_add m1 m2 h e, pow_add]

lemma evalMonom_zero (a : Fin 15 → ℝ) : evalMonom 0 a = 1 := by
  simp [evalMonom, monomDigit]

/-! ### Sparse Polynomials, Structural-Recursion Merge Sort & Soundness -/

/-- A sparse polynomial in `ℤ[a₀, ..., a₁₄]` stored as a list of `(coeff, packed_monom)` pairs. -/
abbrev Poly := List (ℤ × ℕ)

/-- Evaluate a sparse polynomial at `a : Fin 15 → ℝ`. -/
def evalPoly (p : Poly) (a : Fin 15 → ℝ) : ℝ :=
  (p.map fun t => (t.1 : ℝ) * evalMonom t.2 a).sum

@[simp] lemma evalPoly_nil (a : Fin 15 → ℝ) : evalPoly [] a = 0 := rfl

@[simp] lemma evalPoly_cons (c : ℤ) (m : ℕ) (rest : Poly) (a : Fin 15 → ℝ) :
    evalPoly ((c, m) :: rest) a = (c : ℝ) * evalMonom m a + evalPoly rest a := rfl

lemma evalPoly_append (p q : Poly) (a : Fin 15 → ℝ) :
    evalPoly (p ++ q) a = evalPoly p a + evalPoly q a := by
  simp [evalPoly]

/-- Scale every coefficient of a polynomial by an integer `k`. -/
def scalePoly (k : ℤ) (p : Poly) : Poly :=
  p.map fun t => (k * t.1, t.2)

lemma evalPoly_scalePoly (k : ℤ) (p : Poly) (a : Fin 15 → ℝ) :
    evalPoly (scalePoly k p) a = (k : ℝ) * evalPoly p a := by
  induction p with
  | nil => simp [scalePoly]
  | cons t rest ih =>
    rcases t with ⟨c, m⟩
    have hs : scalePoly k ((c, m) :: rest) = (k * c, m) :: scalePoly k rest := rfl
    rw [hs, evalPoly_cons, evalPoly_cons, ih, Int.cast_mul]
    ring

/-- Pure `List.rec` alternating split (zero `brecOn` overhead in the kernel). -/
def splitPolyGo : Bool → Poly → Poly × Poly
  | _, [] => ([], [])
  | false, x :: rest =>
    let p := splitPolyGo true rest
    (x :: p.1, p.2)
  | true, x :: rest =>
    let p := splitPolyGo false rest
    (p.1, x :: p.2)

def splitPoly (l : Poly) : Poly × Poly :=
  splitPolyGo false l

lemma evalPoly_splitPolyGo (b : Bool) (p : Poly) (a : Fin 15 → ℝ) :
    evalPoly (splitPolyGo b p).1 a + evalPoly (splitPolyGo b p).2 a = evalPoly p a := by
  induction p generalizing b with
  | nil => simp [splitPolyGo]
  | cons x rest ih =>
    rcases x with ⟨c, m⟩
    cases b
    · simp only [splitPolyGo]
      have h := ih true
      rcases hsp : splitPolyGo true rest with ⟨l1, l2⟩
      rw [hsp] at h
      simp only [evalPoly_cons] at h ⊢; linarith
    · simp only [splitPolyGo]
      have h := ih false
      rcases hsp : splitPolyGo false rest with ⟨l1, l2⟩
      rw [hsp] at h
      simp only [evalPoly_cons] at h ⊢; linarith

lemma evalPoly_splitPoly (p : Poly) (a : Fin 15 → ℝ) :
    evalPoly (splitPoly p).1 a + evalPoly (splitPoly p).2 a = evalPoly p a :=
  evalPoly_splitPolyGo false p a

/-- Pure `List.rec` merge helper (zero `WellFounded.fix`, 100% kernel-transparent). -/
def mergeStep (t1 : ℤ × ℕ) (r1 : Poly) (mergeR1 : Poly → Poly) : Poly → Poly
  | [] => t1 :: r1
  | t2 :: r2 =>
    if Nat.ble t1.2 t2.2 then
      t1 :: mergeR1 (t2 :: r2)
    else
      t2 :: mergeStep t1 r1 mergeR1 r2

/-- Merge two polynomials sorted by packed monomial key (pure `List.rec`). -/
def mergePoly : Poly → Poly → Poly
  | [], l2 => l2
  | t1 :: r1, l2 => mergeStep t1 r1 (mergePoly r1) l2

lemma evalPoly_mergeStep (t1 : ℤ × ℕ) (r1 : Poly) (mergeR1 : Poly → Poly) (a : Fin 15 → ℝ)
    (hrec : ∀ l, evalPoly (mergeR1 l) a = evalPoly r1 a + evalPoly l a) (l2 : Poly) :
    evalPoly (mergeStep t1 r1 mergeR1 l2) a = evalPoly (t1 :: r1) a + evalPoly l2 a := by
  induction l2 with
  | nil => simp [mergeStep]
  | cons t2 r2 ih =>
    rcases t1 with ⟨c1, m1⟩
    rcases t2 with ⟨c2, m2⟩
    unfold mergeStep
    split_ifs
    · rw [evalPoly_cons, hrec ((c2, m2) :: r2), evalPoly_cons, evalPoly_cons]
      ring
    · rw [evalPoly_cons, ih, evalPoly_cons, evalPoly_cons]
      ring

lemma evalPoly_mergePoly (l1 l2 : Poly) (a : Fin 15 → ℝ) :
    evalPoly (mergePoly l1 l2) a = evalPoly l1 a + evalPoly l2 a := by
  induction l1 generalizing l2 with
  | nil => simp [mergePoly]
  | cons t1 r1 ih =>
    exact evalPoly_mergeStep t1 r1 (mergePoly r1) a ih l2

/-- Fuel-bounded structural-recursion merge sort (zero well-founded overhead in the kernel). -/
def msortPoly : ℕ → Poly → Poly
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, l =>
    let (l1, l2) := splitPoly l
    mergePoly (msortPoly n l1) (msortPoly n l2)

lemma evalPoly_msortPoly (n : ℕ) (l : Poly) (a : Fin 15 → ℝ) :
    evalPoly (msortPoly n l) a = evalPoly l a := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | [x] => rfl
    | x :: y :: rest =>
      simp only [msortPoly]
      have hsp := evalPoly_splitPoly (x :: y :: rest) a
      rcases h : splitPoly (x :: y :: rest) with ⟨l1, l2⟩
      rw [h] at hsp
      rw [evalPoly_mergePoly, ih l1, ih l2]
      exact hsp

/-- Pure `List.rec` adjacent combiner (drops zero coefficients, zero `brecOn`). -/
def combineAdjGo (c : ℤ) (m : ℕ) : Poly → Poly
  | [] => if c == 0 then [] else [(c, m)]
  | (c', m') :: rest =>
    if Nat.beq m m' then
      combineAdjGo (c + c') m rest
    else if c == 0 then
      combineAdjGo c' m' rest
    else
      (c, m) :: combineAdjGo c' m' rest

def combineAdj : Poly → Poly
  | [] => []
  | (c, m) :: rest => combineAdjGo c m rest

lemma evalPoly_combineAdjGo (c : ℤ) (m : ℕ) (l : Poly) (a : Fin 15 → ℝ) :
    evalPoly (combineAdjGo c m l) a = (c : ℝ) * evalMonom m a + evalPoly l a := by
  induction l generalizing c m with
  | nil =>
    unfold combineAdjGo
    by_cases hc : c == 0
    · have hc0 : c = 0 := beq_iff_eq.mp hc
      simp [hc0]
    · simp [hc]
  | cons t rest ih =>
    rcases t with ⟨c', m'⟩
    unfold combineAdjGo
    by_cases hm : Nat.beq m m' = true
    · have hmeq : m = m' := Nat.eq_of_beq_eq_true hm
      simp only [hm, ite_true]
      rw [ih, evalPoly_cons, Int.cast_add, hmeq]
      ring
    · have hmf : Nat.beq m m' = false := Bool.eq_false_iff.mpr hm
      simp only [hmf, Bool.false_eq_true, ite_false]
      by_cases hc : c == 0
      · have hc0 : c = 0 := beq_iff_eq.mp hc
        simp only [hc, ite_true]
        rw [ih, evalPoly_cons, hc0, Int.cast_zero, zero_mul, zero_add]
      · have hcf : (c == 0) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ite_false, evalPoly_cons, ih]

lemma evalPoly_combineAdj (l : Poly) (a : Fin 15 → ℝ) :
    evalPoly (combineAdj l) a = evalPoly l a := by
  cases l with
  | nil => rfl
  | cons t rest =>
    rcases t with ⟨c, m⟩
    exact evalPoly_combineAdjGo c m rest a

/-- Normalize a sparse polynomial by merge sorting (fuel 14 supports up to `16,384` terms)
    and combining adjacent equal monomials. -/
def normPoly (p : Poly) : Poly :=
  combineAdj (msortPoly 14 p)

lemma evalPoly_normPoly (p : Poly) (a : Fin 15 → ℝ) :
    evalPoly (normPoly p) a = evalPoly p a := by
  rw [normPoly, evalPoly_combineAdj, evalPoly_msortPoly]

/-- Linear-time addition of two already-sorted polynomials. -/
def addNormPoly (p q : Poly) : Poly :=
  combineAdj (mergePoly p q)

lemma evalPoly_addNormPoly (p q : Poly) (a : Fin 15 → ℝ) :
    evalPoly (addNormPoly p q) a = evalPoly p a + evalPoly q a := by
  rw [addNormPoly, evalPoly_combineAdj, evalPoly_mergePoly]

/-- Check that every exponent of every monomial in `p` is at most `B`. -/
def monomDigitsLe (m B : ℕ) : Bool :=
  (monomDigit m 0 ≤ B) && (monomDigit m 1 ≤ B) && (monomDigit m 2 ≤ B) &&
  (monomDigit m 3 ≤ B) && (monomDigit m 4 ≤ B) && (monomDigit m 5 ≤ B) &&
  (monomDigit m 6 ≤ B) && (monomDigit m 7 ≤ B) && (monomDigit m 8 ≤ B) &&
  (monomDigit m 9 ≤ B) && (monomDigit m 10 ≤ B) && (monomDigit m 11 ≤ B) &&
  (monomDigit m 12 ≤ B) && (monomDigit m 13 ≤ B) && (monomDigit m 14 ≤ B)

lemma monomDigitsLe_spec {m B : ℕ} (h : monomDigitsLe m B = true) (e : Fin 15) :
    monomDigit m e ≤ B := by
  unfold monomDigitsLe at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  fin_cases e <;> tauto

def polyDigitsLe (p : Poly) (B : ℕ) : Bool :=
  p.all fun t => monomDigitsLe t.2 B

lemma polyDigitsLe_spec {p : Poly} {B : ℕ} (h : polyDigitsLe p B = true)
    {c : ℤ} {m : ℕ} (hm : (c, m) ∈ p) (e : Fin 15) :
    monomDigit m e ≤ B := by
  unfold polyDigitsLe at h
  rw [List.all_eq_true] at h
  exact monomDigitsLe_spec (h (c, m) hm) e

/-- Raw Cartesian product of two sparse polynomials (valid when exponents stay `< 16`). -/
def mulPolyRaw (p q : Poly) : Poly :=
  p.flatMap fun t1 => q.map fun t2 => (t1.1 * t2.1, t1.2 + t2.2)

lemma evalPoly_mulPolyRaw {p q : Poly} {B1 B2 : ℕ} (hB : B1 + B2 < 16)
    (hp : polyDigitsLe p B1 = true) (hq : polyDigitsLe q B2 = true) (a : Fin 15 → ℝ) :
    evalPoly (mulPolyRaw p q) a = evalPoly p a * evalPoly q a := by
  induction p with
  | nil => simp [mulPolyRaw]
  | cons t1 r1 ih =>
    rcases t1 with ⟨c1, m1⟩
    have hp_and : monomDigitsLe m1 B1 = true ∧ polyDigitsLe r1 B1 = true := by
      simpa only [polyDigitsLe, List.all_cons, Bool.and_eq_true] using hp
    have hp1 := hp_and.1
    have hpr := hp_and.2
    have hcons : mulPolyRaw ((c1, m1) :: r1) q =
        (q.map fun t2 => (c1 * t2.1, m1 + t2.2)) ++ mulPolyRaw r1 q := rfl
    rw [hcons, evalPoly_append, evalPoly_cons, ih hpr]
    have hrow : evalPoly (q.map fun t2 => (c1 * t2.1, m1 + t2.2)) a =
        ((c1 : ℝ) * evalMonom m1 a) * evalPoly q a := by
      clear ih hpr hp hp_and hcons
      induction q with
      | nil => simp
      | cons t2 r2 ihq =>
        rcases t2 with ⟨c2, m2⟩
        have hq_and : monomDigitsLe m2 B2 = true ∧ polyDigitsLe r2 B2 = true := by
          simpa only [polyDigitsLe, List.all_cons, Bool.and_eq_true] using hq
        have hq1 := hq_and.1
        have hqr := hq_and.2
        simp only [List.map_cons, evalPoly_cons, Int.cast_mul]
        rw [ihq hqr]
        have hnc : ∀ e : Fin 15, monomDigit m1 e + monomDigit m2 e < 16 := fun e => by
          have h1 := monomDigitsLe_spec hp1 e
          have h2 := monomDigitsLe_spec hq1 e
          omega
        rw [evalMonom_add m1 m2 a hnc]
        ring
    rw [hrow]; ring

/-- Normalized product of two sparse polynomials. -/
def mulPoly (p q : Poly) : Poly :=
  normPoly (mulPolyRaw p q)

lemma evalPoly_mulPoly {p q : Poly} {B1 B2 : ℕ} (hB : B1 + B2 < 16)
    (hp : polyDigitsLe p B1 = true) (hq : polyDigitsLe q B2 = true) (a : Fin 15 → ℝ) :
    evalPoly (mulPoly p q) a = evalPoly p a * evalPoly q a := by
  rw [mulPoly, evalPoly_normPoly, evalPoly_mulPolyRaw hB hp hq]

/-! ### Computable `B₆⁺` Witnesses & Action on Monomials -/

/-- Fast computable parity of a permutation `f : Fin 6 → Fin 6` (inversion count mod 2). -/
def permParity (f : Fin 6 → Fin 6) : Bool :=
  xor (decide (f 1 < f 0)) <|
  xor (decide (f 2 < f 0)) <|
  xor (decide (f 3 < f 0)) <|
  xor (decide (f 4 < f 0)) <|
  xor (decide (f 5 < f 0)) <|
  xor (decide (f 2 < f 1)) <|
  xor (decide (f 3 < f 1)) <|
  xor (decide (f 4 < f 1)) <|
  xor (decide (f 5 < f 1)) <|
  xor (decide (f 3 < f 2)) <|
  xor (decide (f 4 < f 2)) <|
  xor (decide (f 5 < f 2)) <|
  xor (decide (f 4 < f 3)) <|
  xor (decide (f 5 < f 3)) <|
      (decide (f 5 < f 4))

/-- Fast computable parity of a sign vector `s : Fin 6 → Bool`. -/
def sgnParity (s : Fin 6 → Bool) : Bool :=
  xor (s 0) (xor (s 1) (xor (s 2) (xor (s 3) (xor (s 4) (s 5)))))

lemma sgnInt_sgnParity (s : Fin 6 → Bool) :
    (∏ i : Fin 6, sgnInt (s i)) = sgnInt (sgnParity s) := by
  rw [Fin.prod_univ_six, sgnParity]
  simp only [sgnInt_xor]
  ring

lemma sign_eq_signAux (p : Equiv.Perm (Fin 6)) :
    Equiv.Perm.sign p = Equiv.Perm.signAux p := by
  induction p using Equiv.Perm.swap_induction_on with
  | one =>
    simp [Equiv.Perm.signAux_one]
  | swap_mul f x y hxy ih =>
    rw [map_mul, Equiv.Perm.signAux_mul, Equiv.Perm.sign_swap hxy, Equiv.Perm.signAux_swap hxy, ih]

lemma finPairsLT_six_eq :
    Equiv.Perm.finPairsLT 6 =
      ({⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨5, 0⟩,
        ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩,
        ⟨3, 2⟩, ⟨4, 2⟩, ⟨5, 2⟩,
        ⟨4, 3⟩, ⟨5, 3⟩,
        ⟨5, 4⟩} : Finset (Σ _ : Fin 6, Fin 6)) := by
  decide

lemma sign_eq_sgnInt_permParity (p : Equiv.Perm (Fin 6)) :
    (Equiv.Perm.sign p : ℤ) = sgnInt (permParity p) := by
  rw [sign_eq_signAux, Equiv.Perm.signAux, finPairsLT_six_eq]
  have hconv : ∀ i j : Fin 6, i ≠ j →
      (((if p i ≤ p j then (-1 : ℤˣ) else 1) : ℤˣ) : ℤ) = sgnInt (decide (p i < p j)) := by
    intro i j hij
    have hp : p i ≠ p j := fun h => hij (p.injective h)
    by_cases hlt : p i < p j
    · have hle : p i ≤ p j := le_of_lt hlt
      simp [hle, hlt, sgnInt]
    · have hnotle : ¬ p i ≤ p j := fun h => hlt (lt_of_le_of_ne h hp)
      simp [hnotle, hlt, sgnInt]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  simp only [Units.val_mul, permParity, sgnInt_xor]
  rw [hconv 1 0 (by decide), hconv 2 0 (by decide), hconv 3 0 (by decide),
      hconv 4 0 (by decide), hconv 5 0 (by decide), hconv 2 1 (by decide),
      hconv 3 1 (by decide), hconv 4 1 (by decide), hconv 5 1 (by decide),
      hconv 3 2 (by decide), hconv 4 2 (by decide), hconv 5 2 (by decide),
      hconv 4 3 (by decide), hconv 5 3 (by decide), hconv 5 4 (by decide)]

/-- Compact computable witness encoding an element `(p, s) ∈ B₆⁺`. -/
structure B6Wit where
  p0 : Fin 6
  p1 : Fin 6
  p2 : Fin 6
  p3 : Fin 6
  p4 : Fin 6
  p5 : Fin 6
  s0 : Bool
  s1 : Bool
  s2 : Bool
  s3 : Bool
  s4 : Bool
  s5 : Bool
  deriving DecidableEq

def B6Wit.pFun (w : B6Wit) : Fin 6 → Fin 6
  | 0 => w.p0 | 1 => w.p1 | 2 => w.p2 | 3 => w.p3 | 4 => w.p4 | 5 => w.p5

def B6Wit.pInv (w : B6Wit) (y : Fin 6) : Fin 6 :=
  if w.p0 == y then 0
  else if w.p1 == y then 1
  else if w.p2 == y then 2
  else if w.p3 == y then 3
  else if w.p4 == y then 4
  else 5

def B6Wit.sFun (w : B6Wit) : Fin 6 → Bool
  | 0 => w.s0 | 1 => w.s1 | 2 => w.s2 | 3 => w.s3 | 4 => w.s4 | 5 => w.s5

/-- Fast kernel checker verifying that `w : B6Wit` defines a valid element of `B₆⁺`. -/
def isValidB6Wit (w : B6Wit) : Bool :=
  (w.pInv (w.pFun 0) == 0) && (w.pInv (w.pFun 1) == 1) && (w.pInv (w.pFun 2) == 2) &&
  (w.pInv (w.pFun 3) == 3) && (w.pInv (w.pFun 4) == 4) && (w.pInv (w.pFun 5) == 5) &&
  (w.pFun (w.pInv 0) == 0) && (w.pFun (w.pInv 1) == 1) && (w.pFun (w.pInv 2) == 2) &&
  (w.pFun (w.pInv 3) == 3) && (w.pFun (w.pInv 4) == 4) && (w.pFun (w.pInv 5) == 5) &&
  (permParity w.pFun == sgnParity w.sFun)

/-- Lift a validated `B6Wit` to an actual element of the group `B6Plus`. -/
def B6Wit.toB6Plus (w : B6Wit) (hw : isValidB6Wit w = true) : B6Plus :=
  let h : (∀ i : Fin 6, w.pInv (w.pFun i) = i) ∧
          (∀ i : Fin 6, w.pFun (w.pInv i) = i) ∧
          (permParity w.pFun = sgnParity w.sFun) := by
    unfold isValidB6Wit at hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    refine ⟨?_, ?_, hw.2⟩
    · intro i; fin_cases i <;> tauto
    · intro i; fin_cases i <;> tauto
  let perm : Equiv.Perm (Fin 6) :=
    { toFun := w.pFun, invFun := w.pInv, left_inv := h.1, right_inv := h.2.1 }
  { perm := perm
    sgn := w.sFun
    det_one := by
      rw [sign_eq_sgnInt_permParity, sgnInt_sgnParity]
      change sgnInt (permParity w.pFun) * sgnInt (sgnParity w.sFun) = 1
      rw [h.2.2]
      cases sgnParity w.sFun <;> rfl }

/-- Single-edge update step for computing the action of `w : B6Wit` on a packed monomial `m`. -/
def edgeActStep (w : B6Wit) (m : ℕ) (e : Fin 15) (acc : ℤ × ℕ) : ℤ × ℕ :=
  let d := monomDigit m e
  if d == 0 then acc
  else
    let uv := edgePairs e
    let lu := edgeLookup (w.pFun uv.1) (w.pFun uv.2)
    let esgn : ℤ := sgnInt (w.sFun uv.1) * sgnInt (w.sFun uv.2) * lu.2
    let s' := if esgn < 0 && d % 2 == 1 then -acc.1 else acc.1
    (s', acc.2 + d * 16 ^ lu.1.val)

/-- Computable action of `w : B6Wit` on a base-16 packed monomial `m`, returning `(sign, m')`. -/
def actMonomWit (w : B6Wit) (m : ℕ) : ℤ × ℕ :=
  (List.finRange 15).foldl (fun acc e => edgeActStep w m e acc) (1, 0)

lemma neg_one_or_one_pow (x : ℤ) (hx : x = 1 ∨ x = -1) (d : ℕ) :
    (if x < 0 && d % 2 == 1 then (-1 : ℤ) else 1) = x ^ d := by
  rcases hx with rfl | rfl
  · simp
  · by_cases hodd : d % 2 = 1
    · simp only [show (-1 : ℤ) < 0 by omega, decide_true, hodd, beq_self_eq_true,
        Bool.and_self, ite_true]
      have hd : Odd d := Nat.odd_iff.mpr hodd
      exact (hd.neg_one_pow).symm
    · have heven : Even d := Nat.even_iff.mpr (by omega)
      have hbeq : (d % 2 == 1) = false := by simp [hodd]
      simp only [hbeq, Bool.and_false, Bool.false_eq_true, ite_false]
      exact (heven.neg_one_pow).symm

lemma edgeActStep_eq (w : B6Wit) (hw : isValidB6Wit w = true) (m : ℕ) (e : Fin 15) (acc : ℤ × ℕ) :
    let g := w.toB6Plus hw
    edgeActStep w m e acc =
      (acc.1 * (edgeSgnFun g e) ^ (monomDigit m e),
       acc.2 + monomDigit m e * 16 ^ (edgeImgFun g e).val) := by
  intro g
  have hesgn : edgeSgnFun g e = 1 ∨ edgeSgnFun g e = -1 := by
    have hsq : (edgeSgnFun g e : ℝ) ^ 2 = 1 := edgeSgnFun_sq g e
    have hsqZ : (edgeSgnFun g e) ^ 2 = 1 := by exact_mod_cast hsq
    have : (edgeSgnFun g e - 1) * (edgeSgnFun g e + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> omega
  have hg_p : ∀ i : Fin 6, g.perm i = w.pFun i := fun _ => rfl
  have hg_s : ∀ i : Fin 6, g.sgn i = w.sFun i := fun _ => rfl
  unfold edgeActStep
  dsimp only
  by_cases hd0 : monomDigit m e == 0
  · have h0 : monomDigit m e = 0 := beq_iff_eq.mp hd0
    simp [h0]
  · have hd0f : (monomDigit m e == 0) = false := Bool.eq_false_iff.mpr hd0
    simp only [hd0f, Bool.false_eq_true, ite_false]
    have hpow := neg_one_or_one_pow (edgeSgnFun g e) hesgn (monomDigit m e)
    have he1 : sgnInt (w.sFun (edgePairs e).1) * sgnInt (w.sFun (edgePairs e).2) *
        (edgeLookup (w.pFun (edgePairs e).1) (w.pFun (edgePairs e).2)).2 = edgeSgnFun g e := rfl
    have he2 : (edgeLookup (w.pFun (edgePairs e).1) (w.pFun (edgePairs e).2)).1 = edgeImgFun g e := rfl
    rw [he1, he2]
    ext
    · dsimp only
      by_cases hc : (decide (edgeSgnFun g e < 0) && monomDigit m e % 2 == 1) = true
      · simp only [hc, ite_true] at hpow ⊢
        rw [← hpow]; ring
      · have hcf : (decide (edgeSgnFun g e < 0) && monomDigit m e % 2 == 1) = false :=
          Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ite_false] at hpow ⊢
        rw [← hpow]; ring
    · rfl

lemma foldl_pair_prod_sum {α : Type*} (l : List α) (f : α → ℤ) (h : α → ℕ) (acc : ℤ × ℕ) :
    l.foldl (fun a x => (a.1 * f x, a.2 + h x)) acc =
      (acc.1 * (l.map f).prod, acc.2 + (l.map h).sum) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih]
    ext <;> dsimp only <;> ring

lemma actMonomWit_spec (w : B6Wit) (hw : isValidB6Wit w = true) (m : ℕ) :
    let g := w.toB6Plus hw
    actMonomWit w m =
      (∏ e : Fin 15, (edgeSgnFun g e) ^ (monomDigit m e),
       ∑ e : Fin 15, monomDigit m e * 16 ^ (edgeImgFun g e).val) := by
  intro g
  unfold actMonomWit
  have hstep : ∀ acc e, edgeActStep w m e acc =
      (acc.1 * (edgeSgnFun g e) ^ (monomDigit m e),
       acc.2 + monomDigit m e * 16 ^ (edgeImgFun g e).val) :=
    fun acc e => edgeActStep_eq w hw m e acc
  simp_rw [hstep]
  rw [foldl_pair_prod_sum]
  ext
  · simp [Fin.prod_univ_def]
  · simp [Fin.sum_univ_def]

lemma evalMonom_actB6_of_wit (w : B6Wit) (hw : isValidB6Wit w = true) (m : ℕ) (a : Fin 15 → ℝ) :
    evalMonom m (actB6Vec (w.toB6Plus hw) a) =
      ((actMonomWit w m).1 : ℝ) * evalMonom (actMonomWit w m).2 a := by
  set g := w.toB6Plus hw
  have hspec := actMonomWit_spec w hw m
  dsimp only at hspec
  rw [hspec]
  dsimp only
  set σ := edgeEquiv g
  have hpack :
      ∑ e : Fin 15, monomDigit m e * 16 ^ (edgeImgFun g e).val =
      ∑ e' : Fin 15, monomDigit m (σ.symm e') * 16 ^ e'.val := by
    refine Fintype.sum_equiv σ _ _ fun e => ?_
    have hσ : σ e = edgeImgFun g e := rfl
    rw [Equiv.symm_apply_apply, hσ]
  have hdig : ∀ e' : Fin 15,
      monomDigit (∑ e : Fin 15, monomDigit m e * 16 ^ (edgeImgFun g e).val) e' =
        monomDigit m (σ.symm e') := by
    intro e'
    rw [hpack]
    exact monomDigit_pack (fun x => monomDigit m (σ.symm x))
      (fun x => Nat.mod_lt _ (by decide)) e'
  unfold evalMonom
  change ∏ e : Fin 15, (actB6Vec g a e) ^ monomDigit m e =
    ((∏ e : Fin 15, edgeSgnFun g e ^ monomDigit m e : ℤ) : ℝ) *
    ∏ e' : Fin 15, a e' ^ monomDigit (∑ e : Fin 15, monomDigit m e * 16 ^ (edgeImgFun g e).val) e'
  simp_rw [hdig]
  have hprod_equiv :
      ∏ e' : Fin 15, (a e') ^ (monomDigit m (σ.symm e')) =
      ∏ e : Fin 15, (a (edgeImgFun g e)) ^ (monomDigit m e) := by
    refine (Fintype.prod_equiv σ _ _ fun e => ?_).symm
    have hσ : σ e = edgeImgFun g e := rfl
    rw [Equiv.symm_apply_apply, hσ]
  rw [hprod_equiv, Int.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [actB6Vec_apply, mul_pow, Int.cast_pow]

/-! ### Orbit-Cancellation Certificate Verifier -/

/-- Witness for a single monomial `m` in `F_int`:
    - `zero w`: `w ∈ B₆⁺` sends `m ↦ -m`, so its `B₆⁺`-sum vanishes individually.
    - `canon w sgn cm`: `w ∈ B₆⁺` sends `m ↦ sgn * cm`, transferring its weight to canonical `cm`. -/
inductive OrbitWit
  | zero (w : B6Wit)
  | canon (w : B6Wit) (sgn : ℤ) (cm : ℕ)
  deriving DecidableEq

/-- Check validity of a single `(coeff, monom, witness)` entry. -/
def checkWitEntry (entry : ℤ × ℕ × OrbitWit) : Bool :=
  match entry.2.2 with
  | .zero w => isValidB6Wit w && (actMonomWit w entry.2.1 == (-1, entry.2.1))
  | .canon w sgn cm => isValidB6Wit w && (actMonomWit w entry.2.1 == (sgn, cm))

/-- Accumulate canonical orbit weights from all `.canon` entries. -/
def canonAccumPoly (entries : List (ℤ × ℕ × OrbitWit)) : Poly :=
  entries.filterMap fun e =>
    match e.2.2 with
    | .zero _ => none
    | .canon _ sgn cm => some (sgn * e.1, cm)

/-- Extract the underlying sparse polynomial from a witnessed list. -/
def entriesToPoly (entries : List (ℤ × ℕ × OrbitWit)) : Poly :=
  entries.map fun e => (e.1, e.2.1)

/-- Pure-kernel master verifier: checks all `B₆⁺` witnesses AND verifies that all
    canonical orbit sums cancel to `0`. -/
def verifyOrbitCancel (entries : List (ℤ × ℕ × OrbitWit)) : Bool :=
  entries.all checkWitEntry && (normPoly (canonAccumPoly entries) == [])

/-- Master Orbit-Cancellation Theorem:
    If `verifyOrbitCancel entries = true`, then the `B₆⁺`-symmetrization of `entriesToPoly entries`
    is identically `0` on all of `ℝ¹⁵`! -/
theorem sum_B6Plus_evalPoly_eq_zero_of_verify (entries : List (ℤ × ℕ × OrbitWit))
    (hver : verifyOrbitCancel entries = true) (a : Fin 15 → ℝ) :
    ∑ h : B6Plus, evalPoly (entriesToPoly entries) (actB6Vec h a) = 0 := by
  unfold verifyOrbitCancel at hver
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hver
  rcases hver with ⟨hall, hcanon_zero⟩
  -- Step 1: Prove the sum over `B6Plus` equals the sum over `B6Plus` of `canonAccumPoly entries`
  have htransfer :
      ∀ es : List (ℤ × ℕ × OrbitWit),
        (∀ e ∈ es, checkWitEntry e = true) →
        ∑ h : B6Plus, evalPoly (entriesToPoly es) (actB6Vec h a) =
        ∑ h : B6Plus, evalPoly (canonAccumPoly es) (actB6Vec h a) := by
    intro es hes
    induction es with
    | nil => simp [entriesToPoly, canonAccumPoly]
    | cons entry rest ih =>
      rcases entry with ⟨c, m, wit⟩
      have hentry : checkWitEntry (c, m, wit) = true := hes _ (List.mem_cons_self ..)
      have hrest : ∀ e ∈ rest, checkWitEntry e = true :=
        fun e he => hes e (List.mem_cons_of_mem _ he)
      have hcons : entriesToPoly ((c, m, wit) :: rest) = (c, m) :: entriesToPoly rest := rfl
      rw [hcons]
      simp only [evalPoly_cons, Finset.sum_add_distrib]
      rw [ih hrest]
      cases wit with
      | zero w =>
        simp only [checkWitEntry, Bool.and_eq_true, beq_iff_eq] at hentry
        rcases hentry with ⟨hw, hact⟩
        set g := w.toB6Plus hw
        have hzero : ∑ h : B6Plus, (c : ℝ) * evalMonom m (actB6Vec h a) = 0 := by
          have hself : ∑ h : B6Plus, (c : ℝ) * evalMonom m (actB6Vec h a) =
              -(∑ h : B6Plus, (c : ℝ) * evalMonom m (actB6Vec h a)) := by
            rw [← Finset.sum_neg_distrib]
            refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
            change -((c : ℝ) * evalMonom m (actB6Vec h a)) =
                   (c : ℝ) * evalMonom m (actB6Vec (g * h) a)
            rw [actB6Vec_mul, evalMonom_actB6_of_wit w hw m, hact]
            simp
          linarith
        simp only [canonAccumPoly, List.filterMap_cons, hzero, zero_add]
      | canon w sgn cm =>
        simp only [checkWitEntry, Bool.and_eq_true, beq_iff_eq] at hentry
        rcases hentry with ⟨hw, hact⟩
        set g := w.toB6Plus hw
        have hshift : ∑ h : B6Plus, (c : ℝ) * evalMonom m (actB6Vec h a) =
            ∑ h : B6Plus, ((sgn * c : ℤ) : ℝ) * evalMonom cm (actB6Vec h a) := by
          refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
          change ((sgn * c : ℤ) : ℝ) * evalMonom cm (actB6Vec h a) =
                 (c : ℝ) * evalMonom m (actB6Vec (g * h) a)
          rw [actB6Vec_mul, evalMonom_actB6_of_wit w hw m, hact]
          simp [Int.cast_mul]; ring
        simp only [canonAccumPoly, List.filterMap_cons, evalPoly_cons, Finset.sum_add_distrib,
          hshift]
  rw [htransfer entries hall]
  refine Finset.sum_eq_zero fun h _ => ?_
  rw [← evalPoly_normPoly, hcanon_zero, evalPoly_nil]

end TwoQubitMaximalMagic
