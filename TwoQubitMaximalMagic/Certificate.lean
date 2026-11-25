import TwoQubitMaximalMagic.CertificateData
import Mathlib.Tactic

/-!
# Pure-Kernel SOS Certificate Verification & `SO(6)` Fourth-Power Lower Bound

This file proves, entirely within Lean 4's kernel (zero `sorry`, zero `native_decide`),
that for every `a : Fin 15 → ℝ` satisfying `IsSkewOrth6 a`:
1. `so6_fourth_power_bound`: `3 / 4 ≤ ∑ e : Fin 15, (a e) ^ 4`.
2. `so6_equality_iff_spectrum`: equality holds iff `∀ e : Fin 15, |a e| = 0 ∨ |a e| = 1 / 2`,
   in which case exactly 3 edges vanish (forming a perfect matching of `K₆`, i.e., one
   vanishing edge incident to every vertex) and 12 edges satisfy `|a e| = 1 / 2`.
-/

namespace TwoQubitMaximalMagic

/-- Clean finite-product expansion over `Fin 15`. -/
lemma prod_fin15 {M : Type*} [CommMonoid M] (f : Fin 15 → M) :
    ∏ e : Fin 15, f e =
      f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 *
      f 8 * f 9 * f 10 * f 11 * f 12 * f 13 * f 14 := by
  have h : (Finset.univ : Finset (Fin 15)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  rw [h]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  ac_rfl

/-! ### Pure-Kernel Polynomial Checks (Zero `native_decide`) -/

set_option maxRecDepth 20000 in
private lemma digits_Q1 : polyDigitsLe polyQ1 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q2 : polyDigitsLe polyQ2 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q3 : polyDigitsLe polyQ3 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q4 : polyDigitsLe polyQ4 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q5 : polyDigitsLe polyQ5 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q6 : polyDigitsLe polyQ6 4 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_Q7 : polyDigitsLe polyQ7 4 = true := rfl

set_option maxRecDepth 20000 in
private lemma digits_U0  : polyDigitsLe polyU0  6 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_U01 : polyDigitsLe polyU01 6 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_V01 : polyDigitsLe polyV01 6 = true := rfl

set_option maxRecDepth 20000 in
private lemma digits_H0  : polyDigitsLe polyH0  2 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_H01 : polyDigitsLe polyH01 2 = true := rfl
set_option maxRecDepth 20000 in
private lemma digits_G01 : polyDigitsLe polyG01 2 = true := rfl

set_option maxRecDepth 50000 in
private lemma mul_Q1_eq : mulPoly polyQ1 polyQ1 = polyQ1Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q2_eq : mulPoly polyQ2 polyQ2 = polyQ2Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q3_eq : mulPoly polyQ3 polyQ3 = polyQ3Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q4_eq : mulPoly polyQ4 polyQ4 = polyQ4Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q5_eq : mulPoly polyQ5 polyQ5 = polyQ5Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q6_eq : mulPoly polyQ6 polyQ6 = polyQ6Sq := rfl
set_option maxRecDepth 50000 in
private lemma mul_Q7_eq : mulPoly polyQ7 polyQ7 = polyQ7Sq := rfl

set_option maxRecDepth 50000 in
private lemma mul_U0H0_eq   : mulPoly polyU0  polyH0  = polyU0H0   := rfl
set_option maxRecDepth 50000 in
private lemma mul_U01H01_eq : mulPoly polyU01 polyH01 = polyU01H01 := rfl
set_option maxRecDepth 50000 in
private lemma mul_V01G01_eq : mulPoly polyV01 polyG01 = polyV01G01 := rfl

/-- Linear-time assembly of the un-symmetrized degree-8 remainder `F_int`. -/
def assembledF : Poly :=
  let p0 : Poly := [(-(3 * certD / 4), 0), (15 * certD, 4)]
  let p1 := addNormPoly p0 (scalePoly (-certC1) polyQ1Sq)
  let p2 := addNormPoly p1 (scalePoly (-certC2) polyQ2Sq)
  let p3 := addNormPoly p2 (scalePoly (-certC3) polyQ3Sq)
  let p4 := addNormPoly p3 (scalePoly (-certC4) polyQ4Sq)
  let p5 := addNormPoly p4 (scalePoly (-certC5) polyQ5Sq)
  let p6 := addNormPoly p5 (scalePoly (-certC6) polyQ6Sq)
  let p7 := addNormPoly p6 (scalePoly (-certC7) polyQ7Sq)
  let p8 := addNormPoly p7 (scalePoly (-1) polyU0H0)
  let p9 := addNormPoly p8 (scalePoly (-1) polyU01H01)
  addNormPoly p9 (scalePoly (-1) polyV01G01)

set_option maxRecDepth 100000 in
private lemma assembledF_eq : assembledF = entriesToPoly certEntries := rfl

set_option maxRecDepth 50000 in
private lemma chunk1_ok  : certEntries1.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk2_ok  : certEntries2.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk3_ok  : certEntries3.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk4_ok  : certEntries4.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk5_ok  : certEntries5.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk6_ok  : certEntries6.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk7_ok  : certEntries7.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk8_ok  : certEntries8.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk9_ok  : certEntries9.all  checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk10_ok : certEntries10.all checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk11_ok : certEntries11.all checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk12_ok : certEntries12.all checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk13_ok : certEntries13.all checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk14_ok : certEntries14.all checkWitEntry = true := rfl
set_option maxRecDepth 50000 in
private lemma chunk15_ok : certEntries15.all checkWitEntry = true := rfl

set_option maxRecDepth 100000 in
private lemma canon_cancel_ok : normPoly (canonAccumPoly certEntries) = [] := rfl

lemma certEntries_verified : verifyOrbitCancel certEntries = true := by
  unfold verifyOrbitCancel
  rw [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, canon_cancel_ok⟩
  simp only [certEntries, List.all_append, Bool.and_eq_true,
    chunk1_ok, chunk2_ok, chunk3_ok, chunk4_ok, chunk5_ok,
    chunk6_ok, chunk7_ok, chunk8_ok, chunk9_ok, chunk10_ok,
    chunk11_ok, chunk12_ok, chunk13_ok, chunk14_ok, chunk15_ok, and_self]

/-! ### Evaluating `polyH0`, `polyH01`, `polyG01`, `polyQ1`, and `assembledF` -/

private lemma evalMonom_pow0 (a : Fin 15 → ℝ) : evalMonom 0 a = 1 := evalMonom_zero a

private lemma evalMonom_a0_1 (a : Fin 15 → ℝ) : evalMonom 1 a = a 0 := by
  unfold evalMonom; rw [prod_fin15]; simp [monomDigit]

private lemma evalMonom_a0_3 (a : Fin 15 → ℝ) : evalMonom 3 a = a 0 ^ 3 := by
  unfold evalMonom; rw [prod_fin15]; simp [monomDigit]

private lemma evalMonom_a0_4 (a : Fin 15 → ℝ) : evalMonom 4 a = a 0 ^ 4 := by
  unfold evalMonom; rw [prod_fin15]; simp [monomDigit]

lemma evalPoly_polyQ1 (a : Fin 15 → ℝ) :
    evalPoly polyQ1 a = 4 * a 0 ^ 3 - a 0 := by
  simp only [polyQ1, evalPoly_cons, evalPoly_nil, evalMonom_a0_1, evalMonom_a0_3]
  norm_num; ring

lemma evalPoly_polyH0 (a : Fin 15 → ℝ) :
    evalPoly polyH0 a = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 - 1 := by
  simp only [polyH0, evalPoly_cons, evalPoly_nil]
  unfold evalMonom
  simp only [prod_fin15, monomDigit]
  norm_num; ring

lemma evalPoly_polyH01 (a : Fin 15 → ℝ) :
    evalPoly polyH01 a = a 1 * a 5 + a 2 * a 6 + a 3 * a 7 + a 4 * a 8 := by
  simp only [polyH01, evalPoly_cons, evalPoly_nil]
  unfold evalMonom
  simp only [prod_fin15, monomDigit]
  norm_num; ring

lemma evalPoly_polyG01 (a : Fin 15 → ℝ) :
    evalPoly polyG01 a = a 0 - a 9 * a 14 + a 10 * a 13 - a 11 * a 12 := by
  simp only [polyG01, evalPoly_cons, evalPoly_nil]
  unfold evalMonom
  simp only [prod_fin15, monomDigit]
  norm_num; ring

lemma evalPoly_entriesToPoly_eq {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    evalPoly (entriesToPoly certEntries) a =
      (certD : ℝ) * (15 * (a 0) ^ 4 - 3 / 4) -
      ((certC1 : ℝ) * (4 * (a 0) ^ 3 - a 0) ^ 2 +
       (certC2 : ℝ) * (evalPoly polyQ2 a) ^ 2 +
       (certC3 : ℝ) * (evalPoly polyQ3 a) ^ 2 +
       (certC4 : ℝ) * (evalPoly polyQ4 a) ^ 2 +
       (certC5 : ℝ) * (evalPoly polyQ5 a) ^ 2 +
       (certC6 : ℝ) * (evalPoly polyQ6 a) ^ 2 +
       (certC7 : ℝ) * (evalPoly polyQ7 a) ^ 2) := by
  rw [← assembledF_eq]
  unfold assembledF
  simp only [evalPoly_addNormPoly, evalPoly_scalePoly, evalPoly_cons, evalPoly_nil,
    evalMonom_pow0, evalMonom_a0_4]
  rw [← mul_Q1_eq, ← mul_Q2_eq, ← mul_Q3_eq, ← mul_Q4_eq, ← mul_Q5_eq, ← mul_Q6_eq, ← mul_Q7_eq,
      ← mul_U0H0_eq, ← mul_U01H01_eq, ← mul_V01G01_eq]
  rw [evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q1 digits_Q1,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q2 digits_Q2,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q3 digits_Q3,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q4 digits_Q4,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q5 digits_Q5,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q6 digits_Q6,
      evalPoly_mulPoly (by decide : 4 + 4 < 16) digits_Q7 digits_Q7,
      evalPoly_mulPoly (by decide : 6 + 2 < 16) digits_U0 digits_H0,
      evalPoly_mulPoly (by decide : 6 + 2 < 16) digits_U01 digits_H01,
      evalPoly_mulPoly (by decide : 6 + 2 < 16) digits_V01 digits_G01]
  rw [evalPoly_polyH0, h0_eq_zero ha,
      evalPoly_polyH01, h01_eq_zero ha,
      evalPoly_polyG01, g01_eq_zero ha,
      evalPoly_polyQ1]
  have hDdiv : ((-(3 * certD / 4) : ℤ) : ℝ) = -(3 / 4 : ℝ) * (certD : ℝ) := by
    norm_num [certD]
  rw [hDdiv]
  push_cast
  ring

/-! ### The Master Exact SOS Identity & Fourth-Power Bound on `SO(6)` -/

/-- The 7-square SOS summand evaluated at `h · a`. -/
def sosTerm (a : Fin 15 → ℝ) (h : B6Plus) : ℝ :=
  (certC1 : ℝ) * (4 * (actB6Vec h a 0) ^ 3 - actB6Vec h a 0) ^ 2 +
  (certC2 : ℝ) * (evalPoly polyQ2 (actB6Vec h a)) ^ 2 +
  (certC3 : ℝ) * (evalPoly polyQ3 (actB6Vec h a)) ^ 2 +
  (certC4 : ℝ) * (evalPoly polyQ4 (actB6Vec h a)) ^ 2 +
  (certC5 : ℝ) * (evalPoly polyQ5 (actB6Vec h a)) ^ 2 +
  (certC6 : ℝ) * (evalPoly polyQ6 (actB6Vec h a)) ^ 2 +
  (certC7 : ℝ) * (evalPoly polyQ7 (actB6Vec h a)) ^ 2

theorem so6_sos_identity {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    (certD : ℝ) * (Fintype.card B6Plus : ℝ) * ((∑ e : Fin 15, (a e) ^ 4) - 3 / 4) =
      ∑ h : B6Plus, sosTerm a h := by
  have hzero := sum_B6Plus_evalPoly_eq_zero_of_verify certEntries certEntries_verified a
  have hterm : ∀ h : B6Plus,
      evalPoly (entriesToPoly certEntries) (actB6Vec h a) =
        (certD : ℝ) * (15 * (actB6Vec h a 0) ^ 4 - 3 / 4) - sosTerm a h :=
    fun h => evalPoly_entriesToPoly_eq (isSkewOrth6_actB6 h ha)
  simp_rw [hterm] at hzero
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_B6Plus_a0_pow4] at hzero
  linarith

private lemma certD_pos : (0 : ℝ) < (certD : ℝ) := by norm_num [certD]
private lemma certC1_pos : (0 : ℝ) < (certC1 : ℝ) := by norm_num [certC1]
private lemma certC2_pos : (0 : ℝ) < (certC2 : ℝ) := by norm_num [certC2]
private lemma certC3_pos : (0 : ℝ) < (certC3 : ℝ) := by norm_num [certC3]
private lemma certC4_pos : (0 : ℝ) < (certC4 : ℝ) := by norm_num [certC4]
private lemma certC5_pos : (0 : ℝ) < (certC5 : ℝ) := by norm_num [certC5]
private lemma certC6_pos : (0 : ℝ) < (certC6 : ℝ) := by norm_num [certC6]
private lemma certC7_pos : (0 : ℝ) < (certC7 : ℝ) := by norm_num [certC7]

private lemma sos_term_nonneg (a : Fin 15 → ℝ) (h : B6Plus) :
    0 ≤ sosTerm a h := by
  unfold sosTerm
  have h1 := mul_nonneg (le_of_lt certC1_pos) (sq_nonneg (4 * (actB6Vec h a 0) ^ 3 - actB6Vec h a 0))
  have h2 := mul_nonneg (le_of_lt certC2_pos) (sq_nonneg (evalPoly polyQ2 (actB6Vec h a)))
  have h3 := mul_nonneg (le_of_lt certC3_pos) (sq_nonneg (evalPoly polyQ3 (actB6Vec h a)))
  have h4 := mul_nonneg (le_of_lt certC4_pos) (sq_nonneg (evalPoly polyQ4 (actB6Vec h a)))
  have h5 := mul_nonneg (le_of_lt certC5_pos) (sq_nonneg (evalPoly polyQ5 (actB6Vec h a)))
  have h6 := mul_nonneg (le_of_lt certC6_pos) (sq_nonneg (evalPoly polyQ6 (actB6Vec h a)))
  have h7 := mul_nonneg (le_of_lt certC7_pos) (sq_nonneg (evalPoly polyQ7 (actB6Vec h a)))
  linarith

/-- Core `SO(6)` fourth-power bound: for every self-dual skew-orthogonal matrix `A ∈ SO(6)`,
    `∑_{e=0}^{14} a_e^4 ≥ 3 / 4`. -/
theorem so6_fourth_power_bound {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    (3 : ℝ) / 4 ≤ ∑ e : Fin 15, (a e) ^ 4 := by
  have hid := so6_sos_identity ha
  have hrhs : 0 ≤ ∑ h : B6Plus, sosTerm a h :=
    Finset.sum_nonneg fun h _ => sos_term_nonneg a h
  have hcard : (0 : ℝ) < (Fintype.card B6Plus : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : (0 : ℝ) < (certD : ℝ) * (Fintype.card B6Plus : ℝ) := mul_pos certD_pos hcard
  have hprod : 0 ≤ (certD : ℝ) * (Fintype.card B6Plus : ℝ) * ((∑ e : Fin 15, (a e) ^ 4) - 3 / 4) := by
    rw [hid]; exact hrhs
  have hdiff : 0 ≤ (∑ e : Fin 15, (a e) ^ 4) - 3 / 4 := nonneg_of_mul_nonneg_right hprod hpos
  linarith

private lemma fintype_single_le_sum {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (g : α) : f g ≤ ∑ x : α, f x :=
  Finset.single_le_sum (f := f) (fun x _ => hf x) (Finset.mem_univ g)

/-- Equality characterization on `SO(6)`:
    `∑_{e=0}^{14} a_e^4 = 3 / 4` iff every edge satisfies `|a_e| = 0 ∨ |a_e| = 1 / 2`. -/
theorem so6_equality_iff_spectrum {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) :
    (∑ e : Fin 15, (a e) ^ 4 = 3 / 4) ↔ (∀ e : Fin 15, |a e| = 0 ∨ |a e| = 1 / 2) := by
  constructor
  · intro heq e
    have hid := so6_sos_identity ha
    rw [heq, sub_self, mul_zero] at hid
    have hsum0 : ∑ h : B6Plus, sosTerm a h = 0 := hid.symm
    have hle : sosTerm a (edgePerm e) ≤ ∑ h : B6Plus, sosTerm a h :=
      fintype_single_le_sum (sosTerm a) (sos_term_nonneg a) (edgePerm e)
    have hge : 0 ≤ sosTerm a (edgePerm e) := sos_term_nonneg a (edgePerm e)
    have hterm : sosTerm a (edgePerm e) = 0 := by linarith
    unfold sosTerm at hterm
    have h2 := mul_nonneg (le_of_lt certC2_pos) (sq_nonneg (evalPoly polyQ2 (actB6Vec (edgePerm e) a)))
    have h3 := mul_nonneg (le_of_lt certC3_pos) (sq_nonneg (evalPoly polyQ3 (actB6Vec (edgePerm e) a)))
    have h4 := mul_nonneg (le_of_lt certC4_pos) (sq_nonneg (evalPoly polyQ4 (actB6Vec (edgePerm e) a)))
    have h5 := mul_nonneg (le_of_lt certC5_pos) (sq_nonneg (evalPoly polyQ5 (actB6Vec (edgePerm e) a)))
    have h6 := mul_nonneg (le_of_lt certC6_pos) (sq_nonneg (evalPoly polyQ6 (actB6Vec (edgePerm e) a)))
    have h7 := mul_nonneg (le_of_lt certC7_pos) (sq_nonneg (evalPoly polyQ7 (actB6Vec (edgePerm e) a)))
    have h1nonneg := mul_nonneg (le_of_lt certC1_pos)
      (sq_nonneg (4 * (actB6Vec (edgePerm e) a 0) ^ 3 - actB6Vec (edgePerm e) a 0))
    have h1zero : (certC1 : ℝ) * (4 * (actB6Vec (edgePerm e) a 0) ^ 3 - actB6Vec (edgePerm e) a 0) ^ 2 = 0 := by
      linarith
    have hq1_sq : (4 * (actB6Vec (edgePerm e) a 0) ^ 3 - actB6Vec (edgePerm e) a 0) ^ 2 = 0 :=
      (mul_eq_zero.mp h1zero).resolve_left (ne_of_gt certC1_pos)
    have hq1 : 4 * (actB6Vec (edgePerm e) a 0) ^ 3 - actB6Vec (edgePerm e) a 0 = 0 :=
      sq_eq_zero_iff.mp hq1_sq
    have hfact : actB6Vec (edgePerm e) a 0 * (4 * (actB6Vec (edgePerm e) a 0) ^ 2 - 1) = 0 := by
      linarith
    rw [actB6Vec_edgePerm_zero_sq] at hfact
    rcases mul_eq_zero.mp hfact with h0 | hhalf
    · left
      have hsq0 : (a e) ^ 2 = 0 := by
        rw [← actB6Vec_edgePerm_zero_sq e a, h0]; ring
      exact abs_eq_zero.mpr (sq_eq_zero_iff.mp hsq0)
    · right
      have habs_sq : |a e| ^ 2 = (1 / 2 : ℝ) ^ 2 := by
        rw [sq_abs]; linarith
      have hdiff : (|a e| - 1 / 2) * (|a e| + 1 / 2) = 0 := by linarith
      rcases mul_eq_zero.mp hdiff with hpos | hneg
      · linarith
      · linarith [abs_nonneg (a e)]
  · intro hspec
    have h4 : ∀ e : Fin 15, (a e) ^ 4 = (1 / 4 : ℝ) * (a e) ^ 2 := by
      intro e
      rcases hspec e with h0 | hhalf
      · have : a e = 0 := abs_eq_zero.mp h0
        rw [this]; ring
      · have hsq : (a e) ^ 2 = 1 / 4 := by
          rw [← sq_abs, hhalf]; norm_num
        calc (a e) ^ 4 = ((a e) ^ 2) ^ 2 := by ring
          _ = (1 / 4 : ℝ) * (a e) ^ 2 := by rw [hsq]; norm_num
    simp_rw [h4, ← Finset.mul_sum, sum_sq_eq_three ha]
    norm_num

/-- At equality, every vertex of `K₆` is incident to exactly 1 vanishing edge (forming a
    perfect matching of 3 vanishing edges) and 4 edges of magnitude `1 / 2` (12 total). -/
theorem so6_equality_matching_counts {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a)
    (heq : ∑ e : Fin 15, (a e) ^ 4 = 3 / 4) :
    (Finset.univ.filter (fun e : Fin 15 => a e = 0)).card = 3 ∧
    (Finset.univ.filter (fun e : Fin 15 => |a e| = 1 / 2)).card = 12 ∧
    (∀ i : Fin 6, (Finset.univ.filter (fun j : Fin 6 => j ≠ i ∧ toSkewMat a i j = 0)).card = 1) := by
  have hspec := (so6_equality_iff_spectrum ha).mp heq
  have hsq_val : ∀ e : Fin 15, (a e) ^ 2 = if |a e| = 1 / 2 then (1 / 4 : ℝ) else 0 := by
    intro e
    rcases hspec e with h0 | hhalf
    · have ha0 : a e = 0 := abs_eq_zero.mp h0
      simp [ha0]
    · simp only [hhalf, ite_true]
      rw [← sq_abs, hhalf]; norm_num
  have hcard12 : (Finset.univ.filter (fun e : Fin 15 => |a e| = 1 / 2)).card = 12 := by
    have hsum := sum_sq_eq_three ha
    simp_rw [hsq_val] at hsum
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hsum
    have hreal : ((Finset.univ.filter (fun e : Fin 15 => |a e| = 1 / 2)).card : ℝ) = 12 := by
      linarith
    exact_mod_cast hreal
  have hcard3 : (Finset.univ.filter (fun e : Fin 15 => a e = 0)).card = 3 := by
    have hcompl : Finset.univ.filter (fun e : Fin 15 => a e = 0) =
        Finset.univ.filter (fun e : Fin 15 => ¬ (|a e| = 1 / 2)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hspec e with h0 | hhalf
      · constructor
        · intro _; rw [h0]; norm_num
        · intro _; exact abs_eq_zero.mp h0
      · constructor
        · intro ha0; rw [ha0, abs_zero] at hhalf; norm_num at hhalf
        · intro hne; exact absurd hhalf hne
    rw [hcompl]
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 15)))
      (p := fun e : Fin 15 => |a e| = 1 / 2)
    rw [Finset.card_univ, Fintype.card_fin, hcard12] at hpart
    omega
  refine ⟨hcard3, hcard12, ?_⟩
  intro i
  have hrow : ∑ j : Fin 6, (toSkewMat a i j) ^ 2 = 1 := by
    have h := congrFun (congrFun ha.1 i) i
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply_eq] at h
    have hskew : ∀ j : Fin 6, toSkewMat a i j * toSkewMat a j i = - (toSkewMat a i j) ^ 2 := by
      intro j; rw [toSkewMat_swap]; ring
    simp_rw [hskew, Finset.sum_neg_distrib] at h
    linarith
  have hentry : ∀ j : Fin 6, (toSkewMat a i j) ^ 2 =
      if j ≠ i ∧ toSkewMat a i j ≠ 0 then (1 / 4 : ℝ) else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji; simp [toSkewMat_diag]
    · have hne : j ≠ i := hji
      have hlu_sq : ((edgeLookup i j).2 : ℝ) ^ 2 = 1 := by
        fin_cases i <;> fin_cases j <;> simp [edgeLookup] at hne ⊢
      have hm_sq : (toSkewMat a i j) ^ 2 = (a (edgeLookup i j).1) ^ 2 := by
        simp only [toSkewMat, mul_pow, hlu_sq, one_mul]
      rcases hspec (edgeLookup i j).1 with h0 | hhalf
      · have ha0 : a (edgeLookup i j).1 = 0 := abs_eq_zero.mp h0
        have hm0 : toSkewMat a i j = 0 := by simp [toSkewMat, ha0]
        simp [hm0]
      · have hsq4 : (toSkewMat a i j) ^ 2 = 1 / 4 := by
          rw [hm_sq, ← sq_abs, hhalf]; norm_num
        have hmne : toSkewMat a i j ≠ 0 := by
          intro hm0; rw [hm0] at hsq4; norm_num at hsq4
        simp [hne, hmne, hsq4]
  simp_rw [hentry] at hrow
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hrow
  have h4 : (Finset.univ.filter (fun j : Fin 6 => j ≠ i ∧ toSkewMat a i j ≠ 0)).card = 4 := by
    have hr : ((Finset.univ.filter (fun j : Fin 6 => j ≠ i ∧ toSkewMat a i j ≠ 0)).card : ℝ) = 4 := by
      linarith
    exact_mod_cast hr
  have htot : (Finset.univ.filter (fun j : Fin 6 => j ≠ i)).card = 5 := by
    fin_cases i <;> decide
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : Fin 6 => j ≠ i))
    (p := fun j : Fin 6 => toSkewMat a i j = 0)
  simp only [Finset.filter_filter] at hsplit
  rw [htot, h4] at hsplit
  omega

end TwoQubitMaximalMagic
