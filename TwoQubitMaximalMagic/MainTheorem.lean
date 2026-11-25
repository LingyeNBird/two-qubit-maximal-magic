import TwoQubitMaximalMagic.Certificate
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Proof of the Two-Qubit Maximal Magic Conjecture (Two-Qubit Case of Open Quantum Problem E28)

Main results proved in this file (for all normalized pure two-qubit states `ψ : Fin 4 → ℂ`):
1. `pauli_fourth_moment_lower_bound`:
   `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^4 ≥ 7 / 4`.
2. `sre2_upper_bound`:
   `M_2(|ψ⟩) ≤ log (16 / 7)`.
3. `pauli_moment_lower_bound_all_alpha`:
   For every `α ≥ 2`, `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α} ≥ 1 + 3 · 4^{1 - α} = 1 + 12 · 4^{-α}`.
4. `sre_upper_bound_all_alpha` (**Two-Qubit Maximal Magic Conjecture, Liu–Low–Yin QST 2026**):
   For every `α ≥ 2`, `M_α(|ψ⟩) ≤ (1 / (1 - α)) * log ((1 + 3 · 4^{1 - α}) / 4)`.
5. `mub_fiducial_attains_moment`, `mub_fiducial_attains_sre`, `mub_fiducial_attains_sre2`:
   The explicit state `mubFiducial = (1/2, 1/2, 1/2, i/2)` is normalized and achieves exact
   equality for every `α ≥ 2` (in particular `M_2(mubFiducial) = log (16 / 7)`).
6. `maximizer_iff_mub_spectrum`, `maximizer_matching_counts`:
   For every `α ≥ 2`, equality holds iff the 15 non-identity Pauli expectations lie in `{0, ±1/2}`,
   with exactly 3 vanishing expectations (forming a perfect matching in `K₆`) and 12 expectations
   of magnitude `1/2`.

See `TwoQubitMaximalMagic/Maximizers.lean` for the further formal proofs that:
- the 3 vanishing Paulis form a maximal pairwise-commuting Pauli triple,
- the maximizers form a single two-qubit Clifford orbit of `mubFiducial` of exact cardinality 480
  (as pure-state density matrices), and
- a normalized state maximizes `M_α` (`α ≥ 2`) iff it is a two-qubit Pauli (multi-qubit
  Weyl–Heisenberg) 5-MUB fiducial state.
-/

namespace TwoQubitMaximalMagic

/-! ### Part 1: The `α = 2` Conjecture -/

/-- Exact 4th-moment lower bound: `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^4 ≥ 7 / 4` for all pure two-qubit states. -/
theorem pauli_fourth_moment_lower_bound {ψ : State} (hψ : IsNormalized ψ) :
    (7 : ℝ) / 4 ≤ ∑ a : Fin 4, ∑ b : Fin 4, ‖pauliExp ψ a b‖ ^ 4 := by
  rw [pauli_sum_pow4_eq_one_add_so6 hψ]
  have h := so6_fourth_power_bound (so6Edge_isSkewOrth6 hψ)
  linarith

/-- Sharp upper bound on the 2-Stabilizer Rényi Entropy: `M_2(|ψ⟩) ≤ log (16 / 7)`. -/
theorem sre2_upper_bound {ψ : State} (hψ : IsNormalized ψ) :
    sre ψ 2 ≤ Real.log (16 / 7) := by
  have h4 : (7 : ℝ) / 4 ≤ pauliMoment ψ 2 := by
    have hpow : ∀ a b : Fin 4, ‖pauliExp ψ a b‖ ^ (2 * (2 : ℝ)) = ‖pauliExp ψ a b‖ ^ 4 := by
      intro a b
      rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    unfold pauliMoment
    simp_rw [hpow]
    exact pauli_fourth_moment_lower_bound hψ
  unfold sre
  have harg : (7 / 16 : ℝ) ≤ (1 / 4 : ℝ) * pauliMoment ψ 2 := by linarith
  have hlog : Real.log (7 / 16) ≤ Real.log ((1 / 4 : ℝ) * pauliMoment ψ 2) :=
    Real.log_le_log (by norm_num) harg
  have hlog_inv : Real.log (16 / 7 : ℝ) = - Real.log (7 / 16 : ℝ) := by
    rw [← Real.log_inv]
    congr 1; norm_num
  rw [hlog_inv]
  have hc : (1 / (1 - (2 : ℝ))) = -1 := by norm_num
  rw [hc]
  linarith

/-! ### Part 2: Extension to All Rényi Orders `α ≥ 2` via Hölder's Inequality -/

/-- Hölder inequality on `Fin 15`: for nonnegative `y : Fin 15 → ℝ` with `∑ y = 3` and `α > 2`,
    `(∑ y^2)^(α - 1) ≤ 3^(α - 2) * ∑ y^α`. -/
lemma so6_moment_holder {y : Fin 15 → ℝ} (hy_nonneg : ∀ e, 0 ≤ y e)
    (hsum1 : ∑ e : Fin 15, y e = 3)
    {α : ℝ} (hα : 2 < α) :
    (∑ e : Fin 15, (y e) ^ 2) ^ (α - 1) ≤ (3 : ℝ) ^ (α - 2) * ∑ e : Fin 15, (y e) ^ α := by
  have hp_gt1 : 1 < α - 1 := by linarith
  have hα2_pos : 0 < α - 2 := by linarith
  have hα1_pos : 0 < α - 1 := by linarith
  set p : ℝ := α - 1
  set q : ℝ := (α - 1) / (α - 2)
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp_gt1, ?_⟩
    dsimp only [p, q]
    have h1 : α - 1 ≠ 0 := by linarith
    have h2 : α - 2 ≠ 0 := by linarith
    field_simp [h1, h2]
    ring
  let f : Fin 15 → ℝ := fun e => (y e) ^ (α / p)
  let g : Fin 15 → ℝ := fun e => (y e) ^ ((α - 2) / p)
  have hholder := Real.inner_le_Lp_mul_Lq Finset.univ f g hpq
  have hfg : ∀ e : Fin 15, f e * g e = (y e) ^ 2 := by
    intro e
    dsimp only [f, g]
    by_cases he : y e = 0
    · rw [he]
      have h1 : α / p ≠ 0 := div_ne_zero (by linarith) (ne_of_gt hα1_pos)
      have h2 : (α - 2) / p ≠ 0 := div_ne_zero (ne_of_gt hα2_pos) (ne_of_gt hα1_pos)
      rw [Real.zero_rpow h1, Real.zero_rpow h2]
      norm_num
    · have hpos : 0 < y e := lt_of_le_of_ne (hy_nonneg e) (Ne.symm he)
      rw [← Real.rpow_add hpos]
      have hexp : α / p + (α - 2) / p = (2 : ℕ) := by
        field_simp [ne_of_gt hα1_pos]
        ring
      rw [hexp, Real.rpow_natCast]
  have hfp : ∀ e : Fin 15, |f e| ^ p = (y e) ^ α := by
    intro e
    dsimp only [f]
    rw [abs_of_nonneg (Real.rpow_nonneg (hy_nonneg e) _), ← Real.rpow_mul (hy_nonneg e)]
    congr 1
    field_simp [ne_of_gt hα1_pos]
  have hgq : ∀ e : Fin 15, |g e| ^ q = y e := by
    intro e
    dsimp only [g]
    rw [abs_of_nonneg (Real.rpow_nonneg (hy_nonneg e) _), ← Real.rpow_mul (hy_nonneg e)]
    have hexp : (α - 2) / p * q = 1 := by
      dsimp only [p, q]
      have h1 : α - 1 ≠ 0 := by linarith
      have h2 : α - 2 ≠ 0 := by linarith
      field_simp [h1, h2]
    rw [hexp, Real.rpow_one]
  simp_rw [hfg, hfp, hgq, hsum1] at hholder
  -- Raise both sides of `∑ y^2 ≤ (∑ y^α)^(1/p) * 3^(1/q)` to power `p = α - 1 > 0`
  have hS2_nonneg : 0 ≤ ∑ e : Fin 15, (y e) ^ 2 :=
    Finset.sum_nonneg fun e _ => sq_nonneg (y e)
  have hSa_nonneg : 0 ≤ ∑ e : Fin 15, (y e) ^ α :=
    Finset.sum_nonneg fun e _ => Real.rpow_nonneg (hy_nonneg e) _
  have hpow_le := Real.rpow_le_rpow hS2_nonneg hholder (le_of_lt hα1_pos)
  rw [Real.mul_rpow (Real.rpow_nonneg hSa_nonneg _) (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_mul hSa_nonneg, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at hpow_le
  have h1p : 1 / p * p = 1 := by field_simp [ne_of_gt hα1_pos]
  have h1q : 1 / q * p = α - 2 := by
    dsimp only [p, q]
    have h1 : α - 1 ≠ 0 := by linarith
    have h2 : α - 2 ≠ 0 := by linarith
    field_simp [h1, h2]
  rw [h1p, Real.rpow_one, h1q, mul_comm] at hpow_le
  exact hpow_le

/-- On `SO(6)`, for every `α ≥ 2`, `3 * 4^(1 - α) ≤ ∑_{e=0}^{14} |a_e|^{2α}`. -/
theorem so6_moment_lower_bound {a : Fin 15 → ℝ} (ha : IsSkewOrth6 a) {α : ℝ} (hα : 2 ≤ α) :
    3 * (4 : ℝ) ^ (1 - α) ≤ ∑ e : Fin 15, |a e| ^ (2 * α) := by
  have hrew : ∀ e : Fin 15, |a e| ^ (2 * α) = ((a e) ^ 2) ^ α := by
    intro e
    rw [← sq_abs, ← Real.rpow_natCast |a e| 2, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  simp_rw [hrew]
  rcases eq_or_lt_of_le hα with rfl | hlt
  · have h4 : ∀ e : Fin 15, ((a e) ^ 2) ^ (2 : ℝ) = (a e) ^ 4 := by
      intro e
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    simp_rw [h4]
    have hval : 3 * (4 : ℝ) ^ (1 - (2 : ℝ)) = 3 / 4 := by
      rw [show (1 - (2 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one]
      norm_num
    rw [hval]
    exact so6_fourth_power_bound ha
  · have hsum1 := sum_sq_eq_three ha
    have hsum2 : (3 : ℝ) / 4 ≤ ∑ e : Fin 15, ((a e) ^ 2) ^ 2 := by
      have h4 : ∀ e : Fin 15, ((a e) ^ 2) ^ 2 = (a e) ^ 4 := fun e => by ring
      simp_rw [h4]
      exact so6_fourth_power_bound ha
    have hh := so6_moment_holder (fun e => sq_nonneg (a e)) hsum1 hlt
    have hlow : ((3 : ℝ) / 4) ^ (α - 1) ≤ (∑ e : Fin 15, ((a e) ^ 2) ^ 2) ^ (α - 1) :=
      Real.rpow_le_rpow (by norm_num) hsum2 (by linarith)
    have hchain : ((3 : ℝ) / 4) ^ (α - 1) ≤ (3 : ℝ) ^ (α - 2) * ∑ e : Fin 15, ((a e) ^ 2) ^ α :=
      le_trans hlow hh
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ (α - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have h3eq : ((3 : ℝ) / 4) ^ (α - 1) = (3 : ℝ) ^ (α - 2) * (3 * (4 : ℝ) ^ (1 - α)) := by
      rw [Real.div_rpow (by norm_num) (by norm_num)]
      have h3split : (3 : ℝ) ^ (α - 1) = (3 : ℝ) ^ (α - 2) * 3 := by
        rw [← Real.rpow_add_one (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1; ring
      have h4inv : ((4 : ℝ) ^ (α - 1))⁻¹ = (4 : ℝ) ^ (1 - α) := by
        rw [← Real.rpow_neg (by norm_num)]
        congr 1; ring
      rw [div_eq_mul_inv, h3split, h4inv]; ring
    rw [h3eq] at hchain
    exact le_of_mul_le_mul_left hchain h3pos

/-- Full Pauli-moment lower bound for all Rényi orders `α ≥ 2`:
    `1 + 3 · 4^{1 - α} ≤ ∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α}`. -/
theorem pauli_moment_lower_bound_all_alpha {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α) :
    1 + 3 * (4 : ℝ) ^ (1 - α) ≤ pauliMoment ψ α := by
  rw [pauliMoment_eq_one_add_so6 ψ hψ α]
  linarith [so6_moment_lower_bound (so6Edge_isSkewOrth6 hψ) hα]

/-- **Main Theorem (Two-Qubit Maximal Magic Conjecture / Two-Qubit Case of Open Quantum Problem E28)**:
    For every normalized pure two-qubit state `|ψ⟩ ∈ ℂ⁴` and every Rényi order `α ≥ 2`,
    `M_α(|ψ⟩) ≤ (1 / (1 - α)) * log ((1 + 3 · 4^{1 - α}) / 4)`. -/
theorem sre_upper_bound_all_alpha {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α ≤ (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) := by
  have hmom := pauli_moment_lower_bound_all_alpha hψ hα
  have hpos_rhs : (0 : ℝ) < (1 + 3 * (4 : ℝ) ^ (1 - α)) / 4 := by
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  have harg : (1 + 3 * (4 : ℝ) ^ (1 - α)) / 4 ≤ (1 / 4 : ℝ) * pauliMoment ψ α := by linarith
  have hlog : Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ≤
      Real.log ((1 / 4 : ℝ) * pauliMoment ψ α) :=
    Real.log_le_log hpos_rhs harg
  have hneg : (1 / (1 - α)) ≤ 0 := by
    apply div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
  unfold sre
  exact mul_le_mul_of_nonpos_left hlog hneg

/-! ### Part 3: Explicit Attainment by the Weyl–Heisenberg MUB Fiducial State -/

/-- Explicit Weyl–Heisenberg MUB fiducial state `|ψ_MUB⟩ = (1/2, 1/2, 1/2, i/2)`. -/
noncomputable def mubFiducial : State
  | 0 => (1 / 2 : ℂ)
  | 1 => (1 / 2 : ℂ)
  | 2 => (1 / 2 : ℂ)
  | 3 => (1 / 2 : ℂ) * Complex.I

lemma mubFiducial_normalized : IsNormalized mubFiducial := by
  unfold IsNormalized
  rw [normSq_eq_sum_re_im]
  simp [mubFiducial]
  norm_num

lemma mubFiducial_so6_abs (e : Fin 15) :
    |so6Edge mubFiducial e| = if e = 0 ∨ e = 9 ∨ e = 14 then 0 else 1 / 2 := by
  fin_cases e <;>
    simp [so6Edge, mubFiducial,
      pauliExpRe_IX, pauliExpRe_IY, pauliExpRe_IZ,
      pauliExpRe_XI, pauliExpRe_XX, pauliExpRe_XY, pauliExpRe_XZ,
      pauliExpRe_YI, pauliExpRe_YX, pauliExpRe_YY, pauliExpRe_YZ,
      pauliExpRe_ZI, pauliExpRe_ZX, pauliExpRe_ZY, pauliExpRe_ZZ]

/-- The MUB fiducial state attains exact equality in the Pauli-moment bound for all `α ≥ 2`. -/
theorem mub_fiducial_attains_moment {α : ℝ} (hα : 2 ≤ α) :
    pauliMoment mubFiducial α = 1 + 3 * (4 : ℝ) ^ (1 - α) := by
  rw [pauliMoment_eq_one_add_so6 mubFiducial mubFiducial_normalized α, sum_fin15]
  simp only [mubFiducial_so6_abs]
  have h2α_ne : 2 * α ≠ 0 := by linarith
  have h0 : (0 : ℝ) ^ (2 * α) = 0 := Real.zero_rpow h2α_ne
  have hhalf : ((1 / 2 : ℝ)) ^ (2 * α) = (4 : ℝ) ^ (-α) := by
    have h1 : (1 / 2 : ℝ) ^ (2 * α) = ((1 / 2 : ℝ) ^ (2 : ℝ)) ^ α := by
      rw [← Real.rpow_mul (by norm_num)]
    rw [h1]
    have h2 : (1 / 2 : ℝ) ^ (2 : ℝ) = (4 : ℝ)⁻¹ := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have h12 : 12 * (4 : ℝ) ^ (-α) = 3 * (4 : ℝ) ^ (1 - α) := by
    have : (4 : ℝ) ^ (1 - α) = 4 * (4 : ℝ) ^ (-α) := by
      rw [show (1 - α) = 1 + (-α) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 4), Real.rpow_one]
    rw [this]; ring
  norm_num [h0, hhalf]
  linarith

/-- The MUB fiducial state attains exact equality in the SRE bound for every `α ≥ 2`. -/
theorem mub_fiducial_attains_sre {α : ℝ} (hα : 2 ≤ α) :
    sre mubFiducial α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) := by
  unfold sre
  rw [mub_fiducial_attains_moment hα]
  ring_nf

/-- In particular, `M_2(|ψ_MUB⟩) = log (16 / 7)`. -/
theorem mub_fiducial_attains_sre2 :
    sre mubFiducial 2 = Real.log (16 / 7) := by
  rw [mub_fiducial_attains_sre (le_refl 2)]
  have h4 : (4 : ℝ) ^ (1 - (2 : ℝ)) = 1 / 4 := by
    rw [show (1 - (2 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  rw [h4]
  have h1 : (1 + 3 * (1 / 4 : ℝ)) / 4 = (16 / 7 : ℝ)⁻¹ := by norm_num
  rw [h1, Real.log_inv]
  ring

/-! ### Part 4: Complete Characterization of All Maximizers for Every `α ≥ 2` -/

/-- Exact equality characterization for all `α ≥ 2`:
    A normalized pure two-qubit state `ψ` maximizes `M_α` iff every non-identity Pauli
    expectation satisfies `|⟨ψ|P|ψ⟩| ∈ {0, 1/2}` (equivalently, 3 vanishing Paulis forming
    a perfect matching in `K₆` / maximal commuting triple and 12 Paulis of magnitude `1/2`). -/
theorem maximizer_iff_mub_spectrum {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∀ a b : Fin 4, (a ≠ 0 ∨ b ≠ 0) → (‖pauliExp ψ a b‖ = 0 ∨ ‖pauliExp ψ a b‖ = 1 / 2) := by
  have ha := so6Edge_isSkewOrth6 hψ
  -- First reduce equality of `sre` to equality of `∑ |so6Edge ψ e|^{2α} = 3 * 4^{1 - α}`
  have hsre_iff :
      sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∑ e : Fin 15, |so6Edge ψ e| ^ (2 * α) = 3 * (4 : ℝ) ^ (1 - α) := by
    unfold sre
    have h1a_ne : (1 / (1 - α)) ≠ 0 := div_ne_zero one_ne_zero (by linarith)
    have hpos1 : (0 : ℝ) < (1 / 4 : ℝ) * pauliMoment ψ α := by
      have hm := pauli_moment_lower_bound_all_alpha hψ hα
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    have hpos2 : (0 : ℝ) < (1 + 3 * (4 : ℝ) ^ (1 - α)) / 4 := by
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    have hlog_iff :
        Real.log ((1 / 4 : ℝ) * pauliMoment ψ α) = Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
        (1 / 4 : ℝ) * pauliMoment ψ α = (1 + 3 * (4 : ℝ) ^ (1 - α)) / 4 :=
      Real.log_injOn_pos.eq_iff hpos1 hpos2
    rw [mul_right_inj' h1a_ne, hlog_iff, pauliMoment_eq_one_add_so6 ψ hψ α]
    constructor <;> intro h <;> linarith
  -- Next show `∀ a b, (a ≠ 0 ∨ b ≠ 0) → ...` is equivalent to `∀ e : Fin 15, |so6Edge ψ e| ∈ {0, 1/2}`
  have hspec_iff :
      (∀ e : Fin 15, |so6Edge ψ e| = 0 ∨ |so6Edge ψ e| = 1 / 2) ↔
      (∀ a b : Fin 4, (a ≠ 0 ∨ b ≠ 0) → (‖pauliExp ψ a b‖ = 0 ∨ ‖pauliExp ψ a b‖ = 1 / 2)) := by
    constructor
    · intro h a b hab
      rw [norm_pauliExp]
      fin_cases a <;> fin_cases b
      · exfalso; rcases hab with h1 | h1 <;> exact h1 rfl
      · simpa [so6Edge, abs_neg] using h 12
      · simpa [so6Edge, abs_neg] using h 10
      · simpa [so6Edge] using h 9
      · simpa [so6Edge] using h 4
      · simpa [so6Edge, abs_neg] using h 5
      · simpa [so6Edge] using h 6
      · simpa [so6Edge] using h 7
      · simpa [so6Edge, abs_neg] using h 8
      · simpa [so6Edge, abs_neg] using h 1
      · simpa [so6Edge] using h 2
      · simpa [so6Edge] using h 3
      · simpa [so6Edge] using h 0
      · simpa [so6Edge, abs_neg] using h 11
      · simpa [so6Edge] using h 13
      · simpa [so6Edge] using h 14
    · intro h e
      fin_cases e
      · simpa [so6Edge, norm_pauliExp] using h 3 0 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 2 1 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 2 2 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 2 3 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 1 0 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 1 1 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 1 2 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 1 3 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 2 0 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 0 3 (Or.inr (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 0 2 (Or.inr (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 3 1 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp, abs_neg] using h 0 1 (Or.inr (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 3 2 (Or.inl (by decide))
      · simpa [so6Edge, norm_pauliExp] using h 3 3 (Or.inl (by decide))
  rw [hsre_iff, ← hspec_iff]
  constructor
  · intro heq
    -- Show equality at `α ≥ 2` forces equality at `α = 2`!
    have h4eq : ∑ e : Fin 15, (so6Edge ψ e) ^ 4 = 3 / 4 := by
      rcases eq_or_lt_of_le hα with rfl | hlt
      · have hrew : ∀ e : Fin 15, |so6Edge ψ e| ^ (2 * (2 : ℝ)) = (so6Edge ψ e) ^ 4 := by
          intro e
          rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have : |so6Edge ψ e| ^ 4 = (|so6Edge ψ e| ^ 2) ^ 2 := by ring
          rw [this, sq_abs]; ring
        simp_rw [hrew] at heq
        have hval : 3 * (4 : ℝ) ^ (1 - (2 : ℝ)) = 3 / 4 := by
          rw [show (1 - (2 : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one]
          norm_num
        rw [heq, hval]
      · have hrew : ∀ e : Fin 15, |so6Edge ψ e| ^ (2 * α) = ((so6Edge ψ e) ^ 2) ^ α := by
          intro e
          rw [← sq_abs, ← Real.rpow_natCast |so6Edge ψ e| 2, ← Real.rpow_mul (abs_nonneg _)]
          norm_num
        simp_rw [hrew] at heq
        have hsum2_ge : (3 : ℝ) / 4 ≤ ∑ e : Fin 15, ((so6Edge ψ e) ^ 2) ^ 2 := by
          have h4 : ∀ e : Fin 15, ((so6Edge ψ e) ^ 2) ^ 2 = (so6Edge ψ e) ^ 4 := fun e => by ring
          simp_rw [h4]; exact so6_fourth_power_bound ha
        have hh := so6_moment_holder (fun e => sq_nonneg (so6Edge ψ e))
          (sum_sq_eq_three ha) hlt
        rw [heq] at hh
        have hrhs : (3 : ℝ) ^ (α - 2) * (3 * (4 : ℝ) ^ (1 - α)) = ((3 : ℝ) / 4) ^ (α - 1) := by
          rw [Real.div_rpow (by norm_num) (by norm_num)]
          have h3split : (3 : ℝ) ^ (α - 1) = (3 : ℝ) ^ (α - 2) * 3 := by
            rw [← Real.rpow_add_one (by norm_num : (3 : ℝ) ≠ 0)]
            congr 1; ring
          have h4inv : ((4 : ℝ) ^ (α - 1))⁻¹ = (4 : ℝ) ^ (1 - α) := by
            rw [← Real.rpow_neg (by norm_num)]
            congr 1; ring
          rw [div_eq_mul_inv, h3split, h4inv]; ring
        rw [hrhs] at hh
        have hle : ∑ e : Fin 15, ((so6Edge ψ e) ^ 2) ^ 2 ≤ 3 / 4 := by
          by_contra hgt
          push Not at hgt
          have hstr : ((3 : ℝ) / 4) ^ (α - 1) < (∑ e : Fin 15, ((so6Edge ψ e) ^ 2) ^ 2) ^ (α - 1) :=
            Real.rpow_lt_rpow (by norm_num) hgt (by linarith)
          linarith
        have h4 : ∀ e : Fin 15, ((so6Edge ψ e) ^ 2) ^ 2 = (so6Edge ψ e) ^ 4 := fun e => by ring
        simp_rw [h4] at hle hsum2_ge
        linarith
    exact (so6_equality_iff_spectrum ha).mp h4eq
  · intro hspec
    have hterm : ∀ e : Fin 15, |so6Edge ψ e| ^ (2 * α) = (4 : ℝ) ^ (1 - α) * (so6Edge ψ e) ^ 2 := by
      intro e
      rcases hspec e with h0 | hhalf
      · have he0 : so6Edge ψ e = 0 := abs_eq_zero.mp h0
        rw [h0, he0, Real.zero_rpow (by linarith)]; ring
      · rw [hhalf, ← sq_abs, hhalf]
        have h1 : (1 / 2 : ℝ) ^ (2 * α) = (4 : ℝ) ^ (-α) := by
          rw [show (1 / 2 : ℝ) ^ (2 * α) = ((1 / 2 : ℝ) ^ (2 : ℝ)) ^ α from by
            rw [← Real.rpow_mul (by norm_num)]]
          have h2 : (1 / 2 : ℝ) ^ (2 : ℝ) = (4 : ℝ)⁻¹ := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
          rw [h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
        have h2 : (4 : ℝ) ^ (1 - α) * (1 / 2 : ℝ) ^ 2 = (4 : ℝ) ^ (-α) := by
          have : (4 : ℝ) ^ (1 - α) = 4 * (4 : ℝ) ^ (-α) := by
            rw [show (1 - α) = 1 + (-α) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 4),
                Real.rpow_one]
          rw [this]; ring
        rw [h1, h2]
    simp_rw [hterm, ← Finset.mul_sum, sum_sq_eq_three ha]
    ring

/-- Every maximizer of `M_α` (`α ≥ 2`) has exactly 3 vanishing non-identity Pauli expectations
    (forming a perfect matching in `K₆`, i.e., a maximal commuting Pauli triple) and 12
    expectations of magnitude `1 / 2`. -/
theorem maximizer_matching_counts {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α)
    (hmax : sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4)) :
    (Finset.univ.filter (fun e : Fin 15 => so6Edge ψ e = 0)).card = 3 ∧
    (Finset.univ.filter (fun e : Fin 15 => |so6Edge ψ e| = 1 / 2)).card = 12 ∧
    (∀ i : Fin 6, (Finset.univ.filter (fun j : Fin 6 => j ≠ i ∧ toSkewMat (so6Edge ψ) i j = 0)).card = 1) := by
  have ha := so6Edge_isSkewOrth6 hψ
  have hspec_pauli := (maximizer_iff_mub_spectrum hψ hα).mp hmax
  have hspec_so6 : ∀ e : Fin 15, |so6Edge ψ e| = 0 ∨ |so6Edge ψ e| = 1 / 2 := by
    intro e
    fin_cases e
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 3 0 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 2 1 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 2 2 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 2 3 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 1 0 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 1 1 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 1 2 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 1 3 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 2 0 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 0 3 (Or.inr (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 0 2 (Or.inr (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 3 1 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp, abs_neg] using hspec_pauli 0 1 (Or.inr (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 3 2 (Or.inl (by decide))
    · simpa [so6Edge, norm_pauliExp] using hspec_pauli 3 3 (Or.inl (by decide))
  exact so6_equality_matching_counts ha ((so6_equality_iff_spectrum ha).mpr hspec_so6)

end TwoQubitMaximalMagic
