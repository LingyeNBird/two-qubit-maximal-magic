module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Real.Sqrt

/-!
# Challenge: Resolution of the Two-Qubit Maximal Magic Conjecture (Open Quantum Problem E28, `n = 2`)

This trusted statement file defines the standard quantum-information objects for pure two-qubit
states `|ψ⟩ ∈ ℂ⁴` using Mathlib alone and states the principal theorems proved in
`TwoQubitMaximalMagic`:

1. **Sharp Stabilizer Rényi Entropy (SRE) upper bound for all `α ≥ 2`**
   (`pauli_fourth_moment_lower_bound`, `sre2_upper_bound`, `pauli_moment_lower_bound_all_alpha`,
   `sre_upper_bound_all_alpha`): for every normalized pure two-qubit state `|ψ⟩` and every
   `α ≥ 2`, `M_α(|ψ⟩) ≤ (1 / (1 - α)) * log ((1 + 3 · 4^{1 - α}) / 4)`, specializing at `α = 2`
   to `M_2(|ψ⟩) ≤ log (16 / 7)`.
2. **Exact attainment** (`mub_fiducial_attains_sre`, `mub_fiducial_attains_sre2`): attained by
   `|ψ_MUB⟩ = (1/2)(1, 1, 1, i)`.
3. **Complete classification of all 480 maximizers** (`maximizer_iff_mub_spectrum`,
   `maximizer_iff_clifford_orbit`, `maximizer_densityMatrix_ncard_eq_480`,
   `maximizer_iff_pauli_mub_fiducial`): for every `α ≥ 2`, equality holds iff all 15 non-identity
   Pauli expectations have magnitude in `{0, 1/2}`, iff `|ψ⟩` lies in the single two-qubit
   Clifford orbit of `|ψ_MUB⟩` (up to global phase), iff `|ψ⟩` is a two-qubit Pauli 5-MUB
   fiducial state; the set of maximizer density matrices `|ψ⟩⟨ψ|` is finite of exact cardinality
   `480`.
4. **Entanglement (concurrence) dichotomy and 192 / 288 split** (`concurrence_eq_wootters`,
   `maximizer_concurrence_dichotomy`, `maximizer_concurrence_distribution`): every maximizer has
   Wootters concurrence strictly in `{1/2, 1/√2}`, with exactly `192` maximizer density matrices
   having `C = 1/2` and `288` having `C = 1/√2`.

Note: `sre` uses the natural logarithm `Real.log`; dividing by `Real.log 2` converts to the
base-2 convention `log₂(16 / 7)`.
-/

@[expose] public section

open scoped Matrix

namespace TwoQubitMaximalMagic.Challenge

/-- A pure two-qubit state vector in `ℂ⁴`. -/
abbrev State := Fin 4 → ℂ

/-- Squared Euclidean norm `⟨ψ | ψ⟩ = ∑_{i=0}^3 |ψ_i|²`. -/
noncomputable def normSq (ψ : State) : ℝ :=
  ∑ i : Fin 4, ‖ψ i‖ ^ 2

/-- A pure two-qubit state is normalized iff `∑_{i=0}^3 |ψ_i|² = 1`. -/
def IsNormalized (ψ : State) : Prop :=
  normSq ψ = 1

/-- Single-qubit Pauli matrices indexed by `Fin 4`: `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`. -/
def pauli1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- Two-qubit Pauli matrices `P_a ⊗ P_b` on `ℂ⁴ ≅ ℂ² ⊗ ℂ²`. -/
def pauli2 (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    pauli1 a ⟨i.val / 2, Nat.div_lt_of_lt_mul i.isLt⟩ ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ *
    pauli1 b ⟨i.val % 2, Nat.mod_lt i.val Nat.two_pos⟩ ⟨j.val % 2, Nat.mod_lt j.val Nat.two_pos⟩

/-- Complex Pauli expectation value `⟨ψ | (P_a ⊗ P_b) | ψ⟩`. -/
def pauliExp (ψ : State) (a b : Fin 4) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, star (ψ i) * pauli2 a b i j * ψ j

/-- The `2α`-th Pauli moment `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α}`. -/
noncomputable def pauliMoment (ψ : State) (α : ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ‖pauliExp ψ a b‖ ^ (2 * α)

/-- The Stabilizer Rényi Entropy (SRE) of order `α` for a two-qubit pure state `ψ`:
    `M_α(|ψ⟩) = (1 / (1 - α)) * log((1 / 4) * ∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α})`. -/
noncomputable def sre (ψ : State) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * Real.log ((1 / 4 : ℝ) * pauliMoment ψ α)

/-- Explicit two-qubit Pauli 5-MUB fiducial state `|ψ_MUB⟩ = (1/2, 1/2, 1/2, i/2)`. -/
noncomputable def mubFiducial : State
  | 0 => (1 / 2 : ℂ)
  | 1 => (1 / 2 : ℂ)
  | 2 => (1 / 2 : ℂ)
  | 3 => (1 / 2 : ℂ) * Complex.I

/-- Pure-state density matrix `ρ_ψ = |ψ⟩⟨ψ|`. -/
def densityMatrix (ψ : State) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ψ i * star (ψ j)

/-- Textbook definition of the two-qubit Clifford group: a `4 × 4` complex unitary matrix
    normalizing the two-qubit Pauli group `{±1, ±i} · P₂`. -/
def IsClifford2 (U : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  Uᴴ * U = 1 ∧
  ∀ a b : Fin 4, ∃ c d : Fin 4, ∃ k : Fin 4,
    U * pauli2 a b * Uᴴ = (Complex.I ^ k.val) • pauli2 c d

/-- Complex inner product `⟨u | v⟩ = ∑_i conj(u_i) v_i` on `State = Fin 4 → ℂ`. -/
def innerState (u v : State) : ℂ :=
  ∑ i : Fin 4, star (u i) * v i

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

/-- Wootters concurrence of a pure two-qubit state `|ψ⟩ ∈ ℂ⁴`:
    `C(|ψ⟩) = 2 |ψ₀ ψ₃ - ψ₁ ψ₂|`. -/
noncomputable def concurrence (ψ : State) : ℝ :=
  2 * ‖ψ 0 * ψ 3 - ψ 1 * ψ 2‖

/-- Exact 4th-moment lower bound: `∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|⁴ ≥ 7 / 4` for all pure two-qubit states. -/
theorem pauli_fourth_moment_lower_bound {ψ : State} (hψ : IsNormalized ψ) :
    (7 : ℝ) / 4 ≤ ∑ a : Fin 4, ∑ b : Fin 4, ‖pauliExp ψ a b‖ ^ 4 := by
  sorry

/-- Sharp upper bound on the order-2 Stabilizer Rényi Entropy: `M_2(|ψ⟩) ≤ log (16 / 7)`. -/
theorem sre2_upper_bound {ψ : State} (hψ : IsNormalized ψ) :
    sre ψ 2 ≤ Real.log (16 / 7) := by
  sorry

/-- Full Pauli-moment lower bound for all Rényi orders `α ≥ 2`:
    `1 + 3 · 4^{1 - α} ≤ ∑_{P ∈ P_2} |⟨ψ|P|ψ⟩|^{2α}`. -/
theorem pauli_moment_lower_bound_all_alpha {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α) :
    1 + 3 * (4 : ℝ) ^ (1 - α) ≤ pauliMoment ψ α := by
  sorry

/-- Sharp upper bound on the Stabilizer Rényi Entropy `M_α` for every normalized pure two-qubit
    state `|ψ⟩ ∈ ℂ⁴` and every Rényi order `α ≥ 2`. -/
theorem sre_upper_bound_all_alpha {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α ≤ (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) := by
  sorry

/-- The MUB fiducial state `|ψ_MUB⟩ = (1/2)(1, 1, 1, i)` attains exact equality in `M_α` for all `α ≥ 2`. -/
theorem mub_fiducial_attains_sre {α : ℝ} (hα : 2 ≤ α) :
    sre mubFiducial α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) := by
  sorry

/-- In particular, `M_2(|ψ_MUB⟩) = log (16 / 7)`. -/
theorem mub_fiducial_attains_sre2 :
    sre mubFiducial 2 = Real.log (16 / 7) := by
  sorry

/-- Exact Pauli-spectrum characterization of all maximizers of `M_α` (`α ≥ 2`). -/
theorem maximizer_iff_mub_spectrum {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∀ a b : Fin 4, (a ≠ 0 ∨ b ≠ 0) → (‖pauliExp ψ a b‖ = 0 ∨ ‖pauliExp ψ a b‖ = 1 / 2) := by
  sorry

/-- Single Clifford orbit characterization: `ψ` maximizes `M_α` (`α ≥ 2`) iff `ψ` lies in the
    two-qubit Clifford orbit of `mubFiducial` up to a unit global phase. -/
theorem maximizer_iff_clifford_orbit {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsClifford2 U ∧
        ∃ θ : ℂ, ‖θ‖ = 1 ∧ ψ = θ • (U *ᵥ mubFiducial) := by
  sorry

/-- Exact cardinality of the maximizer set: for every `α ≥ 2`, the set of pure-state density
    matrices `|ψ⟩⟨ψ|` maximizing `M_α` is finite and has exact cardinality `480`. -/
theorem maximizer_densityMatrix_ncard_eq_480 {α : ℝ} (hα : 2 ≤ α) :
    let S : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
      {ρ | ∃ ψ : State, IsNormalized ψ ∧
        sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ∧
        ρ = densityMatrix ψ}
    S.Finite ∧ S.ncard = 480 := by
  sorry

/-- Exact equivalence with two-qubit Pauli 5-MUB fiducial states for all `α ≥ 2`. -/
theorem maximizer_iff_pauli_mub_fiducial {ψ : State} (hψ : IsNormalized ψ) {α : ℝ} (hα : 2 ≤ α) :
    sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4) ↔
      IsPauliMUBFiducial ψ := by
  sorry

/-- Equivalence of `concurrence` with Wootters' spin-flip formula `|⟨ψ^* | (Y ⊗ Y) | ψ⟩|`. -/
theorem concurrence_eq_wootters (ψ : State) :
    concurrence ψ = ‖∑ i : Fin 4, ∑ j : Fin 4, ψ i * pauli2 2 2 i j * ψ j‖ := by
  sorry

/-- Concurrence dichotomy: every maximizer of `M_α` (`α ≥ 2`) has concurrence `1 / 2` or `1 / √2`. -/
theorem maximizer_concurrence_dichotomy {ψ : State} (hψ : IsNormalized ψ)
    {α : ℝ} (hα : 2 ≤ α)
    (hmax : sre ψ α = (1 / (1 - α)) * Real.log ((1 + 3 * (4 : ℝ) ^ (1 - α)) / 4)) :
    concurrence ψ = 1 / 2 ∨ concurrence ψ = 1 / Real.sqrt 2 := by
  sorry

/-- Exact `192 / 288` entanglement split: among the 480 maximizer density matrices for `M_α`
    (`α ≥ 2`), exactly `192` have `C = 1 / 2` and exactly `288` have `C = 1 / √2`. -/
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
  sorry

end TwoQubitMaximalMagic.Challenge
