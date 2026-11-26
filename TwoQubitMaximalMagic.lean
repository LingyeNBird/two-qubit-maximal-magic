import TwoQubitMaximalMagic.MainTheorem
import TwoQubitMaximalMagic.Maximizers
import TwoQubitMaximalMagic.Entanglement

/-!
# Formal Proof of the Two-Qubit Maximal Magic Conjecture
(Two-Qubit Case of Open Quantum Problem E28)

Root module re-exporting all definitions and proved theorems (32 audited theorems):
- `TwoQubitMaximalMagic.so6_fourth_power_bound`
- `TwoQubitMaximalMagic.so6_equality_iff_spectrum`
- `TwoQubitMaximalMagic.so6_equality_matching_counts`
- `TwoQubitMaximalMagic.pauli_fourth_moment_lower_bound`
- `TwoQubitMaximalMagic.sre2_upper_bound`
- `TwoQubitMaximalMagic.pauli_moment_lower_bound_all_alpha`
- `TwoQubitMaximalMagic.sre_upper_bound_all_alpha`
- `TwoQubitMaximalMagic.mub_fiducial_attains_moment`
- `TwoQubitMaximalMagic.mub_fiducial_attains_sre`
- `TwoQubitMaximalMagic.mub_fiducial_attains_sre2`
- `TwoQubitMaximalMagic.maximizer_iff_mub_spectrum`
- `TwoQubitMaximalMagic.maximizer_matching_counts`
- `TwoQubitMaximalMagic.pauli_commute_iff_edgeDisjoint`
- `TwoQubitMaximalMagic.pauli_anticommute_iff_not_edgeDisjoint`
- `TwoQubitMaximalMagic.maximizer_zero_paulis_maximal_commuting`
- `TwoQubitMaximalMagic.densityMatrix_eq_pauli_expansion`
- `TwoQubitMaximalMagic.densityMatrix_eq_iff_so6Edge_eq`
- `TwoQubitMaximalMagic.densityMatrix_eq_iff_phase`
- `TwoQubitMaximalMagic.clifford_lift_b6Plus`
- `TwoQubitMaximalMagic.maximizer_iff_clifford_orbit`
- `TwoQubitMaximalMagic.maximizer_iff_clifford_densityMatrix`
- `TwoQubitMaximalMagic.maximizer_densityMatrix_ncard_eq_480`
- `TwoQubitMaximalMagic.mubFiducial_isPauliMUBFiducial`
- `TwoQubitMaximalMagic.maximizer_iff_pauli_mub_fiducial`
- `TwoQubitMaximalMagic.concurrence_eq_wootters`
- `TwoQubitMaximalMagic.concurrence_sq_eq_one_sub_localA`
- `TwoQubitMaximalMagic.concurrence_sq_eq_one_sub_localB`
- `TwoQubitMaximalMagic.concurrence_sq_eq_linear_entropyA`
- `TwoQubitMaximalMagic.mubFiducial_concurrence`
- `TwoQubitMaximalMagic.maximizer_concurrence_dichotomy`
- `TwoQubitMaximalMagic.maximizer_not_maximally_entangled_and_not_separable`
- `TwoQubitMaximalMagic.maximizer_concurrence_distribution`
-/
