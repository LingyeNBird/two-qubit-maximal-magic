import TwoQubitMaximalMagic.MainTheorem
import TwoQubitMaximalMagic.Maximizers

/-!
# Formal Proof of the Two-Qubit Maximal Magic Conjecture
(Two-Qubit Case of Open Quantum Problem E28)

Root module re-exporting all definitions and proved theorems:
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
-/
