# CHMD: pure point spectrum above 1/2, Weyl criterion, local finiteness (2026-10-16)

RH goal ACTIVE. Contribution 5 of this lane (after MUST-1541–1548). STATUS row MUST-1551.
Card: docs/drafts/pipeline/3-formalized/chmd-pure-point-above-threshold-2026-10-16.md.
Module: `RHTower/CHMDPurePointAboveThreshold` (namespace RHTower.CHMDPolar), 11 declarations, standard axioms, wired.

## Results (unconditional)
- `isUnit_of_symmetric_of_bounded_below` / `exists_approx_eigen_of_mem_spectrum`: GENERIC real-Hilbert Weyl criterion
  for symmetric bounded `T : H →L[ℝ] H`: `μ ∈ spectrum ℝ T → ∃ unit w_n, ‖T w_n − μ w_n‖ → 0`. (mathlib lacks it; corpus
  `HTGeometry.isUnit_of_isSelfAdjoint_of_lower_bound` is the ℂ version.)
- `mem_spectrum_of_eigenvector` (generic converse).
- `exists_eigenvector_of_approx_eigen_above_half`: unit approx eigenvectors at μ > 1/2 ⇒ eigenvector (weak subsequence via
  `exists_real_weak_subseq` with `letI := Lp.SecondCountableTopology` + `Fact ((2:ENNReal) ≠ ⊤)`; weak limit ≠ 0 by MUST-1548).
- `mem_spectrum_iff_hasEigenvalue_above_half : 1/2 < μ → (μ ∈ spectrum ℝ resolvent ↔ Module.End.HasEigenvalue ↑resolvent μ)`.
- `finite_eigenvalues_above (hε) : {μ | 1/2 + ε ≤ μ ∧ HasEigenvalue ↑resolvent μ}.Finite`
  (orthogonalFamily_eigenspaces + `isCompact_Icc.tendsto_subseq` + MUST-1548).
- `finiteDimensional_eigenspace_above_half` (Hilbert basis of the closed eigenspace; infinite ⇒ orthonormal ℕ-family ⇒ contradiction).

## Spectral picture of the arithmetic resolvent R (all in Lean now)
σ(R) ⊆ [0,1]; Weyl/essential spectrum ⊆ [0,1/2] with 1/2 attained (cusp escape, MUST-1544/1546); σ(R) ∩ (1/2,1] = pure point,
finite multiplicities, finitely many above 1/2+ε. CHMD dictionary: RH ⟺ R ≤ 1/2 on even primitives, so off-line zeros = bound
states. Next: Birman–Schwinger count vs nonreal Xi orbits; even-sector dictionary in Lean (⇒ exists: `weilOperator_isPositive_of_riemannHypothesis`).

## Lean traps
- `Module.End.HasEigenvalue` must be written fully qualified for `(T : E →ₗ[ℝ] E)` (dot notation `.HasEigenvalue` fails).
- `Module.End.mem_eigenspace_iff` yields `↑T x = μ • x` (coe to linear map); convert with `rw [ContinuousLinearMap.coe_coe]`.
- `ContinuousLinearMap.sub_apply/smul_apply/one_apply` deprecated → root `sub_apply`, `smul_apply`, `one_apply_eq_self`.
- `Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩`; `LinearIsometry.orthonormal_comp_iff` needs `(v := …)`.
- `isClosed_eq T.continuous (continuous_id.const_smul μ)` for eigenspaces.
