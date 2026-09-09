import GaloisForLFunctions.RHTower.SelbergScatteringEntireEigenvectors

/-!
# Nonvanishing of the fixed corrected source's entire residual

The full corrected source has a nonzero closed-cell value strictly below the
cutoff transition, where its retained forcing vanishes. Continuity and actual
Hilbert representatives therefore rule out scalar proportionality of forcing
and source, and hence every native eigen-equation for this source. The exact
entire spectral-fibre classification then proves that its entire residual,
including its actual unit normalization, never vanishes at any Xi copy.

This excludes exact occurrence from this fixed corrected source. It does not
exclude other vectors, approximate source families, or the SQB interface.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringSourceNonvanishing
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
open SelbergScatteringCuspSubtraction SelbergScatteringSourceVector SelbergScatteringSourceGraph
open SelbergScatteringNativeResidual
noncomputable section

/-- The original corrected source is nonzero on the closed cell strictly below
the transition forcing, retaining the complete original scalar field there. -/
theorem globalResidual_nonzero_below_transition (q : XiZeroCopy) :
    ∃ z : UpperHalfPlane, z ∈ fd ∧ z.im<2 ∧ globalResidual q z≠0 := by
  obtain ⟨x,hx⟩ := SelbergScatteringHeightConjugation.scalarSource_xi_nonzero_on_every_height q (3/2) (by norm_num)
  let z : UpperHalfPlane := ⟨⟨x,3/2⟩,by norm_num⟩
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hy := modular_orbit_height_le (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hy
  have hlow : (A • z).im<2 := by
    change (A • z).im ≤ max (3/2:ℝ) (1/(3/2:ℝ)) at hy
    exact lt_of_le_of_lt hy (by norm_num)
  refine ⟨A • z,hA,hlow,?_⟩
  rw [globalResidual_eq_on_fd q _ hA,residual_low q _ hlow.le,physicalScalar_modular]
  exact hx

private theorem forcing_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => cutoffForcing q (coordinates z)) := by
  have hc : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have h := (continuous_const (y := reflectedCompletedLambda ((q.1:ℂ)-1))).mul
    ((cutoffCommutator_continuousOn (1-(q.1:ℂ)/2)).comp_continuous hc (fun z => z.im_pos))
  apply h.congr
  intro z
  exact (SelbergScatteringCutoffForcing.cutoffForcing_eq_commutator q _ z.im_pos).symm

/-- The complete original forcing is not a scalar multiple of the original
corrected source in the native Hilbert space. -/
theorem forcingVector_ne_smul_source (q : XiZeroCopy) (c : ℂ) :
    SelbergScatteringCutoffForcing.forcingVector q ≠ c • sourceVector q := by
  intro he
  have hfield : (fun z => cutoffForcing q (coordinates z)) =ᵐ[measure]
      (fun z => c*globalResidual q z) := by
    filter_upwards [SelbergScatteringCutoffForcing.forcingVector_coe q,sourceVector_coe q,
      Lp.coeFn_smul c (sourceVector q)] with z hH hV hc
    rw [he] at hH
    simp only [Pi.smul_apply,smul_eq_mul] at hc
    rw [← hH,hc,hV]
  change (fun z => cutoffForcing q (coordinates z)) =ᵐ[volume.restrict fd]
    (fun z => c*globalResidual q z) at hfield
  have hclosure : fd ⊆ closure (interior fd) := by
    rw [← fdo_eq_interior_fd,← fd_eq_closure_fdo]
  have hpoint := Measure.eqOn_of_ae_eq hfield (forcing_continuous q).continuousOn
    (continuous_const.mul (globalResidual_smooth q).continuous).continuousOn hclosure
  obtain ⟨z,hz,hy,hn⟩ := globalResidual_nonzero_below_transition q
  have h := hpoint hz
  change cutoffForcing q (coordinates z)=c*globalResidual q z at h
  rw [cutoffForcing_low q (coordinates z) hy] at h
  have hc : c=0 := (mul_eq_zero.mp h.symm).resolve_right hn
  apply SelbergScatteringCutoffForcing.forcingVector_ne_zero q
  rw [he,hc,zero_smul]

/-- The original corrected source cannot be a native eigenvector at any complex
parameter: its retained forcing is genuinely independent of its source vector. -/
theorem sourceNativeDomain_not_eigen (q : XiZeroCopy) (lam : ℂ) :
    energyOperator (sourceNativeDomain q) ≠ lam • sourceVector q := by
  intro he
  apply forcingVector_ne_smul_source q (lam-scatteringEnergy (q.1:ℂ))
  rw [← sourceNativeDomain_equation,he,sub_smul]
  rfl

open SelbergScatteringEntireOperator SelbergScatteringEntireEigenvectors
open SelbergScatteringEntireXiPackets SelbergScatteringForcingTransport

/-- The fixed complete corrected source has nonzero entire residual at every
actual Xi copy, including critical copies. This is a source-specific obstruction. -/
theorem sourceResidual_ne_zero (q : XiZeroCopy) : sourceResidual q≠0 := by
  intro hz
  have h := (covariance_residual_zero_iff q (sourceVector q)).mp hz
  rcases h with h0 | ⟨_,hEig⟩
  · exact sourceVector_ne_zero q h0
  · have hNative := (covariance_native_eigenvector_iff q (sourceNativeDomain q)).mp hEig
    exact sourceNativeDomain_not_eigen q (xiNativeEigenvalue q) hNative

/-- Exact forcing transport does not annihilate the original cutoff forcing. -/
theorem entireForcingTransport_original_ne_zero (q : XiZeroCopy) :
    entireForcingTransport q (SelbergScatteringCutoffForcing.forcingVector q)≠0 := by
  rw [← sourceResidual_eq_transported_forcing]
  exact sourceResidual_ne_zero q

/-- The actual normalized fixed source has strictly positive entire residual
at every full Xi parameter. No uniform bound over varying sources is asserted. -/
theorem sourceUnitVector_residual_pos (q : XiZeroCopy) :
    0 < ‖entireOperator (sourceUnitVector q) - xiEntireTarget q • (sourceUnitVector q : Space)‖ := by
  rw [sourceUnitVector_residual_norm]
  exact mul_pos (inv_pos.mpr (sourceCovariance_norm_pos q)) (norm_pos_iff.mpr (sourceResidual_ne_zero q))

end
end RHTower.SelbergScatteringSourceNonvanishing
