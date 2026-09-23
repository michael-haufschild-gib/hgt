import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralPeierlsPhysicalFrequency
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedQuadraticClosure

/-!
# Literal two-leg cyclic Peierls contact carrier

The physical bulk field is already polarized in its two primary amplitudes,
whereas the actual mixed contact was previously available only on the diagonal.
This leaf gives its literal polarization and joins both actual exterior fields.
It does not assert a causal boundary condition or a cap/contact equality.

Proof-chain role:
`two-leg bulk field + two-leg actual contact -> bilinear physical current ->
literal cap/contact boundary transport -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsContactBilinear

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMFundamentalScalarMetric D4BMModularCore D4BMMetricReconstruction
open D4BMLiteralPeierlsStream D4BMMixedQuadraticClosure

noncomputable section
set_option autoImplicit false

/-- The full two-leg exterior correction, retaining both the causal bulk
response and the actual mixed contact. -/
def completedMetricBilinear (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  forcedMetricBilinear q branch a d x + contactFieldBilinear q branch a d x

private theorem streamMetricField_amplitude (w z : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    streamMetricField w z square V x = z • streamMetricField w 1 square V x := by
  cases square <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [streamMetricField,streamTimeBlock,streamRadiusBlock,streamRadialField,
      streamRadialDerivative,D4BMFundamentalScalarMetric.envelope,smul_eq_mul]
  all_goals ring

/-- The forced two-leg Peierls stream is exactly the product polarization of
the original physical forced field. -/
theorem forcedMetricBilinear_eq_product (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) :
    forcedMetricBilinear q branch a d x = (a*d) • forcedMetricField q branch 1 x := by
  unfold forcedMetricBilinear
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,streamMetricBilinear,
    LinearMap.mk₂_apply,Pi.sub_apply,Pi.smul_apply]
  rw [streamMetricField_amplitude (2 * physicalRate q branch) (a * d) false
      (fullAngularCovector q branch) x,
    streamMetricField_amplitude (2 * physicalRate q branch) (a * d) true
      (fullSquareCovector q) x]
  ext i j
  simp [forcedMetricField,smul_eq_mul]
  ring

/-- Every independent two-leg bulk component has an actual coordinate two-jet. -/
theorem forcedMetricBilinear_smooth (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => forcedMetricBilinear q branch a d x i j) p.val := by
  have hresponse (k : Fin 2) :
      ContDiffAt ℝ 2 (fullAngularCovector q branch k) (angularPoint p.val) := by
    have h := (contDiffAt_infty.mp
      (fullAngularCovector_smooth q branch (angularPoint p.val) p.property.2 k)) 2
    norm_num at h
    exact h
  have hsquare (k : Fin 2) :
      ContDiffAt ℝ 2 (fullSquareCovector q k) (angularPoint p.val) := by
    simpa using fullSquareCovector_smooth q (angularPoint p.val) p.property.2 2 k
  change ContDiffAt ℝ 2 (fun x =>
    streamMetricField (2*physicalRate q branch) (a*d) false (fullAngularCovector q branch) x i j-
      (physicalRate q branch*(physicalRate q branch-1)/4)*
        streamMetricField (2*physicalRate q branch) (a*d) true (fullSquareCovector q) x i j) p.val
  exact (streamMetricField_smooth _ _ false _ p hresponse i j).sub
    (contDiffAt_const.mul (streamMetricField_smooth _ _ true _ p hsquare i j))

/-- The complete two-leg correction is an actual exterior two-jet, not a
formal polarization of supplied jets. -/
theorem completedMetricBilinear_smooth (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => completedMetricBilinear q branch a d x i j) p.val :=
  (forcedMetricBilinear_smooth q branch a d p i j).add
    (contactFieldBilinear_smooth q branch a d p i j)

/-- The completed two-leg correction is cyclic in its independent physical legs. -/
theorem completedMetricBilinear_symm (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) :
    completedMetricBilinear q branch a d x = completedMetricBilinear q branch d a x := by
  unfold completedMetricBilinear
  rw [forcedMetricBilinear_symm,contactFieldBilinear_symm]

/-- On the diagonal, the literal two-leg correction is exactly the existing
actual mixed quadratic field. -/
theorem completedMetricBilinear_diag (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (x : Fin 4 → ℝ) :
    completedMetricBilinear q branch a a x = mixedField q branch a x := by
  unfold completedMetricBilinear
  rw [forcedMetricBilinear_diag,contactFieldBilinear_diag]
  ext i j
  simp [mixedField,forcedMetricField]

/-- The completed literal two-leg correction is not a new ansatz: it is
exactly the independent-amplitude polarization of the established physical
mixed correction. -/
theorem completedMetricBilinear_eq_independentField (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (x : Fin 4 → ℝ) :
    completedMetricBilinear q branch a d x = independentField q branch a d x := by
  unfold completedMetricBilinear independentField mixedField
  rw [forcedMetricBilinear_eq_product,contactFieldBilinear_eq_product]
  ext i j
  simp [smul_eq_mul]
  ring

/-- The literal cyclic Peierls two-leg metric, including its actual contact,
solves the established physical mixed Einstein equation for independent
amplitudes.  This closes the bulk realization; causal and noncompact boundary
transport remain separate B2 obligations. -/
theorem completedMetricBilinear_secondVariation (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    D4BMWeightedCorrectionDiscrepancy.linear p i j
      (ComplexCoordinateMetricTwoJet.toSpace (ofMetricField (completedMetricBilinear q branch a d) p.val)) +
      ComplexCoordinateMetricTwoJet.secondVariation
        (D4BMActualMetricSource.backgroundSpace p) i j
        (a • D4BMWeightedCorrectionDiscrepancy.mode p q branch 1 0)
        (d • D4BMWeightedCorrectionDiscrepancy.mode p q branch 0 1) = 0 := by
  have hfield : completedMetricBilinear q branch a d = independentField q branch a d := by
    funext x
    exact completedMetricBilinear_eq_independentField q branch a d x
  rw [hfield]
  exact independentField_secondVariation q branch a d p i j

end

end RHTower.D4BMLiteralCyclicPeierlsContactBilinear
