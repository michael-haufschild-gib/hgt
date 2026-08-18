import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVGreenStokesConservation
import GaloisForLFunctions.RHTower.FrankensteinCCMGammaWoldCubicJuliaOrbitDescent

/-!
# BV endpoint third-jet descent through a selected Krein residue

This module identifies the literal finite Wold--Julia Xi orbit with the third jet at zero of the
proved BV Green--Stokes endpoint defect.  The identity is exact at every finite prime clock and
cancels all dependence on the strict-right horizontal coordinate.

The completed CCM/Gamma source is kept complex until its second selected residue.  It is paired
with a coefficient-faithful endpoint ghost in a signed two-channel block.  The selected landing is
self-adjoint, trace-free, and indefinite.  Multiplication by the self-adjoint involution
`J = diag(1,-1)` produces an ordinary positive-definite block cofinally in the source clock, for
every retained Xi copy and every nonzero coefficient.

No Loewner domination, primitive Euler budget inequality, or Riemann-hypothesis consequence is
claimed here.  The construction isolates a signed selected-fibre descent which avoids the known
global continuous-order firewall.
-/

open Complex Matrix Filter Set Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

def sourceHorizontalWoldBVGreenStokesEndpointDefect
    (N : ℕ) (u : ℝ) : ℝ :=
  Real.sinh u - sourceHorizontalWoldBVGreenStokesInteriorCurrent N u

def sourceHorizontalWoldBVGreenStokesEndpointThirdJet
    (N : ℕ) : ℝ :=
  -(sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
    xiMassNthPrimeLogHeight N ^ 3)

theorem sourceHorizontalWoldBVGreenStokesEndpointDefect_eq_neg_profile
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldBVGreenStokesEndpointDefect N u =
      -sourceHorizontalWoldPrimeClockProfileSeries N u := by
  rw [sourceHorizontalWoldBVGreenStokesEndpointDefect,
    sourceHorizontalWoldBVGreenStokes_finite_conservation]
  ring

theorem sourceHorizontalWoldPrimeClockProfileSeries_eq_residual_add_linear
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldPrimeClockProfileSeries N u =
      sourceHorizontalWoldResidualPrimitiveDeformation N
          (u / xiMassNthPrimeLogHeight N) +
        xiHeatCassiniWoldLogHolonomyConstant *
          (u / xiMassNthPrimeLogHeight N) := by
  rw [sourceHorizontalWoldPrimeClockProfileSeries_eq_finiteDeformation,
    sourceHorizontalWoldResidualPrimitiveDeformation_primeClock]
  ring

theorem contDiff_sourceHorizontalWoldResidualPrimitiveDeformation_three
    (N : ℕ) :
    ContDiff ℝ 3 (sourceHorizontalWoldResidualPrimitiveDeformation N) := by
  unfold sourceHorizontalWoldResidualPrimitiveDeformation
  apply ContDiff.sub
  · apply ContDiff.sub
    · exact ContDiff.sum fun n _ =>
        contDiff_sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype n) 3
    · exact contDiff_sourceHorizontalTerminalPrimeHolonomyDeformation N 3
  · fun_prop

theorem iteratedDeriv_sourceHorizontalWoldPrimeClockProfileSeries_three
    (N : ℕ) :
    iteratedDeriv 3 (sourceHorizontalWoldPrimeClockProfileSeries N) 0 =
      sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
        xiMassNthPrimeLogHeight N ^ 3 := by
  let H := xiMassNthPrimeLogHeight N
  let R := sourceHorizontalWoldResidualPrimitiveDeformation N
  let L := xiHeatCassiniWoldLogHolonomyConstant
  have hH : H ≠ 0 := by
    exact (xiMassNthPrimeLogHeight_pos N).ne'
  have hfun : sourceHorizontalWoldPrimeClockProfileSeries N =
      fun u : ℝ => R (H⁻¹ * u) + L * (H⁻¹ * u) := by
    funext u
    rw [sourceHorizontalWoldPrimeClockProfileSeries_eq_residual_add_linear]
    simp only [R, H, L]
    field_simp [hH]
  rw [hfun]
  have hR : ContDiff ℝ 3 R := by
    exact contDiff_sourceHorizontalWoldResidualPrimitiveDeformation_three N
  have hRcomp : ContDiffAt ℝ 3 (fun u : ℝ => R (H⁻¹ * u)) 0 := by
    fun_prop
  have hlinear : ContDiffAt ℝ 3 (fun u : ℝ => L * (H⁻¹ * u)) 0 := by
    fun_prop
  rw [iteratedDeriv_fun_add hRcomp hlinear]
  have hcomp := congrFun (iteratedDeriv_comp_const_mul hR H⁻¹) 0
  simp only [mul_zero] at hcomp
  rw [hcomp, iteratedDeriv_sourceHorizontalWoldResidualPrimitiveDeformation_three]
  have hlinearThird :
      iteratedDeriv 3 (fun u : ℝ => L * (H⁻¹ * u)) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id]
  rw [hlinearThird, add_zero]
  dsimp only [H]
  field_simp [hH]

theorem iteratedDeriv_sourceHorizontalWoldBVGreenStokesEndpointDefect_three
    (N : ℕ) :
    iteratedDeriv 3
        (sourceHorizontalWoldBVGreenStokesEndpointDefect N) 0 =
      sourceHorizontalWoldBVGreenStokesEndpointThirdJet N := by
  have hfun : sourceHorizontalWoldBVGreenStokesEndpointDefect N =
      fun u : ℝ => -sourceHorizontalWoldPrimeClockProfileSeries N u := by
    funext u
    exact sourceHorizontalWoldBVGreenStokesEndpointDefect_eq_neg_profile N u
  rw [hfun]
  have hneg :
      (fun u : ℝ => -sourceHorizontalWoldPrimeClockProfileSeries N u) =
        (fun u : ℝ => (-1 : ℝ) *
          sourceHorizontalWoldPrimeClockProfileSeries N u) := by
    funext u
    ring
  rw [hneg]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_sourceHorizontalWoldPrimeClockProfileSeries_three]
  simp [sourceHorizontalWoldBVGreenStokesEndpointThirdJet]

/-- The finite endpoint third jet converges to the positive universal value `2/3`. -/
theorem tendsto_sourceHorizontalWoldBVGreenStokesEndpointThirdJet :
    Tendsto sourceHorizontalWoldBVGreenStokesEndpointThirdJet atTop
      (nhds (2 / 3 : ℝ)) := by
  change Tendsto (fun N : ℕ =>
    -(sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ 3)) atTop (nhds (2 / 3 : ℝ))
  have h :=
    tendsto_sourceHorizontalWoldResidualPrimitiveCubicCoefficient_normalized.neg
  convert h using 1
  norm_num

/-- The endpoint third jet is eventually strictly positive. -/
theorem eventually_sourceHorizontalWoldBVGreenStokesEndpointThirdJet_pos :
    ∀ᶠ N in atTop,
      0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N := by
  exact
    tendsto_sourceHorizontalWoldBVGreenStokesEndpointThirdJet.eventually_const_lt
      (by norm_num)

/-- Exact finite-clock cancellation: the Xi orbit is the coefficient energy times the BV
endpoint third jet, with no residual dependence on the strict-right horizontal coordinate. -/
theorem sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N =
      8 * Complex.normSq c *
        sourceHorizontalWoldBVGreenStokesEndpointThirdJet N := by
  rw [sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse,
    sourceZeroHorizontalWoldRegularizedRoutePConormalResponse,
    sourceZeroHorizontalWoldPrimeClockCubicResponse,
    sourceHorizontalWoldBVGreenStokesEndpointThirdJet,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re]
  have ha : (xiRightCenteredZero q).re ≠ 0 :=
    (xiRightCenteredZero_re_pos q).ne'
  field_simp [ha]
  ring

/-- Positive-channel scalar carried by the BV endpoint third jet. -/
def sourceHorizontalWoldBVKreinGhostEnergy
    (c : ℂ) (N : ℕ) : ℝ :=
  8 * Complex.normSq c *
    sourceHorizontalWoldBVGreenStokesEndpointThirdJet N

/-- Complex pre-residue descent.  Unlike the older physical readout, this retains the signed
complex source landing until selection; no real-part projection is inserted. -/
def frankensteinCCMGammaWoldBVKreinComplexFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) : ℂ :=
  ((4 * Complex.normSq c : ℝ) : ℂ) *
    (-(frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N v) *
      ((1 / (4 * (xiRightCenteredZero q).re ^ 3) : ℝ) : ℂ))

/-- The selected complex residue is exactly the finite BV ghost energy. -/
theorem tendsto_frankensteinCCMGammaWoldBVKreinComplexFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (frankensteinCCMGammaWoldBVKreinComplexFirstLanding c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)) := by
  have h :=
    (tendsto_frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N).neg
  have hreg := h.mul_const
    ((1 / (4 * (xiRightCenteredZero q).re ^ 3) : ℝ) : ℂ)
  have horbit := hreg.const_mul ((4 * Complex.normSq c : ℝ) : ℂ)
  have heq :
      ((4 * Complex.normSq c : ℝ) : ℂ) *
          (-(sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N : ℂ) *
            ((1 / (4 * (xiRightCenteredZero q).re ^ 3) : ℝ) : ℂ)) =
        (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) := by
    norm_cast
    simpa [sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse,
      sourceZeroHorizontalWoldRegularizedRoutePConormalResponse,
      sourceHorizontalWoldBVKreinGhostEnergy] using
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet
          c q N
  rw [← heq]
  exact horbit

/-- Signed pre-residue block: first channel is genuine CCM/Gamma source data, while the second is
the coefficient-faithful BV endpoint ghost. -/
def frankensteinCCMGammaWoldBVKreinSignedSourceBlock
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![frankensteinCCMGammaWoldBVKreinComplexFirstLanding c q N v, 0;
    0, -(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)]

/-- Selected signed landing. -/
def sourceHorizontalWoldBVKreinSignedLanding
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ), 0;
    0, -(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)]

/-- Fundamental symmetry distinguishing physical and ghost channels. -/
def sourceHorizontalWoldBVKreinFundamentalSymmetry :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Xi-selected physical landing obtained by the Krein rotation `J K`. -/
def sourceHorizontalWoldBVKreinPhysicalLanding
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sourceHorizontalWoldBVKreinFundamentalSymmetry *
    sourceHorizontalWoldBVKreinSignedLanding c N

/-- Physical source block before second residue.  Its first diagonal entry is still complex source
data; positivity is not asserted before the Xi-selected landing. -/
def frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  sourceHorizontalWoldBVKreinFundamentalSymmetry *
    frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N v

/-- The fundamental symmetry is an involution. -/
@[simp] theorem sourceHorizontalWoldBVKreinFundamentalSymmetry_sq :
    sourceHorizontalWoldBVKreinFundamentalSymmetry *
      sourceHorizontalWoldBVKreinFundamentalSymmetry = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalWoldBVKreinFundamentalSymmetry,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The fundamental symmetry is self-adjoint. -/
theorem sourceHorizontalWoldBVKreinFundamentalSymmetry_isHermitian :
    sourceHorizontalWoldBVKreinFundamentalSymmetry.IsHermitian := by
  change star sourceHorizontalWoldBVKreinFundamentalSymmetry =
    sourceHorizontalWoldBVKreinFundamentalSymmetry
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalWoldBVKreinFundamentalSymmetry, Matrix.star_apply]

/-- Selected signed landing is self-adjoint even though it is indefinite when its scale is
positive. -/
theorem sourceHorizontalWoldBVKreinSignedLanding_isHermitian
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalWoldBVKreinSignedLanding c N).IsHermitian := by
  change star (sourceHorizontalWoldBVKreinSignedLanding c N) =
    sourceHorizontalWoldBVKreinSignedLanding c N
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalWoldBVKreinSignedLanding, Matrix.star_apply]

/-- Entrywise selected-residue convergence of the signed source block. -/
theorem tendsto_frankensteinCCMGammaWoldBVKreinSignedSourceBlock
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalWoldBVKreinSignedLanding c N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinSignedLanding] using
      tendsto_frankensteinCCMGammaWoldBVKreinComplexFirstLanding c q N
  · simp [frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinSignedLanding]
  · simp [frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinSignedLanding]
  · simp [frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinSignedLanding]

/-- The same selected residue commutes with the Krein rotation and lands in the physical block. -/
theorem tendsto_frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalWoldBVKreinPhysicalLanding c N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock,
      sourceHorizontalWoldBVKreinFundamentalSymmetry,
      frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinPhysicalLanding,
      sourceHorizontalWoldBVKreinSignedLanding,
      Matrix.mul_apply, Fin.sum_univ_two] using
      tendsto_frankensteinCCMGammaWoldBVKreinComplexFirstLanding c q N
  · simp [frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock,
      sourceHorizontalWoldBVKreinFundamentalSymmetry,
      frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinPhysicalLanding,
      sourceHorizontalWoldBVKreinSignedLanding,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock,
      sourceHorizontalWoldBVKreinFundamentalSymmetry,
      frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinPhysicalLanding,
      sourceHorizontalWoldBVKreinSignedLanding,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [frankensteinCCMGammaWoldBVKreinPhysicalSourceBlock,
      sourceHorizontalWoldBVKreinFundamentalSymmetry,
      frankensteinCCMGammaWoldBVKreinSignedSourceBlock,
      sourceHorizontalWoldBVKreinPhysicalLanding,
      sourceHorizontalWoldBVKreinSignedLanding,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Signed selected landing conserves trace exactly. -/
@[simp] theorem sourceHorizontalWoldBVKreinSignedLanding_trace
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalWoldBVKreinSignedLanding c N).trace = 0 := by
  simp [sourceHorizontalWoldBVKreinSignedLanding, Matrix.trace,
    Fin.sum_univ_two]

/-- Krein rotation turns the signed landing into two equal physical channels. -/
theorem sourceHorizontalWoldBVKreinPhysicalLanding_eq
    (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldBVKreinPhysicalLanding c N =
      !![(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ), 0;
        0, (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalWoldBVKreinPhysicalLanding,
      sourceHorizontalWoldBVKreinFundamentalSymmetry,
      sourceHorizontalWoldBVKreinSignedLanding,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- After Xi selection, nonnegative endpoint ghost energy gives an ordinary positive operator. -/
theorem sourceHorizontalWoldBVKreinPhysicalLanding_posSemidef
    (c : ℂ) (N : ℕ)
    (hghost : 0 ≤ sourceHorizontalWoldBVKreinGhostEnergy c N) :
    (sourceHorizontalWoldBVKreinPhysicalLanding c N).PosSemidef := by
  rw [sourceHorizontalWoldBVKreinPhysicalLanding_eq]
  have hdiag :
      !![(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ), 0;
        0, (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)] =
        Matrix.diagonal (fun _ : Fin 2 =>
          (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hdiag]
  apply Matrix.PosSemidef.diagonal
  change ∀ _ : Fin 2, (0 : ℂ) ≤
    (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)
  intro i
  exact_mod_cast hghost

/-- Positivity of the selected physical block is exactly positivity of the source-derived endpoint
ghost; no independent Loewner assumption remains. -/
theorem sourceHorizontalWoldBVKreinPhysicalLanding_posSemidef_iff
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalWoldBVKreinPhysicalLanding c N).PosSemidef ↔
      0 ≤ sourceHorizontalWoldBVKreinGhostEnergy c N := by
  constructor
  · intro hpos
    have hdiag := hpos.diag_nonneg (i := (0 : Fin 2))
    rw [sourceHorizontalWoldBVKreinPhysicalLanding_eq] at hdiag
    simp at hdiag
    exact_mod_cast hdiag
  · exact sourceHorizontalWoldBVKreinPhysicalLanding_posSemidef c N

/-- With nonzero coefficient and positive endpoint third jet, the selected physical block is
positive definite. -/
theorem sourceHorizontalWoldBVKreinPhysicalLanding_posDef
    (c : ℂ) (N : ℕ) (hc : c ≠ 0)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    (sourceHorizontalWoldBVKreinPhysicalLanding c N).PosDef := by
  rw [sourceHorizontalWoldBVKreinPhysicalLanding_eq]
  have hdiag :
      !![(sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ), 0;
        0, (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)] =
        Matrix.diagonal (fun _ : Fin 2 =>
          (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hdiag]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hc)) hjet

/-- Before the fundamental-symmetry rotation, a strictly positive ghost energy forces an
indefinite signed landing. -/
theorem sourceHorizontalWoldBVKreinSignedLanding_not_posSemidef
    (c : ℂ) (N : ℕ)
    (hghost : 0 < sourceHorizontalWoldBVKreinGhostEnergy c N) :
    ¬ (sourceHorizontalWoldBVKreinSignedLanding c N).PosSemidef := by
  intro hpos
  have hdiag := hpos.diag_nonneg (i := (1 : Fin 2))
  simp [sourceHorizontalWoldBVKreinSignedLanding] at hdiag
  have hreal : sourceHorizontalWoldBVKreinGhostEnergy c N ≤ 0 := by
    exact_mod_cast hdiag
  linarith

/-- Strictly positive ghost energy prevents ordinary Loewner positivity at every pre-residue
source point.  Positivity is therefore not a continuous global structure secretly imposed before
Xi selection. -/
theorem frankensteinCCMGammaWoldBVKreinSignedSourceBlock_not_posSemidef
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ)
    (hghost : 0 < sourceHorizontalWoldBVKreinGhostEnergy c N) :
    ¬ (frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N v).PosSemidef := by
  intro hpos
  have hdiag := hpos.diag_nonneg (i := (1 : Fin 2))
  simp [frankensteinCCMGammaWoldBVKreinSignedSourceBlock] at hdiag
  have hreal : sourceHorizontalWoldBVKreinGhostEnergy c N ≤ 0 := by
    exact_mod_cast hdiag
  linarith

/-- For each retained Xi copy and nonzero coefficient, cofinally many source clocks exhibit the
full selected-residue phase change: signed landing is indefinite while its physical `J`-rotation
is positive definite.  The residue convergence remains attached to that exact Xi copy. -/
theorem eventually_frankensteinCCMGammaWoldBVKrein_selectedResidue_phaseChange
    (c : ℂ) (q : XiRightZeroCopy) (hc : c ≠ 0) :
    ∀ᶠ N in atTop,
      (¬ (sourceHorizontalWoldBVKreinSignedLanding c N).PosSemidef) ∧
      (sourceHorizontalWoldBVKreinPhysicalLanding c N).PosDef ∧
      Tendsto (frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N)
        (nhdsWithin
          (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
          ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
        (nhds (sourceHorizontalWoldBVKreinSignedLanding c N)) := by
  filter_upwards
    [eventually_sourceHorizontalWoldBVGreenStokesEndpointThirdJet_pos]
      with N hjet
  have hghost : 0 < sourceHorizontalWoldBVKreinGhostEnergy c N := by
    exact mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hc)) hjet
  exact ⟨sourceHorizontalWoldBVKreinSignedLanding_not_posSemidef c N hghost,
    sourceHorizontalWoldBVKreinPhysicalLanding_posDef c N hc hjet,
    tendsto_frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N⟩

end

end RHTower
