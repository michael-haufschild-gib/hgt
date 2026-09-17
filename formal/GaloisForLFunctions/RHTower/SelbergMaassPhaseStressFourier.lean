import GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
import GaloisForLFunctions.RHTower.MaassCuspSmoothness
import GaloisForLFunctions.RHTower.PeriodicFourierDecay
import GaloisForLFunctions.HTGeometry.KleinGordonEigenEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier expansion of the unresolved mixed phase-stress boundary term

The physical mixed phase stress in the source Rellich boundary term is a genuine smooth,
unit-periodic function.  This file transfers the elliptic smoothness of the actual Maass source
through every finite source readout and stress operation, then applies the existing periodic
Fourier inversion theorem to that exact source-attached boundary slice.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseStressFourier
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassCharacterDynamics SelbergMaassCharacterSeamFlux SelbergMaassDilationStress
open SelbergMaassPhaseRellich SelbergMaassMixedLoss SelbergMaassTraceEnergy SelbergMaassPhaseStress
open SelbergMaassMean SelbergScalarHorizontalAverage
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The complete finite source vector is smooth on the physical upper half-plane. -/
theorem sourceVector_contDiffOn_infty :
    ContDiffOn ℝ ∞ (fun z : ℂ => sourceVector N f (ofComplex z)) {z : ℂ | 0 < z.im} := by
  apply (contDiffOn_piLp 2).mpr
  intro q
  exact (quotientForm N f q).contDiffOn

/-- Every fixed linear readout of the complete source is smooth. -/
theorem readout_contDiffOn_infty (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => L (sourceVector N f (ofComplex z))) {z : ℂ | 0 < z.im} :=
  (L.restrictScalars ℝ).contDiff.comp_contDiffOn (sourceVector_contDiffOn_infty N f)

/-- The mixed physical stress of every actual source readout is smooth. -/
theorem stressXY_contDiffOn_infty (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    ContDiffOn ℝ ∞ (stressXY N f L) {w : ℂ | 0 < w.im} := by
  have hobs := readout_contDiffOn_infty N f L
  have hx := dir_contDiffOn hobs (m := ∞) (by simp) (1 : ℂ)
  have hy := dir_contDiffOn hobs (m := ∞) (by simp) Complex.I
  exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
    (hx.mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hy)))

variable (r s : ZMod (N+1))

/-- The complete source-attached mixed phase stress is smooth, including source zeros. -/
theorem phaseStressXY_contDiffOn_infty :
    ContDiffOn ℝ ∞ (phaseStressXY N r s f) {w : ℂ | 0 < w.im} := by
  unfold phaseStressXY phaseAverage
  exact contDiffOn_const.mul (ContDiffOn.sum fun i _ =>
    stressXY_contDiffOn_infty N f (phaseReadout N r s i))

private theorem phaseStressXY_complex_contDiffOn_infty :
    ContDiffOn ℝ ∞ (fun w : ℂ => (phaseStressXY N r s f w : ℂ)) {w : ℂ | 0 < w.im} :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (phaseStressXY_contDiffOn_infty N f r s)

private theorem phaseStressXY_complex_dir_contDiffOn_infty :
    ContDiffOn ℝ ∞ (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ)))
      {w : ℂ | 0 < w.im} :=
  directional_contDiffOn (phaseStressXY_complex_contDiffOn_infty N f r s) (m := ∞) (by simp) 1

private theorem phaseStressXY_complex_second_dir_contDiffOn_infty :
    ContDiffOn ℝ ∞ (directional 1 (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ))))
      {w : ℂ | 0 < w.im} :=
  directional_contDiffOn (phaseStressXY_complex_dir_contDiffOn_infty N f r s) (m := ∞) (by simp) 1

/-- The literal complexified unresolved mixed boundary density at height one. -/
def phaseStressXYHorizontal (x : ℝ) : ℂ := (phaseStressXY N r s f (point x 1) : ℂ)

/-- Its first physical horizontal derivative. -/
def phaseStressXYHorizontalDeriv (x : ℝ) : ℂ :=
  directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ)) (point x 1)

/-- Its second physical horizontal derivative. -/
def phaseStressXYHorizontalSecondDeriv (x : ℝ) : ℂ :=
  directional 1 (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ))) (point x 1)

private theorem phaseStressXYHorizontal_hasDerivAt (x : ℝ) :
    HasDerivAt (phaseStressXYHorizontal N f r s) (phaseStressXYHorizontalDeriv N f r s x) x := by
  change HasDerivAt (fun t => (phaseStressXY N r s f (point t 1) : ℂ))
    (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ)) (point x 1)) x
  exact slice_horizontal ((phaseStressXY_complex_contDiffOn_infty N f r s).of_le (by simp))
    zero_lt_one x

private theorem phaseStressXYHorizontalDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt (phaseStressXYHorizontalDeriv N f r s)
      (phaseStressXYHorizontalSecondDeriv N f r s x) x := by
  change HasDerivAt (fun t => directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ)) (point t 1))
    (directional 1 (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ))) (point x 1)) x
  exact slice_horizontal ((phaseStressXY_complex_dir_contDiffOn_infty N f r s).of_le (by simp))
    zero_lt_one x

private theorem phaseStressXYHorizontalDeriv_continuous :
    Continuous (phaseStressXYHorizontalDeriv N f r s) := by
  change Continuous (fun x => directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ)) (point x 1))
  exact slice_continuous (phaseStressXY_complex_dir_contDiffOn_infty N f r s).continuousOn zero_lt_one

private theorem phaseStressXYHorizontalSecondDeriv_continuous :
    Continuous (phaseStressXYHorizontalSecondDeriv N f r s) := by
  change Continuous (fun x => directional 1 (directional 1 (fun w : ℂ => (phaseStressXY N r s f w : ℂ))) (point x 1))
  exact slice_continuous (phaseStressXY_complex_second_dir_contDiffOn_infty N f r s).continuousOn zero_lt_one

private theorem phaseStressXYHorizontal_periodic : Function.Periodic (phaseStressXYHorizontal N f r s) 1 := by
  intro x
  have h := phaseStressXY_translation N r s f (ofComplex (point x 1))
  rw [SelbergMaassTraceBoundary.translation_point x zero_lt_one] at h
  simpa only [phaseStressXYHorizontal, SelbergMaassUnipotentPaths.coe_ofComplex_point _ zero_lt_one]
    using congrArg (fun u : ℝ => (u : ℂ)) h

private theorem phaseStressXYHorizontalDeriv_periodic :
    Function.Periodic (phaseStressXYHorizontalDeriv N f r s) 1 := by
  intro x
  simpa only [phaseStressXYHorizontalDeriv] using
    (directional_periodic ((phaseStressXY_complex_contDiffOn_infty N f r s).of_le (by simp))
      zero_lt_one 1 (fun t => phaseStressXYHorizontal_periodic N f r s t) x)

private theorem phaseStressXYHorizontalSecondDeriv_periodic :
    Function.Periodic (phaseStressXYHorizontalSecondDeriv N f r s) 1 := by
  intro x
  simpa only [phaseStressXYHorizontalSecondDeriv] using
    (directional_periodic ((phaseStressXY_complex_dir_contDiffOn_infty N f r s).of_le (by simp))
      zero_lt_one 1 (fun t => phaseStressXYHorizontalDeriv_periodic N f r s t) x)

/-- The unresolved mixed phase-stress boundary density has an absolutely convergent unit Fourier series. -/
theorem summable_phaseStressXYHorizontal_fourierCoeff :
    Summable (fun n : ℤ => fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n) := by
  obtain ⟨C, _hC, hbound⟩ := exists_bound_of_periodic
    (phaseStressXYHorizontalSecondDeriv_continuous N f r s)
    (phaseStressXYHorizontalSecondDeriv_periodic N f r s) zero_lt_one
  exact summable_fourierCoeffOn_of_periodic_two zero_lt_one
    (fun x _ => phaseStressXYHorizontal_hasDerivAt N f r s x)
    (fun x _ => phaseStressXYHorizontalDeriv_hasDerivAt N f r s x)
    ((phaseStressXYHorizontalDeriv_continuous N f r s).intervalIntegrable 0 1)
    ((phaseStressXYHorizontalSecondDeriv_continuous N f r s).intervalIntegrable 0 1) hbound
    (by simpa using phaseStressXYHorizontal_periodic N f r s 0)
    (by simpa using phaseStressXYHorizontalDeriv_periodic N f r s 0)

/-- Pointwise Fourier inversion for the exact unresolved mixed phase-stress boundary density. -/
theorem phaseStressXYHorizontal_hasSum_fourier {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun n : ℤ => fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
      fourier n ((x : ℝ) : AddCircle ((1 : ℝ) - 0))) (phaseStressXYHorizontal N f r s x) := by
  obtain ⟨C, _hC, hbound⟩ := exists_bound_of_periodic
    (phaseStressXYHorizontalSecondDeriv_continuous N f r s)
    (phaseStressXYHorizontalSecondDeriv_periodic N f r s) zero_lt_one
  exact hasSum_fourier_of_periodic_two zero_lt_one
    (fun y _ => phaseStressXYHorizontal_hasDerivAt N f r s y)
    (fun y _ => phaseStressXYHorizontalDeriv_hasDerivAt N f r s y)
    ((phaseStressXYHorizontalDeriv_continuous N f r s).intervalIntegrable 0 1)
    ((phaseStressXYHorizontalSecondDeriv_continuous N f r s).intervalIntegrable 0 1) hbound
    (by simpa using phaseStressXYHorizontal_periodic N f r s 0)
    (by simpa using phaseStressXYHorizontalDeriv_periodic N f r s 0) hx

/-- Real-valuedness of the physical phase stress gives conjugate symmetry of its Fourier
coefficients.  It does not give a sign for their imaginary parts, which are exactly the parts
selected by the centered-moment kernel below. -/
theorem phaseStressXYHorizontal_fourierCoeff_neg (n : ℤ) :
    fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) (-n) =
      (starRingEnd ℂ) (fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  norm_num
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul]
  simp [phaseStressXYHorizontal]

/-- Each coefficient in the centered-moment obstruction is the literal oscillatory
derivative-loss integral of the original congruence source.  This is the exact place where a
new arithmetic orientation estimate must enter. -/
theorem phaseStressXYHorizontal_fourierCoeff_source (n : ℤ) :
    fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n =
      (2 : ℂ) * ∫ x in (0 : ℝ)..1,
        fourier (-n) ((x : ℝ) : AddCircle (1 : ℝ)) *
          (lossPair N r s (sourceDerivative N f 1 (ofComplex (point x 1)))
            (sourceDerivative N f Complex.I (ofComplex (point x 1))) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  norm_num
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  change (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))) *
      phaseStressXYHorizontal N f r s x =
    2 * ((starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))) *
      (lossPair N r s (sourceDerivative N f 1 (ofComplex (point x 1)))
        (sourceDerivative N f Complex.I (ofComplex (point x 1))) : ℂ))
  rw [show phaseStressXYHorizontal N f r s x =
      ((2 * lossPair N r s (sourceDerivative N f 1 (ofComplex (point x 1)))
        (sourceDerivative N f Complex.I (ofComplex (point x 1))) : ℝ) : ℂ) by
    exact congrArg (fun q : ℝ => (q : ℂ)) (by
      simpa only [phaseStressXYHorizontal,
        SelbergMaassUnipotentPaths.coe_ofComplex_point _ zero_lt_one] using
        phaseStressXY_eq N r s f (ofComplex (point x 1)))]
  simp only [Complex.ofReal_mul]
  push_cast
  ring


/-- The centered unit-cell moment of one nonconstant Fourier mode.  This is the exact
coefficient kernel occurring in the unresolved mixed phase-stress term. -/
private theorem centered_integral_mul_fourier (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) =
      fourier n (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) /
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      (by exact_mod_cast hn)
  have hderiv : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      HasDerivAt (fun y : ℝ =>
        (y : ℂ) * fourier n ((y : ℝ) : AddCircle (1 : ℝ)) / a -
          fourier n ((y : ℝ) : AddCircle (1 : ℝ)) / (a * a))
        ((x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) x := by
    intro x _
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
      (hasDerivAt_id x).ofReal_comp
    have hf : HasDerivAt (fun y : ℝ => fourier n ((y : ℝ) : AddCircle (1 : ℝ)))
        (a * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) x := by
      simpa [a] using hasDerivAt_fourier (1 : ℝ) n x
    have h := ((hx.mul hf).div_const a).sub (hf.div_const (a * a))
    exact h.congr_deriv (by field_simp [ha]; ring)
  have hcont : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) volume
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (Complex.continuous_ofReal.mul
      ((map_continuous (fourier n)).comp (AddCircle.continuous_mk' _))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hhalf : ((-(1 / 2 : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
      (((1 / 2 : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    exact ⟨-1, by norm_num⟩
  rw [hhalf]
  dsimp [a]
  field_simp
  norm_num
  ring

private theorem centered_integral_mul_fourier_zero :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * fourier 0 ((x : ℝ) : AddCircle (1 : ℝ))) = 0 := by
  simp only [fourier_zero, mul_one]
  have hderiv : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 / 2) (x : ℂ) x := by
    intro x _
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
      (hasDerivAt_id x).ofReal_comp
    have h := (hx.pow 2).div_const (2 : ℂ)
    exact h.congr_deriv (by ring)
  have hcont : IntervalIntegrable (fun x : ℝ => (x : ℂ)) volume
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    Complex.continuous_ofReal.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  norm_num

/-- A finite Fourier truncation of the literal mixed phase-stress boundary density has an exact
centered-moment coefficient formula.  Passing to the absolutely convergent limit leaves one
specific arithmetic problem: constrain the sign of the displayed coefficient sum. -/
theorem phaseStressXYHorizontal_centered_moment_fourier_truncation (S : Finset ℤ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * ∑ n ∈ S,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          fourier n ((x : ℝ) : AddCircle (1 : ℝ))) =
      ∑ n ∈ S,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          if n = 0 then 0 else
            fourier n (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) /
              (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * ∑ n ∈ S,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          fourier n ((x : ℝ) : AddCircle (1 : ℝ))) =
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ∑ n ∈ S, (x : ℂ) *
            (fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
              fourier n ((x : ℝ) : AddCircle (1 : ℝ))) := by
      apply intervalIntegral.integral_congr
      intro x _
      change (x : ℂ) * ∑ n ∈ S,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          fourier n ((x : ℝ) : AddCircle (1 : ℝ)) = _
      rw [Finset.mul_sum]
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun n _ => ?_
        have heq : (fun x : ℝ => (x : ℂ) *
            (fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
              fourier n ((x : ℝ) : AddCircle (1 : ℝ)))) =
            fun x : ℝ => fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
              ((x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) := by
          funext x
          ring
        rw [heq, intervalIntegral.integral_const_mul]
        by_cases hn : n = 0
        · subst n
          rw [centered_integral_mul_fourier_zero]
          simp
        · rw [centered_integral_mul_fourier n hn, if_neg hn]
      · intro n _
        exact (Complex.continuous_ofReal.mul
          (continuous_const.mul ((map_continuous (fourier n)).comp
            (AddCircle.continuous_mk' _)))).intervalIntegrable _ _

/-- The literal centered mixed phase-stress moment is exactly the absolutely convergent
Fourier coefficient functional.  Thus the remaining Selberg obstruction is not an exchange of
limit and integral: it is the sign of this concrete source-attached series. -/
theorem phaseStressXYHorizontal_centered_moment_fourier :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * phaseStressXYHorizontal N f r s x) =
      ∑' n : ℤ,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          if n = 0 then 0 else
            fourier n (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) /
              (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  let c : ℤ → ℂ := fun n =>
    fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n
  let F : ℤ → ℝ → ℂ := fun n x =>
    c n * ((x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ)))
  have hc : Summable c := summable_phaseStressXYHorizontal_fourierCoeff N f r s
  have hcnorm : Summable (fun n : ℤ => ‖c n‖) := hc.norm
  have hbound_sum : Summable (fun n : ℤ => ‖c n‖ / 2) := hcnorm.div_const 2
  have hF_cont (n : ℤ) : Continuous (F n) := by
    dsimp [F]
    exact continuous_const.mul
      (Complex.continuous_ofReal.mul
        ((map_continuous (fourier n)).comp (AddCircle.continuous_mk' _)))
  have hF_meas : ∀ n : ℤ,
      AEStronglyMeasurable (F n) (volume.restrict (uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) := by
    intro n
    exact (hF_cont n).aestronglyMeasurable.restrict
  have hF_norm (n : ℤ) (x : ℝ) : ‖F n x‖ = |x| * ‖c n‖ := by
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [Circle.norm_coe, mul_one]
    ring
  have hF_bound : ∀ n : ℤ, ∀ᵐ x : ℝ, x ∈ uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) →
      ‖F n x‖ ≤ ‖c n‖ / 2 := by
    intro n
    filter_upwards with x hx
    rw [uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at hx
    rw [hF_norm]
    have habs : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    nlinarith [mul_le_mul_of_nonneg_right habs (norm_nonneg (c n))]
  have hF_point (x : ℝ) (hx : x ∈ uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
      HasSum (fun n : ℤ => F n x) ((x : ℂ) * phaseStressXYHorizontal N f r s x) := by
    rw [uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at hx
    by_cases hx0 : x = 0
    · subst x
      simp [F]
    by_cases hxpos : 0 < x
    · have hfour := phaseStressXYHorizontal_hasSum_fourier (N := N) (f := f) (r := r) (s := s)
        (x := x) ⟨hxpos, by linarith [hx.2]⟩
      simpa [F, c, mul_assoc, mul_left_comm, mul_comm] using hfour.mul_left (x : ℂ)
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hxone : x + 1 ∈ Ioc (0 : ℝ) 1 :=
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hfour := phaseStressXYHorizontal_hasSum_fourier (N := N) (f := f) (r := r) (s := s)
        (x := x + 1) hxone
      have hcircle : (((x + 1 : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
          ((x : ℝ) : AddCircle (1 : ℝ)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
        exact ⟨1, by ring⟩
      have hphase : phaseStressXYHorizontal N f r s (x + 1) =
          phaseStressXYHorizontal N f r s x := phaseStressXYHorizontal_periodic N f r s x
      simpa [F, c, hcircle, hphase, mul_assoc, mul_left_comm, mul_comm] using
        hfour.mul_left (x : ℂ)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (μ := volume)
    (f := fun x => (x : ℂ) * phaseStressXYHorizontal N f r s x)
    (F := F) (fun n _ => ‖c n‖ / 2) hF_meas hF_bound
    (ae_of_all volume fun _ _ => hbound_sum) (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => ∑' n : ℤ, ‖c n‖ / 2) volume
        (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (ae_of_all volume fun x hx => hF_point x hx)
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      (x : ℂ) * phaseStressXYHorizontal N f r s x) =
        ∑' n : ℤ, ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F n x := hsum.tsum_eq.symm
    _ = ∑' n : ℤ,
        fourierCoeffOn zero_lt_one (phaseStressXYHorizontal N f r s) n *
          if n = 0 then 0 else
            fourier n (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) /
              (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      apply tsum_congr
      intro n
      rw [show F n = fun x : ℝ => c n *
          ((x : ℂ) * fourier n ((x : ℝ) : AddCircle (1 : ℝ))) by rfl,
        intervalIntegral.integral_const_mul]
      by_cases hn : n = 0
      · subst n
        rw [centered_integral_mul_fourier_zero]
        simp [c]
      · rw [centered_integral_mul_fourier n hn, if_neg hn]

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseStressFourier
