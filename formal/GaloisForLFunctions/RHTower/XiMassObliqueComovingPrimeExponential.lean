import GaloisForLFunctions.HTGeometry.AbstractSpectralObliqueComovingExponential
import GaloisForLFunctions.RHTower.XiMassComovingPrimeExponential

/-!
# Oblique co-moving Xi prime-source phase diagram

For aperture velocity `v>0`, set `A_v(u)=v|u|+2`.  The universal oblique-cone theorem applies on
every positive real-time line in the exact open chamber `4σv>1`.  It gives exponential extinction
of the Xi trace at rate

`κ(σ,v) = (σ - 1/(4v))/2`.

The Gamma mass-gap theorem transfers the same rate to the literal von-Mangoldt source.  Thus fixed
source minus the oblique arm has the same asymptotic obstruction as the fixed source, throughout a
two-parameter phase chamber.  The former unit-slope theorem is only one interior point of this
larger diagram.
-/

open Complex

namespace RHTower

noncomputable section

/-- Oblique aperture schedule with velocity `v`. -/
def xiObliqueComovingMass (v u : ℝ) : ℝ := v * |u| + 2

theorem xiObliqueComovingMass_ge_two {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    2 ≤ xiObliqueComovingMass v u := by
  unfold xiObliqueComovingMass
  nlinarith [mul_nonneg hv (abs_nonneg u)]

theorem velocity_mul_abs_le_xiObliqueComovingMass_sub_half
    (v u : ℝ) :
    v * |u| ≤ xiObliqueComovingMass v u - 1 / 2 := by
  unfold xiObliqueComovingMass
  linarith

/-- Xi name for the universal oblique-cone decay rate. -/
def xiObliqueComovingExponentialRate (σ v : ℝ) : ℝ :=
  HTGeometry.AbstractSpectralFamily.obliqueComovingExponentialRate σ v

theorem xiObliqueComovingExponentialRate_pos
    {σ v : ℝ} (hv : 0 < v) (hphase : 1 < 4 * σ * v) :
    0 < xiObliqueComovingExponentialRate σ v :=
  HTGeometry.AbstractSpectralFamily.obliqueComovingExponentialRate_pos hv hphase

theorem xiObliqueComovingExponentialRate_lt_sigma
    {σ v : ℝ} (hv : 0 < v) (hphase : 1 < 4 * σ * v) :
    xiObliqueComovingExponentialRate σ v < σ := by
  have hκ := xiObliqueComovingExponentialRate_pos hv hphase
  unfold xiObliqueComovingExponentialRate
    HTGeometry.AbstractSpectralFamily.obliqueComovingExponentialRate
  have hv4 : 0 < 4 * v := by positivity
  have hfrac : 0 < 1 / (4 * v) := by positivity
  have hfracLt : 1 / (4 * v) < σ := by
    rw [div_lt_iff₀ hv4]
    nlinarith
  linarith

/-- Xi trace extinction throughout the open oblique mass chamber. -/
theorem norm_xiMassTraceC_oblique_comoving_le_exponential
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) (u : ℝ) :
    ‖(xiMassFamily (show 1 / 2 ≤ xiObliqueComovingMass v u by
        linarith [xiObliqueComovingMass_ge_two hv.le u])).traceC
          ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2)) *
        xiPoissonTraceReal (xiObliqueComovingExponentialRate σ v) := by
  let ha : 1 / 2 ≤ xiObliqueComovingMass v u := by
    linarith [xiObliqueComovingMass_ge_two hv.le u]
  have h := xiPoissonAbstract.norm_mass_traceC_le_oblique_comoving_exponential
    (xiObliqueComovingMass_ge_two hv.le u) hv
    (velocity_mul_abs_le_xiObliqueComovingMass_sub_half v u) hσ hphase
  rw [← xiMassFamily_traceC_eq ha ((σ : ℂ) + u * I),
    xiPoissonAbstract_traceReal] at h
  simpa only [xiObliqueComovingExponentialRate] using h

/-- Fixed coefficient in the oblique co-moving literal prime bound. -/
def xiMassObliqueComovingPrimeExponentialConstant (σ v : ℝ) : ℝ :=
  ‖(Real.pi : ℂ) * I‖ *
      xiPoissonTraceReal (xiObliqueComovingExponentialRate σ v) +
    xiMassBottomArchUniformBound 2
      (σ - xiObliqueComovingExponentialRate σ v)

theorem xiMassObliqueComovingPrimeExponentialConstant_nonneg
    {σ v : ℝ} (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) :
    0 ≤ xiMassObliqueComovingPrimeExponentialConstant σ v := by
  have hκ := xiObliqueComovingExponentialRate_pos hv hphase
  have hκσ := xiObliqueComovingExponentialRate_lt_sigma hv hphase
  unfold xiMassObliqueComovingPrimeExponentialConstant
  exact add_nonneg
    (mul_nonneg (norm_nonneg _) (xiPoissonTraceReal_nonneg _))
    (xiMassBottomArchUniformBound_nonneg (by norm_num) (by linarith))

/-- **Literal prime-source phase diagram.**  The oblique co-moving Xi source decays exponentially
on every positive line satisfying `4σv>1`. -/
theorem norm_xiMassBottomPrimeIntegral_oblique_comoving_le_exponential
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) (u : ℝ) :
    ‖xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
        ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2)) *
        xiMassObliqueComovingPrimeExponentialConstant σ v := by
  let κ : ℝ := xiObliqueComovingExponentialRate σ v
  let A : ℝ := xiObliqueComovingMass v u
  let E : ℝ := Real.exp (-κ * (A - 1 / 2))
  have hκ : 0 < κ := xiObliqueComovingExponentialRate_pos hv hphase
  have hκσ : κ < σ := xiObliqueComovingExponentialRate_lt_sigma hv hphase
  have hA : 2 ≤ A := xiObliqueComovingMass_ge_two hv.le u
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < A := by linarith
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by simpa [Complex.mul_re] using hσ
  have htrace := norm_xiMassTraceC_oblique_comoving_le_exponential hσ hv hphase u
  have harch0 :
      ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
        xiMassBottomArchUniformBound A σ :=
    norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ
  have harchGap := xiMassBottomArchUniformBound_le_exponential_gap
    (a := A) (b := (2 : ℝ)) (σ := σ) (δ := κ)
    (by norm_num) hA hκ hκσ
  have harch :
      ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
        E * xiMassBottomArchUniformBound 2 (σ - κ) :=
    harch0.trans (by simpa only [E] using harchGap)
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
  calc
    ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I)) +
        xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ ≤
      ‖I * (Real.pi * I *
          (xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I))‖ +
        ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ := norm_add_le _ _
    _ = ‖(Real.pi : ℂ) * I‖ *
          ‖(xiMassFamily (show 1 / 2 ≤ A by linarith)).traceC ((σ : ℂ) + u * I)‖ +
        ‖xiMassBottomArchIntegral A 1 ((σ : ℂ) + u * I)‖ := by
      rw [norm_mul, norm_mul]
      simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (E * xiPoissonTraceReal κ) +
        E * xiMassBottomArchUniformBound 2 (σ - κ) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [E, A, κ] using htrace) (norm_nonneg _)) harch
    _ = Real.exp (-xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2)) *
        xiMassObliqueComovingPrimeExponentialConstant σ v := by
      dsimp only [E, A, κ]
      unfold xiMassObliqueComovingPrimeExponentialConstant
      ring

/-- Fixed source minus the exponentially absorbed oblique aperture. -/
def xiMassPrimeObliqueHighPass (v σ u : ℝ) : ℂ :=
  xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I) -
    xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1 ((σ : ℂ) + u * I)

/-- The oblique high-pass equals the fixed source modulo the explicit exponential ideal. -/
theorem norm_xiMassPrimeObliqueHighPass_sub_fixedSource_le_exponential
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) (u : ℝ) :
    ‖xiMassPrimeObliqueHighPass v σ u -
        xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2)) *
        xiMassObliqueComovingPrimeExponentialConstant σ v := by
  unfold xiMassPrimeObliqueHighPass
  rw [show xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I) -
      xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1 ((σ : ℂ) + u * I) -
      xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I) =
      -xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
        ((σ : ℂ) + u * I) by ring, norm_neg]
  exact norm_xiMassBottomPrimeIntegral_oblique_comoving_le_exponential
    hσ hv hphase u

/-- Uniform vertical boundedness of one oblique prime high-pass. -/
def XiMassPrimeObliqueHighPassLineBound (v σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖xiMassPrimeObliqueHighPass v σ u‖ ≤ C

/-- Subtracting any exponentially absorbed oblique arm preserves fixed-source boundedness exactly. -/
theorem xiMassBottomPrimeLineBound_iff_obliqueHighPassLineBound
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) :
    XiMassBottomPrimeLineBound 1 (3 / 4) σ ↔
      XiMassPrimeObliqueHighPassLineBound v σ := by
  let D : ℝ := xiMassObliqueComovingPrimeExponentialConstant σ v
  have hD : 0 ≤ D :=
    xiMassObliqueComovingPrimeExponentialConstant_nonneg hv hphase
  have hmove : ∀ u : ℝ,
      ‖xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
          ((σ : ℂ) + u * I)‖ ≤ D := by
    intro u
    have hκ := xiObliqueComovingExponentialRate_pos hv hphase
    have hA := xiObliqueComovingMass_ge_two hv.le u
    have hexp : Real.exp (-xiObliqueComovingExponentialRate σ v *
        (xiObliqueComovingMass v u - 1 / 2)) ≤ 1 := by
      have hnonpos : -xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2) ≤ 0 := by nlinarith
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonpos
    have h := norm_xiMassBottomPrimeIntegral_oblique_comoving_le_exponential
      hσ hv hphase u
    calc
      ‖xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
          ((σ : ℂ) + u * I)‖ ≤
        Real.exp (-xiObliqueComovingExponentialRate σ v *
          (xiObliqueComovingMass v u - 1 / 2)) * D := by
            simpa only [D] using h
      _ ≤ 1 * D := mul_le_mul_of_nonneg_right hexp hD
      _ = D := one_mul D
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + D, fun u => ?_⟩
    unfold xiMassPrimeObliqueHighPass
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (hmove u))
  · rintro ⟨C, hC⟩
    refine ⟨C + D, fun u => ?_⟩
    have heq :
        xiMassBottomPrimeIntegral 1 (3 / 4) ((σ : ℂ) + u * I) =
          xiMassPrimeObliqueHighPass v σ u +
            xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
              ((σ : ℂ) + u * I) := by
      unfold xiMassPrimeObliqueHighPass
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hC u) (hmove u))

/-- **Oblique high-pass RH criterion.**  Every point of the open absorber chamber defines the same
RH-strength boundedness problem, on every positive real-time line. -/
theorem riemannHypothesis_iff_xiMassPrimeObliqueHighPassLineBound
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hphase : 1 < 4 * σ * v) :
    RiemannHypothesis ↔ XiMassPrimeObliqueHighPassLineBound v σ := by
  rw [riemannHypothesis_iff_xiMassBottomPrimeLineBound
    (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
    (show (3 / 4 : ℝ) < 1 by norm_num) hσ]
  exact xiMassBottomPrimeLineBound_iff_obliqueHighPassLineBound hσ hv hphase

end


end RHTower
