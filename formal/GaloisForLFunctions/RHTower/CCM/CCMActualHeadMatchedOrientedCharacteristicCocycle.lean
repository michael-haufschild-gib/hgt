import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedCosinePhaseNormalForm

/-!
# Matched prime--polar oriented characteristic cocycle

Mass matching does not merely leave an even cosine discrepancy.  One matched cell carries a
complex characteristic cocycle.  Its real component is the nonnegative-profile cosine rebate,
while its imaginary component is exactly the summable Suzuki sine current.  The cocycle is
Hermitian under frequency reflection and vanishes at spectral center, but its odd radial component
has a strictly positive first jet at every prime-power wall.

Thus scalar/even compression erases a source-forced orientation coordinate.  Any Gamma/Robin/
holonomy completion of the matched CCM producer must retain this complex two-channel carrier.
All identities below are unconditional and use the literal actual-head Fourier density.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section
namespace RHTower

def ccmActualHeadMatchedSinePhaseProfile (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      Real.sin (2 * Real.pi * r * xi)

theorem ccmActualHeadMatchedSinePhaseProfile_neg (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedSinePhaseProfile n (-xi) =
      -ccmActualHeadMatchedSinePhaseProfile n xi := by
  unfold ccmActualHeadMatchedSinePhaseProfile
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [show 2 * Real.pi * r * -xi = -(2 * Real.pi * r * xi) by ring,
    Real.sin_neg]
  ring

theorem ccmActualHeadMatchedSinePhaseProfile_zero (n : ℕ) :
    ccmActualHeadMatchedSinePhaseProfile n 0 = 0 := by
  simp [ccmActualHeadMatchedSinePhaseProfile]

/-- First frequency jet of the odd matched radial phase. -/
def ccmActualHeadMatchedSinePhaseFirstJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      Real.cos (2 * Real.pi * r * xi)

/-- Oriented dipole carried by one matched prime--polar cell. -/
def ccmActualHeadMatchedOrientedFirstMoment (n : ℕ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2)

theorem hasDerivAt_ccmActualHeadMatchedSinePhase_integrand
    (n : ℕ) (r xi : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
          Real.sin (2 * Real.pi * r * x))
      (4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
        Real.cos (2 * Real.pi * r * xi)) xi := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * r * x)
      (2 * Real.pi * r) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * r)
  have hbase := hlin.sin.const_mul
    (2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2))
  apply hbase.congr_deriv
  ring

theorem hasDerivAt_ccmActualHeadMatchedSinePhaseProfile
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedSinePhaseProfile n)
      (ccmActualHeadMatchedSinePhaseFirstJet n xi) xi := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let F : ℝ → ℝ → ℝ := fun x r =>
    2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      Real.sin (2 * Real.pi * r * x)
  let F' : ℝ → ℝ → ℝ := fun x r =>
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      Real.cos (2 * Real.pi * r * x)
  let bound : ℝ → ℝ := fun r =>
    |4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2)|
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc (0 : ℝ) rho)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume 0 rho :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc (0 : ℝ) rho)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x r‖ ≤ bound r := by
    filter_upwards with r
    intro hr x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2)| *
          |Real.cos (2 * Real.pi * r * x)| ≤
        |4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = _ := by ring
  have hboundint : IntervalIntegrable bound volume 0 rho :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y r) (F' x r) x := by
    filter_upwards with r
    intro hr x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadMatchedSinePhase_integrand n r x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadMatchedSinePhaseProfile
  unfold ccmActualHeadMatchedSinePhaseFirstJet
  simpa only [F, F', rho] using hmain

theorem ccmActualHeadMatchedSinePhaseFirstJet_zero
    (n : ℕ) :
    ccmActualHeadMatchedSinePhaseFirstJet n 0 =
      ccmActualHeadMatchedOrientedFirstMoment n := by
  unfold ccmActualHeadMatchedSinePhaseFirstJet
    ccmActualHeadMatchedOrientedFirstMoment
  simp

theorem hasDerivAt_ccmActualHeadMatchedSinePhaseProfile_zero
    (n : ℕ) :
    HasDerivAt (ccmActualHeadMatchedSinePhaseProfile n)
      (ccmActualHeadMatchedOrientedFirstMoment n) 0 := by
  simpa [ccmActualHeadMatchedSinePhaseFirstJet_zero] using
    hasDerivAt_ccmActualHeadMatchedSinePhaseProfile n 0

theorem ccmActualHeadMatchedOrientedFirstMoment_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadMatchedOrientedFirstMoment n := by
  unfold ccmActualHeadMatchedOrientedFirstMoment
  apply intervalIntegral.integral_nonneg
    (ccmActualHeadMatchedPrimePolarRadius_nonneg n)
  intro r hr
  have hr0 : 0 ≤ r := hr.1
  have hsinh : 0 ≤ Real.sinh (r / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  positivity

private theorem arsinh_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.arsinh x := by
  have h : Real.sinh 0 < Real.sinh (Real.arsinh x) := by
    rw [Real.sinh_zero, Real.sinh_arsinh]
    exact hx
  exact Real.sinh_lt_sinh.mp h

theorem ccmActualHeadMatchedPrimePolarRadius_pos_of_weight_pos
    {n : ℕ} (hn : 0 < criticalMellinAtomWeight n) :
    0 < ccmActualHeadMatchedPrimePolarRadius n := by
  unfold ccmActualHeadMatchedPrimePolarRadius
  exact mul_pos (by norm_num) (arsinh_pos_of_pos (div_pos hn (by positivity)))

theorem ccmActualHeadMatchedOrientedFirstMoment_pos_of_weight_pos
    {n : ℕ} (hn : 0 < criticalMellinAtomWeight n) :
    0 < ccmActualHeadMatchedOrientedFirstMoment n := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  have hrho : 0 < rho := ccmActualHeadMatchedPrimePolarRadius_pos_of_weight_pos hn
  unfold ccmActualHeadMatchedOrientedFirstMoment
  apply intervalIntegral.integral_pos (a := (0 : ℝ)) (b := rho) hrho
  · fun_prop
  · intro r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hsinh : 0 ≤ Real.sinh (r / 2) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    positivity
  · refine ⟨rho, Set.mem_Icc.2 ⟨hrho.le, le_rfl⟩, ?_⟩
    have hsinh : 0 < Real.sinh (rho / 2) :=
      Real.sinh_pos_iff.mpr (half_pos hrho)
    positivity

/-- Every literal Suzuki prime-power wall carries a strictly nonzero matched orientation jet. -/
theorem ccmActualHeadMatchedOrientedFirstMoment_primePower_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadMatchedOrientedFirstMoment
      (xiGammaEulerValuationNat (p, e)) := by
  apply ccmActualHeadMatchedOrientedFirstMoment_pos_of_weight_pos
  rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
  exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)

theorem integrable_ccmActualHeadMatchedSinePhase_prod
    (n : ℕ) (f : SoninL2) :
    Integrable (Function.uncurry fun r xi : ℝ =>
      Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
        ((4 * Real.sin (2 * Real.pi * Real.log n * xi) *
          Real.sin (2 * Real.pi * r * xi)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2))
      ((volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))).prod
        volume) := by
  let A : ℝ := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let C : ℝ → ℝ := fun r => 4 * A * |Real.sinh (r / 2)|
  let D : ℝ → ℝ := fun xi => ‖g xi‖ ^ 2
  have hC : Integrable C
      (volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))) := by
    exact (by fun_prop : Continuous C).integrableOn_Ioc
  have hD : Integrable D := by
    dsimp only [D, g]
    exact integrable_norm_sq (fourierUnitary f)
  have hmajor : Integrable (fun p : ℝ × ℝ => C p.1 * D p.2)
      ((volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))).prod
        volume) := hC.mul_prod hD
  have hg : StronglyMeasurable g := Lp.stronglyMeasurable (fourierUnitary f)
  have hDmeas : StronglyMeasurable D := hg.norm.pow 2
  have hcoeff : Continuous (fun p : ℝ × ℝ =>
      A * Real.sinh (p.1 / 2) *
        (4 * Real.sin (2 * Real.pi * Real.log n * p.2) *
          Real.sin (2 * Real.pi * p.1 * p.2))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun r xi : ℝ =>
      A * Real.sinh (r / 2) *
        ((4 * Real.sin (2 * Real.pi * Real.log n * xi) *
          Real.sin (2 * Real.pi * r * xi)) * D xi))
      ((volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))).prod
        volume) := by
    refine (hcoeff.stronglyMeasurable.aestronglyMeasurable.mul
      (hDmeas.comp_measurable measurable_snd).aestronglyMeasurable).congr ?_
    filter_upwards with p
    change (A * Real.sinh (p.1 / 2) *
        (4 * Real.sin (2 * Real.pi * Real.log n * p.2) *
          Real.sin (2 * Real.pi * p.1 * p.2))) * D p.2 =
      A * Real.sinh (p.1 / 2) *
        ((4 * Real.sin (2 * Real.pi * Real.log n * p.2) *
          Real.sin (2 * Real.pi * p.1 * p.2)) * D p.2)
    ring
  apply hmajor.mono' hmeas
  filter_upwards with p
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  change ‖A * Real.sinh (p.1 / 2) *
      ((4 * Real.sin (2 * Real.pi * Real.log n * p.2) *
        Real.sin (2 * Real.pi * p.1 * p.2)) * D p.2)‖ ≤
    C p.1 * D p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hA, abs_of_nonneg hD0]
  norm_num
  dsimp only [C]
  calc
    A * |Real.sinh (p.1 / 2)| *
        (4 * |Real.sin (2 * Real.pi * Real.log n * p.2)| *
          |Real.sin (2 * Real.pi * p.1 * p.2)| * D p.2) ≤
      A * |Real.sinh (p.1 / 2)| * (4 * 1 * 1 * D p.2) := by
        gcongr <;> exact Real.abs_sin_le_one _
    _ = (4 * A * |Real.sinh (p.1 / 2)|) * D p.2 := by ring

theorem ccmActualHeadMatchedSuzukiCurrent_eq_sinePhaseProfile
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedSuzukiCurrent n f =
      2 * ∫ xi : ℝ,
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun r xi =>
    A * Real.sinh (r / 2) *
      ((4 * Real.sin (2 * Real.pi * Real.log n * xi) *
        Real.sin (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)
  have hrho : 0 ≤ rho := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) rho)).prod volume) := by
    simpa only [F, rho, A, g] using
      integrable_ccmActualHeadMatchedSinePhase_prod n f
  have hswap := integral_integral_swap hprod
  have hslice (xi : ℝ) :
      (∫ r in Ioc (0 : ℝ) rho, F r xi) =
        2 * Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadMatchedSinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    rw [show 2 * Real.sin (2 * Real.pi * Real.log n * xi) *
          (∫ r in Ioc (0 : ℝ) rho,
            2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
              Real.sin (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2 =
        (2 * Real.sin (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2) *
          (∫ r in Ioc (0 : ℝ) rho,
            2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
              Real.sin (2 * Real.pi * r * xi)) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [F, A]
    ring
  rw [ccmActualHeadMatchedSuzukiCurrent]
  have houter :
      (∫ r in (0 : ℝ)..rho,
        A * Real.sinh (r / 2) *
          ccmActualHeadTranslationSineCurrent (Real.log n) r f) =
        ∫ r in (0 : ℝ)..rho, ∫ xi : ℝ, F r xi := by
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [ccmActualHeadTranslationSineCurrent_eq_fourierIntegral]
    dsimp only [F]
    rw [← integral_const_mul]
  change (∫ r in (0 : ℝ)..rho,
    A * Real.sinh (r / 2) *
      ccmActualHeadTranslationSineCurrent (Real.log n) r f) = _
  rw [houter, intervalIntegral.integral_of_le hrho]
  calc
    (∫ r in Ioc (0 : ℝ) rho, ∫ xi : ℝ, F r xi) =
        ∫ xi : ℝ, ∫ r in Ioc (0 : ℝ) rho, F r xi := hswap
    _ = ∫ xi : ℝ,
        2 * Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with xi
            exact hslice xi
    _ = 2 * ∫ xi : ℝ,
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with xi
            ring

theorem integrable_ccmActualHeadMatchedSinePhaseProfile_mul_density
    (n : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      Real.sin (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedSinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun r xi =>
    A * Real.sinh (r / 2) *
      ((4 * Real.sin (2 * Real.pi * Real.log n * xi) *
        Real.sin (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)
  have hrho : 0 ≤ rho := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) rho)).prod volume) := by
    simpa only [F, rho, A, g] using
      integrable_ccmActualHeadMatchedSinePhase_prod n f
  have hslice (xi : ℝ) :
      (∫ r in Ioc (0 : ℝ) rho, F r xi) =
        2 * Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadMatchedSinePhaseProfile
    rw [intervalIntegral.integral_of_le hrho]
    rw [show 2 * Real.sin (2 * Real.pi * Real.log n * xi) *
          (∫ r in Ioc (0 : ℝ) rho,
            2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
              Real.sin (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2 =
        (2 * Real.sin (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2) *
          (∫ r in Ioc (0 : ℝ) rho,
            2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
              Real.sin (2 * Real.pi * r * xi)) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [F, A]
    ring
  have htwo : Integrable (fun xi : ℝ =>
      2 * Real.sin (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedSinePhaseProfile n xi * ‖g xi‖ ^ 2) :=
    hprod.integral_prod_right.congr
      (Filter.Eventually.of_forall fun xi => hslice xi)
  have hscale := htwo.const_mul (1 / 2 : ℝ)
  refine hscale.congr (Filter.Eventually.of_forall fun xi => ?_)
  dsimp only [g]
  ring

def ccmActualHeadMatchedOrientedPhaseProfile (n : ℕ) (xi : ℝ) : ℂ :=
  (ccmActualHeadMatchedCosinePhaseProfile n xi : ℂ) -
    I * (ccmActualHeadMatchedSinePhaseProfile n xi : ℂ)

/-- Pointwise oriented characteristic increment of one symmetric polar pair around its arithmetic
anchor. -/
def ccmActualHeadMatchedRadialCharacteristicCocycle
    (n : ℕ) (r xi : ℝ) : ℂ :=
  let A := Real.exp (Real.log n / 2)
  let theta := 2 * Real.pi * r * xi
  ((A * Real.exp (r / 2) : ℝ) : ℂ) *
      (1 - Complex.exp ((theta : ℂ) * I)) +
    ((A * Real.exp (-(r / 2)) : ℝ) : ℂ) *
      (1 - Complex.exp (((-theta : ℝ) : ℂ) * I))

/-- Hyperbolic cosine/sine pair is exactly one complex characteristic cocycle. -/
theorem ccmActualHeadMatchedRadialCharacteristicCocycle_eq
    (n : ℕ) (r xi : ℝ) :
    ccmActualHeadMatchedRadialCharacteristicCocycle n r xi =
      ((Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) : ℝ) : ℂ) -
        I * ((2 * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
          Real.sin (2 * Real.pi * r * xi) : ℝ) : ℂ) := by
  let A := Real.exp (Real.log n / 2)
  let theta := 2 * Real.pi * r * xi
  change ((A * Real.exp (r / 2) : ℝ) : ℂ) *
        (1 - Complex.exp ((theta : ℂ) * I)) +
      ((A * Real.exp (-(r / 2)) : ℝ) : ℂ) *
        (1 - Complex.exp (((-theta : ℝ) : ℂ) * I)) =
    ((A * Real.cosh (r / 2) * (2 - 2 * Real.cos theta) : ℝ) : ℂ) -
      I * ((2 * A * Real.sinh (r / 2) * Real.sin theta : ℝ) : ℂ)
  rw [Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Real.cosh_eq, Real.sinh_eq] <;> ring

def ccmActualHeadMatchedOrientedPhaseSymbol (n : ℕ) (xi : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * Real.log n * xi : ℝ) : ℂ) * I) *
    ccmActualHeadMatchedOrientedPhaseProfile n xi

theorem ccmActualHeadMatchedOrientedPhaseSymbol_re (n : ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re =
      Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi +
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi := by
  let theta : ℝ := 2 * Real.pi * Real.log n * xi
  change (Complex.exp ((theta : ℂ) * I) *
      ((ccmActualHeadMatchedCosinePhaseProfile n xi : ℂ) -
        I * (ccmActualHeadMatchedSinePhaseProfile n xi : ℂ))).re =
    Real.cos theta * ccmActualHeadMatchedCosinePhaseProfile n xi +
      Real.sin theta * ccmActualHeadMatchedSinePhaseProfile n xi
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem ccmActualHeadMatchedOrientedPhaseSymbol_im (n : ℕ) (xi : ℝ) :
    (ccmActualHeadMatchedOrientedPhaseSymbol n xi).im =
      Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi -
        Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi := by
  let theta : ℝ := 2 * Real.pi * Real.log n * xi
  change (Complex.exp ((theta : ℂ) * I) *
      ((ccmActualHeadMatchedCosinePhaseProfile n xi : ℂ) -
        I * (ccmActualHeadMatchedSinePhaseProfile n xi : ℂ))).im =
    Real.sin theta * ccmActualHeadMatchedCosinePhaseProfile n xi -
      Real.cos theta * ccmActualHeadMatchedSinePhaseProfile n xi
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

theorem integrable_ccmActualHeadMatchedOrientedPhaseSymbol_re_mul_density
    (n : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hcos := integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density n f
  have hsin := integrable_ccmActualHeadMatchedSinePhaseProfile_mul_density n f
  refine (hcos.add hsin).congr (Filter.Eventually.of_forall fun xi => ?_)
  change
    Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 +
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 =
      (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re]
  ring

theorem ccmActualHeadMatchedOrientedPhaseSymbol_neg (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedOrientedPhaseSymbol n (-xi) =
      star (ccmActualHeadMatchedOrientedPhaseSymbol n xi) := by
  apply Complex.ext
  · change (ccmActualHeadMatchedOrientedPhaseSymbol n (-xi)).re =
      (conj (ccmActualHeadMatchedOrientedPhaseSymbol n xi)).re
    rw [Complex.conj_re,
      ccmActualHeadMatchedOrientedPhaseSymbol_re,
      ccmActualHeadMatchedOrientedPhaseSymbol_re,
      ccmActualHeadMatchedCosinePhaseProfile_neg,
      ccmActualHeadMatchedSinePhaseProfile_neg]
    rw [show 2 * Real.pi * Real.log n * -xi =
        -(2 * Real.pi * Real.log n * xi) by ring,
      Real.cos_neg, Real.sin_neg]
    ring
  · change (ccmActualHeadMatchedOrientedPhaseSymbol n (-xi)).im =
      (conj (ccmActualHeadMatchedOrientedPhaseSymbol n xi)).im
    rw [Complex.conj_im,
      ccmActualHeadMatchedOrientedPhaseSymbol_im,
      ccmActualHeadMatchedOrientedPhaseSymbol_im,
      ccmActualHeadMatchedCosinePhaseProfile_neg,
      ccmActualHeadMatchedSinePhaseProfile_neg]
    rw [show 2 * Real.pi * Real.log n * -xi =
        -(2 * Real.pi * Real.log n * xi) by ring,
      Real.cos_neg, Real.sin_neg]
    ring

@[simp] theorem ccmActualHeadMatchedOrientedPhaseSymbol_zero (n : ℕ) :
    ccmActualHeadMatchedOrientedPhaseSymbol n 0 = 0 := by
  simp [ccmActualHeadMatchedOrientedPhaseSymbol,
    ccmActualHeadMatchedOrientedPhaseProfile,
    ccmActualHeadMatchedCosinePhaseProfile_zero,
    ccmActualHeadMatchedSinePhaseProfile_zero]

theorem ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_orientedPhase
    (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      -2 * ∫ xi : ℝ,
        (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki,
    ccmActualHeadMatchedSymmetricCellResidual_eq_cosinePhaseProfile,
    ccmActualHeadMatchedSuzukiCurrent_eq_sinePhaseProfile]
  simp_rw [ccmActualHeadMatchedOrientedPhaseSymbol_re]
  have hcos := integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density n f
  have hsin := integrable_ccmActualHeadMatchedSinePhaseProfile_mul_density n f
  rw [show (fun xi : ℝ =>
      (Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi +
        Real.sin (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedSinePhaseProfile n xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      (fun xi : ℝ =>
        Real.cos (2 * Real.pi * Real.log n * xi) *
            ccmActualHeadMatchedCosinePhaseProfile n xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 +
          Real.sin (2 * Real.pi * Real.log n * xi) *
            ccmActualHeadMatchedSinePhaseProfile n xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) by
        funext xi
        ring,
    integral_add hcos hsin]
  ring

/-- Aggregate complex characteristic cocycle of a finite matched source packet. -/
def ccmActualHeadMatchedOrientedPhaseFiniteSymbol
    (F : Finset ℕ) (xi : ℝ) : ℂ :=
  ∑ n ∈ F, ccmActualHeadMatchedOrientedPhaseSymbol n xi

@[simp] theorem ccmActualHeadMatchedOrientedPhaseFiniteSymbol_zero
    (F : Finset ℕ) :
    ccmActualHeadMatchedOrientedPhaseFiniteSymbol F 0 = 0 := by
  simp [ccmActualHeadMatchedOrientedPhaseFiniteSymbol]

/-- Finite matched prime--polar block is the spectral real part of one aggregate Hermitian
characteristic cocycle. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_orientedPhaseFiniteSymbol
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        (ccmActualHeadMatchedOrientedPhaseFiniteSymbol F xi).re *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  unfold ccmActualHeadMatchedPrimePolarFiniteBlock
  simp_rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_orientedPhase]
  rw [← Finset.mul_sum]
  congr 1
  rw [← MeasureTheory.integral_finsetSum F
    (fun n _ =>
      integrable_ccmActualHeadMatchedOrientedPhaseSymbol_re_mul_density n f)]
  apply integral_congr_ae
  filter_upwards with xi
  unfold ccmActualHeadMatchedOrientedPhaseFiniteSymbol
  rw [Complex.re_sum]
  rw [Finset.sum_mul]

end RHTower
