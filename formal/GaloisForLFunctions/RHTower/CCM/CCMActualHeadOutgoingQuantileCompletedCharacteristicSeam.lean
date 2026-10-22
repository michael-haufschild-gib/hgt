import GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileCharacteristicTransport

/-!
# Completed-head outgoing-quantile characteristic seam

This module closes the terminal seam left by finite outgoing-quantile cells. A generic anchored
interval transport theorem is proved for either endpoint orientation. Applied to the quantile
boundary and physical terminal point, it combines all cells and the terminal interval into one
mass-balanced, even characteristic source.

The completed symbol has an exact continuous-minus-prime-minus-endpoint formula, lands exactly on
the Sonin Fourier density, and has a global signed second-moment curvature law. Substitution into
the actual Gamma-wall outgoing producer leaves the fixed Gamma scalar, literal positive endpoint
reserve, and positive higher-Binet energy. Their scalar sum is not asserted positive. No
completed-error threshold, terminal-order premise, or RH-equivalent sign condition is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Cosine phase of an oriented polar interval, measured from a fixed translation anchor. -/
def ccmActualHeadAnchoredCosinePhaseProfile
    (lo hi s xi : ℝ) : ℝ :=
  ∫ h in lo..hi,
    Real.exp (h / 2) *
      (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * s * xi))

theorem ccmActualHeadAnchoredCosinePhaseProfile_neg
    (lo hi s xi : ℝ) :
    ccmActualHeadAnchoredCosinePhaseProfile lo hi s (-xi) =
      ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi := by
  unfold ccmActualHeadAnchoredCosinePhaseProfile
  apply intervalIntegral.integral_congr
  intro h hh
  dsimp only
  rw [show 2 * Real.pi * h * -xi = -(2 * Real.pi * h * xi) by ring,
    show 2 * Real.pi * s * -xi = -(2 * Real.pi * s * xi) by ring,
    Real.cos_neg, Real.cos_neg]

theorem ccmActualHeadAnchoredCosinePhaseProfile_zero
    (lo hi s : ℝ) :
    ccmActualHeadAnchoredCosinePhaseProfile lo hi s 0 = 0 := by
  unfold ccmActualHeadAnchoredCosinePhaseProfile
  simp

theorem ccmActualHeadAnchoredTransport_eq_nestedCosinePhase
    (lo hi s : ℝ) (f : SoninL2) :
    (∫ h in lo..hi,
      Real.exp (h / 2) *
        (ccmActualHeadTranslationDefect s f -
          ccmActualHeadTranslationDefect h f)) =
      ∫ h in lo..hi,
        Real.exp (h / 2) *
          (∫ xi : ℝ,
            2 * (Real.cos (2 * Real.pi * h * xi) -
              Real.cos (2 * Real.pi * s * xi)) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  apply intervalIntegral.integral_congr
  intro h hh
  dsimp only
  rw [ccmActualHeadTranslationDefect_sub_eq_cosineDifference]

theorem integrable_ccmActualHeadAnchoredCosinePhase_prod_of_le
    {lo hi : ℝ} (_hlohi : lo ≤ hi) (s : ℝ) (f : SoninL2) :
    Integrable (Function.uncurry fun h xi : ℝ =>
      Real.exp (h / 2) *
        (2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * s * xi)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2))
      ((volume.restrict (Ioc lo hi)).prod volume) := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let C : ℝ → ℝ := fun h => 4 * Real.exp (h / 2)
  let D : ℝ → ℝ := fun xi => ‖g xi‖ ^ 2
  have hC : Integrable C (volume.restrict (Ioc lo hi)) := by
    exact (by fun_prop : Continuous C).integrableOn_Ioc
  have hD : Integrable D := by
    dsimp only [D, g]
    exact integrable_norm_sq (fourierUnitary f)
  have hmajor : Integrable (fun p : ℝ × ℝ => C p.1 * D p.2)
      ((volume.restrict (Ioc lo hi)).prod volume) :=
    hC.mul_prod hD
  have hg : StronglyMeasurable g := Lp.stronglyMeasurable (fourierUnitary f)
  have hDmeas : StronglyMeasurable D := hg.norm.pow 2
  have hcoeff : Continuous (fun p : ℝ × ℝ =>
      Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * s * p.2)))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun h xi : ℝ =>
      Real.exp (h / 2) *
        (2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * s * xi)) * D xi))
      ((volume.restrict (Ioc lo hi)).prod volume) := by
    refine (hcoeff.stronglyMeasurable.aestronglyMeasurable.mul
      (hDmeas.comp_measurable measurable_snd).aestronglyMeasurable).congr ?_
    filter_upwards with p
    change (Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * s * p.2)))) * D p.2 =
      Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * s * p.2)) * D p.2)
    ring
  apply hmajor.mono' hmeas
  filter_upwards with p
  have hcosh : |Real.cos (2 * Real.pi * p.1 * p.2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hcoss : |Real.cos (2 * Real.pi * s * p.2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  change ‖Real.exp (p.1 / 2) *
      (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
        Real.cos (2 * Real.pi * s * p.2)) * D p.2)‖ ≤
    C p.1 * D p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hD0]
  dsimp only [C]
  calc
    Real.exp (p.1 / 2) *
        (|2| * |Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * s * p.2)| * D p.2) ≤
      Real.exp (p.1 / 2) * (2 * 2 * D p.2) := by
        gcongr
        · norm_num
        · exact (abs_sub _ _).trans (by linarith)
    _ = (4 * Real.exp (p.1 / 2)) * D p.2 := by ring

theorem integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density_of_le
    {lo hi : ℝ} (hlohi : lo ≤ hi) (s : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun h xi =>
    Real.exp (h / 2) *
      (2 * (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc lo hi)).prod volume) := by
    simpa only [F, g] using
      integrable_ccmActualHeadAnchoredCosinePhase_prod_of_le hlohi s f
  have hslice (xi : ℝ) :
      (∫ h in Ioc lo hi, F h xi) =
        2 * ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadAnchoredCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hlohi]
    rw [show 2 *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * s * xi))) * ‖g xi‖ ^ 2 =
        (2 * ‖g xi‖ ^ 2) *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * s * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [F]
    ring
  have htwo : Integrable (fun xi : ℝ =>
      2 * ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi * ‖g xi‖ ^ 2) :=
    hprod.integral_prod_right.congr
      (Filter.Eventually.of_forall fun xi => hslice xi)
  have hscale := htwo.const_mul (1 / 2 : ℝ)
  refine hscale.congr (Filter.Eventually.of_forall fun xi => ?_)
  dsimp only [g]
  ring

theorem ccmActualHeadAnchoredTransport_eq_cosinePhaseProfile_of_le
    {lo hi : ℝ} (hlohi : lo ≤ hi) (s : ℝ) (f : SoninL2) :
    (∫ h in lo..hi,
      Real.exp (h / 2) *
        (ccmActualHeadTranslationDefect s f -
          ccmActualHeadTranslationDefect h f)) =
      2 * ∫ xi : ℝ,
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun h xi =>
    Real.exp (h / 2) *
      (2 * (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc lo hi)).prod volume) := by
    simpa only [F, g] using
      integrable_ccmActualHeadAnchoredCosinePhase_prod_of_le hlohi s f
  have hswap := integral_integral_swap hprod
  have hslicer (xi : ℝ) :
      (∫ h in Ioc lo hi, F h xi) =
        2 * ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadAnchoredCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hlohi]
    rw [show 2 *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * s * xi))) * ‖g xi‖ ^ 2 =
        (2 * ‖g xi‖ ^ 2) *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * s * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [F]
    ring
  rw [ccmActualHeadAnchoredTransport_eq_nestedCosinePhase]
  have houter :
      (∫ h in lo..hi,
        Real.exp (h / 2) *
          (∫ xi : ℝ,
            2 * (Real.cos (2 * Real.pi * h * xi) -
              Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2)) =
        ∫ h in lo..hi, ∫ xi : ℝ, F h xi := by
    apply intervalIntegral.integral_congr
    intro h hh
    dsimp only [F]
    rw [← integral_const_mul]
  change (∫ h in lo..hi,
    Real.exp (h / 2) *
      (∫ xi : ℝ,
        2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2)) = _
  rw [houter, intervalIntegral.integral_of_le hlohi]
  calc
    (∫ h in Ioc lo hi, ∫ xi : ℝ, F h xi) =
        ∫ xi : ℝ, ∫ h in Ioc lo hi, F h xi := hswap
    _ = ∫ xi : ℝ,
        2 * ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖g xi‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with xi
            exact hslicer xi
    _ = 2 * ∫ xi : ℝ,
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖g xi‖ ^ 2 := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with xi
            ring

theorem ccmActualHeadAnchoredTransport_eq_cosinePhaseProfile
    (lo hi s : ℝ) (f : SoninL2) :
    (∫ h in lo..hi,
      Real.exp (h / 2) *
        (ccmActualHeadTranslationDefect s f -
          ccmActualHeadTranslationDefect h f)) =
      2 * ∫ xi : ℝ,
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rcases le_total lo hi with hlohi | hhilo
  · exact ccmActualHeadAnchoredTransport_eq_cosinePhaseProfile_of_le hlohi s f
  · have hreverse :=
      ccmActualHeadAnchoredTransport_eq_cosinePhaseProfile_of_le hhilo s f
    have hphase (xi : ℝ) :
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi =
          -ccmActualHeadAnchoredCosinePhaseProfile hi lo s xi := by
      unfold ccmActualHeadAnchoredCosinePhaseProfile
      rw [intervalIntegral.integral_symm]
    rw [intervalIntegral.integral_symm]
    rw [hreverse]
    rw [show (fun xi : ℝ =>
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
        fun xi : ℝ =>
          -(ccmActualHeadAnchoredCosinePhaseProfile hi lo s xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) by
      funext xi
      rw [hphase]
      ring,
      integral_neg]
    ring

theorem integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density
    (lo hi s : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  rcases le_total lo hi with hlohi | hhilo
  · exact integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density_of_le
      hlohi s f
  · have hordered :=
      integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density_of_le
        hhilo s f
    have hneg := hordered.neg
    have hphase (xi : ℝ) :
        ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi =
          -ccmActualHeadAnchoredCosinePhaseProfile hi lo s xi := by
      unfold ccmActualHeadAnchoredCosinePhaseProfile
      rw [intervalIntegral.integral_symm]
    refine hneg.congr (Filter.Eventually.of_forall fun xi => ?_)
    change -(ccmActualHeadAnchoredCosinePhaseProfile hi lo s xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
    rw [hphase]
    ring

def ccmActualHeadAnchoredCosinePhaseFirstJet
    (lo hi s xi : ℝ) : ℝ :=
  ∫ h in lo..hi,
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
        (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * xi))

def ccmActualHeadAnchoredCosinePhaseSecondJet
    (lo hi s xi : ℝ) : ℝ :=
  ∫ h in lo..hi,
    Real.exp (h / 2) *
      (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
        (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * xi))

theorem hasDerivAt_ccmActualHeadAnchoredCosinePhase_integrand
    (s h xi : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * x) -
          Real.cos (2 * Real.pi * s * x)))
      (Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
          (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * xi))) xi := by
  have hh : HasDerivAt (fun x : ℝ => 2 * Real.pi * h * x)
      (2 * Real.pi * h) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * h)
  have hs : HasDerivAt (fun x : ℝ => 2 * Real.pi * s * x)
      (2 * Real.pi * s) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * s)
  have hbase := (hh.cos.sub hs.cos).const_mul (Real.exp (h / 2))
  have hderiv : HasDerivAt
      (fun y => Real.exp (h / 2) *
        ((fun x => Real.cos (2 * Real.pi * h * x)) -
          fun x => Real.cos (2 * Real.pi * s * x)) y)
      (Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
          (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * xi))) xi :=
    hbase.congr_deriv (by ring)
  simpa only [Pi.sub_apply] using hderiv

theorem hasDerivAt_ccmActualHeadAnchoredCosinePhaseFirstJet_integrand
    (s h xi : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
          (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x)))
      (Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
          (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * xi))) xi := by
  have hh : HasDerivAt (fun x : ℝ => 2 * Real.pi * h * x)
      (2 * Real.pi * h) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * h)
  have hs : HasDerivAt (fun x : ℝ => 2 * Real.pi * s * x)
      (2 * Real.pi * s) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * s)
  have hbase := ((hh.sin.const_mul (-(2 * Real.pi * h))).add
    (hs.sin.const_mul (2 * Real.pi * s))).const_mul (Real.exp (h / 2))
  have hderiv : HasDerivAt
      (fun y => Real.exp (h / 2) *
        ((fun y => -(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * y)) +
          fun y => (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * y)) y)
      (Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
          (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * xi))) xi :=
    hbase.congr_deriv (by ring)
  simpa only [Pi.add_apply] using hderiv

theorem hasDerivAt_ccmActualHeadAnchoredCosinePhaseProfile
    (lo hi s xi : ℝ) :
    HasDerivAt (ccmActualHeadAnchoredCosinePhaseProfile lo hi s)
      (ccmActualHeadAnchoredCosinePhaseFirstJet lo hi s xi) xi := by
  let F : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (Real.cos (2 * Real.pi * h * x) - Real.cos (2 * Real.pi * s * x))
  let F' : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
        (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x))
  let bound : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * (|2 * Real.pi * h| + |2 * Real.pi * s|)
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc lo hi)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume lo hi :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc lo hi)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x h‖ ≤ bound h := by
    filter_upwards with h
    intro hh x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      |-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
          (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x)| ≤
        |-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x)| +
          |(2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x)| := abs_add_le _ _
      _ = |2 * Real.pi * h| * |Real.sin (2 * Real.pi * h * x)| +
          |2 * Real.pi * s| * |Real.sin (2 * Real.pi * s * x)| := by
            rw [abs_mul, abs_mul, abs_neg]
      _ ≤ |2 * Real.pi * h| * 1 + |2 * Real.pi * s| * 1 := by
            gcongr <;> exact Real.abs_sin_le_one _
      _ = |2 * Real.pi * h| + |2 * Real.pi * s| := by ring
  have hboundint : IntervalIntegrable bound volume lo hi :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (fun y => F y h) (F' x h) x := by
    filter_upwards with h
    intro hh x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadAnchoredCosinePhase_integrand s h x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadAnchoredCosinePhaseProfile
    ccmActualHeadAnchoredCosinePhaseFirstJet
  simpa only [F, F'] using hmain

theorem hasDerivAt_ccmActualHeadAnchoredCosinePhaseFirstJet
    (lo hi s xi : ℝ) :
    HasDerivAt (ccmActualHeadAnchoredCosinePhaseFirstJet lo hi s)
      (ccmActualHeadAnchoredCosinePhaseSecondJet lo hi s xi) xi := by
  let F : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
        (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x))
  let F' : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x) +
        (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * x))
  let bound : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ((2 * Real.pi * h) ^ 2 + (2 * Real.pi * s) ^ 2)
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc lo hi)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume lo hi :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc lo hi)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x h‖ ≤ bound h := by
    filter_upwards with h
    intro hh x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      |-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x) +
          (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * x)| ≤
        |-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x)| +
          |(2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * x)| :=
        abs_add_le _ _
      _ = (2 * Real.pi * h) ^ 2 * |Real.cos (2 * Real.pi * h * x)| +
          (2 * Real.pi * s) ^ 2 * |Real.cos (2 * Real.pi * s * x)| := by
            rw [abs_mul, abs_mul, abs_neg, abs_sq, abs_sq]
      _ ≤ (2 * Real.pi * h) ^ 2 * 1 + (2 * Real.pi * s) ^ 2 * 1 := by
            gcongr <;> exact Real.abs_cos_le_one _
      _ = (2 * Real.pi * h) ^ 2 + (2 * Real.pi * s) ^ 2 := by ring
  have hboundint : IntervalIntegrable bound volume lo hi :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (fun y => F y h) (F' x h) x := by
    filter_upwards with h
    intro hh x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadAnchoredCosinePhaseFirstJet_integrand s h x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadAnchoredCosinePhaseFirstJet
    ccmActualHeadAnchoredCosinePhaseSecondJet
  simpa only [F, F'] using hmain

theorem ccmActualHeadAnchoredCosinePhaseSecondJet_zero
    (lo hi s : ℝ) :
    ccmActualHeadAnchoredCosinePhaseSecondJet lo hi s 0 =
      4 * Real.pi ^ 2 *
        ((∫ h in lo..hi, Real.exp (h / 2)) * s ^ 2 -
          ∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) := by
  have hA : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2) * h ^ 2)
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * h ^ 2).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2))
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2)).intervalIntegrable _ _
  unfold ccmActualHeadAnchoredCosinePhaseSecondJet
  simp only [mul_zero, Real.cos_zero, mul_one]
  calc
    (∫ h in lo..hi,
      Real.exp (h / 2) * (-((2 * Real.pi * h) ^ 2) + (2 * Real.pi * s) ^ 2)) =
      ∫ h in lo..hi,
        (-4 * Real.pi ^ 2) * (Real.exp (h / 2) * h ^ 2) +
          (4 * Real.pi ^ 2 * s ^ 2) * Real.exp (h / 2) := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring
    _ = (-4 * Real.pi ^ 2) *
          (∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) +
        (4 * Real.pi ^ 2 * s ^ 2) *
          (∫ h in lo..hi, Real.exp (h / 2)) := by
      rw [intervalIntegral.integral_add (hA.const_mul _) (hB.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = 4 * Real.pi ^ 2 *
        ((∫ h in lo..hi, Real.exp (h / 2)) * s ^ 2 -
          ∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) := by ring

theorem ccmActualHeadAnchoredCosinePhaseProfile_secondDeriv_zero
    (lo hi s : ℝ) :
    deriv (deriv (ccmActualHeadAnchoredCosinePhaseProfile lo hi s)) 0 =
      4 * Real.pi ^ 2 *
        ((∫ h in lo..hi, Real.exp (h / 2)) * s ^ 2 -
          ∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) := by
  have hfirst : deriv (ccmActualHeadAnchoredCosinePhaseProfile lo hi s) =
      ccmActualHeadAnchoredCosinePhaseFirstJet lo hi s := by
    funext xi
    exact (hasDerivAt_ccmActualHeadAnchoredCosinePhaseProfile lo hi s xi).deriv
  rw [hfirst]
  rw [(hasDerivAt_ccmActualHeadAnchoredCosinePhaseFirstJet lo hi s 0).deriv]
  exact ccmActualHeadAnchoredCosinePhaseSecondJet_zero lo hi s

/-- Terminal quantile cell anchored at the physical endpoint. Its interval remains oriented. -/
def ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
    (N : ℕ) (T xi : ℝ) : ℝ :=
  ccmActualHeadAnchoredCosinePhaseProfile
    (ccmOutgoingPrimeQuantileBoundary N) T T xi

/-- Full finite completed-head cosine phase: quantile cells plus oriented terminal seam. -/
def ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
    (N : ℕ) (T xi : ℝ) : ℝ :=
  ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi +
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T xi

theorem ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_neg
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T (-xi) =
      ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T xi :=
  ccmActualHeadAnchoredCosinePhaseProfile_neg _ _ _ _

theorem ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_zero
    (N : ℕ) (T : ℝ) :
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T 0 = 0 :=
  ccmActualHeadAnchoredCosinePhaseProfile_zero _ _ _

theorem ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_neg
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T (-xi) =
      ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi := by
  unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_neg,
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_neg]

theorem ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_zero
    (N : ℕ) (T : ℝ) :
    ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T 0 = 0 := by
  unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_zero,
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_zero]
  ring

theorem ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_eq_polar_sub_endpoint
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T xi =
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) *
        Real.cos (2 * Real.pi * T * xi) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let C : ℝ := Real.cos (2 * Real.pi * T * xi)
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi))
      volume b T := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)).intervalIntegrable _ _
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * C)
      volume b T := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * C).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileBoundary_to_eq_massMismatch T N
  unfold ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
    ccmActualHeadAnchoredCosinePhaseProfile
  change (∫ h in b..T,
      Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * xi) - C)) = _
  calc
    (∫ h in b..T,
      Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * xi) - C)) =
      (∫ h in b..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (∫ h in b..T, Real.exp (h / 2) * C) := by
        rw [← intervalIntegral.integral_sub hvar hconst]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
    _ = (∫ h in b..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (∫ h in b..T, Real.exp (h / 2)) * C := by
        rw [intervalIntegral.integral_mul_const]
    _ = (∫ h in b..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * C := by
        rw [hmass]

/-- Orientation-free completed-head characteristic source. The endpoint coefficient is signed
when the quantile boundary overshoots the physical terminal point. -/
theorem ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_eq_characteristicDiscrepancy
    (N : ℕ) (T xi : ℝ) :
    ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi =
      (∫ h in (0 : ℝ)..T,
        Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)) -
      ∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * Real.log n * xi) -
      (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) *
        Real.cos (2 * Real.pi * T * xi) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * Real.cos (2 * Real.pi * h * xi)
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hsplit :
      (∫ h in (0 : ℝ)..T, F h) =
        (∫ h in (0 : ℝ)..b, F h) + ∫ h in b..T, F h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 b)
      (hF.intervalIntegrable (μ := volume) b T)).symm
  unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_eq_characteristicDiscrepancy,
    ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_eq_polar_sub_endpoint]
  change ((∫ h in (0 : ℝ)..b, F h) - _ +
      ((∫ h in b..T, F h) - _)) = _
  change (∫ h in (0 : ℝ)..T, F h) = _ at hsplit
  rw [hsplit]
  ring

theorem integrable_ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_mul_density
    (N : ℕ) (T : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hfinite :=
    integrable_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_mul_density N f
  have hterminal := integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density
    (ccmOutgoingPrimeQuantileBoundary N) T T f
  exact (hfinite.add hterminal).congr
    (Filter.Eventually.of_forall fun xi => by
      simp only [Pi.add_apply]
      unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
        ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
      ring)

/-- Finite quantile cells and the terminal polar seam land on one completed-head phase symbol.
This theorem has no terminal-orientation or completed-error premise. -/
theorem ccmActualHeadOutgoingQuantileCompletedTransport_eq_cosinePhaseSymbol
    (N : ℕ) (T : ℝ) (f : SoninL2) :
    (∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect (Real.log n) f -
            ccmActualHeadTranslationDefect h f)) +
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect T f -
            ccmActualHeadTranslationDefect h f)) =
      2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  have hfinite := ccmActualHeadOutgoingQuantileFiniteBlock_eq_cosinePhaseFiniteSymbol N f
  have hterminal := ccmActualHeadAnchoredTransport_eq_cosinePhaseProfile
    (ccmOutgoingPrimeQuantileBoundary N) T T f
  have hfinInt :=
    integrable_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_mul_density N f
  have htermInt := integrable_ccmActualHeadAnchoredCosinePhaseProfile_mul_density
    (ccmOutgoingPrimeQuantileBoundary N) T T f
  rw [hfinite, hterminal]
  calc
    (2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) +
        2 * ∫ xi : ℝ,
          ccmActualHeadAnchoredCosinePhaseProfile
              (ccmOutgoingPrimeQuantileBoundary N) T T xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 =
      2 * ((∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) +
        ∫ xi : ℝ,
          ccmActualHeadAnchoredCosinePhaseProfile
              (ccmOutgoingPrimeQuantileBoundary N) T T xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by ring
    _ = 2 * ∫ xi : ℝ,
        (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 +
          ccmActualHeadAnchoredCosinePhaseProfile
              (ccmOutgoingPrimeQuantileBoundary N) T T xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
      rw [integral_add hfinInt htermInt]
    _ = 2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
      apply congrArg (fun z : ℝ => 2 * z)
      apply integral_congr_ae
      filter_upwards with xi
      unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
        ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
      ring

theorem ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile_secondDeriv_zero
    (N : ℕ) (T : ℝ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile N T)) 0 =
      4 * Real.pi ^ 2 *
        ((2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * T ^ 2 -
          ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
            Real.exp (h / 2) * h ^ 2) := by
  unfold ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
  rw [ccmActualHeadAnchoredCosinePhaseProfile_secondDeriv_zero]
  rw [integral_exp_half_quantileBoundary_to_eq_massMismatch]

/-- The completed-head symbol's first surviving jet is the exact second moment of the signed
continuous--prime--endpoint characteristic source. The formula is valid through terminal
overshoot because both terminal mass and moment integrals retain their orientation. -/
theorem ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_secondDeriv_zero
    (N : ℕ) (T : ℝ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T)) 0 =
      4 * Real.pi ^ 2 *
        ((∑ n ∈ Finset.range N,
            criticalMellinAtomWeight n * (Real.log n) ^ 2) +
          (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * T ^ 2 -
          ∫ h in (0 : ℝ)..T, Real.exp (h / 2) * h ^ 2) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let A := ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N
  let B := ccmActualHeadAnchoredCosinePhaseProfile b T T
  let A' := ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N
  let B' := ccmActualHeadAnchoredCosinePhaseFirstJet b T T
  let A'' := ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet N
  let B'' := ccmActualHeadAnchoredCosinePhaseSecondJet b T T
  have hfirst :
      deriv (ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N T) =
        fun xi => A' xi + B' xi := by
    funext xi
    have hA := hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi
    have hB := hasDerivAt_ccmActualHeadAnchoredCosinePhaseProfile b T T xi
    unfold ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol
      ccmActualHeadOutgoingQuantileTerminalCosinePhaseProfile
    have hadd : HasDerivAt
        (fun x => ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N x +
          ccmActualHeadAnchoredCosinePhaseProfile b T T x)
        (ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N xi +
          ccmActualHeadAnchoredCosinePhaseFirstJet b T T xi) xi :=
      (hA.add hB).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => by simp only [Pi.add_apply])
    simpa only [A', B', b] using hadd.deriv
  have hsecond : HasDerivAt (fun xi => A' xi + B' xi)
      (A'' 0 + B'' 0) 0 := by
    have hA := hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N 0
    have hB := hasDerivAt_ccmActualHeadAnchoredCosinePhaseFirstJet b T T 0
    have hadd : HasDerivAt
        (fun x => ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N x +
          ccmActualHeadAnchoredCosinePhaseFirstJet b T T x)
        (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSecondJet N 0 +
          ccmActualHeadAnchoredCosinePhaseSecondJet b T T 0) 0 :=
      (hA.add hB).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => by simp only [Pi.add_apply])
    simpa only [A', B', A'', B'', b] using hadd
  have hfinite : A'' 0 =
      4 * Real.pi ^ 2 *
        ((∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        ∫ h in (0 : ℝ)..b, Real.exp (h / 2) * h ^ 2) := by
    have hfirstA : deriv A = A' := by
      funext xi
      exact (hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi).deriv
    have h := ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero N
    change deriv (deriv A) 0 = _ at h
    rw [hfirstA] at h
    rw [(hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFiniteFirstJet N 0).deriv] at h
    simpa only [A'', A', b] using h
  have hterminal : B'' 0 =
      4 * Real.pi ^ 2 *
        ((2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * T ^ 2 -
          ∫ h in b..T, Real.exp (h / 2) * h ^ 2) := by
    rw [show B'' 0 =
        4 * Real.pi ^ 2 *
          ((∫ h in b..T, Real.exp (h / 2)) * T ^ 2 -
            ∫ h in b..T, Real.exp (h / 2) * h ^ 2) by
      exact ccmActualHeadAnchoredCosinePhaseSecondJet_zero b T T]
    rw [show (∫ h in b..T, Real.exp (h / 2)) =
        2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N) by
      simpa only [b] using integral_exp_half_quantileBoundary_to_eq_massMismatch T N]
  have hmoment :
      (∫ h in (0 : ℝ)..T, Real.exp (h / 2) * h ^ 2) =
        (∫ h in (0 : ℝ)..b, Real.exp (h / 2) * h ^ 2) +
          ∫ h in b..T, Real.exp (h / 2) * h ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * h ^ 2).intervalIntegrable (μ := volume) 0 b)
      ((by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * h ^ 2).intervalIntegrable (μ := volume) b T)).symm
  rw [hfirst, hsecond.deriv, hfinite, hterminal, hmoment]
  ring

/-- Exact full spectral normal form of the actual Γ-wall outgoing producer. All finite prime--polar
and terminal transport is one completed-head characteristic symbol; remaining terms are literal
endpoint reserve and higher-Binet Gamma energy. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_completedCosinePhaseSymbol
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        4 * ‖f‖ ^ 2 +
        2 * ∫ xi : ℝ,
          ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol N (2 * a.1) xi *
            ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2 := by
  dsimp only
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hproducer :=
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_quantileTransport a u
  have htransport := ccmActualHeadOutgoingQuantileCompletedTransport_eq_cosinePhaseSymbol
    N (2 * a.1) (f : SoninL2)
  have hendpoint := ccmActualHeadTranslationDefect_two_aperture a f
  dsimp only at hproducer
  change ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u = _ at hproducer
  change (∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect (Real.log n) (f : SoninL2) -
            ccmActualHeadTranslationDefect h (f : SoninL2))) +
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect (2 * a.1) (f : SoninL2) -
            ccmActualHeadTranslationDefect h (f : SoninL2))) = _ at htransport
  change ccmActualHeadTranslationDefect (2 * a.1) (f : SoninL2) =
    2 * ‖f‖ ^ 2 at hendpoint
  dsimp only [f, N] at htransport hendpoint
  linear_combination hproducer + htransport + 2 * hendpoint

end RHTower
