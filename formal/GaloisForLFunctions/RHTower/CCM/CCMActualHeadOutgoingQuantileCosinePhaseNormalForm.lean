import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer

/-!
# Outgoing-quantile actual-head cosine-phase normal form

Consecutive CCM mass-quantile cells solve global outgoing-polar coverage but leave an oriented
translation current. This module retains that orientation exactly in Fourier space. Each cell is
the spectral average of an even signed cosine-discrepancy profile; finite blocks aggregate before
any absolute-value estimate.

The profile vanishes at frequency zero. Its first surviving jet is its exact weighted second-moment
quadrature error, equivalently a signed moment of the corpus's literal displacement density. Cell
position relative to `log n` classifies the curvature sign, and the completed-error threshold at
`T = log n` is exactly the all-left-cell condition. These are unconditional bridge theorems, not
an RH proof.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem ccmActualHeadTranslationDefect_sub_eq_cosineDifference
    (s h : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect s f - ccmActualHeadTranslationDefect h f =
      ∫ xi : ℝ,
        2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * s * xi)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let g : SoninL2 := fourierUnitary f
  have hfg : fourierUnitary.symm g = f := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply f
  have hs := integrable_ccmGammaCosineDefectSpectralDensity s g
  have hh := integrable_ccmGammaCosineDefectSpectralDensity h g
  rw [← hfg, ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ccmActualHeadTranslationDefect_fourierUnitary_symm,
    LinearIsometryEquiv.apply_symm_apply]
  change
    (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2) -
      (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2) = _
  rw [← integral_sub hs hh]
  apply integral_congr_ae
  filter_upwards with xi
  dsimp only [g]
  ring

def ccmActualHeadOutgoingQuantileCosinePhaseProfile (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) *
      (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * Real.log n * xi))

theorem ccmActualHeadOutgoingQuantileCellTransport_eq_nestedCosinePhase
    (n : ℕ) (f : SoninL2) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        (ccmActualHeadTranslationDefect (Real.log n) f -
          ccmActualHeadTranslationDefect h f)) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (∫ xi : ℝ,
            2 * (Real.cos (2 * Real.pi * h * xi) -
              Real.cos (2 * Real.pi * Real.log n * xi)) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  apply intervalIntegral.integral_congr
  intro h hh
  dsimp only
  rw [ccmActualHeadTranslationDefect_sub_eq_cosineDifference]

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_neg
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadOutgoingQuantileCosinePhaseProfile n (-xi) =
      ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
  apply intervalIntegral.integral_congr
  intro h hh
  dsimp only
  rw [show 2 * Real.pi * h * -xi = -(2 * Real.pi * h * xi) by ring,
    show 2 * Real.pi * Real.log n * -xi =
      -(2 * Real.pi * Real.log n * xi) by ring,
    Real.cos_neg, Real.cos_neg]

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_zero (n : ℕ) :
    ccmActualHeadOutgoingQuantileCosinePhaseProfile n 0 = 0 := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
  simp

theorem integrable_ccmActualHeadOutgoingQuantileCosinePhase_prod
    (n : ℕ) (f : SoninL2) :
    Integrable (Function.uncurry fun h xi : ℝ =>
      Real.exp (h / 2) *
        (2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * Real.log n * xi)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2))
      ((volume.restrict (Ioc
        (ccmOutgoingPrimeQuantileBoundary n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1)))).prod volume) := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let C : ℝ → ℝ := fun h => 4 * Real.exp (h / 2)
  let D : ℝ → ℝ := fun xi => ‖g xi‖ ^ 2
  have hC : Integrable C (volume.restrict (Ioc
      (ccmOutgoingPrimeQuantileBoundary n)
      (ccmOutgoingPrimeQuantileBoundary (n + 1)))) := by
    exact (by fun_prop : Continuous C).integrableOn_Ioc
  have hD : Integrable D := by
    dsimp only [D, g]
    exact integrable_norm_sq (fourierUnitary f)
  have hmajor : Integrable (fun p : ℝ × ℝ => C p.1 * D p.2)
      ((volume.restrict (Ioc
        (ccmOutgoingPrimeQuantileBoundary n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1)))).prod volume) :=
    hC.mul_prod hD
  have hg : StronglyMeasurable g := Lp.stronglyMeasurable (fourierUnitary f)
  have hDmeas : StronglyMeasurable D := hg.norm.pow 2
  have hcoeff : Continuous (fun p : ℝ × ℝ =>
      Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * Real.log n * p.2)))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun h xi : ℝ =>
      Real.exp (h / 2) *
        (2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * Real.log n * xi)) * D xi))
      ((volume.restrict (Ioc
        (ccmOutgoingPrimeQuantileBoundary n)
        (ccmOutgoingPrimeQuantileBoundary (n + 1)))).prod volume) := by
    refine (hcoeff.stronglyMeasurable.aestronglyMeasurable.mul
      (hDmeas.comp_measurable measurable_snd).aestronglyMeasurable).congr ?_
    filter_upwards with p
    change (Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * Real.log n * p.2)))) * D p.2 =
      Real.exp (p.1 / 2) *
        (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * Real.log n * p.2)) * D p.2)
    ring
  apply hmajor.mono' hmeas
  filter_upwards with p
  have hcosh : |Real.cos (2 * Real.pi * p.1 * p.2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hcosn : |Real.cos (2 * Real.pi * Real.log n * p.2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  change ‖Real.exp (p.1 / 2) *
      (2 * (Real.cos (2 * Real.pi * p.1 * p.2) -
        Real.cos (2 * Real.pi * Real.log n * p.2)) * D p.2)‖ ≤
    C p.1 * D p.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hD0]
  dsimp only [C]
  calc
    Real.exp (p.1 / 2) *
        (|2| * |Real.cos (2 * Real.pi * p.1 * p.2) -
          Real.cos (2 * Real.pi * Real.log n * p.2)| * D p.2) ≤
      Real.exp (p.1 / 2) * (2 * 2 * D p.2) := by
        gcongr
        · norm_num
        · exact (abs_sub _ _).trans (by linarith)
    _ = (4 * Real.exp (p.1 / 2)) * D p.2 := by ring

theorem ccmActualHeadOutgoingQuantileCellTransport_eq_cosinePhaseProfile
    (n : ℕ) (f : SoninL2) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        (ccmActualHeadTranslationDefect (Real.log n) f -
          ccmActualHeadTranslationDefect h f)) =
      2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun h xi =>
    Real.exp (h / 2) *
      (2 * (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2)
  have hlohi : lo ≤ hi := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc lo hi)).prod volume) := by
    simpa only [F, lo, hi, g] using
      integrable_ccmActualHeadOutgoingQuantileCosinePhase_prod n f
  have hswap := integral_integral_swap hprod
  have hslicer (xi : ℝ) :
      (∫ h in Ioc lo hi, F h xi) =
        2 * ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hlohi]
    rw [show 2 *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * Real.log n * xi))) * ‖g xi‖ ^ 2 =
        (2 * ‖g xi‖ ^ 2) *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * Real.log n * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [F]
    ring
  rw [ccmActualHeadOutgoingQuantileCellTransport_eq_nestedCosinePhase]
  have houter :
      (∫ h in lo..hi,
        Real.exp (h / 2) *
          (∫ xi : ℝ,
            2 * (Real.cos (2 * Real.pi * h * xi) -
              Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2)) =
        ∫ h in lo..hi, ∫ xi : ℝ, F h xi := by
    apply intervalIntegral.integral_congr
    intro h hh
    dsimp only [F]
    rw [← integral_const_mul]
  change (∫ h in lo..hi,
    Real.exp (h / 2) *
      (∫ xi : ℝ,
        2 * (Real.cos (2 * Real.pi * h * xi) -
          Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2)) = _
  rw [houter, intervalIntegral.integral_of_le hlohi]
  calc
    (∫ h in Ioc lo hi, ∫ xi : ℝ, F h xi) =
        ∫ xi : ℝ, ∫ h in Ioc lo hi, F h xi := hswap
    _ = ∫ xi : ℝ,
        2 * ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖g xi‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with xi
            exact hslicer xi
    _ = 2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖g xi‖ ^ 2 := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with xi
            ring

theorem integrable_ccmActualHeadOutgoingQuantileCosinePhaseProfile_mul_density
    (n : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun h xi =>
    Real.exp (h / 2) *
      (2 * (Real.cos (2 * Real.pi * h * xi) -
        Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2)
  have hlohi : lo ≤ hi := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc lo hi)).prod volume) := by
    simpa only [F, lo, hi, g] using
      integrable_ccmActualHeadOutgoingQuantileCosinePhase_prod n f
  have hslice (xi : ℝ) :
      (∫ h in Ioc lo hi, F h xi) =
        2 * ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hlohi]
    rw [show 2 *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * Real.log n * xi))) * ‖g xi‖ ^ 2 =
        (2 * ‖g xi‖ ^ 2) *
          (∫ h in Ioc lo hi,
            Real.exp (h / 2) *
              (Real.cos (2 * Real.pi * h * xi) -
                Real.cos (2 * Real.pi * Real.log n * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [F]
    ring
  have htwo : Integrable (fun xi : ℝ =>
      2 * ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi * ‖g xi‖ ^ 2) :=
    hprod.integral_prod_right.congr
      (Filter.Eventually.of_forall fun xi => hslice xi)
  have hscale := htwo.const_mul (1 / 2 : ℝ)
  refine hscale.congr (Filter.Eventually.of_forall fun xi => ?_)
  dsimp only [g]
  ring

def ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
    (N : ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi

theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_neg
    (N : ℕ) (xi : ℝ) :
    ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N (-xi) =
      ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadOutgoingQuantileCosinePhaseProfile_neg n xi

theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_zero (N : ℕ) :
    ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N 0 = 0 := by
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  simp [ccmActualHeadOutgoingQuantileCosinePhaseProfile_zero]

theorem integrable_ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_mul_density
    (N : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hsum := integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_ccmActualHeadOutgoingQuantileCosinePhaseProfile_mul_density n f
  exact hsum.congr (Filter.Eventually.of_forall fun xi => by
    unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
    change (∑ n ∈ Finset.range N,
        ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      (∑ n ∈ Finset.range N,
        ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
    rw [Finset.sum_mul])

theorem ccmActualHeadOutgoingQuantileFiniteBlock_eq_cosinePhaseFiniteSymbol
    (N : ℕ) (f : SoninL2) :
    (∑ n ∈ Finset.range N,
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect (Real.log n) f -
            ccmActualHeadTranslationDefect h f)) =
      2 * ∫ xi : ℝ,
        ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  simp_rw [ccmActualHeadOutgoingQuantileCellTransport_eq_cosinePhaseProfile]
  rw [← Finset.mul_sum]
  congr 1
  rw [← MeasureTheory.integral_finsetSum (Finset.range N)
    (fun n _ =>
      integrable_ccmActualHeadOutgoingQuantileCosinePhaseProfile_mul_density n f)]
  apply integral_congr_ae
  filter_upwards with xi
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol
  change (∑ n ∈ Finset.range N,
      ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
    (∑ n ∈ Finset.range N,
      ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  rw [Finset.sum_mul]

def ccmActualHeadOutgoingQuantileCosinePhaseFirstJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
        (2 * Real.pi * Real.log n) *
          Real.sin (2 * Real.pi * Real.log n * xi))

def ccmActualHeadOutgoingQuantileCosinePhaseSecondJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) *
      (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
        (2 * Real.pi * Real.log n) ^ 2 *
          Real.cos (2 * Real.pi * Real.log n * xi))

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhase_integrand
    (n : ℕ) (h xi : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.exp (h / 2) *
        (Real.cos (2 * Real.pi * h * x) -
          Real.cos (2 * Real.pi * Real.log n * x)))
      (Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
          (2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * xi))) xi := by
  have hh : HasDerivAt (fun x : ℝ => 2 * Real.pi * h * x)
      (2 * Real.pi * h) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * h)
  have hs : HasDerivAt (fun x : ℝ => 2 * Real.pi * Real.log n * x)
      (2 * Real.pi * Real.log n) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * Real.log n)
  have hbase := (hh.cos.sub hs.cos).const_mul (Real.exp (h / 2))
  have hderiv : HasDerivAt
      (fun y => Real.exp (h / 2) *
        ((fun x => Real.cos (2 * Real.pi * h * x)) -
          fun x => Real.cos (2 * Real.pi * Real.log n * x)) y)
      (Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * xi) +
          (2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * xi))) xi :=
    hbase.congr_deriv (by ring)
  simpa only [Pi.sub_apply] using hderiv

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFirstJet_integrand
    (n : ℕ) (h xi : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.exp (h / 2) *
        (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
          (2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * x)))
      (Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
          (2 * Real.pi * Real.log n) ^ 2 *
            Real.cos (2 * Real.pi * Real.log n * xi))) xi := by
  have hh : HasDerivAt (fun x : ℝ => 2 * Real.pi * h * x)
      (2 * Real.pi * h) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * h)
  have hs : HasDerivAt (fun x : ℝ => 2 * Real.pi * Real.log n * x)
      (2 * Real.pi * Real.log n) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * Real.log n)
  have hbase := ((hh.sin.const_mul (-(2 * Real.pi * h))).add
    (hs.sin.const_mul (2 * Real.pi * Real.log n))).const_mul
      (Real.exp (h / 2))
  have hderiv : HasDerivAt
      (fun y => Real.exp (h / 2) *
        ((fun y => -(2 * Real.pi * h) *
            Real.sin (2 * Real.pi * h * y)) +
          fun y => (2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * y)) y)
      (Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * xi) +
          (2 * Real.pi * Real.log n) ^ 2 *
            Real.cos (2 * Real.pi * Real.log n * xi))) xi :=
    hbase.congr_deriv (by ring)
  simpa only [Pi.add_apply] using hderiv

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseProfile
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)
      (ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n xi) xi := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let s := Real.log n
  let F : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (Real.cos (2 * Real.pi * h * x) -
        Real.cos (2 * Real.pi * s * x))
  let F' : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
        (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x))
  let bound : ℝ → ℝ := fun h =>
    Real.exp (h / 2) *
      (|2 * Real.pi * h| + |2 * Real.pi * s|)
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
    dsimp only [F', bound, s]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      |-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
          (2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * x)| ≤
        |-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x)| +
          |(2 * Real.pi * Real.log n) *
            Real.sin (2 * Real.pi * Real.log n * x)| := abs_add_le _ _
      _ = |2 * Real.pi * h| * |Real.sin (2 * Real.pi * h * x)| +
          |2 * Real.pi * Real.log n| *
            |Real.sin (2 * Real.pi * Real.log n * x)| := by
              rw [abs_mul, abs_mul, abs_neg]
      _ ≤ |2 * Real.pi * h| * 1 + |2 * Real.pi * Real.log n| * 1 := by
            gcongr <;> exact Real.abs_sin_le_one _
      _ = |2 * Real.pi * h| + |2 * Real.pi * Real.log n| := by ring
  have hboundint : IntervalIntegrable bound volume lo hi :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y h) (F' x h) x := by
    filter_upwards with h
    intro hh x hx
    simpa only [F, F', s] using
      hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhase_integrand n h x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadOutgoingQuantileCosinePhaseProfile
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFirstJet
  simpa only [F, F', lo, hi, s] using hmain

theorem hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFirstJet
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n)
      (ccmActualHeadOutgoingQuantileCosinePhaseSecondJet n xi) xi := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let s := Real.log n
  let F : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-(2 * Real.pi * h) * Real.sin (2 * Real.pi * h * x) +
        (2 * Real.pi * s) * Real.sin (2 * Real.pi * s * x))
  let F' : ℝ → ℝ → ℝ := fun x h =>
    Real.exp (h / 2) *
      (-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x) +
        (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s * x))
  let bound : ℝ → ℝ := fun h =>
    Real.exp (h / 2) *
      ((2 * Real.pi * h) ^ 2 + (2 * Real.pi * s) ^ 2)
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
    dsimp only [F', bound, s]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      |-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x) +
          (2 * Real.pi * Real.log n) ^ 2 *
            Real.cos (2 * Real.pi * Real.log n * x)| ≤
        |-((2 * Real.pi * h) ^ 2) * Real.cos (2 * Real.pi * h * x)| +
          |(2 * Real.pi * Real.log n) ^ 2 *
            Real.cos (2 * Real.pi * Real.log n * x)| := abs_add_le _ _
      _ = (2 * Real.pi * h) ^ 2 * |Real.cos (2 * Real.pi * h * x)| +
          (2 * Real.pi * Real.log n) ^ 2 *
            |Real.cos (2 * Real.pi * Real.log n * x)| := by
              rw [abs_mul, abs_mul, abs_neg, abs_sq, abs_sq]
      _ ≤ (2 * Real.pi * h) ^ 2 * 1 +
          (2 * Real.pi * Real.log n) ^ 2 * 1 := by
            gcongr <;> exact Real.abs_cos_le_one _
      _ = (2 * Real.pi * h) ^ 2 +
          (2 * Real.pi * Real.log n) ^ 2 := by ring
  have hboundint : IntervalIntegrable bound volume lo hi :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc lo hi →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y h) (F' x h) x := by
    filter_upwards with h
    intro hh x hx
    simpa only [F, F', s] using
      hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFirstJet_integrand n h x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadOutgoingQuantileCosinePhaseFirstJet
  unfold ccmActualHeadOutgoingQuantileCosinePhaseSecondJet
  simpa only [F, F', lo, hi, s] using hmain

theorem ccmActualHeadOutgoingQuantileCosinePhaseSecondJet_zero_eq_momentError
    (n : ℕ) :
    ccmActualHeadOutgoingQuantileCosinePhaseSecondJet n 0 =
      4 * Real.pi ^ 2 *
        (criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) * h ^ 2) := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  have hA : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2) * h ^ 2)
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * h ^ 2).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2))
      volume lo hi := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2)).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  unfold ccmActualHeadOutgoingQuantileCosinePhaseSecondJet
  simp only [mul_zero, Real.cos_zero, mul_one]
  change (∫ h in lo..hi,
      Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) +
          (2 * Real.pi * Real.log n) ^ 2)) =
    4 * Real.pi ^ 2 *
      (criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        ∫ h in lo..hi, Real.exp (h / 2) * h ^ 2)
  calc
    (∫ h in lo..hi,
      Real.exp (h / 2) *
        (-((2 * Real.pi * h) ^ 2) +
          (2 * Real.pi * Real.log n) ^ 2)) =
      ∫ h in lo..hi,
        (-4 * Real.pi ^ 2) * (Real.exp (h / 2) * h ^ 2) +
          (4 * Real.pi ^ 2 * (Real.log n) ^ 2) * Real.exp (h / 2) := by
            apply intervalIntegral.integral_congr
            intro h hh
            ring
    _ = (-4 * Real.pi ^ 2) *
          (∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) +
        (4 * Real.pi ^ 2 * (Real.log n) ^ 2) *
          (∫ h in lo..hi, Real.exp (h / 2)) := by
            rw [intervalIntegral.integral_add (hA.const_mul _) (hB.const_mul _),
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    _ = 4 * Real.pi ^ 2 *
        (criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          ∫ h in lo..hi, Real.exp (h / 2) * h ^ 2) := by
            rw [hmass]
            ring

theorem ccmOutgoingPrimeQuantileBoundary_nonneg (N : ℕ) :
    0 ≤ ccmOutgoingPrimeQuantileBoundary N := by
  unfold ccmOutgoingPrimeQuantileBoundary
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  have hP := ccmOutgoingPrimeCumulative_nonneg N
  linarith

theorem ccmActualHeadOutgoingQuantileMomentError_eq_squareDifference
    (n : ℕ) :
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * h ^ 2) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2) := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * (Real.log n) ^ 2)
      volume b0 b1 := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * (Real.log n) ^ 2).intervalIntegrable _ _
  have hsq : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * h ^ 2)
      volume b0 b1 := (by fun_prop : Continuous fun h : ℝ =>
        Real.exp (h / 2) * h ^ 2).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  change criticalMellinAtomWeight n * (Real.log n) ^ 2 -
      (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) =
    ∫ h in b0..b1,
      Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2)
  calc
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) =
      (∫ h in b0..b1, Real.exp (h / 2)) * (Real.log n) ^ 2 -
        (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) := by
          rw [hmass]
    _ = (∫ h in b0..b1, Real.exp (h / 2) * (Real.log n) ^ 2) -
        (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) := by
          rw [intervalIntegral.integral_mul_const]
    _ = ∫ h in b0..b1,
        (Real.exp (h / 2) * (Real.log n) ^ 2 -
          Real.exp (h / 2) * h ^ 2) :=
      (intervalIntegral.integral_sub hconst hsq).symm
    _ = ∫ h in b0..b1,
        Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2) := by
          apply intervalIntegral.integral_congr
          intro h hh
          ring

theorem ccmActualHeadOutgoingQuantileMomentError_eq_displacementMoment
    (n : ℕ) :
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * h ^ 2) =
      ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
        (-(r * (2 * Real.log n + r))) := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let lo := b0 - Real.log n
  let hi := b1 - Real.log n
  let S : Set ℝ := Ioc lo hi
  let G : ℝ → ℝ := fun r =>
    Real.exp ((r + Real.log n) / 2) *
      (-(r * (2 * Real.log n + r)))
  have hleft :
      criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) =
        ∫ h in b0..b1,
          Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2) := by
    simpa only [b0, b1] using
      ccmActualHeadOutgoingQuantileMomentError_eq_squareDifference n
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := b0) (b := b1) G (Real.log n)
  have hlohi : lo ≤ hi := by
    dsimp only [lo, hi, b0, b1]
    exact sub_le_sub_right (ccmOutgoingPrimeQuantileBoundary_mono_step n) _
  calc
    criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * h ^ 2) =
      ∫ h in b0..b1,
        Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2) := by
          simpa only [b0, b1] using hleft
    _ = ∫ h in b0..b1, G (h - Real.log n) := by
      apply intervalIntegral.integral_congr
      intro h hh
      dsimp only [G]
      rw [show (h - Real.log n + Real.log n) / 2 = h / 2 by ring]
      ring
    _ = ∫ r in lo..hi, G r := by
      simpa only [lo, hi, b0, b1] using hshift
    _ = ∫ r in S, G r := by
      rw [intervalIntegral.integral_of_le hlohi]
    _ = ∫ r : ℝ, S.indicator G r := by
      rw [integral_indicator measurableSet_Ioc]
    _ = ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
        (-(r * (2 * Real.log n + r))) := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ S <;>
        simp [ccmOutgoingQuantileDisplacementCellDensity, S, G, lo, hi, b0, b1, hr]

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero
    (n : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 =
      4 * Real.pi ^ 2 *
        (criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) * h ^ 2) := by
  have hfirst : deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n) =
      ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n := by
    funext xi
    exact (hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseProfile n xi).deriv
  rw [hfirst]
  rw [(hasDerivAt_ccmActualHeadOutgoingQuantileCosinePhaseFirstJet n 0).deriv]
  exact ccmActualHeadOutgoingQuantileCosinePhaseSecondJet_zero_eq_momentError n

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_eq_displacementMoment
    (n : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 =
      4 * Real.pi ^ 2 *
        (∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r *
          (-(r * (2 * Real.log n + r)))) := by
  rw [ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero,
    ccmActualHeadOutgoingQuantileMomentError_eq_displacementMoment]

/-- If the arithmetic node lies weakly left of its full mass-quantile cell, the first nonzero
low-frequency jet has nonpositive orientation. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_nonpos_of_node_le_cell
    (n : ℕ)
    (hnode : Real.log n ≤ ccmOutgoingPrimeQuantileBoundary n) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 ≤ 0 := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2)
  have hb : b0 ≤ b1 := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hF : IntervalIntegrable F volume b0 b1 :=
    (by fun_prop : Continuous F).intervalIntegrable _ _
  have hmono : (∫ h in b0..b1, F h) ≤ ∫ _ in b0..b1, 0 := by
    apply intervalIntegral.integral_mono_on hb hF intervalIntegrable_const
    intro h hh
    have hs0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hsh : Real.log n ≤ h := hnode.trans hh.1
    have hdiff : (Real.log n) ^ 2 - h ^ 2 ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hdiff
  have hmoment :
      criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) ≤ 0 := by
    rw [show criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) =
        ∫ h in b0..b1, F h by
      simpa only [F, b0, b1] using
        ccmActualHeadOutgoingQuantileMomentError_eq_squareDifference n]
    simpa using hmono
  rw [ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by simpa only [b0, b1] using hmoment)

/-- If the arithmetic node lies weakly right of its full mass-quantile cell, the first nonzero
low-frequency jet has nonnegative orientation. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_nonneg_of_cell_le_node
    (n : ℕ)
    (hnode : ccmOutgoingPrimeQuantileBoundary (n + 1) ≤ Real.log n) :
    0 ≤ deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ((Real.log n) ^ 2 - h ^ 2)
  have hb : b0 ≤ b1 := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hnonneg : 0 ≤ ∫ h in b0..b1, F h := by
    apply intervalIntegral.integral_nonneg hb
    intro h hh
    have hh0 : 0 ≤ h := (ccmOutgoingPrimeQuantileBoundary_nonneg n).trans hh.1
    have hhs : h ≤ Real.log n := hh.2.trans hnode
    have hdiff : 0 ≤ (Real.log n) ^ 2 - h ^ 2 := by nlinarith
    exact mul_nonneg (Real.exp_pos _).le hdiff
  have hmoment : 0 ≤
      criticalMellinAtomWeight n * (Real.log n) ^ 2 -
        (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) := by
    rw [show criticalMellinAtomWeight n * (Real.log n) ^ 2 -
          (∫ h in b0..b1, Real.exp (h / 2) * h ^ 2) =
        ∫ h in b0..b1, F h by
      simpa only [F, b0, b1] using
        ccmActualHeadOutgoingQuantileMomentError_eq_squareDifference n]
    exact hnonneg
  rw [ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero]
  exact mul_nonneg (by positivity) (by simpa only [b0, b1] using hmoment)

theorem ccmOutgoingPrimeQuantileBoundary_succ_le_log_iff_completedError_ge_threshold
    (n : ℕ) (hn : 0 < n) :
    ccmOutgoingPrimeQuantileBoundary (n + 1) ≤ Real.log n ↔
      2 * (1 - Real.exp (-(Real.log n / 2))) ≤
        criticalMellinCompletedError (Real.log n) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (Real.log n) = (n : ℝ) := Real.exp_log hnreal
  simpa only [hexp, Nat.floor_natCast] using
    quantileBoundary_le_terminal_iff_completedError_ge_threshold (Real.log n)

theorem ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_nonneg_of_completedError
    (n : ℕ) (hn : 0 < n)
    (herror : 2 * (1 - Real.exp (-(Real.log n / 2))) ≤
      criticalMellinCompletedError (Real.log n)) :
    0 ≤ deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseProfile n)) 0 := by
  apply ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_nonneg_of_cell_le_node
  exact (ccmOutgoingPrimeQuantileBoundary_succ_le_log_iff_completedError_ge_threshold
    n hn).mpr herror

end RHTower
