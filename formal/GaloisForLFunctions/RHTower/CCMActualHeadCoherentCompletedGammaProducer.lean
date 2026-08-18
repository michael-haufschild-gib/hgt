import GaloisForLFunctions.RHTower.CCMActualHeadSignedCompletedErrorGammaProducer
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation

/-!
# Phase-coherent completed-error producer on actual Gamma heads

The unsigned reciprocal-Gamma cell envelope diverges because it squares each quantile displacement
before prime and polar phases are assembled.  This module keeps the completed carrier coherent.
For the literal Fourier density `|g(xi)|^2` of an actual form-domain head it proves

`source(a,u) = integral W_a(2 pi xi) |g(xi)|^2 dxi`,

and, after removing the retained Gamma scalar,

`signedProducer(a,u) = integral (W_a(2 pi xi) - 2 gammaRate(0)) |g(xi)|^2 dxi`.

Here `W_a` is the corrected finite-aperture CCM symbol.  Prime atoms, polar continuum, and Gamma
multiplier are combined pointwise before integration.  The proof uses the actual head throughout;
there is no common-clock substitution, absolute prime/polar split, RH premise, computation, or new
postulate.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem ccmArchimedeanMultiplier_eq_two_gammaHardyPhaseRate (xi : ℝ) :
    ccmArchimedeanMultiplier xi = 2 * gammaHardyPhaseRate xi := by
  unfold ccmArchimedeanMultiplier gammaHardyPhaseRate linePt
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + (xi : ℂ) * I) / 2) =
        ((1 / 4 : ℝ) : ℂ) + ((xi / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  ring

theorem ccmActualHeadSymmetricAutocorrelation_fourierUnitary_symm
    (h : ℝ) (g : SoninL2) :
    ccmActualHeadSymmetricAutocorrelation h (fourierUnitary.symm g) =
      ∫ xi : ℝ, Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2 := by
  have hsq : Integrable (fun xi : ℝ => ‖g xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hcos : Integrable
      (fun xi : ℝ => Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2) := by
    have h := Integrable.mul_bdd (c := 1) hsq
      (by exact (by fun_prop : Continuous fun xi : ℝ =>
        Real.cos (2 * Real.pi * h * xi)).aestronglyMeasurable)
      (by
        filter_upwards with xi
        simpa [Real.norm_eq_abs] using
          Real.abs_cos_le_one (2 * Real.pi * h * xi))
    exact h.congr (Filter.Eventually.of_forall fun xi => by ring)
  have hdef := ccmActualHeadTranslationDefect_fourierUnitary_symm h g
  rw [ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation,
    fourierUnitary.symm.norm_map, norm_sq_eq_integral] at hdef
  have hsplit :
      (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * h * xi)) * ‖g xi‖ ^ 2) =
        2 * (∫ xi : ℝ, ‖g xi‖ ^ 2) -
          2 * (∫ xi : ℝ,
            Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2) := by
    calc
      _ = ∫ xi : ℝ,
          (2 * ‖g xi‖ ^ 2 -
            2 * (Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2)) := by
          apply integral_congr_ae
          filter_upwards with xi
          ring
      _ = _ := by
        rw [integral_sub (hsq.const_mul 2) (hcos.const_mul 2),
          integral_const_mul, integral_const_mul]
  rw [hsplit] at hdef
  linarith

lemma integrable_ccmActualHeadPolarCosineJoint
    (T : ℝ) (g : SoninL2) :
    Integrable (Function.uncurry fun h xi : ℝ =>
      2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
  let W : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  let R : ℝ → ℝ := fun xi => ‖g xi‖ ^ 2
  have hW : Integrable W (volume.restrict (Icc (0 : ℝ) T)) := by
    exact (by
      dsimp only [W]
      fun_prop : Continuous W).continuousOn.integrableOn_compact isCompact_Icc
  have hR : Integrable R := by
    dsimp only [R]
    exact (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hmajor : Integrable (Function.uncurry fun h xi : ℝ => W h * R xi)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) :=
    hW.mul_prod hR
  have hscalar : Continuous (fun p : ℝ × ℝ =>
      W p.1 * Real.cos (2 * Real.pi * p.1 * p.2)) := by
    dsimp only [W]
    fun_prop
  have hRmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => R p.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    dsimp only [R]
    exact ((MeasureTheory.Lp.aestronglyMeasurable g).norm.pow 2).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  refine Integrable.mono' hmajor
    (hscalar.aestronglyMeasurable.mul hRmeas) ?_
  filter_upwards with p
  have hW0 : 0 ≤ W p.1 := by dsimp only [W]; positivity
  have hR0 : 0 ≤ R p.2 := by dsimp only [R]; positivity
  dsimp only [Function.uncurry]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hW0,
    abs_of_nonneg hR0]
  calc
    W p.1 * |Real.cos (2 * Real.pi * p.1 * p.2)| * R p.2 ≤
        W p.1 * 1 * R p.2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)) hW0) hR0
    _ = W p.1 * R p.2 := by ring

theorem integral_polarWeight_ccmActualHeadAutocorrelation_fourierUnitary_symm
    (T : ℝ) (g : SoninL2) :
    (∫ h in Icc (0 : ℝ) T,
        2 * Real.cosh (h / 2) *
          ccmActualHeadSymmetricAutocorrelation h (fourierUnitary.symm g)) =
      ∫ xi : ℝ,
        (∫ h in Icc (0 : ℝ) T,
          2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi)) *
            ‖g xi‖ ^ 2 := by
  let K : ℝ → ℝ → ℝ := fun h xi =>
    2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    simpa only [K] using integrable_ccmActualHeadPolarCosineJoint T g
  have hswap := MeasureTheory.integral_integral_swap hK
  calc
    (∫ h in Icc (0 : ℝ) T,
        2 * Real.cosh (h / 2) *
          ccmActualHeadSymmetricAutocorrelation h (fourierUnitary.symm g)) =
        ∫ h in Icc (0 : ℝ) T, ∫ xi : ℝ, K h xi := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with h
          rw [ccmActualHeadSymmetricAutocorrelation_fourierUnitary_symm]
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          dsimp only [K]
          ring
    _ = ∫ xi : ℝ, ∫ h in Icc (0 : ℝ) T, K h xi := hswap
    _ = ∫ xi : ℝ,
        (∫ h in Icc (0 : ℝ) T,
          2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi)) *
            ‖g xi‖ ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          rw [← integral_mul_const]

lemma integrable_ccmActualHeadPrimeCosineDensity (n : ℕ) (g : SoninL2) :
    Integrable (fun xi : ℝ =>
      criticalMellinAtomWeight n *
        Real.cos (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2) := by
  have hsq : Integrable (fun xi : ℝ => ‖g xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hw : 0 ≤ criticalMellinAtomWeight n := criticalMellinAtomWeight_nonneg n
  have h := Integrable.mul_bdd (c := criticalMellinAtomWeight n) hsq
    (by
      exact ((by fun_prop : Continuous fun xi : ℝ =>
        criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * Real.log n * xi))).aestronglyMeasurable)
    (by
      filter_upwards with xi
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      nlinarith [Real.abs_cos_le_one (2 * Real.pi * Real.log n * xi)])
  exact h.congr (Filter.Eventually.of_forall fun xi => by ring)

theorem primeAutocorrelationSum_fourierUnitary_symm
    (a : SuzukiPositiveAperture) (g : SoninL2) :
    (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        criticalMellinAtomWeight n *
          ccmActualHeadSymmetricAutocorrelation
            (Real.log n) (fourierUnitary.symm g)) =
      ∫ xi : ℝ,
        (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          criticalMellinAtomWeight n *
            Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2 := by
  let S := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
  calc
    (∑ n ∈ S, criticalMellinAtomWeight n *
        ccmActualHeadSymmetricAutocorrelation
          (Real.log n) (fourierUnitary.symm g)) =
        ∑ n ∈ S, ∫ xi : ℝ,
          criticalMellinAtomWeight n *
            Real.cos (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [ccmActualHeadSymmetricAutocorrelation_fourierUnitary_symm,
            ← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          ring
    _ = ∫ xi : ℝ, ∑ n ∈ S,
          criticalMellinAtomWeight n *
            Real.cos (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2 := by
          rw [MeasureTheory.integral_finsetSum S fun n _ =>
            integrable_ccmActualHeadPrimeCosineDensity n g]
    _ = ∫ xi : ℝ,
        (∑ n ∈ S, criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * Real.log n * xi)) * ‖g xi‖ ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          rw [Finset.sum_mul]

theorem ccmActualHeadCompletedErrorAutocorrelationCurrent_eq_polarPrimeSymbol
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let g := ccmArchimedeanWeightedToL2 u.1
    ccmActualHeadCompletedErrorAutocorrelationCurrent a
        (ccmArchimedeanFormToAperture a u) =
      ∫ xi : ℝ, polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  let T := 2 * a.1
  let S := Finset.Icc 2 (Nat.floor (Real.exp T))
  let B : ℝ → ℝ := fun xi =>
    ∫ h in Icc (0 : ℝ) T,
      2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi)
  let P : ℝ → ℝ := fun xi =>
    ∑ n ∈ S, criticalMellinAtomWeight n *
      Real.cos (2 * Real.pi * Real.log n * xi)
  have hf : (f : SoninL2) = fourierUnitary.symm g := by
    exact ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm a u
  have hpolar :
      (∫ h in Icc (0 : ℝ) T,
          2 * Real.cosh (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) =
        ∫ xi : ℝ, B xi * ‖g xi‖ ^ 2 := by
    rw [hf]
    simpa only [B] using
      integral_polarWeight_ccmActualHeadAutocorrelation_fourierUnitary_symm T g
  have hprime :
      (∑ n ∈ S, criticalMellinAtomWeight n *
          ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1) =
        ∫ xi : ℝ, P xi * ‖g xi‖ ^ 2 := by
    rw [hf]
    simpa only [S, T, P] using primeAutocorrelationSum_fourierUnitary_symm a g
  have hBint : Integrable (fun xi : ℝ => B xi * ‖g xi‖ ^ 2) := by
    let K : ℝ → ℝ → ℝ := fun h xi =>
      2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2
    have hK : Integrable (Function.uncurry K)
        ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
      simpa only [K] using integrable_ccmActualHeadPolarCosineJoint T g
    exact hK.integral_prod_right.congr (Filter.Eventually.of_forall fun xi => by
      change (∫ h in Icc (0 : ℝ) T,
        2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2) =
          B xi * ‖g xi‖ ^ 2
      rw [← MeasureTheory.integral_mul_const])
  have hPint : Integrable (fun xi : ℝ => P xi * ‖g xi‖ ^ 2) := by
    have hsum := integrable_finsetSum S fun n _ =>
      integrable_ccmActualHeadPrimeCosineDensity n g
    exact hsum.congr (Filter.Eventually.of_forall fun xi => by
      dsimp only [P]
      rw [Finset.sum_mul])
  have hBsymbol (xi : ℝ) : 2 * B xi = polarMultiplier a.1 (2 * Real.pi * xi) := by
    rw [polarMultiplier_eq_cosineTransform a.property.le]
    dsimp only [B, T]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    congr 2
    funext h
    congr 2
    ring
  have hPsymbol (xi : ℝ) :
      2 * P xi = criticalMellinPrimeCosineModule a.1 (2 * Real.pi * xi) := by
    unfold criticalMellinPrimeCosineModule
    dsimp only [P, S, T]
    congr 2
    funext n
    congr 2
    ring
  have hBscale :
      2 * (∫ xi : ℝ, B xi * ‖g xi‖ ^ 2) =
        ∫ xi : ℝ, (2 * B xi) * ‖g xi‖ ^ 2 := by
    rw [← integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with xi
    ring
  have hPscale :
      2 * (∫ xi : ℝ, P xi * ‖g xi‖ ^ 2) =
        ∫ xi : ℝ, (2 * P xi) * ‖g xi‖ ^ 2 := by
    rw [← integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with xi
    ring
  dsimp only
  change ccmActualHeadCompletedErrorAutocorrelationCurrent a f = _
  unfold ccmActualHeadCompletedErrorAutocorrelationCurrent
  dsimp only [T, S] at hpolar hprime ⊢
  rw [hpolar, hprime]
  calc
    2 * (∫ xi : ℝ, B xi * ‖g xi‖ ^ 2) -
          2 * (∫ xi : ℝ, P xi * ‖g xi‖ ^ 2) =
        (∫ xi : ℝ, (2 * B xi) * ‖g xi‖ ^ 2) -
          ∫ xi : ℝ, (2 * P xi) * ‖g xi‖ ^ 2 := by
            rw [hBscale, hPscale]
    _ = ∫ xi : ℝ,
        ((2 * B xi) * ‖g xi‖ ^ 2 - (2 * P xi) * ‖g xi‖ ^ 2) := by
          rw [integral_sub]
          · exact (hBint.const_mul 2).congr
              (Filter.Eventually.of_forall fun xi => by ring)
          · exact (hPint.const_mul 2).congr
              (Filter.Eventually.of_forall fun xi => by ring)
    _ = ∫ xi : ℝ,
        polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with xi
          rw [hBsymbol, hPsymbol]
          unfold polarPrimeStieltjesSymbol
          ring

theorem integrable_polarPrimeStieltjesSymbol_mul_actualHeadDensity
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let g := ccmArchimedeanWeightedToL2 u.1
    Integrable (fun xi : ℝ =>
      polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
  let g := ccmArchimedeanWeightedToL2 u.1
  let T := 2 * a.1
  let S := Finset.Icc 2 (Nat.floor (Real.exp T))
  let B : ℝ → ℝ := fun xi =>
    ∫ h in Icc (0 : ℝ) T,
      2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi)
  let P : ℝ → ℝ := fun xi =>
    ∑ n ∈ S, criticalMellinAtomWeight n *
      Real.cos (2 * Real.pi * Real.log n * xi)
  have hBint : Integrable (fun xi : ℝ => B xi * ‖g xi‖ ^ 2) := by
    let K : ℝ → ℝ → ℝ := fun h xi =>
      2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2
    have hK : Integrable (Function.uncurry K)
        ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
      simpa only [K] using integrable_ccmActualHeadPolarCosineJoint T g
    exact hK.integral_prod_right.congr (Filter.Eventually.of_forall fun xi => by
      change (∫ h in Icc (0 : ℝ) T,
        2 * Real.cosh (h / 2) * Real.cos (2 * Real.pi * h * xi) * ‖g xi‖ ^ 2) =
          B xi * ‖g xi‖ ^ 2
      rw [← MeasureTheory.integral_mul_const])
  have hPint : Integrable (fun xi : ℝ => P xi * ‖g xi‖ ^ 2) := by
    have hsum := integrable_finsetSum S fun n _ =>
      integrable_ccmActualHeadPrimeCosineDensity n g
    exact hsum.congr (Filter.Eventually.of_forall fun xi => by
      dsimp only [P]
      rw [Finset.sum_mul])
  have hBsymbol (xi : ℝ) : 2 * B xi = polarMultiplier a.1 (2 * Real.pi * xi) := by
    rw [polarMultiplier_eq_cosineTransform a.property.le]
    dsimp only [B, T]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    congr 2
    funext h
    congr 2
    ring
  have hPsymbol (xi : ℝ) :
      2 * P xi = criticalMellinPrimeCosineModule a.1 (2 * Real.pi * xi) := by
    unfold criticalMellinPrimeCosineModule
    dsimp only [P, S, T]
    congr 2
    funext n
    congr 2
    ring
  have hpolar : Integrable (fun xi : ℝ =>
      polarMultiplier a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) :=
    (hBint.const_mul 2).congr (Filter.Eventually.of_forall fun xi => by
      change 2 * (B xi * ‖g xi‖ ^ 2) =
        polarMultiplier a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2
      rw [← hBsymbol xi]
      ring)
  have hprime : Integrable (fun xi : ℝ =>
      criticalMellinPrimeCosineModule a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) :=
    (hPint.const_mul 2).congr (Filter.Eventually.of_forall fun xi => by
      change 2 * (P xi * ‖g xi‖ ^ 2) =
        criticalMellinPrimeCosineModule a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2
      rw [← hPsymbol xi]
      ring)
  refine (hpolar.sub hprime).congr (Filter.Eventually.of_forall fun xi => ?_)
  change polarMultiplier a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 -
      criticalMellinPrimeCosineModule a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 =
    polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2
  unfold polarPrimeStieltjesSymbol
  ring

theorem gammaScalar_add_actualHeadAutocorrelationEnergy_eq_symbol
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let g := ccmArchimedeanWeightedToL2 u.1
    2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) =
      ∫ xi : ℝ,
        2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2 := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  have henergy := ccmActualHeadGammaAutocorrelationEnergy_formDomain a u
  have hnorm : ‖f‖ = ‖g‖ := norm_ccmArchimedeanFormToAperture a u
  have hcoe := ccmArchimedeanWeightedToL2_coeFn u.1
  have harch := ccmArchimedean_form_eq_domainNorm_add_scalar u.1
  dsimp only
  change 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
      ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) = _
  rw [henergy, hnorm]
  calc
    2 * gammaHardyPhaseRate 0 * ‖g‖ ^ 2 + (‖u‖ ^ 2 - ‖g‖ ^ 2) =
        ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) * ‖g‖ ^ 2 := by
          rw [show ‖u‖ = ‖u.1‖ by rfl]
          ring
    _ = ∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(u.1 : ℝ → ℂ) xi‖ ^ 2 := harch.symm
    _ = ∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖g xi‖ ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcoe] with xi hxi
          rw [hxi]

def ccmActualHeadCoherentCompletedGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let g := ccmArchimedeanWeightedToL2 u.1
  ∫ xi : ℝ, correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2

theorem ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadCoherentCompletedGammaProducer a u = ccmRestrictedWeilSourceQuadratic a u := by
  let g := ccmArchimedeanWeightedToL2 u.1
  have hgamma := gammaScalar_add_actualHeadAutocorrelationEnergy_eq_symbol a u
  have hcurrent :=
    ccmActualHeadCompletedErrorAutocorrelationCurrent_eq_polarPrimeSymbol a u
  have hgammaInt : Integrable (fun xi : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
    have hcoe := ccmArchimedeanWeightedToL2_coeFn u.1
    exact (integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1).congr
      (by
        filter_upwards [hcoe] with xi hxi
        rw [hxi])
  have hcurrentInt : Integrable (fun xi : ℝ =>
      polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) :=
    integrable_polarPrimeStieltjesSymbol_mul_actualHeadDensity a u
  rw [← ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer_eq_sourceQuadratic]
  unfold ccmActualHeadCoherentCompletedGammaProducer
    ccmRestrictedWeilActualHeadCompletedAutocorrelationProducer
  dsimp only [g] at hgamma hcurrent hgammaInt hcurrentInt ⊢
  rw [hgamma, hcurrent, ← integral_add hgammaInt hcurrentInt]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with xi
  rw [correctedCCMSymbol, ccmArchimedeanMultiplier_eq_two_gammaHardyPhaseRate]
  ring

def ccmActualHeadCoherentSignedCompletedGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let g := ccmArchimedeanWeightedToL2 u.1
  ∫ xi : ℝ,
    (correctedCCMSymbol a.1 (2 * Real.pi * xi) - 2 * gammaHardyPhaseRate 0) *
      ‖g xi‖ ^ 2

theorem ccmActualHeadCoherentSignedCompletedGammaProducer_eq_signedCompletedErrorGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadCoherentSignedCompletedGammaProducer a u =
      ccmActualHeadSignedCompletedErrorGammaProducer a u := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  have hcoherent := ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic a u
  have hfullInt : Integrable (fun xi : ℝ =>
      correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
    have hgammaInt : Integrable (fun xi : ℝ =>
        2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2) := by
      have hcoe := ccmArchimedeanWeightedToL2_coeFn u.1
      exact (integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1).congr
        (by
          filter_upwards [hcoe] with xi hxi
          rw [hxi])
    have hcurrentInt := integrable_polarPrimeStieltjesSymbol_mul_actualHeadDensity a u
    exact (hgammaInt.add hcurrentInt).congr (Filter.Eventually.of_forall fun xi => by
      change 2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖g xi‖ ^ 2 +
          polarPrimeStieltjesSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2 =
        correctedCCMSymbol a.1 (2 * Real.pi * xi) * ‖g xi‖ ^ 2
      rw [correctedCCMSymbol, ccmArchimedeanMultiplier_eq_two_gammaHardyPhaseRate]
      ring)
  have hsq : Integrable (fun xi : ℝ => ‖g xi‖ ^ 2) :=
    (MeasureTheory.Lp.memLp g).integrable_norm_pow (by norm_num)
  have hnorm : ‖f‖ = ‖g‖ := norm_ccmArchimedeanFormToAperture a u
  rw [ccmActualHeadSignedCompletedErrorGammaProducer_eq_source_sub_scalar]
  unfold ccmActualHeadCoherentSignedCompletedGammaProducer
  dsimp only [g] at hcoherent hfullInt hsq hnorm ⊢
  rw [← hcoherent]
  unfold ccmActualHeadCoherentCompletedGammaProducer
  dsimp only [g]
  rw [hnorm, norm_sq_eq_integral, ← integral_const_mul,
    ← integral_sub hfullInt (hsq.const_mul (2 * gammaHardyPhaseRate 0))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with xi
  ring

/-- Literal canonical reverse-prime control is exactly positivity of the phase-coherent completed
Gamma producer on that same finite Gamma--Slepian head. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_coherentCompletedGamma_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmActualHeadCoherentCompletedGammaProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg,
    ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic]

/-- **RH-bearing finite-head producer.** The reverse-prime inequality is precisely the signed
spectral average of the fully completed CCM symbol against the actual canonical-head density.
No prime, polar, or Gamma term has been estimated separately. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_correctedSymbolAverage_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ∫ xi : ℝ,
        correctedCCMSymbol a.1 (2 * Real.pi * xi) *
          ‖ccmArchimedeanWeightedToL2
            (ccmRestrictedWeilCanonicalGroundHead a n).1 xi‖ ^ 2 := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_coherentCompletedGamma_nonneg]
  rfl

/-- Pointwise positivity of the completed symbol is a sufficient, cancellation-preserving signed
control theorem for every literal canonical head at the given aperture. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_of_correctedSymbol_nonneg
    (a : SuzukiPositiveAperture)
    (hsymbol : ∀ xi : ℝ, 0 ≤ correctedCCMSymbol a.1 (2 * Real.pi * xi))
    (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_correctedSymbolAverage_nonneg]
  apply integral_nonneg
  intro xi
  exact mul_nonneg (hsymbol xi) (sq_nonneg _)

end RHTower
