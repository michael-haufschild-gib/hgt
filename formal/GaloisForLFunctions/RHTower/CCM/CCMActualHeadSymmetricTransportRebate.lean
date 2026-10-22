import GaloisForLFunctions.RHTower.CCM.CCMActualHeadGammaAutocorrelationEnergy

/-!
# Coefficient-one symmetric transport for actual CCM heads

For the literal translation defect

`E_f(h) = ‖logTranslation h f - f‖²`,

the usual triangle estimate loses a factor two when moving a polar sample to a nearby prime
anchor. Symmetric anchors avoid that loss. This module proves the exact same-head identity

`E_f(s + r) + E_f(s - r) + J_f(s,r) = 2 E_f(s) + 2 E_f(r)`,

where `J_f(s,r)` is the integral of the product of the two cosine defects against the actual
Fourier-head mass. Consequently `J_f(s,r) ≥ 0`, so a symmetric pair moves with coefficient one
and earns a nonnegative fourth-order joint rebate. No surrogate head, pointwise regularity, or
limiting assumption is used.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace RHTower

/-- Fourth-order rebate earned by transporting a symmetric pair through the same actual head. -/
def ccmActualHeadSymmetricTransportRebate
    (s r : ℝ) (f : SoninL2) : ℝ :=
  ∫ xi : ℝ,
    ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
      (2 - 2 * Real.cos (2 * Real.pi * r * xi))) *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2

theorem integrable_ccmActualHeadSymmetricTransportRebate
    (s r : ℝ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let g : SoninL2 := fourierUnitary f
  have hs := integrable_ccmGammaCosineDefectSpectralDensity s g
  have hrMeas : AEStronglyMeasurable (fun xi : ℝ =>
      2 - 2 * Real.cos (2 * Real.pi * r * xi)) :=
    (by fun_prop : Continuous (fun xi : ℝ =>
      2 - 2 * Real.cos (2 * Real.pi * r * xi))).aestronglyMeasurable
  have hrBound : ∀ᵐ xi : ℝ ∂volume,
      ‖2 - 2 * Real.cos (2 * Real.pi * r * xi)‖ ≤ 4 := by
    filter_upwards with xi
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * r * xi),
        Real.cos_le_one (2 * Real.pi * r * xi)]
  have hmul := Integrable.mul_bdd (c := 4) hs hrMeas hrBound
  exact hmul.congr (Filter.Eventually.of_forall fun xi => by ring)

theorem ccmActualHeadSymmetricTransportRebate_nonneg
    (s r : ℝ) (f : SoninL2) :
    0 ≤ ccmActualHeadSymmetricTransportRebate s r f := by
  unfold ccmActualHeadSymmetricTransportRebate
  apply integral_nonneg
  intro xi
  exact mul_nonneg
    (mul_nonneg
      (by nlinarith [Real.cos_le_one (2 * Real.pi * s * xi)])
      (by nlinarith [Real.cos_le_one (2 * Real.pi * r * xi)]))
    (sq_nonneg _)

/-- Exact coefficient-one symmetric-pair transport law on the literal actual head. -/
theorem ccmActualHeadTranslationDefect_symmetric_pair_add_rebate
    (s r : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect (s + r) f +
        ccmActualHeadTranslationDefect (s - r) f +
        ccmActualHeadSymmetricTransportRebate s r f =
      2 * ccmActualHeadTranslationDefect s f +
        2 * ccmActualHeadTranslationDefect r f := by
  let g : SoninL2 := fourierUnitary f
  have hfg : fourierUnitary.symm g = f := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply f
  have hplus := integrable_ccmGammaCosineDefectSpectralDensity (s + r) g
  have hminus := integrable_ccmGammaCosineDefectSpectralDensity (s - r) g
  have hs := integrable_ccmGammaCosineDefectSpectralDensity s g
  have hr := integrable_ccmGammaCosineDefectSpectralDensity r g
  have hjoint := integrable_ccmActualHeadSymmetricTransportRebate s r f
  have hjointG : Integrable (fun xi : ℝ =>
      ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) := by
    simpa only [g] using hjoint
  rw [← hfg]
  rw [ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ccmActualHeadTranslationDefect_fourierUnitary_symm]
  unfold ccmActualHeadSymmetricTransportRebate
  rw [LinearIsometryEquiv.apply_symm_apply]
  change
    (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2) +
      (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2) +
      (∫ xi : ℝ,
        ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) =
      2 * (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2) +
      2 * (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)
  have hfun :
      (fun xi : ℝ =>
        (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2 +
        (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2 +
        ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) =
      (fun xi : ℝ =>
        2 * ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2) +
        2 * ((2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)) := by
    funext xi
    rw [show 2 * Real.pi * (s + r) * xi =
        2 * Real.pi * s * xi + 2 * Real.pi * r * xi by ring,
      show 2 * Real.pi * (s - r) * xi =
        2 * Real.pi * s * xi - 2 * Real.pi * r * xi by ring,
      Real.cos_add, Real.cos_sub]
    ring
  have hint := congrArg (fun F : ℝ → ℝ => ∫ xi : ℝ, F xi) hfun
  have hpm :
      (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2 +
          (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2) =
        (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2) +
        (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2) := by
    simpa only [Pi.add_apply] using integral_add hplus hminus
  have hleft :
      (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2 +
          (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2 +
          ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
            (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) =
        (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2) +
        (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2) +
        (∫ xi : ℝ,
          ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
            (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) := by
    calc
      _ = (∫ xi : ℝ,
              (2 - 2 * Real.cos (2 * Real.pi * (s + r) * xi)) * ‖g xi‖ ^ 2 +
              (2 - 2 * Real.cos (2 * Real.pi * (s - r) * xi)) * ‖g xi‖ ^ 2) +
            (∫ xi : ℝ,
              ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
                (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) := by
          simpa only [Pi.add_apply] using integral_add (hplus.add hminus) hjointG
      _ = _ := by rw [hpm]
  have hright :
      (∫ xi : ℝ,
          2 * ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2) +
          2 * ((2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)) =
        2 * (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2) +
        2 * (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2) := by
    calc
      _ = (∫ xi : ℝ,
              2 * ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) * ‖g xi‖ ^ 2)) +
            (∫ xi : ℝ,
              2 * ((2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)) := by
          simpa only [Pi.add_apply] using
            integral_add (hs.const_mul 2) (hr.const_mul 2)
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  exact hleft.symm.trans (hint.trans hright)

/-- Symmetric-pair transport inequality obtained by discarding only the explicit joint rebate. -/
theorem ccmActualHeadTranslationDefect_symmetric_pair_le
    (s r : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect (s + r) f +
        ccmActualHeadTranslationDefect (s - r) f ≤
      2 * ccmActualHeadTranslationDefect s f +
        2 * ccmActualHeadTranslationDefect r f := by
  have hid := ccmActualHeadTranslationDefect_symmetric_pair_add_rebate s r f
  have hnonneg := ccmActualHeadSymmetricTransportRebate_nonneg s r f
  linarith

end RHTower
