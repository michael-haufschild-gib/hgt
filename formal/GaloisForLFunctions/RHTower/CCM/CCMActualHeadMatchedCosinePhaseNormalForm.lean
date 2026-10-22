import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedSignedControlProducer

/-!
# Matched symmetric actual-head cosine-phase normal form

This module isolates the exact spectral carrier left by mass-matching a symmetric
prime translation against its polar cell.  The residual is not phase-free: it is
the arithmetic cosine `cos (2π log(n) ξ)` paired with a nonnegative even radial
profile.  In particular, the coefficient is exactly `-2`.

The result is an unconditional bridge theorem.  It makes no positivity claim and
does not prove RH; it identifies the phase information any surviving positivity
mechanism must control.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem ccmActualHeadSymmetricTransportRebate_sub_two_translationDefect_eq_cosinePhase
    (s r : ℝ) (f : SoninL2) :
    ccmActualHeadSymmetricTransportRebate s r f -
        2 * ccmActualHeadTranslationDefect r f =
      ∫ xi : ℝ,
        (-2 * Real.cos (2 * Real.pi * s * xi) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let g : SoninL2 := fourierUnitary f
  have hfg : fourierUnitary.symm g = f := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply f
  have hr := integrable_ccmGammaCosineDefectSpectralDensity r g
  have hj : Integrable (fun xi : ℝ =>
      ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) := by
    simpa only [g] using integrable_ccmActualHeadSymmetricTransportRebate s r f
  rw [← hfg, ccmActualHeadTranslationDefect_fourierUnitary_symm]
  unfold ccmActualHeadSymmetricTransportRebate
  rw [LinearIsometryEquiv.apply_symm_apply]
  change
    (∫ xi : ℝ,
        ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) -
      2 * (∫ xi : ℝ,
        (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2) = _
  calc
    _ = (∫ xi : ℝ,
          ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
            (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) -
        ((∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2) +
        (∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)) := by ring
    _ = (∫ xi : ℝ,
          ((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
            (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2) -
        ∫ xi : ℝ,
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2 +
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2 := by
            rw [integral_add hr hr]
    _ = ∫ xi : ℝ,
        (((2 - 2 * Real.cos (2 * Real.pi * s * xi)) *
            (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2 -
          ((2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2 +
            (2 - 2 * Real.cos (2 * Real.pi * r * xi)) * ‖g xi‖ ^ 2)) := by
              simpa only [Pi.add_apply] using (integral_sub hj (hr.add hr)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xi
      ring

theorem ccmActualHeadMatchedSymmetricCellResidual_eq_nestedCosinePhase
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedSymmetricCellResidual n f =
      ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
        Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          (∫ xi : ℝ,
            (-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  unfold ccmActualHeadMatchedSymmetricCellResidual
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [show Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ccmActualHeadSymmetricTransportRebate (Real.log n) r f -
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect r f =
      Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        (ccmActualHeadSymmetricTransportRebate (Real.log n) r f -
          2 * ccmActualHeadTranslationDefect r f) by ring,
    ccmActualHeadSymmetricTransportRebate_sub_two_translationDefect_eq_cosinePhase]

def ccmActualHeadMatchedCosinePhaseProfile (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
      (2 - 2 * Real.cos (2 * Real.pi * r * xi))

theorem ccmActualHeadMatchedCosinePhaseProfile_nonneg (n : ℕ) (xi : ℝ) :
    0 ≤ ccmActualHeadMatchedCosinePhaseProfile n xi := by
  unfold ccmActualHeadMatchedCosinePhaseProfile
  apply intervalIntegral.integral_nonneg
    (ccmActualHeadMatchedPrimePolarRadius_nonneg n)
  intro r hr
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
    (by nlinarith [Real.cos_le_one (2 * Real.pi * r * xi)])

theorem ccmActualHeadMatchedCosinePhaseProfile_neg (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedCosinePhaseProfile n (-xi) =
      ccmActualHeadMatchedCosinePhaseProfile n xi := by
  unfold ccmActualHeadMatchedCosinePhaseProfile
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [show 2 * Real.pi * r * -xi = -(2 * Real.pi * r * xi) by ring,
    Real.cos_neg]

theorem ccmActualHeadMatchedCosinePhaseProfile_zero (n : ℕ) :
    ccmActualHeadMatchedCosinePhaseProfile n 0 = 0 := by
  unfold ccmActualHeadMatchedCosinePhaseProfile
  simp

theorem integrable_ccmActualHeadMatchedCosinePhase_prod
    (n : ℕ) (f : SoninL2) :
    Integrable (Function.uncurry fun r xi : ℝ =>
      Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ((-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2))
      ((volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))).prod
        volume) := by
  let A : ℝ := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let C : ℝ → ℝ := fun r => 8 * A * Real.cosh (r / 2)
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
      A * Real.cosh (p.1 / 2) *
        (-2 * Real.cos (2 * Real.pi * Real.log n * p.2) *
          (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun r xi : ℝ =>
      A * Real.cosh (r / 2) *
        ((-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * D xi))
      ((volume.restrict (Ioc (0 : ℝ) (ccmActualHeadMatchedPrimePolarRadius n))).prod
        volume) := by
    refine (hcoeff.stronglyMeasurable.aestronglyMeasurable.mul
      (hDmeas.comp_measurable measurable_snd).aestronglyMeasurable).congr ?_
    filter_upwards with p
    change (A * Real.cosh (p.1 / 2) *
        (-2 * Real.cos (2 * Real.pi * Real.log n * p.2) *
          (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)))) * D p.2 =
      A * Real.cosh (p.1 / 2) *
        ((-2 * Real.cos (2 * Real.pi * Real.log n * p.2) *
          (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2))) * D p.2)
    ring
  apply hmajor.mono' hmeas
  filter_upwards with p
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hcosh : 0 ≤ Real.cosh (p.1 / 2) := (Real.cosh_pos _).le
  have hcos : |Real.cos (2 * Real.pi * Real.log n * p.2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hdef0 : 0 ≤ 2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2) := by
    nlinarith [Real.cos_le_one (2 * Real.pi * p.1 * p.2)]
  have hdef4 : 2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2) ≤ 4 := by
    nlinarith [Real.neg_one_le_cos (2 * Real.pi * p.1 * p.2)]
  change ‖A * Real.cosh (p.1 / 2) *
      ((-2 * Real.cos (2 * Real.pi * Real.log n * p.2) *
        (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2))) * D p.2)‖ ≤
    C p.1 * D p.2
  rw [Real.norm_eq_abs]
  have hD0 : 0 ≤ D p.2 := by dsimp only [D]; positivity
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA,
    abs_of_nonneg hcosh, abs_neg, abs_of_nonneg hdef0,
    abs_of_nonneg hD0]
  norm_num
  dsimp only [C]
  calc
    A * Real.cosh (p.1 / 2) *
        (2 * |Real.cos (2 * Real.pi * Real.log n * p.2)| *
          (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)) * D p.2) ≤
      A * Real.cosh (p.1 / 2) * (2 * 1 * 4 * D p.2) := by
        gcongr
    _ = (8 * A * Real.cosh (p.1 / 2)) * D p.2 := by ring

theorem ccmActualHeadMatchedSymmetricCellResidual_eq_cosinePhaseProfile
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedSymmetricCellResidual n f =
      -2 * ∫ xi : ℝ,
        Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun r xi =>
    A * Real.cosh (r / 2) *
      ((-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2)
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) ρ)).prod volume) := by
    simpa only [F, ρ, A, g] using
      integrable_ccmActualHeadMatchedCosinePhase_prod n f
  have hswap := integral_integral_swap hprod
  have hslicer (xi : ℝ) :
      (∫ r in Ioc (0 : ℝ) ρ, F r xi) =
        -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadMatchedCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hρ]
    rw [show -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          (∫ r in Ioc (0 : ℝ) ρ,
            Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2 =
        (-2 * Real.cos (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2) *
          (∫ r in Ioc (0 : ℝ) ρ,
            Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [F, A]
    ring
  rw [ccmActualHeadMatchedSymmetricCellResidual_eq_nestedCosinePhase]
  have houter :
      (∫ r in (0 : ℝ)..ρ,
        A * Real.cosh (r / 2) *
          (∫ xi : ℝ,
            (-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2)) =
        ∫ r in (0 : ℝ)..ρ, ∫ xi : ℝ, F r xi := by
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only [F]
    rw [← integral_const_mul]
  change (∫ r in (0 : ℝ)..ρ,
    A * Real.cosh (r / 2) *
      (∫ xi : ℝ,
        (-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2)) = _
  rw [houter]
  rw [intervalIntegral.integral_of_le hρ]
  calc
    (∫ r in Ioc (0 : ℝ) ρ, ∫ xi : ℝ, F r xi) =
        ∫ xi : ℝ, ∫ r in Ioc (0 : ℝ) ρ, F r xi := hswap
    _ = ∫ xi : ℝ,
        -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with xi
            exact hslicer xi
    _ = -2 * ∫ xi : ℝ,
        Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with xi
            ring

theorem integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density
    (n : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  let F : ℝ → ℝ → ℝ := fun r xi =>
    A * Real.cosh (r / 2) *
      ((-2 * Real.cos (2 * Real.pi * Real.log n * xi) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2)
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) ρ)).prod volume) := by
    simpa only [F, ρ, A, g] using
      integrable_ccmActualHeadMatchedCosinePhase_prod n f
  have hslice (xi : ℝ) :
      (∫ r in Ioc (0 : ℝ) ρ, F r xi) =
        -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi * ‖g xi‖ ^ 2 := by
    unfold ccmActualHeadMatchedCosinePhaseProfile
    rw [intervalIntegral.integral_of_le hρ]
    rw [show -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
          (∫ r in Ioc (0 : ℝ) ρ,
            Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) * ‖g xi‖ ^ 2 =
        (-2 * Real.cos (2 * Real.pi * Real.log n * xi) * ‖g xi‖ ^ 2) *
          (∫ r in Ioc (0 : ℝ) ρ,
            Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
              (2 - 2 * Real.cos (2 * Real.pi * r * xi))) by ring]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [F, A]
    ring
  have hneg : Integrable (fun xi : ℝ =>
      -2 * Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi * ‖g xi‖ ^ 2) :=
    hprod.integral_prod_right.congr
      (Filter.Eventually.of_forall fun xi => hslice xi)
  have hscale := hneg.const_mul (-(1 / 2 : ℝ))
  refine hscale.congr (Filter.Eventually.of_forall fun xi => ?_)
  dsimp only [g]
  ring

/-- Aggregate signed phase symbol for a finite family of mass-matched prime--polar cells. -/
def ccmActualHeadMatchedCosinePhaseFiniteSymbol
    (F : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ n ∈ F,
    Real.cos (2 * Real.pi * Real.log n * xi) *
      ccmActualHeadMatchedCosinePhaseProfile n xi

theorem integrable_ccmActualHeadMatchedCosinePhaseFiniteSymbol_mul_density
    (F : Finset ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadMatchedCosinePhaseFiniteSymbol F xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  have hsum := integrable_finsetSum F fun n _ =>
    integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density n f
  exact hsum.congr (Filter.Eventually.of_forall fun xi => by
    unfold ccmActualHeadMatchedCosinePhaseFiniteSymbol
    change (∑ n ∈ F,
        (Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      (∑ n ∈ F,
        Real.cos (2 * Real.pi * Real.log n * xi) *
          ccmActualHeadMatchedCosinePhaseProfile n xi) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
    rw [Finset.sum_mul])

theorem ccmActualHeadMatchedCosinePhaseFiniteSymbol_neg
    (F : Finset ℕ) (xi : ℝ) :
    ccmActualHeadMatchedCosinePhaseFiniteSymbol F (-xi) =
      ccmActualHeadMatchedCosinePhaseFiniteSymbol F xi := by
  unfold ccmActualHeadMatchedCosinePhaseFiniteSymbol
  apply Finset.sum_congr rfl
  intro n hn
  rw [show 2 * Real.pi * Real.log n * -xi =
      -(2 * Real.pi * Real.log n * xi) by ring,
    Real.cos_neg, ccmActualHeadMatchedCosinePhaseProfile_neg]

theorem ccmActualHeadMatchedCosinePhaseFiniteSymbol_zero
    (F : Finset ℕ) :
    ccmActualHeadMatchedCosinePhaseFiniteSymbol F 0 = 0 := by
  unfold ccmActualHeadMatchedCosinePhaseFiniteSymbol
  simp [ccmActualHeadMatchedCosinePhaseProfile_zero]

/-- A finite matched symmetric block is one spectral average against the aggregate signed phase
symbol.  No atomwise positivity is discarded or introduced. -/
theorem ccmActualHeadMatchedSymmetricFiniteBlock_eq_cosinePhaseFiniteSymbol
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedSymmetricFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedCosinePhaseFiniteSymbol F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  unfold ccmActualHeadMatchedSymmetricFiniteBlock
  simp_rw [ccmActualHeadMatchedSymmetricCellResidual_eq_cosinePhaseProfile]
  rw [← Finset.mul_sum]
  congr 1
  rw [← MeasureTheory.integral_finsetSum F
    (fun n _ => integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density n f)]
  apply integral_congr_ae
  filter_upwards with xi
  unfold ccmActualHeadMatchedCosinePhaseFiniteSymbol
  change (∑ n ∈ F,
      (Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
    (∑ n ∈ F,
      Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  rw [Finset.sum_mul]

end RHTower
