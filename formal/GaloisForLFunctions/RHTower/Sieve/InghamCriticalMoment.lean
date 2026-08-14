import GaloisForLFunctions.RHTower.Sieve.InghamPoleRegularizedDetector
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Critical-line coefficient-three moment for Ingham's detector

The exponent three in Ingham's density theorem starts with one exact Hölder pairing.  On a finite
height interval, put

`f_X(t) = ζ(1/2+it) M_X(1/2+it) - 1`.

Then

`∫ |f_X|^(4/3) ≤ 2^(1/3) (∫ |ζ|^4)^(1/3) (∫ |M_X|^2)^(2/3)
                    + 2^(1/3) · length`.

This file proves that inequality for the actual Riemann zeta function and the actual finite Möbius
mollifier.  Compact-interval integrability is discharged from continuity; no moment estimate is
assumed.  The still-separate hard steps are quantitative bounds for the two moments and Gabriel
interpolation from this critical-line estimate to the interior of the density rectangle.
-/

open Complex MeasureTheory Set
open scoped ENNReal NNReal

namespace RHTower.Sieve

noncomputable section

/-- A continuous function belongs to every `L^p` on a compact real interval. -/
private theorem memLp_of_continuous_Icc {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (U V : ℝ) {f : ℝ → E} (hf : Continuous f) :
    MemLp f p (volume.restrict (Icc U V)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc U V)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- The exact scalar convexity constant used to separate the constant term in `|z-1|^(4/3)`. -/
theorem rpow_four_thirds_add_one_le (x : ℝ) (hx : 0 ≤ x) :
    (x + 1) ^ ((4 : ℝ) / 3) ≤
      (2 : ℝ) ^ ((1 : ℝ) / 3) * (x ^ ((4 : ℝ) / 3) + 1) := by
  lift x to ℝ≥0 using hx with x
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow x 1
    (show (1 : ℝ) ≤ 4 / 3 by norm_num)
  norm_num at h ⊢
  exact_mod_cast h

/-- Hölder with exponents `3` and `3/2`: the `4/3` product moment is priced by fourth and second
moments.  Continuity closes every integrability obligation on the compact interval. -/
theorem integral_norm_mul_rpow_four_thirds_le
    {F M : ℝ → ℂ} (hF : Continuous F) (hM : Continuous M) (U V : ℝ) :
    ∫ t in Icc U V, (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3) ≤
      (∫ t in Icc U V, ‖F t‖ ^ (4 : ℝ)) ^ ((1 : ℝ) / 3) *
        (∫ t in Icc U V, ‖M t‖ ^ (2 : ℝ)) ^ ((2 : ℝ) / 3) := by
  let f : ℝ → ℝ := fun t => ‖F t‖ ^ ((4 : ℝ) / 3)
  let g : ℝ → ℝ := fun t => ‖M t‖ ^ ((4 : ℝ) / 3)
  have hfcont : Continuous f := hF.norm.rpow_const (fun _ => Or.inr (by norm_num))
  have hgcont : Continuous g := hM.norm.rpow_const (fun _ => Or.inr (by norm_num))
  have hfmem : MemLp f (ENNReal.ofReal (3 : ℝ)) (volume.restrict (Icc U V)) :=
    memLp_of_continuous_Icc _ U V hfcont
  have hgmem : MemLp g (ENNReal.ofReal ((3 : ℝ) / 2)) (volume.restrict (Icc U V)) :=
    memLp_of_continuous_Icc _ U V hgcont
  have hpq : (3 : ℝ).HolderConjugate ((3 : ℝ) / 2) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (μ := volume.restrict (Icc U V))
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.Eventually.of_forall fun _ => by positivity)
    hfmem hgmem
  have hleft : (fun t => f t * g t) =
      fun t => (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3) := by
    funext t
    exact (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm
  have hFpow : (fun t => f t ^ (3 : ℝ)) = fun t => ‖F t‖ ^ (4 : ℝ) := by
    funext t
    change (‖F t‖ ^ ((4 : ℝ) / 3)) ^ (3 : ℝ) = ‖F t‖ ^ (4 : ℝ)
    rw [← Real.rpow_mul (norm_nonneg (F t))]
    norm_num
  have hMpow : (fun t => g t ^ ((3 : ℝ) / 2)) = fun t => ‖M t‖ ^ (2 : ℝ) := by
    funext t
    change (‖M t‖ ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = ‖M t‖ ^ (2 : ℝ)
    rw [← Real.rpow_mul (norm_nonneg (M t))]
    norm_num
  rw [hleft, hFpow, hMpow] at h
  norm_num at h ⊢
  exact h

/-- Exact coefficient-three error inequality for arbitrary continuous complex functions on an
ordered compact interval.  This is the analytic core later specialized to `ζ` and `M_X`. -/
theorem integral_norm_mul_sub_one_rpow_four_thirds_le
    {F M : ℝ → ℂ} (hF : Continuous F) (hM : Continuous M)
    (U V : ℝ) (hUV : U ≤ V) :
    ∫ t in Icc U V, ‖F t * M t - 1‖ ^ ((4 : ℝ) / 3) ≤
      (2 : ℝ) ^ ((1 : ℝ) / 3) *
          (∫ t in Icc U V, ‖F t‖ ^ (4 : ℝ)) ^ ((1 : ℝ) / 3) *
          (∫ t in Icc U V, ‖M t‖ ^ (2 : ℝ)) ^ ((2 : ℝ) / 3) +
        (2 : ℝ) ^ ((1 : ℝ) / 3) * (V - U) := by
  let E : ℝ → ℝ := fun t => ‖F t * M t - 1‖ ^ ((4 : ℝ) / 3)
  let P : ℝ → ℝ := fun t => (2 : ℝ) ^ ((1 : ℝ) / 3) *
    ((‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3) + 1)
  have hEcont : Continuous E := by
    apply Continuous.rpow_const
    · exact ((hF.mul hM).sub continuous_const).norm
    · intro t
      exact Or.inr (by norm_num)
  have hPcont : Continuous P := by
    apply Continuous.const_mul
    exact ((hF.norm.mul hM.norm).rpow_const (fun _ => Or.inr (by norm_num))).add continuous_const
  have hEint : Integrable E (volume.restrict (Icc U V)) :=
    (memLp_of_continuous_Icc 1 U V hEcont).integrable (by norm_num)
  have hPint : Integrable P (volume.restrict (Icc U V)) :=
    (memLp_of_continuous_Icc 1 U V hPcont).integrable (by norm_num)
  have hEP : ∀ t : ℝ, E t ≤ P t := by
    intro t
    have htri : ‖F t * M t - 1‖ ≤ ‖F t‖ * ‖M t‖ + 1 := by
      calc
        ‖F t * M t - 1‖ ≤ ‖F t * M t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖F t‖ * ‖M t‖ + 1 := by rw [norm_mul, norm_one]
    calc
      E t ≤ (‖F t‖ * ‖M t‖ + 1) ^ ((4 : ℝ) / 3) := by
        exact Real.rpow_le_rpow (norm_nonneg _) htri (by norm_num)
      _ ≤ P t := rpow_four_thirds_add_one_le _
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hmono : (∫ t in Icc U V, E t) ≤ ∫ t in Icc U V, P t :=
    integral_mono_ae hEint hPint (Filter.Eventually.of_forall hEP)
  have hsplit : (∫ t in Icc U V, P t) =
      (2 : ℝ) ^ ((1 : ℝ) / 3) *
        ((∫ t in Icc U V, (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3)) + (V - U)) := by
    rw [show P = fun t => (2 : ℝ) ^ ((1 : ℝ) / 3) *
      ((‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3) + 1) by rfl]
    have hprodcont : Continuous fun t =>
        (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3) :=
      (hF.norm.mul hM.norm).rpow_const (fun _ => Or.inr (by norm_num))
    have hprodint : Integrable (fun t =>
        (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3)) (volume.restrict (Icc U V)) :=
      (memLp_of_continuous_Icc 1 U V hprodcont).integrable (by norm_num)
    have honeint : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc U V)) :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    rw [integral_const_mul]
    rw [integral_add]
    · rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hUV)]
      simp
    · exact hprodint
    · exact honeint
  rw [hsplit] at hmono
  have hholder := integral_norm_mul_rpow_four_thirds_le hF hM U V
  dsimp [E] at hmono
  calc
    (∫ t in Icc U V, ‖F t * M t - 1‖ ^ ((4 : ℝ) / 3))
        ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) *
          ((∫ t in Icc U V, (‖F t‖ * ‖M t‖) ^ ((4 : ℝ) / 3)) + (V - U)) := hmono
    _ ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) *
          ((∫ t in Icc U V, ‖F t‖ ^ (4 : ℝ)) ^ ((1 : ℝ) / 3) *
          (∫ t in Icc U V, ‖M t‖ ^ (2 : ℝ)) ^ ((2 : ℝ) / 3) + (V - U)) := by
      gcongr
    _ = _ := by ring

/-! ## Specialization to the actual Ingham mollified error -/

/-- Point of height `t` on the Riemann critical line. -/
def inghamCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem continuous_inghamCriticalPoint : Continuous inghamCriticalPoint := by
  unfold inghamCriticalPoint
  fun_prop

theorem inghamCriticalPoint_ne_one (t : ℝ) : inghamCriticalPoint t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [inghamCriticalPoint] at hre

/-- Riemann zeta is continuous along the whole critical line because that line misses its pole. -/
theorem continuous_riemannZeta_inghamCriticalPoint :
    Continuous fun t : ℝ => riemannZeta (inghamCriticalPoint t) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_riemannZeta (inghamCriticalPoint_ne_one t)).continuousAt.comp
    continuous_inghamCriticalPoint.continuousAt

/-- Every finite Ingham mollifier is continuous along the critical line. -/
theorem continuous_inghamMollifier_critical (X : ℕ) :
    Continuous fun t : ℝ => inghamMollifier X (inghamCriticalPoint t) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (analyticAt_inghamMollifier X (inghamCriticalPoint t)).continuousAt.comp
    continuous_inghamCriticalPoint.continuousAt

/-- Actual critical-line fourth moment of Riemann zeta on `[U,V]`. -/
noncomputable def inghamCriticalZetaFourthMoment (U V : ℝ) : ℝ :=
  ∫ t in Icc U V, ‖riemannZeta (inghamCriticalPoint t)‖ ^ (4 : ℝ)

/-- Actual critical-line second moment of the finite Möbius mollifier. -/
noncomputable def inghamCriticalMollifierSecondMoment (X : ℕ) (U V : ℝ) : ℝ :=
  ∫ t in Icc U V, ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ (2 : ℝ)

/-- Actual `4/3` moment of Ingham's mollified zeta error on `[U,V]`. -/
noncomputable def inghamCriticalErrorFourThirdMoment (X : ℕ) (U V : ℝ) : ℝ :=
  ∫ t in Icc U V,
    ‖riemannZeta (inghamCriticalPoint t) * inghamMollifier X (inghamCriticalPoint t) - 1‖ ^
      ((4 : ℝ) / 3)

/-- **Coefficient-three critical moment.**  Exact equation-(41) input for the actual Riemann zeta
function and finite Möbius mollifier.  No quantitative moment hypothesis occurs in the statement. -/
theorem inghamCriticalErrorFourThirdMoment_le (X : ℕ) {U V : ℝ} (hUV : U ≤ V) :
    inghamCriticalErrorFourThirdMoment X U V ≤
      (2 : ℝ) ^ ((1 : ℝ) / 3) * (inghamCriticalZetaFourthMoment U V) ^ ((1 : ℝ) / 3) *
          (inghamCriticalMollifierSecondMoment X U V) ^ ((2 : ℝ) / 3) +
        (2 : ℝ) ^ ((1 : ℝ) / 3) * (V - U) := by
  exact integral_norm_mul_sub_one_rpow_four_thirds_le
    continuous_riemannZeta_inghamCriticalPoint (continuous_inghamMollifier_critical X) U V hUV

end

end RHTower.Sieve
