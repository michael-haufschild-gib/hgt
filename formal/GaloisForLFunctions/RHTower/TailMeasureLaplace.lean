import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy
import GaloisForLFunctions.RHTower.LaplaceAbscissaExists

/-!
# The one-sign tail of a profile, thickened by a reference exponential

Landau's theorem needs a nonnegative carrier with an actual convergence abscissa.  The tail of a
profile past the height where it stops changing sign is nonnegative but may converge everywhere, so
we add a reference density `e^{u/4}`: the sum still converges right of `3/2` and now certainly
diverges left of `1/4`, which pins an abscissa into `[1/4, 3/2]`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The reference-thickened tail density of a profile past height `H`. -/
def tailCarrier (g : ℝ → ℝ) (H u : ℝ) : ℝ := g (H + u) + Real.exp (u / 4)

/-- The measure carried by the thickened tail. -/
def tailMeasure (g : ℝ → ℝ) (H : ℝ) : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (tailCarrier g H u)

theorem measurable_ofReal_tailCarrier {g : ℝ → ℝ} (hg : Measurable g) (H : ℝ) :
    Measurable fun u : ℝ => ENNReal.ofReal (tailCarrier g H u) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact (hg.comp (measurable_const_add H)).add
    (Real.measurable_exp.comp (measurable_id.div_const 4))

theorem tailCarrier_nonneg {g : ℝ → ℝ} {H : ℝ}
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) {u : ℝ} (hu : 0 < u) :
    0 ≤ tailCarrier g H u :=
  add_nonneg (hpos u hu) (Real.exp_pos _).le

/-- The transform of the tail measure is the ordinary integral against the density. -/
theorem laplaceMass_tailMeasure {g : ℝ → ℝ} (hg : Measurable g) (H σ : ℝ) :
    laplaceMass (tailMeasure g H) σ
      = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-σ * u) * tailCarrier g H u) := by
  have hmeas2 : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u)) := by fun_prop
  rw [laplaceMass, tailMeasure, restrict_withDensity measurableSet_Ioi,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ofReal_tailCarrier hg H) hmeas2]
  refine lintegral_congr fun u => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Left of `1/4` the reference density already forces divergence. -/
theorem laplaceMass_tailMeasure_eq_top {g : ℝ → ℝ} (hg : Measurable g) {H : ℝ}
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) {σ : ℝ} (hσ : σ < 1 / 4) :
    laplaceMass (tailMeasure g H) σ = ⊤ := by
  rw [laplaceMass_tailMeasure hg]
  have hle : ∀ u : ℝ, u ∈ Ioi (0 : ℝ) →
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-σ * u) * tailCarrier g H u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hone : (1 : ℝ) ≤ Real.exp (-σ * u) * Real.exp (u / 4) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    have hmono : Real.exp (-σ * u) * Real.exp (u / 4)
        ≤ Real.exp (-σ * u) * tailCarrier g H u := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [tailCarrier]
      linarith [hpos u hu0]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (Real.exp (-σ * u) * tailCarrier g H u) :=
          ENNReal.ofReal_le_ofReal (le_trans hone hmono)
  have hbig : (∫⁻ _u in Ioi (0 : ℝ), (1 : ℝ≥0∞)) = ⊤ := by
    rw [MeasureTheory.lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioi]
  refine top_le_iff.mp ?_
  rw [← hbig]
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  exact hle u hu

/-- Right of the profile's own abscissa the thickened tail still converges. -/
theorem laplaceMass_tailMeasure_ne_top {g : ℝ → ℝ} (hg : Measurable g) {H σ : ℝ}
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u))
    (hint : IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * tailCarrier g H u) (Ioi (0 : ℝ))) :
    laplaceMass (tailMeasure g H) σ ≠ ⊤ := by
  rw [laplaceMass_tailMeasure hg]
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ Real.exp (-σ * u) * tailCarrier g H u := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    exact mul_nonneg (Real.exp_pos _).le (tailCarrier_nonneg hpos hu)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hae]
  exact ENNReal.ofReal_ne_top

/-- The Bochner form of the tail transform. -/
theorem laplaceReal_tailMeasure {g : ℝ → ℝ} (hg : Measurable g) {H : ℝ}
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) (σ : ℝ) :
    laplaceReal (tailMeasure g H) σ
      = ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * tailCarrier g H u := by
  rw [laplaceReal, tailMeasure, restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_tailCarrier hg H)
      (by filter_upwards with u; exact ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  rw [ENNReal.toReal_ofReal (tailCarrier_nonneg hpos hu0), smul_eq_mul, mul_comm]

/-- On the real axis the complex transform is the real one. -/
theorem complexLaplace_ofReal (ν : Measure ℝ) (σ : ℝ) :
    complexLaplace ν ((σ : ℂ)) = ((laplaceReal ν σ : ℝ) : ℂ) := by
  have h : (∫ u in Ioi (0 : ℝ), ((Real.exp (-σ * u) : ℝ) : ℂ) ∂ν)
      = ((∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) ∂ν : ℝ) : ℂ) := integral_ofReal
  rw [complexLaplace, laplaceReal, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end GaloisForLFunctions.RHTower
