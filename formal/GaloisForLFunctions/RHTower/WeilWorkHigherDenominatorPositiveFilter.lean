import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorQuotientMellin
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Positive Mellin filters cannot preserve ordinary Dirichlet sources

A symmetric compactly supported probability measure defines a bilateral Laplace
multiplier. Unless the measure is concentrated at zero, its multiplier tends to
infinity on the positive real axis. Consequently, multiplying a convergent
ordinary Dirichlet series with nonzero first coefficient by this multiplier
cannot give another convergent ordinary Dirichlet series, even eventually on
the real axis. This classifies the source-preserving filters exactly.

This is an obstruction to the positive tail-annihilator shortcut in WP07,
not a proof of the harmonic-deficit converse.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace RHTower.WeilHigherDenominator

/-- Positive symmetric dilation filters with bounded real support. -/
structure PositiveMellinFilter where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  symmetric : measure.IsNegInvariant
  bounded : ∃ R : ℝ, ∀ᵐ t ∂measure, |t| ≤ R

attribute [instance] PositiveMellinFilter.probability PositiveMellinFilter.symmetric

namespace PositiveMellinFilter

/-- The multiplier restricted to the real axis. -/
def laplace (ν : PositiveMellinFilter) (x : ℝ) : ℝ :=
  ∫ t, Real.exp (x * t) ∂ν.measure

/-- First absolute moment detects every nontrivial positive filter. -/
def moment (ν : PositiveMellinFilter) : ℝ := ∫ t, |t| ∂ν.measure

private theorem integrable_continuous (ν : PositiveMellinFilter) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f ν.measure := by
  obtain ⟨R, hR⟩ := ν.bounded
  have hs : ∀ᵐ t ∂ν.measure, t ∈ Icc (-R) R := hR.mono fun _ ht => abs_le.mp ht
  have hi := hf.integrableOn_Icc (μ := ν.measure) (a := -R) (b := R)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi

private theorem integrable_exp (ν : PositiveMellinFilter) (x : ℝ) :
    Integrable (fun t => Real.exp (x * t)) ν.measure :=
  ν.integrable_continuous (Real.continuous_exp.comp (continuous_const.mul continuous_id))

/-- Symmetry identifies the two real directions of the Laplace transform. -/
theorem laplace_neg (ν : PositiveMellinFilter) (x : ℝ) :
    ν.laplace (-x) = ν.laplace x := by
  simpa [laplace, mul_neg, neg_mul] using
    integral_neg_eq_self (fun t => Real.exp (x * t)) ν.measure

/-- The absolute moment vanishes exactly for the identity filter. -/
theorem moment_eq_zero_iff (ν : PositiveMellinFilter) :
    ν.moment = 0 ↔ ν.measure = Measure.dirac 0 := by
  constructor
  · intro h
    have ha := (integral_eq_zero_iff_of_nonneg (fun t : ℝ => abs_nonneg t)
      (ν.integrable_continuous continuous_abs)).mp h
    have ht : (fun t : ℝ => t) =ᵐ[ν.measure] fun _ => 0 := by
      filter_upwards [ha] with t ht
      exact abs_eq_zero.mp ht
    simpa using Measure.map_congr ht
  · intro h
    simp [moment, h]

/-- Positivity prevents cancellation of the first absolute moment. -/
theorem moment_pos_iff (ν : PositiveMellinFilter) :
    0 < ν.moment ↔ ν.measure ≠ Measure.dirac 0 := by
  have hn : 0 ≤ ν.moment := integral_nonneg fun t => abs_nonneg t
  rw [ne_eq, ← ν.moment_eq_zero_iff]
  exact ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne hn (Ne.symm h)⟩

/-- A linear lower bound suffices to obstruct a finite right limit. -/
theorem moment_mul_le_laplace (ν : PositiveMellinFilter) {x : ℝ} (hx : 0 ≤ x) :
    x * (ν.moment / 2) ≤ ν.laplace x := by
  have hp (y : ℝ) : |y| ≤ Real.exp y + Real.exp (-y) := by
    apply abs_le.mpr
    constructor <;> linarith [Real.add_one_le_exp y, Real.add_one_le_exp (-y),
      Real.exp_pos y, Real.exp_pos (-y)]
  have hi := integral_mono
    ((ν.integrable_continuous continuous_abs).const_mul x)
    ((ν.integrable_exp x).add (ν.integrable_exp (-x)))
    (fun t => show x * |t| ≤ Real.exp (x * t) + Real.exp (-x * t) by
      simpa [abs_mul, abs_of_nonneg hx, neg_mul] using hp (x * t))
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (ν.integrable_exp x) (ν.integrable_exp (-x))] at hi
  change x * ν.moment ≤ ν.laplace x + ν.laplace (-x) at hi
  rw [ν.laplace_neg] at hi
  linarith

/-- Every nonidentity positive symmetric filter escapes at the right end. -/
theorem laplace_tendsto_atTop (ν : PositiveMellinFilter)
    (hν : ν.measure ≠ Measure.dirac 0) : Tendsto ν.laplace atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0 : ℝ)).mono fun _ hx => ν.moment_mul_le_laplace hx)
  exact tendsto_id.atTop_mul_const (half_pos (ν.moment_pos_iff.mpr hν))

/-- A positive symmetric multiplier preserves an ordinary Dirichlet source
with nonzero first coefficient only when it is the identity filter. The
representation need hold only eventually on the positive real axis. -/
theorem eq_dirac_of_LSeries (ν : PositiveMellinFilter) {f g : ℕ → ℂ}
    (hg : LSeries.abscissaOfAbsConv g < ⊤) (hg1 : g 1 ≠ 0)
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (a : ℝ)
    (heq : ∀ᶠ x : ℝ in atTop,
      LSeries f x = (ν.laplace (x - a) : ℂ) * LSeries g x) :
    ν.measure = Measure.dirac 0 := by
  by_contra hν
  have hg_lim := LSeries.tendsto_atTop hg
  have hdiv := (LSeries.tendsto_atTop hf).div hg_lim hg1
  have hreal := (Complex.continuous_re.tendsto (f 1 / g 1)).comp hdiv
  have heq' : (fun x : ℝ => (LSeries f x / LSeries g x).re) =ᶠ[atTop]
      (fun x => ν.laplace (x - a)) := by
    filter_upwards [heq, hg_lim.eventually_ne hg1] with x hx hgx
    rw [hx, mul_div_cancel_right₀ _ hgx]
    rfl
  have hfinite := hreal.congr' heq'
  have hshift : Tendsto (fun x : ℝ => x - a) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  exact not_tendsto_atTop_of_tendsto_nhds hfinite ((ν.laplace_tendsto_atTop hν).comp hshift)

/-- Complete classification of filters preserving a given ordinary Dirichlet
source with nonzero first coefficient, including the identity direction. -/
theorem preserves_LSeries_iff (ν : PositiveMellinFilter) {g : ℕ → ℂ}
    (hg : LSeries.abscissaOfAbsConv g < ⊤) (hg1 : g 1 ≠ 0) (a : ℝ) :
    (∃ f : ℕ → ℂ, LSeries.abscissaOfAbsConv f < ⊤ ∧
      ∀ᶠ x : ℝ in atTop, LSeries f x = (ν.laplace (x - a) : ℂ) * LSeries g x) ↔
    ν.measure = Measure.dirac 0 := by
  constructor
  · rintro ⟨f, hf, heq⟩
    exact ν.eq_dirac_of_LSeries hg hg1 hf a heq
  · intro hν
    exact ⟨g, hg, Eventually.of_forall fun x => by simp [laplace, hν]⟩

end PositiveMellinFilter

/-- For the actual normalized cubic datum, the positive filters preserving the
degree-two quotient's ordinary Dirichlet source are exactly the identity.
No additional decay, spectral, or coefficient assumption is used. -/
theorem positiveFilter_preserves_actualQuotient_iff {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hg1 : g 1 = 1)
    (ν : PositiveMellinFilter) (a : ℝ) :
    (∃ f : ℕ → ℂ, LSeries.abscissaOfAbsConv f < ⊤ ∧
      ∀ᶠ x : ℝ in atTop,
        LSeries f x = (ν.laplace (x - a) : ℂ) * LSeries (degreeTwoQuotientCoeff g) x) ↔
    ν.measure = Measure.dirac 0 := by
  have hs := degreeTwoQuotientCoeff_summable
    (hD.summable 2 (by norm_num)) (by norm_num)
  have hc : LSeries.abscissaOfAbsConv (degreeTwoQuotientCoeff g) < ⊤ :=
    hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  apply ν.preserves_LSeries_iff hc
  rw [degreeTwoQuotientCoeff_one, hg1]
  exact one_ne_zero

end RHTower.WeilHigherDenominator
