import GaloisForLFunctions.BiarithmeticGeometry.Affine.DirectionalSpectralWiener
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic

/-!
# Countably many exceptional directions for diffuse planar spectra

Distinct affine lines meet in at most one point. A diffuse finite spectral
measure therefore charges only countably many lines. Wiener's criterion
identifies their slopes with the exceptions to directional mean-square decay.
An atom, conversely, obstructs decay in every direction.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- An affine spectral line, parameterized by slope and intercept. -/
def affineSpectralLine (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x.2 = p.1 * x.1 + p.2}

private theorem affineSpectralLine_measurable (p : ℝ × ℝ) :
    MeasurableSet (affineSpectralLine p) := by
  exact isClosed_eq continuous_snd (continuous_const.mul continuous_fst |>.add continuous_const)
    |>.measurableSet

private theorem affineSpectralLine_inter_subsingleton (p q : ℝ × ℝ) (hpq : p ≠ q) :
    (affineSpectralLine p ∩ affineSpectralLine q).Subsingleton := by
  intro x hx y hy
  obtain ⟨hxp, hxq⟩ := hx
  obtain ⟨hyp, hyq⟩ := hy
  change x.2 = p.1 * x.1 + p.2 at hxp
  change x.2 = q.1 * x.1 + q.2 at hxq
  change y.2 = p.1 * y.1 + p.2 at hyp
  change y.2 = q.1 * y.1 + q.2 at hyq
  have hsl : p.1 ≠ q.1 := by
    intro hs
    apply hpq
    apply Prod.ext hs
    rw [hs] at hxp
    linarith only [hxp, hxq]
  have he : (p.1 - q.1) * (x.1 - y.1) = 0 := by
    linear_combination -hxp + hxq + hyp - hyq
  have hx1 : x.1 = y.1 := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hsl))
  apply Prod.ext hx1
  rw [hxp, hyp, hx1]

/-- With no point masses, only countably many affine spectral lines have positive mass. -/
theorem countable_charged_spectralLines (μ : Measure (ℝ × ℝ)) [SFinite μ]
    [NullSingletonClass μ] :
    {p : ℝ × ℝ | 0 < μ (affineSpectralLine p)}.Countable := by
  apply Measure.countable_meas_pos_of_disjoint_iUnion₀
    (fun p => (affineSpectralLine_measurable p).nullMeasurableSet)
  intro p q hpq
  exact (affineSpectralLine_inter_subsingleton p q hpq).countable.measure_zero μ

/-- Slopes carrying some positive-mass affine spectral line. -/
def exceptionalSpectralSlopes (μ : Measure (ℝ × ℝ)) : Set ℝ :=
  {a | ∃ b, 0 < μ (affineSpectralLine (a, b))}

/-- Countability of exceptional slopes is equivalent to absence of point masses. -/
theorem exceptionalSpectralSlopes_countable_iff (μ : Measure (ℝ × ℝ)) [SFinite μ] :
    (exceptionalSpectralSlopes μ).Countable ↔ NullSingletonClass μ := by
  constructor
  · intro hc
    constructor
    intro x
    by_contra hx
    have hall : exceptionalSpectralSlopes μ = univ := by
      apply eq_univ_of_forall
      intro a
      refine ⟨x.2 - a * x.1, lt_of_lt_of_le (pos_iff_ne_zero.mpr hx) ?_⟩
      apply measure_mono
      intro y hy
      rw [mem_singleton_iff] at hy
      subst y
      change x.2 = a * x.1 + (x.2 - a * x.1)
      ring
    rw [hall] at hc
    exact not_countable_univ hc
  · intro h
    letI := h
    have hc := (countable_charged_spectralLines μ).image Prod.fst
    have he : exceptionalSpectralSlopes μ = Prod.fst '' {p | 0 < μ (affineSpectralLine p)} := by
      ext a
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨(a, b), hb, rfl⟩
      · rintro ⟨⟨a', b⟩, hb, rfl⟩
        exact ⟨b, hb⟩
    rwa [he]

/-- The linear frequency coordinate perpendicular to a line of slope `a`. -/
def slopeFrequency (a : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ ℝ ℝ - a • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- Exceptional slopes are exactly the failures of directional mean-square decay. -/
theorem not_mem_exceptionalSpectralSlopes_iff_mean_square_decay
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (a : ℝ) :
    a ∉ exceptionalSpectralSlopes μ ↔
      Tendsto (fun Y : ℝ => (1 / (2 * Y)) * ∫ t in (-Y)..Y,
        ‖directionalSpectralResponse μ (slopeFrequency a) t‖ ^ 2) atTop (𝓝 0) := by
  rw [directionalSpectralResponse_mean_square_zero_iff]
  simp only [exceptionalSpectralSlopes, mem_setOf_eq, not_exists, not_lt, le_zero_iff]
  apply forall_congr'
  intro b
  have he : affineSpectralLine (a, b) = {x | (slopeFrequency a) x = b} := by
    ext x
    change (x.2 = a * x.1 + b) ↔ x.2 - a * x.1 = b
    constructor <;> intro h <;> linarith only [h]
  rw [he]

end GaloisForLFunctions.BiarithmeticGeometry

#print axioms GaloisForLFunctions.BiarithmeticGeometry.exceptionalSpectralSlopes_countable_iff
#print axioms GaloisForLFunctions.BiarithmeticGeometry.not_mem_exceptionalSpectralSlopes_iff_mean_square_decay
