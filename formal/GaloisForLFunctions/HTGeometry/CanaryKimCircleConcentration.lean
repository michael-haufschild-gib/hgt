import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Extremal concentration for circle probability and Poisson laws

The strict local rate-gap argument in Canary–Kim (arXiv:2609.10325, proof of
Theorem 3.2) specializes to alignment with a boundary direction. Here the gap
is exactly half the squared chordal distance. Its integral gives point-mass
rigidity and quantitative concentration for every circle probability measure.
The corpus's Poisson laws supply exact first-moment and strict-deficit applications.
These statements do not assert the Fuchsian entropy theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set
open scoped ComplexConjugate ENNReal

/-- Alignment with a fixed boundary direction, normalized to have maximum one. -/
def circleExtremalRate (ξ ζ : Circle) : ℝ := ((ζ : ℂ)*conj (ξ : ℂ)).re

def circleExtremalMean (μ : ProbabilityMeasure Circle) (ξ : Circle) : ℝ :=
  ∫ ζ, circleExtremalRate ξ ζ ∂(μ : Measure Circle)

theorem circleExtremalRate_continuous (ξ : Circle) : Continuous (circleExtremalRate ξ) := by
  unfold circleExtremalRate
  fun_prop

theorem circleExtremalRate_le_one (ξ ζ : Circle) : circleExtremalRate ξ ζ ≤ 1 := by
  have h := Complex.re_le_norm ((ζ : ℂ)*conj (ξ : ℂ))
  simpa [circleExtremalRate, norm_mul, Circle.norm_coe] using h

/-- The strict-rate gap is exactly half the squared chordal distance. -/
theorem circleExtremalRate_distance (ξ ζ : Circle) :
    ‖(ζ : ℂ)-(ξ : ℂ)‖^2 = 2*(1-circleExtremalRate ξ ζ) := by
  have hξ := Complex.sq_norm (ξ : ℂ)
  have hζ := Complex.sq_norm (ζ : ℂ)
  rw [Circle.norm_coe] at hξ hζ
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply] at hξ hζ ⊢
  simp only [Complex.sub_re, Complex.sub_im, circleExtremalRate, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  nlinarith

/-- Mean deficit is an exact transport-cost integral for every circle law. -/
theorem circleExtremalMean_distance (μ : ProbabilityMeasure Circle) (ξ : Circle) :
    (∫ ζ : Circle, ‖(ζ : ℂ)-(ξ : ℂ)‖^2 ∂(μ : Measure Circle)) =
      2*(1-circleExtremalMean μ ξ) := by
  simp_rw [circleExtremalRate_distance]
  rw [integral_const_mul, integral_sub (integrable_const 1)
    ((circleExtremalRate_continuous ξ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp [circleExtremalMean]

theorem circleExtremalMean_le_one (μ : ProbabilityMeasure Circle) (ξ : Circle) :
    circleExtremalMean μ ξ ≤ 1 := by
  have h : 0 ≤ ∫ ζ : Circle, ‖(ζ : ℂ)-(ξ : ℂ)‖^2 ∂(μ : Measure Circle) :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [circleExtremalMean_distance] at h
  linarith

/-- Exact maximal alignment forces all probability mass onto the maximizing boundary point. -/
theorem circleExtremalMean_eq_one_iff (μ : ProbabilityMeasure Circle) (ξ : Circle) :
    circleExtremalMean μ ξ = 1 ↔ (μ : Measure Circle) = Measure.dirac ξ := by
  constructor
  · intro h
    have hz : (∫ ζ : Circle, ‖(ζ : ℂ)-(ξ : ℂ)‖^2 ∂(μ : Measure Circle)) = 0 := by
      rw [circleExtremalMean_distance, h]
      ring
    have hc : Continuous (fun ζ : Circle => ‖(ζ : ℂ)-(ξ : ℂ)‖^2) := by fun_prop
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hz
    have he : (fun ζ : Circle => ζ) =ᵐ[(μ : Measure Circle)] (fun _ => ξ) := by
      filter_upwards [hae] with ζ hζ
      apply Subtype.ext
      exact sub_eq_zero.mp (by simpa using hζ)
    have hm := Measure.map_congr (mβ := (inferInstance : MeasurableSpace Circle)) he
    simpa using hm
  · intro h
    have he := circleExtremalRate_distance ξ ξ
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at he
    have hr : circleExtremalRate ξ ξ = 1 := by linarith
    simpa only [circleExtremalMean, h, integral_dirac] using hr

/-- Near-extremal means control mass outside every positive chordal radius. -/
theorem circleExtremalMean_concentration (μ : ProbabilityMeasure Circle) (ξ : Circle) (r : ℝ) :
    Real.exp r ^ 2 * (μ : Measure Circle).real {ζ : Circle | Real.exp r ≤ ‖(ζ : ℂ)-(ξ : ℂ)‖} ≤
      2*(1-circleExtremalMean μ ξ) := by
  have hc : Continuous (fun ζ : Circle => ‖(ζ : ℂ)-(ξ : ℂ)‖^2) := by fun_prop
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ζ : Circle => sq_nonneg ‖(ζ : ℂ)-(ξ : ℂ)‖))
    (hc.integrable_of_hasCompactSupport (μ := (μ : Measure Circle))
      (HasCompactSupport.of_compactSpace _)) (Real.exp r ^ 2)
  rw [circleExtremalMean_distance] at h
  have hs : {ζ : Circle | Real.exp r^2 ≤ ‖(ζ : ℂ)-(ξ : ℂ)‖^2} =
      {ζ : Circle | Real.exp r ≤ ‖(ζ : ℂ)-(ξ : ℂ)‖} := by
    ext ζ
    exact sq_le_sq₀ (Real.exp_pos r).le (norm_nonneg _)
  rwa [hs] at h

/-- For the corpus's Poisson laws, the mean alignment is the first Fourier moment. -/
theorem circleExtremalMean_poisson (a : CirclePoissonParameter) (ξ : Circle) :
    circleExtremalMean (circlePoissonProbabilityMeasure a) ξ =
      ((a : ℂ)*conj (ξ : ℂ)).re := by
  have hc : Continuous (fun ζ : Circle => (ζ : ℂ)*conj (ξ : ℂ)) := by fun_prop
  have hi := hc.integrable_of_hasCompactSupport (μ := circlePoissonMeasure a)
    (HasCompactSupport.of_compactSpace _)
  change (∫ ζ : Circle, ((ζ : ℂ)*conj (ξ : ℂ)).re ∂circlePoissonMeasure a) = _
  calc
    _ = (∫ ζ : Circle, (ζ : ℂ)*conj (ξ : ℂ) ∂circlePoissonMeasure a).re := integral_re hi
    _ = _ := ?_
  rw [integral_mul_const]
  have hm := integral_circlePoissonMeasure_coe_pow a 1
  simp only [pow_one] at hm
  rw [hm]

/-- Every interior Poisson law has a strict deficit in every boundary direction. -/
theorem circleExtremalMean_poisson_lt_one (a : CirclePoissonParameter) (ξ : Circle) :
    circleExtremalMean (circlePoissonProbabilityMeasure a) ξ < 1 := by
  rw [circleExtremalMean_poisson]
  have h := Complex.re_le_norm ((a : ℂ)*conj (ξ : ℂ))
  have ha : ‖(a : ℂ)‖ < 1 := by
    have ha := a.property
    change dist (a : ℂ) 0 < 1 at ha
    simpa only [dist_zero_right] using ha
  simpa [norm_mul, Circle.norm_coe] using h.trans_lt (by simpa [norm_mul, Circle.norm_coe] using ha)

end GaloisForLFunctions.HTGeometry
