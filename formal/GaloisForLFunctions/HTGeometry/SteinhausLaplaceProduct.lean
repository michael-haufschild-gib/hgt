import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Probability.Moments.Tilted

/-!
# Exact Laplace factorization for weighted Steinhaus phases

This file supplies the source-independent probability layer used by weighted
prime-phase comparison models.  A Steinhaus phase is realized as the first
Fourier character on the additive circle of period `2 * pi`.  Product Haar
measure then turns the exponential moment of every finite weighted projection
into the product of its one-circle moments.

The definitions deliberately use the Haar integral itself rather than a
special-function name.  This keeps the exact factorization, symmetry, and
elementary exponential bounds available without importing an independent
Bessel-function interface.
-/

open scoped BigOperators Real
open MeasureTheory

namespace HTGeometry

local instance phaseCirclePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The additive circle whose first Fourier character is a standard unit
complex phase. -/
abbrev PhaseCircle := AddCircle (2 * Real.pi)

/-- The first Fourier character on `PhaseCircle`. -/
noncomputable def steinhausPhase (x : PhaseCircle) : ℂ := fourier 1 x

/-- The real projection of a Steinhaus phase. -/
noncomputable def steinhausProjection (x : PhaseCircle) : ℝ :=
  (steinhausPhase x).re

/-- The one-circle Laplace transform of the real Steinhaus projection. -/
noncomputable def steinhausLaplace (r : ℝ) : ℝ :=
  ∫ x : PhaseCircle, Real.exp (r * steinhausProjection x)
    ∂AddCircle.haarAddCircle

/-- A finite real weighted sum of Steinhaus projections. -/
noncomputable def weightedSteinhausProjection {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ι → PhaseCircle) : ℝ :=
  ∑ i, a i * steinhausProjection (x i)

/-- **Exact finite Steinhaus Laplace product.**  The exponential moment of a
weighted sum under product Haar measure is the product of the one-circle
Laplace transforms. -/
theorem integral_exp_weightedSteinhausProjection {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (r : ℝ) :
    ∫ x : ι → PhaseCircle,
        Real.exp (r * weightedSteinhausProjection a x)
        ∂(Measure.pi fun _ : ι => AddCircle.haarAddCircle) =
      ∏ i, steinhausLaplace (r * a i) := by
  simp_rw [weightedSteinhausProjection, Finset.mul_sum, Real.exp_sum]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i (y : PhaseCircle) =>
      Real.exp (r * (a i * steinhausProjection y)))]
  congr 1
  funext i
  simp only [steinhausLaplace, mul_assoc]

@[simp] theorem norm_steinhausPhase (x : PhaseCircle) :
    ‖steinhausPhase x‖ = 1 := by
  simp [steinhausPhase]

theorem continuous_steinhausPhase : Continuous steinhausPhase := by
  exact (fourier 1).continuous

theorem continuous_steinhausProjection : Continuous steinhausProjection := by
  exact Complex.continuous_re.comp continuous_steinhausPhase

theorem abs_steinhausProjection_le_one (x : PhaseCircle) :
    |steinhausProjection x| ≤ 1 := by
  exact (Complex.abs_re_le_norm (steinhausPhase x)).trans_eq
    (norm_steinhausPhase x)

theorem abs_mul_steinhausProjection_le (r : ℝ) (x : PhaseCircle) :
    |r * steinhausProjection x| ≤ |r| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg r)
    (abs_steinhausProjection_le_one x)

theorem steinhausLaplace_integrable (r : ℝ) :
    Integrable (fun x : PhaseCircle =>
      Real.exp (r * steinhausProjection x))
      AddCircle.haarAddCircle := by
  refine Integrable.of_bound
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_steinhausProjection)).aestronglyMeasurable
    (Real.exp |r|) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr <|
    (le_abs_self (r * steinhausProjection x)).trans
      (abs_mul_steinhausProjection_le r x)

@[simp] theorem steinhausLaplace_zero : steinhausLaplace 0 = 1 := by
  simp [steinhausLaplace]

/-- The elementary lower exponential envelope of the circle Laplace
transform. -/
theorem exp_neg_abs_le_steinhausLaplace (r : ℝ) :
    Real.exp (-|r|) ≤ steinhausLaplace r := by
  rw [steinhausLaplace]
  calc
    Real.exp (-|r|) =
        ∫ _x : PhaseCircle, Real.exp (-|r|)
          ∂AddCircle.haarAddCircle := by simp
    _ ≤ ∫ x : PhaseCircle, Real.exp (r * steinhausProjection x)
        ∂AddCircle.haarAddCircle := by
      apply integral_mono (integrable_const _) (steinhausLaplace_integrable r)
      intro x
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (abs_mul_steinhausProjection_le r x)).trans
        (neg_abs_le (r * steinhausProjection x))

/-- The elementary upper exponential envelope of the circle Laplace
transform. -/
theorem steinhausLaplace_le_exp_abs (r : ℝ) :
    steinhausLaplace r ≤ Real.exp |r| := by
  rw [steinhausLaplace]
  calc
    (∫ x : PhaseCircle, Real.exp (r * steinhausProjection x)
        ∂AddCircle.haarAddCircle) ≤
        ∫ _x : PhaseCircle, Real.exp |r|
          ∂AddCircle.haarAddCircle := by
      apply integral_mono (steinhausLaplace_integrable r) (integrable_const _)
      intro x
      apply Real.exp_le_exp.mpr
      exact (le_abs_self (r * steinhausProjection x)).trans
        (abs_mul_steinhausProjection_le r x)
    _ = Real.exp |r| := by simp

theorem steinhausLaplace_pos (r : ℝ) : 0 < steinhausLaplace r :=
  (Real.exp_pos (-|r|)).trans_le (exp_neg_abs_le_steinhausLaplace r)

/-- A half-period reverses the real Steinhaus projection. -/
theorem steinhausProjection_add_half_period (x : PhaseCircle) :
    steinhausProjection ((Real.pi : ℝ) + x) =
      -steinhausProjection x := by
  have h := fourier_add_half_inv_index
    (T := 2 * Real.pi) (n := (1 : ℤ)) one_ne_zero (by positivity) x
  simp only [Int.cast_one, div_one] at h
  have hshift : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hshift] at h
  rw [add_comm]
  exact congrArg Complex.re h

/-- The one-circle Steinhaus Laplace transform is even. -/
@[simp] theorem steinhausLaplace_neg (r : ℝ) :
    steinhausLaplace (-r) = steinhausLaplace r := by
  rw [steinhausLaplace, steinhausLaplace]
  rw [← MeasureTheory.integral_add_left_eq_self
    (fun x : PhaseCircle => Real.exp (r * steinhausProjection x))
    (Real.pi : PhaseCircle)]
  apply integral_congr_ae
  filter_upwards with x
  rw [steinhausProjection_add_half_period]
  congr 1
  ring

/-- The Steinhaus Laplace transform is at least one.  This is the integrated
half-period pairing `exp(x) + exp(-x) = 2 cosh(x)`. -/
theorem one_le_steinhausLaplace (r : ℝ) :
    1 ≤ steinhausLaplace r := by
  have hsum : 2 ≤ steinhausLaplace r + steinhausLaplace (-r) := by
    rw [steinhausLaplace, steinhausLaplace, ← integral_add
      (steinhausLaplace_integrable r)
      (steinhausLaplace_integrable (-r))]
    calc
      2 = ∫ _x : PhaseCircle, (2 : ℝ)
          ∂AddCircle.haarAddCircle := by simp
      _ ≤ ∫ x : PhaseCircle,
          (Real.exp (r * steinhausProjection x) +
            Real.exp (-r * steinhausProjection x))
          ∂AddCircle.haarAddCircle := by
        apply integral_mono (integrable_const _)
          ((steinhausLaplace_integrable r).add
            (steinhausLaplace_integrable (-r)))
        intro x
        change 2 ≤ Real.exp (r * steinhausProjection x) +
          Real.exp (-r * steinhausProjection x)
        have hcosh := Real.one_le_cosh (r * steinhausProjection x)
        rw [Real.cosh_eq] at hcosh
        have hneg : -r * steinhausProjection x =
            -(r * steinhausProjection x) := by ring
        rw [hneg]
        linarith
  rw [steinhausLaplace_neg] at hsum
  linarith

/-- The logarithmic one-circle cumulant. -/
noncomputable def steinhausLogLaplace (r : ℝ) : ℝ :=
  Real.log (steinhausLaplace r)

@[simp] theorem steinhausLogLaplace_zero : steinhausLogLaplace 0 = 0 := by
  simp [steinhausLogLaplace]

@[simp] theorem steinhausLogLaplace_neg (r : ℝ) :
    steinhausLogLaplace (-r) = steinhausLogLaplace r := by
  simp [steinhausLogLaplace]

theorem steinhausLogLaplace_nonneg (r : ℝ) :
    0 ≤ steinhausLogLaplace r := by
  rw [steinhausLogLaplace, ← Real.log_one]
  exact Real.strictMonoOn_log.monotoneOn
    (show (0 : ℝ) < 1 by norm_num) (steinhausLaplace_pos r)
      (one_le_steinhausLaplace r)

theorem steinhausLogLaplace_le_abs (r : ℝ) :
    steinhausLogLaplace r ≤ |r| := by
  rw [steinhausLogLaplace, ← Real.log_exp |r|]
  exact Real.strictMonoOn_log.monotoneOn
    (steinhausLaplace_pos r) (Real.exp_pos _)
      (steinhausLaplace_le_exp_abs r)

theorem abs_steinhausLogLaplace_le (r : ℝ) :
    |steinhausLogLaplace r| ≤ |r| := by
  rw [abs_of_nonneg (steinhausLogLaplace_nonneg r)]
  exact steinhausLogLaplace_le_abs r

open ProbabilityTheory Set

/-- The circle integral defining `steinhausLaplace` is exactly mathlib's
moment-generating function for the real Steinhaus projection. -/
theorem steinhausLaplace_eq_mgf (r : ℝ) :
    steinhausLaplace r =
      ProbabilityTheory.mgf steinhausProjection
        AddCircle.haarAddCircle r := by
  rfl

/-- The logarithmic circle cumulant agrees with mathlib's cumulant-generating
function. -/
theorem steinhausLogLaplace_eq_cgf (r : ℝ) :
    steinhausLogLaplace r =
      ProbabilityTheory.cgf steinhausProjection
        AddCircle.haarAddCircle r := by
  rfl

/-- Boundedness of the circle projection makes its exponential integrability
domain the whole real line. -/
theorem integrableExpSet_steinhausProjection :
    ProbabilityTheory.integrableExpSet steinhausProjection
      AddCircle.haarAddCircle = Set.univ := by
  ext r
  simp only [ProbabilityTheory.integrableExpSet, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact steinhausLaplace_integrable r

/-- The logarithmic one-circle Steinhaus cumulant is real analytic on the
whole line. -/
theorem analyticOnNhd_steinhausLogLaplace :
    AnalyticOnNhd ℝ steinhausLogLaplace Set.univ := by
  rw [show steinhausLogLaplace =
      ProbabilityTheory.cgf steinhausProjection
        AddCircle.haarAddCircle from rfl]
  simpa [integrableExpSet_steinhausProjection] using
    (ProbabilityTheory.analyticOnNhd_cgf
      (X := steinhausProjection) (μ := AddCircle.haarAddCircle))

@[simp] theorem steinhausProjection_zero :
    steinhausProjection (0 : PhaseCircle) = 1 := by
  simp [steinhausProjection, steinhausPhase]

@[simp] theorem steinhausProjection_pi :
    steinhausProjection (Real.pi : PhaseCircle) = -1 := by
  have h := steinhausProjection_add_half_period (0 : PhaseCircle)
  simpa using h

/-- Every exponentially tilted circle law retains positive centered
projection energy, for every proposed center.  The proof uses the two
antipodal values `1` and `-1` and positivity of Haar measure on nonempty open
sets. -/
theorem centered_tilted_projection_integral_pos (r c : ℝ) :
    0 < ∫ x : PhaseCircle,
      (steinhausProjection x - c) ^ (2 : ℕ) *
        Real.exp (r * steinhausProjection x)
      ∂AddCircle.haarAddCircle := by
  let f : PhaseCircle → ℝ := fun x =>
    (steinhausProjection x - c) ^ (2 : ℕ) *
      Real.exp (r * steinhausProjection x)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact ((continuous_steinhausProjection.sub continuous_const).pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_steinhausProjection))
  have hfnonneg : 0 ≤ f := fun x =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hfi : Integrable f AddCircle.haarAddCircle :=
    hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace f)
  let x0 : PhaseCircle := if c = 1 then (Real.pi : PhaseCircle) else 0
  have hx0 : steinhausProjection x0 ≠ c := by
    dsimp only [x0]
    split_ifs with hc
    · simp [hc]
      norm_num
    · simpa [eq_comm] using hc
  have hfx0 : 0 < f x0 := by
    exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hx0))
      (Real.exp_pos _)
  let U : Set PhaseCircle := {x | 0 < f x}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const hfcont
  have hUne : U.Nonempty := ⟨x0, hfx0⟩
  have hUsub : U ⊆ Function.support f := by
    intro x hx
    exact ne_of_gt hx
  have hsupp :
      0 < AddCircle.haarAddCircle (Function.support f) :=
    (hUopen.measure_pos AddCircle.haarAddCircle hUne).trans_le
      (measure_mono hUsub)
  change 0 < ∫ x : PhaseCircle, f x ∂AddCircle.haarAddCircle
  exact (integral_pos_iff_support_of_nonneg hfnonneg hfi).2 hsupp

/-- The second derivative of the Steinhaus cumulant is strictly positive at
every real tilt.  Equivalently, no finite exponential tilt collapses the
circle projection to a point mass. -/
theorem iteratedDeriv_two_steinhausLogLaplace_pos (r : ℝ) :
    0 < iteratedDeriv 2 steinhausLogLaplace r := by
  rw [show steinhausLogLaplace =
      ProbabilityTheory.cgf steinhausProjection
        AddCircle.haarAddCircle from rfl]
  rw [ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral
    (show r ∈ interior
      (ProbabilityTheory.integrableExpSet steinhausProjection
        AddCircle.haarAddCircle) by
      simp [integrableExpSet_steinhausProjection])]
  exact div_pos
    (centered_tilted_projection_integral_pos r
      (deriv (ProbabilityTheory.cgf steinhausProjection
        AddCircle.haarAddCircle) r))
    (ProbabilityTheory.mgf_pos (steinhausLaplace_integrable r))

/-- The logarithmic one-circle Steinhaus cumulant is strictly convex on the
whole line. -/
theorem strictConvexOn_steinhausLogLaplace :
    StrictConvexOn ℝ Set.univ steinhausLogLaplace := by
  apply strictConvexOn_univ_of_deriv2_pos
  · exact analyticOnNhd_steinhausLogLaplace.continuous
  · intro x
    rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_two_steinhausLogLaplace_pos x

end HTGeometry
