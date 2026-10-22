import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianCountertransport
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Deninger--Meyer Gaussian Green primitive

This module isolates the singular source obstruction in the literal Meyer logarithmic model.
For Cartan displacement `a = re ρ - 1 / 2`, the `r`-th Gaussian Green term has finite
half-density mass `exp (-r a² / (4π))`, while its `a`-tilted mass is exactly one.  Hence
finite Green partial sums have uniformly bounded half-density mass when `a ≠ 0`, but their
Mellin value at horizontal parameter `1 / 2 + a + iτ` is exactly their length and diverges.

The final theorem is unconditional: it gives one explicit family witnessing the mismatch between
completed half-density Green transport and the singular Cartan/Mellin boundary.  Any source-level
descent theorem must cancel this exact defect before passing to the completion.
-/

open Complex MeasureTheory Set Filter
open scoped Real
open GaloisForLFunctions

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- The `r`-th half-density Gaussian Green term at Cartan displacement `a`. -/
def greenTerm (a r t : ℝ) : ℝ :=
  (Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
    Real.exp (-(π * t ^ (2 : ℕ) / r))

theorem greenTerm_nonneg (a r t : ℝ) : 0 ≤ greenTerm a r t := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg r))
    (Real.exp_pos _).le) (Real.exp_pos _).le

/-- Completing the square converts Cartan tilt into translation of the Gaussian center. -/
theorem greenTerm_eq_shifted (a r t : ℝ) (hr : 0 < r) :
    Real.exp (a * t) * greenTerm a r t =
      (Real.sqrt r)⁻¹ * Real.exp
        (-(π / r) * (t - r * a / (2 * π)) ^ (2 : ℕ)) := by
  have hexp :
      a * t + -(r * a ^ (2 : ℕ) / (4 * π)) + -(π * t ^ (2 : ℕ) / r) =
        -(π / r) * (t - r * a / (2 * π)) ^ (2 : ℕ) := by
    field_simp [hr.ne', Real.pi_ne_zero]
    ring
  rw [greenTerm]
  calc
    Real.exp (a * t) *
          ((Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
            Real.exp (-(π * t ^ (2 : ℕ) / r))) =
        (Real.sqrt r)⁻¹ *
          (Real.exp (a * t) * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
            Real.exp (-(π * t ^ (2 : ℕ) / r))) := by ring
    _ = (Real.sqrt r)⁻¹ * Real.exp
          (a * t + -(r * a ^ (2 : ℕ) / (4 * π)) + -(π * t ^ (2 : ℕ) / r)) := by
        rw [Real.exp_add, Real.exp_add]
    _ = _ := by rw [hexp]

/-- Ordinary half-density mass of one Green term. -/
theorem integral_greenTerm (a r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ, greenTerm a r t = Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) := by
  simp only [greenTerm]
  rw [show (fun t : ℝ =>
      (Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
        Real.exp (-(π * t ^ (2 : ℕ) / r))) =
      fun t : ℝ => ((Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π)))) *
        Real.exp (-(π / r) * t ^ (2 : ℕ)) by
      funext t
      congr 2
      field_simp [hr.ne']]
  rw [integral_const_mul, integral_gaussian]
  have hsqrt : Real.sqrt (π / (π / r)) = Real.sqrt r := by
    congr 1
    field_simp [hr.ne', Real.pi_ne_zero]
  rw [hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hr]

theorem integrable_greenTerm (a r : ℝ) (hr : 0 < r) :
    Integrable (greenTerm a r) := by
  rw [show greenTerm a r = fun t : ℝ =>
      ((Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π)))) *
        Real.exp (-(π / r) * t ^ (2 : ℕ)) by
      funext t
      simp only [greenTerm]
      congr 2
      field_simp [hr.ne']]
  exact (integrable_exp_neg_mul_sq (div_pos Real.pi_pos hr)).const_mul _

/-- Every positive-time Green term has exactly unit Cartan-tilted mass. -/
theorem integral_tilt_greenTerm (a r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ, Real.exp (a * t) * greenTerm a r t = 1 := by
  rw [show (fun t : ℝ => Real.exp (a * t) * greenTerm a r t) =
      fun t : ℝ => (Real.sqrt r)⁻¹ *
        Real.exp (-(π / r) * (t - r * a / (2 * π)) ^ (2 : ℕ)) by
      funext t
      exact greenTerm_eq_shifted a r t hr]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun t : ℝ => Real.exp (-(π / r) * t ^ (2 : ℕ))) (r * a / (2 * π))]
  rw [integral_gaussian]
  have hsqrt : Real.sqrt (π / (π / r)) = Real.sqrt r := by
    congr 1
    field_simp [hr.ne', Real.pi_ne_zero]
  rw [hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hr]

theorem integrable_tilt_greenTerm (a r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => Real.exp (a * t) * greenTerm a r t) := by
  rw [show (fun t : ℝ => Real.exp (a * t) * greenTerm a r t) =
      fun t : ℝ => (Real.sqrt r)⁻¹ *
        Real.exp (-(π / r) * (t - r * a / (2 * π)) ^ (2 : ℕ)) by
      funext t
      exact greenTerm_eq_shifted a r t hr]
  exact ((integrable_exp_neg_mul_sq (div_pos Real.pi_pos hr)).comp_sub_right
    (r * a / (2 * π))).const_mul _

/-- Finite Neumann--Green primitive in the half-density coordinate. -/
def greenPartial (a : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, greenTerm a (n + 1 : ℝ) t

theorem greenPartial_nonneg (a : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ greenPartial a N t := by
  exact Finset.sum_nonneg fun n _ => greenTerm_nonneg _ _ _

theorem integral_greenPartial (a : ℝ) (N : ℕ) :
    ∫ t : ℝ, greenPartial a N t =
      ∑ n ∈ Finset.range N,
        Real.exp (-((n + 1 : ℝ) * a ^ (2 : ℕ) / (4 * π))) := by
  simp only [greenPartial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact integral_greenTerm a (n + 1 : ℝ) (by positivity)
  · intro n hn
    exact integrable_greenTerm a (n + 1 : ℝ) (by positivity)

/-- Exact linear accumulation of the singular Cartan moment. -/
theorem integral_tilt_greenPartial (a : ℝ) (N : ℕ) :
    ∫ t : ℝ, Real.exp (a * t) * greenPartial a N t = N := by
  simp only [greenPartial]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · calc
      ∑ n ∈ Finset.range N,
          ∫ t : ℝ, Real.exp (a * t) * greenTerm a (n + 1 : ℝ) t =
          ∑ n ∈ Finset.range N, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact integral_tilt_greenTerm a (n + 1 : ℝ) (by positivity)
      _ = N := by simp
  · intro n hn
    exact integrable_tilt_greenTerm a (n + 1 : ℝ) (by positivity)

theorem integral_greenPartial_eq_geom (a : ℝ) (N : ℕ) :
    ∫ t : ℝ, greenPartial a N t =
      Real.exp (-(a ^ (2 : ℕ) / (4 * π))) *
        ∑ n ∈ Finset.range N, Real.exp (-(a ^ (2 : ℕ) / (4 * π))) ^ n := by
  rw [integral_greenPartial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    Real.exp (-((n + 1 : ℝ) * a ^ (2 : ℕ) / (4 * π))) =
        Real.exp (-(a ^ (2 : ℕ) / (4 * π))) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = Real.exp (-(a ^ (2 : ℕ) / (4 * π))) *
        Real.exp (-(a ^ (2 : ℕ) / (4 * π))) ^ n := by
      rw [pow_succ]
      ring

/-- Off the critical line, ordinary half-density masses are uniformly bounded. -/
theorem integral_greenPartial_le_geometric_bound
    {a : ℝ} (ha : a ≠ 0) (N : ℕ) :
    ∫ t : ℝ, greenPartial a N t ≤
      Real.exp (-(a ^ (2 : ℕ) / (4 * π))) *
        (1 - Real.exp (-(a ^ (2 : ℕ) / (4 * π))))⁻¹ := by
  rw [integral_greenPartial_eq_geom]
  let q := Real.exp (-(a ^ (2 : ℕ) / (4 * π)))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    have ha2 : 0 < a ^ (2 : ℕ) := sq_pos_of_ne_zero ha
    exact neg_lt_zero.mpr (div_pos ha2 (mul_pos (by norm_num) Real.pi_pos))
  have hsum : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hq1)
  have hle := hsum.sum_le_tsum (Finset.range N)
    (fun n hn => pow_nonneg hq0 n)
  rw [tsum_geometric_of_lt_one hq0 hq1] at hle
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

theorem tendsto_integral_tilt_greenPartial_atTop (a : ℝ) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, Real.exp (a * t) * greenPartial a N t)
      atTop atTop := by
  simpa only [integral_tilt_greenPartial] using
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

/-- Raw Meyer source obtained by undoing half-density and centering at height `τ`. -/
def greenSourcePartial (a tau : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) / 2) *
    Complex.exp (-Complex.I * (tau : ℂ) * (t : ℂ)) *
      (greenPartial a N t : ℂ)

theorem halfDensity_norm_greenSourcePartial
    (a tau : ℝ) (N : ℕ) (t : ℝ) :
    Real.exp (t / 2) * ‖greenSourcePartial a tau N t‖ =
      greenPartial a N t := by
  rw [greenSourcePartial, norm_mul, norm_mul, Complex.norm_exp,
    Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (greenPartial_nonneg a N t)]
  have hphase : (-Complex.I * (tau : ℂ) * (t : ℂ)).re = 0 := by
    simp
  have hhalf : (-(t : ℂ) / 2).re = -t / 2 := by
    norm_num
  rw [hphase, Real.exp_zero]
  rw [hhalf]
  simp only [mul_one]
  rw [← mul_assoc, ← Real.exp_add]
  have hz : t / 2 + -t / 2 = 0 := by ring
  rw [hz, Real.exp_zero, one_mul]

theorem integral_halfDensity_norm_greenSourcePartial
    (a tau : ℝ) (N : ℕ) :
    ∫ t : ℝ, Real.exp (t / 2) * ‖greenSourcePartial a tau N t‖ =
      ∑ n ∈ Finset.range N,
        Real.exp (-((n + 1 : ℝ) * a ^ (2 : ℕ) / (4 * π))) := by
  rw [show (fun t : ℝ => Real.exp (t / 2) * ‖greenSourcePartial a tau N t‖) =
      greenPartial a N by
      funext t
      exact halfDensity_norm_greenSourcePartial a tau N t]
  exact integral_greenPartial a N

/-- At `s = 1 / 2 + a + iτ`, phase and half-density factors cancel pointwise. -/
theorem greenSourcePartial_mellin_integrand
    (a tau : ℝ) (N : ℕ) (t : ℝ) :
    Complex.exp
          (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ)) *
        greenSourcePartial a tau N t =
      (Real.exp (a * t) * greenPartial a N t : ℝ) := by
  rw [greenSourcePartial]
  rw [show
      Complex.exp
            (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ)) *
          (Complex.exp (-(t : ℂ) / 2) *
              Complex.exp (-Complex.I * (tau : ℂ) * (t : ℂ)) *
            (greenPartial a N t : ℂ)) =
        (Complex.exp
              (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ)) *
            Complex.exp (-(t : ℂ) / 2) *
              Complex.exp (-Complex.I * (tau : ℂ) * (t : ℂ))) *
          (greenPartial a N t : ℂ) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [show
      ((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ) +
          -(t : ℂ) / 2 + -Complex.I * (tau : ℂ) * (t : ℂ) =
        ((a * t : ℝ) : ℂ) by
      push_cast
      ring]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

/-- Exact value of the raw Green source at its horizontal Mellin parameter. -/
theorem integral_greenSourcePartial_mellin_at_horizontal
    (a tau : ℝ) (N : ℕ) :
    ∫ t : ℝ,
        Complex.exp
            (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ)) *
          greenSourcePartial a tau N t = (N : ℂ) := by
  rw [show (fun t : ℝ =>
      Complex.exp
            (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) * (t : ℂ)) *
          greenSourcePartial a tau N t) =
      fun t : ℝ => ((Real.exp (a * t) * greenPartial a N t : ℝ) : ℂ) by
      funext t
      exact greenSourcePartial_mellin_integrand a tau N t]
  rw [integral_complex_ofReal, integral_tilt_greenPartial]
  norm_num

/-- Exact saddle ray, exposing the Green tail exponent `|a|`. -/
theorem greenTerm_saddle_ray (a r : ℝ) (hr : 0 < r) :
    greenTerm a r (|a| * r / (2 * π)) =
      (Real.sqrt r)⁻¹ * Real.exp (-|a| * (|a| * r / (2 * π))) := by
  rw [greenTerm]
  have hsq : |a| ^ (2 : ℕ) = a ^ (2 : ℕ) := sq_abs a
  have hexp :
      -(r * a ^ (2 : ℕ) / (4 * π)) -
          π * (|a| * r / (2 * π)) ^ (2 : ℕ) / r =
        -|a| * (|a| * r / (2 * π)) := by
    field_simp [hr.ne', Real.pi_ne_zero]
    nlinarith [hsq]
  calc
    (Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
          Real.exp (-(π * (|a| * r / (2 * π)) ^ (2 : ℕ) / r)) =
        (Real.sqrt r)⁻¹ * Real.exp
          (-(r * a ^ (2 : ℕ) / (4 * π)) -
            π * (|a| * r / (2 * π)) ^ (2 : ℕ) / r) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
    _ = _ := by rw [hexp]

/--
Off the critical line, finite Meyer Green sources stay uniformly bounded in half-density mass,
while their horizontal Mellin values diverge linearly.  This is the exact singular-transport defect
that cannot be removed by regular completion alone.
-/
theorem greenSourcePartial_bounded_halfDensity_divergent_mellin
    {a : ℝ} (ha : a ≠ 0) (tau : ℝ) :
    (∀ N : ℕ,
      ∫ t : ℝ, Real.exp (t / 2) * ‖greenSourcePartial a tau N t‖ ≤
        Real.exp (-(a ^ (2 : ℕ) / (4 * π))) *
          (1 - Real.exp (-(a ^ (2 : ℕ) / (4 * π))))⁻¹) ∧
      Tendsto (fun N : ℕ =>
        (∫ t : ℝ,
          Complex.exp
              (((((1 / 2 : ℝ) + a : ℝ) : ℂ) + (tau : ℂ) * Complex.I) *
                (t : ℂ)) * greenSourcePartial a tau N t).re) atTop atTop := by
  constructor
  · intro N
    rw [integral_halfDensity_norm_greenSourcePartial,
      ← integral_greenPartial]
    exact integral_greenPartial_le_geometric_bound ha N
  · simp_rw [integral_greenSourcePartial_mellin_at_horizontal]
    have hcast : (fun N : ℕ => ((N : ℂ).re)) = fun N : ℕ => (N : ℝ) := by
      funext N
      norm_num
    rw [hcast]
    exact (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

/-- General Cartan tilt: completing the square leaves the exact moment ratio. -/
theorem greenTerm_eq_general_shifted (a b r t : ℝ) (hr : 0 < r) :
    Real.exp (b * t) * greenTerm a r t =
      Real.exp (r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) * (Real.sqrt r)⁻¹ *
        Real.exp (-(π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ)) := by
  have hexp :
      b * t + -(r * a ^ (2 : ℕ) / (4 * π)) + -(π * t ^ (2 : ℕ) / r) =
        r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π) -
          (π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ) := by
    field_simp [hr.ne', Real.pi_ne_zero]
    ring
  rw [greenTerm]
  calc
    Real.exp (b * t) *
          ((Real.sqrt r)⁻¹ * Real.exp (-(r * a ^ (2 : ℕ) / (4 * π))) *
            Real.exp (-(π * t ^ (2 : ℕ) / r))) =
        (Real.sqrt r)⁻¹ * Real.exp
          (b * t + -(r * a ^ (2 : ℕ) / (4 * π)) + -(π * t ^ (2 : ℕ) / r)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = (Real.sqrt r)⁻¹ *
          Real.exp (r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π) -
            (π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ)) := by rw [hexp]
    _ = _ := by
      rw [show
        r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π) -
            (π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ) =
          r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π) +
            (-(π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ)) by ring,
        Real.exp_add]
      ring

/-- Exact moment of one Green term at arbitrary real Cartan tilt `b`. -/
theorem integral_general_tilt_greenTerm (a b r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ, Real.exp (b * t) * greenTerm a r t =
      Real.exp (r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) := by
  rw [show (fun t : ℝ => Real.exp (b * t) * greenTerm a r t) =
      fun t : ℝ =>
        (Real.exp (r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) * (Real.sqrt r)⁻¹) *
          Real.exp (-(π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ)) by
      funext t
      rw [greenTerm_eq_general_shifted a b r t hr]]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun t : ℝ => Real.exp (-(π / r) * t ^ (2 : ℕ))) (r * b / (2 * π))]
  rw [integral_gaussian]
  have hsqrt : Real.sqrt (π / (π / r)) = Real.sqrt r := by
    congr 1
    field_simp [hr.ne', Real.pi_ne_zero]
  rw [hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hr]

theorem integrable_general_tilt_greenTerm (a b r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => Real.exp (b * t) * greenTerm a r t) := by
  rw [show (fun t : ℝ => Real.exp (b * t) * greenTerm a r t) =
      fun t : ℝ =>
        (Real.exp (r * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) * (Real.sqrt r)⁻¹) *
          Real.exp (-(π / r) * (t - r * b / (2 * π)) ^ (2 : ℕ)) by
      funext t
      rw [greenTerm_eq_general_shifted a b r t hr]]
  exact ((integrable_exp_neg_mul_sq (div_pos Real.pi_pos hr)).comp_sub_right
    (r * b / (2 * π))).const_mul _

theorem integral_general_tilt_greenPartial (a b : ℝ) (N : ℕ) :
    ∫ t : ℝ, Real.exp (b * t) * greenPartial a N t =
      ∑ n ∈ Finset.range N,
        Real.exp ((n + 1 : ℝ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) := by
  simp only [greenPartial]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact integral_general_tilt_greenTerm a b (n + 1 : ℝ) (by positivity)
  · intro n hn
    exact integrable_general_tilt_greenTerm a b (n + 1 : ℝ) (by positivity)

theorem integral_general_tilt_greenPartial_eq_geom (a b : ℝ) (N : ℕ) :
    ∫ t : ℝ, Real.exp (b * t) * greenPartial a N t =
      Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
        ∑ n ∈ Finset.range N,
          Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ n := by
  rw [integral_general_tilt_greenPartial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    Real.exp ((n + 1 : ℝ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) =
        Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
        Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ n := by
      rw [pow_succ]
      ring

/-- At and beyond the Cartan boundary, every Green term contributes at least unit mass. -/
theorem integral_general_tilt_greenPartial_ge_natCast
    {a b : ℝ} (hab : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) (N : ℕ) :
    (N : ℝ) ≤ ∫ t : ℝ, Real.exp (b * t) * greenPartial a N t := by
  rw [integral_general_tilt_greenPartial]
  calc
    (N : ℝ) = ∑ n ∈ Finset.range N, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ Finset.range N,
        Real.exp ((n + 1 : ℝ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Real.one_le_exp_iff]
      exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hab))
        (mul_nonneg (by norm_num) Real.pi_pos.le)

theorem tendsto_integral_general_tilt_greenPartial_atTop
    {a b : ℝ} (hab : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) :
    Tendsto (fun N : ℕ =>
      ∫ t : ℝ, Real.exp (b * t) * greenPartial a N t) atTop atTop := by
  apply tendsto_atTop_mono
    (fun N => integral_general_tilt_greenPartial_ge_natCast hab N)
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

/-- Infinite completed half-density Green kernel. -/
def greenKernel (a t : ℝ) : ℝ :=
  ∑' n : ℕ, greenTerm a (n + 1 : ℝ) t

theorem summable_integral_norm_general_tilt_greenTerm
    {a b : ℝ} (hab : b ^ (2 : ℕ) < a ^ (2 : ℕ)) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖Real.exp (b * t) * greenTerm a (n + 1 : ℝ) t‖) := by
  let q := Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hab)
      (mul_pos (by norm_num) Real.pi_pos)
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hq1)
  apply (hgeom.mul_left q).congr
  intro n
  symm
  rw [show (fun t : ℝ => ‖Real.exp (b * t) * greenTerm a (n + 1 : ℝ) t‖) =
      fun t : ℝ => Real.exp (b * t) * greenTerm a (n + 1 : ℝ) t by
      funext t
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (greenTerm_nonneg _ _ _))]]
  rw [integral_general_tilt_greenTerm a b (n + 1 : ℝ) (by positivity)]
  dsimp [q]
  calc
    Real.exp ((n + 1 : ℝ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) =
        Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
        Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ n := by
      rw [pow_succ]
      ring

/--
Exact bilateral Laplace transform inside the Cartan strip `b² < a²`.  The geometric denominator
is the completed Gaussian resolvent; its singular boundary is `|b| = |a|`.
-/
theorem integral_general_tilt_greenKernel
    {a b : ℝ} (hab : b ^ (2 : ℕ) < a ^ (2 : ℕ)) :
    ∫ t : ℝ, Real.exp (b * t) * greenKernel a t =
      Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
        (1 - Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)))⁻¹ := by
  rw [show (fun t : ℝ => Real.exp (b * t) * greenKernel a t) =
      fun t : ℝ => ∑' n : ℕ,
        Real.exp (b * t) * greenTerm a (n + 1 : ℝ) t by
      funext t
      rw [greenKernel, tsum_mul_left]]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n : ℕ => integrable_general_tilt_greenTerm a b (n + 1 : ℝ) (by positivity))
    (summable_integral_norm_general_tilt_greenTerm hab)]
  let q := Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hab)
      (mul_pos (by norm_num) Real.pi_pos)
  rw [show (fun n : ℕ =>
      ∫ t : ℝ, Real.exp (b * t) * greenTerm a (n + 1 : ℝ) t) =
      fun n : ℕ => q * q ^ n by
      funext n
      rw [integral_general_tilt_greenTerm a b (n + 1 : ℝ) (by positivity)]
      dsimp [q]
      calc
        Real.exp ((n + 1 : ℝ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) =
            Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ (n + 1) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        _ = Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
            Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) ^ n := by
          rw [pow_succ]
          ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- Exact ordinary mass of the infinite off-critical Green kernel. -/
theorem integral_greenKernel {a : ℝ} (ha : a ≠ 0) :
    ∫ t : ℝ, greenKernel a t =
      Real.exp (-(a ^ (2 : ℕ) / (4 * π))) *
        (1 - Real.exp (-(a ^ (2 : ℕ) / (4 * π))))⁻¹ := by
  have hab : (0 : ℝ) ^ (2 : ℕ) < a ^ (2 : ℕ) := by
    simpa using sq_pos_of_ne_zero ha
  have harg : ((0 : ℝ) ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π) = -(a ^ (2 : ℕ) / (4 * π)) := by
    ring
  simpa only [zero_mul, Real.exp_zero, one_mul, harg] using
    (integral_general_tilt_greenKernel (a := a) (b := 0) hab)

/--
Exact Cartan moment wall: the completed Green transform is geometric precisely inside
`|b| < |a|`, whereas moments of finite source approximants diverge at and beyond the boundary.
-/
theorem greenKernel_exact_Cartan_moment_wall (a b : ℝ) :
    (b ^ (2 : ℕ) < a ^ (2 : ℕ) →
      ∫ t : ℝ, Real.exp (b * t) * greenKernel a t =
        Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)) *
          (1 - Real.exp ((b ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * π)))⁻¹) ∧
    (a ^ (2 : ℕ) ≤ b ^ (2 : ℕ) →
      Tendsto (fun N : ℕ =>
        ∫ t : ℝ, Real.exp (b * t) * greenPartial a N t) atTop atTop) := by
  exact ⟨integral_general_tilt_greenKernel,
    tendsto_integral_general_tilt_greenPartial_atTop⟩

end
end DeningerMeyerGaussianGreen
end RHTower
