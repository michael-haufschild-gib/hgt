import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Explicit spacelike slices from the Schwarzschild Cauchy clock

The time function in Proposition 4.1 of Cogo,
*Entire boosted hypersurfaces of vanishing mean curvature in Schwarzschild
spacetime*, arXiv:2611.15912, is `4m artanh(T/√(1+X²))`.
Its slices are parameterized globally by `T = √(1+X²) tanh u`.

This module proves the domain, inverse-clock, slope, and Lorentz-signature
identities of these slices and transports their normals through the existing
Cartan boosts. It does not assert the global maximal-hypersurface PDE theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

open Real
open HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

/-- Kruskal time coordinate on the slice labeled by `u`. -/
def schwarzschildCauchySlice (u x : ℝ) : ℝ := sqrt (1 + x ^ 2) * tanh u

/-- Cogo's clock, with positive mass parameterized by its logarithm. -/
def schwarzschildCauchyClock (m T X : ℝ) : ℝ :=
  4 * exp m * artanh (T / sqrt (1 + X ^ 2))

/-- Every slice lies strictly inside the maximally extended Kruskal domain. -/
theorem schwarzschildCauchySlice_domain (u x : ℝ) :
    schwarzschildCauchySlice u x ^ 2 - x ^ 2 < 1 := by
  have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hs := sq_sqrt hx.le
  have h := mul_lt_mul_of_pos_left (tanh_sq_lt_one u) hx
  unfold schwarzschildCauchySlice
  rw [mul_pow, hs]
  nlinarith only [h]

/-- The clock takes every real value along each fixed spatial coordinate. -/
theorem schwarzschildCauchyClock_slice (m u x : ℝ) :
    schwarzschildCauchyClock m (schwarzschildCauchySlice u x) x = 4 * exp m * u := by
  have hs : sqrt (1 + x ^ 2) ≠ 0 := by positivity
  simp only [schwarzschildCauchyClock, schwarzschildCauchySlice,
    mul_div_cancel_left₀ _ hs, artanh_tanh]

/-- Different slice labels cannot meet. -/
theorem schwarzschildCauchySlice_injective (x : ℝ) :
    Function.Injective (fun u => schwarzschildCauchySlice u x) := by
  intro u v h
  have hclock := congrArg (fun T => schwarzschildCauchyClock 0 T x) h
  simpa only [schwarzschildCauchyClock_slice, exp_zero, mul_one,
    mul_right_inj' (by norm_num : (4 : ℝ) ≠ 0)] using hclock

/-- The slices cover the full Kruskal domain, exactly once at each spatial coordinate. -/
theorem schwarzschildCauchySlice_foliation (T X : ℝ) :
    T ^ 2 - X ^ 2 < 1 ↔ ∃! u, schwarzschildCauchySlice u X = T := by
  constructor
  · intro hT
    have hs : 0 < sqrt (1 + X ^ 2) := by positivity
    have hs2 : sqrt (1 + X ^ 2) ^ 2 = 1 + X ^ 2 := sq_sqrt (by positivity)
    have habs : |T| < sqrt (1 + X ^ 2) := by
      apply (sq_lt_sq₀ (abs_nonneg T) hs.le).mp
      rw [sq_abs, hs2]
      linarith only [hT]
    have hratio : T / sqrt (1 + X ^ 2) ∈ Set.Ioo (-1) 1 := by
      constructor
      · apply (lt_div_iff₀ hs).mpr
        simpa only [neg_one_mul] using (abs_lt.mp habs).1
      · apply (div_lt_iff₀ hs).mpr
        simpa only [one_mul] using (abs_lt.mp habs).2
    have he : schwarzschildCauchySlice (artanh (T / sqrt (1 + X ^ 2))) X = T := by
      unfold schwarzschildCauchySlice
      rw [tanh_artanh hratio, mul_div_cancel₀ _ hs.ne']
    exact ⟨_, he, fun u hu => schwarzschildCauchySlice_injective X (hu.trans he.symm)⟩
  · rintro ⟨u, rfl, _⟩
    exact schwarzschildCauchySlice_domain u X

/-- Spatial slope of a slice. -/
def schwarzschildCauchySlope (u x : ℝ) : ℝ := tanh u * x / sqrt (1 + x ^ 2)

/-- The stated slope is the derivative of the actual slice function. -/
theorem schwarzschildCauchySlice_hasDerivAt (u x : ℝ) :
    HasDerivAt (schwarzschildCauchySlice u) (schwarzschildCauchySlope u x) x := by
  have hx : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hbase : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_add 1
  have hm := (hbase.sqrt hx).mul_const (tanh u)
  have hc : 2 * x / (2 * sqrt (1 + x ^ 2)) * tanh u =
      schwarzschildCauchySlope u x := by
    unfold schwarzschildCauchySlope
    field_simp
  rw [hc] at hm
  exact hm

/-- Exact spacelike margin, including the radial gain away from `X=0`. -/
theorem schwarzschildCauchySlope_margin (u x : ℝ) :
    1 - schwarzschildCauchySlope u x ^ 2 =
      (1 + (1 - tanh u ^ 2) * x ^ 2) / (1 + x ^ 2) := by
  have hs : sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := sq_sqrt (by positivity)
  unfold schwarzschildCauchySlope
  rw [div_pow, hs]
  field_simp
  ring

/-- Every slice is strictly spacelike in the radial Kruskal plane. -/
theorem schwarzschildCauchySlope_sq_lt_one (u x : ℝ) :
    schwarzschildCauchySlope u x ^ 2 < 1 := by
  have hm := schwarzschildCauchySlope_margin u x
  have hn : 0 < (1 + (1 - tanh u ^ 2) * x ^ 2) / (1 + x ^ 2) := by
    have hp : 0 < 1 - tanh u ^ 2 := sub_pos.mpr (tanh_sq_lt_one u)
    positivity
  linarith only [hm, hn]

/-- The normal direction is timelike for the existing Cartan split form. -/
theorem schwarzschildCauchyNormal_timelike (u x : ℝ) :
    0 < splitForm (1, schwarzschildCauchySlope u x) (1, schwarzschildCauchySlope u x) := by
  have h := schwarzschildCauchySlope_sq_lt_one u x
  simpa only [splitForm, one_mul, pow_two] using sub_pos.mpr h

/-- Cartan boosts preserve timelikeness of every constructed slice normal. -/
theorem schwarzschildCauchyNormal_boost_timelike (s u x : ℝ) :
    0 < splitForm (boost s (1, schwarzschildCauchySlope u x))
      (boost s (1, schwarzschildCauchySlope u x)) := by
  rw [splitForm_boost]
  exact schwarzschildCauchyNormal_timelike u x

/-- The tangent has the opposite, spacelike signature. -/
theorem schwarzschildCauchyTangent_spacelike (u x : ℝ) :
    splitForm (schwarzschildCauchySlope u x, 1) (schwarzschildCauchySlope u x, 1) < 0 := by
  have h := schwarzschildCauchySlope_sq_lt_one u x
  simpa only [splitForm, one_mul, pow_two] using sub_neg.mpr h

/-- The normal and tangent are Lorentz-orthogonal at every point. -/
theorem schwarzschildCauchyNormal_tangent_orthogonal (u x : ℝ) :
    splitForm (1, schwarzschildCauchySlope u x) (schwarzschildCauchySlope u x, 1) = 0 := by
  simp [splitForm]

end GaloisForLFunctions.HTGeometry
