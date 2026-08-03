import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Escaping a spectral relation through a block splitting

Turning on one transverse coupling splits every two-dimensional block of a diagonal Hamiltonian
into `m ± sqrt(d² + u²)`.  An integer spectral character therefore becomes

`f(u) = constant + ∑ β_z sqrt(d_z² + u²)`,

whose second derivative at the origin is `∑ β_z / |d_z|`.  So a character whose block differences
weight the reciprocal gaps nontrivially cannot vanish identically near the diagonal point: the
splitting escapes it.

This is the analytic heart of the escape hypothesis consumed by the analytic spectral relation
machinery: a relation which survives every block splitting has zero block differences.
-/

open scoped BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem sqrtQuadratic_pos {d : ℝ} (hd : d ≠ 0) (u : ℝ) : 0 < d ^ 2 + u ^ 2 := by
  have hd2 : 0 < d ^ 2 := pow_pos (abs_pos.mpr hd) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
  positivity

/-- Derivative of one block square-root branch. -/
theorem hasDerivAt_sqrtQuadratic {d : ℝ} (hd : d ≠ 0) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.sqrt (d ^ 2 + v ^ 2))
      (u / Real.sqrt (d ^ 2 + u ^ 2)) u := by
  have hpos : 0 < d ^ 2 + u ^ 2 := sqrtQuadratic_pos hd u
  have hinner : HasDerivAt (fun v : ℝ => d ^ 2 + v ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_pow 2 u).const_add (d ^ 2))
  have hsqrt := hinner.sqrt (ne_of_gt hpos)
  have hval : 2 * u / (2 * Real.sqrt (d ^ 2 + u ^ 2)) = u / Real.sqrt (d ^ 2 + u ^ 2) := by
    rw [mul_div_mul_left _ _ (two_ne_zero)]
  rwa [hval] at hsqrt

/-- Derivative at the origin of the slope of a block square-root branch. -/
theorem hasDerivAt_slope_sqrtQuadratic {d : ℝ} (hd : d ≠ 0) :
    HasDerivAt (fun u : ℝ => u / Real.sqrt (d ^ 2 + u ^ 2)) (1 / |d|) 0 := by
  have hpos : ∀ u : ℝ, 0 < d ^ 2 + u ^ 2 := sqrtQuadratic_pos hd
  have hden : HasDerivAt (fun u : ℝ => Real.sqrt (d ^ 2 + u ^ 2)) 0 0 := by
    have h := hasDerivAt_sqrtQuadratic hd 0
    simpa using h
  have hnum : HasDerivAt (fun u : ℝ => u) 1 0 := hasDerivAt_id 0
  have hne : Real.sqrt (d ^ 2 + 0 ^ 2) ≠ 0 := by
    have := hpos 0
    positivity
  have hdiv := HasDerivAt.div hnum hden hne
  have hval : (1 * Real.sqrt (d ^ 2 + 0 ^ 2) - 0 * 0) / Real.sqrt (d ^ 2 + 0 ^ 2) ^ 2
      = 1 / |d| := by
    have hsq : Real.sqrt (d ^ 2 + 0 ^ 2) = |d| := by
      rw [show d ^ 2 + 0 ^ 2 = d ^ 2 by ring, Real.sqrt_sq_eq_abs]
    rw [hsq]
    have habs : |d| ≠ 0 := abs_ne_zero.mpr hd
    field_simp
    ring
  rw [hval] at hdiv
  simpa [Pi.div_def] using hdiv

/-- The block-split spectral relation of an integer character. -/
def blockSplitRelation {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ) (u : ℝ) : ℝ :=
  c + ∑ z, β z * Real.sqrt (d z ^ 2 + u ^ 2)

theorem hasDerivAt_blockSplitRelation {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ)
    (hd : ∀ z, d z ≠ 0) (u : ℝ) :
    HasDerivAt (blockSplitRelation c β d)
      (∑ z, β z * (u / Real.sqrt (d z ^ 2 + u ^ 2))) u := by
  have hsum : HasDerivAt (fun v : ℝ => ∑ z, β z * Real.sqrt (d z ^ 2 + v ^ 2))
      (∑ z, β z * (u / Real.sqrt (d z ^ 2 + u ^ 2))) u := by
    refine HasDerivAt.fun_sum fun z _ => ?_
    exact HasDerivAt.const_mul (β z) (hasDerivAt_sqrtQuadratic (hd z) u)
  show HasDerivAt (fun x : ℝ => c + ∑ z, β z * Real.sqrt (d z ^ 2 + x ^ 2)) _ u
  exact HasDerivAt.const_add c hsum

theorem deriv_blockSplitRelation {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ)
    (hd : ∀ z, d z ≠ 0) :
    deriv (blockSplitRelation c β d)
      = fun u => ∑ z, β z * (u / Real.sqrt (d z ^ 2 + u ^ 2)) := by
  funext u
  exact (hasDerivAt_blockSplitRelation c β d hd u).deriv

/-- **The reciprocal-gap weight is the second derivative of the block-split relation.** -/
theorem hasDerivAt_deriv_blockSplitRelation_zero {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ)
    (hd : ∀ z, d z ≠ 0) :
    HasDerivAt (deriv (blockSplitRelation c β d)) (∑ z, β z * (1 / |d z|)) 0 := by
  rw [deriv_blockSplitRelation c β d hd]
  refine HasDerivAt.fun_sum fun z _ => ?_
  exact HasDerivAt.const_mul (β z) (hasDerivAt_slope_sqrtQuadratic (hd z))

/-- **Block splittings escape every character with nontrivial reciprocal-gap weight.**  If the block
differences weight the reciprocal gaps nontrivially, the relation cannot vanish on any neighbourhood
of the unsplit point. -/
theorem not_eventuallyEq_zero_blockSplitRelation {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ)
    (hd : ∀ z, d z ≠ 0) (hweight : ∑ z, β z * (1 / |d z|) ≠ 0) :
    ¬ (blockSplitRelation c β d =ᶠ[𝓝 (0 : ℝ)] fun _ => 0) := by
  intro hzero
  have hderiv : deriv (blockSplitRelation c β d) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [hzero.eventuallyEq_nhds] with u hu
    rw [hu.deriv_eq]
    exact deriv_const u 0
  have hsecond := hasDerivAt_deriv_blockSplitRelation_zero c β d hd
  have hzeroDeriv : HasDerivAt (deriv (blockSplitRelation c β d)) 0 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
    exact hconst.congr_of_eventuallyEq hderiv
  exact hweight (hsecond.unique hzeroDeriv)

/-- Consequently some nearby splitting parameter makes the relation nonzero. -/
theorem exists_ne_zero_blockSplitRelation {ι : Type*} [Fintype ι] (c : ℝ) (β d : ι → ℝ)
    (hd : ∀ z, d z ≠ 0) (hweight : ∑ z, β z * (1 / |d z|) ≠ 0) {V : Set ℝ} (hV : V ∈ 𝓝 (0 : ℝ)) :
    ∃ u ∈ V, blockSplitRelation c β d u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine not_eventuallyEq_zero_blockSplitRelation c β d hd hweight ?_
  filter_upwards [hV] with u hu
  exact hcon u hu

end

end GaloisForLFunctions.HTGeometry
