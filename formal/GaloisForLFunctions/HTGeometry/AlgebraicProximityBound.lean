import GaloisForLFunctions.HTGeometry.AlgebraicRootGrowth
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# Proximity of an algebraic element

An element satisfying a polynomial relation with a nonvanishing top coefficient is bounded, on every
circle, by the normalised lower coefficients.  Averaging turns that pointwise estimate into a bound
on its Nevanlinna proximity function: an algebraic element cannot approach infinity faster than the
coefficients of its equation.

This is the value-distribution form of the algebraic root estimate, and it is the comparison a
composition-growth argument needs in the direction "algebraic over a field cannot outgrow it".
-/

open Real ValueDistribution

namespace GaloisForLFunctions.HTGeometry

/-- **The root estimate in additive form.**  A root of a monic-after-normalisation polynomial is
logarithmically bounded by the sum of the normalised lower coefficients. -/
theorem posLog_norm_le_of_root_sum {n : ℕ} (hn : 1 ≤ n) {g : ℂ} {c : ℕ → ℂ} (hcn : c n ≠ 0)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * g ^ i = 0) :
    Real.posLog ‖g‖ ≤ Real.log n + ∑ i ∈ Finset.range n, Real.posLog ‖c i / c n‖ := by
  refine le_trans (posLog_norm_le_of_root hn hcn hrel) ?_
  have hsum := Real.posLog_sum (Finset.range n) (fun i => ‖c i / c n‖)
  simpa using hsum

/-- **The proximity bound for an algebraic element.**  On a circle where the top coefficient does not
vanish, the proximity of a root is at most that of the normalised lower coefficients. -/
theorem proximity_le_of_root {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {r : ℝ}
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n, proximity (fun z => a i z / a n z) ⊤ r := by
  classical
  have hquot : ∀ i, Meromorphic (fun z => a i z / a n z) := fun i => (ha i).div (ha n)
  have hgint : CircleIntegrable (Real.posLog ‖g ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hg x)
  have hqint : ∀ i ∈ Finset.range n,
      CircleIntegrable (Real.posLog ‖(fun z => a i z / a n z) ·‖) 0 r :=
    fun i _ => MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hquot i x)
  have hbound : circleAverage (Real.posLog ‖g ·‖) 0 r
      ≤ circleAverage
          ((∑ i ∈ Finset.range n, Real.posLog ‖(fun z => a i z / a n z) ·‖)
            + fun _ => Real.log n) 0 r := by
    refine circleAverage_mono hgint
      ((CircleIntegrable.fun_sum (Finset.range n) hqint).add
        (circleIntegrable_const _ _ _)) ?_
    intro x hx
    simp only [Pi.add_apply]
    rw [add_comm]
    exact posLog_norm_le_of_root_sum hn (hcirc x hx) (hrel x)
  have hpi : (fun x : ℂ => ∑ i ∈ Finset.range n, Real.posLog ‖(fun z => a i z / a n z) x‖)
      = ∑ i ∈ Finset.range n, (fun x : ℂ => Real.posLog ‖(fun z => a i z / a n z) x‖) := by
    funext x
    rw [Finset.sum_apply]
  rw [hpi, circleAverage_add (CircleIntegrable.sum (Finset.range n) hqint)
    (circleIntegrable_const (Real.log n) 0 r), circleAverage_sum hqint,
    circleAverage_const] at hbound
  have hgoal : proximity g ⊤ r = circleAverage (Real.posLog ‖g ·‖) 0 r := by
    rw [proximity_top]
  have hgoal2 : ∀ i : ℕ, proximity (fun z => a i z / a n z) ⊤ r
      = circleAverage (Real.posLog ‖(fun z => a i z / a n z) ·‖) 0 r := by
    intro i
    rw [proximity_top]
  rw [hgoal, Finset.sum_congr rfl (fun i _ => hgoal2 i)]
  linarith [hbound]

/-- **The proximity bound in terms of the coefficients themselves.**  Splitting each normalised
coefficient into the coefficient and the reciprocal of the top one. -/
theorem proximity_le_of_root_coeff {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {r : ℝ}
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (proximity (a i) ⊤ r + proximity (a n) 0 r) := by
  have hstep : ∑ i ∈ Finset.range n, proximity (fun z => a i z / a n z) ⊤ r
      ≤ ∑ i ∈ Finset.range n, (proximity (a i) ⊤ r + proximity (a n) 0 r) := by
    refine Finset.sum_le_sum ?_
    intro i _
    have hfun : (fun z => a i z / a n z) = (a i) * (a n)⁻¹ := by
      funext z
      rw [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hfun]
    have hmul := proximity_mul_top_le (ha i) (ha n).inv r
    rw [Pi.add_apply, proximity_inv] at hmul
    exact hmul
  linarith [proximity_le_of_root hn hg ha hcirc hrel, hstep]

/-! ## In terms of the characteristic function -/

/-- The proximity function is at most the characteristic function on `[1, ∞)`. -/
theorem proximity_le_characteristic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : WithTop E} {r : ℝ} (hr : 1 ≤ r) :
    proximity f a r ≤ characteristic f a r := by
  have hdef : characteristic f a r = proximity f a r + logCounting f a r := rfl
  have hnn : 0 ≤ logCounting f a r := logCounting_nonneg hr
  rw [hdef]
  linarith

/-- **An algebraic element is bounded by the characteristics of its coefficients.** -/
theorem proximity_le_of_root_characteristic {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ}
    {r : ℝ} (hr : 1 ≤ r)
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (characteristic (a i) ⊤ r + characteristic (a n) 0 r) := by
  have hstep : ∑ i ∈ Finset.range n, (proximity (a i) ⊤ r + proximity (a n) 0 r)
      ≤ ∑ i ∈ Finset.range n, (characteristic (a i) ⊤ r + characteristic (a n) 0 r) := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact add_le_add (proximity_le_characteristic hr) (proximity_le_characteristic hr)
  linarith [proximity_le_of_root_coeff hn hg ha hcirc hrel, hstep]

end GaloisForLFunctions.HTGeometry
