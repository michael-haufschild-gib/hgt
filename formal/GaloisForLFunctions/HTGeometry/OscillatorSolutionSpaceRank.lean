import GaloisForLFunctions.HTGeometry.OscillatorKineticIntegrable
import GaloisForLFunctions.HTGeometry.LinearSecondOrderUnique

/-!
# The square-integrable solution space of the oscillator is at most one dimensional

For two square-integrable solutions of `v″ = (ξ²−μ)v` the cross-Wronskian `W = v′w − vw′` is a sum
of products of square-integrable factors, hence integrable on the line; being constant, and the line
having infinite measure, it must vanish.  A vanishing Wronskian makes the two solutions
proportional.

So a square-integrable solution is determined up to scale by its rung: in particular its parity is
that of the rung, which is what separates the even sector of the prolate spectrum from the odd one.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A summand of an integrable sum of nonnegative terms is integrable. -/
theorem integrable_of_add_nonneg {f g : ℝ → ℝ} (hf : Continuous f)
    (hfnn : ∀ x, 0 ≤ f x) (hgnn : ∀ x, 0 ≤ g x)
    (h : Integrable fun x => f x + g x) : Integrable f := by
  refine h.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
  linarith [hgnn x]

/-- A product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_sq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable fun x => f x ^ (2 : ℕ)) (hgi : Integrable fun x => g x ^ (2 : ℕ)) :
    Integrable fun x => f x * g x := by
  have hdom : Integrable fun x => (f x ^ (2 : ℕ) + g x ^ (2 : ℕ)) / 2 := (hfi.add hgi).div_const 2
  refine hdom.mono' (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x),
    abs_nonneg (f x), abs_nonneg (g x)]

/-- **The cross-Wronskian of two square-integrable modes vanishes.** -/
theorem secondOrderWronskian_eq_zero_of_integrable {mu : ℝ} {v v' w w' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ (2 : ℕ))
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x)
    (hvnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0) (hvint : Integrable fun x => v x ^ (2 : ℕ))
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : ∀ x, HasDerivAt w' ((x ^ (2 : ℕ) - mu) * w x) x)
    (hwnt : ∀ y, w y ≠ 0 ∨ w' y ≠ 0) (hwint : Integrable fun x => w x ^ (2 : ℕ)) :
    ∀ x, secondOrderWronskian v v' w w' x = 0 := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hcv' : Continuous v' := continuous_of_hasDerivAt hv'
  have hcw : Continuous w := continuous_of_hasDerivAt hw
  have hcw' : Continuous w' := continuous_of_hasDerivAt hw'
  -- the derivatives are square integrable
  have hv'i : Integrable fun x => v' x ^ (2 : ℕ) :=
    integrable_of_add_nonneg (hcv'.pow 2) (fun x => sq_nonneg _)
      (fun x => by positivity) (integrable_kinetic_add_moment ha hmu hv hv' hvnt hvint)
  have hw'i : Integrable fun x => w' x ^ (2 : ℕ) :=
    integrable_of_add_nonneg (hcw'.pow 2) (fun x => sq_nonneg _)
      (fun x => by positivity) (integrable_kinetic_add_moment ha hmu hw hw' hwnt hwint)
  -- so the Wronskian is integrable
  have hWi : Integrable (secondOrderWronskian v v' w w') := by
    rw [secondOrderWronskian_eq]
    exact (integrable_mul_of_sq hcv' hcw hv'i hwint).sub
      (integrable_mul_of_sq hcv hcw' hvint hw'i)
  -- and constant
  have hconst : ∀ x, secondOrderWronskian v v' w w' x
      = secondOrderWronskian v v' w w' 0 :=
    fun x => secondOrderWronskian_const hv hv' hw hw' x 0
  have hfun : (secondOrderWronskian v v' w w')
      = fun _ : ℝ => secondOrderWronskian v v' w w' 0 := funext hconst
  rw [hfun] at hWi
  rcases integrable_const_iff.1 hWi with h | h
  · intro x
    rw [hconst x, h]
  · exact absurd (h.measure_univ_lt_top) (by simp)

/-- **One-dimensionality.**  Two square-integrable modes at the same rung are proportional, as soon
as one of them does not vanish at the origin. -/
theorem eq_smul_of_integrable {mu : ℝ} {v v' w w' : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hmu : mu < a ^ (2 : ℕ))
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' ((x ^ (2 : ℕ) - mu) * v x) x)
    (hvnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0) (hvint : Integrable fun x => v x ^ (2 : ℕ))
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : ∀ x, HasDerivAt w' ((x ^ (2 : ℕ) - mu) * w x) x)
    (hwnt : ∀ y, w y ≠ 0 ∨ w' y ≠ 0) (hwint : Integrable fun x => w x ^ (2 : ℕ))
    (hv0 : v 0 ≠ 0) :
    w = fun x => (w 0 / v 0) * v x := by
  have hP : Continuous fun x : ℝ => x ^ (2 : ℕ) - mu :=
    (continuous_pow 2).sub continuous_const
  exact secondOrder_eq_smul_of_wronskian_zero hP hv hv' hw hw' hv0
    (secondOrderWronskian_eq_zero_of_integrable ha hmu hv hv' hvnt hvint hw hw' hwnt hwint 0)

end GaloisForLFunctions.HTGeometry
