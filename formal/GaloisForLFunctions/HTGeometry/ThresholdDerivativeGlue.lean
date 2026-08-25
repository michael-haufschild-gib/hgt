import Mathlib

/-!
# Derivative gluing across a real threshold

Two differentiable real functions with matching value and derivative at a threshold glue to a
differentiable `if` expression.  This small lemma avoids imposing a neighborhood agreement that is
unavailable for the polynomial/exponential radial splice used by the rapid Fock carrier.
-/

open Filter Set

namespace HTGeometry

/-- Matching first derivatives and values glue the derivative at the threshold itself. -/
theorem hasDerivAt_ite_lt_boundary
    {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hval : f c = g c) :
    HasDerivAt (fun x => if x < c then f x else g x) d c := by
  rw [hasDerivAt_iff_tendsto_slope] at hf hg ⊢
  have ht := Filter.Tendsto.if' (p := fun x : ℝ => x < c) hf hg
  have heq : (fun x => if x < c then slope f c x else slope g c x) =
      slope (fun x => if x < c then f x else g x) c := by
    funext x
    unfold slope
    by_cases hx : x < c
    · simp [hx, hval]
    · simp [hx]
  rw [← heq]
  exact ht

/-- Pointwise derivative formula for a two-piece real function whose value and derivative match at
the threshold. -/
theorem hasDerivAt_ite_lt
    {f g f' g' : ℝ → ℝ} {c x : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : ∀ y, HasDerivAt g (g' y) y)
    (hval : f c = g c) (hderiv : f' c = g' c) :
    HasDerivAt (fun y => if y < c then f y else g y)
      (if x < c then f' x else g' x) x := by
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · rw [if_pos hxc]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxc] with y hy
    change y < c at hy
    simp [hy]
  · subst x
    simp only [lt_self_iff_false, if_false]
    exact hasDerivAt_ite_lt_boundary (by simpa [hderiv] using hf c) (hg c) hval
  · rw [if_neg (not_lt.mpr hcx.le)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hcx] with y hy
    change c < y at hy
    simp [not_lt.mpr hy.le]

/-- Continuous real functions with a common threshold value glue continuously across `<`. -/
theorem continuous_ite_lt
    {f g : ℝ → ℝ} {c : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hval : f c = g c) :
    Continuous (fun x => if x < c then f x else g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · apply hf.continuousAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxc] with y hy
    change y < c at hy
    simp [hy]
  · subst x
    have hg' : Tendsto g (nhds c) (nhds (f c)) := by
      rw [hval]
      exact hg.continuousAt
    have ht := Filter.Tendsto.if' (p := fun x : ℝ => x < c) hf.continuousAt hg'
    simpa [ContinuousAt, hval] using ht
  · apply hg.continuousAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hcx] with y hy
    change c < y at hy
    simp [not_lt.mpr hy.le]

/-- A globally specified derivative with `C^n` regularity promotes its primitive to `C^(n+1)`. -/
theorem contDiff_succ_of_hasDerivAt
    {n : ℕ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ContDiff ℝ n f') :
    ContDiff ℝ (n + 1) f := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
  rw [show deriv f = f' by
    funext x
    exact (hf x).deriv]
  exact hf'

end HTGeometry
