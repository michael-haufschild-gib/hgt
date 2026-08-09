import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# A functional on an `lp` space is determined by its values on the single-support elements

Every element of `lp E p` with `p ≠ ∞` is the unbounded sum of its single-support pieces, so a
continuous linear functional vanishing on all of them vanishes identically.  This is the
annihilator computation for a coefficient factor indexed by a countable set — for instance a
weighted sequence space indexed by the primes, where the single-support elements are the scaled
Dirac masses.

* `HTGeometry.eq_zero_of_forall_apply_lp_single`.
-/

noncomputable section

namespace HTGeometry

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] [DecidableEq α]
  {p : ENNReal} [Fact (1 ≤ p)] [∀ i, NormedSpace ℝ (E i)]

/-- **A continuous functional vanishing on every single-support element is zero.**  Each element is
the sum of its single-support pieces, and a continuous linear map preserves that sum. -/
theorem eq_zero_of_forall_apply_lp_single (hp : p ≠ ⊤) (F : (lp E p) →L[ℝ] ℝ)
    (h : ∀ (i : α) (a : E i), F (lp.single p i a) = 0) : ∀ f : lp E p, F f = 0 := by
  intro f
  have hsum : HasSum (fun i => lp.single p i ((f : ∀ i, E i) i)) f := lp.hasSum_single hp f
  have hmap : HasSum (fun i => F (lp.single p i ((f : ∀ i, E i) i))) (F f) :=
    hsum.map F F.continuous
  have hfun : (fun i => F (lp.single p i ((f : ∀ i, E i) i))) = fun _ : α => (0 : ℝ) := by
    funext i
    exact h i _
  rw [hfun] at hmap
  exact (hasSum_zero.unique hmap).symm

end HTGeometry
