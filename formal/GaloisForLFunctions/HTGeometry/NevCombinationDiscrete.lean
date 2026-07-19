import GaloisForLFunctions.HTGeometry.NevanlinnaEntire

/-!
# Zeros of the Nevanlinna combination are isolated on the whole plane

`NevZeroDichotomy` obtained the identity-theorem alternative only on an open set carrying uniform
kernel bounds, so the "vanishes identically nearby" branch could not be ruled out globally.  With the
entries entire, the plane itself is such a set, and `ℂ` is connected: a single point where the
combination is nonzero forces every zero to be isolated.

The values at the origin are the classical normalisation `A(0) = 0`, `B(0) = -1`, `C(0) = 1`,
`D(0) = 0`, and they supply that point for every `τ ≠ 0` and for `B` itself.
-/

open scoped BigOperators
open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

@[simp] theorem nevAinf_zero (s : ℕ → ℝ) : nevAinf s 0 = 0 := by simp [nevAinf]

@[simp] theorem nevBinf_zero (s : ℕ → ℝ) : nevBinf s 0 = -1 := by simp [nevBinf]

@[simp] theorem nevCinf_zero (s : ℕ → ℝ) : nevCinf s 0 = 1 := by simp [nevCinf]

@[simp] theorem nevDinf_zero (s : ℕ → ℝ) : nevDinf s 0 = 0 := by simp [nevDinf]

/-- **Isolated zeros for an entire function that is somewhere nonzero.**  The local dichotomy plus
connectedness of `ℂ`. -/
theorem eventually_ne_zero_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z₁ : ℂ} (hne : f z₁ ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  have hana : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  rcases (hana z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exfalso
    have heq : Set.EqOn f 0 Set.univ :=
      hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) hz
    exact hne (by simpa using heq (Set.mem_univ z₁))
  · exact hz

/-- The combination `B τ − D` is entire. -/
theorem differentiable_nevCombination (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℂ) : Differentiable ℂ fun w => nevBinf s w * tau - nevDinf s w := by
  obtain ⟨-, hB, -, hD, -⟩ := nevanlinna_entire_unimodular h h0b
  exact (hB.mul_const tau).sub hD

/-- At the origin the combination takes the value `-τ`. -/
theorem nevCombination_at_zero (s : ℕ → ℝ) (tau : ℂ) :
    nevBinf s 0 * tau - nevDinf s 0 = -tau := by
  rw [nevBinf_zero, nevDinf_zero]
  ring

/-- **The zeros of `B τ − D` are isolated, for every `τ ≠ 0`.**  These zero sets are the supports of
the N-extremal measures in the Nevanlinna parametrization. -/
theorem eventually_ne_zero_nevCombination (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {tau : ℂ} (htau : tau ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, nevBinf s w * tau - nevDinf s w ≠ 0 := by
  refine eventually_ne_zero_of_entire (differentiable_nevCombination h h0b tau)
    (z₁ := 0) ?_ z
  rw [nevCombination_at_zero]
  exact neg_ne_zero.mpr htau

/-- **The zeros of `B` are isolated.**  This is the `τ = ∞` member of the same family. -/
theorem eventually_ne_zero_nevBinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, nevBinf s w ≠ 0 := by
  obtain ⟨-, hB, -, -, -⟩ := nevanlinna_entire_unimodular h h0b
  refine eventually_ne_zero_of_entire hB (z₁ := 0) ?_ z
  rw [nevBinf_zero]
  exact neg_ne_zero.mpr one_ne_zero

/-- `B` and `D` have no common zero: the determinant identity forbids it. -/
theorem nevBinf_ne_zero_or_nevDinf_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (z : ℂ) : nevBinf s z ≠ 0 ∨ nevDinf s z ≠ 0 := by
  obtain ⟨-, -, -, -, hdet⟩ := nevanlinna_entire_unimodular h h0b
  by_contra hcon
  rw [not_or, not_ne_iff, not_ne_iff] at hcon
  have := hdet z
  rw [hcon.1, hcon.2] at this
  simp at this

end HTGeometry
