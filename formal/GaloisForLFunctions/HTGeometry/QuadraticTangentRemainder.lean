import Mathlib

/-!
# Differentiation through a quadratic remainder

A quadratic error in a differentiable comparison parameter has zero first
variation. Adding it preserves the comparison function's linear tangent.
-/

open Filter Topology Asymptotics
namespace GaloisForLFunctions.HTGeometry

/-- A quadratic error in a differentiable comparison parameter preserves its linear tangent. -/
theorem hasDerivAt_of_quadratic_comparison {f g : ℝ → ℝ} {x c g' C : ℝ}
    (hg : HasDerivAt g g' x)
    (hbound : ∀ᶠ y in 𝓝 x,
      ‖f y - f x - c * (g y - g x)‖ ≤ C * ‖g y - g x‖ ^ 2) :
    HasDerivAt f (c * g') x := by
  have hsq : HasDerivAt (fun y => (g y - g x) ^ 2) 0 x := by
    have h := (hg.sub_const (g x)).pow 2
    have heq : (fun y => g y - g x) ^ 2 = (fun y => (g y - g x) ^ 2) := rfl
    rw [heq] at h
    simpa using h
  have hqsmall : (fun y => (g y - g x) ^ 2) =o[𝓝 x] (fun y => y - x) := by
    simpa only [sub_self, zero_pow two_ne_zero, sub_zero, smul_zero] using
      hasDerivAt_iff_isLittleO.mp hsq
  have heBig : (fun y => f y - f x - c * (g y - g x)) =O[𝓝 x]
      (fun y => (g y - g x) ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨C, ?_⟩
    filter_upwards [hbound] with y hy
    simpa only [Real.norm_eq_abs, sq_abs, abs_sq] using hy
  have hsum := (heBig.trans_isLittleO hqsmall).add
    (hasDerivAt_iff_isLittleO.mp (hg.const_mul c))
  rw [hasDerivAt_iff_isLittleO]
  have heq : (fun y => f y - f x - (y - x) • (c * g')) =
      fun y => (f y - f x - c * (g y - g x)) +
        (c * g y - c * g x - (y - x) • (c * g')) := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [heq]
  exact hsum

#print axioms hasDerivAt_of_quadratic_comparison
end GaloisForLFunctions.HTGeometry
