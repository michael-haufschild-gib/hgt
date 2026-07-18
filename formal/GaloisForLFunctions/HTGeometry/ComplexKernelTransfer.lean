import GaloisForLFunctions.HTGeometry.ComplexSecondKind

/-!
# Global transfer of kernel convergence

`isOpen_boundedKernel` shows that the set of points where both kernel roots are bounded is open.
Since `ℂ` is connected, that set is everything as soon as it is nonempty *and closed*.

This module isolates that final implication.  Closedness is the one genuinely analytic input still
missing: the local absorption argument cannot supply it, because the propagated bounds double at
each step while the transfer radius `1 / (4 h₀ S P)` shrinks by a factor of four, so no iteration of
the local statement reaches a limit point with control.  Classically closedness comes from local
uniform convergence and a normal-families argument.

Stating the implication separately keeps the dependency explicit: everything here is unconditional
Lean, with closedness appearing as a named hypothesis rather than as an assumption baked into a
definition.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Clopen ⇒ everywhere.**  If the good set is closed as well as open, and is nonempty, then every
point of `ℂ` is good. -/
theorem boundedKernel_of_isClosed (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z₀ : ℂ} (hz₀ : BoundedKernel s z₀) (z : ℂ) : BoundedKernel s z := by
  have hclopen : IsClopen {z : ℂ | BoundedKernel s z} :=
    ⟨hclosed, isOpen_boundedKernel h⟩
  have hne : {z : ℂ | BoundedKernel s z}.Nonempty := ⟨z₀, hz₀⟩
  have huniv : {z : ℂ | BoundedKernel s z} = Set.univ := by
    exact hclopen.eq_univ hne
  have : z ∈ {z : ℂ | BoundedKernel s z} := by
    rw [huniv]
    exact Set.mem_univ z
  exact this

/-- **Everywhere summability from one point**, modulo closedness of the good set. -/
theorem summable_kernel_everywhere_of_isClosed (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z₀ : ℂ} (hz₀ : BoundedKernel s z₀) (z : ℂ) :
    Summable (fun k => Complex.normSq (monicOrthoC s k z) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :=
  summable_of_boundedKernel h (boundedKernel_of_isClosed h hclosed hz₀ z)

end HTGeometry
