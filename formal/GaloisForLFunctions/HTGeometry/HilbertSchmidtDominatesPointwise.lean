import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# The Hilbert--Schmidt norm dominates every pointwise value on the unit sphere

A unit vector extends to a Hilbert basis, and the Hilbert--Schmidt norm squared is the sum over any
Hilbert basis of the squared image norms.  One term of a convergent nonnegative sum is at most the
sum, so the image of a unit vector never exceeds the Hilbert--Schmidt norm.

This is the bridge from a quantitative lower bound on the action of an operator on an explicit unit
vector to a lower bound on its Hilbert--Schmidt energy.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Pointwise domination.**  On a unit vector the image norm squared is at most the squared
Hilbert--Schmidt norm. -/
theorem norm_sq_apply_le_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {x : E} (hx : ‖x‖ = 1) : ‖T x‖ ^ 2 ≤ hsNormSq T := by
  have hortho : Orthonormal 𝕜 ((↑) : ({x} : Set E) → E) := by
    constructor
    · rintro ⟨v, hv⟩
      rw [Set.mem_singleton_iff] at hv
      simpa [hv] using hx
    · rintro ⟨v, hv⟩ ⟨u, hu⟩ hne
      rw [Set.mem_singleton_iff] at hv hu
      exact absurd (Subtype.ext (hv.trans hu.symm)) hne
  obtain ⟨w, b, hsub, hb⟩ := hortho.exists_hilbertBasis_extension
  have hxw : x ∈ w := hsub (Set.mem_singleton x)
  have hbx : b ⟨x, hxw⟩ = x := by rw [hb]
  have hsummable : Summable fun i : w => ‖T (b i)‖ ^ 2 :=
    summable_normSq_basis_of_basis (hsBasis 𝕜 E) b T hT
  have hsum : hsNormSq T = ∑' i : w, ‖T (b i)‖ ^ 2 := hsNormSq_eq hT b
  rw [hsum, ← hbx]
  exact Summable.le_tsum hsummable ⟨x, hxw⟩ fun j _ => by positivity

end RHTower
