import Mathlib

/-!
# The gradient of a finite maximum is an active gradient

A finite maximum of differentiable functions is differentiable only almost everywhere, but wherever
it is differentiable its derivative is forced: comparing one-sided difference quotients against any
function attaining the maximum shows that the derivative of the maximum agrees with the derivative
of that function in every direction.

Consequently a pointwise bound valid for the derivative of every member of the family is inherited
by the maximum at every point of differentiability, with no convexity or uniqueness assumption.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section FiniteMax

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The pointwise finite maximum of a family of real functions. -/
noncomputable def finiteMax (X : ι → E → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun z => X z x

theorem le_finiteMax (X : ι → E → ℝ) (x : E) (z : ι) : X z x ≤ finiteMax X x :=
  Finset.le_sup' (fun z => X z x) (Finset.mem_univ z)

theorem exists_eq_finiteMax (X : ι → E → ℝ) (x : E) : ∃ z, X z x = finiteMax X x := by
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
    (fun z => X z x)
  exact ⟨z, hz.symm⟩

/-- **The derivative of a finite maximum is the derivative of an active member.**  At a point of
differentiability of the maximum, its derivative agrees with the derivative of any member attaining
the maximum there. -/
theorem hasFDerivAt_finiteMax_eq {X : ι → E → ℝ} {x : E} {z : ι}
    (hz : X z x = finiteMax X x) {Lmax Lz : E →L[ℝ] ℝ}
    (hmax : HasFDerivAt (finiteMax X) Lmax x) (hzd : HasFDerivAt (X z) Lz x) :
    Lmax = Lz := by
  have hline : ∀ v : E, Lmax v - Lz v = 0 := by
    intro v
    have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hx0 : x + (0 : ℝ) • v = x := by simp
    have hmax' : HasFDerivAt (finiteMax X) Lmax (x + (0 : ℝ) • v) := by
      rw [hx0]; exact hmax
    have hzd' : HasFDerivAt (X z) Lz (x + (0 : ℝ) • v) := by
      rw [hx0]; exact hzd
    have hlmax : HasDerivAt (fun t : ℝ => finiteMax X (x + t • v)) (Lmax v) 0 := by
      simpa using hmax'.comp_hasDerivAt 0 hg
    have hlz : HasDerivAt (fun t : ℝ => X z (x + t • v)) (Lz v) 0 := by
      simpa using hzd'.comp_hasDerivAt 0 hg
    have hd : HasDerivAt (fun t : ℝ => finiteMax X (x + t • v) - X z (x + t • v))
        (Lmax v - Lz v) 0 := hlmax.sub hlz
    have hmin : IsLocalMin (fun t : ℝ => finiteMax X (x + t • v) - X z (x + t • v)) 0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      have h0 : finiteMax X (x + (0 : ℝ) • v) - X z (x + (0 : ℝ) • v) = 0 := by
        simp [hz]
      have ht : X z (x + t • v) ≤ finiteMax X (x + t • v) := le_finiteMax X _ z
      simp only [h0]
      linarith
    exact hmin.hasDerivAt_eq_zero hd
  refine ContinuousLinearMap.ext fun v => ?_
  have := hline v
  linarith

end FiniteMax

end GaloisForLFunctions.HTGeometry
