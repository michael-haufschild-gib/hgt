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
    have hsub : HasFDerivAt (fun y => finiteMax X y - X z y) (Lmax - Lz) (x + (0 : ℝ) • v) := by
      rw [hx0]
      exact hmax.sub hzd
    have hd : HasDerivAt (fun t : ℝ => finiteMax X (x + t • v) - X z (x + t • v))
        (Lmax v - Lz v) 0 := by
      have hcomp := hsub.comp_hasDerivAt 0 hg
      rw [sub_apply] at hcomp
      exact hcomp
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

/-- **An active gradient realizes the gradient of the maximum.** -/
theorem exists_fderiv_finiteMax_eq {X : ι → E → ℝ} {x : E}
    (hXd : ∀ z, DifferentiableAt ℝ (X z) x) (hmax : DifferentiableAt ℝ (finiteMax X) x) :
    ∃ z, fderiv ℝ (finiteMax X) x = fderiv ℝ (X z) x := by
  obtain ⟨z, hz⟩ := exists_eq_finiteMax X x
  exact ⟨z, hasFDerivAt_finiteMax_eq hz hmax.hasFDerivAt (hXd z).hasFDerivAt⟩

/-- A uniform bound on the derivatives of the family bounds the derivative of the maximum at every
point of differentiability. -/
theorem norm_fderiv_finiteMax_le {X : ι → E → ℝ} {x : E} {K : ℝ}
    (hXd : ∀ z, DifferentiableAt ℝ (X z) x) (hmax : DifferentiableAt ℝ (finiteMax X) x)
    (hK : ∀ z, ‖fderiv ℝ (X z) x‖ ≤ K) : ‖fderiv ℝ (finiteMax X) x‖ ≤ K := by
  obtain ⟨z, hz⟩ := exists_fderiv_finiteMax_eq hXd hmax
  rw [hz]
  exact hK z

theorem abs_finiteMax_sub_finiteMax_le (X : ι → E → ℝ) (x y : E) :
    |finiteMax X x - finiteMax X y| ≤ Finset.univ.sup' Finset.univ_nonempty
      fun z => |X z x - X z y| := by
  have hbound : ∀ u v : E, finiteMax X u - finiteMax X v ≤
      Finset.univ.sup' Finset.univ_nonempty fun z => |X z u - X z v| := by
    intro u v
    obtain ⟨z, hz⟩ := exists_eq_finiteMax X u
    have h1 : X z v ≤ finiteMax X v := le_finiteMax X v z
    have h2 : X z u - X z v ≤ |X z u - X z v| := le_abs_self _
    have h3 : |X z u - X z v| ≤ Finset.univ.sup' Finset.univ_nonempty
        fun w => |X w u - X w v| :=
      Finset.le_sup' (fun w => |X w u - X w v|) (Finset.mem_univ z)
    rw [← hz]
    linarith
  have hsymm : (Finset.univ.sup' Finset.univ_nonempty fun z => |X z y - X z x|) =
      Finset.univ.sup' Finset.univ_nonempty fun z => |X z x - X z y| := by
    refine Finset.sup'_congr _ rfl fun z _ => ?_
    rw [abs_sub_comm]
  rw [abs_le]
  refine ⟨?_, hbound x y⟩
  have := hbound y x
  rw [hsymm] at this
  linarith

/-- A finite maximum of Lipschitz functions is Lipschitz with the same constant. -/
theorem lipschitzWith_finiteMax {X : ι → E → ℝ} {L : NNReal}
    (h : ∀ z, LipschitzWith L (X z)) : LipschitzWith L (finiteMax X) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  refine le_trans (abs_finiteMax_sub_finiteMax_le X x y) ?_
  refine Finset.sup'_le _ _ fun z _ => ?_
  have := (h z).dist_le_mul x y
  rwa [Real.dist_eq] at this

end FiniteMax

end GaloisForLFunctions.HTGeometry
