import GaloisForLFunctions.HTGeometry.ProductCompactConvexFixedPoint
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak compactness and fixed points in Hilbert spaces

Fréchet–Riesz identifies the weak topology with the weak-star topology of the
dual. Banach–Alaoglu therefore makes Hilbert balls weakly compact. Separating
linear functionals transfer compact-convex fixed points from product spaces.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fréchet–Riesz identifies the weak Hilbert topology with the weak-star dual topology. -/
def weakRieszHomeomorph : WeakSpace ℂ H ≃ₜ WeakDual ℂ H where
  toFun x := StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H ((toWeakSpace ℂ H).symm x))
  invFun l := toWeakSpace ℂ H ((InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual l))
  left_inv x := by simp only [StrongDual.toStrongDual_toWeakDual,
    LinearIsometryEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  right_inv l := by simp only [LinearEquiv.symm_apply_apply,
    LinearIsometryEquiv.apply_symm_apply, WeakDual.toWeakDual_toStrongDual]
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro y
    have h : Continuous (fun x : WeakSpace ℂ H =>
        inner ℂ y ((toWeakSpace ℂ H).symm x)) :=
      WeakBilin.eval_continuous (topDualPairing ℂ H).flip (InnerProductSpace.toDual ℂ H y)
    convert h.star using 1
    funext x
    exact (inner_conj_symm _ _).symm
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ H).flip
    intro l
    obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective l
    change Continuous (fun a : WeakDual ℂ H =>
      inner ℂ y ((InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a)))
    convert (WeakDual.eval_continuous (𝕜 := ℂ) y).star using 1
    funext a
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    rfl

/-- The closed radius-`R` Hilbert ball, viewed in the weak topology. -/
def weakHilbertBall (R : ℝ) : Set (WeakSpace ℂ H) :=
  {x | ‖(toWeakSpace ℂ H).symm x‖ ≤ R}

omit [CompleteSpace H] in
theorem convex_weakHilbertBall (R : ℝ) : Convex ℝ (weakHilbertBall (H := H) R) := by
  have he : weakHilbertBall (H := H) R =
      (toWeakSpace ℂ H).symm ⁻¹' Metric.closedBall (0 : H) R := by
    ext x
    simp only [weakHilbertBall, mem_setOf_eq, mem_preimage, Metric.mem_closedBall,
      dist_zero_right]
  rw [he]
  exact (convex_closedBall (0 : H) R).linear_preimage
    ((toWeakSpace ℂ H).symm.toLinearMap.restrictScalars ℝ)

omit [CompleteSpace H] in
theorem nonempty_weakHilbertBall {R : ℝ} (hR : 0 ≤ R) :
    (weakHilbertBall (H := H) R).Nonempty :=
  ⟨0, by simpa only [weakHilbertBall, mem_setOf_eq, map_zero, norm_zero] using hR⟩

theorem isCompact_weakHilbertBall (R : ℝ) :
    IsCompact (weakHilbertBall (H := H) R) := by
  let S : Set (WeakDual ℂ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  have he : weakHilbertBall (H := H) R = weakRieszHomeomorph.symm '' S := by
    ext x
    constructor
    · intro hx
      refine ⟨weakRieszHomeomorph x, ?_, Homeomorph.symm_apply_apply _ x⟩
      change dist (InnerProductSpace.toDual ℂ H ((toWeakSpace ℂ H).symm x)) 0 ≤ R
      rw [dist_zero_right, (InnerProductSpace.toDual ℂ H).norm_map]
      exact hx
    · rintro ⟨a, ha, rfl⟩
      change ‖(InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a)‖ ≤ R
      rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
      simpa only [S, mem_preimage, Metric.mem_closedBall, dist_zero_right] using ha
  rw [he]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) R).image
    weakRieszHomeomorph.symm.continuous

/-- Continuous linear functionals separate weak Hilbert vectors. -/
def weakHilbertCoordinates : WeakSpace ℂ H →ₗ[ℝ] (StrongDual ℂ H → ℂ) :=
  ({ toFun := fun x l => l ((toWeakSpace ℂ H).symm x)
     map_add' := fun x y => by ext l; exact map_add l _ _
     map_smul' := fun c x => by ext l; exact map_smul l c _ } :
      WeakSpace ℂ H →ₗ[ℂ] (StrongDual ℂ H → ℂ)).restrictScalars ℝ

omit [CompleteSpace H] in
theorem continuous_weakHilbertCoordinates : Continuous (weakHilbertCoordinates (H := H)) :=
  WeakBilin.coeFn_continuous (topDualPairing ℂ H).flip

omit [CompleteSpace H] in
theorem injective_weakHilbertCoordinates : Function.Injective (weakHilbertCoordinates (H := H)) := by
  intro x y h
  apply (toWeakSpace ℂ H).symm.injective
  by_contra hne
  obtain ⟨l, hl⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) hne
  exact hl (congrFun h l)

omit [CompleteSpace H] in
/-- Every weakly continuous self-map of a nonempty weakly compact convex Hilbert set fixes a point. -/
theorem exists_fixedPoint_weakHilbert_convex {K : Set (WeakSpace ℂ H)}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : K → K) (hf : Continuous f) : ∃ x, f x = x :=
  exists_fixedPoint_compact_convex_of_linear_injection weakHilbertCoordinates
    continuous_weakHilbertCoordinates injective_weakHilbertCoordinates hK hne hconv f hf

end GaloisForLFunctions.HTGeometry
