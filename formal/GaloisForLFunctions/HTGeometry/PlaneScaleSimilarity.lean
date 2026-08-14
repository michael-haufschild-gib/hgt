import GaloisForLFunctions.HTGeometry.EllipticReparamCurrent
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Scaling the variable is a similarity of the meromorphic plane field

Pullback along `z ↦ m z` is a field automorphism of the meromorphic functions of the plane which
rescales the derivation rather than preserving it:

`(f (m ·))′ = m · f′(m ·)`.

Together with the fact that it fixes the constants, this is exactly the data a similarity extension
to the generic reparametrisation consumes, so an isogeny pullback and an orbifold rotation both act
on the differential-generic carrier.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- Scaling the variable, as a field automorphism of the meromorphic plane field. -/
noncomputable def planeScaleEquiv (m : ℂ) (hm : m ≠ 0) :
    MeromorphicPlane ≃+* MeromorphicPlane where
  toFun := planeScale m hm
  invFun := planeScale m⁻¹ (inv_ne_zero hm)
  left_inv := by
    intro x
    rw [planeScale_planeScale (inv_ne_zero hm) hm x,
      planeScale_congr (mul_ne_zero hm (inv_ne_zero hm)) one_ne_zero (mul_inv_cancel₀ hm) x,
      planeScale_one]
  right_inv := by
    intro x
    rw [planeScale_planeScale hm (inv_ne_zero hm) x,
      planeScale_congr (mul_ne_zero (inv_ne_zero hm) hm) one_ne_zero (inv_mul_cancel₀ hm) x,
      planeScale_one]
  map_add' := planeScale_map_add m hm
  map_mul' := planeScale_map_mul m hm

@[simp] theorem planeScaleEquiv_apply (m : ℂ) (hm : m ≠ 0) (x : MeromorphicPlane) :
    planeScaleEquiv m hm x = planeScale m hm x := rfl

/-- Scaling the variable fixes the constants. -/
@[simp] theorem planeScale_constPlane (m : ℂ) (hm : m ≠ 0) (c : ℂ) :
    planeScale m hm (constPlane c) = constPlane c := by
  have hdef : constPlane c = ofMeromorphic (fun _ : ℂ => c) (fun z => MeromorphicAt.const c z) :=
    rfl
  rw [hdef, planeScale_ofMeromorphic]

/-- **Scaling the variable is a similarity.**  The derivative acquires the scaling factor. -/
theorem planeScale_deriv (m : ℂ) (hm : m ≠ 0) (x : MeromorphicPlane) :
    Differential.deriv (planeScale m hm x)
      = constPlane m * planeScale m hm (Differential.deriv x) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeScale_ofMeromorphic]
  show meromorphicPlaneDeriv _ = _
  rw [meromorphicPlaneDeriv_ofMeromorphic]
  show _ = constPlane m * planeScale m hm (meromorphicPlaneDeriv (ofMeromorphic f hf))
  rw [meromorphicPlaneDeriv_ofMeromorphic, planeScale_ofMeromorphic]
  have hprod : constPlane m
      * ofMeromorphic (fun z => deriv f (m * z)) (fun z =>
          MeromorphicAt.comp_analyticAt (f := deriv f) (g := fun w : ℂ => m * w)
            ((hf (m * z)).deriv) (by fun_prop))
      = ofMeromorphic (fun z => m * deriv f (m * z)) (fun z =>
          (MeromorphicAt.const m z).fun_mul
            (MeromorphicAt.comp_analyticAt (f := deriv f) (g := fun w : ℂ => m * w)
              ((hf (m * z)).deriv) (by fun_prop))) := rfl
  rw [hprod]
  refine (ofMeromorphic_eq_iff _ _).mpr fun x => ?_
  refine Filter.Eventually.of_forall fun z => ?_
  simpa using deriv_comp_mul_left (c := m) (f := f) (x := z)

end GaloisForLFunctions.HTGeometry
