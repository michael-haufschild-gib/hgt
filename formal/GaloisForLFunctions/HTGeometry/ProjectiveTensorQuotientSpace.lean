import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The projective seminorm is computed in the seminorm space

If `κ : E → X` is a surjective map onto a normed space with `‖κ x‖ = p x`, then the projective
seminorm `p ⊗ q` of a tensor is bounded by the projective seminorm of its image in `X ⊗ F`.  The
converse inequality is functoriality, so the two agree: the projective seminorm only sees the
seminorm space of `p`.

The proof lifts a representation of the image termwise — possible because `κ` is surjective — and
observes that the difference lies in `(ker κ) ⊗ F` by flatness, where the seminorm vanishes.

* `projTensorSeminorm_zero_left` : the projective seminorm vanishes when the first seminorm does.
* `projTensorSeminorm_le_map_of_surjective` : **`π(p,q)(z) ≤ π(‖·‖,q)((κ ⊗ 1) z)`.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F X : Type*} [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ## A vanishing seminorm -/

theorem projTensorSum_eq_zero (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (hp : ∀ x, p x = 0)
    (l : List (E × F)) : projTensorSum p q l = 0 := by
  induction l with
  | nil => simp [projTensorSum]
  | cons a l ih =>
    have hcons : projTensorSum p q (a :: l) = p a.1 * q a.2 + projTensorSum p q l := by
      simp [projTensorSum]
    rw [hcons, hp a.1, zero_mul, zero_add, ih]

theorem projTensorSeminorm_zero_left (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (hp : ∀ x, p x = 0)
    (z : E ⊗[𝕜] F) : projTensorSeminorm p q z = 0 := by
  refine le_antisymm ?_ (apply_nonneg _ _)
  obtain ⟨l⟩ := nonempty_projTensorLift (𝕜 := 𝕜) (E := E) (F := F) z
  have hle : projTensorSeminorm p q ((l.1.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum)
      ≤ projTensorSum p q l.1 := projTensorSeminorm_le_projTensorSum p q l.1
  rw [l.2, projTensorSum_eq_zero p q hp l.1] at hle
  exact hle

/-! ## Lifting a representation along a surjection -/

theorem map_list_sum (κ : E →ₗ[𝕜] X) (m : List (E × F)) :
    TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F)
        ((m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum)
      = (m.map fun xy => (κ xy.1) ⊗ₜ[𝕜] xy.2).sum := by
  induction m with
  | nil => simp
  | cons a m ih =>
    have hsum : ((a :: m).map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum
        = a.1 ⊗ₜ[𝕜] a.2 + (m.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum := by
      simp
    have hsum' : ((a :: m).map fun xy : E × F => (κ xy.1) ⊗ₜ[𝕜] xy.2).sum
        = (κ a.1) ⊗ₜ[𝕜] a.2 + (m.map fun xy : E × F => (κ xy.1) ⊗ₜ[𝕜] xy.2).sum := by
      simp
    rw [hsum, hsum', map_add, ih, TensorProduct.map_tmul, LinearMap.id_apply]

/-- **The projective seminorm is bounded by the projective seminorm of the image** in the seminorm
space of `p`. -/
theorem projTensorSeminorm_le_map_of_surjective (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (κ : E →ₗ[𝕜] X) (hsurj : Function.Surjective κ) (hnorm : ∀ x, ‖κ x‖ = p x) (z : E ⊗[𝕜] F) :
    projTensorSeminorm p q z
      ≤ projTensorSeminorm (normSeminorm 𝕜 X) q
          (TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) z) := by
  classical
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨l, hlsum, hlcost⟩ := exists_projTensorSum_lt (normSeminorm 𝕜 X) q
    (TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) z)
    (a := projTensorSeminorm (normSeminorm 𝕜 X) q
      (TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) z) + ε) (by linarith)
  choose lift hlift using hsurj
  set m : List (E × F) := l.map (fun xy => (lift xy.1, xy.2)) with hm
  set w : E ⊗[𝕜] F := (m.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum with hw
  have hcostgen : ∀ n : List (X × F),
      projTensorSum p q (n.map (fun xy => (lift xy.1, xy.2)))
        = projTensorSum (normSeminorm 𝕜 X) q n := by
    intro n
    induction n with
    | nil => simp [projTensorSum]
    | cons a n ih =>
      have h1 : projTensorSum p q ((a :: n).map (fun xy : X × F => (lift xy.1, xy.2)))
          = p (lift a.1) * q a.2
            + projTensorSum p q (n.map (fun xy : X × F => (lift xy.1, xy.2))) := by
        rw [List.map_cons]
        simp [projTensorSum]
      have hn : (normSeminorm 𝕜 X) a.1 = ‖a.1‖ := rfl
      have h2 : projTensorSum (normSeminorm 𝕜 X) q (a :: n)
          = ‖a.1‖ * q a.2 + projTensorSum (normSeminorm 𝕜 X) q n := by
        rw [projTensorSum, projTensorSum, List.map_cons, List.sum_cons, hn]
      have h3 : p (lift a.1) = ‖a.1‖ := by
        have hval := hnorm (lift a.1)
        rw [hlift a.1] at hval
        exact hval.symm
      rw [h1, h2, h3, ih]
  have hcost : projTensorSum p q m = projTensorSum (normSeminorm 𝕜 X) q l := by
    rw [hm]
    exact hcostgen l
  have himage : TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) w
      = TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) z := by
    rw [hw, map_list_sum, ← hlsum, hm, List.map_map]
    refine congrArg List.sum ?_
    refine List.map_congr_left fun xy _ => ?_
    show (κ (lift xy.1)) ⊗ₜ[𝕜] xy.2 = xy.1 ⊗ₜ[𝕜] xy.2
    rw [hlift xy.1]
  have hker : LinearMap.rTensor F κ (z - w) = 0 := by
    show TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) (z - w) = 0
    rw [map_sub, himage, sub_self]
  haveI : Module.Free 𝕜 F := Module.Free.of_divisionRing 𝕜 F
  haveI : Module.Flat 𝕜 F := Module.Flat.of_free
  have hexact := Module.Flat.rTensor_exact (R := 𝕜) F (LinearMap.exact_subtype_ker_map κ)
  obtain ⟨v, hv⟩ := (hexact (z - w)).mp hker
  have hzero : projTensorSeminorm p q (z - w) = 0 := by
    rw [← hv]
    have hsub : ∀ u : (LinearMap.ker κ), p ((LinearMap.ker κ).subtype u) = 0 := by
      intro u
      rw [← hnorm]
      have : κ ((LinearMap.ker κ).subtype u) = 0 := u.2
      rw [this, norm_zero]
    have hmapv : LinearMap.rTensor F (LinearMap.ker κ).subtype v
        = TensorProduct.map (LinearMap.ker κ).subtype (LinearMap.id : F →ₗ[𝕜] F) v := rfl
    rw [hmapv]
    have hbound := projTensorSeminorm_map_le (p.comp (LinearMap.ker κ).subtype) q p q
      (LinearMap.ker κ).subtype (LinearMap.id : F →ₗ[𝕜] F) zero_le_one zero_le_one
      (fun u => by rw [one_mul, Seminorm.comp_apply]) (fun f => by rw [one_mul]; exact le_rfl) v
    rw [one_mul, one_mul] at hbound
    have hzero' : projTensorSeminorm (p.comp (LinearMap.ker κ).subtype) q v = 0 := by
      refine projTensorSeminorm_zero_left _ q ?_ v
      intro u
      rw [Seminorm.comp_apply]
      exact hsub u
    rw [hzero'] at hbound
    exact le_antisymm hbound (apply_nonneg _ _)
  have hsplit : projTensorSeminorm p q z
      ≤ projTensorSeminorm p q w + projTensorSeminorm p q (z - w) := by
    have h := map_add_le_add (projTensorSeminorm p q) w (z - w)
    rw [add_sub_cancel] at h
    exact h
  calc projTensorSeminorm p q z
      ≤ projTensorSeminorm p q w + projTensorSeminorm p q (z - w) := hsplit
    _ = projTensorSeminorm p q w := by rw [hzero, add_zero]
    _ ≤ projTensorSum p q m := by
        rw [hw]
        exact projTensorSeminorm_le_projTensorSum p q m
    _ = projTensorSum (normSeminorm 𝕜 X) q l := hcost
    _ ≤ projTensorSeminorm (normSeminorm 𝕜 X) q
          (TensorProduct.map κ (LinearMap.id : F →ₗ[𝕜] F) z) + ε := hlcost.le

end GaloisForLFunctions

end
