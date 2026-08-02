import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The projective tensor seminorm

For seminorms `p` on `E` and `q` on `F`, the projective tensor seminorm on `E ⊗[𝕜] F` sends a
tensor to the infimum of `∑ p(xᵢ) q(yᵢ)` over all representations `∑ xᵢ ⊗ yᵢ`.  It is the largest
seminorm bounded by `p ⊗ q` on pure tensors, and it linearises bounded bilinear maps: a bilinear map
bounded by `C · p · q` induces a linear map bounded by `C` times the projective seminorm.

This is the seminorm layer of the projective topology on a tensor product of locally convex spaces.

* `projTensorSeminorm` : **the projective tensor seminorm.**
* `projTensorSeminorm_tmul_le` : `p ⊗ q` bounds it on pure tensors.
* `projTensorSeminorm_lift_le` : **the universal property for bounded bilinear maps.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F G : Type*} [NormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [AddCommGroup G] [Module 𝕜 G]

/-! ## Representations by lists of pure tensors -/

/-- A representation of a tensor as a finite sum of pure tensors. -/
def projTensorLift (z : E ⊗[𝕜] F) : Type _ :=
  {l : List (E × F) // ((l.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) = z}

theorem nonempty_projTensorLift (z : E ⊗[𝕜] F) : Nonempty (projTensorLift z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨⟨[], by simp⟩⟩
  | tmul x y => exact ⟨⟨[(x, y)], by simp⟩⟩
  | add z w hz hw =>
    obtain ⟨⟨l, hl⟩⟩ := hz
    obtain ⟨⟨m, hm⟩⟩ := hw
    exact ⟨⟨l ++ m, by simp [hl, hm]⟩⟩

instance instNonemptyProjTensorLift (z : E ⊗[𝕜] F) : Nonempty (projTensorLift z) :=
  nonempty_projTensorLift z

/-- The cost of a representation. -/
def projTensorSum (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (l : List (E × F)) : ℝ :=
  (l.map fun xy => p xy.1 * q xy.2).sum

theorem projTensorSum_nonneg (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (l : List (E × F)) :
    0 ≤ projTensorSum p q l := by
  refine List.sum_nonneg fun a ha => ?_
  simp only [List.mem_map, Prod.exists] at ha
  obtain ⟨x, y, _, hxy⟩ := ha
  rw [← hxy]
  exact mul_nonneg (apply_nonneg p x) (apply_nonneg q y)

theorem projTensorSum_append (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (l m : List (E × F)) :
    projTensorSum p q (l ++ m) = projTensorSum p q l + projTensorSum p q m := by
  simp [projTensorSum]

/-! ## The seminorm -/

/-- The value of the projective tensor seminorm. -/
def projTensorSeminormFun (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) : ℝ :=
  ⨅ l : projTensorLift z, projTensorSum p q l.1

theorem bddBelow_projTensorSum (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    BddBelow (Set.range fun l : projTensorLift z => projTensorSum p q l.1) := by
  refine ⟨0, ?_⟩
  rintro r ⟨l, rfl⟩
  exact projTensorSum_nonneg p q l.1

theorem projTensorSeminormFun_nonneg (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    0 ≤ projTensorSeminormFun p q z :=
  le_ciInf fun l => projTensorSum_nonneg p q l.1

theorem projTensorSeminormFun_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) {z : E ⊗[𝕜] F}
    (l : projTensorLift z) : projTensorSeminormFun p q z ≤ projTensorSum p q l.1 :=
  ciInf_le (bddBelow_projTensorSum p q z) l

theorem projTensorSeminormFun_zero (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) :
    projTensorSeminormFun p q (0 : E ⊗[𝕜] F) = 0 := by
  refine le_antisymm ?_ (projTensorSeminormFun_nonneg p q 0)
  have h := projTensorSeminormFun_le p q (z := (0 : E ⊗[𝕜] F)) ⟨[], by simp⟩
  simpa [projTensorSum] using h

theorem projTensorSeminormFun_add_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z w : E ⊗[𝕜] F) :
    projTensorSeminormFun p q (z + w)
      ≤ projTensorSeminormFun p q z + projTensorSeminormFun p q w := by
  refine le_ciInf_add_ciInf fun l m => ?_
  have hcat : (((l.1 ++ m.1).map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum) = z + w := by
    rw [List.map_append, List.sum_append, l.2, m.2]
  refine le_trans (projTensorSeminormFun_le p q (z := z + w) ⟨l.1 ++ m.1, hcat⟩) (le_of_eq ?_)
  exact projTensorSum_append p q l.1 m.1

theorem projTensorSeminormFun_smul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (a : 𝕜)
    (z : E ⊗[𝕜] F) :
    projTensorSeminormFun p q (a • z) ≤ ‖a‖ * projTensorSeminormFun p q z := by
  have hgoal : ‖a‖ * projTensorSeminormFun p q z
      = ⨅ l : projTensorLift z, ‖a‖ * projTensorSum p q l.1 := by
    rw [projTensorSeminormFun, Real.mul_iInf_of_nonneg (norm_nonneg a)]
  rw [hgoal]
  refine le_ciInf fun l => ?_
  have hmap : ((l.1.map fun xy : E × F => ((a • xy.1, xy.2) : E × F)).map
      fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum = a • z := by
    rw [List.map_map]
    have hfun : ((fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2) ∘ fun xy : E × F => ((a • xy.1, xy.2) : E × F))
        = fun xy : E × F => a • (xy.1 ⊗ₜ[𝕜] xy.2) := by
      funext xy
      simp [TensorProduct.smul_tmul']
    have hstep : (l.1.map fun xy : E × F => a • (xy.1 ⊗ₜ[𝕜] xy.2)).sum
        = a • (l.1.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum := by
      rw [List.smul_sum, List.map_map]
      rfl
    rw [hfun, hstep, l.2]
  refine le_trans (projTensorSeminormFun_le p q (z := a • z)
    ⟨l.1.map fun xy : E × F => ((a • xy.1, xy.2) : E × F), hmap⟩) (le_of_eq ?_)
  rw [projTensorSum, projTensorSum, List.map_map]
  have hfun : ((fun xy : E × F => p xy.1 * q xy.2) ∘ fun xy : E × F => ((a • xy.1, xy.2) : E × F))
      = fun xy : E × F => ‖a‖ * (p xy.1 * q xy.2) := by
    funext xy
    rw [Function.comp_apply, map_smul_eq_mul p a xy.1]
    ring
  rw [hfun, List.sum_map_mul_left]

theorem projTensorSeminormFun_smul (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (a : 𝕜)
    (z : E ⊗[𝕜] F) :
    projTensorSeminormFun p q (a • z) = ‖a‖ * projTensorSeminormFun p q z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [projTensorSeminormFun_zero p q]
  · refine le_antisymm (projTensorSeminormFun_smul_le p q a z) ?_
    have h := projTensorSeminormFun_smul_le p q a⁻¹ (a • z)
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, norm_inv] at h
    have h2 : ‖a‖ * projTensorSeminormFun p q z
        ≤ ‖a‖ * (‖a‖⁻¹ * projTensorSeminormFun p q (a • z)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg a)
    rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul] at h2
    exact h2

/-- **The projective tensor seminorm.** -/
def projTensorSeminorm (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) : Seminorm 𝕜 (E ⊗[𝕜] F) where
  toFun := projTensorSeminormFun p q
  map_zero' := projTensorSeminormFun_zero p q
  add_le' := projTensorSeminormFun_add_le p q
  neg' z := by
    have h := projTensorSeminormFun_smul p q (-1 : 𝕜) z
    rw [neg_one_smul, norm_neg, norm_one, one_mul] at h
    exact h
  smul' := projTensorSeminormFun_smul p q

@[simp] theorem projTensorSeminorm_apply (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) :
    projTensorSeminorm p q z = projTensorSeminormFun p q z := rfl

/-- The projective seminorm is bounded by the product on pure tensors. -/
theorem projTensorSeminorm_tmul_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (x : E) (y : F) :
    projTensorSeminorm p q (x ⊗ₜ[𝕜] y) ≤ p x * q y := by
  have h := projTensorSeminormFun_le p q (z := x ⊗ₜ[𝕜] y) ⟨[(x, y)], by simp⟩
  simpa [projTensorSum] using h

/-! ## List-level interface -/

/-- The projective seminorm of a sum of pure tensors is bounded by the cost of that
representation. -/
theorem projTensorSeminorm_le_projTensorSum (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (l : List (E × F)) :
    projTensorSeminorm p q ((l.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) ≤ projTensorSum p q l :=
  projTensorSeminormFun_le p q ⟨l, rfl⟩

/-- A representation whose cost is arbitrarily close to the projective seminorm. -/
theorem exists_projTensorSum_lt (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (z : E ⊗[𝕜] F) {a : ℝ}
    (h : projTensorSeminorm p q z < a) :
    ∃ l : List (E × F), ((l.map fun xy => xy.1 ⊗ₜ[𝕜] xy.2).sum) = z ∧
      projTensorSum p q l < a := by
  obtain ⟨l, hl⟩ :=
    exists_lt_of_ciInf_lt (f := fun l : projTensorLift z => projTensorSum p q l.1) h
  exact ⟨l.1, l.2, hl⟩

/-! ## The universal property -/

/-- **A bilinear map bounded by `C · p · q` induces a linear map bounded by `C` times the
projective seminorm.** -/
theorem projTensorSeminorm_lift_le (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (r : Seminorm 𝕜 G)
    (B : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ (x : E) (y : F), r (B x y) ≤ C * (p x * q y)) (z : E ⊗[𝕜] F) :
    r (TensorProduct.lift B z) ≤ C * projTensorSeminorm p q z := by
  have hkey : ∀ (l : List (E × F)) (w : E ⊗[𝕜] F),
      ((l.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum) = w →
      r (TensorProduct.lift B w) ≤ C * projTensorSum p q l := by
    intro l
    induction l with
    | nil =>
      intro w hw
      have hz : w = 0 := by simpa using hw.symm
      subst hz
      simp [projTensorSum]
    | cons a l ih =>
      intro w hw
      have hsplit : w = a.1 ⊗ₜ[𝕜] a.2 + (l.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum := by
        rw [← hw]
        simp
      have hrest := ih ((l.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum) rfl
      have hstep : r (TensorProduct.lift B w)
          ≤ r (TensorProduct.lift B (a.1 ⊗ₜ[𝕜] a.2))
            + r (TensorProduct.lift B ((l.map fun xy : E × F => xy.1 ⊗ₜ[𝕜] xy.2).sum)) := by
        rw [hsplit, map_add]
        exact map_add_le_add r _ _
      have hhead : r (TensorProduct.lift B (a.1 ⊗ₜ[𝕜] a.2)) ≤ C * (p a.1 * q a.2) := by
        rw [TensorProduct.lift.tmul]
        exact hB a.1 a.2
      have hsum : projTensorSum p q (a :: l) = p a.1 * q a.2 + projTensorSum p q l := by
        simp [projTensorSum]
      rw [hsum, mul_add]
      linarith
  have hbdd : BddBelow (Set.range fun l : projTensorLift z => C * projTensorSum p q l.1) := by
    refine ⟨0, ?_⟩
    rintro s ⟨l, rfl⟩
    exact mul_nonneg hC (projTensorSum_nonneg p q l.1)
  have hle : r (TensorProduct.lift B z) ≤ ⨅ l : projTensorLift z, C * projTensorSum p q l.1 :=
    le_ciInf fun l => hkey l.1 z l.2
  refine le_trans hle (le_of_eq ?_)
  rw [projTensorSeminorm_apply, projTensorSeminormFun, Real.mul_iInf_of_nonneg hC]

/-! ## Functoriality -/

/-- **A tensor product of bounded maps is bounded** for the projective seminorms. -/
theorem projTensorSeminorm_map_le {E' F' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    [AddCommGroup F'] [Module 𝕜 F'] (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (p' : Seminorm 𝕜 E') (q' : Seminorm 𝕜 F') (f : E →ₗ[𝕜] E') (g : F →ₗ[𝕜] F')
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ x, p' (f x) ≤ C * p x) (hg : ∀ y, q' (g y) ≤ D * q y) (z : E ⊗[𝕜] F) :
    projTensorSeminorm p' q' (TensorProduct.map f g z)
      ≤ C * D * projTensorSeminorm p q z := by
  set B : E →ₗ[𝕜] F →ₗ[𝕜] E' ⊗[𝕜] F' :=
    ((TensorProduct.mk 𝕜 E' F').comp f).compl₂ g with hB
  have hBval : ∀ (x : E) (y : F), B x y = f x ⊗ₜ[𝕜] g y := fun x y => rfl
  have hmap : TensorProduct.map f g z = TensorProduct.lift B z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, hBval]
    | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
  have hbound : ∀ (x : E) (y : F),
      projTensorSeminorm p' q' (B x y) ≤ C * D * (p x * q y) := by
    intro x y
    have hxy : projTensorSeminorm p' q' (B x y) ≤ p' (f x) * q' (g y) := by
      rw [hBval]
      exact projTensorSeminorm_tmul_le p' q' (f x) (g y)
    have hnn : (0 : ℝ) ≤ q' (g y) := apply_nonneg _ _
    have hstep : p' (f x) * q' (g y) ≤ (C * p x) * (D * q y) := by
      refine le_trans (mul_le_mul_of_nonneg_right (hf x) hnn) ?_
      refine mul_le_mul_of_nonneg_left (hg y) ?_
      exact mul_nonneg hC (apply_nonneg p x)
    calc projTensorSeminorm p' q' (B x y) ≤ p' (f x) * q' (g y) := hxy
      _ ≤ (C * p x) * (D * q y) := hstep
      _ = C * D * (p x * q y) := by ring
  rw [hmap]
  exact projTensorSeminorm_lift_le p q (projTensorSeminorm p' q') B (by positivity) hbound z

theorem projTensorSum_mono {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F}
    (hp : ∀ x, p₁ x ≤ p₂ x) (hq : ∀ y, q₁ y ≤ q₂ y) (l : List (E × F)) :
    projTensorSum p₁ q₁ l ≤ projTensorSum p₂ q₂ l := by
  induction l with
  | nil => simp [projTensorSum]
  | cons a l ih =>
    have h1 : p₁ a.1 * q₁ a.2 ≤ p₂ a.1 * q₂ a.2 := by
      refine le_trans (mul_le_mul_of_nonneg_right (hp a.1) (apply_nonneg q₁ a.2)) ?_
      exact mul_le_mul_of_nonneg_left (hq a.2) (apply_nonneg p₂ a.1)
    have hcons : ∀ (P : Seminorm 𝕜 E) (Q : Seminorm 𝕜 F),
        projTensorSum P Q (a :: l) = P a.1 * Q a.2 + projTensorSum P Q l := by
      intro P Q
      simp [projTensorSum]
    rw [hcons, hcons]
    linarith

/-- The projective seminorm is monotone in both factors. -/
theorem projTensorSeminorm_mono {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F}
    (hp : ∀ x, p₁ x ≤ p₂ x) (hq : ∀ y, q₁ y ≤ q₂ y) (z : E ⊗[𝕜] F) :
    projTensorSeminorm p₁ q₁ z ≤ projTensorSeminorm p₂ q₂ z :=
  le_ciInf fun l =>
    (projTensorSeminormFun_le p₁ q₁ l).trans (projTensorSum_mono hp hq l.1)

/-! ## Split strictness -/

/-- **A split bounded injection stays strict after tensoring**: if `S ∘ Z = id` with `S` bounded,
then the projective seminorm of `z` is controlled by the projective seminorm of `(1 ⊗ Z) z`. -/
theorem projTensorSeminorm_strict_of_leftInverse {A B : Type*} [AddCommGroup A] [Module 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B] (r : Seminorm 𝕜 E) (pA : Seminorm 𝕜 A) (qB : Seminorm 𝕜 B)
    (Z : A →ₗ[𝕜] B) (S : B →ₗ[𝕜] A) (hS : ∀ a, S (Z a) = a) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ b, pA (S b) ≤ C * qB b) (z : E ⊗[𝕜] A) :
    projTensorSeminorm r pA z
      ≤ C * projTensorSeminorm r qB (TensorProduct.map LinearMap.id Z z) := by
  have hcomp : TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S
      (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) Z z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, hS a]
    | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
  have hmap := projTensorSeminorm_map_le r qB r pA (LinearMap.id : E →ₗ[𝕜] E) S
    (zero_le_one) hC (fun x => by rw [LinearMap.id_apply, one_mul])
    hbound (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) Z z)
  rw [hcomp, one_mul] at hmap
  exact hmap

end GaloisForLFunctions

end
