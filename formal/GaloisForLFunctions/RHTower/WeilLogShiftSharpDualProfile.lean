import GaloisForLFunctions.RHTower.WeilLogShiftC0VanishingEnvelope

/-!
# The sharp dual profile of a finite-dimensional C₀ family

Evaluation forms a norm-continuous, vanishing dual-valued map. Its norm is
the smallest nonnegative pointwise amplitude envelope, with the same global
norm as the original operator and precisely its common invisible locus.
-/

open Filter Topology Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]

/-- Evaluation of a finite-dimensional C₀ family, as a C₀ map into the dual. -/
def finiteDimensionalC0Dual (S : E →ₗ[ℝ] C₀(X, ℝ)) : C₀(X, E →L[ℝ] ℝ) where
  toFun x := LinearMap.toContinuousLinearMap {
    toFun := fun a => S a x
    map_add' := fun a b => congrArg (fun f : C₀(X, ℝ) => f x) (map_add S a b)
    map_smul' := fun c a => congrArg (fun f : C₀(X, ℝ) => f x) (map_smul S c a) }
  continuous_toFun := continuous_clm_apply.mpr fun a => map_continuous (S a)
  zero_at_infty' := by
    obtain ⟨g, hg, hbound⟩ := exists_finiteDimensional_c0_vanishing_envelope S
    refine squeeze_zero_norm (fun x => ?_) (zero_at_infty g)
    apply ContinuousLinearMap.opNorm_le_bound _ (hg x)
    intro a
    change ‖S a x‖ ≤ g x * ‖a‖
    simpa only [Real.norm_eq_abs, mul_comm] using hbound a x

@[simp] theorem finiteDimensionalC0Dual_apply (S : E →ₗ[ℝ] C₀(X, ℝ)) (x : X) (a : E) :
    finiteDimensionalC0Dual S x a = S a x := rfl

/-- The pointwise optimal nonnegative amplitude envelope for a fixed family. -/
def finiteDimensionalC0SharpProfile (S : E →ₗ[ℝ] C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun x := ‖finiteDimensionalC0Dual S x‖
  continuous_toFun := (map_continuous (finiteDimensionalC0Dual S)).norm
  zero_at_infty' := by
    simpa only [norm_zero] using (zero_at_infty (finiteDimensionalC0Dual S)).norm

/-- Sharpness holds even when the amplitude space is trivial. -/
theorem finiteDimensionalC0SharpProfile_le_iff
    (S : E →ₗ[ℝ] C₀(X, ℝ)) (x : X) {c : ℝ} (hc : 0 ≤ c) :
    finiteDimensionalC0SharpProfile S x ≤ c ↔ ∀ a : E, |S a x| ≤ ‖a‖ * c := by
  change ‖finiteDimensionalC0Dual S x‖ ≤ c ↔ _
  simpa only [finiteDimensionalC0Dual_apply, Real.norm_eq_abs, mul_comm] using
    (ContinuousLinearMap.opNorm_le_iff (f := finiteDimensionalC0Dual S x) hc)

/-- A zero of the sharp profile is exactly a shift invisible to every amplitude. -/
theorem finiteDimensionalC0SharpProfile_eq_zero_iff
    (S : E →ₗ[ℝ] C₀(X, ℝ)) (x : X) :
    finiteDimensionalC0SharpProfile S x = 0 ↔ ∀ a : E, S a x = 0 := by
  change ‖finiteDimensionalC0Dual S x‖ = 0 ↔ _
  rw [norm_eq_zero]
  constructor
  · intro h a
    have := congrArg (fun f : E →L[ℝ] ℝ => f a) h
    exact this
  · intro h
    apply ContinuousLinearMap.ext
    intro a
    exact h a

/-- The sharp pointwise profile retains the exact global operator norm. -/
theorem norm_finiteDimensionalC0SharpProfile (S : E →ₗ[ℝ] C₀(X, ℝ)) :
    ‖finiteDimensionalC0SharpProfile S‖ = ‖S.toContinuousLinearMap‖ := by
  let q := finiteDimensionalC0SharpProfile S
  have hq (x : X) : 0 ≤ q x := norm_nonneg (finiteDimensionalC0Dual S x)
  have hbound (a : E) (x : X) : |S a x| ≤ ‖a‖ * q x :=
    (finiteDimensionalC0SharpProfile_le_iff S x (hq x)).mp le_rfl a
  apply le_antisymm
  · change ‖q.toBCF‖ ≤ ‖S.toContinuousLinearMap‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg S.toContinuousLinearMap)).mpr
    intro x
    change ‖q x‖ ≤ ‖S.toContinuousLinearMap‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hq x)]
    apply (finiteDimensionalC0SharpProfile_le_iff S x (norm_nonneg S.toContinuousLinearMap)).mpr
    intro a
    calc
      |S a x| ≤ ‖S a‖ := by
        simpa only [Real.norm_eq_abs] using!
          BoundedContinuousFunction.norm_coe_le_norm (S a).toBCF x
      _ ≤ ‖a‖ * ‖S.toContinuousLinearMap‖ := by
        simpa only [LinearMap.coe_toContinuousLinearMap', mul_comm] using!
          S.toContinuousLinearMap.le_opNorm a
  · apply S.toContinuousLinearMap.opNorm_le_bound (norm_nonneg q)
    intro a
    change ‖(S a).toBCF‖ ≤ ‖q‖ * ‖a‖
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg q) (norm_nonneg a))).mpr
    intro x
    change ‖S a x‖ ≤ ‖q‖ * ‖a‖
    have hx : q x ≤ ‖q‖ :=
      (le_abs_self (q x)).trans (by
        simpa only [Real.norm_eq_abs] using! BoundedContinuousFunction.norm_coe_le_norm q.toBCF x)
    simpa only [Real.norm_eq_abs, mul_comm] using
      (hbound a x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg a))

/-- Sustaining a positive response at escaping points forces amplitude norm
beyond every fixed bound, uniformly over amplitudes chosen at those points. -/
theorem finiteDimensionalC0_response_cost_escapes
    (S : E →ₗ[ℝ] C₀(X, ℝ)) (ε : ℝ) (hε : 0 < ε) (R : ℝ) :
    ∀ᶠ x in cocompact X, ∀ a : E, ε ≤ |S a x| → R < ‖a‖ := by
  let q := finiteDimensionalC0SharpProfile S
  have hq (x : X) : 0 ≤ q x := norm_nonneg (finiteDimensionalC0Dual S x)
  have ht : Tendsto (fun x => (1 + max R 0) * q x) (cocompact X) (𝓝 0) := by
    simpa only [mul_zero] using (zero_at_infty q).const_mul (1 + max R 0)
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with x hx
  intro a ha
  by_contra hn
  have hn' : ‖a‖ ≤ 1 + max R 0 := by
    have := le_of_not_gt hn
    linarith only [this, le_max_left R (0 : ℝ)]
  have hb := (finiteDimensionalC0SharpProfile_le_iff S x (hq x)).mp le_rfl a
  have := hb.trans (mul_le_mul_of_nonneg_right hn' (hq x))
  exact (not_lt_of_ge (ha.trans this)) hx

end RHTower
