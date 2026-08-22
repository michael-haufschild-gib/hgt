import GaloisForLFunctions.HTGeometry.OperatorNormLoewner
import GaloisForLFunctions.HTGeometry.LyapunovInverseBounds
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldDerivative

/-!
# The Wasserstein vector field is a Newton contraction near the identity

The Newton map of the Wasserstein vector field is `N(X) = X - 2 Φ(X)`, whose derivative vanishes
at `(𝕀, I)`.  On self-adjoint directions,

`(id - 2 DΦ(X))(P) = (P - X⁻¹ P X⁻¹) - ∑ᵢ wᵢ Aᵢ^{1/2} (2 yᵢ - qᵢ) Aᵢ^{1/2}`,

where `qᵢ = Aᵢ^{-1/2} X⁻¹ P X⁻¹ Aᵢ^{-1/2}` and `yᵢ` solves the Lyapunov equation
`vᵢ yᵢ + yᵢ vᵢ = qᵢ` for `vᵢ = (Aᵢ^{-1/2} X⁻¹ Aᵢ^{-1/2})^{1/2}`.  The identity uses only
`∑ wᵢ = 1` and `Aᵢ^{1/2} qᵢ Aᵢ^{1/2} = X⁻¹ P X⁻¹`, and the two resulting terms are estimated by
the perturbation bounds for the square root and the Lyapunov inverse.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugation is bounded by the square of the norm of the conjugator. -/
lemma norm_conjMap_le (b x : A) : ‖conjMap b x‖ ≤ ‖b‖ * ‖b‖ * ‖x‖ := by
  rw [conjMap_apply']
  calc ‖b * x * b‖ ≤ ‖b * x‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ (‖b‖ * ‖x‖) * ‖b‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖b‖ * ‖b‖ * ‖x‖ := by ring

/-- Peeling the outer conjugation off the inner one. -/
lemma conjMap_rpow_half_conjMap_rpow_neg_half {a : A} (ha : IsStrictlyPositive a) (x : A) :
    conjMap (a ^ (1/2 : ℝ)) (conjMap (a ^ (-(1/2) : ℝ)) x) = x := by
  rw [conjMap_apply', conjMap_apply']
  exact sandwich_peel ha x

/-- **One-term Newton difference bound.**  The `i`-th term of `X⁻¹ P X⁻¹ - 2 DΦ(X)(P)` is
controlled by the distance of `vᵢ` from the identity. -/
theorem norm_deriv_term_sub_le {a X P : A} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (hP : IsSelfAdjoint P)
    {μ : ℝ} (hμ : 0 < μ)
    (hlb : μ • (1 : A) ≤ CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))
    {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    μ * ‖X⁻¹ʳ * P * X⁻¹ʳ
        - (2 : ℝ) • conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : A →L[ℝ] A)
            (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))‖
      ≤ ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖
        * (‖(1 : A) - CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ)‖
          * ‖conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)‖) := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : A) := isSelfAdjoint_rpow a _
  have hqsa : IsSelfAdjoint (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)) :=
    isSelfAdjoint_conjMap hNsa (hP.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hvsa : IsSelfAdjoint (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  have hlyap := lyapunov_twisted_unit_inv hu hqsa
  have hres := norm_two_smul_sub_lyapunov hvsa hμ hlb hlyap
  have hpeel : conjMap (a ^ (1/2 : ℝ)) (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))
      = X⁻¹ʳ * P * X⁻¹ʳ := conjMap_rpow_half_conjMap_rpow_neg_half ha _
  have hdiff : X⁻¹ʳ * P * X⁻¹ʳ
      - (2 : ℝ) • conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : A →L[ℝ] A)
          (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
      = -(conjMap (a ^ (1/2 : ℝ))
          ((2 : ℝ) • ((↑u⁻¹ : A →L[ℝ] A) (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
            - conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))) := by
    rw [map_sub, map_smul, hpeel]
    abel
  rw [hdiff, norm_neg]
  have hb := norm_conjMap_le (a ^ (1/2 : ℝ) : A)
    ((2 : ℝ) • ((↑u⁻¹ : A →L[ℝ] A) (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
      - conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))
  have hnn : (0 : ℝ) ≤ ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖ := by positivity
  nlinarith [norm_nonneg ((2 : ℝ) • ((↑u⁻¹ : A →L[ℝ] A)
      (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
    - conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))]

/-! ### Explicit bounds near the identity -/

/-- The square root respects an upper Loewner bound in norm. -/
lemma norm_cfcSqrt_le_of_le_smul_one {a : A} (_ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β)
    (h : a ≤ β • (1 : A)) : ‖CFC.sqrt a‖ ≤ Real.sqrt β := by
  have hm : CFC.sqrt a ≤ (Real.sqrt β) • (1 : A) := by
    have hmono := CFC.sqrt_le_sqrt _ _ h
    rwa [cfcSqrt_smul hβ (zero_le_one (α := A)), CFC.sqrt_one] at hmono
  exact norm_le_of_le_smul_one (CFC.sqrt_nonneg a) (Real.sqrt_nonneg β) hm

/-- The squared norm of `a^{1/2}` is bounded by the upper Loewner bound of `a`. -/
lemma norm_rpow_half_sq_le {a : A} (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β) (h : a ≤ β • (1 : A)) :
    ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖ ≤ β := by
  have hb : ‖(a ^ (1/2 : ℝ) : A)‖ ≤ Real.sqrt β := by
    rw [← CFC.sqrt_eq_rpow]
    exact norm_cfcSqrt_le_of_le_smul_one ha hβ h
  calc ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖ ≤ Real.sqrt β * Real.sqrt β :=
        mul_le_mul hb hb (norm_nonneg _) (Real.sqrt_nonneg β)
    _ = β := Real.mul_self_sqrt hβ

/-- The squared norm of `a^{-1/2}` is bounded by the reciprocal of the lower Loewner bound. -/
lemma norm_rpow_neg_half_sq_le {a : A} (ha : IsStrictlyPositive a) {m : ℝ} (hm : 0 < m)
    (h : m • (1 : A) ≤ a) :
    ‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ ≤ m⁻¹ := by
  have hinv : (a⁻¹ʳ : A) ≤ m⁻¹ • (1 : A) := ringInverse_le_of_smul_one_le hm h
  have heq : (a ^ (-(1/2) : ℝ) : A) = (a⁻¹ʳ : A) ^ (1/2 : ℝ) := (rpow_half_ringInverse ha).symm
  rw [heq]
  exact norm_rpow_half_sq_le ha.ringInverse.nonneg (inv_pos.mpr hm).le hinv

/-- **Lower Loewner bound for the square root of the conjugated inverse.** -/
lemma smul_one_le_cfcSqrt_conjMap {a X : A} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) {β : ℝ} (hβ : 0 < β)
    (haβ : a ≤ β • (1 : A)) (hXβ : X ≤ β • (1 : A)) :
    β⁻¹ • (1 : A) ≤ CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ) := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : A) := isSelfAdjoint_rpow a _
  have hXinv : β⁻¹ • (1 : A) ≤ X⁻¹ʳ := smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ
  have hainv : β⁻¹ • (1 : A) ≤ a⁻¹ʳ := smul_one_le_ringInverse_of_le_smul_one ha hβ haβ
  have hcl : (β⁻¹ * β⁻¹) • (1 : A) ≤ conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ := by
    have h1 : (a ^ (-(1/2) : ℝ) : A) * (β⁻¹ • (1 : A)) * (a ^ (-(1/2) : ℝ))
        ≤ (a ^ (-(1/2) : ℝ) : A) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ)) :=
      hNsa.conjugate_le_conjugate hXinv
    have h2 : (a ^ (-(1/2) : ℝ) : A) * (β⁻¹ • (1 : A)) * (a ^ (-(1/2) : ℝ))
        = β⁻¹ • (a⁻¹ʳ : A) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one,
        show (a ^ (-(1/2) : ℝ) : A) * (a ^ (-(1/2) : ℝ)) = (a⁻¹ʳ : A) by
          rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]; norm_num]
    have h3 : (β⁻¹ * β⁻¹) • (1 : A) ≤ β⁻¹ • (a⁻¹ʳ : A) := by
      rw [mul_smul]
      exact smul_le_smul_of_nonneg_left hainv (inv_pos.mpr hβ).le
    rw [conjMap_apply']
    exact h3.trans (h2 ▸ h1)
  have hm := CFC.sqrt_le_sqrt _ _ hcl
  rwa [cfcSqrt_smul (by positivity) (zero_le_one (α := A)), CFC.sqrt_one,
    show Real.sqrt (β⁻¹ * β⁻¹) = β⁻¹ from Real.sqrt_mul_self (inv_pos.mpr hβ).le] at hm

/-- **One-term Newton difference bound with explicit constants.** -/
theorem norm_deriv_term_sub_le_delta {a X P : A} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (hP : IsSelfAdjoint P)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (haδ : ‖a - 1‖ ≤ δ) (hXδ : ‖X - 1‖ ≤ δ)
    {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    ‖X⁻¹ʳ * P * X⁻¹ʳ
        - (2 : ℝ) • conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : A →L[ℝ] A)
            (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))‖
      ≤ (1 + δ) * ((1 + δ)
        * (((1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ)
          * (((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖)))))) := by
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hβpos : (0 : ℝ) < 1 + δ := by linarith
  have hinvnn : (0 : ℝ) ≤ (1 - δ)⁻¹ := (inv_pos.mpr h1δ).le
  have haβ : a ≤ (1 + δ) • (1 : A) := le_smul_one_of_norm_sub_one_le ha.isSelfAdjoint haδ
  have haα : (1 - δ) • (1 : A) ≤ a := smul_one_le_of_norm_sub_one_le ha.isSelfAdjoint haδ
  have hXβ : X ≤ (1 + δ) • (1 : A) := le_smul_one_of_norm_sub_one_le hX.isSelfAdjoint hXδ
  have hXα : (1 - δ) • (1 : A) ≤ X := smul_one_le_of_norm_sub_one_le hX.isSelfAdjoint hXδ
  have hμ := smul_one_le_cfcSqrt_conjMap ha hX hβpos haβ hXβ
  have hmain := norm_deriv_term_sub_le ha hX hP (inv_pos.mpr hβpos) hμ hu
  have hA2 : ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖ ≤ 1 + δ :=
    norm_rpow_half_sq_le ha.nonneg hβpos.le haβ
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ ≤ (1 - δ)⁻¹ :=
    norm_rpow_neg_half_sq_le ha h1δ haα
  have hXinvn : ‖(X⁻¹ʳ : A)‖ ≤ (1 - δ)⁻¹ := norm_ringInverse_le_of_smul_one_le hX h1δ hXα
  have hainvn : ‖(a⁻¹ʳ : A)‖ ≤ (1 - δ)⁻¹ := norm_ringInverse_le_of_smul_one_le ha h1δ haα
  have hXinv1 : ‖(X⁻¹ʳ : A) - 1‖ ≤ (1 - δ)⁻¹ * δ :=
    (norm_ringInverse_sub_one_le hX).trans (mul_le_mul hXinvn hXδ (norm_nonneg _) hinvnn)
  have hainv1 : ‖(a⁻¹ʳ : A) - 1‖ ≤ (1 - δ)⁻¹ * δ :=
    (norm_ringInverse_sub_one_le ha).trans (mul_le_mul hainvn haδ (norm_nonneg _) hinvnn)
  have hsq : (a ^ (-(1/2) : ℝ) : A) * (a ^ (-(1/2) : ℝ)) = (a⁻¹ʳ : A) := by
    rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]; norm_num
  have hid : (a ^ (-(1/2) : ℝ) : A) * ((X⁻¹ʳ : A) - 1) * (a ^ (-(1/2) : ℝ)) + ((a⁻¹ʳ : A) - 1)
      = conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ - 1 := by
    rw [conjMap_apply']
    have h : (a ^ (-(1/2) : ℝ) : A) * ((X⁻¹ʳ : A) - 1) * (a ^ (-(1/2) : ℝ))
        = (a ^ (-(1/2) : ℝ) : A) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ))
          - (a ^ (-(1/2) : ℝ) : A) * (a ^ (-(1/2) : ℝ)) := by noncomm_ring
    rw [h, hsq]
    abel
  have hc1 : ‖conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ - 1‖
      ≤ (1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ := by
    rw [← hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ hainv1)
    rw [← conjMap_apply']
    exact (norm_conjMap_le _ _).trans (mul_le_mul hN2 hXinv1 (norm_nonneg _) hinvnn)
  have hv1 : ‖(1 : A) - CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ)‖
      ≤ (1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ := by
    rw [← norm_neg, neg_sub]
    exact (norm_cfcSqrt_sub_one_le
      (isStrictlyPositive_conjMap_rpow ha hX.ringInverse).nonneg).trans hc1
  have hXPX : ‖(X⁻¹ʳ : A) * P * X⁻¹ʳ‖ ≤ (1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖) := by
    calc ‖(X⁻¹ʳ : A) * P * X⁻¹ʳ‖ ≤ ‖(X⁻¹ʳ : A) * P‖ * ‖(X⁻¹ʳ : A)‖ := norm_mul_le _ _
      _ ≤ (‖(X⁻¹ʳ : A)‖ * ‖P‖) * ‖(X⁻¹ʳ : A)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((1 - δ)⁻¹ * ‖P‖) * (1 - δ)⁻¹ := by gcongr
      _ = (1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖) := by ring
  have hq : ‖conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : A) * P * X⁻¹ʳ)‖
      ≤ (1 - δ)⁻¹ * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖)) := by
    refine (norm_conjMap_le _ _).trans ?_
    exact mul_le_mul hN2 hXPX (norm_nonneg _) hinvnn
  have hprod : ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖
      * (‖(1 : A) - CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ)‖
        * ‖conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : A) * P * X⁻¹ʳ)‖)
      ≤ (1 + δ) * (((1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ)
        * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖)))) := by
    gcongr
  have hfinal : (1 + δ)⁻¹ * ‖(X⁻¹ʳ : A) * P * X⁻¹ʳ
      - (2 : ℝ) • conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : A →L[ℝ] A)
          (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : A) * P * X⁻¹ʳ)))‖
      ≤ (1 + δ) * (((1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ)
        * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * ‖P‖)))) := hmain.trans hprod
  have hmul := mul_le_mul_of_nonneg_left hfinal hβpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hβpos), one_mul] at hmul

/-! ### The aggregate Newton bound -/

/-- The one-term Newton constant on the ball of radius `δ` around the identity. -/
noncomputable def newtonTermConst (δ : ℝ) : ℝ :=
  (1 + δ) * ((1 + δ) * (((1 - δ)⁻¹ * ((1 - δ)⁻¹ * δ) + (1 - δ)⁻¹ * δ)
    * ((1 - δ)⁻¹ * ((1 - δ)⁻¹ * (1 - δ)⁻¹))))

/-- The Newton contraction constant on the ball of radius `δ` around the identity. -/
noncomputable def newtonConst (δ : ℝ) : ℝ :=
  (1 - δ)⁻¹ * δ * (1 + (1 - δ)⁻¹) + newtonTermConst δ

lemma newtonTermConst_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : 0 ≤ newtonTermConst δ := by
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  unfold newtonTermConst
  positivity

/-- The one-term bound in factored form. -/
theorem norm_deriv_term_sub_le_const {a X P : A} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (hP : IsSelfAdjoint P)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (haδ : ‖a - 1‖ ≤ δ) (hXδ : ‖X - 1‖ ≤ δ)
    {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    ‖X⁻¹ʳ * P * X⁻¹ʳ
        - (2 : ℝ) • conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : A →L[ℝ] A)
            (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))‖
      ≤ newtonTermConst δ * ‖P‖ := by
  have h := norm_deriv_term_sub_le_delta ha hX hP hδ0 hδ1 haδ hXδ hu
  refine h.trans (le_of_eq ?_)
  unfold newtonTermConst
  ring

/-- The commutator term `P - X⁻¹ P X⁻¹`. -/
theorem norm_sub_conj_ringInverse_le {X P : A} (hX : IsStrictlyPositive X)
    {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hXδ : ‖X - 1‖ ≤ δ) :
    ‖P - X⁻¹ʳ * P * X⁻¹ʳ‖ ≤ ((1 - δ)⁻¹ * δ * (1 + (1 - δ)⁻¹)) * ‖P‖ := by
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hinvnn : (0 : ℝ) ≤ (1 - δ)⁻¹ := (inv_pos.mpr h1δ).le
  have hXα : (1 - δ) • (1 : A) ≤ X := smul_one_le_of_norm_sub_one_le hX.isSelfAdjoint hXδ
  have hXinvn : ‖(X⁻¹ʳ : A)‖ ≤ (1 - δ)⁻¹ := norm_ringInverse_le_of_smul_one_le hX h1δ hXα
  have hXinv1 : ‖(1 : A) - X⁻¹ʳ‖ ≤ (1 - δ)⁻¹ * δ := by
    rw [← norm_neg, neg_sub]
    exact (norm_ringInverse_sub_one_le hX).trans
      (mul_le_mul hXinvn hXδ (norm_nonneg _) hinvnn)
  have hid : P - (X⁻¹ʳ : A) * P * X⁻¹ʳ
      = ((1 : A) - X⁻¹ʳ) * P + X⁻¹ʳ * P * ((1 : A) - X⁻¹ʳ) := by
    noncomm_ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have hb1 : ‖((1 : A) - X⁻¹ʳ) * P‖ ≤ ((1 - δ)⁻¹ * δ) * ‖P‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hXinv1 (norm_nonneg _))
  have hb2 : ‖(X⁻¹ʳ : A) * P * ((1 : A) - X⁻¹ʳ)‖ ≤ ((1 - δ)⁻¹ * ‖P‖) * ((1 - δ)⁻¹ * δ) := by
    calc ‖(X⁻¹ʳ : A) * P * ((1 : A) - X⁻¹ʳ)‖
        ≤ ‖(X⁻¹ʳ : A) * P‖ * ‖(1 : A) - X⁻¹ʳ‖ := norm_mul_le _ _
      _ ≤ (‖(X⁻¹ʳ : A)‖ * ‖P‖) * ‖(1 : A) - X⁻¹ʳ‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((1 - δ)⁻¹ * ‖P‖) * ((1 - δ)⁻¹ * δ) := by gcongr
  nlinarith [norm_nonneg P]

variable {ι : Type*}

/-- **The aggregate Newton bound.**  On self-adjoint directions the Newton derivative
`id - 2 DΦ(X)` is bounded by `newtonConst δ`. -/
theorem norm_newton_deriv_le {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X P : A}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hP : IsSelfAdjoint P) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hAδ : ∀ i ∈ s, ‖Av i - 1‖ ≤ δ) (hXδ : ‖X - 1‖ ≤ δ)
    {u : ι → (A →L[ℝ] A)ˣ}
    (hu : ∀ i ∈ s, (↑(u i) : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    ‖P - (2 : ℝ) • (∑ i ∈ s, w i • conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(u i)⁻¹ : A →L[ℝ] A)
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))))‖
      ≤ newtonConst δ * ‖P‖ := by
  set D : ι → A := fun i => conjMap ((Av i) ^ (1/2 : ℝ))
    ((↑(u i)⁻¹ : A →L[ℝ] A)
      (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))) with hD
  have hsplit : P - (2 : ℝ) • (∑ i ∈ s, w i • D i)
      = (P - X⁻¹ʳ * P * X⁻¹ʳ)
        + ∑ i ∈ s, w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i) := by
    have h1 : ∑ i ∈ s, w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i)
        = (∑ i ∈ s, w i) • ((X⁻¹ʳ : A) * P * X⁻¹ʳ) - (2 : ℝ) • (∑ i ∈ s, w i • D i) := by
      rw [Finset.sum_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_sub, smul_comm]
    rw [h1, hwsum, one_smul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hterm : ∀ i ∈ s, ‖w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i)‖
      ≤ w i * (newtonTermConst δ * ‖P‖) := by
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    exact mul_le_mul_of_nonneg_left
      (norm_deriv_term_sub_le_const (hA i hi) hX hP hδ0 hδ1 (hAδ i hi) hXδ (hu i hi))
      (hw i hi)
  have hsum : ‖∑ i ∈ s, w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i)‖
      ≤ newtonTermConst δ * ‖P‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ s, ‖w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i)‖
        ≤ ∑ i ∈ s, w i * (newtonTermConst δ * ‖P‖) := Finset.sum_le_sum hterm
      _ = newtonTermConst δ * ‖P‖ := by rw [← Finset.sum_mul, hwsum, one_mul]
  have hcomm := norm_sub_conj_ringInverse_le (P := P) hX hδ0 hδ1 hXδ
  calc ‖P - (X⁻¹ʳ : A) * P * X⁻¹ʳ‖
        + ‖∑ i ∈ s, w i • ((X⁻¹ʳ : A) * P * X⁻¹ʳ - (2 : ℝ) • D i)‖
      ≤ ((1 - δ)⁻¹ * δ * (1 + (1 - δ)⁻¹)) * ‖P‖ + newtonTermConst δ * ‖P‖ :=
        add_le_add hcomm hsum
    _ = newtonConst δ * ‖P‖ := by unfold newtonConst; ring

/-- At radius `1/32` the Newton derivative contracts by a factor `1/2`. -/
lemma newtonConst_thirtysecond : newtonConst (1/32 : ℝ) ≤ 1/2 := by
  unfold newtonConst newtonTermConst
  norm_num

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
