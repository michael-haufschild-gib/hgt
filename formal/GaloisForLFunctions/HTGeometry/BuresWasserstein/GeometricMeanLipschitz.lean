import GaloisForLFunctions.HTGeometry.SylvesterInverseBounds
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison
import GaloisForLFunctions.HTGeometry.BuresWasserstein.KantorovichConverse
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldContraction

/-!
# The geometric mean is Lipschitz in its second argument

If `x = a # b` and `y = a # c` then the Riccati equations `x a⁻¹ x = b` and `y a⁻¹ y = c`
telescope to

`x a⁻¹ (x - y) + (x - y) a⁻¹ y = b - c`,

a Sylvester equation whose coefficients become positive after conjugation by `a^{-1/2}`.  The
Sylvester norm bounds then give a Lipschitz estimate for `b ↦ a # b` in the operator norm and in
the Hilbert–Schmidt norm, with no differentiability and no functional calculus in the estimate.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The difference of two geometric means solves a Sylvester equation.** -/
theorem gm_sub_sylvester {a b c : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hc : IsStrictlyPositive c) :
    (a ^ (-(1/2) : ℝ) * gm a b * a ^ (-(1/2) : ℝ))
        * (a ^ (-(1/2) : ℝ) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
      + (a ^ (-(1/2) : ℝ) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
        * (a ^ (-(1/2) : ℝ) * gm a c * a ^ (-(1/2) : ℝ))
      = a ^ (-(1/2) : ℝ) * (b - c) * a ^ (-(1/2) : ℝ) := by
  have hinv : (a ^ (-(1/2) : ℝ) : A) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ := by
    rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]; norm_num
  have hkey : gm a b * a⁻¹ʳ * (gm a b - gm a c) + (gm a b - gm a c) * (a⁻¹ʳ * gm a c)
      = b - c := by
    have h1 := gm_riccati ha hb
    have h2 := gm_riccati ha hc
    have hexp : gm a b * a⁻¹ʳ * (gm a b - gm a c) + (gm a b - gm a c) * (a⁻¹ʳ * gm a c)
        = gm a b * a⁻¹ʳ * gm a b - gm a c * a⁻¹ʳ * gm a c := by noncomm_ring
    rw [hexp, h1, h2]
  calc (a ^ (-(1/2) : ℝ) * gm a b * a ^ (-(1/2) : ℝ))
          * (a ^ (-(1/2) : ℝ) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
        + (a ^ (-(1/2) : ℝ) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
          * (a ^ (-(1/2) : ℝ) * gm a c * a ^ (-(1/2) : ℝ))
      = a ^ (-(1/2) : ℝ) * (gm a b * ((a ^ (-(1/2) : ℝ) : A) * a ^ (-(1/2) : ℝ))
            * (gm a b - gm a c)
          + (gm a b - gm a c) * (((a ^ (-(1/2) : ℝ) : A) * a ^ (-(1/2) : ℝ)) * gm a c))
        * a ^ (-(1/2) : ℝ) := by noncomm_ring
    _ = a ^ (-(1/2) : ℝ) * (b - c) * a ^ (-(1/2) : ℝ) := by rw [hinv, hkey]

/-- Conjugation by `a^{-1/2}` of a Loewner-bounded element. -/
lemma smul_one_le_conj_rpow_neg_half {a x : A} (ha : IsStrictlyPositive a) {γ M : ℝ}
    (hγ : 0 < γ) (hM : 0 < M) (haM : a ≤ M • (1 : A)) (hx : γ • (1 : A) ≤ x) :
    (γ * M⁻¹) • (1 : A) ≤ a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ) := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : A) := isSelfAdjoint_rpow a _
  have hinv : (a ^ (-(1/2) : ℝ) : A) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ := by
    rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]; norm_num
  have h1 : (a ^ (-(1/2) : ℝ) : A) * (γ • (1 : A)) * (a ^ (-(1/2) : ℝ))
      ≤ a ^ (-(1/2) : ℝ) * x * a ^ (-(1/2) : ℝ) := hNsa.conjugate_le_conjugate hx
  have h2 : (a ^ (-(1/2) : ℝ) : A) * (γ • (1 : A)) * (a ^ (-(1/2) : ℝ)) = γ • (a⁻¹ʳ : A) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hinv]
  have h3 : (γ * M⁻¹) • (1 : A) ≤ γ • (a⁻¹ʳ : A) := by
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left (smul_one_le_ringInverse_of_le_smul_one ha hM haM) hγ.le
  exact h3.trans (h2 ▸ h1)

/-- **Operator-norm Lipschitz estimate for the geometric mean in its second argument.** -/
theorem norm_gm_sub_le {a b c : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hc : IsStrictlyPositive c) {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M)
    (haM : a ≤ M • (1 : A)) (hgb : γ • (1 : A) ≤ gm a b) (hgc : γ • (1 : A) ≤ gm a c) :
    (2 * (γ * M⁻¹)) * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖
      ≤ ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖ := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : A) := isSelfAdjoint_rpow a _
  have hxsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : A) * gm a b * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a b).isSelfAdjoint.conjugate_self hNsa
  have hysa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : A) * gm a c * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a c).isSelfAdjoint.conjugate_self hNsa
  have hxl := smul_one_le_conj_rpow_neg_half ha hγ hM haM hgb
  have hyl := smul_one_le_conj_rpow_neg_half ha hγ hM haM hgc
  have hpos : (0 : ℝ) < γ * M⁻¹ := by positivity
  have h := norm_le_of_sylvester hxsa hysa hpos hpos hxl hyl
    (gm_sub_sylvester ha hb hc)
  calc (2 * (γ * M⁻¹))
        * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖
      = (γ * M⁻¹ + γ * M⁻¹)
        * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖ := by ring
    _ ≤ ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖ := h

/-- **The geometric mean is Lipschitz in its second argument.**  On a Loewner interval
`α · 1 ≤ a ≤ M · 1` with `γ · 1 ≤ a # b, a # c`, the constant is `M²/(2γα)`. -/
theorem norm_gm_sub_le_of_Icc {a b c : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hc : IsStrictlyPositive c) {α γ M : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hM : 0 < M)
    (haα : α • (1 : A) ≤ a) (haM : a ≤ M • (1 : A))
    (hgb : γ • (1 : A) ≤ gm a b) (hgc : γ • (1 : A) ≤ gm a c) :
    (2 * (γ * M⁻¹)) * ‖gm a b - gm a c‖ ≤ (M * α⁻¹) * ‖b - c‖ := by
  have hP2 : ‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖ ≤ M :=
    norm_rpow_half_sq_le ha.nonneg hM.le haM
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  have hpeel : (a ^ (1/2 : ℝ) : A)
      * ((a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ)
      = gm a b - gm a c := sandwich_peel ha _
  have hz : ‖gm a b - gm a c‖
      ≤ (‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
        * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖ := by
    conv_lhs => rw [← hpeel]
    calc ‖(a ^ (1/2 : ℝ) : A)
          * ((a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)) * a ^ (1/2 : ℝ)‖
        ≤ ‖(a ^ (1/2 : ℝ) : A)
            * ((a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))‖
              * ‖(a ^ (1/2 : ℝ) : A)‖ := norm_mul_le _ _
      _ ≤ (‖(a ^ (1/2 : ℝ) : A)‖
            * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖)
              * ‖(a ^ (1/2 : ℝ) : A)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = (‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
            * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖ := by ring
  have hd : ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖
      ≤ (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖) * ‖b - c‖ := by
    calc ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖
        ≤ ‖(a ^ (-(1/2) : ℝ) : A) * (b - c)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ := norm_mul_le _ _
      _ ≤ (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖b - c‖) * ‖(a ^ (-(1/2) : ℝ) : A)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖) * ‖b - c‖ := by ring
  have hsyl := norm_gm_sub_le ha hb hc hγ hM haM hgb hgc
  have hpos : (0 : ℝ) < 2 * (γ * M⁻¹) := by positivity
  calc (2 * (γ * M⁻¹)) * ‖gm a b - gm a c‖
      ≤ (2 * (γ * M⁻¹)) * ((‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
          * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖) :=
        mul_le_mul_of_nonneg_left hz hpos.le
    _ = (‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
          * ((2 * (γ * M⁻¹))
            * ‖(a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)‖) := by ring
    _ ≤ (‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
          * ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖ :=
        mul_le_mul_of_nonneg_left hsyl (by positivity)
    _ ≤ (‖(a ^ (1/2 : ℝ) : A)‖ * ‖(a ^ (1/2 : ℝ) : A)‖)
          * ((‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖) * ‖b - c‖) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ M * (α⁻¹ * ‖b - c‖) := by
        refine mul_le_mul hP2 (mul_le_mul_of_nonneg_right hN2 (norm_nonneg _))
          (by positivity) hM.le
    _ = (M * α⁻¹) * ‖b - c‖ := by ring

/-- **The geometric mean is Lipschitz in its first argument**, by symmetry. -/
theorem norm_gm_sub_le_left {a b c : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hc : IsStrictlyPositive c) {α γ M : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hM : 0 < M)
    (hcα : α • (1 : A) ≤ c) (hcM : c ≤ M • (1 : A))
    (hga : γ • (1 : A) ≤ gm c a) (hgb : γ • (1 : A) ≤ gm c b) :
    (2 * (γ * M⁻¹)) * ‖gm a c - gm b c‖ ≤ (M * α⁻¹) * ‖a - b‖ := by
  rw [gm_comm ha hc, gm_comm hb hc]
  exact norm_gm_sub_le_of_Icc hc ha hb hα hγ hM hcα hcM hga hgb

/-! ### The Hilbert–Schmidt versions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- **The difference of two geometric means is Hilbert–Schmidt** whenever the difference of the
second arguments is.  This is what makes the Wasserstein vector field well defined on `Σ₂`. -/
theorem isHilbertSchmidt_gm_sub {a b c : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (hc : IsStrictlyPositive c) {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M)
    (haM : a ≤ M • (1 : E →L[ℂ] E))
    (hgb : γ • (1 : E →L[ℂ] E) ≤ gm a b) (hgc : γ • (1 : E →L[ℂ] E) ≤ gm a c)
    (hbc : IsHilbertSchmidt (b - c)) : IsHilbertSchmidt (gm a b - gm a c) := by
  have hNsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ)) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hxsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a b * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a b).isSelfAdjoint.conjugate_self hNsa
  have hysa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a c * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a c).isSelfAdjoint.conjugate_self hNsa
  have hpos : (0 : ℝ) < γ * M⁻¹ := by positivity
  have hdHS : IsHilbertSchmidt ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (b - c) * a ^ (-(1/2) : ℝ)) :=
    (hbc.comp_left _).comp_right _
  have hzHS : IsHilbertSchmidt
      ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)) :=
    isHilbertSchmidt_of_sylvester hxsa hysa hpos hpos
      (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgb)
      (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgc) hdHS (gm_sub_sylvester ha hb hc)
  have hpeel : (a ^ (1/2 : ℝ) : E →L[ℂ] E)
      * ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
        * a ^ (1/2 : ℝ) = gm a b - gm a c := sandwich_peel ha _
  rw [← hpeel]
  exact (hzHS.comp_left _).comp_right _

/-- **Hilbert–Schmidt Lipschitz estimate for the geometric mean in its second argument.** -/
theorem hsNorm_gm_sub_le_of_Icc {a b c : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (hc : IsStrictlyPositive c) {α γ M : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hM : 0 < M)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haM : a ≤ M • (1 : E →L[ℂ] E))
    (hgb : γ • (1 : E →L[ℂ] E) ≤ gm a b) (hgc : γ • (1 : E →L[ℂ] E) ≤ gm a c)
    (hbc : IsHilbertSchmidt (b - c)) :
    (2 * (γ * M⁻¹)) * hsNorm (gm a b - gm a c) ≤ (M * α⁻¹) * hsNorm (b - c) := by
  have hNsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ)) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hxsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a b * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a b).isSelfAdjoint.conjugate_self hNsa
  have hysa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a c * a ^ (-(1/2) : ℝ)) :=
    (gm_nonneg a c).isSelfAdjoint.conjugate_self hNsa
  have hpos : (0 : ℝ) < γ * M⁻¹ := by positivity
  have hdHS : IsHilbertSchmidt ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (b - c) * a ^ (-(1/2) : ℝ)) :=
    (hbc.comp_left _).comp_right _
  have hzHS : IsHilbertSchmidt
      ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)) :=
    isHilbertSchmidt_of_sylvester hxsa hysa hpos hpos
      (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgb)
      (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgc) hdHS (gm_sub_sylvester ha hb hc)
  have hsyl := hsNorm_le_of_sylvester hxsa hysa hzHS hpos hpos
    (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgb)
    (smul_one_le_conj_rpow_neg_half ha hγ hM haM hgc) (gm_sub_sylvester ha hb hc)
  have hP2 : ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ ≤ M :=
    norm_rpow_half_sq_le ha.nonneg hM.le haM
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  have hpeel : (a ^ (1/2 : ℝ) : E →L[ℂ] E)
      * (((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ))
        * a ^ (1/2 : ℝ)) = gm a b - gm a c := by
    rw [← mul_assoc]
    exact sandwich_peel ha _
  have hz : hsNorm (gm a b - gm a c)
      ≤ (‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖)
        * hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ)) := by
    conv_lhs => rw [← hpeel]
    exact hsNorm_sandwich_le hzHS
  have hd : hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (b - c) * a ^ (-(1/2) : ℝ))
      ≤ (‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖)
        * hsNorm (b - c) := by
    have h : hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * ((b - c) * a ^ (-(1/2) : ℝ)))
        ≤ ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖
          * hsNorm (b - c) := hsNorm_sandwich_le hbc
    rwa [← mul_assoc] at h
  calc (2 * (γ * M⁻¹)) * hsNorm (gm a b - gm a c)
      ≤ (2 * (γ * M⁻¹)) * ((‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖)
          * hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c)
            * a ^ (-(1/2) : ℝ))) := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = (‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖)
          * ((γ * M⁻¹ + γ * M⁻¹)
            * hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a b - gm a c)
              * a ^ (-(1/2) : ℝ))) := by ring
    _ ≤ (‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖)
          * hsNorm ((a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (b - c) * a ^ (-(1/2) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsyl (by positivity)
    _ ≤ (‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖)
          * ((‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖)
            * hsNorm (b - c)) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ M * (α⁻¹ * hsNorm (b - c)) := by
        refine mul_le_mul hP2 (mul_le_mul_of_nonneg_right hN2 (hsNorm_nonneg _))
          (mul_nonneg (by positivity) (hsNorm_nonneg _)) hM.le
    _ = (M * α⁻¹) * hsNorm (b - c) := by ring

/-- **Hilbert–Schmidt Lipschitz estimate for the geometric mean in its first argument.** -/
theorem hsNorm_gm_sub_le_left {a b c : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (hc : IsStrictlyPositive c) {α γ M : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hM : 0 < M)
    (hcα : α • (1 : E →L[ℂ] E) ≤ c) (hcM : c ≤ M • (1 : E →L[ℂ] E))
    (hga : γ • (1 : E →L[ℂ] E) ≤ gm c a) (hgb : γ • (1 : E →L[ℂ] E) ≤ gm c b)
    (hab : IsHilbertSchmidt (a - b)) :
    (2 * (γ * M⁻¹)) * hsNorm (gm a c - gm b c) ≤ (M * α⁻¹) * hsNorm (a - b) := by
  rw [gm_comm ha hc, gm_comm hb hc]
  exact hsNorm_gm_sub_le_of_Icc hc ha hb hα hγ hM hcα hcM hga hgb hab

/-- **The difference of geometric means in the first argument is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_gm_sub_left {a b c : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (hc : IsStrictlyPositive c) {γ M : ℝ}
    (hγ : 0 < γ) (hM : 0 < M) (hcM : c ≤ M • (1 : E →L[ℂ] E))
    (hga : γ • (1 : E →L[ℂ] E) ≤ gm c a) (hgb : γ • (1 : E →L[ℂ] E) ≤ gm c b)
    (hab : IsHilbertSchmidt (a - b)) : IsHilbertSchmidt (gm a c - gm b c) := by
  rw [gm_comm ha hc, gm_comm hb hc]
  exact isHilbertSchmidt_gm_sub hc ha hb hγ hM hcM hga hgb hab

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
