import GaloisForLFunctions.HTGeometry.BuresWasserstein.GeometricMeanLipschitz
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldHilbertSchmidt
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# The affine homotopy of a Wasserstein family

To continue the Wasserstein equation from a family for which the Loewner ratio is small to an
arbitrary family, Kim–Mer–Pálfia use `t ↦ Aᵢ^t`.  The affine homotopy
`Aᵢ(t) = (1-t)·1 + t·Aᵢ` serves the same purpose and is far better behaved: it is *exactly*
Lipschitz in `t`, with constant `‖Aᵢ - 1‖`, and it stays in the fixed Loewner interval
`[min(1,α)·1, max(1,β)·1]` for all `t ∈ [0,1]`, so every constant along the continuation is
uniform.  At `t = 0` the family is constantly `1`, whose Wasserstein point is `1`.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

/-- The affine homotopy from the constant family `1` to the family `Av`. -/
noncomputable def homotopyFamily (Av : ι → A) (t : ℝ) (i : ι) : A :=
  (1 - t) • (1 : A) + t • Av i

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma homotopyFamily_zero (Av : ι → A) (i : ι) : homotopyFamily Av 0 i = 1 := by
  simp [homotopyFamily]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma homotopyFamily_one (Av : ι → A) (i : ι) : homotopyFamily Av 1 i = Av i := by
  simp [homotopyFamily]

omit [PartialOrder A] [StarOrderedRing A] in
lemma homotopyFamily_sub (Av : ι → A) (s t : ℝ) (i : ι) :
    homotopyFamily Av s i - homotopyFamily Av t i = (s - t) • (Av i - 1) := by
  unfold homotopyFamily
  rw [smul_sub, sub_smul]
  module

omit [PartialOrder A] [StarOrderedRing A] in
lemma isSelfAdjoint_homotopyFamily {Av : ι → A} (hA : IsSelfAdjoint (Av i)) (t : ℝ) :
    IsSelfAdjoint (homotopyFamily Av t i) :=
  (IsSelfAdjoint.smul (star_trivial _) (IsSelfAdjoint.one A)).add
    (IsSelfAdjoint.smul (star_trivial _) hA)

/-- The homotopy stays above the smaller of `1` and the lower Loewner bound. -/
lemma smul_one_le_homotopyFamily {Av : ι → A} {α t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAα : α • (1 : A) ≤ Av i) : (min 1 α) • (1 : A) ≤ homotopyFamily Av t i := by
  unfold homotopyFamily
  have h1 : ((1 - t) * min 1 α) • (1 : A) ≤ (1 - t) • (1 : A) := by
    refine smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := A))
    nlinarith [min_le_left (1 : ℝ) α, ht1]
  have h2 : (t * min 1 α) • (1 : A) ≤ t • Av i := by
    rw [mul_smul]
    refine smul_le_smul_of_nonneg_left ?_ ht0
    exact (smul_le_smul_of_nonneg_right (min_le_right 1 α) (zero_le_one (α := A))).trans hAα
  have hsum := add_le_add h1 h2
  rwa [← add_smul, show (1 - t) * min 1 α + t * min 1 α = min 1 α by ring] at hsum

/-- The homotopy stays below the larger of `1` and the upper Loewner bound. -/
lemma homotopyFamily_le_smul_one {Av : ι → A} {β t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAβ : Av i ≤ β • (1 : A)) : homotopyFamily Av t i ≤ (max 1 β) • (1 : A) := by
  unfold homotopyFamily
  have h1 : (1 - t) • (1 : A) ≤ ((1 - t) * max 1 β) • (1 : A) := by
    refine smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := A))
    nlinarith [le_max_left (1 : ℝ) β, ht1]
  have h2 : t • Av i ≤ (t * max 1 β) • (1 : A) := by
    rw [mul_smul]
    refine smul_le_smul_of_nonneg_left ?_ ht0
    exact hAβ.trans (smul_le_smul_of_nonneg_right (le_max_right 1 β) (zero_le_one (α := A)))
  have hsum := add_le_add h1 h2
  rwa [← add_smul, show (1 - t) * max 1 β + t * max 1 β = max 1 β by ring] at hsum

/-- The homotopy is strictly positive. -/
lemma isStrictlyPositive_homotopyFamily {Av : ι → A} {α t : ℝ} (hα : 0 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAα : α • (1 : A) ≤ Av i) : IsStrictlyPositive (homotopyFamily Av t i) := by
  have hmin : (0 : ℝ) < min 1 α := lt_min one_pos hα
  have hlow := smul_one_le_homotopyFamily (Av := Av) (i := i) ht0 ht1 hAα
  refine (CStarAlgebra.isUnit_of_le _ hlow
    (IsStrictlyPositive.smul hmin isStrictlyPositive_one)).isStrictlyPositive ?_
  exact le_trans (smul_nonneg hmin.le zero_le_one) hlow

/-! ### Lipschitz dependence of the Wasserstein field on the homotopy parameter -/

variable {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X : A}

/-- **The Wasserstein field is Lipschitz in the homotopy parameter.** -/
theorem norm_wassField_homotopy_sub_le {α M γ Λ σ τ : ℝ}
    (hα : 0 < α) (hM : 0 < M) (hγ : 0 < γ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hX : IsStrictlyPositive X)
    (hXα : α • (1 : A) ≤ X⁻¹ʳ) (hXM : (X⁻¹ʳ : A) ≤ M • (1 : A))
    (hAσ : ∀ i ∈ s, IsStrictlyPositive (homotopyFamily Av σ i))
    (hAτ : ∀ i ∈ s, IsStrictlyPositive (homotopyFamily Av τ i))
    (hgσ : ∀ i ∈ s, γ • (1 : A) ≤ gm X⁻¹ʳ (homotopyFamily Av σ i))
    (hgτ : ∀ i ∈ s, γ • (1 : A) ≤ gm X⁻¹ʳ (homotopyFamily Av τ i))
    (hΛ : ∀ i ∈ s, ‖Av i - 1‖ ≤ Λ) :
    (2 * (γ * M⁻¹))
        * ‖wassField s w (homotopyFamily Av σ) X - wassField s w (homotopyFamily Av τ) X‖
      ≤ (M * α⁻¹) * (|σ - τ| * Λ) := by
  have hdiff : wassField s w (homotopyFamily Av σ) X - wassField s w (homotopyFamily Av τ) X
      = ∑ i ∈ s, w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
        - gm (homotopyFamily Av σ i) X⁻¹ʳ) := by
    unfold wassField
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hX, ← smul_sub]
    congr 1
    abel
  have hterm : ∀ i ∈ s, (2 * (γ * M⁻¹))
      * ‖w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ - gm (homotopyFamily Av σ i) X⁻¹ʳ)‖
      ≤ w i * ((M * α⁻¹) * (|σ - τ| * Λ)) := by
    intro i hi
    have hsub : ‖homotopyFamily Av τ i - homotopyFamily Av σ i‖ ≤ |σ - τ| * Λ := by
      rw [homotopyFamily_sub, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hΛ i hi) (abs_nonneg _)
    have hgm := norm_gm_sub_le_left (hAτ i hi) (hAσ i hi) hX.ringInverse hα hγ hM hXα hXM
      (hgτ i hi) (hgσ i hi)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    have hchain : (2 * (γ * M⁻¹))
        * ‖gm (homotopyFamily Av τ i) X⁻¹ʳ - gm (homotopyFamily Av σ i) X⁻¹ʳ‖
        ≤ (M * α⁻¹) * (|σ - τ| * Λ) :=
      hgm.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
    nlinarith [hw i hi, norm_nonneg (gm (homotopyFamily Av τ i) X⁻¹ʳ
      - gm (homotopyFamily Av σ i) X⁻¹ʳ), mul_pos (mul_pos two_pos hγ) (inv_pos.mpr hM)]
  rw [hdiff]
  calc (2 * (γ * M⁻¹))
        * ‖∑ i ∈ s, w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
          - gm (homotopyFamily Av σ i) X⁻¹ʳ)‖
      ≤ (2 * (γ * M⁻¹))
        * ∑ i ∈ s, ‖w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
          - gm (homotopyFamily Av σ i) X⁻¹ʳ)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i ∈ s, (2 * (γ * M⁻¹))
          * ‖w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
            - gm (homotopyFamily Av σ i) X⁻¹ʳ)‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, w i * ((M * α⁻¹) * (|σ - τ| * Λ)) := Finset.sum_le_sum hterm
    _ = (M * α⁻¹) * (|σ - τ| * Λ) := by rw [← Finset.sum_mul, hwsum, one_mul]

end

section HilbertSchmidt

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E} {X : E →L[ℂ] E}

/-- **The Wasserstein field is Lipschitz in the homotopy parameter**, in the Hilbert–Schmidt
norm. -/
theorem hsNorm_wassField_homotopy_sub_le {α M γ Λ σ τ : ℝ}
    (hα : 0 < α) (hM : 0 < M) (hγ : 0 < γ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hX : IsStrictlyPositive X)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X⁻¹ʳ) (hXM : (X⁻¹ʳ : E →L[ℂ] E) ≤ M • (1 : E →L[ℂ] E))
    (hAσ : ∀ i ∈ s, IsStrictlyPositive (homotopyFamily Av σ i))
    (hAτ : ∀ i ∈ s, IsStrictlyPositive (homotopyFamily Av τ i))
    (hgσ : ∀ i ∈ s, γ • (1 : E →L[ℂ] E) ≤ gm X⁻¹ʳ (homotopyFamily Av σ i))
    (hgτ : ∀ i ∈ s, γ • (1 : E →L[ℂ] E) ≤ gm X⁻¹ʳ (homotopyFamily Av τ i))
    (hHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hΛ : ∀ i ∈ s, hsNorm (Av i - 1) ≤ Λ) :
    (2 * (γ * M⁻¹))
        * hsNorm (wassField s w (homotopyFamily Av σ) X
          - wassField s w (homotopyFamily Av τ) X)
      ≤ (M * α⁻¹) * (|σ - τ| * Λ) := by
  have hsubHS : ∀ i ∈ s, IsHilbertSchmidt
      (homotopyFamily Av τ i - homotopyFamily Av σ i) := by
    intro i hi
    rw [homotopyFamily_sub]
    exact IsHilbertSchmidt.real_smul (hHS i hi) _
  have hdiff : wassField s w (homotopyFamily Av σ) X - wassField s w (homotopyFamily Av τ) X
      = ∑ i ∈ s, w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
        - gm (homotopyFamily Av σ i) X⁻¹ʳ) := by
    unfold wassField
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hX, ← smul_sub]
    congr 1
    abel
  have hHSterm : ∀ i ∈ s, IsHilbertSchmidt (w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
      - gm (homotopyFamily Av σ i) X⁻¹ʳ)) := fun i hi =>
    IsHilbertSchmidt.real_smul
      (isHilbertSchmidt_gm_sub_left (hAτ i hi) (hAσ i hi) hX.ringInverse hγ hM hXM
        (hgτ i hi) (hgσ i hi) (hsubHS i hi)) _
  have hterm : ∀ i ∈ s, (2 * (γ * M⁻¹))
      * hsNorm (w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ - gm (homotopyFamily Av σ i) X⁻¹ʳ))
      ≤ w i * ((M * α⁻¹) * (|σ - τ| * Λ)) := by
    intro i hi
    have hsub : hsNorm (homotopyFamily Av τ i - homotopyFamily Av σ i) ≤ |σ - τ| * Λ := by
      rw [homotopyFamily_sub, hsNorm_real_smul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hΛ i hi) (abs_nonneg _)
    have hgm := hsNorm_gm_sub_le_left (hAτ i hi) (hAσ i hi) hX.ringInverse hα hγ hM hXα hXM
      (hgτ i hi) (hgσ i hi) (hsubHS i hi)
    rw [hsNorm_real_smul, abs_of_nonneg (hw i hi)]
    have hchain : (2 * (γ * M⁻¹))
        * hsNorm (gm (homotopyFamily Av τ i) X⁻¹ʳ - gm (homotopyFamily Av σ i) X⁻¹ʳ)
        ≤ (M * α⁻¹) * (|σ - τ| * Λ) :=
      hgm.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
    nlinarith [hw i hi, hsNorm_nonneg (gm (homotopyFamily Av τ i) X⁻¹ʳ
      - gm (homotopyFamily Av σ i) X⁻¹ʳ), mul_pos (mul_pos two_pos hγ) (inv_pos.mpr hM)]
  rw [hdiff]
  calc (2 * (γ * M⁻¹))
        * hsNorm (∑ i ∈ s, w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
          - gm (homotopyFamily Av σ i) X⁻¹ʳ))
      ≤ (2 * (γ * M⁻¹))
        * ∑ i ∈ s, hsNorm (w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
          - gm (homotopyFamily Av σ i) X⁻¹ʳ)) :=
        mul_le_mul_of_nonneg_left (hsNorm_sum_le hHSterm) (by positivity)
    _ = ∑ i ∈ s, (2 * (γ * M⁻¹))
          * hsNorm (w i • (gm (homotopyFamily Av τ i) X⁻¹ʳ
            - gm (homotopyFamily Av σ i) X⁻¹ʳ)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, w i * ((M * α⁻¹) * (|σ - τ| * Λ)) := Finset.sum_le_sum hterm
    _ = (M * α⁻¹) * (|σ - τ| * Λ) := by rw [← Finset.sum_mul, hwsum, one_mul]

end

end HilbertSchmidt

end GaloisForLFunctions.HTGeometry.BuresWasserstein
