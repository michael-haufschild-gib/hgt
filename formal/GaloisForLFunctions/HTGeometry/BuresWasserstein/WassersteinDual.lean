import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds

/-!
# The dual Wasserstein mean

The Wasserstein barycentre is not self-dual, so Kim–Mer–Pálfia (arXiv:2607.29142, §6) study the
*dual mean* `Ω(ω; 𝔸⁻¹)⁻¹`, characterised as the unique strictly positive solution of

`∑ᵢ wᵢ (X # Aᵢ⁻¹) = 1`,   equivalently   `∑ᵢ wᵢ (X^{1/2} Aᵢ X^{1/2})^{-1/2} = X⁻¹`.

Theorem 6.13 compares it with the quasi-arithmetic mean `Q_{-1/2}(ω; 𝔸) = (∑ wᵢ Aᵢ^{-1/2})^{-2}`:
if the dual mean is a contraction then so is `Q_{-1/2}`.  The engine is again Hansen's inequality
for the square root.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X : A}

/-- `X` is a **dual Wasserstein point** of `(w, Av)`: it is strictly positive and solves
`∑ᵢ wᵢ (X # Aᵢ⁻¹) = 1`. -/
def IsDualWassersteinPoint (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A) : Prop :=
  IsStrictlyPositive X ∧ ∑ i ∈ s, w i • gm X (Av i)⁻¹ʳ = 1

/-- The dual points of `(w, Av)` are exactly the inverses of the Wasserstein points of the
inverted family. -/
theorem isDualWassersteinPoint_iff (hX : IsStrictlyPositive X)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    IsDualWassersteinPoint s w Av X ↔
      IsWassersteinPoint s w (fun i => (Av i)⁻¹ʳ) X⁻¹ʳ := by
  unfold IsDualWassersteinPoint IsWassersteinPoint
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hX.ringInverse, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Ring.inverse_inverse hX.isUnit, gm_comm (hA i hi).ringInverse hX]
  · rintro ⟨-, h⟩
    refine ⟨hX, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Ring.inverse_inverse hX.isUnit, gm_comm (hA i hi).ringInverse hX]

/-- The inverse of a conjugation. -/
lemma ringInverse_conj_rpow_half (hX : IsStrictlyPositive X) {a : A} (ha : IsStrictlyPositive a) :
    (X ^ (1/2 : ℝ) * a * X ^ (1/2 : ℝ))⁻¹ʳ
      = X ^ (-(1/2) : ℝ) * a⁻¹ʳ * X ^ (-(1/2) : ℝ) := by
  rw [Ring.inverse_mul (Or.inl ((hX.rpow X _).isUnit.mul ha.isUnit)),
    Ring.inverse_mul (Or.inl (hX.rpow X _).isUnit), ringInverse_rpow_half hX, mul_assoc]

lemma rpow_half_mul_ringInverse_mul_rpow_half (hX : IsStrictlyPositive X) :
    X ^ (1/2 : ℝ) * X⁻¹ʳ * X ^ (1/2 : ℝ) = 1 := by
  rw [← rpow_neg_half_mul_rpow_neg_half hX,
    show X ^ (1/2 : ℝ) * (X ^ (-(1/2) : ℝ) * X ^ (-(1/2) : ℝ)) * X ^ (1/2 : ℝ)
      = (X ^ (1/2 : ℝ) * X ^ (-(1/2) : ℝ)) * (X ^ (-(1/2) : ℝ) * X ^ (1/2 : ℝ)) by
      simp only [mul_assoc],
    rpow_half_mul_rpow_neg_half hX, rpow_neg_half_mul_rpow_half hX, one_mul]

/-- The primal form of the dual equation:
`∑ wᵢ (X^{1/2} Aᵢ X^{1/2})^{-1/2} = X⁻¹`. -/
theorem isDualWassersteinPoint_iff_sqrtInv (hX : IsStrictlyPositive X)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    IsDualWassersteinPoint s w Av X ↔
      ∑ i ∈ s, w i • (CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)))⁻¹ʳ = X⁻¹ʳ := by
  have hconj : ∀ i ∈ s, X ^ (-(1/2) : ℝ) * gm X (Av i)⁻¹ʳ * X ^ (-(1/2) : ℝ)
      = (CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)))⁻¹ʳ := by
    intro i hi
    have hc := gm_conjugate (m := X ^ (-(1/2) : ℝ)) (hX.rpow X _).isUnit hX (hA i hi).ringInverse
    rw [(isSelfAdjoint_rpow X (-(1/2) : ℝ)).star_eq] at hc
    rw [hc, rpow_neg_half_mul_self_mul_rpow_neg_half hX, gm_one_left,
      ← ringInverse_conj_rpow_half hX (hA i hi),
      cfcSqrt_ringInverse (IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _
        (hX.rpow X _).isUnit (isSelfAdjoint_rpow X _) (hA i hi))]
  constructor
  · rintro ⟨-, h⟩
    have hL := congrArg (fun z : A => X ^ (-(1/2) : ℝ) * z * X ^ (-(1/2) : ℝ)) h
    simp only [← sum_smul_conjugate, mul_one] at hL
    rw [rpow_neg_half_mul_rpow_neg_half hX] at hL
    rw [← hL]
    exact Finset.sum_congr rfl fun i hi => by rw [hconj i hi]
  · intro h
    refine ⟨hX, ?_⟩
    have hL := congrArg (fun z : A => X ^ (1/2 : ℝ) * z * X ^ (1/2 : ℝ)) h
    simp only [← sum_smul_conjugate] at hL
    rw [rpow_half_mul_ringInverse_mul_rpow_half hX] at hL
    rw [← hL]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hconj i hi, sandwich_peel hX]

/-! ### Theorem 6.13 -/

/-- **Theorem 6.13**: if the dual Wasserstein mean is a contraction then so is the
quasi-arithmetic mean `Q_{-1/2}(ω; 𝔸) = (∑ wᵢ Aᵢ^{-1/2})^{-2}`. -/
theorem IsDualWassersteinPoint.one_le_sqrtInvMean (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsDualWassersteinPoint s w Av X)
    (hle : X ≤ 1) : (1 : A) ≤ ∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ := by
  have hX : IsStrictlyPositive X := h.1
  have hprimal := (isDualWassersteinPoint_iff_sqrtInv hX hA).mp h
  have hzsa : star (X ^ (1/2 : ℝ)) = X ^ (1/2 : ℝ) := (isSelfAdjoint_rpow X _).star_eq
  have hz : X ^ (1/2 : ℝ) * star (X ^ (1/2 : ℝ)) ≤ 1 := by
    rw [hzsa, rpow_half_mul_rpow_half hX]; exact hle
  have hstep : ∀ i ∈ s, (CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)))⁻¹ʳ
      ≤ X ^ (-(1/2) : ℝ) * (CFC.sqrt (Av i))⁻¹ʳ * X ^ (-(1/2) : ℝ) := by
    intro i hi
    have hh := conj_sqrt_le_sqrt_conj hz (Av i)
    rw [hzsa] at hh
    have hpos : IsStrictlyPositive (X ^ (1/2 : ℝ) * CFC.sqrt (Av i) * X ^ (1/2 : ℝ)) :=
      IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _
        (hX.rpow X _).isUnit (isSelfAdjoint_rpow X _) ((hA i hi).sqrt _)
    have hcmp := CStarAlgebra.ringInverse_le_ringInverse hh hpos
    rwa [ringInverse_conj_rpow_half hX ((hA i hi).sqrt _)] at hcmp
  have hsum : X⁻¹ʳ ≤ X ^ (-(1/2) : ℝ) * (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)
      * X ^ (-(1/2) : ℝ) := by
    rw [← hprimal, ← sum_smul_conjugate]
    exact Finset.sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (hstep i hi) (hw i hi)
  have hconj := (isSelfAdjoint_rpow X (1/2 : ℝ)).conjugate_le_conjugate hsum
  rwa [rpow_half_mul_ringInverse_mul_rpow_half hX, sandwich_peel hX] at hconj

/-- The contraction form of Theorem 6.13. -/
theorem IsDualWassersteinPoint.quasiArith_le_one (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsDualWassersteinPoint s w Av X)
    (hle : X ≤ 1) :
    (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ * (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ
      ≤ 1 := by
  have hone := h.one_le_sqrtInvMean hw hA hle
  have hQu : IsUnit (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ) :=
    CStarAlgebra.isUnit_of_le 1 hone isStrictlyPositive_one
  have hcmp := CStarAlgebra.ringInverse_le_ringInverse hone (isStrictlyPositive_one (A := A))
  rw [Ring.inverse_one] at hcmp
  have hQnn : (0 : A) ≤ (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ :=
    (hQu.isStrictlyPositive (le_trans zero_le_one hone)).ringInverse.nonneg
  have hmul := mul_self_le_of_le_smul_one hQnn zero_le_one (by simpa using hcmp)
  simpa using hmul

/-! ### Homogeneity and the norm form (Corollary 6.14) -/

/-- The dual equation is homogeneous. -/
theorem isDualWassersteinPoint_smul {r : ℝ} (hr : 0 < r) (hX : IsStrictlyPositive X)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    IsDualWassersteinPoint s w (fun i => r • Av i) (r • X) ↔
      IsDualWassersteinPoint s w Av X := by
  have hpt : ∀ i ∈ s, gm (r • X) ((r • Av i)⁻¹ʳ) = gm X ((Av i)⁻¹ʳ) := by
    intro i hi
    rw [ringInverse_smul hr (hA i hi), gm_smul hr (inv_pos.mpr hr) hX (hA i hi).ringInverse,
      show r * r⁻¹ = 1 by field_simp, Real.sqrt_one, one_smul]
  unfold IsDualWassersteinPoint
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hX, by rw [← h]; exact (Finset.sum_congr rfl fun i hi => by rw [hpt i hi]).symm⟩
  · rintro ⟨-, h⟩
    exact ⟨hX.smul hr, by rw [← h]; exact Finset.sum_congr rfl fun i hi => by rw [hpt i hi]⟩

/-- **Corollary 6.14**: `‖Q_{-1/2}(ω; 𝔸)‖ ≤ ‖D‖` for the dual Wasserstein mean `D`. -/
theorem IsDualWassersteinPoint.norm_quasiArith_le (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsDualWassersteinPoint s w Av X) :
    ‖(∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ * (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ‖
      ≤ ‖X‖ := by
  have hX : IsStrictlyPositive X := h.1
  rcases eq_or_lt_of_le (norm_nonneg X) with hc | hc
  · have hX0 : X = 0 := norm_eq_zero.mp hc.symm
    have hsub : Subsingleton A := by
      rcases subsingleton_or_nontrivial A with hsub | _
      · exact hsub
      · exact absurd (hX0 ▸ hX.isUnit) not_isUnit_zero
    simp [Subsingleton.elim
      ((∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ * (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ) 0,
      ← hc]
  · set c := ‖X‖ with hcdef
    have hr : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have hsr : (0 : ℝ) < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr hr
    have hscaled : IsDualWassersteinPoint s w (fun i => c⁻¹ • Av i) (c⁻¹ • X) :=
      (isDualWassersteinPoint_smul hr hX hA).mpr h
    have hle : c⁻¹ • X ≤ (1 : A) := by
      have h1 : c⁻¹ • X ≤ c⁻¹ • (c • (1 : A)) :=
        smul_le_smul_of_nonneg_left (le_smul_one_norm hX.nonneg) hr.le
      rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h1
    have hone := hscaled.one_le_sqrtInvMean hw (fun i hi => (hA i hi).smul hr) hle
    have hrw : ∑ i ∈ s, w i • (CFC.sqrt (c⁻¹ • Av i))⁻¹ʳ
        = (Real.sqrt c⁻¹)⁻¹ • ∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [cfcSqrt_smul hr.le (hA i hi).nonneg,
        ringInverse_smul hsr ((hA i hi).sqrt _), smul_comm]
    rw [hrw] at hone
    have hQge : Real.sqrt c⁻¹ • (1 : A) ≤ ∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ := by
      have h2 := smul_le_smul_of_nonneg_left hone hsr.le
      rwa [smul_smul, mul_inv_cancel₀ hsr.ne', one_smul] at h2
    have hQpos : IsStrictlyPositive (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ) := by
      refine (CStarAlgebra.isUnit_of_le _ hQge
        (IsStrictlyPositive.smul hsr isStrictlyPositive_one)).isStrictlyPositive ?_
      exact le_trans (smul_nonneg hsr.le zero_le_one) hQge
    have hQinv : (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ ≤ (Real.sqrt c⁻¹)⁻¹ • (1 : A) := by
      have hcmp := CStarAlgebra.ringInverse_le_ringInverse hQge
        (IsStrictlyPositive.smul hsr isStrictlyPositive_one)
      rwa [ringInverse_smul hsr (isStrictlyPositive_one (A := A)), Ring.inverse_one] at hcmp
    have hsq := mul_self_le_of_le_smul_one hQpos.ringInverse.nonneg
      (inv_pos.mpr hsr).le hQinv
    have hnn : (0 : A) ≤ (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ
        * (∑ i ∈ s, w i • (CFC.sqrt (Av i))⁻¹ʳ)⁻¹ʳ := by
      nth_rewrite 1 [← hQpos.ringInverse.nonneg.isSelfAdjoint.star_eq]
      exact star_mul_self_nonneg _
    refine norm_le_of_le_smul_one hnn hc.le (hsq.trans (le_of_eq ?_))
    congr 1
    rw [Real.sqrt_inv, inv_inv, Real.mul_self_sqrt hc.le]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
