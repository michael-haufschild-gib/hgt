import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinBounds

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

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
