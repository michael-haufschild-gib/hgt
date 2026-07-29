import GaloisForLFunctions.HTGeometry.RepresentationFracture

/-!
# Agreement and disagreement projectors of a pure pair

Two commuting complex structures `J₁`, `J₂` have an involutive product `K = J₁J₂`. This file
proves that the half-sum and half-difference projectors are complementary and identifies their
ranges exactly:

* `(1 - K) / 2` projects onto the locus where `J₁ = J₂`;
* `(1 + K) / 2` projects onto the locus where `J₁ = -J₂`.

These are unconditional finite-dimensional complex matrix identities. The file does not assert
that the matrices arise from pure spinors, that either range has dimension six or four, or that a
range is an internal or spacetime carrier.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Product comparison of two complex structures. -/
def purePairComparison
    (J₁ J₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  J₁ * J₂

/-- Projector onto directions where the complex structures agree. -/
def purePairAgreementProjection
    (J₁ J₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  involutionProjection (purePairComparison J₁ J₂)

/-- Projector onto directions where the complex structures disagree. -/
def purePairDisagreementProjection
    (J₁ J₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 + purePairComparison J₁ J₂)

/-- Commuting complex structures have an involutive product. -/
theorem purePairComparison_sq
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    purePairComparison J₁ J₂ * purePairComparison J₁ J₂ = 1 := by
  calc
    purePairComparison J₁ J₂ * purePairComparison J₁ J₂ =
        J₁ * (J₂ * J₁) * J₂ := by
          simp only [purePairComparison]
          noncomm_ring
    _ = J₁ * (J₁ * J₂) * J₂ := by rw [hcomm]
    _ = (J₁ * J₁) * (J₂ * J₂) := by noncomm_ring
    _ = (-1) * (-1) := by rw [hJ₁, hJ₂]
    _ = 1 := by simp

/-- Agreement and disagreement projectors sum to the identity. -/
theorem purePairAgreement_add_disagreement
    (J₁ J₂ : Matrix n n ℂ) :
    purePairAgreementProjection J₁ J₂ +
        purePairDisagreementProjection J₁ J₂ = 1 := by
  simp only [purePairAgreementProjection, purePairDisagreementProjection,
    involutionProjection]
  module

/-- The agreement projector is idempotent. -/
theorem purePairAgreementProjection_isIdempotent
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    IsIdempotentElem (purePairAgreementProjection J₁ J₂) := by
  exact involutionProjection_isIdempotent _
    (purePairComparison_sq J₁ J₂ hJ₁ hJ₂ hcomm)

/-- The disagreement projector is the complement of the agreement projector. -/
theorem purePairDisagreement_eq_one_sub_agreement
    (J₁ J₂ : Matrix n n ℂ) :
    purePairDisagreementProjection J₁ J₂ =
      1 - purePairAgreementProjection J₁ J₂ := by
  have h := purePairAgreement_add_disagreement J₁ J₂
  exact eq_sub_iff_add_eq'.mpr h

/-- The disagreement projector is idempotent. -/
theorem purePairDisagreementProjection_isIdempotent
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    IsIdempotentElem (purePairDisagreementProjection J₁ J₂) := by
  rw [purePairDisagreement_eq_one_sub_agreement, IsIdempotentElem]
  have hP :=
    (purePairAgreementProjection_isIdempotent J₁ J₂ hJ₁ hJ₂ hcomm).eq
  calc
    (1 - purePairAgreementProjection J₁ J₂) *
          (1 - purePairAgreementProjection J₁ J₂) =
        1 - purePairAgreementProjection J₁ J₂ -
          purePairAgreementProjection J₁ J₂ +
          purePairAgreementProjection J₁ J₂ *
            purePairAgreementProjection J₁ J₂ := by noncomm_ring
    _ = 1 - purePairAgreementProjection J₁ J₂ := by rw [hP]; module

/-- Agreement followed by disagreement is zero. -/
theorem purePairAgreement_mul_disagreement
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    purePairAgreementProjection J₁ J₂ *
        purePairDisagreementProjection J₁ J₂ = 0 := by
  rw [purePairDisagreement_eq_one_sub_agreement]
  have hP :=
    (purePairAgreementProjection_isIdempotent J₁ J₂ hJ₁ hJ₂ hcomm).eq
  calc
    purePairAgreementProjection J₁ J₂ *
          (1 - purePairAgreementProjection J₁ J₂) =
        purePairAgreementProjection J₁ J₂ -
          purePairAgreementProjection J₁ J₂ *
            purePairAgreementProjection J₁ J₂ := by noncomm_ring
    _ = 0 := by rw [hP]; simp

/-- Disagreement followed by agreement is zero. -/
theorem purePairDisagreement_mul_agreement
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    purePairDisagreementProjection J₁ J₂ *
        purePairAgreementProjection J₁ J₂ = 0 := by
  rw [purePairDisagreement_eq_one_sub_agreement]
  have hP :=
    (purePairAgreementProjection_isIdempotent J₁ J₂ hJ₁ hJ₂ hcomm).eq
  calc
    (1 - purePairAgreementProjection J₁ J₂) *
          purePairAgreementProjection J₁ J₂ =
        purePairAgreementProjection J₁ J₂ -
          purePairAgreementProjection J₁ J₂ *
            purePairAgreementProjection J₁ J₂ := by noncomm_ring
    _ = 0 := by rw [hP]; simp

/-- The agreement projector lands where the complex structures agree. -/
theorem purePairAgreement_difference_mul
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    (J₁ - J₂) * purePairAgreementProjection J₁ J₂ = 0 := by
  have hJ₁K : J₁ * purePairComparison J₁ J₂ = -J₂ := by
    simp only [purePairComparison]
    calc
      J₁ * (J₁ * J₂) = (J₁ * J₁) * J₂ := by noncomm_ring
      _ = (-1) * J₂ := by rw [hJ₁]
      _ = -J₂ := by simp
  have hJ₂K : J₂ * purePairComparison J₁ J₂ = -J₁ := by
    simp only [purePairComparison]
    calc
      J₂ * (J₁ * J₂) = J₁ * (J₂ * J₂) := by
        rw [← mul_assoc, hcomm, mul_assoc]
      _ = J₁ * (-1) := by rw [hJ₂]
      _ = -J₁ := by simp
  simp only [purePairAgreementProjection, involutionProjection,
    Matrix.mul_smul, Matrix.mul_sub, mul_one, sub_mul]
  rw [hJ₁K, hJ₂K]
  module

/-- The disagreement projector lands where the complex structures are opposite. -/
theorem purePairDisagreement_sum_mul
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    (J₁ + J₂) * purePairDisagreementProjection J₁ J₂ = 0 := by
  have hJ₁K : J₁ * purePairComparison J₁ J₂ = -J₂ := by
    simp only [purePairComparison]
    calc
      J₁ * (J₁ * J₂) = (J₁ * J₁) * J₂ := by noncomm_ring
      _ = (-1) * J₂ := by rw [hJ₁]
      _ = -J₂ := by simp
  have hJ₂K : J₂ * purePairComparison J₁ J₂ = -J₁ := by
    simp only [purePairComparison]
    calc
      J₂ * (J₁ * J₂) = J₁ * (J₂ * J₂) := by
        rw [← mul_assoc, hcomm, mul_assoc]
      _ = J₁ * (-1) := by rw [hJ₂]
      _ = -J₁ := by simp
  simp only [purePairDisagreementProjection, Matrix.mul_smul,
    Matrix.mul_add, mul_one, add_mul]
  rw [hJ₁K, hJ₂K]
  module

/-- The agreement range is contained in the equal-complex-structure locus. -/
theorem purePairAgreement_range_le_ker_difference
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    LinearMap.range (purePairAgreementProjection J₁ J₂).toLin' ≤
      LinearMap.ker (J₁ - J₂).toLin' := by
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul,
    purePairAgreement_difference_mul J₁ J₂ hJ₁ hJ₂ hcomm]
  simp

/-- The disagreement range is contained in the opposite-complex-structure locus. -/
theorem purePairDisagreement_range_le_ker_sum
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    LinearMap.range (purePairDisagreementProjection J₁ J₂).toLin' ≤
      LinearMap.ker (J₁ + J₂).toLin' := by
  rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul,
    purePairDisagreement_sum_mul J₁ J₂ hJ₁ hJ₂ hcomm]
  simp

/-- The complementary projector factors through failure of agreement. -/
theorem purePairDisagreement_factor_difference
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1) :
    purePairDisagreementProjection J₁ J₂ =
      -(2 : ℂ)⁻¹ • (J₁ * (J₁ - J₂)) := by
  have hfactor :
      J₁ * (J₁ - J₂) = -(1 + purePairComparison J₁ J₂) := by
    simp only [mul_sub, purePairComparison, hJ₁]
    module
  rw [hfactor]
  simp only [purePairDisagreementProjection]
  module

/-- The complementary projector factors through failure of opposition. -/
theorem purePairAgreement_factor_sum
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1) :
    purePairAgreementProjection J₁ J₂ =
      -(2 : ℂ)⁻¹ • (J₁ * (J₁ + J₂)) := by
  have hfactor :
      J₁ * (J₁ + J₂) = -(1 - purePairComparison J₁ J₂) := by
    simp only [mul_add, purePairComparison, hJ₁]
    module
  rw [hfactor]
  simp only [purePairAgreementProjection, involutionProjection]
  module

/-- The agreement projector has exactly the locus where the two complex structures agree. -/
theorem purePairAgreement_range_eq_ker_difference
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    LinearMap.range (purePairAgreementProjection J₁ J₂).toLin' =
      LinearMap.ker (J₁ - J₂).toLin' := by
  apply le_antisymm
  · exact purePairAgreement_range_le_ker_difference J₁ J₂ hJ₁ hJ₂ hcomm
  · intro x hx
    have hx0 : (J₁ - J₂).mulVec x = 0 := by
      simpa only [Matrix.toLin'_apply] using hx
    have hD :
        (purePairDisagreementProjection J₁ J₂).toLin' x = 0 := by
      rw [purePairDisagreement_factor_difference J₁ J₂ hJ₁]
      simp only [Matrix.toLin'_apply, Matrix.smul_mulVec]
      rw [← Matrix.mulVec_mulVec, hx0]
      simp
    refine ⟨x, ?_⟩
    have hsum := congrArg
      (fun A : Matrix n n ℂ => A.toLin' x)
      (purePairAgreement_add_disagreement J₁ J₂)
    simp only [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec] at hsum
    rw [Matrix.toLin'_apply] at hD ⊢
    rw [hD, add_zero] at hsum
    exact hsum

/-- The disagreement projector has exactly the locus where the complex structures are opposite. -/
theorem purePairDisagreement_range_eq_ker_sum
    (J₁ J₂ : Matrix n n ℂ)
    (hJ₁ : J₁ * J₁ = -1)
    (hJ₂ : J₂ * J₂ = -1)
    (hcomm : J₂ * J₁ = J₁ * J₂) :
    LinearMap.range (purePairDisagreementProjection J₁ J₂).toLin' =
      LinearMap.ker (J₁ + J₂).toLin' := by
  apply le_antisymm
  · exact purePairDisagreement_range_le_ker_sum J₁ J₂ hJ₁ hJ₂ hcomm
  · intro x hx
    have hx0 : (J₁ + J₂).mulVec x = 0 := by
      simpa only [Matrix.toLin'_apply] using hx
    have hA :
        (purePairAgreementProjection J₁ J₂).toLin' x = 0 := by
      rw [purePairAgreement_factor_sum J₁ J₂ hJ₁]
      simp only [Matrix.toLin'_apply, Matrix.smul_mulVec]
      rw [← Matrix.mulVec_mulVec, hx0]
      simp
    refine ⟨x, ?_⟩
    have hsum := congrArg
      (fun A : Matrix n n ℂ => A.toLin' x)
      (purePairAgreement_add_disagreement J₁ J₂)
    simp only [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec] at hsum
    rw [Matrix.toLin'_apply] at hA ⊢
    rw [hA, zero_add] at hsum
    exact hsum

end GaloisForLFunctions.HTGeometry
