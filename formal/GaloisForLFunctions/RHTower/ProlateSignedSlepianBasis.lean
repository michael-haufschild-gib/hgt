import GaloisForLFunctions.RHTower.ProlateSlepianBasis
import GaloisForLFunctions.RHTower.ConstrainedProlateBesselBound

/-!
# The signed Slepian Hilbert basis of the time-limited carrier

The constrained-prolate transfer theorems are stated in the coordinates of the **signed** prolate
family `evenProlateSignedMode a n = sgVec (evenTimeBandFourier a) n`, whose leakage values are
`evenProlateSignedLeakage a n = 1 − σ_n²` and whose constraint coordinates are
`evenProlateConstraintCoord a n`.  This module builds the Hilbert basis of the time-limited carrier
in exactly that family.

Dead signed vectors are zero, so orthogonality to the live modes already gives orthogonality to the
whole signed family and `apply_eq_zero_of_forall_inner_sgVec` applies; injectivity of the compressed
Fourier transform on the carrier then makes the joint orthogonal complement trivial.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The live indices of the signed prolate family. -/
def signedLiveIndex (a : ℝ) : Type := {n : ℕ // evenProlateSignedValue a n ≠ 0}

theorem evenProlateSignedMode_ne_zero_of_value_ne_zero (a : ℝ) {n : ℕ}
    (hn : evenProlateSignedValue a n ≠ 0) : evenProlateSignedMode a n ≠ 0 := by
  intro h
  exact hn (ContinuousLinearMap.sgVal_zero_of_dead h)

/-- A live signed mode, typed as an element of the time-limited carrier. -/
def signedCarrierMode (a : ℝ) (n : signedLiveIndex a) : evenTimeLimitedSubspace a :=
  ⟨evenProlateSignedMode a n.1,
    evenProlateSignedMode_mem_timeLimited_of_value_ne_zero a n.2⟩

/-- **The live signed modes are orthonormal in the carrier.** -/
theorem orthonormal_signedCarrierMode (a : ℝ) :
    Orthonormal ℂ (signedCarrierMode a) := by
  constructor
  · intro n
    rcases evenProlateSignedMode_norm_zero_or_one a n.1 with h0 | h1
    · exact absurd h0 (evenProlateSignedMode_ne_zero_of_value_ne_zero a n.2)
    · simpa [signedCarrierMode] using h1
  · intro m n hmn
    have hne : m.1 ≠ n.1 := fun h => hmn (Subtype.ext h)
    simpa [signedCarrierMode] using evenProlateSignedMode_orthogonal_of_ne a hne

/-- **The live signed modes span the carrier.** -/
theorem signedCarrierMode_orthogonal_eq_bot {a : ℝ} (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (signedCarrierMode a)))ᗮ = ⊥ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (adjoint_evenTimeBandFourier a)
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxorth : ∀ n : ℕ, (inner ℂ (evenProlateSignedMode a n)
      ((x : evenTimeLimitedSubspace a) : evenSubspace) : ℂ) = 0 := by
    intro n
    by_cases hn : evenProlateSignedValue a n = 0
    · have hzero : evenProlateSignedMode a n = 0 := by
        refine ContinuousLinearMap.sgVec_eq_zero_of_orthSup_eq_zero _ ?_
        rw [← ContinuousLinearMap.abs_sgVal (isCompactOperator_evenTimeBandFourier a ha) hsym n,
          show ContinuousLinearMap.sgVal (evenTimeBandFourier a) n
            = evenProlateSignedValue a n from rfl, hn, abs_zero]
      rw [hzero]
      simp
    · have h := hx (signedCarrierMode a ⟨n, hn⟩) (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩)
      simpa [signedCarrierMode] using h
  have hT : evenTimeBandFourier a ((x : evenTimeLimitedSubspace a) : evenSubspace) = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_forall_inner_sgVec
      (isCompactOperator_evenTimeBandFourier a ha) hsym hxorth
  exact Subtype.ext (evenTimeBandFourier_injective_on_timeLimited ha x.2 hT)

/-- **The signed Slepian Hilbert basis of the time-limited carrier.**  This is the coordinate system
in which the constrained-prolate transfer theorems' diagonal `d` and constraint coordinates `ℓ` are
defined. -/
def signedCarrierBasis (a : ℝ) (ha : 0 < a) :
    HilbertBasis (signedLiveIndex a) ℂ (evenTimeLimitedSubspace a) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_signedCarrierMode a)
    (signedCarrierMode_orthogonal_eq_bot ha)

theorem signedCarrierBasis_apply (a : ℝ) (ha : 0 < a) (n : signedLiveIndex a) :
    signedCarrierBasis a ha n = signedCarrierMode a n := by
  rw [signedCarrierBasis]
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (orthonormal_signedCarrierMode a) (signedCarrierMode_orthogonal_eq_bot ha)) n

end RHTower

end
