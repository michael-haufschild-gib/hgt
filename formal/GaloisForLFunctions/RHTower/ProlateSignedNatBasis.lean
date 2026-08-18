import GaloisForLFunctions.RHTower.ProlateConstraintCoordinateExpansion

/-!
# The signed Slepian basis, indexed by the natural numbers

Every signed value is nonzero at a positive aperture (`evenProlateSignedValue_ne_zero`, proved in the
corpus from the shell vectors: a vanishing value would force the carrier to be finite dimensional).
So the live index type is all of `ℕ`, and the signed Slepian basis of the time-limited carrier can be
indexed by `ℕ` directly — which is the index type the constrained-prolate transfer theorems use for
their diagonal `d` and constraint sequence `ℓ`.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The signed modes of a positive aperture, as elements of the carrier, indexed by `ℕ`. -/
def signedNatMode (a : ℝ) (ha : 0 < a) (n : ℕ) : evenTimeLimitedSubspace a :=
  ⟨evenProlateSignedMode a n,
    evenProlateSignedMode_mem_timeLimited_of_value_ne_zero a (evenProlateSignedValue_ne_zero ha n)⟩

theorem orthonormal_signedNatMode {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (signedNatMode a ha) := by
  constructor
  · intro n
    rcases evenProlateSignedMode_norm_zero_or_one a n with h0 | h1
    · exact absurd h0
        (evenProlateSignedMode_ne_zero_of_value_ne_zero a (evenProlateSignedValue_ne_zero ha n))
    · simpa [signedNatMode] using h1
  · intro m n hmn
    simpa [signedNatMode] using evenProlateSignedMode_orthogonal_of_ne a hmn

theorem signedNatMode_orthogonal_eq_bot {a : ℝ} (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (signedNatMode a ha)))ᗮ = ⊥ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (adjoint_evenTimeBandFourier a)
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxorth : ∀ n : ℕ, (inner ℂ (evenProlateSignedMode a n)
      ((x : evenTimeLimitedSubspace a) : evenSubspace) : ℂ) = 0 := by
    intro n
    have h := hx (signedNatMode a ha n) (Submodule.subset_span ⟨n, rfl⟩)
    simpa [signedNatMode] using h
  have hT : evenTimeBandFourier a ((x : evenTimeLimitedSubspace a) : evenSubspace) = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_forall_inner_sgVec
      (isCompactOperator_evenTimeBandFourier a ha) hsym hxorth
  exact Subtype.ext (evenTimeBandFourier_injective_on_timeLimited ha x.2 hT)

/-- **The signed Slepian Hilbert basis, indexed by `ℕ`.** -/
def signedNatBasis (a : ℝ) (ha : 0 < a) :
    HilbertBasis ℕ ℂ (evenTimeLimitedSubspace a) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_signedNatMode ha)
    (signedNatMode_orthogonal_eq_bot ha)

theorem signedNatBasis_apply (a : ℝ) (ha : 0 < a) (n : ℕ) :
    signedNatBasis a ha n = signedNatMode a ha n := by
  rw [signedNatBasis]
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (orthonormal_signedNatMode ha) (signedNatMode_orthogonal_eq_bot ha)) n

/-- **The constraint functional in `ℕ`-indexed coordinates.** -/
theorem hasSum_inner_evenCentralIndicator_nat {a : ℝ} (ha : 0 < a)
    (x : evenTimeLimitedSubspace a) :
    HasSum (fun n : ℕ => (signedNatBasis a ha).repr x n * evenProlateConstraintCoord a n)
      (inner ℂ (evenCentralIndicator a) ((x : evenTimeLimitedSubspace a) : evenSubspace)) := by
  have hrepr := (signedNatBasis a ha).hasSum_repr x
  set f : evenTimeLimitedSubspace a →L[ℂ] ℂ :=
    (innerSL ℂ (evenCentralIndicator a)).comp (evenTimeLimitedSubspace a).subtypeL with hfdef
  have hmap := f.hasSum hrepr
  have hterm : ∀ n : ℕ,
      f ((signedNatBasis a ha).repr x n • (signedNatBasis a ha) n)
        = (signedNatBasis a ha).repr x n * evenProlateConstraintCoord a n := by
    intro n
    rw [map_smul, signedNatBasis_apply]
    have hval : f (signedNatMode a ha n) = evenProlateConstraintCoord a n := rfl
    rw [hval, smul_eq_mul]
  have hfun : (fun n : ℕ =>
      f ((signedNatBasis a ha).repr x n • (signedNatBasis a ha) n))
      = fun n : ℕ => (signedNatBasis a ha).repr x n * evenProlateConstraintCoord a n :=
    funext hterm
  rw [hfun] at hmap
  exact hmap

end RHTower

end
