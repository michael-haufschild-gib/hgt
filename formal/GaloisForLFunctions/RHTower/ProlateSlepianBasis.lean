import GaloisForLFunctions.RHTower.ConstrainedProlateConcentrationInjective

/-!
# The Slepian Hilbert basis of the time-limited carrier

The even concentration modes with nonzero singular value are orthonormal, lie in the time-limited
carrier, and — by the injectivity of the concentration operator there — span it.  Dead greedy vectors
are literally zero (`svVec_eq_zero_of_svVal_eq_zero`), so orthogonality to the live family already
implies orthogonality to the whole greedy family, and the completeness theorem applies.

This is the coordinate system in which the constrained-prolate transfer theorems are stated: the
leakage operator is diagonal in it with eigenvalues `evenProlateSignedLeakage`, and the zero-integral
constraint becomes a single linear condition on the coordinates.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

instance evenTimeLimitedSubspace_normedAddCommGroup (a : ℝ) :
    NormedAddCommGroup (evenTimeLimitedSubspace a) :=
  (evenTimeLimitedSubspace a).normedAddCommGroup

instance evenTimeLimitedSubspace_innerProductSpace (a : ℝ) :
    InnerProductSpace ℂ (evenTimeLimitedSubspace a) :=
  (evenTimeLimitedSubspace a).innerProductSpace

/-- The live indices of the even Slepian family. -/
def slepianLiveIndex (a : ℝ) : Type := {n : ℕ // evenProlateConcentrationValue a n ≠ 0}

instance (a : ℝ) : CoeHead (slepianLiveIndex a) ℕ := ⟨Subtype.val⟩

/-- A live Slepian mode, typed as an element of the time-limited carrier. -/
def slepianCarrierMode (a : ℝ) (n : slepianLiveIndex a) : evenTimeLimitedSubspace a :=
  ⟨evenProlateConcentrationMode a n.1,
    evenProlateConcentrationMode_mem_timeLimited_of_value_ne_zero a n.2⟩

theorem slepianCarrierMode_coe (a : ℝ) (n : slepianLiveIndex a) :
    ((slepianCarrierMode a n : evenTimeLimitedSubspace a) : evenSubspace)
      = evenProlateConcentrationMode a n.1 := rfl

/-- **The live Slepian modes are orthonormal in the carrier.** -/
theorem orthonormal_slepianCarrierMode {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (slepianCarrierMode a) := by
  constructor
  · intro n
    have h := norm_evenProlateConcentrationMode_of_value_ne_zero a ha n.2
    simpa [slepianCarrierMode] using h
  · intro m n hmn
    have hne : (m : ℕ) ≠ (n : ℕ) := fun h => hmn (Subtype.ext h)
    have h := evenProlateConcentrationMode_orthogonal_of_ne a hne
    simpa [slepianCarrierMode] using h

/-- **The live Slepian modes span the carrier.** -/
theorem slepianCarrierMode_orthogonal_eq_bot {a : ℝ} (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (slepianCarrierMode a)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxorth : ∀ n : ℕ, (inner ℂ (evenProlateConcentrationMode a n)
      ((x : evenTimeLimitedSubspace a) : evenSubspace) : ℂ) = 0 := by
    intro n
    by_cases hn : evenProlateConcentrationValue a n = 0
    · have hzero : evenProlateConcentrationMode a n = 0 :=
        ContinuousLinearMap.svVec_eq_zero_of_svVal_eq_zero _ hn
      rw [hzero]
      simp
    · have hmem : slepianCarrierMode a ⟨n, hn⟩ ∈ Set.range (slepianCarrierMode a) :=
        ⟨⟨n, hn⟩, rfl⟩
      have h := hx (slepianCarrierMode a ⟨n, hn⟩) (Submodule.subset_span hmem)
      simpa [slepianCarrierMode] using h
  have hcarrier : ((x : evenTimeLimitedSubspace a) : evenSubspace)
      ∈ evenTimeLimitedSubspace a := x.2
  have := evenProlateConcentrationMode_complete_on_timeLimited ha hcarrier hxorth
  exact Subtype.ext this

/-- **The Slepian Hilbert basis of the time-limited carrier.** -/
def slepianCarrierBasis (a : ℝ) (ha : 0 < a) :
    HilbertBasis (slepianLiveIndex a) ℂ (evenTimeLimitedSubspace a) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_slepianCarrierMode ha)
    (slepianCarrierMode_orthogonal_eq_bot ha)

theorem slepianCarrierBasis_apply (a : ℝ) (ha : 0 < a) (n : slepianLiveIndex a) :
    slepianCarrierBasis a ha n = slepianCarrierMode a n := by
  rw [slepianCarrierBasis]
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (orthonormal_slepianCarrierMode ha) (slepianCarrierMode_orthogonal_eq_bot ha)) n

end RHTower

end
