import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace

/-!
# Fixed-weight FE--Schwarz Ward dichotomy

The exact four-sector trace classification leaves two—and only two—ways a fixed
reflection-invariant orbit Ward identity can vanish on every Xi copy. Its two conjugate-pair
weights may have zero total, in which case cancellation is unconditional and RH-blind; otherwise
the Ward identity is equivalent to RH. Positive-total-weight stationarity is therefore not a
formal consequence of covariance, Stokes orientation, or group averaging: it is the entire
remaining HB theorem.

`[NEW] [WARD CLASSIFICATION] [NO-GO] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Global fixed-weight orbit Ward identity. -/
def HBXiPeierlsFESchwarzFixedWeightWardIdentity
    (n : ℕ) (a b : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    hbXiPeierlsFESchwarzWeightedOrbitCubicTrace n q a b = 0

theorem hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff
    (n : ℕ) (a b : ℝ) :
    HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b ↔
      a + b = 0 ∨ RiemannHypothesis := by
  constructor
  · intro h
    by_cases hsum : a + b = 0
    · exact Or.inl hsum
    · right
      apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
        n).mp
      intro q
      apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
      exact ((hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff n q a b).mp
        (h q)).resolve_left hsum
  · rintro (hsum | hRH)
    · intro q
      exact (hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff n q a b).mpr
        (Or.inl hsum)
    · intro q
      apply (hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff n q a b).mpr
      right
      exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (q.1 : ℂ)
        (xi_eq_zero_of_mem_divisor_support q.1)

theorem hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff_rh_of_sum_ne_zero
    (n : ℕ) (a b : ℝ) (hsum : a + b ≠ 0) :
    HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b ↔
      RiemannHypothesis := by
  rw [hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff]
  exact or_iff_right hsum

theorem hbXiPeierlsFESchwarzPositiveWeightWardIdentity_iff_rh
    (n : ℕ) (a b : ℝ) (hsum : 0 < a + b) :
    HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b ↔
      RiemannHypothesis := by
  exact hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff_rh_of_sum_ne_zero
    n a b hsum.ne'

theorem hbXiPeierlsFESchwarzZeroTotalWardIdentity
    (n : ℕ) (a b : ℝ) (hsum : a + b = 0) :
    HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b := by
  exact (hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff n a b).mpr
    (Or.inl hsum)

end

end RHTower
