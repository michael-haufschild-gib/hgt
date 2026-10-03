import GaloisForLFunctions.HTGeometry.CompactOperatorIdealSimplicity
import GaloisForLFunctions.HTGeometry.PrimeHodgeReachabilityProperness
import GaloisForLFunctions.RHTower.IntegralNuclearRelationIncidenceHorizon

/-!
# The prime–Hodge idempotence defect and the bounded multiplicative horizon no-go

For an injective compact operator `T` on an infinite-dimensional Hilbert space, the idempotence
defect `Δ_T = T - T²` is a nonzero element of the topologically simple ring `𝒦(H)`.  Hence every
continuous ring homomorphism `π` out of `𝒦(H)` (not assumed linear, unital, positive or
star-preserving) with `π(T)` idempotent vanishes identically, and `π(T) = 0`.

The prime–Hodge defect `𝖳_d = Φ ⊗ A_d` on `ℓ²(ℕ × Primes)` is compact and injective, so its
defect `Δ_d = 𝖳_d - 𝖳_d²` is full in `𝒦(ℓ²(ℕ × Primes))`, and no continuous ring homomorphism
sends `𝖳_d` to the strict-right relation-incidence horizon `P_ρ`, a nonzero rank-one projection.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower InnerProductSpace

/-! ## The abstract exclusion -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {B : Type*} [TopologicalSpace B] [NonUnitalRing B] [T1Space B]

/-- **Theorem 3.2 (PHFI.6).**  A continuous ring homomorphism out of `𝒦(H)` sending a faithful
compact operator to an idempotent vanishes; in particular it sends the operator to zero. -/
theorem compactOperatorRingHom_eq_zero_of_idempotent (hH : ¬ FiniteDimensional ℂ H)
    (T : CompactOperatorRing H) (hT : Function.Injective (T : H →L[ℂ] H))
    (π : CompactOperatorRing H →ₙ+* B) (hπ : Continuous π) (hidem : π T * π T = π T) :
    (∀ x, π x = 0) ∧ π T = 0 :=
  topologicallySimpleFormationIdempotenceDefect_closed π hπ T
    (formationIdempotenceDefect_ne_zero hH T hT) hidem

end Abstract

/-! ## The prime–Hodge defect -/

variable {d : ℝ}

/-- `𝖳_d` as an element of `𝒦(ℓ²(ℕ × Primes))`. -/
def primeHodgeCompactDefect (hd : 0 < d) : CompactOperatorRing PrimeHodgeHistoryHilbert :=
  ⟨primeHodgeHistoryDefectOperator hd,
    MemSchattenClass.isCompactOperator one_pos (primeHodgeHistoryDefectOperator_memSchattenClass_one hd)⟩

/-- **(PHFI.8)** `Δ_d = 𝖳_d - 𝖳_d² ≠ 0`. -/
theorem primeHodgeIdempotenceDefect_ne_zero (hd : 0 < d) :
    formationIdempotenceDefect (primeHodgeCompactDefect hd) ≠ 0 :=
  formationIdempotenceDefect_ne_zero not_finiteDimensional_primeHodgeHistoryHilbert _
    (primeHodgeHistoryDefectOperator_injective hd)

/-- **(PHFI.8)** `Δ_d` is full: every closed two-sided ideal of `𝒦(ℓ²(ℕ × Primes))` containing it is
everything. -/
theorem eq_top_of_primeHodgeIdempotenceDefect_mem (hd : 0 < d)
    (I : TwoSidedIdeal (CompactOperatorRing PrimeHodgeHistoryHilbert))
    (hI : IsClosed (I : Set (CompactOperatorRing PrimeHodgeHistoryHilbert)))
    (hmem : formationIdempotenceDefect (primeHodgeCompactDefect hd) ∈ I) : I = ⊤ :=
  eq_top_of_formationIdempotenceDefect_mem not_finiteDimensional_primeHodgeHistoryHilbert _
    (primeHodgeHistoryDefectOperator_injective hd) I hI hmem

/-- Every continuous ring homomorphism out of `𝒦(ℓ²(ℕ × Primes))` with `π(𝖳_d)` idempotent is zero. -/
theorem primeHodgeRingHom_eq_zero_of_idempotent (hd : 0 < d)
    {B : Type*} [TopologicalSpace B] [NonUnitalRing B] [T1Space B]
    (π : CompactOperatorRing PrimeHodgeHistoryHilbert →ₙ+* B) (hπ : Continuous π)
    (hidem : π (primeHodgeCompactDefect hd) * π (primeHodgeCompactDefect hd) =
      π (primeHodgeCompactDefect hd)) :
    (∀ x, π x = 0) ∧ π (primeHodgeCompactDefect hd) = 0 :=
  compactOperatorRingHom_eq_zero_of_idempotent not_finiteDimensional_primeHodgeHistoryHilbert _
    (primeHodgeHistoryDefectOperator_injective hd) π hπ hidem

/-! ## The relation-incidence horizon -/

theorem xiRightPrimeMixedHorizonDefect_mul_self (q : XiRightZeroCopy) :
    xiRightPrimeMixedHorizonDefect q * xiRightPrimeMixedHorizonDefect q =
      xiRightPrimeMixedHorizonDefect q := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hz : xiRightPrimeMixedHorizonDefect q z =
      ⟪deningerCalderonWittCrossPrimePacketHorizon, z⟫_ℂ • deningerCalderonWittCrossPrimePacketHorizon := by
    rw [xiRightPrimeMixedHorizonDefect, rankOne_apply]
  rw [mul_apply_eq_comp, hz, map_smul, xiRightPrimeMixedHorizonDefect_apply_horizon]

theorem xiRightPrimeMixedHorizonDefect_ne_zero (q : XiRightZeroCopy) :
    xiRightPrimeMixedHorizonDefect q ≠ 0 := by
  intro h
  have h1 := xiRightPrimeMixedHorizonDefect_apply_horizon q
  rw [h, zero_apply] at h1
  have h2 := deningerCalderonWittCrossPrimePacketHorizon_norm
  rw [← h1, norm_zero] at h2
  exact zero_ne_one h2

/-- **(PHFI.9) Bounded multiplicative horizon no-go.**  No continuous ring homomorphism
`𝒦(ℓ²(ℕ × Primes)) → B(H_ρ)` sends `𝖳_d` to the strict-right horizon projection `P_ρ`. -/
theorem not_exists_ringHom_primeHodge_to_horizon (hd : 0 < d) (q : XiRightZeroCopy) :
    ¬ ∃ π : CompactOperatorRing PrimeHodgeHistoryHilbert →ₙ+*
        (DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ] DeningerCalderonWittCrossPrimePacketHilbert),
      Continuous π ∧ π (primeHodgeCompactDefect hd) = xiRightPrimeMixedHorizonDefect q := by
  rintro ⟨π, hπ, hT⟩
  have hidem : π (primeHodgeCompactDefect hd) * π (primeHodgeCompactDefect hd) =
      π (primeHodgeCompactDefect hd) := by
    rw [hT, xiRightPrimeMixedHorizonDefect_mul_self]
  have h0 := (primeHodgeRingHom_eq_zero_of_idempotent hd π hπ hidem).2
  rw [hT] at h0
  exact xiRightPrimeMixedHorizonDefect_ne_zero q h0

end GaloisForLFunctions.HTGeometry
