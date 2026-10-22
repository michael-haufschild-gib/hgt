import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheNodeFaceUnitIsAReciprocalPrimePower

/-!
# The prime powers are the least positive node set

Node criticality says that deleting one prime power from a node set destroys zero-pole positivity.
That is irredundancy: every prime power is needed. It does not say that the prime powers are
*enough*, so the positive node sets were not described. They are described here, and the
description is as tight as possible.

Blindness on a larger node set is a stronger constraint on the admissible combinations, so
positivity is monotone in the node set (`zeroPoleBlindPositiveOn_mono`) — a one-line consequence of
the definition that had not been drawn. With irredundancy on one side and monotonicity on the
other:

* `zeroPoleBlindPositiveOn_iff_primePowers_subset` — under RH, a node set is zero-pole positive
  **exactly** when it contains every prime power;
* `isLeast_zeroPoleBlindPositiveOn` — hence the prime powers are the least positive node set: the
  positive sets form a principal up-set with the prime powers as its bottom;
* `zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero` — and the node unit is faithful: positivity is
  exactly the vanishing of the node scale, so the floor `½` of the asymptotic readings is a floor
  for the criterion itself and not merely for a necessary condition.

The classification changes what a mechanism on this face has to do. It no longer has to establish an
inequality about a node set; it has to decide a *membership* question — whether a single prescribed
prime power lies in the data — and `resolves_nodeScale_iff_resolves_zeroPoleBlindPositiveOn`
transports every statement about one face to the other. This is the exact sense in which the node
face is pure incidence: it carries no magnitude at all, only a principal up-set.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ### 1. Positivity is monotone in the node set -/

/-- **Monotonicity.** Blindness on more nodes is a stronger constraint on the admissible
combinations, so a larger node set is easier to be positive on. -/
theorem zeroPoleBlindPositiveOn_mono {𝒩 ℳ : Set ℕ} (h : ZeroPoleBlindPositiveOn 𝒩)
    (hsub : 𝒩 ⊆ ℳ) : ZeroPoleBlindPositiveOn ℳ :=
  fun c hc hblind hmass => h c hc (fun j hj => hblind j (hsub hj)) hmass

/-! ### 2. The classification -/

/-- **Classification of the positive node sets.** Under RH a node set is zero-pole positive exactly
when it carries every prime power. -/
theorem zeroPoleBlindPositiveOn_iff_primePowers_subset (hRH : RiemannHypothesis) (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔ ∀ m : ℕ, IsPrimePow m → m ∈ 𝒩 := by
  refine ⟨fun h m hm => (nodeScale_eq_zero_iff 𝒩).mp
      (nodeScale_eq_zero_of_zeroPoleBlindPositiveOn h) m hm, fun h => ?_⟩
  exact zeroPoleBlindPositiveOn_mono
    (riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH) h

/-- **The prime powers are the least positive node set.** -/
theorem isLeast_zeroPoleBlindPositiveOn (hRH : RiemannHypothesis) :
    IsLeast {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} {n : ℕ | IsPrimePow n} := by
  refine ⟨riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH, ?_⟩
  intro 𝒩 h𝒩
  exact fun m hm => (zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩).mp h𝒩 m hm

/-- The positive node sets form a principal up-set. -/
theorem zeroPoleBlindPositiveOn_setOf_eq (hRH : RiemannHypothesis) :
    {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} = {𝒩 : Set ℕ | {n : ℕ | IsPrimePow n} ⊆ 𝒩} := by
  ext 𝒩
  exact zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩

/-! ### 3. The node unit is faithful -/

/-- **The node unit decides the node face.** Under RH, zero-pole positivity is exactly the
vanishing of the node scale. -/
theorem zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero (hRH : RiemannHypothesis) (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔ nodeScale 𝒩 = 0 := by
  rw [zeroPoleBlindPositiveOn_iff_primePowers_subset hRH, nodeScale_eq_zero_iff]

/-- **Transport between the two descriptions of the face.** A reading decides node positivity
exactly when it decides the vanishing of the node scale, so every floor in the node unit is a floor
for the criterion. -/
theorem resolves_nodeScale_iff_resolves_zeroPoleBlindPositiveOn (hRH : RiemannHypothesis)
    {O : Type*} (r : Set ℕ → O) :
    Resolves r (fun 𝒩 => nodeScale 𝒩 = 0) ↔ Resolves r ZeroPoleBlindPositiveOn := by
  constructor <;> intro h 𝒩 ℳ hmem
  · show ZeroPoleBlindPositiveOn ℳ ↔ ZeroPoleBlindPositiveOn 𝒩
    rw [zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
      zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH]
    exact h 𝒩 ℳ hmem
  · show nodeScale ℳ = 0 ↔ nodeScale 𝒩 = 0
    rw [← zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
      ← zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH]
    exact h 𝒩 ℳ hmem

/-- **The node face in one statement.** Under RH: the positive node sets are the supersets of the
prime powers, that set is least among them, positivity is the vanishing of the node unit, and no
asymptotic reading certifies anything about that unit beyond the trivial `½`. -/
theorem theNodeFaceIsAPrincipalUpSet (hRH : RiemannHypothesis) :
    IsLeast {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} {n : ℕ | IsPrimePow n} ∧
      (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn 𝒩 ↔ nodeScale 𝒩 = 0) ∧
      ∀ (O : Type) (r : Set ℕ → O), AsymptoticReading r →
        resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  ⟨isLeast_zeroPoleBlindPositiveOn hRH, zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
    fun _ _ h => resolutionLimit_nodeScale_asymptoticReading h⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
