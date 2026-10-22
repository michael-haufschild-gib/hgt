import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheNodeFaceUnitIsAReciprocalPrimePower
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem

/-!
# Finitely many membership bits have an exact limit

The node face has two very different classes of reading. The *asymptotic* ones — densities, counting
functions, sieve levels — have the trivial limit `½`
(`TheNodeFaceUnitIsAReciprocalPrimePower`), and no amount of them helps. The *finite* ones, which
read the membership of finitely many prescribed nodes, behave quite differently, and this module
computes their limit exactly.

Reading the bits of a finite set `S` leaves the data free at every node outside `S`. The worst case
is to omit the **smallest prime power not in `S`**, which exists because there are infinitely many
primes (`exists_primePow_notMem`) and is well defined (`leastMissingPrimePow`). Hence
(`resolutionLimit_nodeScale_bitsReading`)

`resolutionLimit nodeScale (bitsReading S) = 1 / q₀(S)`,

a nontrivial number, attained by deleting that one node. As `S` grows to contain every prime power
below a bound, `q₀(S)` grows and the limit decreases to `0`
(`bitsLadderConverges`): **the finite-bit ladder of the incidence face is a progress measure**,
unlike the asymptotic readings and unlike the aperture ladder in the width unit
(`WhichLaddersAreProgressMeasures`).

So the incidence face is not uniformly hopeless; it is hopeless only for readings that are blind to
individual nodes. A mechanism that verifies the incidence condition node by node makes exact,
quantified progress, and the quantity it improves is the reciprocal of the first node it has not yet
checked.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ### 1. The smallest unchecked node -/

/-- A finite set of nodes always omits a prime power. -/
theorem exists_primePow_notMem (S : Finset ℕ) : ∃ m : ℕ, IsPrimePow m ∧ m ∉ S := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (S.sup id + 1)
  refine ⟨p, hp.isPrimePow, fun hmem => ?_⟩
  have := Finset.le_sup (f := id) hmem
  simp only [id] at this
  omega

/-- The smallest prime power the bits of `S` do not check. -/
noncomputable def leastMissingPrimePow (S : Finset ℕ) : ℕ :=
  Nat.find (exists_primePow_notMem S)

theorem leastMissingPrimePow_spec (S : Finset ℕ) :
    IsPrimePow (leastMissingPrimePow S) ∧ leastMissingPrimePow S ∉ S :=
  Nat.find_spec (exists_primePow_notMem S)

theorem leastMissingPrimePow_le {S : Finset ℕ} {m : ℕ} (hm : IsPrimePow m) (hmS : m ∉ S) :
    leastMissingPrimePow S ≤ m :=
  Nat.find_le ⟨hm, hmS⟩

/-! ### 2. The bit reading -/

/-- The reading of the membership bits of a finite set of nodes. -/
def bitsReading (S : Finset ℕ) (𝒩 : Set ℕ) : {m : ℕ // m ∈ S} → Prop := fun m => (m.1 ∈ 𝒩)

/-- Deleting an unchecked node leaves every bit unchanged. -/
theorem bitsReading_deleteNode {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) (𝒩 : Set ℕ) :
    bitsReading S (deleteNode q 𝒩) = bitsReading S 𝒩 := by
  funext m
  have hne : m.1 ≠ q := fun h => hq (h ▸ m.2)
  simp only [bitsReading, deleteNode, Set.mem_sdiff, Set.mem_singleton_iff]
  exact propext ⟨fun h => h.1, fun h => ⟨h, hne⟩⟩

/-- The node scale after deleting one prime power from the prime powers. -/
theorem nodeScale_deleteNode {q : ℕ} (hq : IsPrimePow q) :
    nodeScale (deleteNode q {n : ℕ | IsPrimePow n}) = ((q : ℝ))⁻¹ := by
  have hset : missingPrimePowers (deleteNode q {n : ℕ | IsPrimePow n}) = {q} := by
    ext m
    simp only [missingPrimePowers, deleteNode, mem_setOf_eq, Set.mem_sdiff,
      Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨by subst h; exact hq, fun _ => h⟩⟩
  unfold nodeScale
  rw [hset, Set.image_singleton, csSup_singleton]

/-! ### 3. The exact limit -/

/-- **The exact limit of a finite bit reading.** -/
theorem resolutionLimit_nodeScale_bitsReading (S : Finset ℕ) :
    resolutionLimit nodeScale (bitsReading S) {n : ℕ | IsPrimePow n} =
      ((leastMissingPrimePow S : ℝ))⁻¹ := by
  obtain ⟨hq, hqS⟩ := leastMissingPrimePow_spec S
  have hq2 : (2 : ℝ) ≤ (leastMissingPrimePow S : ℝ) := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < (leastMissingPrimePow S : ℝ) := by linarith
  have hub : ∀ 𝒩 ∈ shadow (bitsReading S) {n : ℕ | IsPrimePow n},
      nodeScale 𝒩 ≤ ((leastMissingPrimePow S : ℝ))⁻¹ := by
    intro 𝒩 h𝒩
    refine Real.sSup_le ?_ (by positivity)
    rintro y ⟨m, ⟨hm, hmem⟩, rfl⟩
    have hmS : m ∉ S := by
      intro hmemS
      have hbit : (m ∈ 𝒩) = (m ∈ {n : ℕ | IsPrimePow n}) :=
        congrFun (mem_shadow_iff.mp h𝒩) ⟨m, hmemS⟩
      have hin : m ∈ 𝒩 := by rw [hbit]; exact hm
      exact hmem hin
    have hle : leastMissingPrimePow S ≤ m := leastMissingPrimePow_le hm hmS
    have hle' : (leastMissingPrimePow S : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hq0 hle'
    exact (inv_le_inv₀ hm0 hq0).mpr hle'
  have hbdd : BddAbove (nodeScale '' shadow (bitsReading S) {n : ℕ | IsPrimePow n}) :=
    ⟨((leastMissingPrimePow S : ℝ))⁻¹, by rintro x ⟨𝒩, h𝒩, rfl⟩; exact hub 𝒩 h𝒩⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty nodeScale (bitsReading S) _) ?_) ?_
  · rintro x ⟨𝒩, h𝒩, rfl⟩
    exact hub 𝒩 h𝒩
  · have hmem : deleteNode (leastMissingPrimePow S) {n : ℕ | IsPrimePow n} ∈
        shadow (bitsReading S) {n : ℕ | IsPrimePow n} := bitsReading_deleteNode hqS _
    have hle := le_csSup hbdd ⟨_, hmem, rfl⟩
    rwa [nodeScale_deleteNode hq] at hle

/-! ### 4. The finite-bit ladder converges -/

/-- **The finite-bit ladder is a progress measure.** Checking more nodes raises the smallest
unchecked prime power and lowers the limit; every tolerance is reached by a finite set of bits. -/
theorem bitsLadderConverges {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ,
      resolutionLimit nodeScale (bitsReading S) {n : ℕ | IsPrimePow n} < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨Finset.range (N + 1), ?_⟩
  rw [resolutionLimit_nodeScale_bitsReading]
  obtain ⟨hq, hqS⟩ := leastMissingPrimePow_spec (Finset.range (N + 1))
  have hgt : N < leastMissingPrimePow (Finset.range (N + 1)) := by
    by_contra hcon
    exact hqS (Finset.mem_range.mpr (by omega))
  have hgt' : (N : ℝ) < (leastMissingPrimePow (Finset.range (N + 1)) : ℝ) := by
    exact_mod_cast hgt
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hq0 : (0 : ℝ) < (leastMissingPrimePow (Finset.range (N + 1)) : ℝ) := by linarith
  rw [inv_eq_one_div, div_lt_iff₀ hq0]
  rw [div_lt_iff₀ hε] at hN
  nlinarith [hgt', hN, mul_lt_mul_of_pos_right hgt' hε]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
