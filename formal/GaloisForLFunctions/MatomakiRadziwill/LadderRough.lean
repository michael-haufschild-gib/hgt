import GaloisForLFunctions.MatomakiRadziwill.LadderCover

/-!
# The rough set of the ladder

Scales `Pr_0, …, Pr_{J−1}` and the top scale `Pr*` are pairwise disjoint sets of primes.  The rough
set `S` consists of the `X < n ≤ 4X` with a prime factor in every scale (`ladderS`).  For each scale
`j` the condition "a prime factor in every other scale" (`restAt`) is stable under multiplication by
the primes of scale `j` (`restAt_mul_iff`), and `S` is the rough set of scale `j` with that rest
condition (`roughSet_restAt_eq`), so Ramaré's decomposition applies at every scale to the same `S`.
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The scales of a ladder: `J` ladder scales and a top scale, pairwise disjoint sets of primes. -/
structure LadderScales where
  /-- The ladder scales. -/
  scale : ℕ → Finset ℕ
  /-- The top scale. -/
  top : Finset ℕ
  /-- The number of ladder scales. -/
  J : ℕ
  prime_scale : ∀ j p, p ∈ scale j → p.Prime
  prime_top : ∀ p ∈ top, p.Prime
  disjoint_scale : ∀ i j, i ≠ j → Disjoint (scale i) (scale j)
  disjoint_top : ∀ j, Disjoint (scale j) top

namespace LadderScales

variable (L : LadderScales)

/-- `n` has a prime factor in the finite set `Pr`. -/
def hits (Pr : Finset ℕ) (n : ℕ) : Prop := ∃ p ∈ Pr, p ∣ n

instance (Pr : Finset ℕ) (n : ℕ) : Decidable (hits Pr n) := by
  unfold hits; infer_instance

/-- A prime factor in every ladder scale other than `j`, and in the top scale. -/
def restAt (j : ℕ) (n : ℕ) : Prop :=
  (∀ i ∈ range L.J, i ≠ j → hits (L.scale i) n) ∧ hits L.top n

/-- A prime factor in every ladder scale. -/
def restTop (n : ℕ) : Prop := ∀ i ∈ range L.J, hits (L.scale i) n

instance (j n : ℕ) : Decidable (L.restAt j n) := by unfold restAt; infer_instance
instance (n : ℕ) : Decidable (L.restTop n) := by unfold restTop; infer_instance

/-- The rough set: `X < n ≤ 4X` with a prime factor in every scale. -/
def ladderS (X : ℕ) : Finset ℕ :=
  (Ioc X (4 * X)).filter fun n => (∀ i ∈ range L.J, hits (L.scale i) n) ∧ hits L.top n

/-- Multiplying by a prime outside `Pr` does not change whether `Pr` is hit. -/
theorem hits_mul_iff {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpPr : p ∉ Pr) (m : ℕ) : hits Pr (p * m) ↔ hits Pr m := by
  constructor
  · rintro ⟨q, hq, hqd⟩
    refine ⟨q, hq, ?_⟩
    rcases (Nat.Prime.dvd_mul (hPr q hq)).mp hqd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq (hPr q hq) hp).mp h ▸ hq) hpPr
    · exact h
  · rintro ⟨q, hq, hqd⟩
    exact ⟨q, hq, dvd_mul_of_dvd_right hqd p⟩

/-- **The rest condition of scale `j` is stable under its primes.** -/
theorem restAt_mul_iff {j : ℕ} {p : ℕ} (hp : p ∈ L.scale j) (m : ℕ) :
    L.restAt j (p * m) ↔ L.restAt j m := by
  have hpp := L.prime_scale j p hp
  have hnot : ∀ i, i ≠ j → p ∉ L.scale i := fun i hij hpi =>
    Finset.disjoint_left.mp (L.disjoint_scale i j hij) hpi hp
  have hnottop : p ∉ L.top := fun h => Finset.disjoint_left.mp (L.disjoint_top j) hp h
  unfold restAt
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi hij => (hits_mul_iff (L.prime_scale i) hpp (hnot i hij) m).mp (h1 i hi hij),
      (hits_mul_iff L.prime_top hpp hnottop m).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi hij => (hits_mul_iff (L.prime_scale i) hpp (hnot i hij) m).mpr (h1 i hi hij),
      (hits_mul_iff L.prime_top hpp hnottop m).mpr h2⟩

/-- **The top rest condition is stable under the top primes.** -/
theorem restTop_mul_iff {p : ℕ} (hp : p ∈ L.top) (m : ℕ) :
    L.restTop (p * m) ↔ L.restTop m := by
  have hpp := L.prime_top p hp
  have hnot : ∀ i, p ∉ L.scale i := fun i hpi =>
    Finset.disjoint_left.mp (L.disjoint_top i) hpi hp
  unfold restTop
  exact ⟨fun h i hi => (hits_mul_iff (L.prime_scale i) hpp (hnot i) m).mp (h i hi),
    fun h i hi => (hits_mul_iff (L.prime_scale i) hpp (hnot i) m).mpr (h i hi)⟩

theorem one_le_omegaIn_iff (Pr : Finset ℕ) (n : ℕ) : 1 ≤ omegaIn Pr n ↔ hits Pr n := by
  unfold omegaIn hits
  rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨p, hp⟩; rw [mem_filter] at hp; exact ⟨p, hp.1, hp.2⟩
  · rintro ⟨p, hp, hpn⟩; exact ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

/-- **Every ladder scale sees the same rough set.** -/
theorem roughSet_restAt_eq {j : ℕ} (hj : j ∈ range L.J) (X : ℕ) :
    roughSet (L.restAt j) (L.scale j) X = L.ladderS X := by
  ext n
  rw [roughSet, ladderS, mem_filter, mem_filter, one_le_omegaIn_iff]
  unfold restAt
  constructor
  · rintro ⟨hn, ⟨h1, h2⟩, h3⟩
    refine ⟨hn, fun i hi => ?_, h2⟩
    by_cases hij : i = j
    · rw [hij]; exact h3
    · exact h1 i hi hij
  · rintro ⟨hn, h1, h2⟩
    exact ⟨hn, ⟨fun i hi _ => h1 i hi, h2⟩, h1 j hj⟩

/-- **The top scale sees the same rough set.** -/
theorem roughSet_restTop_eq (X : ℕ) : roughSet L.restTop L.top X = L.ladderS X := by
  ext n
  rw [roughSet, ladderS, mem_filter, mem_filter, one_le_omegaIn_iff]
  unfold restTop
  tauto

end LadderScales

end

end GaloisForLFunctions.MatomakiRadziwill
