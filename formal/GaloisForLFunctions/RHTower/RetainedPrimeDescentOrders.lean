import GaloisForLFunctions.RHTower.RetainedPrimeStateTransport
import GaloisForLFunctions.RHTower.PartialSubsetEnergyOrder
import GaloisForLFunctions.RHTower.MobiusDivisorSignedPrimeBatches

/-!
# Finite retained-field prime descent and pool orders

Every finite retained source field has nontrivial integer witnesses with a
common clipping margin. Any actual prime family copying those witnesses
admits an energy-decreasing choice. Repeated choices consume any common
finite pool capacity in a distinct order below the starting energy. The
entire preparation of a finite core has an explicit cardinality-dependent
quadratic bound; no uniform bound over growing cores is asserted.
-/

noncomputable section
open Finset
namespace RHTower

/-- The literal source has no mass at cutoffs zero and one. -/
lemma retainedPrimeFieldPairing_eq_zero_of_le_one (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) {M : ℕ} (hM : M ≤ 1) :
    retainedPrimeFieldPairing Q z M = 0 := by
  interval_cases M <;> simp [retainedPrimeFieldPairing, mobiusDivisorDilationChannel]

/-- Finite clipping-stable witnesses can all be chosen at nontrivial child cutoffs. -/
theorem exists_retainedPrimeField_nontrivial_clip_margin (Q : Finset Nat.Primes) :
    ∃ K : Finset ℕ, K.Nonempty ∧ (∀ k ∈ K, 2 ≤ k) ∧ ∃ c δ : ℝ,
      0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ clip : ℕ → ℝ, (∀ k ∈ K, 0 ≤ clip k ∧ clip k ≤ δ) →
      ∀ z : retainedPrimeFieldCoordinates Q, ∃ k ∈ K,
        c * ‖z‖ ≤ (1-clip k) * retainedPrimeFieldPairing Q z k +
          clip k * retainedPrimeFieldPairing Q z (k+1) := by
  obtain ⟨K, hK, c, δ, hc, hδ, hδ1, hmargin⟩ := exists_retainedPrimeField_finite_clip_margin Q
  let J := K.filter (fun k => 2 ≤ k)
  have hnonzero (clip : ℕ → ℝ) (hclip : ∀ k ∈ J, 0 ≤ clip k ∧ clip k ≤ δ)
      (z : retainedPrimeFieldCoordinates Q) (hz : z ≠ 0) :
      ∃ k ∈ J, c * ‖z‖ ≤ (1-clip k) * retainedPrimeFieldPairing Q z k +
        clip k * retainedPrimeFieldPairing Q z (k+1) := by
    let clip' := fun k => if 2 ≤ k then clip k else 0
    have hclip' : ∀ k ∈ K, 0 ≤ clip' k ∧ clip' k ≤ δ := by
      intro k hk
      by_cases h : 2 ≤ k
      · simpa [clip', h] using hclip k (mem_filter.mpr ⟨hk, h⟩)
      · simp [clip', h, hδ.le]
    obtain ⟨k, hk, hm⟩ := hmargin clip' hclip' z
    have hk2 : 2 ≤ k := by
      by_contra hn
      have hz0 := retainedPrimeFieldPairing_eq_zero_of_le_one Q z (by omega : k ≤ 1)
      have hp : 0 < c * ‖z‖ := mul_pos hc (norm_pos_iff.mpr hz)
      simp [clip', hn, hz0] at hm
      linarith
    exact ⟨k, mem_filter.mpr ⟨hk, hk2⟩, by simpa [clip', hk2] using hm⟩
  have hJ : J.Nonempty := by
    have h1 : (1 : retainedPrimeFieldCoordinates Q) ≠ 0 := by
      intro he
      have h := congrFun he ⟨∅, by simp⟩
      norm_num at h
    obtain ⟨k, hk, _⟩ := hnonzero (fun _ => 0) (by simp [hδ.le]) 1 h1
    exact ⟨k, hk⟩
  refine ⟨J, hJ, fun k hk => (mem_filter.mp hk).2, c, δ, hc, hδ, hδ1, ?_⟩
  intro clip hclip z
  by_cases hz : z = 0
  · obtain ⟨k, hk⟩ := hJ
    refine ⟨k, hk, ?_⟩
    simp [hz, retainedPrimeFieldPairing]
  · exact hnonzero clip hclip z hz

/-- An available copied witness yields a quantitatively nonincreasing actual prime step.
No energy of omitted coordinates or removed prime packets is discarded. -/
theorem exists_retainedPrimeField_prime_descent (Q : Finset Nat.Primes) :
    ∃ K : Finset ℕ, K.Nonempty ∧ (∀ k ∈ K, 2 ≤ k) ∧ ∃ c δ : ℝ,
      0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (M : ℕ) (P : Finset ℕ) (prime : ℕ → ℕ),
      Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ mobiusDivisorSelectionPrimes M →
      Disjoint P (Q.image (fun q : Nat.Primes => (q : ℕ))) →
      (∀ k ∈ K, mobiusDivisorSelectionPrimes (k+1) \ Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ P) →
      (∀ k ∈ K, (prime k).Prime ∧ prime k < M ∧ prime k ∉ P ∧
        prime k ∉ Q.image (fun q : Nat.Primes => (q : ℕ)) ∧
        M / prime k = k ∧ divisorPrimeClipWeight M (prime k) ≤ δ) →
      ∃ k ∈ K, mobiusDivisorSelectionEnergy M (insert (prime k) P) -
          mobiusDivisorSelectionEnergy M P ≤
        -2 * Real.sqrt (prime k) * (c * ‖retainedPrimeParentField Q M P‖) := by
  obtain ⟨K, hK, hK2, c, δ, hc, hδ, hδ1, hmargin⟩ :=
    exists_retainedPrimeField_nontrivial_clip_margin Q
  refine ⟨K, hK, hK2, c, δ, hc, hδ, hδ1, ?_⟩
  intro M P prime hQM hdis hcore hprime
  obtain ⟨k, hk, hm⟩ := hmargin (fun k => divisorPrimeClipWeight M (prime k))
    (fun k hk => ⟨divisorPrimeClipWeight_nonneg M (prime k) (hprime k hk).1.pos,
      (hprime k hk).2.2.2.2.2⟩) (retainedPrimeParentField Q M P)
  obtain ⟨hp, hpM, hpP, hpQ, hquot, hclip⟩ := hprime k hk
  refine ⟨k, hk, ?_⟩
  rw [mobiusDivisorSelectionEnergy_insert_retainedProfile Q M P hp hpM hpP hpQ hQM
    (by simpa only [hquot] using hcore k hk) hdis,
    retainedPrimeClippedProfile_pairing, hquot]
  exact mul_le_mul_of_nonpos_left hm (by have := Real.sqrt_nonneg (prime k : ℝ); linarith)

/-- Every finite retained field admits source-defined witness pools such that
any available capacity can be consumed in a distinct energy-controlled order. -/
theorem exists_retainedPrimeField_pool_orders (Q : Finset Nat.Primes) :
    ∃ K : Finset ℕ, K.Nonempty ∧ (∀ k ∈ K, 2 ≤ k) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (M : ℕ) (P : Finset ℕ) (pool : ℕ → Finset ℕ) (n : ℕ),
      Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ mobiusDivisorSelectionPrimes M →
      Disjoint P (Q.image (fun q : Nat.Primes => (q : ℕ))) →
      (∀ k ∈ K, mobiusDivisorSelectionPrimes (k+1) \ Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ P) →
      (∀ k ∈ K, n ≤ (pool k).card) →
      (∀ k ∈ K, ∀ p ∈ pool k, p.Prime ∧ p < M ∧ p ∉ P ∧
        p ∉ Q.image (fun q : Nat.Primes => (q : ℕ)) ∧
        M/p = k ∧ divisorPrimeClipWeight M p ≤ δ) →
      ∃ l : List ℕ, l.Nodup ∧ l.length = n ∧ l.toFinset ⊆ K.biUnion pool ∧
        ∀ j : ℕ, mobiusDivisorSelectionEnergy M (P ∪ (l.take j).toFinset) ≤
          mobiusDivisorSelectionEnergy M P := by
  obtain ⟨K, hK, hK2, c, δ, hc, hδ, hδ1, hdescent⟩ := exists_retainedPrimeField_prime_descent Q
  refine ⟨K, hK, hK2, δ, hδ, hδ1, ?_⟩
  intro M P pool n hQM hdis hcore hcard hpool
  let U := K.biUnion pool
  have hU (p : ℕ) (hp : p ∈ U) : p ∉ Q.image (fun q : Nat.Primes => (q : ℕ)) := by
    obtain ⟨k, hk, hp⟩ := mem_biUnion.mp hp
    exact (hpool k hk p hp).2.2.2.1
  obtain ⟨l, hnd, hlen, hsub, hbound⟩ := exists_partialSubsetEnergyOrder
    (fun L => mobiusDivisorSelectionEnergy M (P ∪ L)) U n (by
      intro L hLU hLn
      have hex (k : ℕ) : ∃ p : ℕ, k ∈ K → p ∈ pool k ∧ p ∉ L := by
        by_cases hk : k ∈ K
        · have hex' : ∃ p ∈ pool k, p ∉ L := by
            by_contra hn
            push Not at hn
            have hle := card_le_card hn
            have := hcard k hk
            omega
          obtain ⟨p, hp, hpL⟩ := hex'
          exact ⟨p, fun _ => ⟨hp, hpL⟩⟩
        · exact ⟨0, fun h => False.elim (hk h)⟩
      choose prime hprime using hex
      have hdis' : Disjoint (P ∪ L) (Q.image (fun q : Nat.Primes => (q : ℕ))) := by
        apply disjoint_left.mpr
        intro p hp hpQ
        rcases mem_union.mp hp with hp | hp
        · exact disjoint_left.mp hdis hp hpQ
        · exact hU p (hLU hp) hpQ
      have hdata (k : ℕ) (hk : k ∈ K) :
          (prime k).Prime ∧ prime k < M ∧ prime k ∉ P ∪ L ∧
          prime k ∉ Q.image (fun q : Nat.Primes => (q : ℕ)) ∧
          M / prime k = k ∧ divisorPrimeClipWeight M (prime k) ≤ δ := by
        obtain ⟨hp, hpM, hpP, hpQ, hquot, hclip⟩ := hpool k hk (prime k) (hprime k hk).1
        exact ⟨hp, hpM, by simp [hpP, (hprime k hk).2], hpQ, hquot, hclip⟩
      obtain ⟨k, hk, he⟩ := hdescent M (P ∪ L) prime hQM hdis'
        (fun k hk => (hcore k hk).trans subset_union_left) hdata
      have hn : -2 * Real.sqrt (prime k) * (c * ‖retainedPrimeParentField Q M (P ∪ L)‖) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by have := Real.sqrt_nonneg (prime k : ℝ); linarith)
          (mul_nonneg hc.le (norm_nonneg _))
      refine ⟨prime k, mem_biUnion.mpr ⟨k, hk, (hprime k hk).1⟩, (hprime k hk).2, ?_⟩
      rw [union_insert]
      linarith only [he, hn])
  exact ⟨l, hnd, hlen, hsub, by simpa only [union_empty] using hbound⟩

/-- The complete preparation history of a finite core has an explicit quadratic budget. -/
theorem mobiusDivisorSelectionEnergy_subcore_le (M : ℕ) (P T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p < M) (hT : T ⊆ P) :
    mobiusDivisorSelectionEnergy M T ≤ (2:ℝ)^P.card * 722 * (M:ℝ)^2 := by
  have he := mobiusDivisorSelectionEnergy_le_pow_card M T (fun p hp => hP p (hT hp))
  rw [mobiusDivisorSelectionEnergy_empty] at he
  have hd := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
  have hpow : (2:ℝ)^T.card ≤ 2^P.card := by
    gcongr
    norm_num
  calc
    _ ≤ 2^T.card * (722 * (M:ℝ)^2) := he.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    _ ≤ 2^P.card * (722 * (M:ℝ)^2) := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by ring

end RHTower
