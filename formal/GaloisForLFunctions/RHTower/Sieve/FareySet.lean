import GaloisForLFunctions.RHTower.Sieve.LargeSieveExpSum

/-!
# The Farey set of order `Q` and the textbook large sieve

The large sieve of `LargeSieveExpSum.lean` is stated over an arbitrary set of reduced fractions.
Its canonical instance is the Farey set of order `Q`, and organising that set by denominator turns
the single sum into the familiar double sum:

`∑_{q ≤ Q} ∑_{1 ≤ a ≤ q, (a,q) = 1} |S(a/q)|² ≤ (N + Q²(1 + log(Q²/2 + 1))) ∑_n |c_n|²`.

The regrouping is a disjoint union over denominators; the fibres are disjoint because the second
coordinate determines the denominator.
-/

namespace RHTower.Sieve

open Finset

/-- The Farey set of order `Q`: reduced fractions `a/q` with `1 ≤ a ≤ q ≤ Q`. -/
def fareySet (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q ×ˢ Finset.Icc 1 Q).filter (fun p => p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2)

theorem mem_fareySet {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ fareySet Q ↔
      (1 ≤ p.1 ∧ p.1 ≤ Q) ∧ (1 ≤ p.2 ∧ p.2 ≤ Q) ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2 := by
  simp only [fareySet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- **The large sieve on the Farey set of order `Q`.** -/
theorem largeSieve_expSum_fareySet (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ p ∈ fareySet Q, ‖expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1)))
          * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  refine largeSieve_expSum_farey N hQ _ (fun p hp => ?_) c
  obtain ⟨⟨ha1, _⟩, ⟨hq1, hqQ⟩, hle, hcop⟩ := mem_fareySet.mp hp
  exact ⟨hq1, hqQ, ha1, hle, hcop⟩

/-- The Farey set fibred over its denominators. -/
theorem fareySet_eq_biUnion (Q : ℕ) :
    fareySet Q = (Finset.Icc 1 Q).biUnion
      (fun q => ((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q))) := by
  ext p
  simp only [mem_fareySet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha1, _⟩, ⟨hq1, hqQ⟩, hle, hcop⟩
    exact ⟨p.2, ⟨hq1, hqQ⟩, p.1, ⟨⟨ha1, hle⟩, hcop⟩, rfl⟩
  · rintro ⟨q, ⟨hq1, hqQ⟩, a, ⟨⟨ha1, haq⟩, hcop⟩, rfl⟩
    exact ⟨⟨ha1, le_trans haq hqQ⟩, ⟨hq1, hqQ⟩, haq, hcop⟩

/-- **The large sieve in textbook form.** -/
theorem largeSieve_expSum_double (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖expSum N c ((a : ℝ) / (q : ℝ))‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1)))
          * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  classical
  have hdisj : (↑(Finset.Icc 1 Q) : Set ℕ).PairwiseDisjoint
      (fun q => ((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).image
        (fun a => (a, q))) := by
    intro q _ q' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro p hp hp'
    rw [Finset.mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨a', _, heq⟩ := hp'
    exact hne (congrArg Prod.snd heq).symm
  have hbase := largeSieve_expSum_fareySet N hQ c
  rw [fareySet_eq_biUnion, Finset.sum_biUnion hdisj] at hbase
  have hinner : ∀ q ∈ Finset.Icc 1 Q,
      ∑ p ∈ ((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q)),
          ‖expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ (2 : ℕ)
        = ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
            ‖expSum N c ((a : ℝ) / (q : ℝ))‖ ^ (2 : ℕ) := by
    intro q _
    refine Finset.sum_image ?_
    intro a _ a' _ heq
    exact congrArg Prod.fst heq
  rw [Finset.sum_congr rfl hinner] at hbase
  exact hbase

end RHTower.Sieve
