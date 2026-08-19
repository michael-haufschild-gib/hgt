import GaloisForLFunctions.RHTower.Sieve.FibreMultiplicitySecondMoment

/-!
# Markers over an exceptional set of starts

The device in one statement: a set of markers whose starts avoid an exceptional set of density `ρ`
loses only a `√ρ` fraction, provided the per-start marker multiplicity has bounded second moment.
The multiplicity's second moment is the marker count plus twice a shifted-pair count
(`Sieve/FibreMultiplicitySecondMoment`), and for marker primes the latter is what the
two-dimensional sieve bounds.

Against the trivial estimate — every marker over a bad start is lost, so the loss is
`(density of bad starts) × (maximal multiplicity)` — this replaces the *maximal* multiplicity by the
*mean square*, which is exactly the gain that removes the factor `log x` from the marker join of the
route-E Hall law.
-/

namespace RHTower.Sieve

open Finset

/-- **Markers over an exceptional set of starts.** -/
theorem sq_card_marker_bad_le {S B : Finset ℕ} (f : ℕ → ℕ) (K : ℕ)
    (hB : B ⊆ S.image f)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p < q → f q = f p → q ≤ p + K) {Pi : ℝ}
    (hpair : ∑ d ∈ Finset.Icc 1 K, (((S.filter (fun p => p + d ∈ S)).card : ℕ) : ℝ) ≤ Pi) :
    ((((S.filter (fun p => f p ∈ B)).card : ℕ) : ℝ)) ^ 2
      ≤ (B.card : ℝ) * ((S.card : ℝ) + 2 * Pi) := by
  classical
  set c : ℕ → ℕ := fun t => (S.filter (fun p => f p = t)).card with hc
  -- the markers over `B` are the union of the fibres over `B`
  have hcount : (S.filter (fun p => f p ∈ B)).card = ∑ t ∈ B, c t := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := f) (s := S.filter (fun p => f p ∈ B)) (t := B)
      (fun p hp => (Finset.mem_filter.1 hp).2)]
    refine Finset.sum_congr rfl fun t ht => ?_
    congr 1
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, -⟩, hft⟩
      exact ⟨hpS, hft⟩
    · rintro ⟨hpS, hft⟩
      exact ⟨⟨hpS, hft ▸ ht⟩, hft⟩
  -- Cauchy–Schwarz against the second moment
  have hcs := sq_sum_subset_le_card_mul_sumSq (S := S.image f) (B := B) hB
    (fun t => ((c t : ℕ) : ℝ))
  have hsm : ∑ t ∈ S.image f, (((c t : ℕ) : ℝ)) ^ 2
      ≤ (S.card : ℝ) + 2 * Pi := by
    have hnat := sum_sq_fibreCard_le (S := S) f K hsep
    have hcast : ((∑ t ∈ S.image f, (c t) ^ 2 : ℕ) : ℝ)
        = ∑ t ∈ S.image f, (((c t : ℕ) : ℝ)) ^ 2 := by push_cast; ring
    have hmono : ((∑ t ∈ S.image f, (c t) ^ 2 : ℕ) : ℝ)
        ≤ ((S.card + 2 * ∑ d ∈ Finset.Icc 1 K, (S.filter (fun p => p + d ∈ S)).card : ℕ) : ℝ) :=
      Nat.cast_le.2 hnat
    rw [hcast] at hmono
    refine hmono.trans ?_
    push_cast
    linarith [hpair]
  have hB0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  calc ((((S.filter (fun p => f p ∈ B)).card : ℕ) : ℝ)) ^ 2
      = (∑ t ∈ B, ((c t : ℕ) : ℝ)) ^ 2 := by rw [hcount]; push_cast; ring
    _ ≤ (B.card : ℝ) * ∑ t ∈ S.image f, (((c t : ℕ) : ℝ)) ^ 2 := hcs
    _ ≤ (B.card : ℝ) * ((S.card : ℝ) + 2 * Pi) := mul_le_mul_of_nonneg_left hsm hB0

end RHTower.Sieve
