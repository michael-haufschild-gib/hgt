import GaloisForLFunctions.RHTower.Sieve.MarkerScaleTransfer

/-!
# The second moment of a fibre multiplicity

If a finite set `S` of integers is mapped to starts by `f`, and two elements of `S` sharing a start
differ by at most `K`, then the second moment of the fibre sizes is the first moment plus twice a
sum of shifted-pair counts.  This is the input the Cauchy--Schwarz transfer of
`Sieve/MarkerScaleTransfer` needs, and for marker primes the shifted-pair counts are exactly what
the two-dimensional sieve of `Sieve/PrimePairAverage` bounds.
-/

namespace RHTower.Sieve

open Finset

/-- The two off-diagonal halves of a fibre agree in total. -/
theorem sum_card_lower_eq_sum_card_upper {S : Finset ℕ} (f : ℕ → ℕ) :
    ∑ p ∈ S, (S.filter (fun q => f q = f p ∧ p < q)).card
      = ∑ p ∈ S, (S.filter (fun q => f q = f p ∧ q < p)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  refine if_congr ?_ rfl rfl
  exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- Each fibre's upper half injects into the admissible shifts. -/
theorem card_upper_le_card_shifts {S : Finset ℕ} (f : ℕ → ℕ) (K : ℕ)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p < q → f q = f p → q ≤ p + K) {p : ℕ} (hp : p ∈ S) :
    (S.filter (fun q => f q = f p ∧ p < q)).card
      ≤ ((Finset.Icc 1 K).filter (fun d => p + d ∈ S)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun q => q - p) ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hqS, hfq, hpq⟩ := hq
    have hle := hsep p hp q hqS hpq hfq
    have hpq' : p + (q - p) = q := by omega
    show (q - p) ∈ ↑((Finset.Icc 1 K).filter (fun d => p + d ∈ S))
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by rw [hpq']; exact hqS⟩
  · intro q hq q' hq' he
    rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
    have h1 : p < q := hq.2.2
    have h2 : p < q' := hq'.2.2
    simp only at he
    omega

/-- **The second moment of the fibre sizes.** -/
theorem sum_sq_fibreCard_le {S : Finset ℕ} (f : ℕ → ℕ) (K : ℕ)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p < q → f q = f p → q ≤ p + K) :
    ∑ t ∈ S.image f, ((S.filter (fun p => f p = t)).card) ^ (2 : ℕ)
      ≤ S.card + 2 * ∑ d ∈ Finset.Icc 1 K, (S.filter (fun p => p + d ∈ S)).card := by
  classical
  set c : ℕ → ℕ := fun t => (S.filter (fun p => f p = t)).card with hc
  have hfib : ∑ t ∈ S.image f, (c t) ^ (2 : ℕ) = ∑ p ∈ S, c (f p) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := f)
      (fun p hp => Finset.mem_image_of_mem f hp) (fun p => c (f p))]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hconst : ∀ p ∈ S.filter (fun p => f p = t), c (f p) = c t := by
      intro p hp
      rw [(Finset.mem_filter.1 hp).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, hc]
    ring
  rw [hfib]
  set A : ℕ → ℕ := fun p => (S.filter (fun q => f q = f p ∧ p < q)).card with hA
  set B : ℕ → ℕ := fun p => (S.filter (fun q => f q = f p ∧ q < p)).card with hB
  have hsplit : ∀ p ∈ S, c (f p) ≤ 1 + A p + B p := by
    intro p hp
    have hsub : S.filter (fun q => f q = f p)
        ⊆ (({p} : Finset ℕ) ∪ (S.filter (fun q => f q = f p ∧ p < q)))
            ∪ (S.filter (fun q => f q = f p ∧ q < p)) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rcases lt_trichotomy q p with hlt | heq | hgt
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hq.1, hq.2, hlt⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton.2 heq))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hq.1, hq.2, hgt⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      (({p} : Finset ℕ) ∪ (S.filter (fun q => f q = f p ∧ p < q)))
      (S.filter (fun q => f q = f p ∧ q < p))
    have h3 := Finset.card_union_le ({p} : Finset ℕ) (S.filter (fun q => f q = f p ∧ p < q))
    simp only [Finset.card_singleton] at h3
    rw [show c (f p) = (S.filter (fun q => f q = f p)).card from rfl,
      show A p = (S.filter (fun q => f q = f p ∧ p < q)).card from rfl,
      show B p = (S.filter (fun q => f q = f p ∧ q < p)).card from rfl]
    omega
  have hsum1 : ∑ p ∈ S, c (f p) ≤ ∑ p ∈ S, (1 + A p + B p) := Finset.sum_le_sum hsplit
  have hAB : ∑ p ∈ S, A p = ∑ p ∈ S, B p := sum_card_lower_eq_sum_card_upper f
  have hshift : ∑ p ∈ S, A p
      ≤ ∑ p ∈ S, ((Finset.Icc 1 K).filter (fun d => p + d ∈ S)).card :=
    Finset.sum_le_sum fun p hp => card_upper_le_card_shifts f K hsep hp
  have hswap : ∑ p ∈ S, ((Finset.Icc 1 K).filter (fun d => p + d ∈ S)).card
      = ∑ d ∈ Finset.Icc 1 K, (S.filter (fun p => p + d ∈ S)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hexp : ∑ p ∈ S, (1 + A p + B p) = S.card + ∑ p ∈ S, A p + ∑ p ∈ S, B p := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  calc ∑ p ∈ S, c (f p) ≤ ∑ p ∈ S, (1 + A p + B p) := hsum1
    _ = S.card + ∑ p ∈ S, A p + ∑ p ∈ S, B p := hexp
    _ = S.card + 2 * ∑ p ∈ S, A p := by rw [← hAB]; ring
    _ ≤ S.card + 2 * ∑ p ∈ S, ((Finset.Icc 1 K).filter (fun d => p + d ∈ S)).card := by
        gcongr
    _ = S.card + 2 * ∑ d ∈ Finset.Icc 1 K, (S.filter (fun p => p + d ∈ S)).card := by
        rw [hswap]

end RHTower.Sieve
