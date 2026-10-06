import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeIntegral
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimePairs

/-!
# Both orientations of the actual prime-gap integrals

Finite reindexing by the lower prime retains every pair and cutoff endpoint.
The harmonic pair sieve then bounds the complete small-gap integral mass.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology MeasureTheory

private theorem abs_natCast_sub {p r : ℕ} (h : r ≤ p) :
    |(p : ℝ) - r| = ((p - r : ℕ) : ℝ) := by
  rw [Nat.cast_sub h, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h))]

private theorem positive_gap_sum (P : Finset ℕ) (D : ℕ) (f : ℝ → ℝ) :
    (∑ pr ∈ (P.product P).filter
      (fun pr => pr.2 < pr.1 ∧ |(pr.1 : ℝ) - pr.2| ≤ D), f |(pr.1 : ℝ) - pr.2|) =
      ∑ d ∈ Finset.Icc 1 D, (((P.filter (fun r => r + d ∈ P)).card : ℕ) : ℝ) * f d := by
  classical
  let T := ((Finset.Icc 1 D).product P).filter (fun dr => dr.2 + dr.1 ∈ P)
  have hbij : (∑ pr ∈ (P.product P).filter
      (fun pr => pr.2 < pr.1 ∧ |(pr.1 : ℝ) - pr.2| ≤ D), f |(pr.1 : ℝ) - pr.2|) =
      ∑ dr ∈ T, f dr.1 := by
    apply Finset.sum_bij (fun pr _ => (pr.1 - pr.2, pr.2))
    · rintro ⟨p, r⟩ hpr
      obtain ⟨hmem, hlt, hD⟩ := Finset.mem_filter.1 hpr
      obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
      change r < p at hlt
      change |(p : ℝ) - r| ≤ D at hD
      rw [abs_natCast_sub hlt.le] at hD
      have hcut : p - r ≤ D := by exact_mod_cast hD
      have hrecover : r + (p - r) = p := by omega
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_Icc.2 ⟨by omega, hcut⟩, hr⟩, by simpa only [hrecover] using hp⟩
    · rintro ⟨p, r⟩ hpr ⟨q, s⟩ hqs heq
      have hp : r < p := (Finset.mem_filter.1 hpr).2.1
      have hq : s < q := (Finset.mem_filter.1 hqs).2.1
      simp only [Prod.mk.injEq] at heq
      apply Prod.ext <;> dsimp <;> omega
    · rintro ⟨d, r⟩ hdr
      obtain ⟨hmem, hp⟩ := Finset.mem_filter.1 hdr
      obtain ⟨hd, hr⟩ := Finset.mem_product.1 hmem
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.1 hd
      refine ⟨(r + d, r), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp, hr⟩, ?_, ?_⟩, ?_⟩
      · dsimp
        omega
      · change |((r + d : ℕ) : ℝ) - r| ≤ D
        simp only [Nat.cast_add, add_sub_cancel_left,
          abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d)]
        exact_mod_cast hdD
      · simp
    · rintro ⟨p, r⟩ hpr
      exact congrArg f (abs_natCast_sub (Finset.mem_filter.1 hpr).2.1.le)
  rw [hbij]
  dsimp [T]
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- All original prime pairs with a nonzero gap at most the given cutoff. -/
def chiCubicPrimeGapPairs (N : ℝ) (D : ℕ) : Finset (ℕ × ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter
    (fun pr => pr.1 ≠ pr.2 ∧ |(pr.1 : ℝ) - pr.2| ≤ D)

/-- Exact two-orientation reindexing of every real-valued weight of the actual
prime gap. No positivity assumption or endpoint omission is needed. -/
theorem chiCubicPrimeGapPairs_sum (N : ℝ) (D : ℕ) (f : ℝ → ℝ) :
    (∑ pr ∈ chiCubicPrimeGapPairs N D, f |(pr.1 : ℝ) - pr.2|) =
      2 * ∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * f d := by
  classical
  let P := primeProfileBand N
  let g := fun p r : ℕ => if r < p ∧ |(p : ℝ) - r| ≤ D then f |(p : ℝ) - r| else 0
  have hsplit (p r : ℕ) : (if p ≠ r ∧ |(p : ℝ) - r| ≤ D then f |(p : ℝ) - r| else 0) =
      g p r + g r p := by
    dsimp [g]
    rcases lt_trichotomy p r with h | h | h
    · simp [h, show ¬r < p by omega, ne_of_lt h, abs_sub_comm]
    · subst p
      simp
    · simp [h, show ¬p < r by omega, ne_of_gt h, abs_sub_comm]
  have hpos : (∑ p ∈ P, ∑ r ∈ P, g p r) =
      ∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * f d := by
    simpa only [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product,
      chiCubicPrimeGapCount, g, P] using positive_gap_sum P D f
  have hswap : (∑ p ∈ P, ∑ r ∈ P, g r p) = ∑ p ∈ P, ∑ r ∈ P, g p r := Finset.sum_comm
  unfold chiCubicPrimeGapPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  simp only [hsplit, Finset.sum_add_distrib]
  change (∑ p ∈ P, ∑ r ∈ P, g p r) + (∑ p ∈ P, ∑ r ∈ P, g r p) = _
  rw [hswap]
  simp only [hpos]
  ring

/-- Complete sum of norms of the actual small-gap support integrals. -/
def chiCubicHyperbolicPrimeSmallGapMass (N : ℝ) (M D : ℕ) : ℝ :=
  ∑ pr ∈ chiCubicPrimeGapPairs N D, ‖chiCubicHyperbolicPrimePairIntegral N M pr‖

/-- The actual small-gap integral mass has the required logarithmic bound,
uniformly for every gap cutoff. -/
theorem exists_chiCubicHyperbolicPrimeSmallGapMass_bound (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ D : ℕ,
      chiCubicHyperbolicPrimeSmallGapMass N M D ≤
        C * N / Real.log N ^ 3 * (1 + Real.log D) := by
  obtain ⟨A, hA, hpre⟩ := exists_chiCubicPrimeGapCount_harmonic_bound
  refine ⟨16 * Real.pi * ((M : ℝ) + 1) * A, by positivity, ?_⟩
  filter_upwards [hpre, eventually_gt_atTop (1 : ℝ)] with N hpreN hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  intro D
  have hH : 0 ≤ 1 + Real.log D :=
    (Finset.sum_nonneg (fun d _ => by positivity : ∀ d ∈ Finset.Icc 1 D, (0 : ℝ) ≤ 1 / d)).trans
      (Sieve.sum_Icc_one_div_le_one_add_log D)
  have hmass : chiCubicHyperbolicPrimeSmallGapMass N M D ≤
      (16 * Real.pi * M / Real.log N) *
        (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ)) := by
    calc
      _ ≤ ∑ pr ∈ chiCubicPrimeGapPairs N D,
          8 * Real.pi * M / (|(pr.1 : ℝ) - pr.2| * Real.log N) := by
        apply Finset.sum_le_sum
        intro pr hpr
        obtain ⟨hmem, hne, _⟩ := Finset.mem_filter.1 hpr
        obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
        exact norm_chiCubicHyperbolicPrimePairIntegral_le hN M hp hr hne
      _ = (8 * Real.pi * M / Real.log N) *
          (∑ pr ∈ chiCubicPrimeGapPairs N D, 1 / |(pr.1 : ℝ) - pr.2|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pr _
        ring
      _ = _ := by
        rw [chiCubicPrimeGapPairs_sum]
        simp only [mul_one_div]
        ring
  calc
    _ ≤ (16 * Real.pi * M / Real.log N) *
        (A * N / Real.log N ^ 2 * (1 + Real.log D)) :=
      hmass.trans (mul_le_mul_of_nonneg_left (hpreN D) (by positivity))
    _ ≤ (16 * Real.pi * ((M : ℝ) + 1) / Real.log N) *
        (A * N / Real.log N ^ 2 * (1 + Real.log D)) := by gcongr; linarith
    _ = _ := by ring

end RHTower
