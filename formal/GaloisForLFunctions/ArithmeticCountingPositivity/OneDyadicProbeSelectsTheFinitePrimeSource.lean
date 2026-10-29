import GaloisForLFunctions.ArithmeticCountingPositivity.InteriorSecularRootsForceStrictPrimeGapDecrease
import GaloisForLFunctions.ArithmeticCountingPositivity.SmallPrimeFlipsLieBelowTheMaximalGap

/-!
# A fixed dyadic probe selects the untwisted finite-prime sign

The maximal gap alone allows nontrivial finite prime flips. Requiring also
the untwisted response to a prime-two flip excludes all of them: the first
bound excludes flipping two already, and strict inclusion decreases the
dyadic response for every remaining nonempty prime set.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Toggle the prime two in a finite prime set. -/
def dyadicPrimeToggle (F : Finset ℕ) : Finset ℕ :=
  if 2 ∈ F then F.erase 2 else insert 2 F

/-- Multiplication by dyadic parity toggles exactly the prime two, at every
integer coordinate. -/
theorem finiteFlip_dyadicPrimeToggle (F : Finset ℕ) (n : ℕ) :
    finiteFlip (dyadicPrimeToggle F) n = finiteFlip {2} n * finiteFlip F n := by
  classical
  by_cases h2 : 2 ∈ F
  · simp only [dyadicPrimeToggle, if_pos h2]
    have he : finiteFlip F n = finiteFlip {2} n * finiteFlip (F.erase 2) n := by
      calc
        _ = finiteFlip (insert 2 (F.erase 2)) n :=
          congrArg (fun G => finiteFlip G n) (insert_erase h2).symm
        _ = _ := by
          have hn : 2 ∉ F.erase 2 := fun h => (mem_erase.mp h).1 rfl
          simp only [finiteFlip, prod_insert hn, prod_singleton]
    rw [he, ← mul_assoc, singleFlip_mul_self, one_mul]
  · simp only [dyadicPrimeToggle, if_neg h2, finiteFlip, prod_insert h2, prod_singleton]

private theorem dyadic_singleton_prime : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by
  intro p hp
  have he : p = 2 := mem_singleton.mp hp
  subst p
  exact Nat.prime_two

/-- Dyadic parity has a greatest gap strictly below the universal ceiling. -/
theorem dyadicFlipGreatestGap_lt_ceiling :
    finiteFlipGreatestGap {2} < 2 * Real.log 2 := by
  by_contra hnot
  have hgap := (finiteFlip_hasHyperplaneGap_iff_le_greatestGap {2}
    dyadic_singleton_prime (2 * Real.log 2)).mpr (le_of_not_gt hnot)
  exact (smallPrimeFlip_has_positive_but_not_maximal_gap Nat.prime_two (by norm_num)).2 hgap

private theorem insert_two_prime {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    ∀ p ∈ insert 2 F, p.Prime := by
  intro p hp
  rcases mem_insert.mp hp with he | hp
  · subst p
    exact Nat.prime_two
  · exact hF p hp

/-- Among finite prime flips, the maximal original gap and the untwisted
dyadic-response gap jointly select the empty flip set. Both conditions are
lower bounds, so no equality of entire spectral data is assumed. -/
theorem finiteFlip_two_gap_selection (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    (HasHyperplaneGap (finiteFlip F) (2 * Real.log 2) ∧
      HasHyperplaneGap (fun n => finiteFlip {2} n * finiteFlip F n)
        (finiteFlipGreatestGap {2})) ↔ F = ∅ := by
  classical
  constructor
  · rintro ⟨hbase, hprobe⟩
    have h2 : 2 ∉ F := by
      intro hmem
      have hsub : ({2} : Finset ℕ) ⊆ F := singleton_subset_iff.mpr hmem
      have hupper := finiteFlipGreatestGap_antitone hsub hF
      have hlower := (isGreatest_finiteFlip_hyperplaneGap F hF).2 hbase
      exact not_lt_of_ge (hlower.trans hupper) dyadicFlipGreatestGap_lt_ceiling
    by_contra hne
    have hproper : ({2} : Finset ℕ) ⊂ insert 2 F := by
      refine ⟨singleton_subset_iff.mpr (mem_insert_self 2 F), ?_⟩
      intro hback
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have he : p = 2 := mem_singleton.mp (hback (mem_insert_of_mem hp))
      exact h2 (he ▸ hp)
    have hbelow : finiteFlipGreatestGap (insert 2 F) < 2 * Real.log 2 :=
      (finiteFlipGreatestGap_antitone hproper.1 (insert_two_prime hF)).trans_lt
        dyadicFlipGreatestGap_lt_ceiling
    have hstrict := (finiteFlipGreatestGap_lt_iff_of_ssubset hproper
      (insert_two_prime hF)).mpr hbelow
    have he : (fun n => finiteFlip {2} n * finiteFlip F n) = finiteFlip (insert 2 F) := by
      funext n
      symm
      simpa only [dyadicPrimeToggle, if_neg h2] using finiteFlip_dyadicPrimeToggle F n
    rw [he] at hprobe
    exact not_lt_of_ge ((isGreatest_finiteFlip_hyperplaneGap (insert 2 F)
      (insert_two_prime hF)).2 hprobe) hstrict
  · intro he
    subst F
    refine ⟨(finiteFlip_hasHyperplaneGap_iff_le_greatestGap ∅ hF _).mpr ?_, ?_⟩
    · simpa only [finiteFlipHarmonicDensity, prod_empty, one_pow, mul_one] using
        (finiteFlipGreatestGap_bounds ∅ hF).1
    · have hgauge : (fun n => finiteFlip {2} n * finiteFlip ∅ n) = finiteFlip {2} := by
        funext n
        have hempty : finiteFlip ∅ n = 1 := prod_empty
        rw [hempty, mul_one]
      rw [hgauge]
      exact (isGreatest_finiteFlip_hyperplaneGap {2} dyadic_singleton_prime).1

end GaloisForLFunctions.ArithmeticCountingPositivity
