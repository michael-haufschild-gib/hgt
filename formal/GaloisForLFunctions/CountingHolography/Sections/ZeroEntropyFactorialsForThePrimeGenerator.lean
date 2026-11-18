import GaloisForLFunctions.CountingHolography.Sections.EntropyAndValueOfBalancedFactorials
import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSectionModuli

/-! # Zero-entropy factorials for the ordinary prime section generator

Every individual logarithmic prime valuation is an integer multiple of a
zero-entropy price at the same horizon plus one. Adding the presentations
gives the exact signed rational section generator.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction

/-- The complete ordinary prime generator is a balanced factorial ratio
of exactly zero Stirling entropy, including all integer flooring errors. -/
theorem ordinaryPrimeGenerator_zeroEntropy_factorials {N : ℕ} (a : Fin N → ℤ) :
    ∃ c : ℕ →₀ ℤ, (∀ j, max 10 (3*windowEnd N+1) < j → c j=0) ∧
      factorialBalance c = 0 ∧ factorialEntropy c = 0 ∧ factorialValue c = ordinaryPrimeGenerator a := by
  let L := max 10 (3*windowEnd N+1)
  let H := zeroEntropyPrices L
  have hm : Real.log (ordinaryPrimeGenerator a : ℝ) ∈ H := by
    rw [log_ordinaryPrimeGenerator]
    apply H.sum_mem
    intro k hk
    obtain ⟨hI,hp⟩ := mem_filter.mp hk
    have hkL : k < L := (Nat.lt_succ_of_le (mem_Icc.mp hI).2).trans_le (le_max_right _ _)
    rw [vonMangoldt_apply_prime hp,← zsmul_eq_mul]
    exact H.zsmul_mem (log_nat_mem_zeroEntropyPrices (le_max_left _ _) k hkL) _
  obtain ⟨c,hc,hb,he,hv⟩ := hm
  refine ⟨c,hc,hb,he,?_⟩
  have hp : 0 < ordinaryPrimeGenerator a :=
    prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
  have hh : (factorialValue c:ℝ)=(ordinaryPrimeGenerator a:ℝ) :=
    Real.log_injOn_pos (by exact_mod_cast factorialValue_pos c) (by exact_mod_cast hp)
      ((log_factorialValue c).trans hv)
  exact_mod_cast hh

#print axioms ordinaryPrimeGenerator_zeroEntropy_factorials

end GaloisForLFunctions.CountingHolography.Sections
