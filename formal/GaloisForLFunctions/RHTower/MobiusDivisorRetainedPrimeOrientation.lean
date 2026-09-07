import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptivePrimeEnergyObstruction
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Orientation reversal after merging smaller prime labels

The negative complete source at cutoff seven is copied with reversed sign
into an isolated prime fibre at cutoff `7*p`, for every prime `p>7`, after
the smaller source primes are processed. These positive retained fibres are
unbounded along prime dilations. Processing them strictly increases the head.
The exact source recursion, not the original prime coefficient sign,
determines the retained orientation.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- The complete source at seven is strictly negative by its analytic two-group bounds. -/
theorem sum_mobiusDivisorDilationChannel_seven_neg :
    (∑ n ∈ Icc 1 7,mobiusDivisorDilationChannel 7 n) < 0 := by
  obtain ⟨hf,hd⟩ := mobiusDivisorLastPrime_seven_both_neg 2 (by simp)
  have he := mobiusDivisorLastPrime_add_eq_total 7 2
  linarith

/-- The processed smaller source has an exact reflected prime-fibre copy. -/
theorem mobiusDivisorSelectionFibre_seven_mul_prime {p : ℕ} (hp : p.Prime) (h7p : 7<p) :
    mobiusDivisorSelectionFibre (p*7) (mobiusDivisorSelectionPrimes 7) {p} =
      -Real.sqrt p*(∑ n ∈ Icc 1 7,mobiusDivisorDilationChannel 7 n) := by
  apply mobiusDivisorSelectionFibre_mul_prime_of_all_small_primes_processed hp h7p
  · intro h
    have := mem_range.mp (mem_filter.mp h).1
    omega
  · exact Subset.refl _

/-- The retained new-prime singleton is positive after the smaller primes are processed. -/
theorem mobiusDivisorSelectionFibre_seven_mul_prime_pos {p : ℕ} (hp : p.Prime) (h7p : 7<p) :
    0 < mobiusDivisorSelectionFibre (p*7) (mobiusDivisorSelectionPrimes 7) {p} := by
  rw [mobiusDivisorSelectionFibre_seven_mul_prime hp h7p]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)))
    sum_mobiusDivisorDilationChannel_seven_neg

/-- Positive retained singleton fibres exceed every fixed bound beyond every cutoff. -/
theorem exists_mobiusDivisorSelectionFibre_positive_gt (B : ℝ) (M₀ : ℕ) :
    ∃ p : ℕ,p.Prime ∧ 7<p ∧ M₀ ≤ p*7 ∧
      B < mobiusDivisorSelectionFibre (p*7) (mobiusDivisorSelectionPrimes 7) {p} := by
  let S : ℝ := ∑ n ∈ Icc 1 7,mobiusDivisorDilationChannel 7 n
  have hS : S<0 := sum_mobiusDivisorDilationChannel_seven_neg
  have hlim : Tendsto (fun n : ℕ => (-S)*Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (neg_pos.mpr hS)
  have hev : ∀ᶠ n : ℕ in atTop,B+1 ≤ (-S)*Real.sqrt n := (tendsto_atTop.1 hlim) (B+1)
  obtain ⟨N,hN⟩ := eventually_atTop.1 hev
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (max 8 (max N M₀))
  have h7p : 7<p := by omega
  have hpN : N ≤ p := by omega
  have hpM : M₀ ≤ p*7 := by omega
  refine ⟨p,hp,h7p,hpM,?_⟩
  rw [mobiusDivisorSelectionFibre_seven_mul_prime hp h7p]
  have h := hN p hpN
  change B < -Real.sqrt p*S
  nlinarith only [h]

/-- Original prime coefficient orientation does not persist under arbitrary prior mergers. -/
theorem not_forall_mobiusDivisorSelectionPrimeFibre_nonpos :
    ¬ ∀ (M : ℕ) (P : Finset ℕ) (p : ℕ),p.Prime → p<M → p ∉ P →
      mobiusDivisorSelectionFibre M P {p} ≤ 0 := by
  intro h
  obtain ⟨p,hp,h7p,hM,hpos⟩ := exists_mobiusDivisorSelectionFibre_positive_gt 0 0
  have hpM : p<p*7 := by omega
  have hpP : p ∉ mobiusDivisorSelectionPrimes 7 := by
    intro hpP
    have := mem_range.mp (mem_filter.mp hpP).1
    omega
  exact (not_lt_of_ge (h (p*7) (mobiusDivisorSelectionPrimes 7) p hp hpM hpP)) hpos

/-- The reflected negative smaller source forces a strict head increase at the larger cutoff. -/
theorem mobiusDivisorSelectionHead_insert_seven_mul_prime_gt {p : ℕ} (hp : p.Prime) (h7p : 7<p) :
    mobiusDivisorSelectionFibre (p*7) (mobiusDivisorSelectionPrimes 7) ∅ <
      mobiusDivisorSelectionFibre (p*7) (insert p (mobiusDivisorSelectionPrimes 7)) ∅ := by
  rw [mobiusDivisorSelectionFibre_insert]
  simp only [notMem_empty,if_false,insert_empty_eq]
  have hpos := mobiusDivisorSelectionFibre_seven_mul_prime_pos hp h7p
  linarith

end RHTower
