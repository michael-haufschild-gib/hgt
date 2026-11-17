import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.BezoutValuationIncidence.VinogradovKorobovCofinalMobiusDiscrepancy
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Adjacent first-octave cofactors recover the ordinary prime count

Increasing the cutoff from `t` to `t+1` removes the Möbius coefficient
at `t+1` and adds those at `2t+1` and `2t+2`. For a prime
`p = 2t+1 ≡ 7 (mod 8)`, both even endpoints are multiples of four.
Only the coefficient `-1` at the ordinary prime survives.
-/

noncomputable section

open Finset ArithmeticFunction
open RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The Vaughan short cofactor truncated at twice the Möbius cutoff. -/
def firstOctaveCofactor (t : ℕ) := truncAF (typeIIShort t) (2 * t)

private theorem octave_apply (t d : ℕ) :
    firstOctaveCofactor t d = if t < d ∧ d ≤ 2 * t then moebiusReal d else 0 := by
  rw [firstOctaveCofactor, truncAF_apply]
  by_cases hhi : d ≤ 2 * t
  · rw [if_pos hhi]
    by_cases hlo : t < d
    · rw [if_pos ⟨hlo, hhi⟩]
      exact typeIIShort_eq_moebiusReal_first_octave hlo hhi
    · rw [if_neg (fun h => hlo h.1)]
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact ArithmeticFunction.map_zero
      · exact typeIIShort_apply_eq_zero_of_le hpos (by omega)
  · simp only [hhi, and_false, if_false]

private theorem mu_zero_of_four_dvd {k : ℕ} (hk : 4 ∣ k) : moebiusReal k = 0 := by
  have h : ArithmeticFunction.moebius k = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact Nat.prime_two.not_isUnit (hs 2 (by simpa using hk))
  simp [moebiusReal, h]

/-- At a prime in the residue class seven modulo eight the difference of two
whole Vaughan octaves is a single signed atom, pointwise at every integer. -/
theorem adjacent_octave_difference {t : ℕ} (hp : (2 * t + 1).Prime) (ht : 4 ∣ t + 1) (d : ℕ) :
    firstOctaveCofactor (t + 1) d - firstOctaveCofactor t d = if d = 2 * t + 1 then -1 else 0 := by
  have hpos : 1 ≤ t := by have := hp.two_le; omega
  rw [octave_apply, octave_apply]
  by_cases hmid : d = 2 * t + 1
  · subst d
    have hμ : moebiusReal (2 * t + 1) = -1 := by simp [moebiusReal, moebius_apply_prime hp]
    rw [if_pos (by omega), if_neg (by omega), if_pos rfl, hμ, sub_zero]
  rw [if_neg hmid]
  by_cases hlow : d = t + 1
  · subst d
    simp [mu_zero_of_four_dvd ht]
  by_cases hhigh : d = 2 * (t + 1)
  · subst d
    have h4 : 4 ∣ 2 * (t + 1) := dvd_mul_of_dvd_right ht _
    simp [mu_zero_of_four_dvd h4]
  have hsame : (t + 1 < d ∧ d ≤ 2 * (t + 1)) ↔ (t < d ∧ d ≤ 2 * t) := by omega
  simp only [hsame, sub_self]

private theorem octave_count (t M : ℕ) :
    cofactorCountError t (2*t) M =
      ∑ d ∈ Icc 1 M, firstOctaveCofactor t d * (Chebyshev.psi (M / d : ℕ) - (M / d : ℕ)) := by
  rw [cofactorCountError, cofactorCountCoeff, mul_comm, RHTower.sum_Icc_mul_apply]
  simp only [sum_vonMangoldt_sub_zeta, firstOctaveCofactor]

/-- Sampling at multiples of the isolated prime recovers every ordinary
prime error exactly from two adjacent cofactor counts. Such pairs occur
above every prescribed lower bound on the cutoff. -/
theorem cofinal_adjacent_octaves_recover_prime_error (B : ℕ) :
    ∃ t > B, (2*t+1).Prime ∧ ∀ N : ℕ,
      cofactorCountError (t+1) (2*(t+1)) ((2*t+1)*N) -
        cofactorCountError t (2*t) ((2*t+1)*N) = (N : ℝ) - Chebyshev.psi N := by
  obtain ⟨p, hlarge, hp, hclass⟩ := Nat.forall_exists_prime_gt_and_modEq (2*B+2)
    (q := 8) (a := 7) (by decide) (by decide)
  change p % 8 = 7 % 8 at hclass
  let t := p / 2
  have hpt : 2*t+1 = p := by dsimp [t]; omega
  have h4 : 4 ∣ t+1 := by dsimp [t]; omega
  have ht : B < t := by dsimp [t]; omega
  refine ⟨t, ht, hpt.symm ▸ hp, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cofactorCountError, Chebyshev.psi]
  let M := (2*t+1)*N
  have hm : 2*t+1 ∈ Icc 1 M := mem_Icc.mpr ⟨by omega, Nat.le_mul_of_pos_right _ hN⟩
  have hq : M / (2*t+1) = N := Nat.mul_div_cancel_left _ (by omega)
  rw [octave_count, octave_count, ← sum_sub_distrib]
  simp_rw [← sub_mul, adjacent_octave_difference (hpt.symm ▸ hp) h4, ite_mul, zero_mul]
  change (∑ d ∈ Icc 1 M, if d = 2*t+1 then (-1 : ℝ) *
    (Chebyshev.psi (M/d : ℕ) - (M/d : ℕ)) else 0) = _
  rw [sum_ite_eq', if_pos hm, hq]
  ring

#print axioms cofinal_adjacent_octaves_recover_prime_error

end GaloisForLFunctions.ExceptionalLayerTheory
