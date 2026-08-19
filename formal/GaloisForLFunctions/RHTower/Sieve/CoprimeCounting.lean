import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusIdentity
import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquare

/-!
# Counting the residues coprime to a modulus

The same detector-and-swap that decomposes the coprime harmonic sum decomposes the coprime counting
function: `#{k ≤ z : (e,k) = 1} = ∑_{f ∣ e} μ(f) ⌊z/f⌋`.  This is the exact identity behind the
density `φ(e)/e` and behind every elementary estimate of the coprime Möbius sums.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The coprime counting identity.** -/
theorem coprimeCount_eq_sum_divisors {e z : ℕ} (he : 0 < e) :
    ((((Finset.Icc 1 z).filter (fun k => Nat.Coprime e k)).card : ℕ) : ℝ)
      = ∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) * ((z / f : ℕ) : ℝ) := by
  classical
  have hcard : ((((Finset.Icc 1 z).filter (fun k => Nat.Coprime e k)).card : ℕ) : ℝ)
      = ∑ k ∈ (Finset.Icc 1 z).filter (fun k => Nat.Coprime e k), (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, Finset.sum_filter]
  have hdet : ∀ k ∈ Finset.Icc 1 z,
      (if Nat.Coprime e k then (1 : ℝ) else 0)
        = ∑ f ∈ (Nat.gcd e k).divisors, ((μ f : ℤ) : ℝ) := by
    intro k _
    rw [sum_divisors_moebius_real]
  rw [Finset.sum_congr rfl hdet]
  have hmem : ∀ (k f : ℕ),
      k ∈ Finset.Icc 1 z ∧ f ∈ (Nat.gcd e k).divisors
        ↔ k ∈ (Finset.Icc 1 z).filter (fun k => f ∣ k) ∧ f ∈ e.divisors := by
    intro k f
    constructor
    · rintro ⟨hk, hf⟩
      obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
      have hfg : f ∣ Nat.gcd e k := Nat.dvd_of_mem_divisors hf
      have hfe : f ∣ e := dvd_trans hfg (Nat.gcd_dvd_left _ _)
      have hfk : f ∣ k := dvd_trans hfg (Nat.gcd_dvd_right _ _)
      exact ⟨Finset.mem_filter.mpr ⟨hk, hfk⟩, Nat.mem_divisors.mpr ⟨hfe, by omega⟩⟩
    · rintro ⟨hkf, hf⟩
      obtain ⟨hk, hfk⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
      have hfe : f ∣ e := Nat.dvd_of_mem_divisors hf
      refine ⟨hk, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hfe hfk, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_right e (by omega)).ne'
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
  rw [Finset.sum_const, card_filter_dvd_Icc hf0, nsmul_eq_mul]
  ring

end RHTower.Sieve
