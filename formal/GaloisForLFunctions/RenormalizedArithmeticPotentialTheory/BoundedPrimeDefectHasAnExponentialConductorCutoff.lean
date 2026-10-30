import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.FiniteSieveProfilesHaveEffectiveRamanujanApproximations
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSmoothRoughMeanApproximatesBoundedDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanAdjunctionEnergiesAreDistinct

/-!
# Exponential conductor confinement from bounded prime defect

Conditioning on small-prime parts and discarding their logarithmic tail gives
a finite sieve profile. Its actual harmonic weights admit spectral truncation
without a primorial loss. Exact finite Ramanujan spans cover smaller horizons.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory BezoutValuationIncidence

/-- The finite sieve consisting of all primes below an integer threshold. -/
def primePrefixSieve (P : ℕ) : Finset Nat.Primes :=
  ((range P).filter Nat.Prime).subtype Nat.Prime

theorem mem_primePrefixSieve (P : ℕ) (p : Nat.Primes) :
    p ∈ primePrefixSieve P ↔ (p : ℕ) < P := by
  simp only [primePrefixSieve, Finset.mem_subtype, mem_filter, mem_range,
    p.property, and_true]

private theorem divisors_eq_horizon_filter {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    d.divisors = (Icc 1 N).filter (fun q => q ∣ d) := by
  ext q
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hqd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hqd hd, (Nat.le_of_dvd hd hqd).trans hdN⟩, hqd⟩
  · rintro ⟨_, hqd⟩
    exact ⟨hqd, hd.ne'⟩

/-- The first `N` conductors span all real data on the first `N` positive integers. -/
theorem exists_horizon_normalizedRamanujan_expansion (N : ℕ) (F : ℕ → ℝ) :
    ∃ b : ℕ → ℝ, ∀ n ∈ Icc 1 N,
      F n = ∑ m ∈ Icc 1 N, b m * normalizedRamanujanMode m n := by
  let a : ℕ → ℝ := fun m => ∑ d ∈ Icc 1 N,
    if m ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0
  refine ⟨fun m => a m * Real.sqrt (m.totient : ℝ), fun n hn => ?_⟩
  have hn0 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hinversion : F n = ∑ d ∈ Icc 1 N,
      if d ∣ n then gcdProfileMobiusCoefficient F d else 0 := by
    rw [← sum_gcdProfileMobiusCoefficient F hn0, divisors_eq_horizon_filter hn0 hnN, sum_filter]
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      (if d ∣ n then gcdProfileMobiusCoefficient F d else 0) =
        ∑ m ∈ Icc 1 N,
          (if m ∣ d then gcdProfileMobiusCoefficient F d / (d : ℝ) else 0) *
            ramanujanLagCoefficient m n := by
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hs := sum_divisors_ramanujanLagCoefficient hn0 hd0
    calc
      _ = gcdProfileMobiusCoefficient F d / (d : ℝ) *
          (∑ m ∈ d.divisors, ramanujanLagCoefficient m n) := by
        rw [hs]
        by_cases hdn : d ∣ n
        · rw [if_pos hdn, if_pos hdn, div_mul_cancel₀ _ hdR]
        · rw [if_neg hdn, if_neg hdn, mul_zero]
      _ = _ := by
        rw [divisors_eq_horizon_filter hd0 (mem_Icc.mp hd).2, sum_filter, mul_sum]
        exact sum_congr rfl fun m _ => by
          by_cases hmd : m ∣ d
          · rw [if_pos hmd, if_pos hmd]
          · rw [if_neg hmd, if_neg hmd, mul_zero, zero_mul]
  have hexp : F n = ∑ m ∈ Icc 1 N, a m * ramanujanLagCoefficient m n := by
    rw [hinversion, sum_congr rfl hterm, sum_comm]
    exact sum_congr rfl fun m _ => (sum_mul _ _ _).symm
  rw [hexp]
  refine sum_congr rfl fun m hm => ?_
  have hm0 := (mem_Icc.mp hm).1
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hs : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot).ne'
  rw [normalizedRamanujanMode_eq_coefficient hm0]
  field_simp

/-- Every finite physical vector has an exact Ramanujan pole expansion within its own horizon. -/
theorem exists_horizon_ramanujanPole_expansion (N : ℕ) (x : ℕ → ℝ) :
    ∃ b : ℕ → ℝ, ∀ n ∈ Icc 1 N,
      x n = ∑ m ∈ Icc 1 N, b m * ramanujanPoleProfile m n := by
  obtain ⟨b, hb⟩ := exists_horizon_normalizedRamanujan_expansion N (fun n => Real.sqrt n * x n)
  refine ⟨b, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have h := hb n hn
  calc
    x n = (Real.sqrt n * x n) / Real.sqrt n := by field_simp
    _ = (∑ m ∈ Icc 1 N, b m * normalizedRamanujanMode m n) / Real.sqrt n := by rw [h]
    _ = _ := by
      rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile]; ring


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_horizon_ramanujanPole_expansion
