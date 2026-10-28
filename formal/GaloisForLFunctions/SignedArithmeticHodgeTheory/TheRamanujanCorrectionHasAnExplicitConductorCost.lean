import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes
import Mathlib.Data.Nat.Log

/-!
# Explicit conductor cost of the Ramanujan prime correction

The reciprocal Mangoldt tail on one prime tower is at most `2 log p / y`.
Only conductor primes change a Ramanujan mode, so the normalized row correction
is bounded by `4 sqrt(phi(m)) log(m) / y`, uniformly in the row index.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open RenormalizedArithmeticPotentialTheory ArithmeticIntersectionTheory

/-- Reciprocal Mangoldt mass beyond an inclusive horizon on one prime tower. -/
def localMangoldtTail (p y : ℕ) : ℝ :=
  (∑' t, localMangoldtMass p t) - ∑ t ∈ range (y + 1), localMangoldtMass p t

private theorem localMangoldtMass_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    localMangoldtMass p (p ^ (k + 1)) = Real.log p / (p : ℝ) ^ (k + 1) := by
  rw [localMangoldtMass, if_pos (dvd_pow_self p (by omega)),
    vonMangoldt_prime_pow hp (by omega), Nat.cast_pow]

private theorem localMangoldt_prefix_ge {p y K : ℕ} (hp : p.Prime)
    (hK : p ^ K ≤ y) :
    (∑ k ∈ range K, Real.log p / (p : ℝ) ^ (k + 1)) ≤
      ∑ t ∈ range (y + 1), localMangoldtMass p t := by
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := by
    apply StrictMono.injective
    intro a b hab
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hsub : (range K).image (fun k => p ^ (k + 1)) ⊆ range (y + 1) := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
    have hkK : k + 1 ≤ K := by
      have := mem_range.mp hk
      omega
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.pow_le_pow_right hp.pos hkK).trans hK))
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun t _ _ => localMangoldtMass_nonneg p t)
  rw [sum_image (fun a _ b _ hab => hinj hab)] at h
  simpa only [localMangoldtMass_pow hp] using h

private theorem prime_geometric_remainder {p : ℕ} (hp : p.Prime) (K : ℕ) :
    Real.log p / ((p : ℝ) - 1) -
        (∑ k ∈ range K, Real.log p / (p : ℝ) ^ (k + 1)) =
      (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ K := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith only [this]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ← sub_sub, ih, pow_succ]
    field_simp
    ring

/-- The exact prime-power cutoff gives a geometric bound on the remaining mass. -/
theorem localMangoldtTail_le_geometric {p y K : ℕ} (hp : p.Prime)
    (hK : p ^ K ≤ y) :
    localMangoldtTail p y ≤ (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ K := by
  have htotal : (∑' t, localMangoldtMass p t) ≤ Real.log p / ((p : ℝ) - 1) :=
    Real.tsum_le_of_sum_le (localMangoldtMass_nonneg p) (sum_dvd_vonMangoldt_div_le hp)
  calc
    _ ≤ Real.log p / ((p : ℝ) - 1) -
        (∑ k ∈ range K, Real.log p / (p : ℝ) ^ (k + 1)) :=
      sub_le_sub htotal (localMangoldt_prefix_ge hp hK)
    _ = _ := prime_geometric_remainder hp K

/-- One explicit reciprocal-horizon bound works for every prime tower. -/
theorem localMangoldtTail_le {p y : ℕ} (hp : p.Prime) (hy : 0 < y) :
    localMangoldtTail p y ≤ 2 * Real.log p / (y : ℝ) := by
  let K := Nat.log p y
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith only [hp2]
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp2])
  have hY : (y : ℝ) ≤ (p : ℝ) ^ K * p := by
    have h : (y : ℝ) ≤ (p : ℝ) ^ (K + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self hp.one_lt y).le
    simpa only [pow_succ] using h
  have hfactor : (Real.log p / ((p : ℝ) - 1)) * p ≤ 2 * Real.log p := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp1]
    nlinarith only [mul_nonneg hlog (show 0 ≤ (p : ℝ) - 2 by linarith only [hp2])]
  calc
    _ ≤ (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ K :=
      localMangoldtTail_le_geometric hp (Nat.pow_log_le_self p hy.ne')
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos hp0 K) hy0).mpr
      calc
        _ ≤ (Real.log p / ((p : ℝ) - 1)) * ((p : ℝ) ^ K * p) :=
          mul_le_mul_of_nonneg_left hY (div_nonneg hlog hp1.le)
        _ = ((Real.log p / ((p : ℝ) - 1)) * p) * (p : ℝ) ^ K := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hp0.le K)

private theorem ramanujanCorrectionTail_eq_sum_local (m y : ℕ) :
    ramanujanCorrectionTail m y =
      (2 * (m.totient : ℝ)) * ∑ p ∈ m.primeFactors, localMangoldtTail p y := by
  have hs := hasSum_sum (s := m.primeFactors) fun p hp =>
    (summable_localMangoldtMass (Nat.prime_of_mem_primeFactors hp)).hasSum
  have ht : (∑' t, ramanujanCorrectionMajorant m t) =
      (2 * (m.totient : ℝ)) * ∑ p ∈ m.primeFactors, ∑' t, localMangoldtMass p t :=
    (hs.mul_left (2 * (m.totient : ℝ))).tsum_eq
  unfold ramanujanCorrectionTail
  rw [ht]
  simp only [ramanujanCorrectionMajorant, ← mul_sum]
  rw [sum_comm]
  simp only [localMangoldtTail, sum_sub_distrib, mul_sub]

private theorem sum_conductor_prime_logs_le {m : ℕ} (hm : 0 < m) :
    (∑ p ∈ m.primeFactors, Real.log p) ≤ Real.log m := by
  have hprimes : ∀ p ∈ m.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < ∏ p ∈ m.primeFactors, p := prod_pos fun p hp => (hprimes p hp).pos
  have hle : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero), ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos) hle

/-- The conductor correction has an explicit bound before normalization. -/
theorem ramanujanCorrectionTail_le {m y : ℕ} (hm : 0 < m) (hy : 0 < y) :
    ramanujanCorrectionTail m y ≤ 4 * (m.totient : ℝ) * Real.log m / (y : ℝ) := by
  rw [ramanujanCorrectionTail_eq_sum_local]
  calc
    _ ≤ (2 * (m.totient : ℝ)) *
        ∑ p ∈ m.primeFactors, (2 * Real.log p / (y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum fun p hp => localMangoldtTail_le (Nat.prime_of_mem_primeFactors hp) hy)
        (by positivity)
    _ = 4 * (m.totient : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) / (y : ℝ) := by
      rw [← sum_div, ← mul_sum]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sum_conductor_prime_logs_le hm) (by positivity))
      (Nat.cast_nonneg y)

/-- All rows share the same conductor-explicit, reciprocal-horizon correction bound. -/
theorem abs_normalizedRamanujan_correction_le {m n y : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hy : 0 < y) :
    |poleProfileCorrection (normalizedRamanujanMode m) y n +
      (Real.log m + tameDifferent m) * normalizedRamanujanMode m n| ≤
        4 * Real.sqrt (m.totient : ℝ) * Real.log m / (y : ℝ) := by
  have hφ : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsqrt : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
  have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  calc
    _ ≤ ramanujanCorrectionTail m y / Real.sqrt (m.totient : ℝ) :=
      abs_normalizedRamanujan_correction_le_tail hm hn y
    _ ≤ (4 * (m.totient : ℝ) * Real.log m / (y : ℝ)) /
        Real.sqrt (m.totient : ℝ) :=
      div_le_div_of_nonneg_right (ramanujanCorrectionTail_le hm hy) (Real.sqrt_nonneg _)
    _ = (4 * Real.sqrt (m.totient : ℝ) ^ 2 * Real.log m / (y : ℝ)) /
        Real.sqrt (m.totient : ℝ) := by rw [Real.sq_sqrt hφ.le]
    _ = _ := by
      field_simp [hsqrt, hy0]
      ring

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.localMangoldtTail_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.ramanujanCorrectionTail_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_normalizedRamanujan_correction_le
