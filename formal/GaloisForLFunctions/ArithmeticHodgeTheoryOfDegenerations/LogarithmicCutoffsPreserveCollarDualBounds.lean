import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LeftCutoffsPreserveLipschitzApproximation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NonpolarCollarResidualsVanish

/-!
# Logarithmic cutoffs preserve collar dual bounds

Removing a lower logarithmic strip costs only its truncated dual seventh mass.
The retained part is bounded by a fixed terminal-window square norm.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory

/-- Multiply horizon coordinates by a fixed left cutoff in logarithmic coordinates. -/
def horizonLogCutoff (a : ℝ) {N : ℕ} (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (fun n => leftProfileCutoff a (Real.log ((n : ℝ) / N)) *
    primeHorizonExtension v n) N

lemma horizonLogCutoff_apply (a : ℝ) {N : ℕ}
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) (i : PrimeHorizonIndex N) :
    horizonLogCutoff a v i = leftProfileCutoff a (Real.log ((i.1 : ℝ) / N)) * v i := by
  change leftProfileCutoff a (Real.log ((i.1 : ℝ) / N)) * primeHorizonExtension v i.1 = _
  rw [primeHorizonExtension_coe]

/-- Removing the left cutoff only charges the truncated dual seventh mass below `exp(a+2)N`. -/
theorem topCollarDualSeventhMass_sub_logCutoff_le (a : ℝ) {M N : ℕ} (hN : 1 ≤ N)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (v - horizonLogCutoff a v) ≤
      truncatedCollarDualSeventhMass M ⌊Real.exp (a + 2) * (N : ℝ)⌋₊ N v := by
  let D := ⌊Real.exp (a + 2) * (N : ℝ)⌋₊
  let w : ℕ → ℝ := fun n => ((n : ℝ) / N) ^ 7 * primeHorizonExtension v n ^ 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : ∀ n ∈ Ioc M N,
      ((n : ℝ) / N) ^ 7 * primeHorizonExtension (v - horizonLogCutoff a v) n ^ 2 ≤
        if n ≤ D then w n else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let i : PrimeHorizonIndex N := ⟨n, hnI⟩
    have he : primeHorizonExtension (v - horizonLogCutoff a v) n =
        (1 - leftProfileCutoff a (Real.log ((n : ℝ) / N))) * primeHorizonExtension v n := by
      change primeHorizonExtension (v - horizonLogCutoff a v) i.1 = _
      rw [primeHorizonExtension_coe]
      change v i - horizonLogCutoff a v i = _
      rw [horizonLogCutoff_apply]
      change _ = (1 - leftProfileCutoff a (Real.log ((n : ℝ) / N))) * primeHorizonExtension v i.1
      rw [primeHorizonExtension_coe]
      ring
    rw [he]
    by_cases hnD : n ≤ D
    · rw [if_pos hnD]
      obtain ⟨hcut0, hcut1⟩ := leftProfileCutoff_bounds a (Real.log ((n : ℝ) / N))
      have hsq : (1 - leftProfileCutoff a (Real.log ((n : ℝ) / N))) ^ 2 ≤ 1 := by
        nlinarith only [hcut0, hcut1, mul_nonneg hcut0 (sub_nonneg.mpr hcut1)]
      have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (primeHorizonExtension v n))
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hh) (by positivity)
    · rw [if_neg hnD]
      have hfrac : Real.exp (a + 2) < (n : ℝ) / N := (lt_div_iff₀ hN0).mpr
        ((Nat.floor_lt (by positivity : 0 ≤ Real.exp (a + 2) * (N : ℝ))).mp
          (by exact not_le.mp hnD : D < n))
      have hlog : a + 2 ≤ Real.log ((n : ℝ) / N) :=
        ((Real.lt_log_iff_exp_lt (div_pos hn0 hN0)).mpr hfrac).le
      rw [leftProfileCutoff_eq_one hlog, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hs := sum_le_sum hp
  rw [← sum_filter] at hs
  exact hs.trans (sum_le_sum_of_subset_of_nonneg
    (fun n hn => by
      obtain ⟨hn, hnD⟩ := mem_filter.mp hn
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hnD⟩)
    (fun n _ _ => by dsimp only [w]; positivity))

/-- A logarithmic cutoff has operator norm at most one on every terminal square norm. -/
theorem topWindowResidualMass_logCutoff_le (a δ : ℝ) {N : ℕ}
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topWindowResidualMass δ N (horizonLogCutoff a v) ≤ topWindowResidualMass δ N v := by
  apply sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  let i : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩⟩
  change primeHorizonExtension (horizonLogCutoff a v) i.1 ^ 2 ≤ primeHorizonExtension v i.1 ^ 2
  rw [primeHorizonExtension_coe, primeHorizonExtension_coe, horizonLogCutoff_apply, mul_pow]
  obtain ⟨h0, h1⟩ := leftProfileCutoff_bounds a (Real.log ((n : ℝ) / N))
  have hsq : leftProfileCutoff a (Real.log ((n : ℝ) / N)) ^ 2 ≤ 1 := by
    nlinarith only [h0, h1, mul_nonneg h0 (sub_nonneg.mpr h1)]
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg (v i))).trans_eq (one_mul _)

/-- The cutoff dual mass is controlled by the original terminal square mass above its left end. -/
theorem topCollarDualSeventhMass_logCutoff_le_topWindow (a : ℝ) {M N : ℕ} (hN : 1 ≤ N)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (horizonLogCutoff a v) ≤
      topWindowResidualMass (Real.exp a) N v := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let D := ⌊Real.exp a * (N : ℝ)⌋₊
  have hp : ∀ n ∈ Ioc M N,
      ((n : ℝ) / N) ^ 7 * primeHorizonExtension (horizonLogCutoff a v) n ^ 2 ≤
        if D < n then primeHorizonExtension v n ^ 2 else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let i : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩⟩
    change ((n : ℝ) / N) ^ 7 * primeHorizonExtension (horizonLogCutoff a v) i.1 ^ 2 ≤ _
    rw [primeHorizonExtension_coe, horizonLogCutoff_apply]
    change _ ≤ if D < n then primeHorizonExtension v i.1 ^ 2 else 0
    rw [primeHorizonExtension_coe]
    by_cases hDn : D < n
    · rw [if_pos hDn, mul_pow]
      obtain ⟨hcut0, hcut1⟩ := leftProfileCutoff_bounds a (Real.log ((n : ℝ) / N))
      have hcut2 : leftProfileCutoff a (Real.log ((n : ℝ) / N)) ^ 2 ≤ 1 := by
        nlinarith only [hcut0, hcut1, mul_nonneg hcut0 (sub_nonneg.mpr hcut1)]
      have hw : ((n : ℝ) / N) ^ 7 ≤ 1 := pow_le_one₀ (by positivity)
        ((div_le_one hN0).mpr (by exact_mod_cast (mem_Ioc.mp hn).2))
      have hh := mul_le_mul hw hcut2 (sq_nonneg _) zero_le_one
      simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hh (sq_nonneg (v i))
    · rw [if_neg hDn]
      have hx : (n : ℝ) / N ≤ Real.exp a := (div_le_iff₀ hN0).mpr
        ((by exact_mod_cast (not_lt.mp hDn) : (n : ℝ) ≤ D).trans (Nat.floor_le (by positivity)))
      have hlog : Real.log ((n : ℝ) / N) ≤ a := (Real.log_le_iff_le_exp (div_pos hn0 hN0)).mpr hx
      rw [leftProfileCutoff_eq_zero hlog, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hs := sum_le_sum hp
  rw [← sum_filter] at hs
  exact hs.trans (sum_le_sum_of_subset_of_nonneg
    (fun n hn => by
      obtain ⟨hn, hnD⟩ := mem_filter.mp hn
      exact mem_Ioc.mpr ⟨hnD, (mem_Ioc.mp hn).2⟩)
    (fun n _ _ => sq_nonneg _))

lemma horizonLogCutoff_sub (a : ℝ) {N : ℕ}
    (u v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonLogCutoff a (u - v) = horizonLogCutoff a u - horizonLogCutoff a v := by
  ext i
  simp only [PiLp.sub_apply, horizonLogCutoff_apply]
  change _ * (u i - v i) = _ * u i - _ * v i
  ring

lemma horizonLogCutoff_smul (a t : ℝ) {N : ℕ}
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonLogCutoff a (t • v) = t • horizonLogCutoff a v := by
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, horizonLogCutoff_apply]
  change _ * (t * v i) = t * (_ * v i)
  ring

#print axioms topCollarDualSeventhMass_logCutoff_le_topWindow

#print axioms topCollarDualSeventhMass_sub_logCutoff_le
#print axioms topWindowResidualMass_logCutoff_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
