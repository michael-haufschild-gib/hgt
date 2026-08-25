/- Uniform summability of the proper-prime-power correction in the Mangoldt square moment. -/

import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareHyperbola
import GaloisForLFunctions.RHTower.EulerFisherCurvature

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

/-- Natural number represented by a prime and an exponent at least two. -/
def properPrimePowerNat (pk : Nat.Primes × ℕ) : ℕ :=
  pk.1.1 ^ (pk.2 + 2)

theorem properPrimePowerNat_injective : Function.Injective properPrimePowerNat := by
  intro x y hxy
  have hshift :
      RHTower.eulerPrimePowerNat (x.1, x.2 + 1) =
        RHTower.eulerPrimePowerNat (y.1, y.2 + 1) := by
    simpa [properPrimePowerNat, RHTower.eulerPrimePowerNat] using hxy
  have hpair := RHTower.eulerPrimePowerNat_injective hshift
  injection hpair with hp hk
  exact Prod.ext hp (by omega)

theorem properPrimePowerNat_isPrimePow (pk : Nat.Primes × ℕ) :
    IsPrimePow (properPrimePowerNat pk) := by
  apply (isPrimePow_nat_iff _).mpr
  exact ⟨pk.1.1, pk.2 + 2, pk.1.2, by omega, rfl⟩

theorem properPrimePowerNat_not_prime (pk : Nat.Primes × ℕ) :
    ¬ Nat.Prime (properPrimePowerNat pk) := by
  rw [properPrimePowerNat]
  exact Nat.Prime.not_prime_pow (by omega)

/-- Fourth-log harmonic weight on a proper prime power and zero elsewhere. -/
def properPrimePowerLogFourthWeight (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ ¬ Nat.Prime n then Real.log n ^ 4 / (n : ℝ) else 0

theorem properPrimePowerLogFourthWeight_nonneg (n : ℕ) :
    0 ≤ properPrimePowerLogFourthWeight n := by
  rw [properPrimePowerLogFourthWeight]
  split_ifs
  · positivity
  · exact le_rfl

private def properPrimePowerLogFourthMajor (pk : Nat.Primes × ℕ) : ℝ :=
  (Real.log (pk.1 : ℝ)) ^ 4 * ((pk.1 : ℝ)⁻¹) ^ 2 *
    (((pk.2 + 2 : ℕ) : ℝ) ^ 4 * (1 / 2 : ℝ) ^ pk.2)

private theorem summable_shiftedFourthGeometric :
    Summable (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h0 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr
  have h4 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hr
  have hsum := (((h4.add (h3.mul_left 8)).add (h2.mul_left 24)).add
    (h1.mul_left 32)).add (h0.mul_left 16)
  apply hsum.congr
  intro k
  push_cast
  ring

private theorem summable_primeLogFourthInvSquare :
    Summable (fun p : Nat.Primes =>
      (Real.log (p : ℝ)) ^ 4 * ((p : ℝ)⁻¹) ^ 2) := by
  have hnat := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 4 2
    (by norm_num : (1 : ℝ) < 2)
  have hp := hnat.subtype Nat.Prime
  apply hp.congr
  intro p
  change |Real.log (p : ℝ)| ^ 4 * (p : ℝ) ^ (-2 : ℝ) = _
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
    exact_mod_cast p.prop.one_le)
  rw [abs_of_nonneg hlog, Real.rpow_neg hp0.le, Real.rpow_two, inv_pow]

private theorem summable_properPrimePowerLogFourthMajor :
    Summable properPrimePowerLogFourthMajor := by
  rw [summable_prod_of_nonneg]
  constructor
  · intro p
    exact summable_shiftedFourthGeometric.mul_left
      ((Real.log (p : ℝ)) ^ 4 * ((p : ℝ)⁻¹) ^ 2)
  · apply (summable_primeLogFourthInvSquare.mul_right
      (∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k))).congr
    intro p
    symm
    change (∑' k : ℕ,
      ((Real.log (p : ℝ)) ^ 4 * ((p : ℝ)⁻¹) ^ 2) *
        (((k + 2 : ℕ) : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)) = _
    rw [tsum_mul_left]
  · intro pk
    unfold properPrimePowerLogFourthMajor
    positivity

private theorem properPrimePowerLogFourthWeight_comp_le_major
    (pk : Nat.Primes × ℕ) :
      properPrimePowerLogFourthWeight (properPrimePowerNat pk) ≤
      properPrimePowerLogFourthMajor pk := by
  have hpp := properPrimePowerNat_isPrimePow pk
  have hnp := properPrimePowerNat_not_prime pk
  rcases pk with ⟨p, k⟩
  change properPrimePowerLogFourthWeight (p.1 ^ (k + 2)) ≤
    (Real.log (p : ℝ)) ^ 4 * ((p : ℝ)⁻¹) ^ 2 *
      (((k + 2 : ℕ) : ℝ) ^ 4 * (1 / 2 : ℝ) ^ k)
  rw [properPrimePowerLogFourthWeight, if_pos ⟨hpp, hnp⟩]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := (inv_pos.mpr hp0).le
  have hpow : ((p : ℝ)⁻¹) ^ k ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_left₀ hinv0 hinv _
  rw [Nat.cast_pow, Real.log_pow, div_eq_mul_inv, ← inv_pow, pow_add]
  push_cast
  have hcoef : 0 ≤
      (Real.log (p : ℝ)) ^ 4 * ((p : ℝ)⁻¹) ^ 2 *
        ((k : ℝ) + 2) ^ 4 := by positivity
  nlinarith

private theorem summable_properPrimePowerLogFourthWeight_comp :
    Summable (properPrimePowerLogFourthWeight ∘ properPrimePowerNat) := by
  apply Summable.of_nonneg_of_le
    (fun pk => properPrimePowerLogFourthWeight_nonneg _) 
    properPrimePowerLogFourthWeight_comp_le_major
    summable_properPrimePowerLogFourthMajor

theorem summable_properPrimePowerLogFourthWeight :
    Summable properPrimePowerLogFourthWeight := by
  apply (properPrimePowerNat_injective.summable_iff ?_).mp
    summable_properPrimePowerLogFourthWeight_comp
  intro n hnrange
  by_cases hproper : IsPrimePow n ∧ ¬ Nat.Prime n
  · obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff n).mp hproper.1
    have ha2 : 2 ≤ a := by
      by_contra hnot
      have ha1 : a = 1 := by omega
      subst a
      simp at hpa
      exact hproper.2 (hpa ▸ hp)
    exfalso
    apply hnrange
    refine ⟨((⟨p, hp⟩ : Nat.Primes), a - 2), ?_⟩
    rw [properPrimePowerNat, show a - 2 + 2 = a by omega, hpa]
  · simp [properPrimePowerLogFourthWeight, hproper]

/-- Proper-prime-power part of the fourth-log harmonic sum. -/
def properPrimePowerLogFourthHarmonicSum (N : ℕ) : ℝ :=
  ∑ k ∈ {k ∈ Finset.Icc 2 N | IsPrimePow k ∧ ¬ Nat.Prime k},
    Real.log k ^ 4 / (k : ℝ)

/-- Finite proper-prime-power sums have one unconditional, height-independent budget. -/
theorem properPrimePowerLogFourthHarmonicSum_le_tsum (N : ℕ) :
    properPrimePowerLogFourthHarmonicSum N ≤
      ∑' n : ℕ, properPrimePowerLogFourthWeight n := by
  rw [properPrimePowerLogFourthHarmonicSum]
  have hsum :
      ∑ k ∈ {k ∈ Finset.Icc 2 N | IsPrimePow k ∧ ¬ Nat.Prime k},
          Real.log k ^ 4 / (k : ℝ) =
        ∑ k ∈ Finset.Icc 2 N, properPrimePowerLogFourthWeight k := by
    simpa [properPrimePowerLogFourthWeight] using
      (Finset.sum_filter (s := Finset.Icc 2 N)
        (fun k : ℕ => IsPrimePow k ∧ ¬ Nat.Prime k)
        (fun k : ℕ => Real.log k ^ 4 / (k : ℝ)))
  rw [hsum]
  exact summable_properPrimePowerLogFourthWeight.sum_le_tsum _
    (fun n _ => properPrimePowerLogFourthWeight_nonneg n)

theorem vonMangoldtSelfConv_sq_sub_two_mul_squareConv_eq_zero_of_prime
    {p : ℕ} (hp : p.Prime) :
    ((Λ * Λ) p) ^ 2 - 2 * (vonMangoldtSquare * vonMangoldtSquare) p = 0 := by
  rw [← pow_one p,
    GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow hp (by omega),
    vonMangoldtSquare_mul_self_prime_pow hp (by omega)]
  norm_num

theorem abs_vonMangoldtSelfConvSquareCorrection_le_proper (N : ℕ) :
    |vonMangoldtSelfConvSquareCorrection N| ≤
      properPrimePowerLogFourthHarmonicSum N := by
  rw [vonMangoldtSelfConvSquareCorrection]
  calc
    |∑ k ∈ Finset.Icc 2 N,
        (((Λ * Λ) k) ^ 2 -
          2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| ≤
        ∑ k ∈ Finset.Icc 2 N,
          |(((Λ * Λ) k) ^ 2 -
            2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ {k ∈ Finset.Icc 2 N | IsPrimePow k ∧ ¬ Nat.Prime k},
          |(((Λ * Λ) k) ^ 2 -
            2 * (vonMangoldtSquare * vonMangoldtSquare) k) / (k : ℝ)| := by
      symm
      apply Finset.sum_subset
        (Finset.filter_subset (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)
          (Finset.Icc 2 N))
      intro k hk hknot
      have hkIcc := Finset.mem_Icc.mp hk
      by_cases hpp : IsPrimePow k
      · have hkprime : Nat.Prime k := by
          by_contra hnotprime
          exact hknot (Finset.mem_filter.mpr ⟨hk, hpp, hnotprime⟩)
        rw [vonMangoldtSelfConv_sq_sub_two_mul_squareConv_eq_zero_of_prime hkprime,
          zero_div, abs_zero]
      · have heq := vonMangoldtSelfConv_sq_eq_two_mul_squareConv_of_not_isPrimePow
          k (by omega) hpp
        have hnum : ((Λ * Λ) k) ^ 2 -
            2 * (vonMangoldtSquare * vonMangoldtSquare) k = 0 :=
          sub_eq_zero.mpr heq
        rw [hnum, zero_div, abs_zero]
    _ ≤ properPrimePowerLogFourthHarmonicSum N := by
      rw [properPrimePowerLogFourthHarmonicSum]
      apply Finset.sum_le_sum
      intro k hk
      have hpp : IsPrimePow k := (Finset.mem_filter.mp hk).2.1
      have hkpos : (0 : ℝ) < k := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)
      rw [abs_div, abs_of_pos hkpos]
      exact div_le_div_of_nonneg_right
        (abs_vonMangoldtSelfConv_sq_sub_two_mul_squareConv_le_of_isPrimePow hpp)
        hkpos.le

/-- Prime-power correction is uniformly bounded in the cutoff. -/
theorem abs_vonMangoldtSelfConvSquareCorrection_le_tsum (N : ℕ) :
    |vonMangoldtSelfConvSquareCorrection N| ≤
      ∑' n : ℕ, properPrimePowerLogFourthWeight n :=
  (abs_vonMangoldtSelfConvSquareCorrection_le_proper N).trans
    (properPrimePowerLogFourthHarmonicSum_le_tsum N)

end RHTower.Sieve
