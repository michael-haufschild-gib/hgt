import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeReciprocalTail
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# Exact Euler product and sigma-minus-half bound for smooth-prime fractional mass
-/

namespace RHTower.Sieve

open Finset Set
open scoped BigOperators

noncomputable section

/-- Real-power weight restricted exactly to integers supported on primes dividing `r`. -/
def primeSupportedRpowHom (r : ℕ) (alpha : ℝ) : ℕ →* ℝ := by
  classical
  exact
    { toFun := fun n => if primeSupportedOn r n then (n : ℝ) ^ (-alpha) else 0
      map_one' := by simp [primeSupportedOn_one]
      map_mul' := by
        intro m n
        rw [primeSupportedOn_mul_iff]
        by_cases hm : primeSupportedOn r m <;>
          by_cases hn : primeSupportedOn r n <;>
          simp [hm, hn]
        rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }

theorem smoothPrimeThreeQuarterWeight_eq_rpowHom (r n : ℕ) :
    smoothPrimeThreeQuarterWeight r n = primeSupportedRpowHom r (3 / 4) n := by
  classical
  rfl

/-- Chen's squarefree `σ₋₁/₂` factor, in its prime Euler-product form. -/
def squarefreeSigmaNegHalf (r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))

theorem squarefreeSigmaNegHalf_nonneg (r : ℕ) : 0 ≤ squarefreeSigmaNegHalf r := by
  exact Finset.prod_nonneg fun p _ => add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg p) _)

private theorem norm_primeSupportedRpowHom_lt_one
    {r p : ℕ} (hp : p.Prime) {alpha : ℝ} (halpha : 0 < alpha) :
    ‖primeSupportedRpowHom r alpha p‖ < 1 := by
  classical
  by_cases hpr : p ∣ r
  · have hs : primeSupportedOn r p := by
      rw [show p = p ^ 1 by simp, primeSupportedOn_prime_pow_iff hp (by omega)]
      exact hpr
    rw [show primeSupportedRpowHom r alpha p = (p : ℝ) ^ (-alpha) by
      simp [primeSupportedRpowHom, hs], Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  · have hs : ¬ primeSupportedOn r p := by
      intro hs
      have := (primeSupportedOn_prime_pow_iff hp (by omega : 1 ≤ 1)).mp (by simpa using hs)
      exact hpr this
    simp [primeSupportedRpowHom, hs]

theorem smoothPrimeThreeQuarterMass_eq_primesBelow_prod {r : ℕ} (hr : 0 < r) :
    smoothPrimeThreeQuarterMass r =
      ∏ p ∈ (r + 1).primesBelow,
        (1 - primeSupportedRpowHom r (3 / 4) p)⁻¹ := by
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := primeSupportedRpowHom r (3 / 4))
      (fun {_} hp => norm_primeSupportedRpowHom_lt_one hp (by norm_num)) (r + 1)
  have hsubtype :
      (∑' n : (r + 1).smoothNumbers, primeSupportedRpowHom r (3 / 4) (n : ℕ)) =
        ∏ p ∈ (r + 1).primesBelow,
          (1 - primeSupportedRpowHom r (3 / 4) p)⁻¹ := heuler.2.tsum_eq
  rw [_root_.tsum_subtype] at hsubtype
  have hindicator :
      ((r + 1).smoothNumbers : Set ℕ).indicator
          (fun n : ℕ => primeSupportedRpowHom r (3 / 4) n) =
        fun n : ℕ => primeSupportedRpowHom r (3 / 4) n := by
    funext n
    by_cases hs : primeSupportedOn r n
    · have hmem := primeSupportedOn_mem_smoothNumbers hr hs
      simp [Set.indicator, hmem]
    · have hz : primeSupportedRpowHom r (3 / 4) n = 0 := by
        simp [primeSupportedRpowHom, hs]
      by_cases hmem : n ∈ (r + 1).smoothNumbers
      · simp [Set.indicator, hmem, hz]
      · simp [Set.indicator, hmem, hz]
  rw [hindicator] at hsubtype
  rw [smoothPrimeThreeQuarterMass]
  convert hsubtype using 1
  apply tsum_congr
  intro n
  exact smoothPrimeThreeQuarterWeight_eq_rpowHom r n

private theorem primeFactors_subset_primesBelow_succ {r : ℕ} (hr : 0 < r) :
    r.primeFactors ⊆ (r + 1).primesBelow := by
  intro p hp
  rw [Nat.mem_primesBelow]
  have hdata := Nat.mem_primeFactors.mp hp
  exact ⟨by
    have hple : p ≤ r := Nat.le_of_dvd hr hdata.2.1
    omega, hdata.1⟩

theorem smoothPrimeThreeQuarterMass_eq_primeFactors_prod {r : ℕ} (hr : 0 < r) :
    smoothPrimeThreeQuarterMass r =
      ∏ p ∈ r.primeFactors, (1 - (p : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹ := by
  rw [smoothPrimeThreeQuarterMass_eq_primesBelow_prod hr]
  have hprod :
      ∏ p ∈ r.primeFactors, (1 - primeSupportedRpowHom r (3 / 4) p)⁻¹ =
        ∏ p ∈ (r + 1).primesBelow, (1 - primeSupportedRpowHom r (3 / 4) p)⁻¹ := by
    apply Finset.prod_subset (primeFactors_subset_primesBelow_succ hr)
    intro p hpBelow hpNot
    have hp := (Nat.mem_primesBelow.mp hpBelow).2
    have hpr : ¬ p ∣ r := by
      intro hpr
      exact hpNot (Nat.mem_primeFactors.mpr ⟨hp, hpr, Nat.ne_of_gt hr⟩)
    have hs : ¬ primeSupportedOn r p := by
      intro hs
      have h := (primeSupportedOn_prime_pow_iff hp (by omega : 1 ≤ 1)).mp (by simpa using hs)
      exact hpr h
    simp [primeSupportedRpowHom, hs]
  rw [← hprod]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpr := (Nat.mem_primeFactors.mp hp).2.1
  have hs : primeSupportedOn r p := by
    rw [show p = p ^ 1 by simp, primeSupportedOn_prime_pow_iff hprime (by omega)]
    exact hpr
  rw [show primeSupportedRpowHom r (3 / 4) p =
      (p : ℝ) ^ (-(3 / 4 : ℝ)) by simp [primeSupportedRpowHom, hs]]

private theorem prime_threeQuarter_geometric_le_sigma_factor
    {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹ ≤
      (if p < 16 then 4 else 1) * (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let a : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  let b : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  let c : ℝ := (p : ℝ) ^ (-(1 / 4 : ℝ))
  have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have ha0 : 0 ≤ a := Real.rpow_nonneg hpR0.le _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hpR0.le _
  have hc0 : 0 ≤ c := Real.rpow_nonneg hpR0.le _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  by_cases hsmall : p < 16
  · rw [if_pos hsmall]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have ha_le_half : a ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le hpR1 (by norm_num)
    have hp_half_le_two : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    have htwo_half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
      have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      have hinv := (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
        (by norm_num : (0 : ℝ) < 4 / 3)).2 hsqrt
      have hfour : (4 / 3 : ℝ)⁻¹ = 3 / 4 := by norm_num
      rw [hfour] at hinv
      exact hinv
    have ha : a ≤ 3 / 4 := le_trans ha_le_half (le_trans hp_half_le_two htwo_half)
    have hquarter : (1 / 4 : ℝ) ≤ 1 - a := by linarith
    have hinv : (1 - a)⁻¹ ≤ (4 : ℝ) := by
      have hi := (inv_le_inv₀ hden (by norm_num : (0 : ℝ) < 1 / 4)).2 hquarter
      norm_num at hi
      exact hi
    calc
      (1 - a)⁻¹ ≤ 4 := hinv
      _ ≤ 4 * (1 + b) := by nlinarith
  · rw [if_neg hsmall]
    have hp16Nat : 16 ≤ p := Nat.le_of_not_gt hsmall
    have hp16 : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp16Nat
    have hb : b ≤ 1 / 4 := by
      have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 16)
        hp16 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
      norm_num at h
      exact h
    have hc : c ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 16)
        hp16 (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
      norm_num at h
      exact h
    have habc : a = b * c := by
      dsimp [a, b, c]
      rw [← Real.rpow_add hpR0]
      congr 1
      norm_num
    have hcprod : c * (1 + b) ≤ 1 := by
      calc
        c * (1 + b) ≤ (1 / 2 : ℝ) * (1 + 1 / 4) := by
          exact mul_le_mul hc (by linarith) (by positivity) (by positivity)
        _ ≤ 1 := by norm_num
    have haprod : a * (1 + b) ≤ b := by
      rw [habc]
      calc
        b * c * (1 + b) = b * (c * (1 + b)) := by ring
        _ ≤ b * 1 := mul_le_mul_of_nonneg_left hcprod hb0
        _ = b := by ring
    have hone : 1 ≤ (1 - a) * (1 + b) := by nlinarith
    have hdiv : 1 / (1 - a) ≤ 1 + b :=
      (div_le_iff₀ hden).2 (by simpa only [mul_comm] using hone)
    simpa [a, b, one_div] using hdiv

/-- Exact fractional smooth-prime mass is bounded by an absolute constant times Chen's
squarefree `σ₋₁/₂` factor. -/
theorem smoothPrimeThreeQuarterMass_le_sigmaNegHalf {r : ℕ} (hr : 0 < r) :
    smoothPrimeThreeQuarterMass r ≤ (4 : ℝ) ^ 16 * squarefreeSigmaNegHalf r := by
  rw [smoothPrimeThreeQuarterMass_eq_primeFactors_prod hr]
  calc
    (∏ p ∈ r.primeFactors, (1 - (p : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) ≤
        ∏ p ∈ r.primeFactors,
          ((if p < 16 then 4 else 1) *
            (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hlt : (p : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (by norm_num)
        exact inv_nonneg.mpr (sub_nonneg.mpr hlt.le)
      · intro p hp
        exact prime_threeQuarter_geometric_le_sigma_factor
          (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ r.primeFactors, (if p < 16 then (4 : ℝ) else 1)) *
          squarefreeSigmaNegHalf r := by
      rw [squarefreeSigmaNegHalf, Finset.prod_mul_distrib]
    _ ≤ (4 : ℝ) ^ 16 * squarefreeSigmaNegHalf r := by
      apply mul_le_mul_of_nonneg_right _ (squarefreeSigmaNegHalf_nonneg r)
      have hcorr :
          (∏ p ∈ r.primeFactors, (if p < 16 then (4 : ℝ) else 1)) =
            (4 : ℝ) ^ (r.primeFactors.filter (fun p => p < 16)).card := by
        rw [← Finset.prod_filter]
        simp
      rw [hcorr]
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
      calc
        (r.primeFactors.filter (fun p => p < 16)).card ≤ (Finset.range 16).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_range]
          exact (Finset.mem_filter.mp hp).2
        _ = 16 := by simp

end

end RHTower.Sieve
