import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree

/-!
# Positive divisor profile of natural Ramanujan bands

The prime multiplier below is the one obtained on paper from the coprime
squarefree density in the actual band coefficients. This module proves its
exact finite divisor identity, positive weighted summability at every positive
exponent, subpower growth, and finite anchored reciprocal energy.

It does not prove the actual-band asymptotic or control its moving remainder.
Those source and norm statements remain separate mathematical obligations.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Prime multiplier forced by the coprime density of the actual Ramanujan band. -/
def pmRamanujanBandProfilePrime (ε : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) / ((p : ℝ) + 1 - (p : ℝ)^(-ε))

private theorem prime_rpow_bounds {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ)^(-ε) ∧ (p : ℝ)^(-ε) < 1 :=
  ⟨Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)⟩

theorem pmRamanujanBandProfilePrime_complement {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) :
    1 - pmRamanujanBandProfilePrime ε p =
      (1-(p : ℝ)^(-ε))/((p : ℝ)+1-(p : ℝ)^(-ε)) := by
  have hv := prime_rpow_bounds hε hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : (p : ℝ)+1-(p : ℝ)^(-ε) ≠ 0 := ne_of_gt (by linarith)
  unfold pmRamanujanBandProfilePrime
  field_simp [hd]; ring

theorem pmRamanujanBandProfilePrime_complement_pos {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) : 0 < 1-pmRamanujanBandProfilePrime ε p := by
  rw [pmRamanujanBandProfilePrime_complement hε hp]
  have hv := prime_rpow_bounds hε hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact div_pos (by linarith) (by linarith)

theorem pmRamanujanBandProfilePrime_complement_le {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) : 1-pmRamanujanBandProfilePrime ε p ≤ 1/(p : ℝ) := by
  rw [pmRamanujanBandProfilePrime_complement hε hp]
  have hv := prime_rpow_bounds hε hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (by linarith : (0 : ℝ) < p-1) hv.1]

/-- Positive divisor coefficient of the fixed-index band profile. -/
def pmRamanujanBandProfileCoeff (ε : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.divisorSum (pmRamanujanBandProfilePrime ε)

/-- The cumulative profile, before multiplication by its positive band constant. -/
def pmRamanujanBandProfile (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, pmRamanujanBandProfileCoeff ε n

theorem pmRamanujanBandProfileCoeff_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ pmRamanujanBandProfileCoeff ε n := by
  by_cases hn : n=0
  · subst n; simp
  unfold pmRamanujanBandProfileCoeff DampedMobius.divisorSum
  rw [prodPrimeFactors_apply hn]
  exact prod_nonneg fun p hp =>
    (pmRamanujanBandProfilePrime_complement_pos hε (Nat.prime_of_mem_primeFactors hp)).le

theorem pmRamanujanBandProfile_eq_floor (ε : ℝ) (N : ℕ) :
    pmRamanujanBandProfile ε N =
      ∑ d ∈ Icc 1 N, DampedMobius.dampedMobius (pmRamanujanBandProfilePrime ε) d *
        ((N/d : ℕ) : ℝ) := by
  unfold pmRamanujanBandProfile pmRamanujanBandProfileCoeff
  rw [← DampedMobius.dampedMobius_mul_zeta]
  simp_rw [ArithmeticFunction.mul_apply]
  rw [Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun d m => DampedMobius.dampedMobius (pmRamanujanBandProfilePrime ε) d *
      (zeta : ArithmeticFunction ℝ) m) N]
  apply sum_congr rfl
  intro d hd
  trans ∑ m ∈ Icc 1 (N/d), DampedMobius.dampedMobius (pmRamanujanBandProfilePrime ε) d
  · apply sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hm0]
  · simp [mul_comm]

private def profileWeighted (ε δ : ℝ) : ArithmeticFunction ℝ where
  toFun n := pmRamanujanBandProfileCoeff ε n * (n : ℝ)^(-δ)
  map_zero' := by simp

private theorem weighted_nonneg {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (n : ℕ) :
    0 ≤ profileWeighted ε δ n :=
  mul_nonneg (pmRamanujanBandProfileCoeff_nonneg hε n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem weighted_multiplicative (ε δ : ℝ) : (profileWeighted ε δ).IsMultiplicative := by
  constructor
  · simp [profileWeighted, pmRamanujanBandProfileCoeff,
      (DampedMobius.isMultiplicative_divisorSum _).map_one]
  · intro m n hmn
    change DampedMobius.divisorSum (pmRamanujanBandProfilePrime ε) (m*n) *
      ((m*n : ℕ) : ℝ)^(-δ) = _
    rw [(DampedMobius.isMultiplicative_divisorSum _).map_mul_of_coprime hmn]
    simp only [profileWeighted, pmRamanujanBandProfileCoeff, ArithmeticFunction.coe_mk, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private theorem weighted_prime_pow (ε δ : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    profileWeighted ε δ (p^k) =
      (1-pmRamanujanBandProfilePrime ε p)*((p : ℝ)^(-δ))^k := by
  change DampedMobius.divisorSum _ (p^k) * ((p^k : ℕ) : ℝ)^(-δ) = _
  rw [DampedMobius.divisorSum_apply_prime_pow _ hp, if_neg hk, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) (-δ),
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]

private theorem weighted_prime_hasSum (ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => profileWeighted ε δ (p^k))
      (1+(1-pmRamanujanBandProfilePrime ε p)*(p : ℝ)^(-δ)/(1-(p : ℝ)^(-δ))) := by
  let q : ℝ := (p : ℝ)^(-δ)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by linarith)
  have htail := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    ((1-pmRamanujanBandProfilePrime ε p)*q)
  have ht : HasSum (fun k : ℕ => profileWeighted ε δ (p^(k+1)))
      ((1-pmRamanujanBandProfilePrime ε p)*q/(1-q)) := by
    have he : (1-pmRamanujanBandProfilePrime ε p)*q*(1-q)⁻¹ =
        (1-pmRamanujanBandProfilePrime ε p)*q/(1-q) := by ring
    rw [he] at htail
    apply htail.congr_fun
    intro k
    rw [weighted_prime_pow ε δ hp (Nat.succ_ne_zero k), pow_succ]
    dsimp [q]
    ring
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => profileWeighted ε δ (p^k)) 1).mp ht
  simpa only [sum_range_one, pow_zero, (weighted_multiplicative ε δ).map_one, add_comm, q] using h

private theorem weighted_prime_sum_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, profileWeighted ε δ (p^k)) ≤
      Real.exp ((1/(1-(2 : ℝ)^(-δ)))*(p : ℝ)^(-1-δ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2 : (2 : ℝ)^(-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hp2 : (p : ℝ)^(-δ) ≤ (2 : ℝ)^(-δ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have ht : (1-pmRamanujanBandProfilePrime ε p)*(p : ℝ)^(-δ)/(1-(p : ℝ)^(-δ)) ≤
      (1/(1-(2 : ℝ)^(-δ)))*(p : ℝ)^(-1-δ) := by
    calc
      _ ≤ (1/(p : ℝ))*(p : ℝ)^(-δ)/(1-(p : ℝ)^(-δ)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pmRamanujanBandProfilePrime_complement_le hε hp) (by positivity))
          (by linarith)
      _ ≤ (1/(p : ℝ))*(p : ℝ)^(-δ)/(1-(2 : ℝ)^(-δ)) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      _ = _ := by
        rw [show (-1-δ : ℝ) = -1+(-δ) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
        ring
  rw [(weighted_prime_hasSum ε hδ hp).tsum_eq]
  calc
    _ ≤ 1+(1/(1-(2 : ℝ)^(-δ)))*(p : ℝ)^(-1-δ) := by simpa only [add_comm] using add_le_add_left ht 1
    _ ≤ _ := by
      simpa only [add_comm] using
        Real.add_one_le_exp ((1/(1-(2 : ℝ)^(-δ)))*(p : ℝ)^(-1-δ))

theorem summable_pmRamanujanBandProfileCoeff_weighted {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Summable (fun n : ℕ => pmRamanujanBandProfileCoeff ε n*(n : ℝ)^(-δ)) := by
  let C : ℝ := 1/(1-(2 : ℝ)^(-δ))
  have hC : 0 ≤ C := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := -δ)
      (by norm_num) (by linarith)
    exact div_nonneg (by norm_num) (by linarith)
  exact pm_summable_of_multiplicative_local_bound (profileWeighted ε δ)
    (weighted_multiplicative ε δ) (weighted_nonneg hε δ)
    (fun hp => (weighted_prime_hasSum ε hδ hp).summable)
    (fun n => C*(n : ℝ)^(-1-δ))
    (fun n => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    ((Real.summable_nat_rpow.mpr (by linarith : -1-δ < -1)).mul_left C)
    (fun hp => weighted_prime_sum_le hε hδ hp)


theorem pmRamanujanBandProfile_nonneg {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    0 ≤ pmRamanujanBandProfile ε N :=
  sum_nonneg fun n _ => pmRamanujanBandProfileCoeff_nonneg hε n

theorem pmRamanujanBandProfile_one (ε : ℝ) : pmRamanujanBandProfile ε 1 = 1 := by
  simp [pmRamanujanBandProfile, pmRamanujanBandProfileCoeff,
    (DampedMobius.isMultiplicative_divisorSum _).map_one]

/-- The source-derived positive profile is subpower, with no cancellation premise. -/
theorem exists_pmRamanujanBandProfile_subpower {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      pmRamanujanBandProfile ε N ≤ C*(N : ℝ)^δ := by
  let w : ℕ → ℝ := fun n => pmRamanujanBandProfileCoeff ε n*(n : ℝ)^(-δ)
  have hw (n : ℕ) : 0 ≤ w n := weighted_nonneg hε δ n
  have hs : Summable w := summable_pmRamanujanBandProfileCoeff_weighted hε hδ
  refine ⟨∑' n, w n, tsum_nonneg hw, fun N hN => ?_⟩
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ)^δ * w n := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      calc
        pmRamanujanBandProfileCoeff ε n = (n : ℝ)^δ*w n := by
          dsimp only [w]
          rw [mul_left_comm, ← Real.rpow_add hn0]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hn0.le (by exact_mod_cast (mem_Icc.mp hn).2) hδ.le) (hw n)
    _ = (N : ℝ)^δ * ∑ n ∈ Icc 1 N, w n := (mul_sum ..).symm
    _ ≤ (N : ℝ)^δ * ∑' n, w n := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun n _ => hw n)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by ring

/-- The fixed-index profile has finite anchored reciprocal energy. This is not a
bound on the moving actual band remainder. -/
theorem summable_pmRamanujanBandProfile_energy {ε : ℝ} (hε : 0 < ε) :
    Summable (fun N : ℕ => pmRamanujanBandProfile ε N^2 /
      ((N : ℝ)*((N : ℝ)+1))) := by
  obtain ⟨C,hC,hbound⟩ := exists_pmRamanujanBandProfile_subpower hε
    (by norm_num : (0 : ℝ) < 1/4)
  apply Summable.of_norm_bounded
    ((Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).mul_left (C^2))
  intro N
  by_cases hN : N=0
  · subst N
    simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hF := pmRamanujanBandProfile_nonneg hε N
  have hB := hbound N (Nat.one_le_iff_ne_zero.mpr hN)
  have hB0 : 0 ≤ C*(N : ℝ)^(1/4 : ℝ) := mul_nonneg hC (by positivity)
  have hsq : pmRamanujanBandProfile ε N^2 ≤ (C*(N : ℝ)^(1/4 : ℝ))^2 := by
    nlinarith
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc
    _ ≤ (C*(N : ℝ)^(1/4 : ℝ))^2/((N : ℝ)*((N : ℝ)+1)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ ≤ (C*(N : ℝ)^(1/4 : ℝ))^2/(N : ℝ)^2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    _ = C^2 * ((N : ℝ)^(1/2 : ℝ)/(N : ℝ)^(2 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N), Real.rpow_two]
      norm_num
      ring
    _ = _ := by rw [← Real.rpow_sub hN0]; norm_num

end RHTower
