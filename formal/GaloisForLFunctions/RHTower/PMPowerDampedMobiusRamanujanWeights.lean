import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanExpansion
import GaloisForLFunctions.RHTower.Sieve.CoprimeMoebiusSeries

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

theorem pm_reciprocal_mobius_prime_mul (ε : ℝ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (moebius (p*n) : ℝ) * ((p*n : ℕ) : ℝ)^(-ε) / ((p*n : ℕ) : ℝ) =
      -(1/(p : ℝ)^(1+ε)) *
        (if p ∣ n then 0 else (moebius n : ℝ) * (n : ℝ)^(-ε)/(n : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Sieve.moebius_prime_mul hp, Nat.cast_mul,
    Real.mul_rpow hp0.le (Nat.cast_nonneg n)]
  by_cases hpn : p ∣ n
  · simp [hpn]
  · rw [if_neg hpn, if_neg hpn, Real.rpow_add hp0, Real.rpow_one, Real.rpow_neg hp0.le]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring

theorem pmPowerDampedMobiusCoeff_div_prime_mul (ε : ℝ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    pmPowerDampedMobiusCoeff ε (p*n) / ((p*n : ℕ) : ℂ) =
      -((1/(p : ℝ)^(1+ε) : ℝ) : ℂ) *
        (if p ∣ n then 0 else pmPowerDampedMobiusCoeff ε n/(n : ℂ)) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (pm_reciprocal_mobius_prime_mul ε hp n)
  by_cases hpn : p ∣ n <;> simpa [pmPowerDampedMobiusCoeff, hpn] using h

theorem summable_pmPowerDampedRamanujanWeight_terms {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    Summable (fun m : ℕ => pmPowerDampedMobiusCoeff ε (q*m) / ((q*m : ℕ) : ℂ)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [pmPowerDampedMobiusCoeff_zero]
  · exact (summable_pmPowerDampedDivisorDensity_terms hε).comp_injective
      (fun a b hab => Nat.eq_of_mul_eq_mul_left hq hab)

theorem pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree (ε : ℝ) {q : ℕ}
    (hq : ¬Squarefree q) : pmPowerDampedRamanujanWeight ε q = 0 := by
  have hz (m : ℕ) : pmPowerDampedMobiusCoeff ε (q*m) / ((q*m : ℕ) : ℂ) = 0 := by
    have hqm : ¬Squarefree (q*m) := fun hs => hq hs.of_mul_left
    simp [pmPowerDampedMobiusCoeff, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hqm]
  simp only [pmPowerDampedRamanujanWeight, hz, tsum_zero]

theorem pm_tsum_dvd_multiples (w : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (q : ℕ) :
    (∑' m : ℕ, if p ∣ m then w (q*m) else 0) = ∑' m : ℕ, w ((p*q)*m) := by
  classical
  let F : ℕ → ℂ := fun m => if p ∣ m then w (q*m) else 0
  have hinj : Function.Injective (fun m : ℕ => p*m) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp hab
  have hsupp : Function.support F ⊆ Set.range (fun m : ℕ => p*m) := by
    intro m hm
    rw [Function.mem_support] at hm
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · exact (hm (by simp [F, hpm])).elim
  rw [← hinj.tsum_eq (f := F) hsupp]
  apply tsum_congr
  intro m
  dsimp only [F]
  rw [if_pos (dvd_mul_right p m)]
  congr 1
  ac_rfl

theorem pmPowerDampedRamanujanWeight_prime_recursion {ε : ℝ} (hε : 0 < ε)
    {p q : ℕ} (hp : p.Prime) (hpq : ¬p ∣ q) :
    pmPowerDampedRamanujanWeight ε (p*q) =
      -((1/(p : ℝ)^(1+ε) : ℝ) : ℂ) *
        (pmPowerDampedRamanujanWeight ε q - pmPowerDampedRamanujanWeight ε (p*q)) := by
  classical
  let w : ℕ → ℂ := fun n => pmPowerDampedMobiusCoeff ε n/(n : ℂ)
  have hs : Summable (fun m : ℕ => w (q*m)) :=
    summable_pmPowerDampedRamanujanWeight_terms hε q
  have hd : Summable (fun m : ℕ => if p ∣ m then w (q*m) else 0) := by
    apply Summable.of_norm_bounded hs.norm
    intro m
    split_ifs <;> simp
  have hre : (∑' m : ℕ, if p ∣ m then w (q*m) else 0) =
      pmPowerDampedRamanujanWeight ε (p*q) := pm_tsum_dvd_multiples w hp.pos q
  have ht (m : ℕ) : w ((p*q)*m) = -((1/(p : ℝ)^(1+ε) : ℝ) : ℂ) *
      (w (q*m) - (if p ∣ m then w (q*m) else 0)) := by
    change pmPowerDampedMobiusCoeff ε ((p*q)*m) / (((p*q)*m : ℕ) : ℂ) = _
    rw [mul_assoc, pmPowerDampedMobiusCoeff_div_prime_mul ε hp]
    by_cases hpm : p ∣ m
    · simp [hpm, dvd_mul_of_dvd_right hpm q]
    · have hprod : ¬p ∣ q*m := by
        rw [hp.dvd_mul]
        exact not_or.mpr ⟨hpq, hpm⟩
      simp [hpm, hprod, w]
  change (∑' m : ℕ, w ((p*q)*m)) = _
  rw [tsum_congr ht, tsum_mul_left, hs.tsum_sub hd, hre]
  rfl

theorem pmPowerDampedRamanujanWeight_prime_mul {ε : ℝ} (hε : 0 < ε)
    {p q : ℕ} (hp : p.Prime) (hpq : ¬p ∣ q) :
    pmPowerDampedRamanujanWeight ε (p*q) =
      -pmPowerDampedRamanujanWeight ε q / (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : 1 < (p : ℝ)^(1+ε) := Real.one_lt_rpow hp1 (by linarith)
  have hr0 : (((p : ℝ)^(1+ε) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < (p : ℝ)^(1+ε)))
  have hd : ((((p : ℝ)^(1+ε)-1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hr))
  have h := pmPowerDampedRamanujanWeight_prime_recursion hε hp hpq
  rw [Complex.ofReal_div, Complex.ofReal_one] at h
  apply (eq_div_iff hd).mpr
  push_cast
  field_simp [hr0] at h
  linear_combination h

def pmPowerDampedRamanujanDenominator (ε : ℝ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, ((p : ℝ)^(1+ε)-1)

theorem pmPowerDampedRamanujanDenominator_pos {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    0 < pmPowerDampedRamanujanDenominator ε q := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith))

theorem pmPowerDampedRamanujanDenominator_prime_mul (ε : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q ≠ 0) (hpq : ¬p ∣ q) :
    pmPowerDampedRamanujanDenominator ε (p*q) =
      ((p : ℝ)^(1+ε)-1) * pmPowerDampedRamanujanDenominator ε q := by
  have hnot : p ∉ q.primeFactors := fun h => hpq (Nat.dvd_of_mem_primeFactors h)
  simp only [pmPowerDampedRamanujanDenominator, Nat.primeFactors_mul hp.ne_zero hq,
    hp.primeFactors, Finset.singleton_union, Finset.prod_insert hnot]

theorem pmPowerDampedRamanujanWeight_eq_euler (ε : ℝ) (hε : 0 < ε) (q : ℕ) :
    pmPowerDampedRamanujanWeight ε q =
      pmPowerDampedDivisorDensity ε * (moebius q : ℂ) /
        (pmPowerDampedRamanujanDenominator ε q : ℂ) := by
  classical
  induction q using induction_on_primes with
  | zero => simp [pmPowerDampedRamanujanWeight_zero]
  | one => simp [pmPowerDampedRamanujanWeight_one hε, pmPowerDampedRamanujanDenominator]
  | prime_mul p q hp ih =>
    by_cases hq : q = 0
    · subst q
      simp [pmPowerDampedRamanujanWeight_zero]
    by_cases hpq : p ∣ q
    · have hns : ¬Squarefree (p*q) := fun hs =>
        (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hpq
      rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hns,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
      simp
    · have hmu : (moebius (p*q) : ℂ) = -(moebius q : ℂ) := by
        have h := Sieve.moebius_prime_mul (e := q) hp
        rw [if_neg hpq] at h
        exact_mod_cast h
      rw [pmPowerDampedRamanujanWeight_prime_mul hε hp hpq, ih,
        pmPowerDampedRamanujanDenominator_prime_mul ε hp hq hpq, hmu]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem pmPowerDampedRamanujanWeight_eq_ofReal {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    pmPowerDampedRamanujanWeight ε q =
      (((pmPowerDampedDivisorDensity ε).re * (moebius q : ℝ) /
        pmPowerDampedRamanujanDenominator ε q : ℝ) : ℂ) := by
  rw [pmPowerDampedRamanujanWeight_eq_euler ε hε,
    pmPowerDampedDivisorDensity_eq_ofReal_re hε]
  push_cast
  rfl

theorem pmPowerDampedDivisorDensity_re_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (pmPowerDampedDivisorDensity ε).re := by
  have hv := pmPowerDampedDivisorVariance_pos hε
  have hγ := pmPowerDampedSecondDensity_le_density hε
  dsimp only [pmPowerDampedDivisorVariance] at hv
  nlinarith [sq_nonneg (pmPowerDampedDivisorDensity ε).re]

theorem pmPowerDampedRamanujanWeight_mobius_re_nonneg {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    0 ≤ (moebius q : ℝ) * (pmPowerDampedRamanujanWeight ε q).re := by
  rw [pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]
  have heq : (moebius q : ℝ) *
      ((pmPowerDampedDivisorDensity ε).re * (moebius q : ℝ) /
        pmPowerDampedRamanujanDenominator ε q) =
      (pmPowerDampedDivisorDensity ε).re * (moebius q : ℝ)^2 /
        pmPowerDampedRamanujanDenominator ε q := by ring
  rw [heq]
  exact div_nonneg
    (mul_nonneg (pmPowerDampedDivisorDensity_re_pos hε).le (sq_nonneg _))
    (pmPowerDampedRamanujanDenominator_pos hε q).le

theorem pm_ramanujan_at_one (q : ℕ) :
    d4BMRamanujanNaturalCoefficient 1 q = (moebius q : ℂ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [d4BMRamanujanNaturalCoefficient]
  · rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hq]
    simp

theorem norm_pmPowerDampedRamanujanWeight {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    ‖pmPowerDampedRamanujanWeight ε q‖ =
      (moebius q : ℝ) * (pmPowerDampedRamanujanWeight ε q).re := by
  by_cases hq : Squarefree q
  · have hsq : (moebius q : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
    have habs : |(moebius q : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hq
    have hprod : (moebius q : ℝ) *
        ((pmPowerDampedDivisorDensity ε).re * (moebius q : ℝ) /
          pmPowerDampedRamanujanDenominator ε q) =
        (pmPowerDampedDivisorDensity ε).re / pmPowerDampedRamanujanDenominator ε q := by
      calc
        _ = (pmPowerDampedDivisorDensity ε).re * (moebius q : ℝ)^2 /
            pmPowerDampedRamanujanDenominator ε q := by ring
        _ = _ := by rw [hsq, mul_one]
    rw [pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.norm_real,
      Real.norm_eq_abs, Complex.ofReal_re, hprod]
    simp only [abs_div, abs_mul, abs_of_pos (pmPowerDampedDivisorDensity_re_pos hε),
      abs_of_pos (pmPowerDampedRamanujanDenominator_pos hε q), habs, mul_one]
  · rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hq]
    simp

theorem hasSum_norm_pmPowerDampedRamanujanWeight {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun q : ℕ => ‖pmPowerDampedRamanujanWeight ε q‖) 1 := by
  have hs := (summable_pmPowerDampedRamanujanExpansion hε (n := 1) (by norm_num)).hasSum
  have hv := pmPowerDampedDivisorCoeff_eq_ramanujan hε (n := 1) (by norm_num)
  have hc : pmPowerDampedDivisorCoeff ε 1 = 1 := by simp [pmPowerDampedDivisorCoeff]
  rw [hc, Complex.ofReal_one] at hv
  rw [← hv] at hs
  have hr := Complex.hasSum_re hs
  have hfun (q : ℕ) :
      (pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient 1 q).re =
        ‖pmPowerDampedRamanujanWeight ε q‖ := by
    rw [pm_ramanujan_at_one, norm_pmPowerDampedRamanujanWeight hε]
    simp [Complex.mul_re, mul_comm]
  simpa only [Complex.one_re] using hr.congr_fun (fun q => (hfun q).symm)

end RHTower
