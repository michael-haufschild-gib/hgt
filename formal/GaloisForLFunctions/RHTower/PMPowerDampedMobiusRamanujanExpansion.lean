import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmallDampingVariance
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

theorem pm_ramanujan_sum_divisors {n : ℕ} (hn : 0 < n) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ d.divisors, d4BMRamanujanNaturalCoefficient n q) =
      if d ∣ n then (d : ℂ) else 0 := by
  have hm : d4BMMoebiusArithmeticC = (moebius : ArithmeticFunction ℂ) := by
    ext q
    rfl
  simp_rw [d4BMRamanujanNaturalCoefficient_eq_convolution hn]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, mul_assoc, hm,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  simp [d4BMRamanujanDivisorSeed, hd.ne']

theorem norm_pm_ramanujan_le_divisor_mass {n q : ℕ} (hn : 0 < n) :
    ‖d4BMRamanujanNaturalCoefficient n q‖ ≤ ∑ d ∈ n.divisors, (d : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [d4BMRamanujanNaturalCoefficient]
    exact Finset.sum_nonneg fun d hd => Nat.cast_nonneg d
  rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hq]
  calc
    _ ≤ ∑ d ∈ (n.gcd q).divisors, ‖(d : ℂ) * (moebius (q/d) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (n.gcd q).divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      have hmu : |(moebius (q/d) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q/d))
      simpa using mul_le_mul_of_nonneg_left hmu (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    _ ≤ ∑ d ∈ n.divisors, (d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left _ _), hn.ne'⟩
      · intro d hd hnot
        exact Nat.cast_nonneg d

def pmPowerDampedRamanujanWeight (ε : ℝ) (q : ℕ) : ℂ :=
  ∑' m : ℕ, pmPowerDampedMobiusCoeff ε (q*m) / ((q*m : ℕ) : ℂ)

theorem pmPowerDampedRamanujanWeight_one {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedRamanujanWeight ε 1 = pmPowerDampedDivisorDensity ε := by
  simp only [pmPowerDampedRamanujanWeight, one_mul]
  exact (pmPowerDampedDivisorDensity_eq_tsum hε).symm

theorem norm_pmPowerDampedMobiusCoeff_div_le (ε : ℝ) (k : ℕ) :
    ‖pmPowerDampedMobiusCoeff ε k / (k : ℂ)‖ ≤ 1/(k : ℝ)^(1+ε) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pmPowerDampedMobiusCoeff_zero]
    simp only [Nat.cast_zero, zero_div, norm_zero]
    positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmu : |(moebius k : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  rw [norm_div, pmPowerDampedMobiusCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg hk0.le _), Complex.norm_natCast]
  calc
    _ ≤ 1*(k : ℝ)^(-ε)/(k : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hk0.le _)) hk0.le
    _ = _ := by
      rw [Real.rpow_add hk0, Real.rpow_one, Real.rpow_neg hk0.le]
      simp only [one_mul, div_eq_mul_inv, mul_inv_rev]

def pmPowerDampedRamanujanPair (ε : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℂ :=
  pmPowerDampedMobiusCoeff ε (p.1*p.2) / ((p.1*p.2 : ℕ) : ℂ) *
    d4BMRamanujanNaturalCoefficient n p.1

theorem norm_pmPowerDampedRamanujanPair_le (ε : ℝ)
    {n : ℕ} (hn : 0 < n) (p : ℕ × ℕ) :
    ‖pmPowerDampedRamanujanPair ε n p‖ ≤
      (1/(p.1 : ℝ)^(1+ε)) * (1/(p.2 : ℝ)^(1+ε)) *
        (∑ d ∈ n.divisors, (d : ℝ)) := by
  rw [pmPowerDampedRamanujanPair, norm_mul]
  have hw : ‖pmPowerDampedMobiusCoeff ε (p.1*p.2) / ((p.1*p.2 : ℕ) : ℂ)‖ ≤
      (1/(p.1 : ℝ)^(1+ε)) * (1/(p.2 : ℝ)^(1+ε)) := by
    calc
      _ ≤ 1/((p.1*p.2 : ℕ) : ℝ)^(1+ε) := norm_pmPowerDampedMobiusCoeff_div_le ε _
      _ = _ := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  exact mul_le_mul hw (norm_pm_ramanujan_le_divisor_mass hn)
    (norm_nonneg _) (by positivity)

theorem summable_pmPowerDampedRamanujanPair {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) : Summable (pmPowerDampedRamanujanPair ε n) := by
  let f : ℕ → ℝ := fun q => 1/(q : ℝ)^(1+ε)
  let C : ℝ := ∑ d ∈ n.divisors, (d : ℝ)
  have hf : Summable f := (Real.summable_one_div_nat_rpow (p := 1+ε)).mpr (by linarith)
  have hf0 : ∀ q, 0 ≤ f q := fun q => by dsimp [f]; positivity
  have hp : Summable (fun p : ℕ × ℕ => f p.1 * f p.2) :=
    hf.mul_of_nonneg hf hf0 hf0
  have hmajor : Summable (fun p : ℕ × ℕ => f p.1 * f p.2 * C) := hp.mul_right C
  have hnorm : Summable (fun p : ℕ × ℕ => ‖pmPowerDampedRamanujanPair ε n p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (norm_pmPowerDampedRamanujanPair_le ε hn) hmajor
  exact hnorm.of_norm

theorem pmPowerDampedRamanujanPair_fiber_sum (ε : ℝ) {n : ℕ} (hn : 0 < n) (d : ℕ) :
    (∑' p : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {d},
      pmPowerDampedRamanujanPair ε n p) =
        if d ∈ n.divisors then pmPowerDampedMobiusCoeff ε d else 0 := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : ∀ p : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {0},
        pmPowerDampedRamanujanPair ε n p = 0 := by
      intro p
      have hp : p.val.1*p.val.2 = 0 := p.property
      simp [pmPowerDampedRamanujanPair, hp, pmPowerDampedMobiusCoeff_zero]
    simp [hz]
  rw [show (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {d} =
      (d.divisorsAntidiagonal : Set (ℕ × ℕ)) by ext p; simp [hd.ne'],
    Finset.tsum_subtype']
  have hs : (∑ p ∈ d.divisorsAntidiagonal, pmPowerDampedRamanujanPair ε n p) =
      (pmPowerDampedMobiusCoeff ε d/(d : ℂ)) *
        (∑ q ∈ d.divisors, d4BMRamanujanNaturalCoefficient n q) := by
    calc
      _ = ∑ p ∈ d.divisorsAntidiagonal,
          (pmPowerDampedMobiusCoeff ε d/(d : ℂ)) * d4BMRamanujanNaturalCoefficient n p.1 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [pmPowerDampedRamanujanPair, (Nat.mem_divisorsAntidiagonal.mp hp).1]
      _ = _ := by
        rw [← Finset.mul_sum,
          Nat.sum_divisorsAntidiagonal (fun a b => d4BMRamanujanNaturalCoefficient n a)]
  rw [hs, pm_ramanujan_sum_divisors hn hd]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, if_pos (Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩)]
    exact div_mul_cancel₀ _ (by exact_mod_cast hd.ne' : (d : ℂ) ≠ 0)
  · simp [Nat.mem_divisors, hdn]

theorem tsum_pmPowerDampedRamanujanPair {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    (∑' p : ℕ × ℕ, pmPowerDampedRamanujanPair ε n p) =
      (pmPowerDampedDivisorCoeff ε n : ℂ) := by
  classical
  have hf := (summable_pmPowerDampedRamanujanPair hε hn).hasSum.tsum_fiberwise
    (fun p : ℕ × ℕ => p.1*p.2)
  calc
    _ = ∑' d : ℕ, if d ∈ n.divisors then pmPowerDampedMobiusCoeff ε d else 0 := by
      rw [← hf.tsum_eq]
      exact tsum_congr (pmPowerDampedRamanujanPair_fiber_sum ε hn)
    _ = _ := by
      rw [tsum_eq_sum (s := n.divisors)]
      · rw [pmPowerDampedDivisorCoeff, Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos hd]
        rfl
      · intro d hd
        simp only [if_neg hd]

theorem pmPowerDampedDivisorCoeff_eq_ramanujan {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    (pmPowerDampedDivisorCoeff ε n : ℂ) = ∑' q : ℕ,
      pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q := by
  rw [← tsum_pmPowerDampedRamanujanPair hε hn,
    (summable_pmPowerDampedRamanujanPair hε hn).tsum_prod]
  apply tsum_congr
  intro q
  exact tsum_mul_right (a := d4BMRamanujanNaturalCoefficient n q)
    (f := fun m : ℕ => pmPowerDampedMobiusCoeff ε (q*m) / ((q*m : ℕ) : ℂ))

theorem summable_pmPowerDampedRamanujanExpansion {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    Summable (fun q : ℕ =>
      pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q) := by
  have h := (summable_pmPowerDampedRamanujanPair hε hn).prod
  apply h.congr
  intro q
  exact tsum_mul_right (a := d4BMRamanujanNaturalCoefficient n q)
    (f := fun m : ℕ => pmPowerDampedMobiusCoeff ε (q*m) / ((q*m : ℕ) : ℂ))

theorem pmPowerDampedRamanujanWeight_zero (ε : ℝ) :
    pmPowerDampedRamanujanWeight ε 0 = 0 := by
  simp [pmPowerDampedRamanujanWeight, pmPowerDampedMobiusCoeff_zero]

theorem pm_ramanujan_one (n : ℕ) : d4BMRamanujanNaturalCoefficient n 1 = 1 := by
  rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum (by norm_num : 0 < 1)]
  simp

def pmPowerDampedRamanujanCenteredPrefix (ε : ℝ) (Q n : ℕ) : ℂ :=
  ∑ q ∈ Finset.range Q,
    pmPowerDampedRamanujanWeight ε (q+2) * d4BMRamanujanNaturalCoefficient n (q+2)

theorem tendsto_pmPowerDampedRamanujanCenteredPrefix {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun Q : ℕ => pmPowerDampedRamanujanCenteredPrefix ε Q n) atTop
      (𝓝 ((pmPowerDampedCenteredDivisorCoeff ε n : ℝ) : ℂ)) := by
  let f : ℕ → ℂ := fun q =>
    pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q
  have hs : Summable f := summable_pmPowerDampedRamanujanExpansion hε hn
  have ht : Summable (fun q => f (q+2)) := (summable_nat_add_iff 2).mpr hs
  have he := hs.sum_add_tsum_nat_add 2
  have h0 : f 0 = 0 := by simp [f, pmPowerDampedRamanujanWeight_zero]
  have h1 : f 1 = pmPowerDampedDivisorDensity ε := by
    simp [f, pmPowerDampedRamanujanWeight_one hε, pm_ramanujan_one]
  have hv : (∑' q : ℕ, f q) = (pmPowerDampedDivisorCoeff ε n : ℂ) :=
    (pmPowerDampedDivisorCoeff_eq_ramanujan hε hn).symm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, hv] at he
  have heq : (∑' q : ℕ, f (q+2)) = (pmPowerDampedCenteredDivisorCoeff ε n : ℂ) := by
    rw [pmPowerDampedCenteredDivisorCoeff, Complex.ofReal_sub,
      ← pmPowerDampedDivisorDensity_eq_ofReal_re hε]
    linear_combination he
  simpa only [pmPowerDampedRamanujanCenteredPrefix, f, heq] using ht.hasSum.tendsto_sum_nat

def pmPowerDampedRamanujanCumulativePrefix (ε : ℝ) (Q N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, pmPowerDampedRamanujanCenteredPrefix ε Q n

theorem tendsto_pmPowerDampedRamanujanCumulativePrefix {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    Tendsto (fun Q : ℕ => pmPowerDampedRamanujanCumulativePrefix ε Q N) atTop
      (𝓝 ((pmPowerDampedCenteredDivisorPrefix ε N : ℝ) : ℂ)) := by
  rw [pmPowerDampedCenteredDivisorPrefix, Complex.ofReal_sum]
  exact tendsto_finsetSum _ (fun n hn =>
    tendsto_pmPowerDampedRamanujanCenteredPrefix hε (by have := (Finset.mem_Icc.mp hn).1; omega))

def pmPowerDampedRamanujanPrefixEnergy (ε : ℝ) (Q T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T,
    ‖pmPowerDampedRamanujanCumulativePrefix ε Q n‖^2 / ((n : ℝ)*((n : ℝ)+1))

theorem tendsto_pmPowerDampedRamanujanPrefixEnergy {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    Tendsto (fun Q : ℕ => pmPowerDampedRamanujanPrefixEnergy ε Q T) atTop
      (𝓝 (pmPowerDampedDivisorDiscreteEnergy ε T)) := by
  unfold pmPowerDampedRamanujanPrefixEnergy pmPowerDampedDivisorDiscreteEnergy
  apply tendsto_finsetSum
  intro n hn
  have h := ((tendsto_pmPowerDampedRamanujanCumulativePrefix hε n).norm.pow 2).div_const
    ((n : ℝ)*((n : ℝ)+1))
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem pmPowerDampedFermiSource_memLp_of_ramanujan_budget {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q T : ℕ, pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (pmPowerDampedFermiSource_memLp_iff_discrete_budget hε).mpr
  refine ⟨B, fun T => ?_⟩
  exact le_of_tendsto (tendsto_pmPowerDampedRamanujanPrefixEnergy hε T)
    (Filter.Eventually.of_forall fun Q => hB Q T)

end RHTower
