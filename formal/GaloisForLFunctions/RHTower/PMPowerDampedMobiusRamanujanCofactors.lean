import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanWeights
import GaloisForLFunctions.RHTower.EulerDeletionRemainderMobiusInversion

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

theorem pm_weighted_divisor_antidiagonal_swap (A : ℕ → ℂ) (F : ℕ → ℕ → ℂ) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, A q * ∑ x ∈ q.divisorsAntidiagonal, F x.1 x.2) =
      ∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q/d), A (d*m) * F d m := by
  rw [← Sieve.sum_Icc_divisorsAntidiagonal_swap (fun d m => A (d*m) * F d m) Q]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]

theorem pm_ramanujan_eq_antidiagonal {n : ℕ} (hn : 0 < n) (q : ℕ) :
    d4BMRamanujanNaturalCoefficient n q =
      ∑ x ∈ q.divisorsAntidiagonal,
        (if x.1 ∣ n then (x.1 : ℂ) else 0) * (moebius x.2 : ℂ) := by
  rw [d4BMRamanujanNaturalCoefficient_eq_convolution hn, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hx0 : x.1 ≠ 0 := by
    have hm := Nat.mem_divisorsAntidiagonal.mp hx
    intro hz
    simp only [hz, zero_mul] at hm
    exact hm.2 hm.1.symm
  simp [d4BMRamanujanDivisorSeed, d4BMMoebiusArithmeticC, moebiusCoeffC, hx0]

def pmPowerDampedRamanujanCofactor (ε : ℝ) (Q d : ℕ) : ℂ :=
  (d : ℂ) * ∑ m ∈ Finset.Icc 1 (Q/d),
    (moebius m : ℂ) * pmPowerDampedRamanujanWeight ε (d*m)

theorem pmPowerDampedRamanujanCofactor_expansion (ε : ℝ) (Q : ℕ)
    {n : ℕ} (hn : 0 < n) :
    (∑ q ∈ Finset.Icc 1 Q,
      pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q) =
      ∑ d ∈ Finset.Icc 1 Q,
        if d ∣ n then pmPowerDampedRamanujanCofactor ε Q d else 0 := by
  simp_rw [pm_ramanujan_eq_antidiagonal hn]
  rw [pm_weighted_divisor_antidiagonal_swap _
    (fun d m => (if d ∣ n then (d : ℂ) else 0) * (moebius m : ℂ)) Q]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn, pmPowerDampedRamanujanCofactor, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  · simp [hdn]

theorem pm_sum_dvd_indicator (N d : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (1 : ℂ) else 0) = (N/d : ℕ) := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp [hset, Nat.Ioc_filter_dvd_card_eq_div]

theorem pmPowerDampedRamanujanCofactor_cumulative (ε : ℝ) (Q N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 Q,
      pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q) =
      ∑ d ∈ Finset.Icc 1 Q,
        pmPowerDampedRamanujanCofactor ε Q d * ((N/d : ℕ) : ℂ) := by
  have h (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :=
    pmPowerDampedRamanujanCofactor_expansion ε Q (n := n) (by have := (Finset.mem_Icc.mp hn).1; omega)
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← pm_sum_dvd_indicator N d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

theorem pm_mobius_antidiagonal_sum (q : ℕ) :
    (∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℂ)) = if q = 1 then 1 else 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun _ m => (moebius m : ℂ)), Nat.sum_div_divisors (f := fun m => (moebius m : ℂ))]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f q)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem pmPowerDampedRamanujanCofactor_density {ε : ℝ} (hε : 0 < ε)
    {Q : ℕ} (hQ : 1 ≤ Q) :
    (∑ d ∈ Finset.Icc 1 Q, pmPowerDampedRamanujanCofactor ε Q d/(d : ℂ)) =
      pmPowerDampedDivisorDensity ε := by
  have hcancel (d : ℕ) (hd : d ∈ Finset.Icc 1 Q) :
      pmPowerDampedRamanujanCofactor ε Q d/(d : ℂ) =
        ∑ m ∈ Finset.Icc 1 (Q/d),
          pmPowerDampedRamanujanWeight ε (d*m) * (moebius m : ℂ) := by
    have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hd).1; omega : d ≠ 0)
    simp [pmPowerDampedRamanujanCofactor, hd0, mul_comm]
  rw [Finset.sum_congr rfl hcancel,
    ← pm_weighted_divisor_antidiagonal_swap _ (fun _ m => (moebius m : ℂ)) Q]
  simp_rw [pm_mobius_antidiagonal_sum]
  simp [Finset.mem_Icc, hQ, pmPowerDampedRamanujanWeight_one hε]

theorem pmPowerDampedRamanujanCenteredPrefix_eq_Icc {ε : ℝ} (hε : 0 < ε)
    (Q n : ℕ) :
    pmPowerDampedRamanujanCenteredPrefix ε Q n =
      (∑ q ∈ Finset.Icc 1 (Q+1),
        pmPowerDampedRamanujanWeight ε q * d4BMRamanujanNaturalCoefficient n q) -
      pmPowerDampedDivisorDensity ε := by
  induction Q with
  | zero => simp [pmPowerDampedRamanujanCenteredPrefix,
      pmPowerDampedRamanujanWeight_one hε, pm_ramanujan_one]
  | succ Q ih =>
    rw [pmPowerDampedRamanujanCenteredPrefix, Finset.sum_range_succ]
    change pmPowerDampedRamanujanCenteredPrefix ε Q n +
      pmPowerDampedRamanujanWeight ε (Q+2) * d4BMRamanujanNaturalCoefficient n (Q+2) = _
    rw [ih, Finset.sum_Icc_succ_top (a := 1) (b := Q+1) (by omega)]
    ring

theorem pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_floor {ε : ℝ}
    (hε : 0 < ε) (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε Q N =
      (∑ d ∈ Finset.Icc 1 (Q+1),
        pmPowerDampedRamanujanCofactor ε (Q+1) d * ((N/d : ℕ) : ℂ)) -
      pmPowerDampedDivisorDensity ε * N := by
  simp only [pmPowerDampedRamanujanCumulativePrefix,
    pmPowerDampedRamanujanCenteredPrefix_eq_Icc hε, Finset.sum_sub_distrib]
  rw [pmPowerDampedRamanujanCofactor_cumulative]
  simp [mul_comm]

theorem pm_nat_div_eq_sub_fract (N d : ℕ) :
    ((N/d : ℕ) : ℂ) = (((N : ℝ)/(d : ℝ) - Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ) := by
  rw [Int.fract, sub_sub_cancel,
    ← Int.natCast_floor_eq_floor (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)),
    Int.cast_natCast, Nat.floor_div_natCast, Nat.floor_natCast]
  norm_cast

theorem pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract {ε : ℝ}
    (hε : 0 < ε) (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε Q N =
      -∑ d ∈ Finset.Icc 1 (Q+1),
        pmPowerDampedRamanujanCofactor ε (Q+1) d *
          ((Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ) := by
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_floor hε]
  simp_rw [pm_nat_div_eq_sub_fract, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast, mul_sub]
  rw [Finset.sum_sub_distrib]
  have he : (∑ d ∈ Finset.Icc 1 (Q+1),
      pmPowerDampedRamanujanCofactor ε (Q+1) d * ((N : ℂ)/(d : ℂ))) =
      pmPowerDampedDivisorDensity ε * N := by
    calc
      _ = (∑ d ∈ Finset.Icc 1 (Q+1),
          pmPowerDampedRamanujanCofactor ε (Q+1) d/(d : ℂ)) * N := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = _ := by rw [pmPowerDampedRamanujanCofactor_density hε (by omega)]
  rw [he]
  ring

theorem summable_pmPowerDampedMobiusCoeff_multiple_pair {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    Summable (fun x : ℕ+ × ℕ+ =>
      ‖pmPowerDampedMobiusCoeff ε (d*((x.1 : ℕ)*x.2)) /
        ((d*((x.1 : ℕ)*x.2) : ℕ) : ℂ)‖) := by
  let a : ℕ+ → ℝ := fun n => 1/(n : ℝ)^(1+ε)
  have ha : Summable a :=
    ((Real.summable_one_div_nat_rpow (p := 1+ε)).mpr (by linarith)).subtype _
  have hmajor := (ha.mul_of_nonneg ha (fun _ => by positivity) (fun _ => by positivity)).mul_left
    (1/(d : ℝ)^(1+ε))
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmajor
  intro x
  refine (norm_pmPowerDampedMobiusCoeff_div_le ε _).trans_eq ?_
  push_cast
  change 1/((d : ℝ)*((x.1 : ℝ)*(x.2 : ℝ)))^(1+ε) = _
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  simp only [a, one_div, mul_inv_rev]
  ring

theorem pmPowerDampedRamanujanWeight_multiples_inversion {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    (∑' m : ℕ, (moebius m : ℂ) * pmPowerDampedRamanujanWeight ε (d*m)) =
      pmPowerDampedMobiusCoeff ε d/(d : ℂ) := by
  let w : ℕ → ℂ := fun n => pmPowerDampedMobiusCoeff ε n/(n : ℂ)
  have h := DeletionMixedRefinement.moebius_multiples_inversion (fun k => w (d*k))
    (summable_pmPowerDampedMobiusCoeff_multiple_pair hε d)
  have hin (m : ℕ+) : (∑' n : ℕ+, w (d*((m : ℕ)*n))) =
      pmPowerDampedRamanujanWeight ε (d*m) := by
    rw [tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => w (d*((m : ℕ)*n)))
      (by simp [w, pmPowerDampedMobiusCoeff_zero])]
    simp only [pmPowerDampedRamanujanWeight, mul_assoc, w]
  simp_rw [hin] at h
  rw [tsum_pnat_eq_tsum_of_eq_zero
    (f := fun m : ℕ => (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)) (by simp)] at h
  simpa only [mul_one] using h

theorem pmPowerDampedRamanujanWeight_mobius_pair {ε : ℝ} (hε : 0 < ε) (d m : ℕ) :
    (moebius d : ℂ) * (moebius m : ℂ) * pmPowerDampedRamanujanWeight ε (d*m) =
      (‖pmPowerDampedRamanujanWeight ε (d*m)‖ : ℂ) := by
  by_cases hdm : Squarefree (d*m)
  · have hmu : (moebius (d*m) : ℂ) = (moebius d : ℂ)*(moebius m : ℂ) := by
      exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_of_squarefree_mul hdm)
    have hreal : (((pmPowerDampedRamanujanWeight ε (d*m)).re : ℝ) : ℂ) =
        pmPowerDampedRamanujanWeight ε (d*m) := by
      rw [pmPowerDampedRamanujanWeight_eq_ofReal hε]
      rfl
    rw [norm_pmPowerDampedRamanujanWeight hε, Complex.ofReal_mul,
      Complex.ofReal_intCast, hreal, hmu]
  · simp [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hdm]

theorem hasSum_norm_pmPowerDampedRamanujanWeight_multiples {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d) :
    HasSum (fun m : ℕ => ‖pmPowerDampedRamanujanWeight ε (d*m)‖)
      ((moebius d : ℝ)^2 * (d : ℝ)^(-ε)/(d : ℝ)) := by
  have hs := (hasSum_norm_pmPowerDampedRamanujanWeight hε).summable.comp_injective
    (fun a b hab => Nat.eq_of_mul_eq_mul_left hd hab)
  have he : ((∑' m : ℕ, ‖pmPowerDampedRamanujanWeight ε (d*m)‖ : ℝ) : ℂ) =
      (moebius d : ℂ) * (pmPowerDampedMobiusCoeff ε d/(d : ℂ)) := by
    rw [Complex.ofReal_tsum]
    simp_rw [← pmPowerDampedRamanujanWeight_mobius_pair hε]
    rw [show (fun m : ℕ => (moebius d : ℂ)*(moebius m : ℂ)*
        pmPowerDampedRamanujanWeight ε (d*m)) =
        (fun m : ℕ => (moebius d : ℂ)*((moebius m : ℂ)*
          pmPowerDampedRamanujanWeight ε (d*m))) by funext m; ring,
      tsum_mul_left, pmPowerDampedRamanujanWeight_multiples_inversion hε]
  have hcast : (moebius d : ℂ) * (pmPowerDampedMobiusCoeff ε d/(d : ℂ)) =
      (((moebius d : ℝ)^2 * (d : ℝ)^(-ε)/(d : ℝ) : ℝ) : ℂ) := by
    simp only [pmPowerDampedMobiusCoeff]
    push_cast
    ring
  have ht : (∑' m : ℕ, ‖pmPowerDampedRamanujanWeight ε (d*m)‖) =
      (moebius d : ℝ)^2 * (d : ℝ)^(-ε)/(d : ℝ) := by
    exact_mod_cast he.trans hcast
  simpa only [Function.comp_def, ht] using hs.hasSum

theorem pmPowerDampedRamanujanCofactor_mobius_re {ε : ℝ} (hε : 0 < ε) (Q d : ℕ) :
    (moebius d : ℝ) * (pmPowerDampedRamanujanCofactor ε Q d).re =
      (d : ℝ) * ∑ m ∈ Finset.Icc 1 (Q/d), ‖pmPowerDampedRamanujanWeight ε (d*m)‖ := by
  have ht (m : ℕ) : (moebius d : ℝ) *
      ((moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)).re =
      ‖pmPowerDampedRamanujanWeight ε (d*m)‖ := by
    have h := congrArg Complex.re (pmPowerDampedRamanujanWeight_mobius_pair hε d m)
    simpa [Complex.mul_re, mul_assoc] using h
  unfold pmPowerDampedRamanujanCofactor
  rw [Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.re_sum]
  rw [mul_left_comm, Finset.mul_sum]
  simp_rw [ht]

theorem norm_pmPowerDampedRamanujanCofactor_le {ε : ℝ} (hε : 0 < ε)
    (Q : ℕ) {d : ℕ} (hd : 0 < d) :
    ‖pmPowerDampedRamanujanCofactor ε Q d‖ ≤ (d : ℝ)^(-ε) := by
  by_cases hsq : Squarefree d
  · have hmu : (moebius d : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    have hmass := hasSum_norm_pmPowerDampedRamanujanWeight_multiples hε hd
    rw [hmu, one_mul] at hmass
    have hbound : (∑ m ∈ Finset.Icc 1 (Q/d), ‖pmPowerDampedRamanujanWeight ε (d*m)‖) ≤
        (d : ℝ)^(-ε)/(d : ℝ) := by
      rw [← hmass.tsum_eq]
      exact hmass.summable.sum_le_tsum _ (fun _ _ => norm_nonneg _)
    have htri : ‖∑ m ∈ Finset.Icc 1 (Q/d),
        (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)‖ ≤
        ∑ m ∈ Finset.Icc 1 (Q/d), ‖pmPowerDampedRamanujanWeight ε (d*m)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      have hmu1 : ‖(moebius m : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
      exact mul_le_of_le_one_left (norm_nonneg _) hmu1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      _ = (d : ℝ) * ‖∑ m ∈ Finset.Icc 1 (Q/d),
          (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m)‖ := by
        simp [pmPowerDampedRamanujanCofactor]
      _ ≤ (d : ℝ) * ((d : ℝ)^(-ε)/(d : ℝ)) :=
        mul_le_mul_of_nonneg_left (htri.trans hbound) hdR.le
      _ = _ := by field_simp
  · have hz (m : ℕ) : pmPowerDampedRamanujanWeight ε (d*m) = 0 :=
      pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε (fun h => hsq h.of_mul_left)
    simpa [pmPowerDampedRamanujanCofactor, hz] using Real.rpow_nonneg (Nat.cast_nonneg d) (-ε)

end RHTower
