import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.RHTower.FourthMomentDiagonal
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorCount

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

def pmPowerDampedSecondWeight (ε : ℝ) (p : ℕ) : ℝ :=
  2 * (p : ℝ) ^ (-ε) - ((p : ℝ) ^ (-ε)) ^ 2

def pmPowerDampedSecondCoeff (ε : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.dampedMobius (pmPowerDampedSecondWeight ε)

theorem pmPowerDampedDivisorCoeff_sq (ε : ℝ) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n ^ 2 =
      ∑ d ∈ n.divisors, pmPowerDampedSecondCoeff ε d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (DampedMobius.dampedMobius_mul_zeta (pmPowerDampedSecondWeight ε))
  rw [coe_mul_zeta_apply] at h
  rw [show (∑ d ∈ n.divisors, pmPowerDampedSecondCoeff ε d) =
    DampedMobius.divisorSum (pmPowerDampedSecondWeight ε) n from h]
  by_cases hn : n = 0
  · subst n
    simp [pmPowerDampedDivisorCoeff_zero]
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hn,
    DampedMobius.divisorSum, prodPrimeFactors_apply hn, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  dsimp only [pmPowerDampedSecondWeight]
  ring

theorem abs_pmPowerDampedSecondCoeff_le {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    |pmPowerDampedSecondCoeff ε n| ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-ε) := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hsq : Squarefree n
  · have hmu : |(moebius n : ℝ)| = 1 := by
      exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
    rw [pmPowerDampedSecondCoeff, DampedMobius.dampedMobius, pmul_apply,
      intCoe_apply, prodPrimeFactors_apply hn, abs_mul, hmu, one_mul, Finset.abs_prod]
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (2 * (p : ℝ) ^ (-ε)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact abs_nonneg _
        · intro p hp
          have hp1 : (1 : ℝ) ≤ p := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
          have ht0 := Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)
          have ht1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hε)
          dsimp only [pmPowerDampedSecondWeight]
          rw [abs_of_nonneg (by nlinarith)]
          nlinarith [sq_nonneg ((p : ℝ) ^ (-ε))]
      _ = (2 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (-ε) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        congr 1
        change (∏ p ∈ n.primeFactors, pmNaturalRpowHom ε p) = pmNaturalRpowHom ε n
        simpa only [map_prod] using congrArg (pmNaturalRpowHom ε)
          (Nat.prod_primeFactors_of_squarefree hsq)
      _ = _ := by
        rw [Sieve.card_divisors_of_squarefree_squarefreeDivisorCount hsq hn]
        push_cast
        rfl
  · simp [pmPowerDampedSecondCoeff, DampedMobius.dampedMobius, pmul_apply,
      intCoe_apply, moebius_eq_zero_of_not_squarefree hsq,
      mul_nonneg (Nat.cast_nonneg n.divisors.card) (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

theorem summable_pmPowerDampedSecondCoeff_div {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => pmPowerDampedSecondCoeff ε n / (n : ℝ)) := by
  apply summable_norm_iff.mp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    (summable_divisor_sq_rpow (σ := (1 + ε) / 2) (by linarith))
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc1 : 1 ≤ n.divisors.card := by
    exact Finset.one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  have hc1R : (1 : ℝ) ≤ n.divisors.card := by exact_mod_cast hc1
  have hcsq : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ)^2 := by nlinarith
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnpos]
  calc
    _ ≤ ((n.divisors.card : ℝ) * (n : ℝ)^(-ε)) / n :=
      div_le_div_of_nonneg_right (abs_pmPowerDampedSecondCoeff_le hε.le n) hnpos.le
    _ ≤ ((n.divisors.card : ℝ)^2 * (n : ℝ)^(-ε)) / n := by
      gcongr
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hnpos.ne']
      congr 2
      ring

def pmPowerDampedSecondDensity (ε : ℝ) : ℝ :=
  ∑' n : ℕ, pmPowerDampedSecondCoeff ε n / (n : ℝ)

theorem pmPowerDampedSecondDensity_hasProd {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes =>
      1 - pmPowerDampedSecondWeight ε p / (p : ℕ)) (pmPowerDampedSecondDensity ε) := by
  let a := pmPowerDampedSecondCoeff ε
  have hm := DampedMobius.isMultiplicative_dampedMobius (pmPowerDampedSecondWeight ε)
  have h1 : a 1 / ((1 : ℕ) : ℝ) = 1 := by
    simpa [a, pmPowerDampedSecondCoeff] using hm.map_one
  have hmul {m n : ℕ} (h : m.Coprime n) :
      a (m*n) / ((m*n : ℕ) : ℝ) = (a m / (m : ℝ)) * (a n / (n : ℝ)) := by
    rw [show a (m*n) = a m * a n from hm.map_mul_of_coprime h, Nat.cast_mul]
    ring
  have hp := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} h => hmul h)
    (summable_pmPowerDampedSecondCoeff_div hε).norm (by simp)
  apply hp.congr_fun
  intro p
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · simp [pmPowerDampedSecondCoeff, DampedMobius.dampedMobius_apply_prime_pow,
      p.property, sub_eq_add_neg, neg_div]
  · have hk0 : k ≠ 0 := fun h => hk (by simp [h])
    have hk1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [pmPowerDampedSecondCoeff, DampedMobius.dampedMobius_apply_prime_pow,
      p.property, hk0, hk1]

theorem pm_divisor_average_eq_tsum (a : ℕ → ℝ)
    {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, a d) / x =
      ∑' d : ℕ, a d * (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) := by
  have hfinite : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, a d) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, a d * ((⌊x / (d : ℝ)⌋ : ℤ) : ℝ) := by
    apply Complex.ofReal_injective
    push_cast
    exact (pm_divisor_floor_sum (fun d => (a d : ℂ)) hx.le le_rfl).symm
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun d hd => ?_)]
  · rw [hfinite, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Int.natCast_floor_eq_floor (div_nonneg hx.le (Nat.cast_nonneg d)), Int.cast_natCast]
    ring
  · by_cases hd0 : d = 0
    · subst d
      simp
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hgt : ⌊x⌋₊ < d := by
      have hh := mt Finset.mem_Icc.mpr hd
      omega
    have hxd : x / (d : ℝ) < 1 := (div_lt_one hdpos).mpr ((Nat.floor_lt hx.le).mp hgt)
    rw [Nat.floor_eq_zero.mpr hxd]
    simp

theorem pm_tendsto_divisor_average {a : ℕ → ℝ}
    (hs : Summable (fun n : ℕ => a n / (n : ℝ))) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, a d) / x)
      atTop (𝓝 (∑' n : ℕ, a n / (n : ℝ))) := by
  let F := fun (x : ℝ) (d : ℕ) => a d * (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x)
  let b := fun d : ℕ => a d / (d : ℝ)
  have hlim (d : ℕ) : Tendsto (fun x => F x d) atTop (𝓝 (b d)) := by
    have he (x : ℝ) : (1 / (d : ℝ)) * x = x / (d : ℝ) := by ring
    have hfloor : Tendsto (fun x : ℝ => ((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) atTop
        (𝓝 (1 / (d : ℝ))) := by
      simpa only [he] using tendsto_nat_floor_mul_div_atTop (a := 1 / (d : ℝ)) (by positivity)
    simpa only [F, b, mul_one_div] using hfloor.const_mul (a d)
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ d : ℕ, ‖F x d‖ ≤ ‖b d‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [F, b]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hn0 : 0 ≤ (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) := by positivity
    have hn1 : (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) ≤ 1 / (d : ℝ) := by
      rw [div_le_iff₀ hx, show (1 / (d : ℝ)) * x = x / (d : ℝ) by ring]
      exact Nat.floor_le (div_nonneg hx.le hdpos.le)
    dsimp only [F, b]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn0,
      norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hdpos]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hn1 (abs_nonneg (a d))
  have h := tendsto_tsum_of_dominated_convergence hs.norm hlim hbound
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (pm_divisor_average_eq_tsum a hx).symm

theorem tendsto_pmPowerDampedDivisorCoeff_sq_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedDivisorCoeff ε n ^ 2) / x)
      atTop (𝓝 (pmPowerDampedSecondDensity ε)) := by
  simpa only [← pmPowerDampedDivisorCoeff_sq, pmPowerDampedSecondDensity] using
    pm_tendsto_divisor_average (a := pmPowerDampedSecondCoeff ε)
      (summable_pmPowerDampedSecondCoeff_div hε)

theorem tendsto_pmPowerDampedDivisorSum_div_real {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => pmPowerDampedDivisorSum ε x / x) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_pmPowerDampedDivisorSum_div hε)
  simpa only [Function.comp_def, ← Complex.ofReal_div, Complex.ofReal_re] using h

theorem pm_centered_square_sum (c : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (c n - a)^2) =
      (∑ n ∈ Finset.Icc 1 N, c n ^ 2) - 2*a*(∑ n ∈ Finset.Icc 1 N, c n) + a^2*N := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]

def pmPowerDampedDivisorVariance (ε : ℝ) : ℝ :=
  pmPowerDampedSecondDensity ε - (pmPowerDampedDivisorDensity ε).re ^ 2

theorem tendsto_pmPowerDampedCenteredDivisorCoeff_sq_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedCenteredDivisorCoeff ε n ^ 2) / x)
      atTop (𝓝 (pmPowerDampedDivisorVariance ε)) := by
  have hf : Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ) / x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_mul] using
      (tendsto_nat_floor_mul_div_atTop (a := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1))
  have h := ((tendsto_pmPowerDampedDivisorCoeff_sq_mean hε).sub
    ((tendsto_pmPowerDampedDivisorSum_div_real hε).const_mul
      (2*(pmPowerDampedDivisorDensity ε).re))).add
        (hf.const_mul ((pmPowerDampedDivisorDensity ε).re ^ 2))
  have he : pmPowerDampedSecondDensity ε -
      2*(pmPowerDampedDivisorDensity ε).re*(pmPowerDampedDivisorDensity ε).re +
        (pmPowerDampedDivisorDensity ε).re ^ 2 * 1 = pmPowerDampedDivisorVariance ε := by
    dsimp only [pmPowerDampedDivisorVariance]
    ring
  rw [he] at h
  convert h using 1
  funext x
  rw [show (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedCenteredDivisorCoeff ε n ^ 2) =
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedDivisorCoeff ε n ^ 2) -
      2*(pmPowerDampedDivisorDensity ε).re*pmPowerDampedDivisorSum ε x +
        (pmPowerDampedDivisorDensity ε).re ^ 2 * ⌊x⌋₊ from
    pm_centered_square_sum (pmPowerDampedDivisorCoeff ε) (pmPowerDampedDivisorDensity ε).re ⌊x⌋₊]
  ring

theorem pmPowerDampedDivisorVariance_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ pmPowerDampedDivisorVariance ε := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_pmPowerDampedCenteredDivisorCoeff_sq_mean hε)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact div_nonneg (Finset.sum_nonneg fun n hn => sq_nonneg _) hx.le

theorem pmPowerDampedSecondWeight_div (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    pmPowerDampedSecondWeight ε p / (p : ℝ) =
      2 * (p : ℝ)^(-1-ε) - (p : ℝ)^(-1-2*ε) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : ((p : ℝ)^(-ε))^2 = (p : ℝ)^(-(2*ε)) := by
    rw [← Real.rpow_natCast ((p : ℝ)^(-ε)) 2, ← Real.rpow_mul hpR.le]
    congr 1
    ring
  rw [pmPowerDampedSecondWeight, sub_div, mul_div_assoc, hsq,
    ← Real.rpow_sub_one hpR.ne', ← Real.rpow_sub_one hpR.ne']
  rw [show -ε-1 = -1-ε by ring, show -(2*ε)-1 = -1-2*ε by ring]

theorem pmPowerDampedSecondDensity_euler {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes =>
      1 - 2 * (p : ℝ)^(-1-ε) + (p : ℝ)^(-1-2*ε))
        (pmPowerDampedSecondDensity ε) := by
  apply (pmPowerDampedSecondDensity_hasProd hε).congr_fun
  intro p
  rw [pmPowerDampedSecondWeight_div ε p.property.pos]
  ring

theorem pmPowerDampedSecondDensity_le_density {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedSecondDensity ε ≤ (pmPowerDampedDivisorDensity ε).re := by
  apply le_of_tendsto_of_tendsto (tendsto_pmPowerDampedDivisorCoeff_sq_mean hε)
    (tendsto_pmPowerDampedDivisorSum_div_real hε)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply div_le_div_of_nonneg_right _ hx.le
  apply Finset.sum_le_sum
  intro n hn
  have h0 := pmPowerDampedDivisorCoeff_nonneg hε.le n
  have h1 := pmPowerDampedDivisorCoeff_le_one hε.le n
  nlinarith

end RHTower
