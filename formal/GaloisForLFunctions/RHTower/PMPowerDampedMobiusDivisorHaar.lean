import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteSmoothSource
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree
import Mathlib.Analysis.Normed.Group.Tannery

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

def pmPowerDampedDivisorCoeff (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (moebius d : ℝ) * (d : ℝ) ^ (-ε)

theorem pmPowerDampedDivisorCoeff_zero (ε : ℝ) : pmPowerDampedDivisorCoeff ε 0 = 0 := by
  simp [pmPowerDampedDivisorCoeff]

theorem pmPowerDampedDivisorCoeff_one (ε : ℝ) : pmPowerDampedDivisorCoeff ε 1 = 1 := by
  simp [pmPowerDampedDivisorCoeff]

theorem pm_dampedMobius_rpow (ε : ℝ) (n : ℕ) :
    DampedMobius.dampedMobius (fun p => (p : ℝ) ^ (-ε)) n =
      (moebius n : ℝ) * (n : ℝ) ^ (-ε) := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hsq : Squarefree n
  · rw [DampedMobius.dampedMobius, pmul_apply, intCoe_apply, prodPrimeFactors_apply hn]
    congr 1
    change (∏ p ∈ n.primeFactors, pmNaturalRpowHom ε p) = pmNaturalRpowHom ε n
    simpa only [map_prod] using congrArg (pmNaturalRpowHom ε) (Nat.prod_primeFactors_of_squarefree hsq)
  · simp [DampedMobius.dampedMobius, pmul_apply, intCoe_apply,
      moebius_eq_zero_of_not_squarefree hsq]

theorem pmPowerDampedDivisorCoeff_eq_divisorSum (ε : ℝ) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n = DampedMobius.divisorSum (fun p => (p : ℝ) ^ (-ε)) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (DampedMobius.dampedMobius_mul_zeta (fun p => (p : ℝ) ^ (-ε)))
  simpa only [coe_mul_zeta_apply, pm_dampedMobius_rpow, pmPowerDampedDivisorCoeff] using h

theorem pmPowerDampedDivisorCoeff_eq_prod (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    pmPowerDampedDivisorCoeff ε n = ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-ε)) := by
  rw [pmPowerDampedDivisorCoeff_eq_divisorSum, DampedMobius.divisorSum, prodPrimeFactors_apply hn]

theorem pmPowerDampedDivisorCoeff_pos {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) :
    0 < pmPowerDampedDivisorCoeff ε n := by
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hn]
  apply Finset.prod_pos
  intro p hp
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (by linarith)

theorem pmPowerDampedDivisorCoeff_nonneg {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ pmPowerDampedDivisorCoeff ε n := by
  rw [pmPowerDampedDivisorCoeff_eq_divisorSum]
  apply DampedMobius.divisorSum_nonneg
  intro p hp
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le) (by linarith)

theorem pmPowerDampedDivisorCoeff_le_one {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    pmPowerDampedDivisorCoeff ε n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [pmPowerDampedDivisorCoeff_zero]
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hn]
  apply Finset.prod_le_one
  · intro p hp
    apply sub_nonneg.mpr
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le) (by linarith)
  · intro p hp
    linarith [Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)]

def pmPowerDampedDivisorSum (ε x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedDivisorCoeff ε n

theorem pmPowerDampedDivisorSum_eq_floor_sum (ε : ℝ) {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    (pmPowerDampedDivisorSum ε x : ℂ) =
      ∑ d ∈ Finset.Icc 1 N, pmPowerDampedMobiusCoeff ε d * (⌊x / (d : ℝ)⌋ : ℂ) := by
  rw [pm_divisor_floor_sum _ hx hN]
  simp only [pmPowerDampedDivisorSum, pmPowerDampedDivisorCoeff, pmPowerDampedMobiusCoeff,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]

theorem pmPowerDampedFermiSource_eq_divisor_counts (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedFermiSource ε t = (pmPowerDampedDivisorSum ε (1 / t) : ℂ) -
      2 * (pmPowerDampedDivisorSum ε (1 / (2 * t)) : ℂ) := by
  have hhalf : ⌊1 / (2 * t)⌋₊ ≤ ⌊1 / t⌋₊ := by
    apply Nat.floor_mono
    exact one_div_le_one_div_of_le ht (by linarith)
  rw [pmPowerDampedDivisorSum_eq_floor_sum ε (by positivity) le_rfl,
    pmPowerDampedDivisorSum_eq_floor_sum ε (by positivity) hhalf]
  unfold pmPowerDampedFermiSource
  simp_rw [fermiNymanGen_eq_floor_difference]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [pmPowerDampedMobiusCoeff]
  push_cast
  ring

def pmPowerDampedDivisorDensity (ε : ℝ) : ℂ := 1 / riemannZeta (1 + (ε : ℂ))

theorem pmPowerDampedMobiusCoeff_term_one (ε : ℝ) (n : ℕ) :
    LSeries.term (pmPowerDampedMobiusCoeff ε) 1 n = pmPowerDampedMobiusCoeff ε n / (n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one]

theorem summable_pmPowerDampedDivisorDensity_terms {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => pmPowerDampedMobiusCoeff ε n / (n : ℂ)) := by
  have hs := pmPowerDampedMobiusCoeff_lSeriesSummable ε (s := 1) (by simpa using hε)
  exact hs.congr (pmPowerDampedMobiusCoeff_term_one ε)

theorem pmPowerDampedDivisorDensity_eq_tsum {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedDivisorDensity ε = ∑' n : ℕ, pmPowerDampedMobiusCoeff ε n / (n : ℂ) := by
  rw [pmPowerDampedDivisorDensity, ← pmPowerDampedMobiusCoeff_lSeries ε (s := 1) (by simpa using hε)]
  exact tsum_congr (pmPowerDampedMobiusCoeff_term_one ε)

theorem pmPowerDampedDivisorSum_div_eq_tsum (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    (pmPowerDampedDivisorSum ε x : ℂ) / (x : ℂ) =
      ∑' d : ℕ, pmPowerDampedMobiusCoeff ε d * ((((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x : ℝ) : ℂ) := by
  have hfloor (d : ℕ) : (⌊x / (d : ℝ)⌋ : ℂ) = ((⌊x / (d : ℝ)⌋₊ : ℕ) : ℂ) := by
    rw [← Int.natCast_floor_eq_floor (div_nonneg hx.le (Nat.cast_nonneg d)), Int.cast_natCast]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun d hd => ?_)]
  · rw [pmPowerDampedDivisorSum_eq_floor_sum ε hx.le le_rfl, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hfloor, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  · by_cases hd0 : d = 0
    · subst d
      simp [pmPowerDampedMobiusCoeff_zero]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hgt : ⌊x⌋₊ < d := by
      have hh := mt Finset.mem_Icc.mpr hd
      omega
    have hxd : x / (d : ℝ) < 1 := (div_lt_one hdpos).mpr ((Nat.floor_lt hx.le).mp hgt)
    rw [Nat.floor_eq_zero.mpr hxd]
    simp

theorem tendsto_pmPowerDampedDivisorSum_div {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => (pmPowerDampedDivisorSum ε x : ℂ) / (x : ℂ)) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε)) := by
  let F := fun (x : ℝ) (d : ℕ) => pmPowerDampedMobiusCoeff ε d *
    ((((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x : ℝ) : ℂ)
  let b := fun d : ℕ => pmPowerDampedMobiusCoeff ε d / (d : ℂ)
  have hlim (d : ℕ) : Tendsto (fun x => F x d) atTop (𝓝 (b d)) := by
    have he (x : ℝ) : (1 / (d : ℝ)) * x = x / (d : ℝ) := by ring
    have hfloor : Tendsto (fun x : ℝ => ((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) atTop
        (𝓝 (1 / (d : ℝ))) := by
      simpa only [he] using tendsto_nat_floor_mul_div_atTop (a := 1 / (d : ℝ)) (by positivity)
    have h := ((Complex.continuous_ofReal.tendsto (1 / (d : ℝ))).comp hfloor).const_mul
      (pmPowerDampedMobiusCoeff ε d)
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, mul_one_div, F, b] using h
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ d : ℕ, ‖F x d‖ ≤ ‖b d‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [F, b, pmPowerDampedMobiusCoeff_zero]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hn0 : 0 ≤ (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) := by positivity
    have hn1 : (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) ≤ 1 / (d : ℝ) := by
      rw [div_le_iff₀ hx, show (1 / (d : ℝ)) * x = x / (d : ℝ) by ring]
      exact Nat.floor_le (div_nonneg hx.le hdpos.le)
    dsimp only [F, b]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0,
      norm_div, Complex.norm_natCast]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hn1 (norm_nonneg (pmPowerDampedMobiusCoeff ε d))
  have h := tendsto_tsum_of_dominated_convergence
    (summable_pmPowerDampedDivisorDensity_terms hε).norm hlim hbound
  rw [← pmPowerDampedDivisorDensity_eq_tsum hε] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (pmPowerDampedDivisorSum_div_eq_tsum ε hx).symm

theorem pmPowerDampedFermiSource_eq_weighted_haar (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedFermiSource ε t = ∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      (pmPowerDampedDivisorCoeff ε n : ℂ) * pmSupportedDyadicHaar ((n : ℝ) * t) := by
  classical
  let K := ⌊1 / t⌋₊
  let L := ⌊1 / (2 * t)⌋₊
  let c := fun n => (pmPowerDampedDivisorCoeff ε n : ℂ)
  have hLK : L ≤ K := Nat.floor_mono (one_div_le_one_div_of_le ht (by linarith))
  have hcond (n : ℕ) : (n : ℝ) * t ≤ 1 / 2 ↔ n ≤ L := by
    rw [Nat.le_floor_iff (by positivity : 0 ≤ 1 / (2 * t)), le_div_iff₀ (by positivity : 0 < 2 * t)]
    constructor <;> intro h <;> nlinarith
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 K) :
      c n * pmSupportedDyadicHaar ((n : ℝ) * t) = c n - 2 * (c n * (if n ≤ L then 1 else 0)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn1 : (n : ℝ) * t ≤ 1 := by
      apply (le_div_iff₀ ht).mp
      exact (Nat.le_floor_iff (by positivity : 0 ≤ 1 / t)).mp (Finset.mem_Icc.mp hn).2
    rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos hn0 ht), if_pos hn1]
    simp only [hcond n]
    ring
  have hfilter : (Finset.Icc 1 K).filter (fun n => n ≤ L) = Finset.Icc 1 L := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hhalf : (∑ n ∈ Finset.Icc 1 K, c n * (if n ≤ L then 1 else 0)) = ∑ n ∈ Finset.Icc 1 L, c n := by
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter]
  rw [pmPowerDampedFermiSource_eq_divisor_counts ε ht]
  simp only [pmPowerDampedDivisorSum, Complex.ofReal_sum]
  change (∑ n ∈ Finset.Icc 1 K, c n) - 2 * (∑ n ∈ Finset.Icc 1 L, c n) = ∑ n ∈ Finset.Icc 1 K, _
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hhalf]

theorem measurable_pmPowerDampedDivisorSum (ε : ℝ) : Measurable (pmPowerDampedDivisorSum ε) := by
  exact (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
    pmPowerDampedDivisorCoeff ε n)).comp Nat.measurable_floor

def pmPowerDampedDivisorRemainder (ε x : ℝ) : ℂ :=
  (pmPowerDampedDivisorSum ε x : ℂ) - pmPowerDampedDivisorDensity ε * (x : ℂ)

def pmPowerDampedCenteredSource (ε t : ℝ) : ℂ := pmPowerDampedDivisorRemainder ε (1 / t)

theorem measurable_pmPowerDampedDivisorRemainder (ε : ℝ) :
    Measurable (pmPowerDampedDivisorRemainder ε) := by
  exact (Complex.measurable_ofReal.comp (measurable_pmPowerDampedDivisorSum ε)).sub
    (measurable_const.mul Complex.measurable_ofReal)

theorem measurable_pmPowerDampedCenteredSource (ε : ℝ) :
    Measurable (pmPowerDampedCenteredSource ε) := by
  exact (measurable_pmPowerDampedDivisorRemainder ε).comp (measurable_const.div measurable_id)

theorem pmPowerDampedFermiSource_eq_centered_difference (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedFermiSource ε t =
      pmPowerDampedCenteredSource ε t - 2 * pmPowerDampedCenteredSource ε (2 * t) := by
  rw [pmPowerDampedFermiSource_eq_divisor_counts ε ht]
  dsimp only [pmPowerDampedCenteredSource, pmPowerDampedDivisorRemainder]
  push_cast
  field_simp
  ring

theorem tendsto_pmPowerDampedDivisorRemainder_div {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => pmPowerDampedDivisorRemainder ε x / (x : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_pmPowerDampedDivisorSum_div hε).sub_const (pmPowerDampedDivisorDensity ε)
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [pmPowerDampedDivisorRemainder]
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp

theorem tendsto_pmPowerDampedCenteredSource_dyadic_boundary {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmPowerDampedCenteredSource ε (t / (2 : ℝ) ^ N) / (2 : ℂ) ^ N)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => (2 : ℝ) ^ N / t) atTop atTop :=
    (tendsto_div_const_atTop_of_pos ht).mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h := ((tendsto_pmPowerDampedDivisorRemainder_div hε).comp hx).div_const (t : ℂ)
  simp only [zero_div] at h
  convert h using 1
  funext N
  dsimp only [Function.comp_def, pmPowerDampedCenteredSource]
  rw [one_div_div]
  push_cast
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp

theorem pmPowerDampedCenteredSource_dyadic_telescope (ε : ℝ) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    pmPowerDampedCenteredSource ε t =
      pmPowerDampedCenteredSource ε (t / (2 : ℝ) ^ N) / (2 : ℂ) ^ N -
        ∑ k ∈ Finset.range N, pmPowerDampedFermiSource ε (t / (2 : ℝ) ^ (k + 1)) / (2 : ℂ) ^ (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := pmPowerDampedFermiSource_eq_centered_difference ε (div_pos ht (by positivity : (0 : ℝ) < 2 ^ (N + 1)))
    have harg : 2 * (t / (2 : ℝ) ^ (N + 1)) = t / (2 : ℝ) ^ N := by
      rw [pow_succ]
      field_simp
    rw [harg] at hstep
    rw [Finset.sum_range_succ, ih]
    rw [hstep, pow_succ]
    field_simp
    ring

theorem tendsto_pmPowerDampedCenteredSource_dyadic_sum {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => -∑ k ∈ Finset.range N,
      pmPowerDampedFermiSource ε (t / (2 : ℝ) ^ (k + 1)) / (2 : ℂ) ^ (k + 1))
      atTop (𝓝 (pmPowerDampedCenteredSource ε t)) := by
  have hconst : Tendsto (fun _ : ℕ => pmPowerDampedCenteredSource ε t) atTop
      (𝓝 (pmPowerDampedCenteredSource ε t)) := tendsto_const_nhds
  have h := hconst.sub (tendsto_pmPowerDampedCenteredSource_dyadic_boundary hε ht)
  simp only [sub_zero] at h
  convert h using 1
  funext N
  rw [pmPowerDampedCenteredSource_dyadic_telescope ε ht N]
  ring

end RHTower
