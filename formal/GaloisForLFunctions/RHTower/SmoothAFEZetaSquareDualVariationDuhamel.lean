import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeSourceField
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

/-- The literal square-dual derivative source field is jointly measurable in height and phase. -/
theorem measurable_smoothAFEZetaSquareDualDerivativeSourceField_uncurry
    (T : ℝ) :
    Measurable (Function.uncurry fun r t : ℝ =>
      smoothAFEZetaSquareDualDerivativeSourceField T r t) := by
  unfold smoothAFEZetaSquareDualDerivativeSourceField
  apply Measurable.tsum
  intro n
  unfold smoothAFEZetaSquareDualDerivativeCoefficient
  letI : NeZero (n + 1 : ℂ) := ⟨by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith⟩
  have hphase : Measurable (fun p : ℝ × ℝ =>
      (n + 1 : ℂ) ^ (linePt p.2 - 1)) := by
    exact ((continuous_const_cpow (n + 1 : ℂ)).comp (by
      unfold linePt
      fun_prop)).measurable
  have hderiv : Measurable (fun p : ℝ × ℝ =>
      deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) p.1) :=
    (measurable_deriv _).comp measurable_fst
  exact (measurable_const.mul hphase).mul hderiv

theorem measurable_smoothAFEZetaSquareDualDerivativeSourceField_height
    (T t : ℝ) :
    Measurable (fun r : ℝ =>
      smoothAFEZetaSquareDualDerivativeSourceField T r t) := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using
    (measurable_smoothAFEZetaSquareDualDerivativeSourceField_uncurry T).comp
      (measurable_id.prodMk measurable_const)

/-- On a dyadic height rectangle, the full source derivative field has a uniform bound. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {r t : ℝ},
      4 ≤ N → r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
      ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ≤ C := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_large_power
  have hbase : Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(599 / 400 : ℝ)) < -1 by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ =>
        (n : ℝ) ^ (-(599 / 400 : ℝ))) 1).mpr h
  let S : ℝ := ∑' n : ℕ, (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  refine ⟨3 * K * S, by positivity, ?_⟩
  intro N r t hN hr
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    exact hN4real.trans hr.1
  have hfactor : K * (1 + r) / (N : ℝ) ≤ 3 * K := by
    have hlin : 1 + r ≤ 3 * (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      linarith [hr.2]
    apply (div_le_iff₀ hN0).2
    nlinarith [mul_le_mul_of_nonneg_left hlin hK]
  have hnorm : Summable (fun n : ℕ =>
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖) :=
    summable_norm_smoothAFEZetaSquareDualDerivativeCoefficient hr4 hN0
  have hq : Summable (fun n : ℕ =>
      (3 * K) * (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))) :=
    hbase.mul_left (3 * K)
  have hpoint : ∀ n : ℕ,
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ≤
        (3 * K) * (n + 1 : ℝ) ^ (-(599 / 400 : ℝ)) := by
    intro n
    exact (hcoefficient hr4 hN0).trans (by
      gcongr)
  calc
    ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖
        ≤ ∑' n : ℕ,
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        (3 * K) * (n + 1 : ℝ) ^ (-(599 / 400 : ℝ)) :=
      hnorm.tsum_le_tsum hpoint hq
    _ = 3 * K * S := by
      rw [tsum_mul_left]

theorem integrableOn_normSq_smoothAFEZetaSquareDualDerivativeSourceField_prod_Icc
    {N : ℕ} {a b : ℝ} (hN : 4 ≤ N) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField
          (N : ℝ) p.1 p.2‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ) ×ˢ Set.Icc a b) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ‖smoothAFEZetaSquareDualDerivativeSourceField
        (N : ℝ) p.1 p.2‖ ^ 2) :=
    ((measurable_smoothAFEZetaSquareDualDerivativeSourceField_uncurry
      (N : ℝ)).norm.pow_const 2)
  have hfinite :
      volume (Set.Icc (N : ℝ) (2 * N : ℝ) ×ˢ Set.Icc a b) ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C ^ 2)
    hfinite hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hbound hN hp.1) 2

private theorem tsum_intervalIntegral_of_intervalIntegrable_bound
    {a b : ℝ} {f : ℕ → ℝ → ℂ} {M : ℕ → ℝ}
    (hf : ∀ m, IntervalIntegrable (f m) volume a b)
    (hM : ∀ m, ∀ t ∈ Set.uIoc a b, ‖f m t‖ ≤ M m)
    (hMs : Summable M) :
    (∑' m, ∫ t in a..b, f m t) = ∫ t in a..b, ∑' m, f m t := by
  have hint : ∀ m, Integrable (f m) (volume.restrict (Set.uIoc a b)) :=
    fun m => intervalIntegrable_iff.mp (hf m)
  have hnorm : ∀ m, Integrable (fun t => ‖f m t‖)
      (volume.restrict (Set.uIoc a b)) := fun m => (hint m).norm
  have hconst : ∀ m : ℕ, Integrable (fun _ : ℝ => M m)
      (volume.restrict (Set.uIoc a b)) := by
    intro m
    exact intervalIntegrable_iff.mp intervalIntegrable_const
  have hle : ∀ m, (∫ t in Set.uIoc a b, ‖f m t‖) ≤
      M m * volume.real (Set.uIoc a b) := by
    intro m
    have hmono : (∫ t in Set.uIoc a b, ‖f m t‖) ≤
        ∫ _t in Set.uIoc a b, M m :=
      setIntegral_mono_on (hnorm m) (hconst m) measurableSet_uIoc
        fun t ht => hM m t ht
    rw [setIntegral_const] at hmono
    calc
      (∫ t in Set.uIoc a b, ‖f m t‖) ≤
          volume.real (Set.uIoc a b) • M m := hmono
      _ = M m * volume.real (Set.uIoc a b) := by
        rw [smul_eq_mul]
        ring
  have hsum : Summable fun m => ∫ t in Set.uIoc a b, ‖f m t‖ := by
    refine Summable.of_nonneg_of_le
      (fun m => integral_nonneg fun t => norm_nonneg _) hle ?_
    exact hMs.mul_right _
  have hcore := integral_tsum_of_summable_integral_norm hint hsum
  have hsummable : Summable fun m => ∫ t in Set.uIoc a b, f m t := by
    refine Summable.of_norm_bounded hsum fun m => ?_
    exact norm_integral_le_integral_norm _
  have hsides : ∀ m : ℕ, (∫ t in a..b, f m t) =
      (if a ≤ b then (1 : ℝ) else -1) •
        ∫ t in Set.uIoc a b, f m t := fun m =>
    intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _
  calc
    (∑' m, ∫ t in a..b, f m t) =
        ∑' m, (if a ≤ b then (1 : ℝ) else -1) •
          ∫ t in Set.uIoc a b, f m t := tsum_congr fun m => hsides m
    _ = (if a ≤ b then (1 : ℝ) else -1) •
        ∑' m, ∫ t in Set.uIoc a b, f m t :=
      hsummable.tsum_const_smul _
    _ = (if a ≤ b then (1 : ℝ) else -1) •
        ∫ t in Set.uIoc a b, ∑' m, f m t := by rw [hcore]
    _ = ∫ t in a..b, ∑' m, f m t :=
      (intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _).symm

/-- Literal square-dual source variation between two separated weight heights. -/
def smoothAFEZetaSquareDualVariationSourceField
    (T a u t : ℝ) : ℂ :=
  ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1) *
      (smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T) -
        smoothAFEZetaSquareDualWeight a ((n + 1 : ℝ) * T))

/-- Exact source FTC: separated-height square-dual variation is the height integral of the
phase-faithful derivative source field. -/
theorem smoothAFEZetaSquareDualVariationSourceField_eq_intervalIntegral_derivative
    {N : ℕ} {a u t : ℝ} (hN : 4 ≤ N)
    (ha : a ∈ Set.Icc (N : ℝ) (2 * N : ℝ))
    (hu : u ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) :
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) a u t =
      ∫ r in a..u,
        smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_large_power
  let F : ℕ → ℝ → ℂ := fun n r =>
    smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n
  let M : ℕ → ℝ := fun n =>
    (3 * K) * (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(599 / 400 : ℝ)) < -1 by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ =>
        (n : ℝ) ^ (-(599 / 400 : ℝ))) 1).mpr h
  have hMs : Summable M := hbase.mul_left (3 * K)
  have huIcc : Set.uIcc a u ⊆ Set.Icc (N : ℝ) (2 * N : ℝ) := by
    intro r hr
    rcases Set.mem_uIcc.mp hr with hru | hru
    · exact ⟨ha.1.trans hru.1, hru.2.trans hu.2⟩
    · exact ⟨hu.1.trans hru.1, hru.2.trans ha.2⟩
  have hM : ∀ n, ∀ r ∈ Set.uIoc a u, ‖F n r‖ ≤ M n := by
    intro n r hr
    have hrIcc := huIcc (Set.uIoc_subset_uIcc hr)
    have hr4 : (4 : ℝ) ≤ r := hN4real.trans hrIcc.1
    have hfactor : K * (1 + r) / (N : ℝ) ≤ 3 * K := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hlin : 1 + r ≤ 3 * (N : ℝ) := by linarith [hrIcc.2]
      apply (div_le_iff₀ hN0).2
      nlinarith [mul_le_mul_of_nonneg_left hlin hK]
    exact (hcoefficient hr4 hN0).trans (by
      dsimp only [M]
      gcongr)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    dsimp only [F]
    unfold smoothAFEZetaSquareDualDerivativeCoefficient
    exact (measurable_const.mul measurable_const).mul (measurable_deriv _)
  have hFint : ∀ n, IntervalIntegrable (F n) volume a u := by
    intro n
    rw [intervalIntegrable_iff]
    have hfinite : volume (Set.uIoc a u) ≠ ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := M n)
      hfinite (hFmeas n).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    exact hM n r hr
  have hswap :=
    tsum_intervalIntegral_of_intervalIntegrable_bound hFint hM hMs
  change smoothAFEZetaSquareDualVariationSourceField (N : ℝ) a u t =
    ∫ r in a..u, ∑' n : ℕ, F n r
  rw [← hswap]
  unfold smoothAFEZetaSquareDualVariationSourceField
  apply tsum_congr
  intro n
  let c : ℂ := ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1)
  have hY : 0 < (n + 1 : ℝ) * (N : ℝ) := by positivity
  have hderiv : ∀ r ∈ Set.uIcc a u,
      HasDerivAt
        (fun v : ℝ => c *
          smoothAFEZetaSquareDualWeight v ((n + 1 : ℝ) * (N : ℝ)))
        (F n r) r := by
    intro r hr
    have hw := (hasDerivAt_smoothAFEZetaSquareDualWeight hY r).differentiableAt.hasDerivAt
    simpa only [F, c, smoothAFEZetaSquareDualDerivativeCoefficient,
      mul_assoc] using hw.const_mul c
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hFint n)
  dsimp only [F, c] at hftc ⊢
  simpa [mul_sub] using hftc.symm

/-- The physical diagonal variation is measurable in observation height. -/
theorem measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal
    {N : ℕ} (hN : 4 ≤ N) :
    Measurable (fun t : ℝ =>
      smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t) := by
  unfold smoothAFEZetaSquareDualVariationSourceField
  apply Measurable.tsum
  intro n
  letI : NeZero (n + 1 : ℂ) := ⟨by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith⟩
  have hphase : Measurable (fun t : ℝ =>
      (n + 1 : ℂ) ^ (linePt t - 1)) := by
    exact ((continuous_const_cpow (n + 1 : ℂ)).comp (by
      unfold linePt
      fun_prop)).measurable
  have hY : 0 < (n + 1 : ℝ) * (N : ℝ) := by
    have hN0 : 0 < N := by omega
    positivity
  have hweight : Continuous (fun t : ℝ =>
      smoothAFEZetaSquareDualWeight t ((n + 1 : ℝ) * (N : ℝ))) := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hasDerivAt_smoothAFEZetaSquareDualWeight hY t).continuousAt
  exact (measurable_const.mul hphase).mul
    (hweight.measurable.sub measurable_const)

private theorem normSq_intervalIntegral_le_length_mul_integral_normSq
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ} (hf : Measurable f)
    (hfsq : IntegrableOn (fun x => ‖f x‖ ^ 2) (Set.Ioc a b) volume) :
    ‖∫ x in a..b, f x‖ ^ 2 ≤
      (b - a) * ∫ x in a..b, ‖f x‖ ^ 2 := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hfm : AEStronglyMeasurable (fun x => ‖f x‖) mu :=
    hf.norm.aestronglyMeasurable.restrict
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) mu := hfsq
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) mu := by
    haveI : IsFiniteMeasure mu := ⟨by simp [mu, Real.volume_Ioc]⟩
    simpa only [one_pow] using (integrable_const (μ := mu) (1 : ℝ))
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := mu) hfm aestronglyMeasurable_const hf2 h1
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) hab (f := f)
  have hlen : ∫ _x : ℝ, (1 : ℝ) ^ 2 ∂mu = b - a := by
    simp [mu, hab]
  have hconv : ∀ g : ℝ → ℝ,
      (∫ x in a..b, g x) = ∫ x, g x ∂mu := by
    intro g
    rw [intervalIntegral.integral_of_le hab]
  simp only [mul_one] at hcs
  rw [hlen] at hcs
  calc
    ‖∫ x in a..b, f x‖ ^ 2 ≤ (∫ x in a..b, ‖f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (∫ x, ‖f x‖ ∂mu) ^ 2 := by
      rw [hconv]
    _ ≤ (∫ x, ‖f x‖ ^ 2 ∂mu) * (b - a) := hcs
    _ = (b - a) * ∫ x in a..b, ‖f x‖ ^ 2 := by
      rw [hconv]
      ring

/-- Measurable Duhamel on the literal square-dual source: one dyadic height variation costs one
factor of the dyadic length while retaining the full observation phase. -/
theorem integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_duhamel :
    ∀ {N : ℕ}, 4 ≤ N →
    (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
      ‖smoothAFEZetaSquareDualVariationSourceField
        (N : ℝ) (N : ℝ) t t‖ ^ 2) ≤
      (N : ℝ) * ∫ r in Set.Icc (N : ℝ) (2 * N : ℝ),
        ∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r t‖ ^ 2 := by
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let g : ℝ × ℝ → ℝ := fun p =>
    ‖smoothAFEZetaSquareDualDerivativeSourceField
      (N : ℝ) p.1 p.2‖ ^ 2
  let V : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t
  obtain ⟨C, hC, hDbound⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hNN : (N : ℝ) ∈ S := by
    dsimp only [S]
    constructor <;> linarith
  have hVmeas : Measurable V := by
    dsimp only [V]
    exact measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal hN
  have hVbound : ∀ t ∈ S, ‖V t‖ ≤ C * (N : ℝ) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by simpa [S] using ht
    change ‖smoothAFEZetaSquareDualVariationSourceField
      (N : ℝ) (N : ℝ) t t‖ ≤ C * (N : ℝ)
    rw [smoothAFEZetaSquareDualVariationSourceField_eq_intervalIntegral_derivative
      hN hNN htIcc]
    have hpoint : ∀ r ∈ Set.uIoc (N : ℝ) t,
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ≤ C := by
      intro r hr
      have hr' := Set.uIoc_subset_uIcc hr
      have hrS : r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by
        rcases Set.mem_uIcc.mp hr' with hrt | hrt
        · exact ⟨hrt.1, hrt.2.trans htIcc.2⟩
        · exact ⟨htIcc.1.trans hrt.1, hrt.2.trans (by linarith)⟩
      exact hDbound hN hrS
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [abs_of_nonneg (sub_nonneg.mpr htIcc.1)] at hb
    exact hb.trans (by
      exact mul_le_mul_of_nonneg_left (by linarith [htIcc.2]) hC)
  have hVint : IntegrableOn (fun t => ‖V t‖ ^ 2) S volume := by
    have hfinite : volume S ≠ ⊤ := by
      exact isCompact_Icc.measure_lt_top.ne
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (M := (C * (N : ℝ)) ^ 2) hfinite
      (hVmeas.norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hVbound t ht) 2
  have hgmeas : Measurable g := by
    dsimp only [g]
    exact (measurable_smoothAFEZetaSquareDualDerivativeSourceField_uncurry
      (N : ℝ)).norm.pow_const 2
  have hgprod : IntegrableOn g (S ×ˢ S) volume := by
    dsimp only [g, S]
    exact integrableOn_normSq_smoothAFEZetaSquareDualDerivativeSourceField_prod_Icc hN
  let mu : Measure ℝ := volume.restrict S
  have hgprod' : Integrable g (mu.prod mu) := by
    dsimp only [mu]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    exact hgprod
  have hRint : IntegrableOn
      (fun t : ℝ => (N : ℝ) * ∫ r in S, g (r, t)) S volume := by
    change Integrable (fun t : ℝ => (N : ℝ) * ∫ r, g (r, t) ∂mu) mu
    exact hgprod'.integral_prod_right.const_mul (N : ℝ)
  have hpoint : ∀ t ∈ S,
      ‖V t‖ ^ 2 ≤ (N : ℝ) * ∫ r in S, g (r, t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by simpa [S] using ht
    have hsectionMeas : Measurable (fun r : ℝ =>
        smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t) :=
      measurable_smoothAFEZetaSquareDualDerivativeSourceField_height (N : ℝ) t
    have hsectionFull : IntegrableOn (fun r : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2)
        S volume := by
      have hfinite : volume S ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
      refine MeasureTheory.Measure.integrableOn_of_bounded (M := C ^ 2)
        hfinite (hsectionMeas.norm.pow_const 2).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDbound hN (by simpa [S] using hr)) 2
    have hsectionSub : IntegrableOn (fun r : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2)
        (Set.Ioc (N : ℝ) t) volume :=
      hsectionFull.mono_set (by
        intro r hr
        dsimp only [S]
        exact ⟨hr.1.le, hr.2.trans htIcc.2⟩)
    have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
      htIcc.1 hsectionMeas hsectionSub
    have hmono :
        (∫ r in (N : ℝ)..t,
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2) ≤
        ∫ r in S,
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le htIcc.1]
      refine setIntegral_mono_set hsectionFull
        (Filter.Eventually.of_forall fun r => sq_nonneg _) ?_
      exact Filter.Eventually.of_forall fun r hr => by
        dsimp only [S]
        exact ⟨hr.1.le, hr.2.trans htIcc.2⟩
    have hsub0 : 0 ≤ ∫ r in (N : ℝ)..t,
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall htIcc.1 fun _ => sq_nonneg _
    change ‖smoothAFEZetaSquareDualVariationSourceField
      (N : ℝ) (N : ℝ) t t‖ ^ 2 ≤
        (N : ℝ) * ∫ r in S, g (r, t)
    rw [smoothAFEZetaSquareDualVariationSourceField_eq_intervalIntegral_derivative
      hN hNN htIcc]
    dsimp only [g]
    exact hcs.trans (by
      have hlen : t - (N : ℝ) ≤ (N : ℝ) := by linarith [htIcc.2]
      exact mul_le_mul hlen hmono hsub0 hN0.le)
  have hmono := setIntegral_mono_on hVint hRint measurableSet_Icc hpoint
  calc
    (∫ t in S, ‖V t‖ ^ 2) ≤
        ∫ t in S, (N : ℝ) * ∫ r in S, g (r, t) := hmono
    _ = (N : ℝ) * ∫ t in S, ∫ r in S, g (r, t) := by
      rw [integral_const_mul]
    _ = (N : ℝ) * ∫ r in S, ∫ t in S, g (r, t) := by
      congr 1
      exact (integral_integral_swap hgprod').symm

/-- The literal square-dual height variation has dyadic mean square bounded by the affine
source estimate after measurable Duhamel. -/
theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_dyadic :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualVariationSourceField
          (N : ℝ) (N : ℝ) t t‖ ^ 2) ≤
        (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) *
                ((N : ℝ) / 2)) := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic_logCube
  refine ⟨A, K, hA, hK, ?_⟩
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let B : ℝ :=
    5 * Real.pi * Real.exp 1 *
        (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
      (5 * Real.pi / 2) *
        (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * ((N : ℝ) / 2)
  let g : ℝ × ℝ → ℝ := fun p =>
    ‖smoothAFEZetaSquareDualDerivativeSourceField
      (N : ℝ) p.1 p.2‖ ^ 2
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hH : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hDuhamel :=
    integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_duhamel hN
  have hgprod : IntegrableOn g (S ×ˢ S) volume := by
    dsimp only [g, S]
    exact integrableOn_normSq_smoothAFEZetaSquareDualDerivativeSourceField_prod_Icc hN
  let mu : Measure ℝ := volume.restrict S
  have hgprod' : Integrable g (mu.prod mu) := by
    dsimp only [mu]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    exact hgprod
  have hinnerInt : IntegrableOn (fun r : ℝ => ∫ t in S, g (r, t)) S volume := by
    change Integrable (fun r : ℝ => ∫ t, g (r, t) ∂mu) mu
    exact hgprod'.integral_prod_left
  have hfinite : volume S ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  have hconstInt : IntegrableOn (fun _ : ℝ => B) S volume :=
    integrableOn_const hfinite (by simp)
  have hpoint : ∀ r ∈ S, (∫ t in S, g (r, t)) ≤ B := by
    intro r hr
    have hrIcc : r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by simpa [S] using hr
    have hb := hmv (center := 3 * (N : ℝ) / 2) hN hrIcc hH
    dsimp only [g, S, B]
    have hleft : 3 * (N : ℝ) / 2 - (N : ℝ) / 2 = (N : ℝ) := by ring
    have hright : 3 * (N : ℝ) / 2 + (N : ℝ) / 2 = 2 * (N : ℝ) := by ring
    simpa only [hleft, hright] using hb
  have houter := setIntegral_mono_on hinnerInt hconstInt measurableSet_Icc hpoint
  have hvolume : volume.real S = (N : ℝ) := by
    dsimp only [S]
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith : 0 ≤ (2 * N : ℝ) - (N : ℝ))]
    ring
  have houter' : (∫ r in S, ∫ t in S, g (r, t)) ≤ (N : ℝ) * B := by
    calc
      (∫ r in S, ∫ t in S, g (r, t)) ≤ ∫ _r in S, B := houter
      _ = volume.real S • B := by rw [setIntegral_const]
      _ = (N : ℝ) * B := by rw [hvolume, smul_eq_mul]
  exact hDuhamel.trans (by
    dsimp only [S, g] at houter'
    calc
      (N : ℝ) *
          (∫ r in Set.Icc (N : ℝ) (2 * N : ℝ),
            ∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
              ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2)
          ≤ (N : ℝ) * ((N : ℝ) *
              (5 * Real.pi * Real.exp 1 *
                  (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
                (5 * Real.pi / 2) *
                  (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) *
                    ((N : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left houter' hN0.le
      _ = (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) *
                ((N : ℝ) / 2)) := by ring)

/-- Exponent-normalized source law. The literal square-dual variation contributes only
`N log^3 N + N^(201/200)` to the dyadic fourth-moment scale. -/
theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_logCube_add_rpow :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualVariationSourceField
          (N : ℝ) (N : ℝ) t t‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
            (1 + Real.log (N : ℝ)) ^ 3 +
          (5 * Real.pi / 4) * A * (N : ℝ) ^ (201 / 200 : ℝ) := by
  obtain ⟨A, K, hA, hK, hraw⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_dyadic
  refine ⟨A, K, hA, hK, ?_⟩
  intro N hN
  have hx : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hxpow :
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(399 / 200 : ℝ)) * (N : ℝ) =
        (N : ℝ) ^ (201 / 200 : ℝ) := by
    calc
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(399 / 200 : ℝ)) * (N : ℝ) =
          (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-(399 / 200 : ℝ)) * (N : ℝ) := by
            exact congrArg (fun z : ℝ =>
              z * (N : ℝ) ^ (-(399 / 200 : ℝ)) * (N : ℝ))
              (Real.rpow_natCast (N : ℝ) 2).symm
      _ = (N : ℝ) ^ ((2 : ℝ) + -(399 / 200 : ℝ)) * (N : ℝ) := by
        exact congrArg (fun z : ℝ => z * (N : ℝ))
          (Real.rpow_add hx (2 : ℝ) (-(399 / 200 : ℝ))).symm
      _ = (N : ℝ) ^ (((2 : ℝ) + -(399 / 200 : ℝ)) + 1) := by
        calc
          (N : ℝ) ^ ((2 : ℝ) + -(399 / 200 : ℝ)) * (N : ℝ) =
              (N : ℝ) ^ ((2 : ℝ) + -(399 / 200 : ℝ)) * (N : ℝ) ^ (1 : ℝ) :=
            congrArg (fun z : ℝ =>
              (N : ℝ) ^ ((2 : ℝ) + -(399 / 200 : ℝ)) * z)
              (Real.rpow_one (N : ℝ)).symm
          _ = (N : ℝ) ^ (((2 : ℝ) + -(399 / 200 : ℝ)) + 1) :=
            (Real.rpow_add hx ((2 : ℝ) + -(399 / 200 : ℝ)) 1).symm
      _ = (N : ℝ) ^ (201 / 200 : ℝ) := by
        congr 1
        ring
  have hfirst :
      (N : ℝ) ^ 2 *
          (5 * Real.pi * Real.exp 1 *
            (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))) =
        5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 3 := by
    field_simp [hx.ne']
  have hsecond :
      (N : ℝ) ^ 2 *
          ((5 * Real.pi / 2) *
            (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * ((N : ℝ) / 2)) =
        (5 * Real.pi / 4) * A * (N : ℝ) ^ (201 / 200 : ℝ) := by
    calc
      (N : ℝ) ^ 2 *
          ((5 * Real.pi / 2) *
            (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * ((N : ℝ) / 2)) =
        (5 * Real.pi / 4) * A *
          ((N : ℝ) ^ 2 * (N : ℝ) ^ (-(399 / 200 : ℝ)) * (N : ℝ)) := by
            ring
      _ = (5 * Real.pi / 4) * A * (N : ℝ) ^ (201 / 200 : ℝ) := by
        rw [hxpow]
  exact (hraw hN).trans_eq (by
    rw [mul_add, hfirst, hsecond])

end RHTower
