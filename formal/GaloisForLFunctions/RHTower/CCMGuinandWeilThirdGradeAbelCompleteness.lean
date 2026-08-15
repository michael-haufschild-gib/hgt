import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection
import GaloisForLFunctions.RHTower.CriticalPrimeSourceSchattenIdeal
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore
import GaloisForLFunctions.RHTower.CCMInverseTiltedCriticalMellinFactorization
import GaloisForLFunctions.RHTower.CCMFirstClockLandauCompleteness
import GaloisForLFunctions.RHTower.ArchEnvelope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Complex Filter Function Set MeasureTheory Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Laplace transform of a real tail carrier. -/
def ccmAbelLaplaceTail (q : ℝ → ℝ) (b : ℝ) (u : ℂ) : ℂ :=
  ∫ h : ℝ in Set.Ioi b,
    Complex.exp (-u * (h : ℂ)) * (q h : ℂ)

theorem differentiableAt_ccmAbelLaplaceTail_of_bounded
    {q : ℝ → ℝ} (hq : Measurable q)
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hqC : ∀ h, b < h → |q h| ≤ C)
    {u₀ : ℂ} (hu₀ : 0 < u₀.re) :
    DifferentiableAt ℂ (ccmAbelLaplaceTail q b) u₀ := by
  let σ : ℝ := u₀.re / 2
  let F : ℂ → ℝ → ℂ := fun u h =>
    Complex.exp (-u * (h : ℂ)) * (q h : ℂ)
  let F' : ℂ → ℝ → ℂ := fun u h =>
    (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) * (q h : ℂ)
  let bound : ℝ → ℝ := fun h =>
    C * h * Real.exp (-σ * h)
  have hσ : 0 < σ := by
    dsimp only [σ]
    linarith
  have hball : Metric.ball u₀ σ ⊆ {u : ℂ | σ < u.re} := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have hre : |u.re - u₀.re| ≤ ‖u - u₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (u - u₀)
    have hlower := (abs_le.mp hre).1
    change σ < u.re
    dsimp only [σ] at hu ⊢
    linarith
  have hFmeas : ∀ᶠ u in 𝓝 u₀,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi b)) := by
    filter_upwards with u
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    fun_prop
  have hFint : Integrable (F u₀) (volume.restrict (Set.Ioi b)) := by
    have hbase : IntegrableOn
        (fun h : ℝ => Real.exp (-u₀.re * h) * C)
        (Set.Ioi b) := by
      have hexp : IntegrableOn
          (fun h : ℝ => Real.exp ((-u₀.re) * h))
          (Set.Ioi b) :=
        integrableOn_exp_mul_Ioi (by linarith) b
      simpa only [MeasureTheory.IntegrableOn, mul_comm] using hexp.mul_const C
    have hbase' : Integrable
        (fun h : ℝ => Real.exp (-u₀.re * h) * C)
        (volume.restrict (Set.Ioi b)) := by
      simpa only [MeasureTheory.IntegrableOn] using hbase
    change Integrable
      (fun h : ℝ => Complex.exp (-u₀ * (h : ℂ)) * (q h : ℂ))
      (volume.restrict (Set.Ioi b))
    apply hbase'.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      have hh0 : 0 < h := hb.trans hh
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      have hexpNorm : ‖Complex.exp (-u₀ * (h : ℂ))‖ =
          Real.exp (-u₀.re * h) := by
        rw [Complex.norm_exp]
        congr 1
        simp [mul_re]
      rw [hexpNorm]
      exact mul_le_mul_of_nonneg_left (hqC h hh)
        (Real.exp_nonneg _)
  have hF'meas : AEStronglyMeasurable (F' u₀)
      (volume.restrict (Set.Ioi b)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F']
    fun_prop
  have hboundInt : Integrable bound (volume.restrict (Set.Ioi b)) := by
    have hgamma : IntegrableOn
        (fun h : ℝ => h ^ (1 : ℝ) * Real.exp (-σ * h ^ (1 : ℝ)))
        (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := σ)
        (by norm_num) (by norm_num) hσ
    have hgamma' : IntegrableOn
        (fun h : ℝ => h * Real.exp (-σ * h)) (Set.Ioi b) := by
      apply (hgamma.mono_set (Set.Ioi_subset_Ioi hb.le)).congr_fun
      · intro h hh
        have hh0 : 0 < h := hb.trans hh
        simp only [Real.rpow_one]
      · exact measurableSet_Ioi
    change IntegrableOn bound (Set.Ioi b)
    simpa only [MeasureTheory.IntegrableOn, bound, mul_assoc] using
      hgamma'.const_mul C
  have hbound : ∀ᵐ h ∂volume.restrict (Set.Ioi b),
      ∀ u ∈ Metric.ball u₀ σ, ‖F' u h‖ ≤ bound h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    intro u hu
    have hh0 : 0 < h := hb.trans hh
    have hure : σ < u.re := hball hu
    have hexpLe : Real.exp (-u.re * h) ≤ Real.exp (-σ * h) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_right (neg_le_neg hure.le) hh0.le
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos hh0, Complex.norm_exp,
      norm_real, Real.norm_eq_abs]
    have hre : (-u * (h : ℂ)).re = -u.re * h := by
      simp [mul_re]
    rw [hre]
    calc
      h * Real.exp (-u.re * h) * |q h| ≤
          h * Real.exp (-σ * h) * |q h| := by
        gcongr
      _ ≤ h * Real.exp (-σ * h) * C := by
        gcongr
        exact hqC h hh
      _ = C * h * Real.exp (-σ * h) := by ring
  have hdiff : ∀ᵐ h ∂volume.restrict (Set.Ioi b),
      ∀ u ∈ Metric.ball u₀ σ,
        HasDerivAt (fun u => F u h) (F' u h) u := by
    filter_upwards with h
    intro u hu
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (h : ℂ)))
        (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) u := by
      simpa [mul_comm] using
        (((hasDerivAt_id u).neg.mul_const (h : ℂ)).cexp)
    dsimp only [F, F']
    exact hexp.mul_const (q h : ℂ)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi b)) (F := F) (F' := F')
    (x₀ := u₀) (s := Metric.ball u₀ σ) (bound := bound)
    (Metric.ball_mem_nhds u₀ hσ) hFmeas hFint hF'meas
    hbound hboundInt hdiff
  change DifferentiableAt ℂ
    (fun u : ℂ => ∫ h : ℝ in Set.Ioi b,
      Complex.exp (-u * (h : ℂ)) * (q h : ℂ)) u₀
  exact hmain.2.differentiableAt

theorem analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    {q : ℝ → ℝ} (hq : Measurable q)
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hqC : ∀ h, b < h → |q h| ≤ C) :
    AnalyticOnNhd ℂ (ccmAbelLaplaceTail q b) {u : ℂ | 0 < u.re} := by
  have hdiff : DifferentiableOn ℂ (ccmAbelLaplaceTail q b)
      {u : ℂ | 0 < u.re} := by
    intro u hu
    exact (differentiableAt_ccmAbelLaplaceTail_of_bounded
      hq hb hC hqC hu).differentiableWithinAt
  exact hdiff.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Abel transform of a bounded cumulative source. -/
def ccmAbelCumulativeSourceContinuation
    (q : ℝ → ℝ) (b : ℝ) (u : ℂ) : ℂ :=
  u * ccmAbelLaplaceTail q b u

theorem analyticOnNhd_ccmAbelCumulativeSourceContinuation_of_bounded
    {q : ℝ → ℝ} (hq : Measurable q)
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hqC : ∀ h, b < h → |q h| ≤ C) :
    AnalyticOnNhd ℂ (ccmAbelCumulativeSourceContinuation q b)
      {u : ℂ | 0 < u.re} := by
  intro u hu
  exact analyticAt_id.mul
    (analyticOnNhd_ccmAbelLaplaceTail_of_bounded hq hb hC hqC u hu)

/-! ## Measurable cumulative realization of the third-grade source -/

/-- Continuous extension of the polar third-grade density below a positive base wall. -/
def ccmGuinandWeilThirdGradePolarDensityClamped (b h : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradeWeight (max b h) *
    (2 * Real.cosh (max b h / 2))

theorem continuous_ccmGuinandWeilThirdGradePolarDensityClamped
    {b : ℝ} (hb : 0 < b) :
    Continuous (ccmGuinandWeilThirdGradePolarDensityClamped b) := by
  have hpos : ∀ h : ℝ, 0 < max b h := fun h =>
    hb.trans_le (le_max_left b h)
  have hm : Continuous (fun h : ℝ => max b h) :=
    continuous_const.max continuous_id
  have hw : Continuous (fun h : ℝ => 32 / (max b h) ^ 3) :=
    continuous_const.div (hm.pow 3) (fun h => pow_ne_zero 3 (hpos h).ne')
  have hc : Continuous (fun h : ℝ => 2 * Real.cosh (max b h / 2)) :=
    continuous_const.mul (Real.continuous_cosh.comp (hm.div_const 2))
  change Continuous (fun h : ℝ =>
    (32 / (max b h) ^ 3) * (2 * Real.cosh (max b h / 2)))
  exact hw.mul hc

theorem measurable_ccmGuinandWeilPrimeThirdGradeRateWindow
    (b : ℝ) :
    Measurable (ccmGuinandWeilPrimeThirdGradeRateWindow b) := by
  let A : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.Icc 2 m,
      if b < Real.log k then ccmGuinandWeilPrimeEntryThirdJetScale k else 0
  have hA : Measurable A := measurable_of_countable A
  have hfloor : Measurable (fun H : ℝ => ⌊Real.exp H⌋₊) :=
    Real.measurable_exp.nat_floor
  change Measurable (fun H : ℝ => A ⌊Real.exp H⌋₊)
  exact hA.comp hfloor

/-- Globally measurable representative of the cumulative source.  On and above `b` it is
literally the finite prime-minus-polar third-grade window; clamping only regularizes the unused
region below the positive wall. -/
def ccmGuinandWeilThirdGradeCumulativeMeasurable (b H : ℝ) : ℝ :=
  ccmGuinandWeilPrimeThirdGradeRateWindow b H -
    ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h

theorem measurable_ccmGuinandWeilThirdGradeCumulativeMeasurable
    {b : ℝ} (hb : 0 < b) :
    Measurable (ccmGuinandWeilThirdGradeCumulativeMeasurable b) := by
  have hcont :=
    continuous_ccmGuinandWeilThirdGradePolarDensityClamped hb
  have hprim : Continuous (fun H : ℝ =>
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h) :=
    intervalIntegral.continuous_primitive
      (fun a c => hcont.intervalIntegrable a c) b
  exact (measurable_ccmGuinandWeilPrimeThirdGradeRateWindow b).sub
    hprim.measurable

theorem ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar
    {b H : ℝ} (hbH : b ≤ H) :
    ccmGuinandWeilThirdGradeCumulativeMeasurable b H =
      ccmGuinandWeilPrimePolarWeightedWindow b H
        ccmGuinandWeilThirdGradeWeight := by
  rw [ccmGuinandWeilThirdGradeCumulativeMeasurable,
    ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar,
    ccmGuinandWeilPolarThirdGradeRateWindow]
  congr 1
  apply intervalIntegral.integral_congr
  intro h hh
  rw [Set.uIcc_of_le hbH] at hh
  rw [ccmGuinandWeilThirdGradePolarDensityClamped,
    max_eq_right hh.1]

theorem tendsto_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    Tendsto (ccmGuinandWeilThirdGradeCumulativeMeasurable b) atTop
      (nhds (L - ∫ h in Set.Ioi b,
        ccmGuinandWeilThirdGradeWeight h *
          ccmPublishedArchimedeanDensity h)) := by
  let G : ℝ := ∫ h in Set.Ioi b,
    ccmGuinandWeilThirdGradeWeight h *
      ccmPublishedArchimedeanDensity h
  have hgamma : Tendsto (ccmGuinandWeilGammaThirdGradeRateWindow b)
      atTop (nhds G) :=
    tendsto_ccmGuinandWeilGammaThirdGradeRateWindow hb
  have hsub := hL.sub hgamma
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop b] with H hH
  rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hH,
    ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
  unfold ccmGuinandWeilCompletedThirdGradeRateWindow
  ring

theorem exists_tail_bound_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    ∃ B C : ℝ, b ≤ B ∧ 0 ≤ C ∧
      ∀ H : ℝ, B < H →
        |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C := by
  let G : ℝ := ∫ h in Set.Ioi b,
    ccmGuinandWeilThirdGradeWeight h *
      ccmPublishedArchimedeanDensity h
  have hq : Tendsto (ccmGuinandWeilThirdGradeCumulativeMeasurable b)
      atTop (nhds (L - G)) := by
    simpa only [G] using
      tendsto_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed hb hL
  have hev : ∀ᶠ H : ℝ in atTop,
      dist (ccmGuinandWeilThirdGradeCumulativeMeasurable b H) (L - G) < 1 :=
    (Metric.tendsto_nhds.mp hq) 1 zero_lt_one
  obtain ⟨B, hB⟩ := (eventually_atTop.1 (hev.and (eventually_ge_atTop b)))
  have hdistB := (hB B le_rfl).1
  have hbB := (hB B le_rfl).2
  refine ⟨B, |L - G| + 1, hbB, by positivity, ?_⟩
  intro H hBH
  have hdist := (hB H hBH.le).1
  rw [Real.dist_eq] at hdist
  calc
    |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| =
        |(ccmGuinandWeilThirdGradeCumulativeMeasurable b H - (L - G)) +
          (L - G)| := by ring_nf
    _ ≤ |ccmGuinandWeilThirdGradeCumulativeMeasurable b H - (L - G)| +
          |L - G| := abs_add_le _ _
    _ ≤ |L - G| + 1 := by linarith

/-! ## Atomic Abel lane -/

/-- Dirichlet coefficient of the third-grade prime source above the base wall. -/
def ccmGuinandWeilThirdGradePrimeDirichletCoeff (b : ℝ) (n : ℕ) : ℂ :=
  if b < Real.log n then (ccmGuinandWeilPrimeEntryThirdJetScale n : ℂ) else 0

theorem norm_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ‖ccmGuinandWeilThirdGradePrimeDirichletCoeff b n‖ ≤ 32 / b ^ 2 := by
  rw [ccmGuinandWeilThirdGradePrimeDirichletCoeff]
  split_ifs with hn
  · have hn1 : 1 < n := by
      have : 0 < Real.log n := hb.trans hn
      exact Nat.one_lt_cast.mp ((Real.log_pos_iff (by positivity)).mp this)
    have hlog : 0 < Real.log n := hb.trans hn
    have hscale : 0 ≤ ccmGuinandWeilPrimeEntryThirdJetScale n :=
      ccmGuinandWeilPrimeEntryThirdJetScale_nonneg hn1
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
    rw [ccmGuinandWeilPrimeEntryThirdJetScale]
    have hatom := criticalMellinAtomWeight_le_log n
    have hrpow : (n : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))) (by norm_num)
    have hatom' : criticalMellinAtomWeight n ≤ Real.log n := by
      calc
        criticalMellinAtomWeight n ≤
            Real.log n * (n : ℝ) ^ (-1 / 2 : ℝ) := hatom
        _ ≤ Real.log n * 1 := mul_le_mul_of_nonneg_left hrpow hlog.le
        _ = Real.log n := mul_one _
    rw [div_le_iff₀ (pow_pos hlog 3), div_eq_mul_inv]
    calc
      32 * criticalMellinAtomWeight n ≤ 32 * Real.log n := by gcongr
      _ ≤ 32 / b ^ 2 * Real.log n ^ 3 := by
        have hb2 : b ^ 2 ≤ Real.log n ^ 2 := by nlinarith
        field_simp
        nlinarith [sq_nonneg b]
  · simp
    positivity

theorem ccmGuinandWeilThirdGradePrimeDirichletCoeff_sum_norm_isBigO
    {b : ℝ} (hb : 0 < b) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ‖ccmGuinandWeilThirdGradePrimeDirichletCoeff b k‖) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (32 / b ^ 2)
    (Filter.Eventually.of_forall fun n => ?_)
  have hcalc :
    ∑ k ∈ Finset.Icc 1 n, ‖ccmGuinandWeilThirdGradePrimeDirichletCoeff b k‖ ≤
        (32 / b ^ 2) * n := by
    calc
      ∑ k ∈ Finset.Icc 1 n, ‖ccmGuinandWeilThirdGradePrimeDirichletCoeff b k‖ ≤
          ∑ _k ∈ Finset.Icc 1 n, 32 / b ^ 2 := by
        exact Finset.sum_le_sum fun k _ =>
          norm_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le hb k
      _ ≤ (32 / b ^ 2) * n := by
        simp [Nat.card_Icc, nsmul_eq_mul, mul_comm]
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  exact hcalc

theorem sum_ccmGuinandWeilThirdGradePrimeDirichletCoeff_eq_rate
    {b H : ℝ} (hH : 0 < H) :
    (∑ k ∈ Finset.Icc 1 ⌊Real.exp H⌋₊,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff b k) =
      (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) := by
  have hm : 1 ≤ ⌊Real.exp H⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_exp hH.le)
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hm,
    Finset.sum_insert (by simp), ccmGuinandWeilPrimeThirdGradeRateWindow]
  have hone : ccmGuinandWeilThirdGradePrimeDirichletCoeff b 1 = 0 := by
    simp [ccmGuinandWeilThirdGradePrimeDirichletCoeff,
      ccmGuinandWeilPrimeEntryThirdJetScale]
  rw [hone, zero_add, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k <;>
    simp [ccmGuinandWeilThirdGradePrimeDirichletCoeff, hbk]

theorem ccmGuinandWeilPrimeThirdGradeRateWindow_eq_zero_of_le
    {b H : ℝ} (hHb : H ≤ b) :
    ccmGuinandWeilPrimeThirdGradeRateWindow b H = 0 := by
  rw [ccmGuinandWeilPrimeThirdGradeRateWindow]
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  intro hbk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkfloor : k ≤ ⌊Real.exp H⌋₊ := (Finset.mem_Icc.mp hk).2
  have hkexp : (k : ℝ) ≤ Real.exp H := by
    exact (Nat.cast_le.mpr hkfloor).trans (Nat.floor_le (Real.exp_pos H).le)
  have hHlog : H < Real.log k := hHb.trans_lt hbk
  have hexplt : Real.exp H < (k : ℝ) := by
    calc
      Real.exp H < Real.exp (Real.log k) := Real.exp_lt_exp.mpr hHlog
      _ = (k : ℝ) := Real.exp_log (by positivity)
  exact (not_lt_of_ge hkexp) hexplt

theorem exp_mul_cpow_neg_add_one (u : ℂ) (H : ℝ) :
    (Real.exp H : ℂ) * (Real.exp H : ℂ) ^ (-(u + 1)) =
      Complex.exp (-u * (H : ℂ)) := by
  rw [show (Real.exp H : ℂ) = Complex.exp (H : ℂ) by simp]
  conv_lhs =>
    lhs
    rw [← Complex.cpow_one (Complex.exp (H : ℂ))]
  rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _),
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  congr 1
  ring

/-- Exact Abel representation of the atomic third-grade source on its elementary half-plane. -/
theorem LSeries_ccmGuinandWeilThirdGradePrimeDirichletCoeff_eq_abel
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) u =
      u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) := by
  have hmain := LSeries_eq_mul_integral'
    (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)
    (r := 1) zero_le_one hu
    (ccmGuinandWeilThirdGradePrimeDirichletCoeff_sum_norm_isBigO hb)
  rw [hmain]
  congr 1
  let g : ℝ → ℂ := fun t =>
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff b k) *
        (t : ℂ) ^ (-(u + 1))
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => Real.hasDerivAt_exp x |>.hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Real.image_exp_Ioi, Real.exp_zero] at hchange
  change (∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        ccmGuinandWeilThirdGradePrimeDirichletCoeff b k) *
          (t : ℂ) ^ (-(u + 1))) = _
  calc
    (∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        ccmGuinandWeilThirdGradePrimeDirichletCoeff b k) *
          (t : ℂ) ^ (-(u + 1))) =
        ∫ H : ℝ in Set.Ioi 0, |Real.exp H| • g (Real.exp H) := hchange
    _ = ∫ H : ℝ in Set.Ioi 0,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H hH
      have hH0 : 0 < H := hH
      dsimp only [g]
      rw [sum_ccmGuinandWeilThirdGradePrimeDirichletCoeff_eq_rate hH0]
      rw [abs_of_pos (Real.exp_pos H), Complex.real_smul]
      change (Real.exp H : ℂ) *
          ((ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) *
            (Real.exp H : ℂ) ^ (-(u + 1))) = _
      calc
        (Real.exp H : ℂ) *
            ((ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) *
              (Real.exp H : ℂ) ^ (-(u + 1))) =
            ((Real.exp H : ℂ) *
              (Real.exp H : ℂ) ^ (-(u + 1))) *
                (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) := by ring
        _ = _ := by rw [exp_mul_cpow_neg_add_one]
    _ = ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with H
      by_cases hbH : b < H
      · have hH0 : 0 < H := hb.trans hbH
        simp [hbH, hH0]
      · by_cases hH0 : 0 < H
        · have hz := ccmGuinandWeilPrimeThirdGradeRateWindow_eq_zero_of_le
            (le_of_not_gt hbH)
          simp [hbH, hH0, hz]
        · simp [hbH, hH0, not_lt_of_ge hb.le]

/-! ## Polar Abel lane -/

/-- Positive continuous density whose primitive is the polar third-grade rate. -/
def ccmGuinandWeilThirdGradePolarDensity (h : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradeWeight h * (2 * Real.cosh (h / 2))

theorem continuousOn_ccmGuinandWeilThirdGradePolarDensity
    {b : ℝ} (hb : 0 < b) :
    ContinuousOn ccmGuinandWeilThirdGradePolarDensity (Set.Ici b) := by
  intro h hh
  have hh0 : 0 < h := hb.trans_le hh
  unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_const.div (continuousAt_id.pow 3)
    (pow_ne_zero 3 hh0.ne')).mul
      (continuousAt_const.mul (Real.continuous_cosh.continuousAt.comp
        (continuousAt_id.div_const 2)))

theorem ccmGuinandWeilThirdGradePolarDensity_nonneg
    {h : ℝ} (hh : 0 < h) :
    0 ≤ ccmGuinandWeilThirdGradePolarDensity h := by
  unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
  exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (Real.cosh_pos _).le)

theorem ccmGuinandWeilThirdGradePolarDensity_le
    {b h : ℝ} (hb : 0 < b) (hbh : b ≤ h) :
    ccmGuinandWeilThirdGradePolarDensity h ≤
      (64 / b ^ 3) * Real.exp (h / 2) := by
  have hh : 0 < h := hb.trans_le hbh
  have hb3 : 0 < b ^ 3 := pow_pos hb 3
  have hh3 : 0 < h ^ 3 := pow_pos hh 3
  have hpow : b ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hb.le hbh 3
  have hwle : ccmGuinandWeilThirdGradeWeight h ≤ 32 / b ^ 3 := by
    unfold ccmGuinandWeilThirdGradeWeight
    exact div_le_div_of_nonneg_left (by norm_num) hb3 hpow
  have he : Real.exp (-h / 2) ≤ Real.exp (h / 2) := by
    rw [Real.exp_le_exp]
    linarith
  have he' : Real.exp (-(h / 2)) ≤ Real.exp (h / 2) := by
    simpa [neg_div] using he
  have hcosh : 2 * Real.cosh (h / 2) ≤ 2 * Real.exp (h / 2) := by
    rw [Real.cosh_eq]
    nlinarith [he']
  have hcosh0 : 0 ≤ 2 * Real.cosh (h / 2) :=
    mul_nonneg (by norm_num) (Real.cosh_pos _).le
  unfold ccmGuinandWeilThirdGradePolarDensity
  calc
    ccmGuinandWeilThirdGradeWeight h * (2 * Real.cosh (h / 2)) ≤
        (32 / b ^ 3) * (2 * Real.cosh (h / 2)) :=
      mul_le_mul_of_nonneg_right hwle hcosh0
    _ ≤ (32 / b ^ 3) * (2 * Real.exp (h / 2)) :=
      mul_le_mul_of_nonneg_left hcosh
        (div_nonneg (by norm_num) hb3.le)
    _ = (64 / b ^ 3) * Real.exp (h / 2) := by ring

theorem ccmGuinandWeilPolarThirdGradeRateWindow_nonneg
    {b H : ℝ} (hb : 0 < b) (hBH : b ≤ H) :
    0 ≤ ccmGuinandWeilPolarThirdGradeRateWindow b H := by
  rw [ccmGuinandWeilPolarThirdGradeRateWindow]
  apply intervalIntegral.integral_nonneg hBH
  intro h hh
  exact ccmGuinandWeilThirdGradePolarDensity_nonneg (hb.trans_le hh.1)

theorem ccmGuinandWeilPolarThirdGradeRateWindow_le
    {b H : ℝ} (hb : 0 < b) (hBH : b ≤ H) :
    ccmGuinandWeilPolarThirdGradeRateWindow b H ≤
      (64 / b ^ 3) * H * Real.exp (H / 2) := by
  rw [ccmGuinandWeilPolarThirdGradeRateWindow]
  have hcont := continuousOn_ccmGuinandWeilThirdGradePolarDensity hb
  have hmajorCont : ContinuousOn
      (fun _h : ℝ => (64 / b ^ 3) * Real.exp (H / 2)) (Set.uIcc b H) :=
    continuousOn_const
  have hcontI : ContinuousOn ccmGuinandWeilThirdGradePolarDensity
      (Set.uIcc b H) := by
    apply hcont.mono
    rw [Set.uIcc_of_le hBH]
    exact Set.Icc_subset_Ici_self
  have hmono : (∫ h in b..H, ccmGuinandWeilThirdGradePolarDensity h) ≤
      ∫ _h in b..H, (64 / b ^ 3) * Real.exp (H / 2) := by
    apply intervalIntegral.integral_mono_on hBH
      hcontI.intervalIntegrable
      (hmajorCont.intervalIntegrable)
    intro h hh
    have hhhalf : h / 2 ≤ H / 2 := by
      exact div_le_div_of_nonneg_right hh.2 (by norm_num)
    exact (ccmGuinandWeilThirdGradePolarDensity_le hb hh.1).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hhhalf) (by positivity))
  calc
    (∫ h in b..H, ccmGuinandWeilThirdGradePolarDensity h) ≤
        ∫ _h in b..H, (64 / b ^ 3) * Real.exp (H / 2) := hmono
    _ = (H - b) * ((64 / b ^ 3) * Real.exp (H / 2)) := by
      simp
      ring
    _ ≤ (64 / b ^ 3) * H * Real.exp (H / 2) := by
      have hC : 0 ≤ 64 / b ^ 3 := by positivity
      have hlen : H - b ≤ H := by linarith
      calc
        (H - b) * ((64 / b ^ 3) * Real.exp (H / 2)) ≤
            H * ((64 / b ^ 3) * Real.exp (H / 2)) :=
          mul_le_mul_of_nonneg_right hlen
            (mul_nonneg hC (Real.exp_nonneg _))
        _ = (64 / b ^ 3) * H * Real.exp (H / 2) := by ring

theorem ccmGuinandWeilPolarThirdGradeRateWindow_eq_clamped
    {b H : ℝ} (hBH : b ≤ H) :
    ccmGuinandWeilPolarThirdGradeRateWindow b H =
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h := by
  rw [ccmGuinandWeilPolarThirdGradeRateWindow]
  apply intervalIntegral.integral_congr
  intro h hh
  rw [Set.uIcc_of_le hBH] at hh
  rw [ccmGuinandWeilThirdGradePolarDensityClamped, max_eq_right hh.1]

theorem integrableOn_exp_mul_ccmGuinandWeilThirdGradePolarDensity
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 / 2 < u.re) :
    IntegrableOn
      (fun h : ℝ => Complex.exp (-u * (h : ℂ)) *
        (ccmGuinandWeilThirdGradePolarDensity h : ℂ))
      (Set.Ioi b) := by
  let δ : ℝ := u.re - 1 / 2
  let C : ℝ := 64 / b ^ 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hbase : IntegrableOn (fun h : ℝ => C * Real.exp (-δ * h))
      (Set.Ioi b) := by
    have he := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) b
    simpa only [MeasureTheory.IntegrableOn, neg_mul] using he.const_mul C
  apply hbase.mono'
  · apply Measurable.aestronglyMeasurable
    unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hb.trans hh
    have hd0 := ccmGuinandWeilThirdGradePolarDensity_nonneg hh0
    rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hd0]
    have hre : (-u * (h : ℂ)).re = -u.re * h := by simp [mul_re]
    rw [hre]
    calc
      Real.exp (-u.re * h) * ccmGuinandWeilThirdGradePolarDensity h ≤
          Real.exp (-u.re * h) * (C * Real.exp (h / 2)) :=
        mul_le_mul_of_nonneg_left
          (ccmGuinandWeilThirdGradePolarDensity_le hb hh.le)
          (Real.exp_nonneg _)
      _ = C * Real.exp (-δ * h) := by
        calc
          Real.exp (-u.re * h) * (C * Real.exp (h / 2)) =
              C * (Real.exp (-u.re * h) * Real.exp (h / 2)) := by ring
          _ = C * Real.exp (-δ * h) := by
            rw [← Real.exp_add]
            congr 1
            dsimp only [δ]
            ring

theorem integrableOn_ccmGuinandWeilPolarThirdGradeRateWindow_mul_exp
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 / 2 < u.re) :
    IntegrableOn
      (fun h : ℝ =>
        (ccmGuinandWeilPolarThirdGradeRateWindow b h : ℂ) *
          Complex.exp (-u * (h : ℂ)))
      (Set.Ioi b) := by
  let δ : ℝ := u.re - 1 / 2
  let C : ℝ := 64 / b ^ 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hgamma : IntegrableOn
      (fun h : ℝ => h ^ (1 : ℝ) * Real.exp (-δ * h ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := δ)
      (by norm_num) (by norm_num) hδ
  have hlinear : IntegrableOn (fun h : ℝ => h * Real.exp (-δ * h))
      (Set.Ioi b) := by
    apply (hgamma.mono_set (Set.Ioi_subset_Ioi hb.le)).congr_fun
    · intro h hh
      have hh0 : 0 < h := hb.trans hh
      simp only [Real.rpow_one]
    · exact measurableSet_Ioi
  have hbase : IntegrableOn (fun h : ℝ => C * h * Real.exp (-δ * h))
      (Set.Ioi b) := by
    simpa only [MeasureTheory.IntegrableOn, mul_assoc] using hlinear.const_mul C
  apply hbase.mono'
  · let P : ℝ → ℝ := fun H =>
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h
    have hPc : Continuous P := by
      exact intervalIntegral.continuous_primitive
        (fun a c => (continuous_ccmGuinandWeilThirdGradePolarDensityClamped hb).intervalIntegrable a c)
        b
    have hmeas : AEStronglyMeasurable
        (fun h : ℝ => (P h : ℂ) * Complex.exp (-u * (h : ℂ)))
        (volume.restrict (Set.Ioi b)) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    apply hmeas.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [ccmGuinandWeilPolarThirdGradeRateWindow_eq_clamped hh.le]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hb.trans hh
    have hp0 := ccmGuinandWeilPolarThirdGradeRateWindow_nonneg hb hh.le
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hp0,
      Complex.norm_exp]
    have hre : (-u * (h : ℂ)).re = -u.re * h := by simp [mul_re]
    rw [hre]
    calc
      ccmGuinandWeilPolarThirdGradeRateWindow b h * Real.exp (-u.re * h) ≤
          (C * h * Real.exp (h / 2)) * Real.exp (-u.re * h) :=
        mul_le_mul_of_nonneg_right
          (ccmGuinandWeilPolarThirdGradeRateWindow_le hb hh.le)
          (Real.exp_nonneg _)
      _ = C * h * Real.exp (-δ * h) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        dsimp only [δ]
        ring

theorem continuousAt_ccmGuinandWeilThirdGradePolarDensity
    {h : ℝ} (hh : h ≠ 0) :
    ContinuousAt ccmGuinandWeilThirdGradePolarDensity h := by
  unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
  exact (continuousAt_const.div (continuousAt_id.pow 3)
    (pow_ne_zero 3 hh)).mul
      (continuousAt_const.mul (Real.continuous_cosh.continuousAt.comp
        (continuousAt_id.div_const 2)))

theorem hasDerivAt_ccmGuinandWeilPolarThirdGradeRateWindow
    {b H : ℝ} (hb : 0 < b) (hBH : b < H) :
    HasDerivAt (ccmGuinandWeilPolarThirdGradeRateWindow b)
      (ccmGuinandWeilThirdGradePolarDensity H) H := by
  change HasDerivAt
    (fun H => ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensity h)
    (ccmGuinandWeilThirdGradePolarDensity H) H
  have hcont := continuousAt_ccmGuinandWeilThirdGradePolarDensity
    (hb.trans hBH).ne'
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuousOn_ccmGuinandWeilThirdGradePolarDensity hb).mono
      (by rw [Set.uIcc_of_le hBH.le]; exact Set.Icc_subset_Ici_self)
      |>.intervalIntegrable)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      ((continuousOn_ccmGuinandWeilThirdGradePolarDensity hb).mono
        Set.Ioi_subset_Ici_self) H hBH)
    hcont

theorem tendsto_exp_mul_ccmGuinandWeilPolarThirdGradeRateWindow_atTop
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 / 2 < u.re) :
    Tendsto
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ))
      atTop (nhds 0) := by
  let δ : ℝ := u.re - 1 / 2
  let C : ℝ := 64 / b ^ 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hpoint : ∀ᶠ H : ℝ in atTop,
      ‖Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ)‖ ≤
          C * (H ^ (1 : ℝ) * Real.exp (-δ * H)) := by
    filter_upwards [eventually_gt_atTop b] with H hH
    have hH0 : 0 < H := hb.trans hH
    have hp0 := ccmGuinandWeilPolarThirdGradeRateWindow_nonneg hb hH.le
    rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp0, Real.rpow_one]
    have hre : (-u * (H : ℂ)).re = -u.re * H := by simp [mul_re]
    rw [hre]
    calc
      Real.exp (-u.re * H) * ccmGuinandWeilPolarThirdGradeRateWindow b H ≤
          Real.exp (-u.re * H) * (C * H * Real.exp (H / 2)) :=
        mul_le_mul_of_nonneg_left
          (ccmGuinandWeilPolarThirdGradeRateWindow_le hb hH.le)
          (Real.exp_nonneg _)
      _ = C * (H * Real.exp (-δ * H)) := by
        calc
          Real.exp (-u.re * H) * (C * H * Real.exp (H / 2)) =
              C * H * (Real.exp (-u.re * H) * Real.exp (H / 2)) := by ring
          _ = C * (H * Real.exp (-δ * H)) := by
            have hexp : Real.exp (-u.re * H) * Real.exp (H / 2) =
                Real.exp (-δ * H) := by
              rw [← Real.exp_add]
              congr 1
              dsimp only [δ]
              ring
            rw [hexp]
            ring
  have hmajor : Tendsto
      (fun H : ℝ => C * (H ^ (1 : ℝ) * Real.exp (-δ * H)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ hδ).const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun H => norm_nonneg _) hpoint hmajor

/-- Abel transform of the polar primitive equals Laplace transform of its density. -/
theorem ccmGuinandWeilPolarThirdGradeRateWindow_abel_eq_density
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 / 2 < u.re) :
    u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ) =
      ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilThirdGradePolarDensity H : ℂ) := by
  let E : ℝ → ℂ := fun H => Complex.exp (-u * (H : ℂ))
  let E' : ℝ → ℂ := fun H => -u * Complex.exp (-u * (H : ℂ))
  let P : ℝ → ℂ := fun H =>
    (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ)
  let P' : ℝ → ℂ := fun H =>
    (ccmGuinandWeilThirdGradePolarDensity H : ℂ)
  have hEP' : IntegrableOn (E * P') (Set.Ioi b) := by
    exact (integrableOn_exp_mul_ccmGuinandWeilThirdGradePolarDensity hb hu).congr_fun
      (fun H _ => by rfl) measurableSet_Ioi
  have hE'P : IntegrableOn (E' * P) (Set.Ioi b) := by
    have hbase := integrableOn_ccmGuinandWeilPolarThirdGradeRateWindow_mul_exp hb hu
    have hconst : IntegrableOn
        (fun H : ℝ =>
          ((ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ) *
            Complex.exp (-u * (H : ℂ))) * (-u))
        (Set.Ioi b) := hbase.mul_const (-u)
    exact hconst.congr_fun
      (fun H _ => by dsimp only [E', P, Pi.mul_apply]; ring) measurableSet_Ioi
  have hzero : Tendsto (E * P) (𝓝[>] b) (nhds 0) := by
    let Pc : ℝ → ℝ := fun H =>
      ∫ h in b..H, ccmGuinandWeilThirdGradePolarDensityClamped b h
    have hPc : Continuous Pc := intervalIntegral.continuous_primitive
      (fun a c => (continuous_ccmGuinandWeilThirdGradePolarDensityClamped hb).intervalIntegrable a c)
      b
    have ht : Tendsto
        (fun H : ℝ => E H * (Pc H : ℂ)) (𝓝[>] b)
        (nhds (E b * (Pc b : ℂ))) :=
      (by fun_prop : ContinuousAt (fun H : ℝ => E H * (Pc H : ℂ)) b)
        |>.continuousWithinAt
    have heq : E * P =ᶠ[𝓝[>] b] fun H : ℝ => E H * (Pc H : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with H hH
      dsimp only [P, Pc, Pi.mul_apply]
      rw [ccmGuinandWeilPolarThirdGradeRateWindow_eq_clamped hH.le]
    have hlim := ht.congr' heq.symm
    convert hlim using 1 <;> simp [Pc]
  have hinfty : Tendsto (E * P) atTop (nhds 0) := by
    exact (tendsto_exp_mul_ccmGuinandWeilPolarThirdGradeRateWindow_atTop hb hu).congr'
      (Eventually.of_forall fun H => rfl)
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := b) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (u := E) (u' := E') (v := P) (v' := P')
    (fun H _ => by
      dsimp only [E, E']
      simpa [mul_comm] using
        ((((hasDerivAt_id H).ofReal_comp.const_mul (-u)).cexp)))
    (fun H hH => by
      dsimp only [P, P']
      exact (hasDerivAt_ccmGuinandWeilPolarThirdGradeRateWindow hb hH).ofReal_comp)
    hEP' hE'P hzero hinfty
  dsimp only [E, E', P, P'] at hibp
  have hibp' :
      (∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilThirdGradePolarDensity H : ℂ)) =
        -(∫ H : ℝ in Set.Ioi b,
          (-u * Complex.exp (-u * (H : ℂ))) *
            (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ)) := by
    simpa using hibp
  calc
    u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ) =
        -(∫ H : ℝ in Set.Ioi b,
          (-u * Complex.exp (-u * (H : ℂ))) *
            (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ)) := by
      rw [← MeasureTheory.integral_const_mul]
      rw [← MeasureTheory.integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H hH
      ring
    _ = _ := hibp'.symm

theorem ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg
    {b H : ℝ} : 0 ≤ ccmGuinandWeilPrimeThirdGradeRateWindow b H := by
  rw [ccmGuinandWeilPrimeThirdGradeRateWindow]
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact ccmGuinandWeilPrimeEntryThirdJetScale_nonneg (by
      have := (Finset.mem_Icc.mp hk).1
      omega)
  · exact le_rfl

theorem ccmGuinandWeilPrimeThirdGradeRateWindow_le
    {b : ℝ} (hb : 0 < b) (H : ℝ) :
    ccmGuinandWeilPrimeThirdGradeRateWindow b H ≤
      (32 / b ^ 2) * Real.exp H := by
  rw [ccmGuinandWeilPrimeThirdGradeRateWindow]
  calc
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then ccmGuinandWeilPrimeEntryThirdJetScale k else 0) ≤
        ∑ _k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊, (32 / b ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcoeff := norm_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le hb k
      by_cases hbk : b < Real.log k
      · rw [ccmGuinandWeilThirdGradePrimeDirichletCoeff, if_pos hbk,
          norm_real, Real.norm_eq_abs] at hcoeff
        rw [if_pos hbk]
        have hk1 : 1 < k := by
          have := (Finset.mem_Icc.mp hk).1
          omega
        rw [abs_of_nonneg (ccmGuinandWeilPrimeEntryThirdJetScale_nonneg hk1)] at hcoeff
        exact hcoeff
      · rw [if_neg hbk]
        positivity
    _ ≤ (32 / b ^ 2) * Real.exp H := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 2 ⌊Real.exp H⌋₊).card : ℝ) ≤ Real.exp H := by
        calc
          ((Finset.Icc 2 ⌊Real.exp H⌋₊).card : ℝ) ≤ (⌊Real.exp H⌋₊ : ℝ) := by
            exact_mod_cast (by simp [Nat.card_Icc] :
              (Finset.Icc 2 ⌊Real.exp H⌋₊).card ≤ ⌊Real.exp H⌋₊)
          _ ≤ Real.exp H := Nat.floor_le (Real.exp_pos H).le
      have hC : 0 ≤ 32 / b ^ 2 := by positivity
      nlinarith

theorem integrableOn_exp_mul_ccmGuinandWeilPrimeThirdGradeRateWindow
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ))
      (Set.Ioi b) := by
  let δ : ℝ := u.re - 1
  let C : ℝ := 32 / b ^ 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hbase : IntegrableOn (fun H : ℝ => C * Real.exp (-δ * H))
      (Set.Ioi b) := by
    have he := integrableOn_exp_mul_Ioi (a := -δ) (by linarith) b
    simpa only [MeasureTheory.IntegrableOn, neg_mul] using he.const_mul C
  apply hbase.mono'
  · apply Measurable.aestronglyMeasurable
    have he : Measurable
        (fun H : ℝ => Complex.exp (-u * (H : ℂ))) := by fun_prop
    exact he.mul (Complex.continuous_ofReal.measurable.comp
      (measurable_ccmGuinandWeilPrimeThirdGradeRateWindow b))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    have hp0 := ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg
      (b := b) (H := H)
    rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp0]
    have hre : (-u * (H : ℂ)).re = -u.re * H := by simp [mul_re]
    rw [hre]
    calc
      Real.exp (-u.re * H) * ccmGuinandWeilPrimeThirdGradeRateWindow b H ≤
          Real.exp (-u.re * H) * (C * Real.exp H) :=
        mul_le_mul_of_nonneg_left
          (ccmGuinandWeilPrimeThirdGradeRateWindow_le hb H)
          (Real.exp_nonneg _)
      _ = C * Real.exp (-δ * H) := by
        calc
          Real.exp (-u.re * H) * (C * Real.exp H) =
              C * (Real.exp (-u.re * H) * Real.exp H) := by ring
          _ = C * Real.exp (-δ * H) := by
            rw [← Real.exp_add]
            congr 1
            dsimp only [δ]
            ring

/-- On the elementary half-plane, the Abel transform of the cumulative source is exactly the
atomic L-series minus the polar density transform. -/
theorem ccmAbelCumulativeSourceContinuation_eq_atomic_sub_polar
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b u =
      LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) u -
        ∫ H : ℝ in Set.Ioi b,
          Complex.exp (-u * (H : ℂ)) *
            (ccmGuinandWeilThirdGradePolarDensity H : ℂ) := by
  have hprime := integrableOn_exp_mul_ccmGuinandWeilPrimeThirdGradeRateWindow hb hu
  have hpolar0 := integrableOn_ccmGuinandWeilPolarThirdGradeRateWindow_mul_exp
    hb (by linarith : 1 / 2 < u.re)
  have hpolar : IntegrableOn
      (fun H : ℝ => Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ))
      (Set.Ioi b) :=
    hpolar0.congr_fun (fun H _ => by ring) measurableSet_Ioi
  rw [ccmAbelCumulativeSourceContinuation, ccmAbelLaplaceTail]
  have hsplit :
      (∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ)) =
        (∫ H : ℝ in Set.Ioi b,
          Complex.exp (-u * (H : ℂ)) *
            (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ)) -
        ∫ H : ℝ in Set.Ioi b,
          Complex.exp (-u * (H : ℂ)) *
            (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ) := by
    rw [← MeasureTheory.integral_sub hprime hpolar]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro H hH
    change Complex.exp (-u * (H : ℂ)) *
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b H : ℂ) =
      Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPrimeThirdGradeRateWindow b H : ℂ) -
        Complex.exp (-u * (H : ℂ)) *
          (ccmGuinandWeilPolarThirdGradeRateWindow b H : ℂ)
    rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hH.le,
      ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
    push_cast
    ring
  rw [hsplit, mul_sub,
    ← LSeries_ccmGuinandWeilThirdGradePrimeDirichletCoeff_eq_abel hb hu,
    ccmGuinandWeilPolarThirdGradeRateWindow_abel_eq_density hb (by linarith)]

/-! ## All-order polar Laplace moments -/

def ccmGuinandWeilThirdGradePolarLaplaceMoment
    (b : ℝ) (m : ℕ) (u : ℂ) : ℂ :=
  ∫ h : ℝ in Set.Ioi b,
    Complex.exp (-u * (h : ℂ)) *
      ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ)

theorem integrableOn_ccmGuinandWeilThirdGradePolarLaplaceMoment
    {b : ℝ} (hb : 0 < b) (m : ℕ) {u : ℂ} (hu : 1 / 2 < u.re) :
    IntegrableOn
      (fun h : ℝ => Complex.exp (-u * (h : ℂ)) *
        ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ))
      (Set.Ioi b) := by
  let δ : ℝ := u.re - 1 / 2
  let C : ℝ := 64 / b ^ 3
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hgamma : IntegrableOn
      (fun h : ℝ => h ^ (m : ℝ) * Real.exp (-δ * h ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (m : ℝ)) (b := δ)
      (by have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
      (by norm_num) hδ
  have hpow : IntegrableOn
      (fun h : ℝ => h ^ m * Real.exp (-δ * h)) (Set.Ioi b) := by
    apply (hgamma.mono_set (Set.Ioi_subset_Ioi hb.le)).congr_fun
    · intro h hh
      change h ^ (m : ℝ) * Real.exp (-δ * h ^ (1 : ℝ)) =
        h ^ m * Real.exp (-δ * h)
      rw [Real.rpow_natCast h m, Real.rpow_one]
    · exact measurableSet_Ioi
  have hbase : IntegrableOn
      (fun h : ℝ => C * (h ^ m * Real.exp (-δ * h))) (Set.Ioi b) := by
    simpa only [MeasureTheory.IntegrableOn] using hpow.const_mul C
  apply hbase.mono'
  · apply Measurable.aestronglyMeasurable
    unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hb.trans hh
    have hd0 := ccmGuinandWeilThirdGradePolarDensity_nonneg hh0
    rw [norm_mul, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hh0.le m) hd0)]
    have hre : (-u * (h : ℂ)).re = -u.re * h := by simp [mul_re]
    rw [hre]
    calc
      Real.exp (-u.re * h) *
          (h ^ m * ccmGuinandWeilThirdGradePolarDensity h) ≤
        Real.exp (-u.re * h) *
          (h ^ m * (C * Real.exp (h / 2))) := by
        gcongr
        exact ccmGuinandWeilThirdGradePolarDensity_le hb hh.le
      _ = C * (h ^ m * Real.exp (-δ * h)) := by
        have hexp : Real.exp (-u.re * h) * Real.exp (h / 2) =
            Real.exp (-δ * h) := by
          rw [← Real.exp_add]
          congr 1
          dsimp only [δ]
          ring
        calc
          Real.exp (-u.re * h) * (h ^ m * (C * Real.exp (h / 2))) =
              C * h ^ m *
                (Real.exp (-u.re * h) * Real.exp (h / 2)) := by ring
          _ = C * (h ^ m * Real.exp (-δ * h)) := by
            rw [hexp]
            ring

theorem hasDerivAt_ccmGuinandWeilThirdGradePolarLaplaceMoment
    {b : ℝ} (hb : 0 < b) (m : ℕ) {u₀ : ℂ} (hu₀ : 1 / 2 < u₀.re) :
    HasDerivAt (ccmGuinandWeilThirdGradePolarLaplaceMoment b m)
      (-ccmGuinandWeilThirdGradePolarLaplaceMoment b (m + 1) u₀) u₀ := by
  let σ : ℝ := (u₀.re - 1 / 2) / 2
  let C : ℝ := 64 / b ^ 3
  let F : ℂ → ℝ → ℂ := fun u h =>
    Complex.exp (-u * (h : ℂ)) *
      ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ)
  let F' : ℂ → ℝ → ℂ := fun u h =>
    (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) *
      ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ)
  let bound : ℝ → ℝ := fun h =>
    C * (h ^ (m + 1) * Real.exp (-σ * h))
  have hσ : 0 < σ := by dsimp only [σ]; linarith
  have hball : Metric.ball u₀ σ ⊆ {u : ℂ | 1 / 2 + σ < u.re} := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have hre : |u.re - u₀.re| ≤ ‖u - u₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (u - u₀)
    have hlower := (abs_le.mp hre).1
    change 1 / 2 + σ < u.re
    dsimp only [σ] at hu ⊢
    linarith
  have hFmeas : ∀ᶠ u in 𝓝 u₀,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioi b)) := by
    filter_upwards with u
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
    fun_prop
  have hFint : Integrable (F u₀) (volume.restrict (Set.Ioi b)) := by
    change IntegrableOn
      (fun h : ℝ => Complex.exp (-u₀ * (h : ℂ)) *
        ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ))
      (Set.Ioi b)
    exact integrableOn_ccmGuinandWeilThirdGradePolarLaplaceMoment hb m hu₀
  have hF'meas : AEStronglyMeasurable (F' u₀)
      (volume.restrict (Set.Ioi b)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F']
    unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
    fun_prop
  have hboundInt : Integrable bound (volume.restrict (Set.Ioi b)) := by
    have hgamma : IntegrableOn
        (fun h : ℝ => h ^ ((m + 1 : ℕ) : ℝ) *
          Real.exp (-σ * h ^ (1 : ℝ))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := ((m + 1 : ℕ) : ℝ)) (b := σ)
        (by have hm0 : 0 ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
        (by norm_num) hσ
    have hpow : IntegrableOn
        (fun h : ℝ => h ^ (m + 1) * Real.exp (-σ * h)) (Set.Ioi b) := by
      apply (hgamma.mono_set (Set.Ioi_subset_Ioi hb.le)).congr_fun
      · intro h hh
        change h ^ ((m + 1 : ℕ) : ℝ) * Real.exp (-σ * h ^ (1 : ℝ)) =
          h ^ (m + 1) * Real.exp (-σ * h)
        rw [Real.rpow_natCast h (m + 1), Real.rpow_one]
      · exact measurableSet_Ioi
    change IntegrableOn bound (Set.Ioi b)
    simpa only [MeasureTheory.IntegrableOn, bound] using hpow.const_mul C
  have hbound : ∀ᵐ h ∂volume.restrict (Set.Ioi b),
      ∀ u ∈ Metric.ball u₀ σ, ‖F' u h‖ ≤ bound h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    intro u hu
    have hh0 : 0 < h := hb.trans hh
    have hure : 1 / 2 + σ < u.re := hball hu
    have hd0 := ccmGuinandWeilThirdGradePolarDensity_nonneg hh0
    have hexpLe : Real.exp (-(u.re - 1 / 2) * h) ≤ Real.exp (-σ * h) := by
      rw [Real.exp_le_exp]
      have : σ < u.re - 1 / 2 := by linarith
      exact mul_le_mul_of_nonneg_right (neg_le_neg this.le) hh0.le
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_pos hh0, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hh0.le m) hd0)]
    have hre : (-u * (h : ℂ)).re = -u.re * h := by simp [mul_re]
    rw [hre]
    calc
      h * Real.exp (-u.re * h) *
          (h ^ m * ccmGuinandWeilThirdGradePolarDensity h) ≤
        h * Real.exp (-u.re * h) *
          (h ^ m * (C * Real.exp (h / 2))) := by
        gcongr
        exact ccmGuinandWeilThirdGradePolarDensity_le hb hh.le
      _ = C * (h ^ (m + 1) * Real.exp (-(u.re - 1 / 2) * h)) := by
        have hexp : Real.exp (-u.re * h) * Real.exp (h / 2) =
            Real.exp (-(u.re - 1 / 2) * h) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          h * Real.exp (-u.re * h) * (h ^ m * (C * Real.exp (h / 2))) =
              C * (h ^ m * h) *
                (Real.exp (-u.re * h) * Real.exp (h / 2)) := by ring
          _ = C * (h ^ (m + 1) * Real.exp (-(u.re - 1 / 2) * h)) := by
            rw [pow_succ, hexp]
            ring
      _ ≤ C * (h ^ (m + 1) * Real.exp (-σ * h)) := by
        gcongr
  have hdiff : ∀ᵐ h ∂volume.restrict (Set.Ioi b),
      ∀ u ∈ Metric.ball u₀ σ, HasDerivAt (fun u => F u h) (F' u h) u := by
    filter_upwards with h
    intro u hu
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (h : ℂ)))
        (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) u := by
      simpa [mul_comm] using (((hasDerivAt_id u).neg.mul_const (h : ℂ)).cexp)
    dsimp only [F, F']
    exact hexp.mul_const
      ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi b)) (F := F) (F' := F')
    (x₀ := u₀) (s := Metric.ball u₀ σ) (bound := bound)
    (Metric.ball_mem_nhds u₀ hσ) hFmeas hFint hF'meas
    hbound hboundInt hdiff
  change HasDerivAt
    (fun u : ℂ => ∫ h : ℝ in Set.Ioi b,
      Complex.exp (-u * (h : ℂ)) *
        ((h ^ m * ccmGuinandWeilThirdGradePolarDensity h : ℝ) : ℂ))
    (-ccmGuinandWeilThirdGradePolarLaplaceMoment b (m + 1) u₀) u₀
  have hderiv : (∫ h : ℝ in Set.Ioi b, F' u₀ h) =
      -ccmGuinandWeilThirdGradePolarLaplaceMoment b (m + 1) u₀ := by
    rw [ccmGuinandWeilThirdGradePolarLaplaceMoment,
      ← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    dsimp only [F']
    push_cast
    rw [pow_succ]
    ring
  rw [← hderiv]
  exact hmain.2

theorem iteratedDeriv_ccmGuinandWeilThirdGradePolarLaplaceMoment_zero
    {b : ℝ} (hb : 0 < b) (m : ℕ) {u : ℂ} (hu : 1 / 2 < u.re) :
    iteratedDeriv m (ccmGuinandWeilThirdGradePolarLaplaceMoment b 0) u =
      (-1 : ℂ) ^ m * ccmGuinandWeilThirdGradePolarLaplaceMoment b m u := by
  induction m generalizing u with
  | zero => simp
  | succ m ihm =>
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have heq : iteratedDeriv m
          (ccmGuinandWeilThirdGradePolarLaplaceMoment b 0) =ᶠ[𝓝 u]
          fun z => (-1 : ℂ) ^ m *
            ccmGuinandWeilThirdGradePolarLaplaceMoment b m z := by
        filter_upwards [hopen.mem_nhds hu] with z hz
        exact ihm hz
      rw [heq.deriv_eq]
      have hderiv := (hasDerivAt_ccmGuinandWeilThirdGradePolarLaplaceMoment
        hb m hu).const_mul ((-1 : ℂ) ^ m)
      rw [hderiv.deriv]
      ring

def ccmGuinandWeilThirdGradePolarTailLaplace
    (b : ℝ) (u : ℂ) : ℂ :=
  ∫ h : ℝ in Set.Ioi b,
    Complex.exp (-u * (h : ℂ)) * (2 * Real.cosh (h / 2) : ℝ)

theorem ccmGuinandWeilThirdGradePolarLaplaceMoment_three_eq
    {b : ℝ} (hb : 0 < b) (u : ℂ) :
    ccmGuinandWeilThirdGradePolarLaplaceMoment b 3 u =
      32 * ccmGuinandWeilThirdGradePolarTailLaplace b u := by
  rw [ccmGuinandWeilThirdGradePolarLaplaceMoment,
    ccmGuinandWeilThirdGradePolarTailLaplace,
    ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  have hh0 : 0 < h := hb.trans hh
  unfold ccmGuinandWeilThirdGradePolarDensity ccmGuinandWeilThirdGradeWeight
  push_cast
  field_simp [hh0.ne']

theorem iteratedDeriv_three_ccmGuinandWeilThirdGradePolarLaplaceMoment_zero
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 / 2 < u.re) :
    iteratedDeriv 3 (ccmGuinandWeilThirdGradePolarLaplaceMoment b 0) u =
      -32 * ccmGuinandWeilThirdGradePolarTailLaplace b u := by
  rw [iteratedDeriv_ccmGuinandWeilThirdGradePolarLaplaceMoment_zero hb 3 hu,
    ccmGuinandWeilThirdGradePolarLaplaceMoment_three_eq hb]
  norm_num

def ccmGuinandWeilActiveCriticalMellinAtomCoeff (b : ℝ) (n : ℕ) : ℂ :=
  if b < Real.log n then (criticalMellinAtomWeight n : ℂ) else 0

theorem abscissaOfAbsConv_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le_one
    {b : ℝ} (hb : 0 < b) :
    LSeries.abscissaOfAbsConv (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨32 / b ^ 2, ?_⟩
  intro n hn
  exact norm_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le hb n

theorem iterate_logMul_three_ccmGuinandWeilThirdGradePrimeDirichletCoeff
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ((LSeries.logMul^[3]) (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)) n =
      32 * ccmGuinandWeilActiveCriticalMellinAtomCoeff b n := by
  rw [show ((LSeries.logMul^[3])
      (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)) n =
      Complex.log n ^ 3 * ccmGuinandWeilThirdGradePrimeDirichletCoeff b n by
    simp [Function.iterate_succ_apply, pow_succ]
    ring]
  rw [ccmGuinandWeilThirdGradePrimeDirichletCoeff,
    ccmGuinandWeilActiveCriticalMellinAtomCoeff]
  by_cases hbn : b < Real.log n
  · rw [if_pos hbn, if_pos hbn,
      ccmGuinandWeilPrimeEntryThirdJetScale]
    have hn1 : 1 < n := by
      have hlog : 0 < Real.log n := hb.trans hbn
      exact Nat.one_lt_cast.mp ((Real.log_pos_iff (by positivity)).mp hlog)
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log n ≠ 0 := (Real.log_pos (Nat.one_lt_cast.mpr hn1)).ne'
    have hclog0 : ((Real.log n : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hlog0
    have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
    have hlogEq : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [hncast]
      exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hlogEq]
    push_cast
    rw [hlogEq]
    field_simp [hclog0]
  · rw [if_neg hbn, if_neg hbn]
    ring

theorem iteratedDeriv_three_LSeries_ccmGuinandWeilThirdGradePrimeDirichletCoeff
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    iteratedDeriv 3
        (LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)) u =
      -32 * LSeries (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) u := by
  have habs : LSeries.abscissaOfAbsConv
      (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) < u.re :=
    (abscissaOfAbsConv_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le_one hb).trans_lt
      (by exact_mod_cast hu)
  rw [LSeries_iteratedDeriv 3 habs]
  have hcoeff : ((LSeries.logMul^[3])
      (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)) =
      fun n => 32 * ccmGuinandWeilActiveCriticalMellinAtomCoeff b n := by
    funext n
    exact iterate_logMul_three_ccmGuinandWeilThirdGradePrimeDirichletCoeff hb n
  rw [hcoeff]
  have hscale : LSeries
      (fun n => 32 * ccmGuinandWeilActiveCriticalMellinAtomCoeff b n) u =
      32 * LSeries (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) u := by
    simp only [LSeries]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      ring
  rw [hscale]
  norm_num

theorem analyticOnNhd_ccmGuinandWeilThirdGradePolarLaplaceMoment
    {b : ℝ} (hb : 0 < b) (m : ℕ) :
    AnalyticOnNhd ℂ (ccmGuinandWeilThirdGradePolarLaplaceMoment b m)
      {u : ℂ | 1 / 2 < u.re} := by
  have hdiff : DifferentiableOn ℂ
      (ccmGuinandWeilThirdGradePolarLaplaceMoment b m)
      {u : ℂ | 1 / 2 < u.re} := by
    intro u hu
    exact (hasDerivAt_ccmGuinandWeilThirdGradePolarLaplaceMoment hb m hu)
      |>.differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

def ccmGuinandWeilThirdGradeTailMellinDefect (b : ℝ) (u : ℂ) : ℂ :=
  ccmGuinandWeilThirdGradePolarTailLaplace b u -
    LSeries (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) u

/-- **Cubic Abel cancellation.** Three spectral derivatives of the cumulative third-grade
source remove the inverse-cubic wall exactly and produce the unweighted tail Mellin defect. -/
theorem iteratedDeriv_three_ccmAbelCumulativeSourceContinuation_eq_tailDefect
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 1 < u.re) :
    iteratedDeriv 3
        (ccmAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) u =
      32 * ccmGuinandWeilThirdGradeTailMellinDefect b u := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b =ᶠ[𝓝 u]
      fun z => LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) z -
        ccmGuinandWeilThirdGradePolarLaplaceMoment b 0 z := by
    filter_upwards [hopen.mem_nhds hu] with z hz
    rw [ccmAbelCumulativeSourceContinuation_eq_atomic_sub_polar hb hz]
    rw [ccmGuinandWeilThirdGradePolarLaplaceMoment]
    simp
  rw [heq.iteratedDeriv_eq 3]
  have habs : LSeries.abscissaOfAbsConv
      (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) < u.re :=
    (abscissaOfAbsConv_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le_one hb).trans_lt
      (by exact_mod_cast hu)
  have hL : ContDiffAt ℂ (3 : WithTop ℕ∞)
      (LSeries (ccmGuinandWeilThirdGradePrimeDirichletCoeff b)) u :=
    (LSeries_analyticOnNhd (ccmGuinandWeilThirdGradePrimeDirichletCoeff b) u habs)
      |>.contDiffAt
  have hP : ContDiffAt ℂ (3 : WithTop ℕ∞)
      (ccmGuinandWeilThirdGradePolarLaplaceMoment b 0) u :=
    (analyticOnNhd_ccmGuinandWeilThirdGradePolarLaplaceMoment hb 0 u
      (by
        have huHalf : (1 / 2 : ℝ) < u.re := by linarith
        simpa only [Set.mem_setOf_eq] using huHalf))
      |>.contDiffAt
  rw [iteratedDeriv_fun_sub hL hP,
    iteratedDeriv_three_LSeries_ccmGuinandWeilThirdGradePrimeDirichletCoeff hb hu,
    iteratedDeriv_three_ccmGuinandWeilThirdGradePolarLaplaceMoment_zero hb (by linarith)]
  rw [ccmGuinandWeilThirdGradeTailMellinDefect]
  ring

/-! ## Entire wall head -/

def ccmGuinandWeilPolarCompactLaplace (b : ℝ) (u : ℂ) : ℂ :=
  ∫ h : ℝ in Set.Ioc 0 b,
    Complex.exp (-u * (h : ℂ)) * (2 * Real.cosh (h / 2) : ℝ)

theorem differentiableAt_ccmGuinandWeilPolarCompactLaplace
    {b : ℝ} (hb : 0 < b) (u₀ : ℂ) :
    DifferentiableAt ℂ (ccmGuinandWeilPolarCompactLaplace b) u₀ := by
  let F : ℂ → ℝ → ℂ := fun u h =>
    Complex.exp (-u * (h : ℂ)) * (2 * Real.cosh (h / 2) : ℝ)
  let F' : ℂ → ℝ → ℂ := fun u h =>
    (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) *
      (2 * Real.cosh (h / 2) : ℝ)
  let bound : ℝ → ℝ := fun h =>
    h * Real.exp ((‖u₀‖ + 1) * h) * (2 * Real.cosh (h / 2))
  have hFmeas : ∀ᶠ u in 𝓝 u₀,
      AEStronglyMeasurable (F u) (volume.restrict (Set.Ioc 0 b)) := by
    filter_upwards with u
    apply Measurable.aestronglyMeasurable
    dsimp only [F]
    fun_prop
  have hFint : Integrable (F u₀) (volume.restrict (Set.Ioc 0 b)) := by
    change IntegrableOn (F u₀) (Set.Ioc 0 b)
    have hc : Continuous (F u₀) := by
      dsimp only [F]
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hF'meas : AEStronglyMeasurable (F' u₀)
      (volume.restrict (Set.Ioc 0 b)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F']
    fun_prop
  have hboundInt : Integrable bound (volume.restrict (Set.Ioc 0 b)) := by
    change IntegrableOn bound (Set.Ioc 0 b)
    have hc : Continuous bound := by
      dsimp only [bound]
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ᵐ h ∂volume.restrict (Set.Ioc 0 b),
      ∀ u ∈ Metric.ball u₀ 1, ‖F' u h‖ ≤ bound h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    intro u hu
    have hh0 : 0 < h := hh.1
    have hnorm : ‖u‖ < ‖u₀‖ + 1 := by
      calc
        ‖u‖ ≤ ‖u - u₀‖ + ‖u₀‖ := by
          have := norm_add_le (u - u₀) u₀
          simpa only [sub_add_cancel] using this
        _ < ‖u₀‖ + 1 := by
          rw [Metric.mem_ball, dist_eq_norm] at hu
          linarith
    have hre : -u.re ≤ ‖u₀‖ + 1 := by
      have hure : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
      have := (neg_le_of_abs_le hure)
      linarith
    have hexp : Real.exp (-u.re * h) ≤
        Real.exp ((‖u₀‖ + 1) * h) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_right hre hh0.le
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_pos hh0, Complex.norm_exp, norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) (Real.cosh_pos _))]
    have hrexp : (-u * (h : ℂ)).re = -u.re * h := by simp [mul_re]
    rw [hrexp]
    gcongr
  have hdiff : ∀ᵐ h ∂volume.restrict (Set.Ioc 0 b),
      ∀ u ∈ Metric.ball u₀ 1, HasDerivAt (fun u => F u h) (F' u h) u := by
    filter_upwards with h
    intro u hu
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (h : ℂ)))
        (-(h : ℂ) * Complex.exp (-u * (h : ℂ))) u := by
      simpa [mul_comm] using (((hasDerivAt_id u).neg.mul_const (h : ℂ)).cexp)
    dsimp only [F, F']
    exact hexp.mul_const (2 * Real.cosh (h / 2) : ℝ)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc 0 b)) (F := F) (F' := F')
    (x₀ := u₀) (s := Metric.ball u₀ 1) (bound := bound)
    (Metric.ball_mem_nhds u₀ zero_lt_one) hFmeas hFint hF'meas
    hbound hboundInt hdiff
  change DifferentiableAt ℂ
    (fun u : ℂ => ∫ h : ℝ in Set.Ioc 0 b,
      Complex.exp (-u * (h : ℂ)) * (2 * Real.cosh (h / 2) : ℝ)) u₀
  exact hmain.2.differentiableAt

theorem analyticOnNhd_ccmGuinandWeilPolarCompactLaplace
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (ccmGuinandWeilPolarCompactLaplace b) Set.univ := by
  have hdiff : Differentiable ℂ (ccmGuinandWeilPolarCompactLaplace b) :=
    fun u => differentiableAt_ccmGuinandWeilPolarCompactLaplace hb u
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

def ccmGuinandWeilThirdGradePolarHead (b : ℝ) (s : ℂ) : ℂ :=
  ccmGuinandWeilPolarCompactLaplace b (s + 1 / 2)

theorem analyticOnNhd_ccmGuinandWeilThirdGradePolarHead
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (ccmGuinandWeilThirdGradePolarHead b) Set.univ := by
  intro s hs
  have hg := analyticOnNhd_ccmGuinandWeilPolarCompactLaplace hb
    (s + 1 / 2) (Set.mem_univ _)
  have hf : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := by fun_prop
  have hc := AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2) (x := s) hg hf
  change AnalyticAt ℂ
    (ccmGuinandWeilPolarCompactLaplace b ∘ fun z : ℂ => z + 1 / 2) s
  exact hc

def ccmGuinandWeilCriticalMellinAtomCoeff (n : ℕ) : ℂ :=
  (criticalMellinAtomWeight n : ℂ)

def ccmGuinandWeilInactiveCriticalMellinAtomCoeff (b : ℝ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 2 ⌊Real.exp b⌋₊ then (criticalMellinAtomWeight n : ℂ) else 0

def ccmGuinandWeilThirdGradePrimeHead (b : ℝ) (u : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp b⌋₊,
    LSeries.term ccmGuinandWeilCriticalMellinAtomCoeff u n

theorem analyticOnNhd_ccmGuinandWeilThirdGradePrimeHead (b : ℝ) :
    AnalyticOnNhd ℂ (ccmGuinandWeilThirdGradePrimeHead b) Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro u
  have heq : (fun u : ℂ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp b⌋₊,
      LSeries.term ccmGuinandWeilCriticalMellinAtomCoeff u n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp b⌋₊,
        fun u : ℂ => LSeries.term ccmGuinandWeilCriticalMellinAtomCoeff u n := by
    funext z
    rw [Finset.sum_apply]
  change DifferentiableAt ℂ
    (fun u : ℂ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp b⌋₊,
      LSeries.term ccmGuinandWeilCriticalMellinAtomCoeff u n) u
  rw [heq]
  apply DifferentiableAt.sum
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  simp only [LSeries.term, if_neg hn0]
  apply DifferentiableAt.div
  · fun_prop
  · exact differentiableAt_id.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn0))
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hn0))

theorem criticalMellinAtomCoeff_eq_active_add_inactive
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ccmGuinandWeilCriticalMellinAtomCoeff n =
      ccmGuinandWeilActiveCriticalMellinAtomCoeff b n +
        ccmGuinandWeilInactiveCriticalMellinAtomCoeff b n := by
  rw [ccmGuinandWeilCriticalMellinAtomCoeff,
    ccmGuinandWeilActiveCriticalMellinAtomCoeff,
    ccmGuinandWeilInactiveCriticalMellinAtomCoeff]
  by_cases hn2 : 2 ≤ n
  · by_cases hactive : b < Real.log n
    · rw [if_pos hactive]
      have hexp : Real.exp b < (n : ℝ) := by
        calc
          Real.exp b < Real.exp (Real.log n) := Real.exp_lt_exp.mpr hactive
          _ = (n : ℝ) := Real.exp_log (by positivity)
      have hfloor : ⌊Real.exp b⌋₊ < n :=
        (Nat.floor_lt (Real.exp_pos b).le).mpr hexp
      rw [if_neg]
      · ring
      · simp only [Finset.mem_Icc]
        exact fun h => (not_le_of_gt hfloor) h.2
    · rw [if_neg hactive]
      have hlog : Real.log n ≤ b := le_of_not_gt hactive
      have hnexp : (n : ℝ) ≤ Real.exp b := by
        calc
          (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp b := Real.exp_le_exp.mpr hlog
      have hfloor : n ≤ ⌊Real.exp b⌋₊ := Nat.le_floor hnexp
      rw [if_pos (Finset.mem_Icc.mpr ⟨hn2, hfloor⟩)]
      ring
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl <;>
      simp [criticalMellinAtomWeight, hb.ne']

theorem norm_ccmGuinandWeilCriticalMellinAtomCoeff_le_nat
    (n : ℕ) (hn : n ≠ 0) :
    ‖ccmGuinandWeilCriticalMellinAtomCoeff n‖ ≤ (n : ℝ) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hrpow : (n : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hn1) (by norm_num)
  have hatom : criticalMellinAtomWeight n ≤ Real.log n := by
    calc
      criticalMellinAtomWeight n ≤
          Real.log n * (n : ℝ) ^ (-1 / 2 : ℝ) :=
        criticalMellinAtomWeight_le_log n
      _ ≤ Real.log n * 1 := mul_le_mul_of_nonneg_left hrpow hlog0
      _ = Real.log n := mul_one _
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ))
    linarith
  rw [ccmGuinandWeilCriticalMellinAtomCoeff, norm_real,
    Real.norm_eq_abs, abs_of_nonneg (criticalMellinAtomWeight_nonneg' n)]
  exact hatom.trans hlogn

theorem abscissaOfAbsConv_ccmGuinandWeilCriticalMellinAtomCoeff_le_two :
    LSeries.abscissaOfAbsConv ccmGuinandWeilCriticalMellinAtomCoeff ≤ 2 := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := ccmGuinandWeilCriticalMellinAtomCoeff) (x := (1 : ℝ))
    ⟨1, fun n hn => ?_⟩
  · convert h using 1 <;> norm_num
  · simpa only [one_mul, Real.rpow_one] using
      norm_ccmGuinandWeilCriticalMellinAtomCoeff_le_nat n hn

theorem abscissaOfAbsConv_ccmGuinandWeilActiveCriticalMellinAtomCoeff_le_two
    {b : ℝ} (hb : 0 < b) :
    LSeries.abscissaOfAbsConv
      (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) ≤ 2 := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := ccmGuinandWeilActiveCriticalMellinAtomCoeff b) (x := (1 : ℝ))
    ⟨1, fun n hn => ?_⟩
  · convert h using 1 <;> norm_num
  · rw [ccmGuinandWeilActiveCriticalMellinAtomCoeff]
    split_ifs
    · change ‖ccmGuinandWeilCriticalMellinAtomCoeff n‖ ≤
        1 * (n : ℝ) ^ (1 : ℝ)
      simpa only [one_mul, Real.rpow_one] using
        norm_ccmGuinandWeilCriticalMellinAtomCoeff_le_nat n hn
    · simp

theorem abscissaOfAbsConv_ccmGuinandWeilInactiveCriticalMellinAtomCoeff_le_two
    (b : ℝ) :
    LSeries.abscissaOfAbsConv
      (ccmGuinandWeilInactiveCriticalMellinAtomCoeff b) ≤ 2 := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := ccmGuinandWeilInactiveCriticalMellinAtomCoeff b) (x := (1 : ℝ))
    ⟨1, fun n hn => ?_⟩
  · convert h using 1 <;> norm_num
  · rw [ccmGuinandWeilInactiveCriticalMellinAtomCoeff]
    split_ifs
    · change ‖ccmGuinandWeilCriticalMellinAtomCoeff n‖ ≤
        1 * (n : ℝ) ^ (1 : ℝ)
      simpa only [one_mul, Real.rpow_one] using
        norm_ccmGuinandWeilCriticalMellinAtomCoeff_le_nat n hn
    · simp

theorem LSeries_ccmGuinandWeilInactiveCriticalMellinAtomCoeff_eq_primeHead
    (b : ℝ) (u : ℂ) :
    LSeries (ccmGuinandWeilInactiveCriticalMellinAtomCoeff b) u =
      ccmGuinandWeilThirdGradePrimeHead b u := by
  rw [LSeries, tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp b⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [LSeries.term, ccmGuinandWeilInactiveCriticalMellinAtomCoeff,
      ccmGuinandWeilCriticalMellinAtomCoeff, hn]
  · intro n hn
    simp [LSeries.term, ccmGuinandWeilInactiveCriticalMellinAtomCoeff, hn]

theorem LSeries_ccmGuinandWeilCriticalMellinAtomCoeff_eq_active_add_primeHead
    {b : ℝ} (hb : 0 < b) {u : ℂ} (hu : 2 < u.re) :
    LSeries ccmGuinandWeilCriticalMellinAtomCoeff u =
      LSeries (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) u +
        ccmGuinandWeilThirdGradePrimeHead b u := by
  have ha : LSeriesSummable
      (ccmGuinandWeilActiveCriticalMellinAtomCoeff b) u :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt
      (abscissaOfAbsConv_ccmGuinandWeilActiveCriticalMellinAtomCoeff_le_two hb)
      (by
        change ((2 : ℝ) : EReal) < (u.re : EReal)
        exact EReal.coe_lt_coe hu))
  have hi : LSeriesSummable
      (ccmGuinandWeilInactiveCriticalMellinAtomCoeff b) u :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt
      (abscissaOfAbsConv_ccmGuinandWeilInactiveCriticalMellinAtomCoeff_le_two b)
      (by
        change ((2 : ℝ) : EReal) < (u.re : EReal)
        exact EReal.coe_lt_coe hu))
  have hcoeff : ccmGuinandWeilCriticalMellinAtomCoeff =
      ccmGuinandWeilActiveCriticalMellinAtomCoeff b +
        ccmGuinandWeilInactiveCriticalMellinAtomCoeff b := by
    funext n
    exact criticalMellinAtomCoeff_eq_active_add_inactive hb n
  rw [hcoeff, LSeries_add ha hi,
    LSeries_ccmGuinandWeilInactiveCriticalMellinAtomCoeff_eq_primeHead]

theorem LSeries_term_ccmGuinandWeilCriticalMellinAtomCoeff_eq_vonMangoldt_shift
    (u : ℂ) (n : ℕ) :
    LSeries.term ccmGuinandWeilCriticalMellinAtomCoeff u n =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (u + 1 / 2) n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    change (criticalMellinAtomWeight n : ℂ) / (n : ℂ) ^ u = _
    rw [criticalMellinAtomWeight_cast_eq_lSeriesTerm_half hn,
      LSeries.term_of_ne_zero hn]
    rw [div_div, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    congr 2
    ring

theorem LSeries_ccmGuinandWeilCriticalMellinAtomCoeff_eq_primeChannel
    (u : ℂ) :
    LSeries ccmGuinandWeilCriticalMellinAtomCoeff u =
      vonMangoldtPrimeLaplaceChannelComplex (u - 1 / 2) := by
  rw [LSeries, vonMangoldtPrimeLaplaceChannelComplex, LSeries]
  have hshift : u - 1 / 2 + 1 = u + 1 / 2 := by ring
  rw [hshift]
  exact tsum_congr
    (LSeries_term_ccmGuinandWeilCriticalMellinAtomCoeff_eq_vonMangoldt_shift u)

theorem continuousPolarLaplaceChannelComplex_eq_polarHead_add_tail
    {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 0 < s.re) :
    continuousPolarLaplaceChannelComplex s =
      ccmGuinandWeilThirdGradePolarHead b s +
        ccmGuinandWeilThirdGradePolarTailLaplace b (s + 1 / 2) := by
  let f : ℝ → ℂ := fun h =>
    Complex.exp (-(s + 1 / 2) * (h : ℂ)) *
      (2 * Real.cosh (h / 2) : ℝ)
  have hs0 : (-s).re < 0 := by simp; linarith
  have hs1 : (-(s + 1)).re < 0 := by simp; linarith
  have hfun : f = fun h : ℝ =>
      Complex.exp ((-s) * h) + Complex.exp (-(s + 1) * h) := by
    funext h
    dsimp only [f]
    rw [Real.cosh_eq]
    push_cast
    ring_nf
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> ring
  have hfull : IntegrableOn f (Set.Ioi 0) := by
    rw [hfun]
    exact (integrableOn_exp_mul_complex_Ioi hs0 0).add
      (integrableOn_exp_mul_complex_Ioi hs1 0)
  have hhead : IntegrableOn f (Set.Ioc 0 b) :=
    hfull.mono_set Set.Ioc_subset_Ioi_self
  have htail : IntegrableOn f (Set.Ioi b) :=
    hfull.mono_set (Set.Ioi_subset_Ioi hb.le)
  rw [continuousPolarLaplaceChannelComplex,
    ccmGuinandWeilThirdGradePolarHead,
    ccmGuinandWeilPolarCompactLaplace,
    ccmGuinandWeilThirdGradePolarTailLaplace]
  change (∫ h : ℝ in Set.Ioi 0, f h) =
    (∫ h : ℝ in Set.Ioc 0 b, f h) + ∫ h : ℝ in Set.Ioi b, f h
  rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail,
    Set.Ioc_union_Ioi_eq_Ioi hb.le]

def ccmGuinandWeilThirdGradeWallHead (b : ℝ) (s : ℂ) : ℂ :=
  ccmGuinandWeilThirdGradePolarHead b s -
    ccmGuinandWeilThirdGradePrimeHead b (s + 1 / 2)

theorem analyticOnNhd_ccmGuinandWeilThirdGradeWallHead
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (ccmGuinandWeilThirdGradeWallHead b) Set.univ := by
  intro s hs
  have hpolar := analyticOnNhd_ccmGuinandWeilThirdGradePolarHead hb s hs
  have hprimeAt := analyticOnNhd_ccmGuinandWeilThirdGradePrimeHead b
    (s + 1 / 2) (Set.mem_univ _)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := by fun_prop
  have hprime := AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
    (x := s) hprimeAt hshift
  change AnalyticAt ℂ
    (fun z => ccmGuinandWeilThirdGradePolarHead b z -
      ccmGuinandWeilThirdGradePrimeHead b (z + 1 / 2)) s
  exact hpolar.sub hprime

/-- Wall localization of the full critical Mellin defect.  Above a safe Euler line, the defect is
the base-wall-invariant tail defect plus an entire compact/finite head. -/
theorem criticalMellinDefectLaplaceChannelComplex_eq_tailDefect_add_wallHead
    {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 3 / 2 < s.re) :
    criticalMellinDefectLaplaceChannelComplex s =
      ccmGuinandWeilThirdGradeTailMellinDefect b (s + 1 / 2) +
        ccmGuinandWeilThirdGradeWallHead b s := by
  have hs0 : 0 < s.re := by linarith
  have hu : 2 < (s + 1 / 2).re := by
    norm_num [div_re]
    linarith
  have hprime : vonMangoldtPrimeLaplaceChannelComplex s =
      LSeries ccmGuinandWeilCriticalMellinAtomCoeff (s + 1 / 2) := by
    rw [LSeries_ccmGuinandWeilCriticalMellinAtomCoeff_eq_primeChannel]
    congr 1
    ring
  rw [criticalMellinDefectLaplaceChannelComplex,
    continuousPolarLaplaceChannelComplex_eq_polarHead_add_tail hb hs0,
    hprime,
    LSeries_ccmGuinandWeilCriticalMellinAtomCoeff_eq_active_add_primeHead hb hu,
    ccmGuinandWeilThirdGradeTailMellinDefect,
    ccmGuinandWeilThirdGradeWallHead]
  ring

theorem exists_global_bound_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C := by
  obtain ⟨B, C, hbB, hC, htail⟩ :=
    exists_tail_bound_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed hb hL
  let D : ℝ := (32 / b ^ 2) * Real.exp B +
    (64 / b ^ 3) * B * Real.exp (B / 2)
  have hB0 : 0 < B := hb.trans_le hbB
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro H hbH
  by_cases hBH : B < H
  · exact (htail H hBH).trans (le_add_of_nonneg_right hD)
  · have hHB : H ≤ B := le_of_not_gt hBH
    have hq := ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hbH.le
    rw [hq, ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
    have hp0 := ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg
      (b := b) (H := H)
    have hr0 := ccmGuinandWeilPolarThirdGradeRateWindow_nonneg hb hbH.le
    have hp : ccmGuinandWeilPrimeThirdGradeRateWindow b H ≤
        (32 / b ^ 2) * Real.exp B := by
      calc
        ccmGuinandWeilPrimeThirdGradeRateWindow b H ≤
            (32 / b ^ 2) * Real.exp H :=
          ccmGuinandWeilPrimeThirdGradeRateWindow_le hb H
        _ ≤ (32 / b ^ 2) * Real.exp B := by
          gcongr
    have hr : ccmGuinandWeilPolarThirdGradeRateWindow b H ≤
        (64 / b ^ 3) * B * Real.exp (B / 2) := by
      calc
        ccmGuinandWeilPolarThirdGradeRateWindow b H ≤
            (64 / b ^ 3) * H * Real.exp (H / 2) :=
          ccmGuinandWeilPolarThirdGradeRateWindow_le hb hbH.le
        _ ≤ (64 / b ^ 3) * B * Real.exp (B / 2) := by
          have hcoef : 0 ≤ 64 / b ^ 3 := by positivity
          have hH0 : 0 ≤ H := (hb.trans hbH).le
          gcongr
    calc
      |ccmGuinandWeilPrimeThirdGradeRateWindow b H -
          ccmGuinandWeilPolarThirdGradeRateWindow b H| ≤
          |ccmGuinandWeilPrimeThirdGradeRateWindow b H| +
            |ccmGuinandWeilPolarThirdGradeRateWindow b H| := abs_sub _ _
      _ = ccmGuinandWeilPrimeThirdGradeRateWindow b H +
          ccmGuinandWeilPolarThirdGradeRateWindow b H := by
        rw [abs_of_nonneg hp0, abs_of_nonneg hr0]
      _ ≤ D := by
        dsimp only [D]
        exact add_le_add hp hr
      _ ≤ C + D := le_add_of_nonneg_left hC

/-! ## Cubic continuation and RH completeness -/

/-- Half-plane reached after third-grade Abel damping and the critical half-shift. -/
def ccmGuinandWeilCriticalMellinContinuationHalfPlane : Set ℂ :=
  {s : ℂ | -1 / 2 < s.re}

theorem isOpen_ccmGuinandWeilCriticalMellinContinuationHalfPlane :
    IsOpen ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- The cubic Abel continuation of the full critical Mellin defect. -/
def ccmGuinandWeilThirdGradeAbelCriticalMellinExtension
    (b : ℝ) (s : ℂ) : ℂ :=
  (1 / 32 : ℂ) * iteratedDeriv 3
      (ccmAbelCumulativeSourceContinuation
        (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) (s + 1 / 2) +
    ccmGuinandWeilThirdGradeWallHead b s

theorem analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_bounded
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C) :
    AnalyticOnNhd ℂ
      (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
  have hG := analyticOnNhd_ccmAbelCumulativeSourceContinuation_of_bounded
    (measurable_ccmGuinandWeilThirdGradeCumulativeMeasurable hb)
    hb hC hbound
  have hG3 : AnalyticOnNhd ℂ
      (iteratedDeriv 3
        (ccmAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b))
      {u : ℂ | 0 < u.re} := by
    simpa only [iteratedDeriv_eq_iterate] using hG.iterated_deriv 3
  intro s hs
  have hu : 0 < (s + 1 / 2).re := by
    change -1 / 2 < s.re at hs
    norm_num [div_re]
    linarith
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := by fun_prop
  have hGcomp := AnalyticAt.comp (f := fun z : ℂ => z + 1 / 2)
    (hG3 (s + 1 / 2) hu) hshift
  have hwall := analyticOnNhd_ccmGuinandWeilThirdGradeWallHead hb
    s (Set.mem_univ _)
  change AnalyticAt ℂ
    (fun z => (1 / 32 : ℂ) * iteratedDeriv 3
        (ccmAbelCumulativeSourceContinuation
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b) (z + 1 / 2) +
      ccmGuinandWeilThirdGradeWallHead b z) s
  exact analyticAt_const.mul hGcomp |>.add hwall

theorem analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_completed
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    AnalyticOnNhd ℂ
      (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_global_bound_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed hb hL
  exact analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_bounded
    hb hC hbound

theorem ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_laplaceDefect
    {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 3 / 2 < s.re) :
    ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b s =
      criticalMellinDefectLaplaceChannelComplex s := by
  have hu : 1 < (s + 1 / 2).re := by
    norm_num [div_re]
    linarith
  rw [ccmGuinandWeilThirdGradeAbelCriticalMellinExtension,
    iteratedDeriv_three_ccmAbelCumulativeSourceContinuation_eq_tailDefect hb hu,
    criticalMellinDefectLaplaceChannelComplex_eq_tailDefect_add_wallHead hb hs]
  ring

theorem ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_safe
    {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 3 / 2 < s.re) :
    ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b s =
      regularizedCriticalMellinDefect s := by
  have hs0 : 0 < s.re := by linarith
  rw [ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_laplaceDefect hb hs,
    criticalMellinDefectLaplaceChannelComplex_eq_continued hs0,
    ← regularizedCriticalMellinDefect_eq_continued hs0]

theorem analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane :
    AnalyticOnNhd ℂ regularizedCriticalMellinDefect {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
  have hden : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hsne : s + 1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hzeta : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      norm_num [Complex.add_re]
      linarith)
  have hreg : regularizedRiemannZeta (s + 1) ≠ 0 := by
    rw [regularizedRiemannZeta_of_ne_one hsne]
    exact mul_ne_zero (sub_ne_zero.mpr hsne) hzeta
  have hregAt : AnalyticAt ℂ regularizedRiemannZeta (s + 1) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (s + 1) (Set.mem_univ _)
  have hlogBase : AnalyticAt ℂ (logDeriv regularizedRiemannZeta) (s + 1) := by
    rw [logDeriv]
    exact hregAt.deriv.div hregAt hreg
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z + 1)) s :=
    AnalyticAt.comp (f := fun z : ℂ => z + 1) hlogBase hshift
  have hrat : AnalyticAt ℂ (fun z : ℂ => 1 / (z + 1)) s :=
    analyticAt_const.div hshift hden
  change AnalyticAt ℂ
    (fun z : ℂ => 1 / (z + 1) +
      logDeriv regularizedRiemannZeta (z + 1)) s
  exact hrat.add hlog

theorem ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_of_bounded
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C) :
    ∀ s : ℂ, 0 < s.re →
      ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b s =
        regularizedCriticalMellinDefect s := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hsubset : U ⊆ ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
    intro s hs
    change -1 / 2 < s.re
    change 0 < s.re at hs
    linarith
  have hA : AnalyticOnNhd ℂ
      (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b) U :=
    (analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_bounded
      hb hC hbound).mono hsubset
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  let z₀ : ℂ := 2
  have hz₀ : z₀ ∈ U := by
    change 0 < (2 : ℂ).re
    norm_num
  have hsafeOpen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hz₀safe : z₀ ∈ {s : ℂ | 3 / 2 < s.re} := by
    change 3 / 2 < (2 : ℂ).re
    norm_num
  have hevent :
      ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b =ᶠ[nhds z₀]
        regularizedCriticalMellinDefect := by
    filter_upwards [hsafeOpen.mem_nhds hz₀safe] with s hs
    exact ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_safe hb hs
  have heq := hA.eqOn_of_preconnected_of_eventuallyEq hR hUpre hz₀ hevent
  intro s hs
  exact heq (show s ∈ U from hs)

theorem ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    ∀ s : ℂ, 0 < s.re →
      ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b s =
        regularizedCriticalMellinDefect s := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_global_bound_ccmGuinandWeilThirdGradeCumulativeMeasurable_of_completed hb hL
  exact ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_of_bounded
    hb hC hbound

/-- Any analytic extension of the regularized critical-Mellin defect across the third-grade
half-plane excludes every off-critical Xi zero. -/
theorem riemannHypothesis_of_regularizedCriticalMellinDefect_extension
    (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A ccmGuinandWeilCriticalMellinContinuationHalfPlane)
    (hagree : ∀ s : ℂ, 0 < s.re → A s = regularizedCriticalMellinDefect s) :
    RiemannHypothesis := by
  let B : ℂ → ℂ := fun w =>
    -I * (A (-1 / 2 - I * w) +
      gammaRealLogConnection (1 / 2 - I * w))
  have hB : AnalyticOnNhd ℂ B ccmXiUpperHalfPlane := by
    intro w hw
    change 0 < w.im at hw
    have hs : -1 / 2 - I * w ∈
        ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
      change -1 / 2 < (-1 / 2 - I * w).re
      simp [mul_re]
      exact hw
    have hinner : AnalyticAt ℂ (fun z : ℂ => -1 / 2 - I * z) w := by
      fun_prop
    have hAcomp : AnalyticAt ℂ (fun z : ℂ => A (-1 / 2 - I * z)) w :=
      AnalyticAt.comp (f := fun z : ℂ => -1 / 2 - I * z)
        (hA _ hs) hinner
    have hgammaArg : 0 < ((1 / 2 - I * w) / 2).re := by
      norm_num [Complex.div_re, mul_re]
      linarith
    have hgammaBase : AnalyticAt ℂ Complex.digamma ((1 / 2 - I * w) / 2) :=
      digamma_analyticOnNhd_re_pos _ hgammaArg
    have hgammaInner : AnalyticAt ℂ (fun z : ℂ => (1 / 2 - I * z) / 2) w := by
      fun_prop
    have hgammaComp : AnalyticAt ℂ
        (fun z : ℂ => Complex.digamma ((1 / 2 - I * z) / 2)) w :=
      AnalyticAt.comp (f := fun z : ℂ => (1 / 2 - I * z) / 2)
        hgammaBase hgammaInner
    have hconn : AnalyticAt ℂ
        (fun z : ℂ => gammaRealLogConnection (1 / 2 - I * z)) w := by
      unfold gammaRealLogConnection
      fun_prop
    exact analyticAt_const.mul (hAcomp.add hconn)
  have hBagree : ∀ w : ℂ, 1 / 2 < w.im → B w = logDeriv XiC w := by
    intro w hw
    let z : ℂ := -w
    let s : ℂ := 1 / 2 + z * I
    have hsre : 1 < s.re := by
      dsimp only [s, z]
      simp [mul_re]
      linarith
    have hspos : 0 < s.re := lt_trans zero_lt_one hsre
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.zero_re] at hre
      linarith
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [Complex.one_re] at hre
      linarith
    have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re hsre
    have htrace : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
      rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
        hspos hs1 hzeta]
      exact (logDeriv_XiC_eq_relativeResolventTrace
        (by
          change xi s ≠ 0
          rw [xi_eq_archFactor_mul_zeta hs0 hs1
            (Gammaℝ_ne_zero_of_re_pos hspos)]
          exact mul_ne_zero
            (archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)) hzeta)).symm
    have hsource := continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
      hspos hs0 hs1
    have hcoord : xiCriticalMellinCoordinate z = -1 / 2 - I * w := by
      dsimp only [xiCriticalMellinCoordinate, z]
      ring
    have hgammaCoord : 1 / 2 + z * I = 1 / 2 - I * w := by
      dsimp only [z]
      ring
    have hdefRe : 0 < (-1 / 2 - I * w).re := by
      simp [mul_re]
      linarith
    have hdef := hagree (-1 / 2 - I * w) hdefRe
    have hreg := regularizedCriticalMellinDefect_eq_continued hdefRe
    dsimp only [B]
    rw [hdef]
    have hsource' :
        continuedPrimeArchSourceRelativeTrace z =
          I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
            gammaRealLogConnection (1 / 2 - I * w)) := by
      rw [hsource, continuedMellinGammaSourceTrace, hcoord, hgammaCoord]
      rw [← hreg]
    rw [hsource'] at htrace
    rw [show logDeriv XiC z = -logDeriv XiC w by
      dsimp only [z]
      rw [logDeriv_XiC_neg]] at htrace
    calc
      -I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
          gammaRealLogConnection (1 / 2 - I * w)) =
          -(I * (regularizedCriticalMellinDefect (-1 / 2 - I * w) +
            gammaRealLogConnection (1 / 2 - I * w))) := by ring
      _ = -(-logDeriv XiC w) := by rw [htrace]
      _ = logDeriv XiC w := neg_neg _
  exact riemannHypothesis_of_upper_logDeriv_extension B hB hBagree

/-- **Cumulative-source completeness.** A uniform bound on the measurable cumulative
prime-minus-polar third-grade source already forces RH; ordinary convergence is not needed. -/
theorem riemannHypothesis_of_bounded_ccmGuinandWeilThirdGradeCumulativeMeasurable
    {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbound : ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_regularizedCriticalMellinDefect_extension
    (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b)
    (analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_bounded
      hb hC hbound)
    (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized_of_bounded
      hb hC hbound)

/-- If RH fails, the literal cumulative third-grade source escapes every finite bound beyond
every positive base wall.  This is the contrapositive form of cubic Abel completeness. -/
theorem ccmGuinandWeilThirdGradeCumulativeMeasurable_unbounded_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    ∀ C : ℝ, 0 ≤ C → ∃ H : ℝ, b < H ∧
      C < |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| := by
  intro C hC
  by_contra hnot
  have hbound : ∀ H : ℝ, b < H →
      |ccmGuinandWeilThirdGradeCumulativeMeasurable b H| ≤ C := by
    intro H hbH
    exact le_of_not_gt fun hgt => hnot ⟨H, hbH, hgt⟩
  exact hRH
    (riemannHypothesis_of_bounded_ccmGuinandWeilThirdGradeCumulativeMeasurable
      hb hC hbound)

/-- **Third-grade Abel completeness.** Convergence of one completed four-unit third-grade
Guinand--Weil window forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow
    {b L : ℝ} (hb : 0 < b)
    (hL : Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L)) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_regularizedCriticalMellinDefect_extension
    (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension b)
    (analyticOnNhd_ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_of_completed hb hL)
    (ccmGuinandWeilThirdGradeAbelCriticalMellinExtension_eq_regularized hb hL)

theorem not_tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) {b : ℝ} (hb : 0 < b) (L : ℝ) :
    ¬Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b)
      atTop (nhds L) := by
  exact fun hL => hRH
    (riemannHypothesis_of_tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow hb hL)

end

end RHTower
