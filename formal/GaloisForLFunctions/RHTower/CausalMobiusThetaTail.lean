import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction

/-!
# The causal Möbius–theta tail and its boundary identity

For `k = thetaCuspFullSource` and `t > 0` the causal tail

`B(t) = ∑_{n > t} μ(n) n^{−1/2} k(log(n/t))`

converges absolutely.  Its Mellin transform `F(w) = ∫_1^∞ B(t) t^{−w−1} dt` satisfies, on
`Re w > 1/2`, the exact boundary identity

`F(w) + H(w) = K(w)/ζ(w + 1/2)`,  `H(w) = ∑_n μ(n) n^{−w−1/2} ∫_{log n}^∞ k(u) e^{wu} du`,

with `K` the half-line transform of `k` and `H` entire.  If `B(t) = O(t^a)` then `F` is analytic on
`Re w > a`, the identity continues there (in the denominator-free form with `(s − 1)ζ(s)`), and a
zeta zero `ρ` with `1/2 + a < Re ρ < 1` would force `K(ρ − 1/2) = 0`, which the positivity of the
reflected transform forbids.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-! ### The causal tail -/

/-- A term of the causal Möbius–theta tail. -/
def causalMobiusThetaTerm (t : ℝ) (n : ℕ) : ℝ :=
  Set.indicator (Ioo 0 (n : ℝ)) (fun t => ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (n / t))) t

/-- The causal Möbius–theta tail `B(t) = ∑_{n > t} μ(n) n^{−1/2} k(log(n/t))`. -/
def causalMobiusThetaTail (t : ℝ) : ℝ := ∑' n : ℕ, causalMobiusThetaTerm t n

/-- `n^{−1/2} e^{−2 log(n/t)} = t² n^{−5/2}`. -/
theorem rpow_neg_half_mul_exp_neg_two_log {n t : ℝ} (hn : 0 < n) (ht : 0 < t) :
    n ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 * Real.log (n / t))) = t ^ 2 * n ^ (-(5 / 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn, Real.log_div hn.ne' ht.ne',
    ← Real.exp_add, show t ^ 2 = Real.exp (Real.log t) ^ 2 by rw [Real.exp_log ht],
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **Termwise bound.**  `|μ(n) n^{−1/2} k(log(n/t))| ≤ C t² n^{−5/2}`. -/
theorem exists_abs_causalMobiusThetaTerm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (n : ℕ), 0 < t →
      |causalMobiusThetaTerm t n| ≤ C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le 2
  refine ⟨C, hC0, fun t n ht => ?_⟩
  simp only [causalMobiusThetaTerm]
  by_cases hmem : t ∈ Ioo 0 (n : ℝ)
  · rw [Set.indicator_of_mem hmem]
    have hn : (0 : ℝ) < n := ht.trans hmem.2
    have hlog : 0 < Real.log (n / t) := Real.log_pos ((one_lt_div ht).mpr hmem.2)
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn _)]
    have hk := hC (Real.log (n / t))
    rw [abs_of_pos hlog] at hk
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          |thetaCuspFullSource (Real.log (n / t))|
        ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * Real.exp (-(2 * Real.log (n / t)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (Sieve.abs_moebius_real_le_one n)
            (Real.rpow_pos_of_pos hn _).le) hk (abs_nonneg _) (by positivity)
      _ = C * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 * Real.log (n / t)))) := by ring
      _ = C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
          rw [rpow_neg_half_mul_exp_neg_two_log hn ht]; ring
  · rw [Set.indicator_of_notMem hmem, abs_zero]
    positivity

theorem summable_natCast_rpow_neg_five_halves :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

theorem causalMobiusThetaTerm_of_nonpos {t : ℝ} (ht : t ≤ 0) (n : ℕ) :
    causalMobiusThetaTerm t n = 0 := by
  simp only [causalMobiusThetaTerm]
  exact Set.indicator_of_notMem (fun h => not_lt.mpr ht h.1) _

theorem summable_causalMobiusThetaTerm (t : ℝ) : Summable (causalMobiusThetaTerm t) := by
  rcases le_or_gt t 0 with ht | ht
  · have h0 : causalMobiusThetaTerm t = 0 := funext (causalMobiusThetaTerm_of_nonpos ht)
    rw [h0]; exact summable_zero
  obtain ⟨C, _, hC⟩ := exists_abs_causalMobiusThetaTerm_le
  refine Summable.of_norm_bounded (summable_natCast_rpow_neg_five_halves.mul_left (C * t ^ 2))
    (fun n => ?_)
  rw [Real.norm_eq_abs]
  exact (hC t n ht).trans (le_of_eq (by ring))

/-- A crude global bound, used only for local integrability: `|B(t)| ≤ C t²`. -/
theorem exists_abs_causalMobiusThetaTail_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → |causalMobiusThetaTail t| ≤ C * t ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalMobiusThetaTerm_le
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(5 / 2 : ℝ)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C * S, mul_nonneg hC0 hS0, fun t ht => ?_⟩
  have hsum := summable_causalMobiusThetaTerm t
  calc |causalMobiusThetaTail t| ≤ ∑' n, |causalMobiusThetaTerm t n| := by
        rw [causalMobiusThetaTail]
        exact (norm_tsum_le_tsum_norm hsum.norm)
    _ ≤ ∑' n : ℕ, C * t ^ 2 * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
        hsum.abs.tsum_le_tsum (fun n => hC t n ht)
          (summable_natCast_rpow_neg_five_halves.mul_left _)
    _ = C * S * t ^ 2 := by rw [tsum_mul_left, hS]; ring

theorem measurable_causalMobiusThetaTerm (n : ℕ) :
    Measurable (fun t => causalMobiusThetaTerm t n) := by
  refine Measurable.indicator ?_ measurableSet_Ioo
  exact measurable_const.mul (continuous_thetaCuspFullSource.measurable.comp
    (Real.measurable_log.comp (measurable_const.div measurable_id)))

theorem measurable_causalMobiusThetaTail : Measurable causalMobiusThetaTail := by
  refine measurable_of_tendsto_metrizable (f := fun N t => ∑ n ∈ Finset.range N,
    causalMobiusThetaTerm t n) (fun N => Finset.measurable_sum _
      (fun n _ => measurable_causalMobiusThetaTerm n)) ?_
  exact tendsto_pi_nhds.mpr (fun t => (summable_causalMobiusThetaTerm t).hasSum.tendsto_sum_nat)


/-! ### The Mellin transform of the causal tail -/

/-- The causal tail restricted to `t > 1`, as a complex function on the multiplicative ray. -/
def causalTailBeyondOne (t : ℝ) : ℂ :=
  ((Set.indicator (Ioi 1) causalMobiusThetaTail t : ℝ) : ℂ)

/-- `F(w) = ∫_1^∞ B(t) t^{−w−1} dt`. -/
def causalTailMellin (w : ℂ) : ℂ := mellin causalTailBeyondOne (-w)

theorem measurable_causalTailBeyondOne : Measurable causalTailBeyondOne :=
  Complex.continuous_ofReal.measurable.comp
    (measurable_causalMobiusThetaTail.indicator measurableSet_Ioi)

theorem locallyIntegrableOn_causalTailBeyondOne :
    LocallyIntegrableOn causalTailBeyondOne (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalMobiusThetaTail_le_sq
  have hLI : LocallyIntegrable causalTailBeyondOne volume := by
    refine locallyIntegrable_iff.mpr (fun K hK => ?_)
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine Measure.integrableOn_of_bounded (M := C * R ^ 2) hK.measure_lt_top.ne
      measurable_causalTailBeyondOne.aestronglyMeasurable
      ((ae_restrict_iff' hK.measurableSet).mpr (ae_of_all _ (fun t ht => ?_)))
    simp only [causalTailBeyondOne, Complex.norm_real, Real.norm_eq_abs]
    by_cases h1 : t ∈ Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem h1]
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans h1
      have htR : t ≤ R := by
        have := hR ht
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht0] at this
        exact this
      exact (hC t ht0).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le htR 2) hC0)
    · rw [Set.indicator_of_notMem h1, abs_zero]
      positivity
  exact hLI.locallyIntegrableOn _

/-- **Analyticity from a growth bound.**  If `|B(t)| ≤ C t^a` for `t ≥ 1`, then `F` is
complex-differentiable on `Re w > a`. -/
theorem differentiableAt_causalTailMellin {a C : ℝ}
    (hB : ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ a) {w : ℂ} (hw : a < w.re) :
    DifferentiableAt ℂ causalTailMellin w := by
  have htop : causalTailBeyondOne =O[atTop] (fun t : ℝ => t ^ (-(-a))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp only [causalTailBeyondOne, Complex.norm_real, Real.norm_eq_abs, neg_neg,
      Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
    rw [abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _)]
    exact hB t ht.le
  have hbot : causalTailBeyondOne =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-w.re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    simp only [causalTailBeyondOne, Set.indicator_of_notMem
      (show t ∉ Ioi (1 : ℝ) from fun h => lt_asymm h ht.2), Complex.ofReal_zero, norm_zero,
      zero_mul, le_refl]
  have hd : DifferentiableAt ℂ (mellin causalTailBeyondOne) (-w) :=
    mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_causalTailBeyondOne htop
      (by simp; linarith) hbot (by simp)
  exact hd.comp w differentiableAt_id.neg

/-! ### The entire correction series -/

theorem norm_natCast_cpow_neg_add_half (n : ℕ) (hn : 0 < n) (w : ℂ) :
    ‖(n : ℂ) ^ (-(w + 1 / 2))‖ = (n : ℝ) ^ (-(w.re + 1 / 2)) := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- `H(w) = ∑_n μ(n) n^{−w−1/2} ∫_{log n}^∞ k(u) e^{wu} du`. -/
def causalTailCorrection (w : ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w + 1 / 2)) *
    thetaHalfLaplaceTail (Real.log n) w

/-- The terms of `H` are bounded by `C n^{−5/2}` uniformly on `|w| < r`. -/
theorem exists_norm_causalTailCorrection_term_le (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : ℂ), ‖w‖ < r →
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w + 1 / 2)) *
        thetaHalfLaplaceTail (Real.log n) w‖ ≤ C * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le (2 * r + 2)
  refine ⟨C / (r + 2), div_nonneg hC0 (by linarith), fun n w hw => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hre : |w.re| < r := (Complex.abs_re_le_norm w).trans_lt hw
  have hwre : w.re ≤ r := (le_abs_self _).trans hre.le
  have htail := norm_thetaHalfLaplaceTail_le hC (show r < 2 * r + 2 by linarith)
    (Real.log_nonneg hn1) hwre
  have hlog : Real.exp (-((2 * r + 2 - r) * Real.log n)) = (n : ℝ) ^ (-(r + 2)) := by
    rw [Real.rpow_def_of_pos hnR]; congr 1; ring
  rw [hlog, show 2 * r + 2 - r = r + 2 by ring] at htail
  have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact Sieve.abs_moebius_real_le_one n
  rw [norm_mul, norm_mul, norm_natCast_cpow_neg_add_half n hn]
  have hpow : (n : ℝ) ^ (-(w.re + 1 / 2)) ≤ (n : ℝ) ^ (r - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [neg_abs_le w.re])
  calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-(w.re + 1 / 2)) *
        ‖thetaHalfLaplaceTail (Real.log n) w‖
      ≤ 1 * (n : ℝ) ^ (r - 1 / 2) * (C * (n : ℝ) ^ (-(r + 2)) / (r + 2)) :=
        mul_le_mul (mul_le_mul hmu hpow (by positivity) zero_le_one) htail (norm_nonneg _)
          (by positivity)
    _ = C / (r + 2) * ((n : ℝ) ^ (r - 1 / 2) * (n : ℝ) ^ (-(r + 2))) := by ring
    _ = C / (r + 2) * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add hnR]; congr 2; ring

/-- **The correction series is entire.** -/
theorem differentiable_causalTailCorrection : Differentiable ℂ causalTailCorrection := by
  intro w
  set r : ℝ := ‖w‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨C, _, hC⟩ := exists_norm_causalTailCorrection_term_le r hr0
  have hdiff : DifferentiableOn ℂ causalTailCorrection (Metric.ball 0 r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_natCast_rpow_neg_five_halves.mul_left C) (fun n => ?_) Metric.isOpen_ball
      (fun n w hw => hC n w (by simpa using hw))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul]
      exact differentiableOn_const 0
    · have h1 : Differentiable ℂ (fun w : ℂ => (n : ℂ) ^ (-(w + 1 / 2))) := fun w =>
        ((differentiableAt_id.add_const _).neg).const_cpow (Or.inl (by exact_mod_cast hn.ne'))
      exact (((differentiable_const _).mul h1).mul
        (differentiable_thetaHalfLaplaceTail _)).differentiableOn
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [hr]))


/-! ### The boundary identity -/

theorem natCast_cpow_eq_cexp_mul_log {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp (z * (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', mul_comm]
  congr 2
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log (by positivity)]

theorem ofReal_exp_cpow' (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- `F` in logarithmic coordinates: `F(w) = ∫_0^∞ e^{−wx} B(e^x) dx`. -/
theorem causalTailMellin_eq_integral (w : ℂ) :
    causalTailMellin w = ∫ x in Ioi (0 : ℝ),
      Complex.exp (-(w * x)) * (causalMobiusThetaTail (Real.exp x) : ℂ) := by
  rw [causalTailMellin, mellin, integral_Ioi_comp_exp_complex,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  simp only [causalTailBeyondOne, smul_eq_mul]
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
      Set.indicator_of_mem (show Real.exp x ∈ Ioi (1 : ℝ) from Real.one_lt_exp_iff.mpr hx),
      ofReal_exp_cpow', Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      Set.indicator_of_notMem (show Real.exp x ∉ Ioi (1 : ℝ) from
        fun h => hx (Real.one_lt_exp_iff.mp h))]
    simp

/-- A term of the causal tail in logarithmic coordinates. -/
def causalLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  Set.indicator (Iio (Real.log n)) (fun x => ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log n - x)) x

theorem causalMobiusThetaTerm_exp (x : ℝ) (n : ℕ) :
    causalMobiusThetaTerm (Real.exp x) n = causalLogTerm x n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [causalMobiusThetaTerm, causalLogTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [causalMobiusThetaTerm, causalLogTerm]
  by_cases hx : x < Real.log n
  · have hmem : Real.exp x ∈ Ioo 0 (n : ℝ) :=
      ⟨Real.exp_pos x, (Real.lt_log_iff_exp_lt hnR).mp hx⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show x ∈ Iio (Real.log n) from hx),
      Real.log_div hnR.ne' (Real.exp_pos x).ne', Real.log_exp]
  · have hmem : Real.exp x ∉ Ioo 0 (n : ℝ) := fun h =>
      hx ((Real.lt_log_iff_exp_lt hnR).mpr h.2)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show x ∉ Iio (Real.log n) from hx)]

theorem measurable_causalLogTerm (n : ℕ) : Measurable (fun x => causalLogTerm x n) := by
  refine Measurable.indicator ?_ measurableSet_Iio
  exact measurable_const.mul (continuous_thetaCuspFullSource.measurable.comp
    (measurable_const.sub measurable_id))

/-- The logarithmic integrand `g_n(x) = e^{−wx} μ(n) n^{−1/2} k(log n − x) 1_{x < log n}`. -/
def causalLogIntegrand (w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-(w * x)) * (causalLogTerm x n : ℂ)

/-- Pointwise bound `‖g_n(x)‖ ≤ C n^{−(σ+3/2)} e^x 1_{x < log n}` on the positive ray. -/
theorem exists_norm_causalLogIntegrand_le (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), 0 < x →
      ‖causalLogIntegrand w n x‖ ≤ C * (n : ℝ) ^ (-(w.re + 3 / 2)) *
        Set.indicator (Iio (Real.log n)) Real.exp x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le (w.re + 1)
  refine ⟨C, hC0, fun n x hx => ?_⟩
  simp only [causalLogIntegrand, causalLogTerm]
  by_cases hmem : x ∈ Iio (Real.log n)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    have hLx : 0 < Real.log n - x := sub_pos.mpr hmem
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hmem; linarith
      · exact h
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hnR _)]
    have h1 : (-(w * (x : ℂ))).re = -(w.re * x) := by simp
    rw [h1]
    have hk := hC (Real.log n - x)
    rw [abs_of_pos hLx] at hk
    have hmu := Sieve.abs_moebius_real_le_one n
    calc Real.exp (-(w.re * x)) * (|((ArithmeticFunction.moebius n : ℤ) : ℝ)| *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * |thetaCuspFullSource (Real.log n - x)|)
        ≤ Real.exp (-(w.re * x)) * (1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (C * Real.exp (-((w.re + 1) * (Real.log n - x))))) := by
          gcongr
      _ = C * (n : ℝ) ^ (-(w.re + 3 / 2)) * Real.exp x := by
          rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR]
          rw [show Real.exp (-(w.re * x)) * (1 * Real.exp (Real.log n * -(1 / 2)) *
              (C * Real.exp (-((w.re + 1) * (Real.log n - x))))) =
              C * (Real.exp (-(w.re * x)) * Real.exp (Real.log n * -(1 / 2)) *
                Real.exp (-((w.re + 1) * (Real.log n - x)))) by ring,
            ← Real.exp_add, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    simp

theorem integral_Ioi_indicator_Iio_exp {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in Ioi (0 : ℝ), Set.indicator (Iio L) Real.exp x = Real.exp L - 1 := by
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hL, integral_exp, Real.exp_zero]

theorem integrableOn_Ioi_indicator_Iio_exp (L : ℝ) :
    IntegrableOn (Set.indicator (Iio L) Real.exp) (Ioi 0) := by
  have h : IntegrableOn (Set.indicator (Iio L) Real.exp) (Icc 0 L) :=
    (Real.continuous_exp.integrableOn_Icc (a := 0) (b := L)).indicator measurableSet_Iio
  refine h.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => ?_)
  have hxL : x ∉ Iio L := fun hlt => hx.2 ⟨le_of_lt (show (0 : ℝ) < x from hx.1), le_of_lt hlt⟩
  exact Set.indicator_of_notMem hxL Real.exp

theorem integrableOn_causalLogIntegrand (w : ℂ) (n : ℕ) :
    IntegrableOn (causalLogIntegrand w n) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_causalLogIntegrand_le w
  refine Integrable.mono' ((integrableOn_Ioi_indicator_Iio_exp (Real.log n)).const_mul
    (C * (n : ℝ) ^ (-(w.re + 3 / 2)))) ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).measurable.mul
      (Complex.continuous_ofReal.measurable.comp (measurable_causalLogTerm n))).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => hC n x hx))

theorem integral_norm_causalLogIntegrand_le (w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∫ x in Ioi (0 : ℝ), ‖causalLogIntegrand w n x‖ ≤ C * (n : ℝ) ^ (-(w.re + 1 / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_causalLogIntegrand_le w
  refine ⟨C, hC0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ x, causalLogIntegrand w 0 x = 0 := fun x => by
      simp [causalLogIntegrand, causalLogTerm]
    simp only [h0, norm_zero, integral_zero]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ∫ x in Ioi (0 : ℝ), ‖causalLogIntegrand w n x‖
      ≤ ∫ x in Ioi (0 : ℝ), C * (n : ℝ) ^ (-(w.re + 3 / 2)) *
          Set.indicator (Iio (Real.log n)) Real.exp x :=
        setIntegral_mono_on (integrableOn_causalLogIntegrand w n).norm
          ((integrableOn_Ioi_indicator_Iio_exp _).const_mul _) measurableSet_Ioi
          (fun x hx => hC n x hx)
    _ = C * (n : ℝ) ^ (-(w.re + 3 / 2)) * (n - 1) := by
        rw [integral_const_mul, integral_Ioi_indicator_Iio_exp (Real.log_nonneg hn1),
          Real.exp_log hnR]
    _ ≤ C * (n : ℝ) ^ (-(w.re + 3 / 2)) * n := by
        gcongr; linarith
    _ = C * (n : ℝ) ^ (-(w.re + 1 / 2)) := by
        rw [mul_assoc, ← Real.rpow_add_one hnR.ne']
        congr 2; ring

/-- The substitution `u = log n − x`. -/
theorem integral_causalLogIntegrand (w : ℂ) {n : ℕ} (hn : 0 < n) :
    ∫ x in Ioi (0 : ℝ), causalLogIntegrand w n x =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w + 1 / 2)) *
        (thetaHalfLaplace w - thetaHalfLaplaceTail (Real.log n) w) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℝ := Real.log n with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
  set c : ℂ := ((((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    with hc
  have hform : ∀ x, causalLogIntegrand w n x = Set.indicator (Iio L)
      (fun x => c * (Complex.exp (-(w * x)) * (thetaCuspFullSource (L - x) : ℂ))) x := by
    intro x
    simp only [causalLogIntegrand, causalLogTerm, ← hLdef]
    by_cases hx : x ∈ Iio L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hc]
      push_cast; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
  simp_rw [hform]
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hL, intervalIntegral.integral_const_mul]
  have hsub : ∫ x in (0 : ℝ)..L, Complex.exp (-(w * x)) * (thetaCuspFullSource (L - x) : ℂ) =
      ∫ u in (0 : ℝ)..L, Complex.exp (-(w * (L - u))) * (thetaCuspFullSource u : ℂ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => Complex.exp (-(w * (L - u))) * (thetaCuspFullSource u : ℂ)) (a := 0) (b := L) L
    simp only [sub_zero, sub_self] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [Complex.ofReal_sub, sub_sub_cancel]
  have hfac : ∫ u in (0 : ℝ)..L, Complex.exp (-(w * (L - u))) * (thetaCuspFullSource u : ℂ) =
      Complex.exp (-(w * L)) * ∫ u in (0 : ℝ)..L, Complex.exp (w * u) *
        (thetaCuspFullSource u : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring
  have hsplit : ∫ u in (0 : ℝ)..L, Complex.exp (w * u) * (thetaCuspFullSource u : ℂ) =
      thetaHalfLaplace w - thetaHalfLaplaceTail L w := by
    have hdisj : Disjoint (Ioc 0 L) (Ioi L) := Set.disjoint_left.mpr
      (fun x (hx : x ∈ Ioc 0 L) (hx' : x ∈ Ioi L) => (not_lt.mpr hx.2) hx')
    rw [intervalIntegral.integral_of_le hL, thetaHalfLaplace, thetaHalfLaplaceTail,
      thetaHalfLaplaceTail, ← Ioc_union_Ioi_eq_Ioi hL,
      setIntegral_union hdisj measurableSet_Ioi (integrableOn_cexp_mul_thetaCuspFullSource w _)
        (integrableOn_cexp_mul_thetaCuspFullSource w _)]
    ring
  rw [hsub, hfac, hsplit, natCast_cpow_eq_cexp_mul_log hn, hc]
  rw [show ((((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) by
    rw [Complex.ofReal_mul, Real.rpow_def_of_pos hnR, Complex.ofReal_exp]
    push_cast; ring_nf]
  rw [← hLdef]
  have : Complex.exp (-(1 / 2 : ℂ) * (L : ℂ)) * Complex.exp (-(w * L)) =
      Complex.exp (-(w + 1 / 2) * (L : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc ((ArithmeticFunction.moebius n : ℤ) : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (L : ℂ)) *
        (Complex.exp (-(w * L)) * (thetaHalfLaplace w - thetaHalfLaplaceTail L w))
      = ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (Complex.exp (-(1 / 2 : ℂ) * (L : ℂ)) *
        Complex.exp (-(w * L))) * (thetaHalfLaplace w - thetaHalfLaplaceTail L w) := by ring
    _ = _ := by rw [this]


/-! ### The Dirichlet series of the Möbius function -/

theorem moebius_mul_natCast_cpow_eq_term (s : ℂ) (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s) =
      LSeries.term (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem summable_moebius_mul_natCast_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)) := by
  have h := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  exact (h.congr (fun n => (moebius_mul_natCast_cpow_eq_term s n).symm))

theorem tsum_moebius_mul_natCast_cpow {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s) = (riemannZeta s)⁻¹ := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [tsum_congr (moebius_mul_natCast_cpow_eq_term s), ← LSeries]
  exact eq_inv_of_mul_eq_one_right h

/-- **The boundary identity (3).**  For `Re w > 1/2`,
`F(w) + H(w) = K(w)/ζ(w + 1/2)`. -/
theorem causalTailMellin_add_correction {w : ℂ} (hw : 1 / 2 < w.re) :
    causalTailMellin w + causalTailCorrection w =
      thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹ := by
  have hs : 1 < (w + 1 / 2).re := by simp; linarith
  obtain ⟨C, _, hC⟩ := integral_norm_causalLogIntegrand_le w
  have hsumm : Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖causalLogIntegrand w n x‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) hC
      ((Real.summable_nat_rpow.mpr (by linarith)).mul_left C)
  have hF : causalTailMellin w = ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), causalLogIntegrand w n x := by
    rw [integral_tsum_of_summable_integral_norm (fun n => integrableOn_causalLogIntegrand w n)
      hsumm, causalTailMellin_eq_integral]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [causalLogIntegrand]
    rw [tsum_mul_left, causalMobiusThetaTail, Complex.ofReal_tsum]
    congr 1
    exact tsum_congr (fun n => by rw [causalMobiusThetaTerm_exp])
  have hterm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), causalLogIntegrand w n x =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w + 1 / 2)) * thetaHalfLaplace w -
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w + 1 / 2)) *
          thetaHalfLaplaceTail (Real.log n) w := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : ∀ x, causalLogIntegrand w 0 x = 0 := fun x => by
        simp [causalLogIntegrand, causalLogTerm]
      simp [h0]
    · rw [integral_causalLogIntegrand w hn]; ring
  have hs1 := summable_moebius_mul_natCast_cpow hs
  obtain ⟨Ch, _, hCh⟩ := exists_norm_causalTailCorrection_term_le (‖w‖ + 1) (by positivity)
  have hs2 : Summable (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (n : ℂ) ^ (-(w + 1 / 2)) * thetaHalfLaplaceTail (Real.log n) w) :=
    Summable.of_norm_bounded (summable_natCast_rpow_neg_five_halves.mul_left Ch)
      (fun n => hCh n w (by linarith))
  rw [hF, tsum_congr hterm, (hs1.mul_right (thetaHalfLaplace w)).tsum_sub hs2, tsum_mul_right,
    tsum_moebius_mul_natCast_cpow hs, causalTailCorrection]
  ring

/-! ### The zero-exclusion criterion -/

/-- **A growth bound excludes zeros.**  If `|B(t)| ≤ C t^a` for `t ≥ 1` with `a ≥ 0`, then `ζ` has
no zero `ρ` with `1/2 + a < Re ρ < 1`. -/
theorem causalMobiusThetaTail_growth_excludes_zero {a C : ℝ} (ha : 0 ≤ a)
    (hB : ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ a) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h1 : 1 / 2 + a < ρ.re) (h2 : ρ.re < 1) : False := by
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ causalTailMellin U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_causalTailMellin hB hw).differentiableWithinAt) hUo
  have hH : AnalyticOnNhd ℂ causalTailCorrection U :=
    fun w _ => differentiable_causalTailCorrection.analyticAt w
  have hK : AnalyticOnNhd ℂ thetaHalfLaplace U :=
    fun w _ => differentiable_thetaHalfLaplace.analyticAt w
  have hΦ : AnalyticOnNhd ℂ (fun w => (causalTailMellin w + causalTailCorrection w) *
      zetaResidueUnit (w + 1 / 2)) U :=
    (hF.add hH).mul (fun w _ => (analyticAt_zetaResidueUnit _).comp
      (analyticAt_id.add analyticAt_const))
  have hΨ : AnalyticOnNhd ℂ (fun w => thetaHalfLaplace w * (w - 1 / 2)) U :=
    hK.mul (fun w _ => analyticAt_id.sub analyticAt_const)
  have h1U : (1 : ℂ) ∈ U := by simp only [hU, mem_setOf_eq, Complex.one_re]; linarith
  have hev : (fun w => (causalTailMellin w + causalTailCorrection w) *
      zetaResidueUnit (w + 1 / 2)) =ᶠ[𝓝 (1 : ℂ)] (fun w => thetaHalfLaplace w * (w - 1 / 2)) := by
    have hnear : ∀ᶠ w in 𝓝 (1 : ℂ), 1 / 2 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear] with w hw
    have hs : 1 < (w + 1 / 2).re := by simp; linarith
    have hs1 : w + 1 / 2 ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    rw [causalTailMellin_add_correction hw, zetaResidueUnit, Function.update_of_ne hs1]
    calc thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹ *
          ((w + 1 / 2 - 1) * riemannZeta (w + 1 / 2))
        = thetaHalfLaplace w * (w - 1 / 2) *
            ((riemannZeta (w + 1 / 2))⁻¹ * riemannZeta (w + 1 / 2)) := by ring
      _ = thetaHalfLaplace w * (w - 1 / 2) := by rw [inv_mul_cancel₀ hz, mul_one]
  have heq := hΦ.eqOn_of_preconnected_of_eventuallyEq hΨ (convex_halfSpace_re_gt a).isPreconnected
    h1U hev
  have hw0 : ρ - 1 / 2 ∈ U := by simp only [hU, mem_setOf_eq, Complex.sub_re]; norm_num; linarith
  have hval := heq hw0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h2; simp at h2
  simp only [sub_add_cancel] at hval
  rw [zetaResidueUnit, Function.update_of_ne hρ1, hρ, mul_zero, mul_zero] at hval
  have hne : ρ - 1 / 2 - 1 / 2 ≠ 0 := by
    intro h; apply hρ1; linear_combination h
  have hK0 : thetaHalfLaplace (ρ - 1 / 2) = 0 := by
    rcases mul_eq_zero.mp hval.symm with h | h
    · exact h
    · exact absurd h hne
  exact thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero hρ (by linarith) h2 hK0

/-- **Subpower growth of the causal tail implies RH.** -/
theorem riemannHypothesis_of_causalMobiusThetaTail_subpower
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ ε) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxi
  have hhalf : 1 / 2 < s.re := hs
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, xi_one] at hxi; norm_num at hxi
  have hζ : riemannZeta s = 0 := (xi_eq_zero_iff (by linarith) hs1).mp hxi
  rcases lt_or_ge s.re 1 with hlt | hge
  · obtain ⟨C, hC⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
    exact causalMobiusThetaTail_growth_excludes_zero (by linarith) hC hζ (by linarith) hlt
  · exact riemannZeta_ne_zero_of_one_le_re hge hζ


/-! ### RH gives subpower growth: Abel summation -/

/-- The causal profile `f_t(u) = u^{−1/2} k(log u − log t)`. -/
def causalProfile (t u : ℝ) : ℝ := u ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log u - Real.log t)

/-- Its derivative `f_t'(u) = u^{−3/2} (k'(log(u/t)) − k(log(u/t))/2)`. -/
def causalProfileDeriv (t u : ℝ) : ℝ :=
  u ^ (-(3 / 2 : ℝ)) * (deriv thetaCuspFullSource (Real.log u - Real.log t) -
    thetaCuspFullSource (Real.log u - Real.log t) / 2)

theorem hasDerivAt_causalProfile (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (causalProfile t) (causalProfileDeriv t u) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (-(1 / 2) * u ^ (-(1 / 2 : ℝ) - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have h2 : HasDerivAt (fun u : ℝ => thetaCuspFullSource (Real.log u - Real.log t))
      (deriv thetaCuspFullSource (Real.log u - Real.log t) * u⁻¹) u :=
    ((differentiable_thetaCuspFullSource _).hasDerivAt).comp u
      ((Real.hasDerivAt_log hu.ne').sub_const _)
  have hu32 : u ^ (-(1 / 2 : ℝ) - 1) = u ^ (-(3 / 2 : ℝ)) := by norm_num
  have hmul : u ^ (-(1 / 2 : ℝ)) * u⁻¹ = u ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hu]; norm_num
  have hval : -(1 / 2) * u ^ (-(1 / 2 : ℝ) - 1) * thetaCuspFullSource (Real.log u - Real.log t) +
      u ^ (-(1 / 2 : ℝ)) * (deriv thetaCuspFullSource (Real.log u - Real.log t) * u⁻¹) =
      causalProfileDeriv t u := by
    unfold causalProfileDeriv
    rw [hu32, show u ^ (-(1 / 2 : ℝ)) * (deriv thetaCuspFullSource (Real.log u - Real.log t) *
      u⁻¹) = (u ^ (-(1 / 2 : ℝ)) * u⁻¹) * deriv thetaCuspFullSource (Real.log u - Real.log t) by
        ring, hmul]
    ring
  exact (h1.mul h2).congr_deriv hval

theorem exp_neg_two_log_sub {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Real.exp (-(2 * (Real.log u - Real.log t))) = t ^ 2 * (u ^ 2)⁻¹ := by
  rw [show -(2 * (Real.log u - Real.log t)) = 2 * Real.log t + -(2 * Real.log u) by ring,
    Real.exp_add, Real.exp_neg, show 2 * Real.log t = ((2 : ℕ) : ℝ) * Real.log t by norm_num,
    show 2 * Real.log u = ((2 : ℕ) : ℝ) * Real.log u by norm_num, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_log ht, Real.exp_log hu]

/-- Bounds on the profile and its derivative beyond the cusp: `|f_t(u)| ≤ D t² u^{−5/2}` and
`|f_t'(u)| ≤ (3/2) D t² u^{−7/2}` for `0 < t ≤ u`. -/
theorem exists_causalProfile_bounds :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t u : ℝ, 0 < t → t ≤ u →
      |causalProfile t u| ≤ D * t ^ 2 * u ^ (-(5 / 2 : ℝ)) ∧
      |causalProfileDeriv t u| ≤ 3 / 2 * D * t ^ 2 * u ^ (-(7 / 2 : ℝ)) := by
  obtain ⟨D₀, hD₀, hk⟩ := exists_abs_thetaCuspFullSource_le 2
  obtain ⟨D₁, hD₁, hk'⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  refine ⟨max D₀ D₁, le_max_of_le_left hD₀, fun t u ht htu => ?_⟩
  have hu : 0 < u := ht.trans_le htu
  have hy : 0 ≤ Real.log u - Real.log t := sub_nonneg.mpr (Real.log_le_log ht htu)
  have he := exp_neg_two_log_sub ht hu
  have hk0 : |thetaCuspFullSource (Real.log u - Real.log t)| ≤ max D₀ D₁ * (t ^ 2 * (u ^ 2)⁻¹) := by
    have := hk (Real.log u - Real.log t)
    rw [abs_of_nonneg hy, he] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hk1 : |deriv thetaCuspFullSource (Real.log u - Real.log t)| ≤
      max D₀ D₁ * (t ^ 2 * (u ^ 2)⁻¹) := by
    have := hk' (Real.log u - Real.log t)
    rw [abs_of_nonneg hy, he] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hr5 : u ^ (-(1 / 2 : ℝ)) * (u ^ 2)⁻¹ = u ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hu.le, ← Real.rpow_add hu]; norm_num
  have hr7 : u ^ (-(3 / 2 : ℝ)) * (u ^ 2)⁻¹ = u ^ (-(7 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hu.le, ← Real.rpow_add hu]; norm_num
  constructor
  · unfold causalProfile
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu _)]
    calc u ^ (-(1 / 2 : ℝ)) * |thetaCuspFullSource (Real.log u - Real.log t)|
        ≤ u ^ (-(1 / 2 : ℝ)) * (max D₀ D₁ * (t ^ 2 * (u ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hk0 (Real.rpow_pos_of_pos hu _).le
      _ = max D₀ D₁ * t ^ 2 * (u ^ (-(1 / 2 : ℝ)) * (u ^ 2)⁻¹) := by ring
      _ = _ := by rw [hr5]
  · unfold causalProfileDeriv
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu _)]
    have hsub : |deriv thetaCuspFullSource (Real.log u - Real.log t) -
        thetaCuspFullSource (Real.log u - Real.log t) / 2| ≤
        3 / 2 * (max D₀ D₁ * (t ^ 2 * (u ^ 2)⁻¹)) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_two]
      linarith
    calc u ^ (-(3 / 2 : ℝ)) * |deriv thetaCuspFullSource (Real.log u - Real.log t) -
          thetaCuspFullSource (Real.log u - Real.log t) / 2|
        ≤ u ^ (-(3 / 2 : ℝ)) * (3 / 2 * (max D₀ D₁ * (t ^ 2 * (u ^ 2)⁻¹))) :=
          mul_le_mul_of_nonneg_left hsub (Real.rpow_pos_of_pos hu _).le
      _ = 3 / 2 * max D₀ D₁ * t ^ 2 * (u ^ (-(3 / 2 : ℝ)) * (u ^ 2)⁻¹) := by ring
      _ = _ := by rw [hr7]

/-- **Increment bound.**  `|f_t(n+1) − f_t(n)| ≤ (3/2) D t² n^{−7/2}` for `0 < t ≤ n`. -/
theorem abs_causalProfile_succ_sub_le {D : ℝ} (hD : ∀ t u : ℝ, 0 < t → t ≤ u →
      |causalProfile t u| ≤ D * t ^ 2 * u ^ (-(5 / 2 : ℝ)) ∧
      |causalProfileDeriv t u| ≤ 3 / 2 * D * t ^ 2 * u ^ (-(7 / 2 : ℝ)))
    {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    |causalProfile t (x + 1) - causalProfile t x| ≤ 3 / 2 * D * t ^ 2 * x ^ (-(7 / 2 : ℝ)) := by
  have hx : 0 < x := ht.trans_le htx
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := causalProfile t) (a := x)
    (b := x + 1) (f' := causalProfileDeriv t) (C := 3 / 2 * D * t ^ 2 * x ^ (-(7 / 2 : ℝ)))
    (fun y hy => (hasDerivAt_causalProfile t (hx.trans_le hy.1)).hasDerivWithinAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      refine (hD t y ht (htx.trans hy.1)).2.trans ?_
      have hD0 : 0 ≤ D := by
        have := (hD t t ht le_rfl).1
        have hpos : 0 < t ^ 2 * t ^ (-(5 / 2 : ℝ)) := by positivity
        by_contra hneg
        push Not at hneg
        have : D * t ^ 2 * t ^ (-(5 / 2 : ℝ)) < 0 := by
          rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
        linarith [abs_nonneg (causalProfile t t)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hy.1 (by norm_num))
        (by positivity))
    (x + 1) ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  simpa using h

/-- The real Mertens function `M(N) = ∑_{n ≤ N} μ(n)`. -/
def mertensReal (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ)

theorem mertensReal_succ (N : ℕ) :
    mertensReal (N + 1) = mertensReal N + ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) := by
  simp only [mertensReal]
  rw [Finset.sum_range_succ]

theorem abs_mertensReal_le (N : ℕ) : |mertensReal N| ≤ N + 1 := by
  unfold mertensReal
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ Finset.range (N + 1), |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
      ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => Sieve.abs_moebius_real_le_one n)
    _ = N + 1 := by simp

theorem norm_mobiusMertensPartialSum_eq (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ = |mertensReal N| := by
  rw [mobiusMertensPartialSum, mertensReal]
  simp only [mobiusComplexCoefficient]
  rw [show (∑ n ∈ Finset.range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℂ)) =
      ((∑ n ∈ Finset.range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) by
    push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]

/-- **Abel summation on a tail.** -/
theorem tsum_sub_mul_eq_abel (M g : ℕ → ℝ) (h1 : Summable (fun j => M (j + 1) * g j))
    (h2 : Summable (fun j => M j * g j)) :
    ∑' j, (M (j + 1) - M j) * g j = -(M 0 * g 0) + ∑' j, M (j + 1) * (g j - g (j + 1)) := by
  have h3 : Summable (fun j => M (j + 1) * g (j + 1)) := (summable_nat_add_iff 1).mpr h2
  have e1 : ∑' j, (M (j + 1) - M j) * g j = ∑' j, M (j + 1) * g j - ∑' j, M j * g j := by
    rw [← h1.tsum_sub h2]; congr 1; funext j; ring
  have e2 : ∑' j, M j * g j = M 0 * g 0 + ∑' j, M (j + 1) * g (j + 1) := h2.tsum_eq_zero_add
  have e3 : ∑' j, M (j + 1) * (g j - g (j + 1)) =
      ∑' j, M (j + 1) * g j - ∑' j, M (j + 1) * g (j + 1) := by
    rw [← h1.tsum_sub h3]; congr 1; funext j; ring
  rw [e1, e2, e3]; ring


theorem causalMobiusThetaTerm_eq_profile {t : ℝ} (ht : 0 < t) (n : ℕ) (htn : t < n) :
    causalMobiusThetaTerm t n =
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * causalProfile t n := by
  have hn : (0 : ℝ) < n := ht.trans htn
  simp only [causalMobiusThetaTerm, causalProfile]
  rw [Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht, htn⟩),
    Real.log_div hn.ne' ht.ne']
  ring

/-- The shifted tail representation `B(t) = ∑_j μ(a+1+j) f_t(a+1+j)`, `a = ⌊t⌋`. -/
theorem causalMobiusThetaTail_eq_tsum_shift {t : ℝ} (ht : 0 < t) :
    causalMobiusThetaTail t = ∑' j : ℕ, ((ArithmeticFunction.moebius (j + ⌊t⌋₊ + 1) : ℤ) : ℝ) *
      causalProfile t ((j + ⌊t⌋₊ + 1 : ℕ) : ℝ) := by
  set a := ⌊t⌋₊ with ha
  have hsum := summable_causalMobiusThetaTerm t
  rw [causalMobiusThetaTail, ← hsum.sum_add_tsum_nat_add (a + 1)]
  have hzero : ∑ i ∈ Finset.range (a + 1), causalMobiusThetaTerm t i = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    have hna : (n : ℝ) ≤ t := by
      have : n ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le ht.le)
    simp only [causalMobiusThetaTerm]
    exact Set.indicator_of_notMem (fun h => not_lt.mpr hna h.2) _
  rw [hzero, zero_add]
  refine tsum_congr (fun j => ?_)
  have htj : t < ((j + (a + 1) : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one t
    rw [← ha] at this
    push_cast
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  rw [causalMobiusThetaTerm_eq_profile ht _ htj, show j + (a + 1) = j + a + 1 by ring]

/-- **RH gives subpower growth of the causal tail.** -/
theorem causalMobiusThetaTail_subpower_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ ε := by
  intro ε hε
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨CM, hCM0, hCM⟩ := riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ
  have hM : ∀ N : ℕ, |mertensReal N| ≤ CM * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := fun N => by
    rw [← norm_mobiusMertensPartialSum_eq]; exact hCM N
  obtain ⟨D, hD0, hD⟩ := exists_causalProfile_bounds
  have hk0 : 0 < thetaCuspFullSource 0 := thetaCuspFullSource_pos_all 0
  refine ⟨2 * CM * thetaCuspFullSource 0 + 12 * CM * D, fun t ht => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  set a := ⌊t⌋₊ with ha
  have ha1 : 1 ≤ a := Nat.le_floor (by exact_mod_cast ht)
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hat : (a : ℝ) ≤ t := Nat.floor_le ht0.le
  have hta : t < a + 1 := by have := Nat.lt_floor_add_one t; rwa [← ha] at this
  have ht2a : t / 2 ≤ a := by
    rcases lt_or_ge t 2 with h2 | h2
    · linarith
    · linarith
  -- the shifted Abel data
  set M : ℕ → ℝ := fun j => mertensReal (j + a) with hMdef
  set g : ℕ → ℝ := fun j => causalProfile t ((j + a + 1 : ℕ) : ℝ) with hgdef
  have hxj : ∀ j : ℕ, t ≤ ((j + a + 1 : ℕ) : ℝ) := fun j => by
    push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hxpos : ∀ j : ℕ, (0 : ℝ) < ((j + a + 1 : ℕ) : ℝ) := fun j => ht0.trans_le (hxj j)
  have hg_le : ∀ j, |g j| ≤ D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) :=
    fun j => (hD t _ ht0 (hxj j)).1
  have hmu : ∀ j : ℕ, ((ArithmeticFunction.moebius (j + a + 1) : ℤ) : ℝ) = M (j + 1) - M j := by
    intro j
    simp only [hMdef]
    rw [show j + 1 + a = (j + a) + 1 by ring, mertensReal_succ]
    ring
  have hshift := causalMobiusThetaTail_eq_tsum_shift ht0
  rw [← ha] at hshift
  simp_rw [hmu] at hshift
  -- summability of the two Abel series
  have hpow_sum : Summable (fun j : ℕ => ((j + a + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have h := (summable_nat_add_iff (a + 1)).mpr (Real.summable_nat_rpow.mpr
      (show -(3 / 2 : ℝ) < -1 by norm_num))
    exact h.congr (fun j => by push_cast; ring_nf)
  have hbound32 : ∀ j : ℕ, ∀ N : ℕ, N ≤ j + a + 1 →
      |mertensReal N * g j| ≤ 2 * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro j N hN
    rw [abs_mul]
    have hMN : |mertensReal N| ≤ 2 * ((j + a + 1 : ℕ) : ℝ) := by
      refine (abs_mertensReal_le N).trans ?_
      have : (N : ℝ) ≤ ((j + a + 1 : ℕ) : ℝ) := by exact_mod_cast hN
      have h1 : (1 : ℝ) ≤ ((j + a + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + a + 1)
      linarith
    have hx := hxpos j
    calc |mertensReal N| * |g j|
        ≤ 2 * ((j + a + 1 : ℕ) : ℝ) * (D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul hMN (hg_le j) (abs_nonneg _) (by positivity)
      _ = 2 * D * t ^ 2 * (((j + a + 1 : ℕ) : ℝ) ^ (1 : ℝ) *
            ((j + a + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = 2 * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hx]; norm_num
  have h1 : Summable (fun j => M (j + 1) * g j) :=
    Summable.of_norm_bounded (hpow_sum.mul_left (2 * D * t ^ 2)) (fun j => by
      rw [Real.norm_eq_abs]; exact hbound32 j _ (by omega))
  have h2 : Summable (fun j => M j * g j) :=
    Summable.of_norm_bounded (hpow_sum.mul_left (2 * D * t ^ 2)) (fun j => by
      rw [Real.norm_eq_abs]; exact hbound32 j _ (by omega))
  rw [hshift, tsum_sub_mul_eq_abel M g h1 h2]
  -- the boundary term
  have hb0 : |M 0 * g 0| ≤ 2 * CM * thetaCuspFullSource 0 * t ^ δ := by
    simp only [hMdef, hgdef, zero_add]
    have hx0 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by simpa using hxpos 0
    have hprof : |causalProfile t ((a + 1 : ℕ) : ℝ)| ≤
        ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0 := by
      unfold causalProfile
      have hy : 0 ≤ Real.log ((a + 1 : ℕ) : ℝ) - Real.log t :=
        sub_nonneg.mpr (Real.log_le_log ht0 (by simpa using hxj 0))
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
        abs_of_pos (thetaCuspFullSource_pos_all _)]
      push_cast
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (by positivity) _).le
      exact HedenmalmThetaSource.antitoneOn_thetaCuspFullSource (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr (by push_cast at hy; exact hy)) (by push_cast at hy; exact hy)
    rw [abs_mul]
    have hMa := hM a
    have hA : ((a : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) * ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) =
        ((a : ℝ) + 1) ^ δ := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have hA2 : ((a : ℝ) + 1) ^ δ ≤ 2 * t ^ δ := by
      have h1 : (a : ℝ) + 1 ≤ 2 * t := by linarith
      calc ((a : ℝ) + 1) ^ δ ≤ (2 * t) ^ δ :=
            Real.rpow_le_rpow (by positivity) h1 hδ.le
        _ = 2 ^ δ * t ^ δ := Real.mul_rpow (by norm_num) ht0.le
        _ ≤ 2 * t ^ δ := by
            gcongr
            calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
    calc |mertensReal a| * |causalProfile t ((a + 1 : ℕ) : ℝ)|
        ≤ CM * ((a : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) *
            (((a : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource 0) :=
          mul_le_mul hMa hprof (abs_nonneg _) (by positivity)
      _ = CM * thetaCuspFullSource 0 * (((a : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) *
            ((a : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ CM * thetaCuspFullSource 0 * (2 * t ^ δ) := by
          rw [hA]; exact mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = 2 * CM * thetaCuspFullSource 0 * t ^ δ := by ring
  -- the Abel series
  have hterm : ∀ j : ℕ, |M (j + 1) * (g j - g (j + 1))| ≤
      3 * CM * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(3 - δ)) := by
    intro j
    have hx := hxpos j
    have hMj : |M (j + 1)| ≤ 2 * CM * ((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
      simp only [hMdef]
      refine (hM _).trans ?_
      have h1 : (((j + 1 + a : ℕ) : ℝ) + 1) ≤ 2 * ((j + a + 1 : ℕ) : ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), haR]
      calc CM * (((j + 1 + a : ℕ) : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)
          ≤ CM * (2 * ((j + a + 1 : ℕ) : ℝ)) ^ ((1 / 2 : ℝ) + δ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h1 (by linarith)) hCM0
        _ = CM * (2 ^ ((1 / 2 : ℝ) + δ) * ((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) := by
            rw [Real.mul_rpow (by norm_num) hx.le]
        _ ≤ CM * (2 * ((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ)) := by
            gcongr
            calc (2 : ℝ) ^ ((1 / 2 : ℝ) + δ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
        _ = 2 * CM * ((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ) := by ring
    have hgj : |g j - g (j + 1)| ≤ 3 / 2 * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ)) := by
      simp only [hgdef]
      have h := abs_causalProfile_succ_sub_le hD ht0 (hxj j)
      rw [abs_sub_comm] at h
      have hcast : ((j + 1 + a + 1 : ℕ) : ℝ) = ((j + a + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact h
    rw [abs_mul]
    calc |M (j + 1)| * |g j - g (j + 1)|
        ≤ 2 * CM * ((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ) *
            (3 / 2 * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul hMj hgj (abs_nonneg _) (by positivity)
      _ = 3 * CM * D * t ^ 2 * (((j + a + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + δ) *
            ((j + a + 1 : ℕ) : ℝ) ^ (-(7 / 2 : ℝ))) := by ring
      _ = 3 * CM * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(3 - δ)) := by
          rw [← Real.rpow_add hx]; congr 2; ring
  have htail := Sieve.tsum_tail_rpow_neg_le (show (1 : ℝ) < 3 - δ by linarith) ha1
  have hsum3 : Summable (fun j : ℕ => ((j + a + 1 : ℕ) : ℝ) ^ (-(3 - δ))) := by
    have h := (summable_nat_add_iff (a + 1)).mpr (Real.summable_nat_rpow.mpr
      (show -(3 - δ) < -1 by linarith))
    exact h.congr (fun j => by push_cast; ring_nf)
  have hser : |∑' j, M (j + 1) * (g j - g (j + 1))| ≤ 12 * CM * D * t ^ δ := by
    have habs : Summable (fun j => |M (j + 1) * (g j - g (j + 1))|) :=
      Summable.of_nonneg_of_le (fun j => abs_nonneg _) hterm (hsum3.mul_left _)
    calc |∑' j, M (j + 1) * (g j - g (j + 1))|
        ≤ ∑' j, |M (j + 1) * (g j - g (j + 1))| := by
          have := norm_tsum_le_tsum_norm (f := fun j => M (j + 1) * (g j - g (j + 1)))
            (by simpa [Real.norm_eq_abs] using habs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' j : ℕ, 3 * CM * D * t ^ 2 * ((j + a + 1 : ℕ) : ℝ) ^ (-(3 - δ)) :=
          habs.tsum_le_tsum hterm (hsum3.mul_left _)
      _ = 3 * CM * D * t ^ 2 * ∑' j : ℕ, ((j + a + 1 : ℕ) : ℝ) ^ (-(3 - δ)) := tsum_mul_left
      _ ≤ 3 * CM * D * t ^ 2 * ((a : ℝ) ^ (1 - (3 - δ)) / (3 - δ - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (le_of_eq (tsum_congr (fun j => by push_cast; ring_nf))) htail
      _ ≤ 3 * CM * D * t ^ 2 * (4 * t ^ (-(2 - δ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : (a : ℝ) ^ (1 - (3 - δ)) ≤ (t / 2) ^ (-(2 - δ)) := by
            rw [show (1 : ℝ) - (3 - δ) = -(2 - δ) by ring]
            exact Real.rpow_le_rpow_of_nonpos (by positivity) ht2a (by linarith)
          have h2 : (t / 2) ^ (-(2 - δ)) = 2 ^ (2 - δ) * t ^ (-(2 - δ)) := by
            rw [Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              div_eq_mul_inv, inv_inv, mul_comm]
          have h3 : (2 : ℝ) ^ (2 - δ) ≤ 4 := by
            calc (2 : ℝ) ^ (2 - δ) ≤ 2 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 4 := by norm_num
          have h4 : 1 ≤ 3 - δ - 1 := by linarith
          rw [h2] at h1
          calc (a : ℝ) ^ (1 - (3 - δ)) / (3 - δ - 1) ≤ (a : ℝ) ^ (1 - (3 - δ)) :=
                div_le_self (by positivity) h4
            _ ≤ 2 ^ (2 - δ) * t ^ (-(2 - δ)) := h1
            _ ≤ 4 * t ^ (-(2 - δ)) :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 12 * CM * D * (t ^ (2 : ℝ) * t ^ (-(2 - δ))) := by
          rw [show t ^ (2 : ℝ) = t ^ 2 by norm_num]; ring
      _ = 12 * CM * D * t ^ δ := by
          rw [← Real.rpow_add ht0]; congr 2; ring
  have htδε : t ^ δ ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_le ht hδε
  calc |-(M 0 * g 0) + ∑' j, M (j + 1) * (g j - g (j + 1))|
      ≤ |M 0 * g 0| + |∑' j, M (j + 1) * (g j - g (j + 1))| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ ≤ 2 * CM * thetaCuspFullSource 0 * t ^ δ + 12 * CM * D * t ^ δ := add_le_add hb0 hser
    _ = (2 * CM * thetaCuspFullSource 0 + 12 * CM * D) * t ^ δ := by ring
    _ ≤ (2 * CM * thetaCuspFullSource 0 + 12 * CM * D) * t ^ ε :=
        mul_le_mul_of_nonneg_left htδε (by positivity)

/-- **The causal Möbius–theta boundary criterion (2).**
`RH ⟺ ∀ ε > 0, B(t) = O_ε(t^ε)` on `t ≥ 1`. -/
theorem riemannHypothesis_iff_causalMobiusThetaTail_subpower :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C * t ^ ε :=
  ⟨causalMobiusThetaTail_subpower_of_riemannHypothesis,
    riemannHypothesis_of_causalMobiusThetaTail_subpower⟩

end

end RHTower
