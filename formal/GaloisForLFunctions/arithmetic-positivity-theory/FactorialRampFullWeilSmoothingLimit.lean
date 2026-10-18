import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampSmoothingAndGramMargin
import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilGramDecoupling
import GaloisForLFunctions.BiScaleUncertainty.FactorialRampDiagonalIdentity
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-! Complete Weil-energy continuity under mollification and the ramp–tent Weil margin.

For a compact continuous real source `f` with finite Lévy jump energy, mollification by the
normalized nonnegative bumps `η_k` (support radius `→ 0`) gives:
1. pointwise convergence `η_k * f → f`, and pointwise convergence of all correlations
   `C_{η_k * f}(t) → C_f(t)` by dominated convergence on a common compact window;
2. the jump integrands `(C(0) - C(t)) w(t)` of the mollified sources lie between `0` and the
   integrand of `f`, since averaging contracts squared translation increments, so the Lévy
   jump energies converge by dominated convergence, including the singular endpoint;
3. a fixed finite set of prime powers carries every prime term, and the polar integrals
   converge on a common compact window.
Hence the literal complete Weil energies (archimedean, prime, and polar terms) converge.

For the factorial ramp `r_n = sourceFactorialRamp (n + 1)` this identifies the limit of the
smoothed-ramp energies with the ramp diagonal `factorialSpanWeil n 1 0`. Since each smoothed ramp
is a smooth compact test, its zero-side Weil diagonal equals its complete energy. The zero-side
lower bound `log(n + 1) / (4096 (n + 1))` and upper bound `C (1 + log(n + 1)) / (n + 1)` pass to
the ramp diagonal, and the tent coupling estimates give, eventually in `n` and for all real
`c, d`, `factorialSpanWeil n c d ≥ (log(n + 1) / (8192 (n + 1))) c^2 + ((n + 1) / 2) d^2`. -/

open MeasureTheory Set Filter Complex
open scoped Topology Convolution BigOperators CompactlySupported
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDDoobGraph
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

local notation "acorr" => RHTower.ArchimedeanAnomaly.autocorr

/-- The normalized mollifier vanishes outside `[-1, 1]`. -/
theorem mollifier_eq_zero_of_one_lt_abs (k : ℕ) {t : ℝ} (ht : 1 < |t|) :
    CHMDDoobGraph.mollifier k t = 0 := by
  have hr : (WeilOneSided.narrowBump k).rOut ≤ 1 := by
    change 1 / (4 * ((k : ℝ) + 1)) ≤ 1
    rw [div_le_one (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  apply Function.notMem_support.mp
  rw [CHMDDoobGraph.mollifier, ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs]
  linarith

/-- A compactly supported real source vanishes outside some centered interval. -/
theorem exists_vanishing_radius_of_hasCompactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < |x| → f x = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have h := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
  linarith [le_max_left R 0]

/-- Mollification enlarges the support of a source by at most one. -/
theorem smooth_eq_zero_of_far {f : ℝ → ℝ} {R : ℝ} (hf : ∀ x, R < |x| → f x = 0) (k : ℕ)
    {x : ℝ} (hx : R + 1 < |x|) : smooth f k x = 0 := by
  change (∫ t, CHMDDoobGraph.mollifier k t * f (x - t)) = 0
  have h0 : ∀ t, CHMDDoobGraph.mollifier k t * f (x - t) = 0 := by
    intro t
    by_cases ht : 1 < |t|
    · rw [mollifier_eq_zero_of_one_lt_abs k ht, zero_mul]
    · push Not at ht
      have hxt : R < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      rw [hf _ hxt, mul_zero]
  simp only [h0, integral_zero]

/-- The mollified source converges pointwise to every continuous source. -/
theorem smooth_tendsto_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Tendsto (fun k => smooth f k x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
    narrowBump_rOut_tendsto hf x
  refine h.congr fun k => ?_
  rw [convolution_def]
  rfl

/-- The correlation of a source supported in `[-R, R]` vanishes beyond lag `2 R`. -/
theorem autocorr_eq_zero_of_far {g : ℝ → ℝ} {R : ℝ} (hg : ∀ x, R < |x| → g x = 0)
    {t : ℝ} (ht : 2 * R < |t|) : acorr g t = 0 := by
  change (∫ u, g u * g (u + t)) = 0
  have h0 : ∀ u, g u * g (u + t) = 0 := by
    intro u
    by_cases hu : R < |u|
    · rw [hg u hu, zero_mul]
    · push Not at hu
      have hut : R < |u + t| := by
        have := abs_sub_abs_le_abs_sub t (-u)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [hg _ hut, mul_zero]
  simp only [h0, integral_zero]

/-- Uniform bound for correlations of bounded sources supported in `[-R, R]`. -/
theorem abs_autocorr_le_of_bound {g : ℝ → ℝ} {M R : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hg : ∀ x, R < |x| → g x = 0) (t : ℝ) :
    |acorr g t| ≤ ∫ u, (Icc (-R) R).indicator (fun _ => M ^ 2) u := by
  have hbint : Integrable (fun u => (Icc (-R) R).indicator (fun _ => M ^ 2) u) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hpt : ∀ u, ‖g u * g (u + t)‖ ≤ (Icc (-R) R).indicator (fun _ => M ^ 2) u := by
    intro u
    by_cases hu : u ∈ Icc (-R) R
    · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, sq]
      exact mul_le_mul (hM u) (hM _) (abs_nonneg _) ((abs_nonneg _).trans (hM u))
    · have hu' : R < |u| := not_le.mp fun h => hu (abs_le.mp h)
      rw [indicator_of_notMem hu, hg u hu', zero_mul, norm_zero]
  have h := norm_integral_le_of_norm_le hbint (Eventually.of_forall hpt)
  change |∫ u, g u * g (u + t)| ≤ _
  simpa only [Real.norm_eq_abs] using h

/-- Correlations of mollified bounded compactly supported sources converge pointwise. -/
theorem autocorr_smooth_tendsto {f : ℝ → ℝ} (hf : Continuous f) {M R : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hR : ∀ x, R < |x| → f x = 0) (t : ℝ) :
    Tendsto (fun k => acorr (smooth f k) t) atTop (𝓝 (acorr f t)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
    fun x hx => hR x (by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
      exact hx)
  have hf2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hfc
  have hcont (k : ℕ) : Continuous (smooth f k) := (smooth_contDiff hf2 k).continuous
  have hbint : Integrable (fun u => (Icc (-(R + 1)) (R + 1)).indicator (fun _ => M ^ 2) u) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  change Tendsto (fun k => ∫ u, smooth f k u * smooth f k (u + t)) atTop
    (𝓝 (∫ u, f u * f (u + t)))
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbint (fun k => ?_) ?_
  · exact ((hcont k).mul ((hcont k).comp (continuous_add_const t))).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Icc (-(R + 1)) (R + 1)
    · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, sq]
      exact mul_le_mul (smooth_bound hM0 hM k u) (smooth_bound hM0 hM k _) (abs_nonneg _) hM0
    · have hu' : R + 1 < |u| := not_le.mp fun h => hu (abs_le.mp h)
      rw [indicator_of_notMem hu, smooth_eq_zero_of_far hR k hu', zero_mul, norm_zero]
  · exact Eventually.of_forall fun u =>
      (smooth_tendsto_of_continuous hf u).mul (smooth_tendsto_of_continuous hf (u + t))

/-- Squared translation increments of a mollified source are dominated by those of the source,
so its Lévy jump integrand is squeezed between zero and the source's integrand. -/
theorem autocorr_smooth_sub_le {f : ℝ → ℝ} (hf : Continuous f) {M R : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hR : ∀ x, R < |x| → f x = 0) (k : ℕ) (t : ℝ) :
    0 ≤ acorr (smooth f k) 0 - acorr (smooth f k) t ∧
      acorr (smooth f k) 0 - acorr (smooth f k) t ≤ acorr f 0 - acorr f t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
    fun x hx => hR x (by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
      exact hx)
  have hf2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hfc
  have hs := smooth_contDiff hf2 k
  have hsc := smooth_compact hfc k
  have h1 := RHTower.ArchimedeanAnomaly.integral_sub_shift_sq hsc hs.continuous t
  have h2 := RHTower.ArchimedeanAnomaly.integral_sub_shift_sq hfc hf t
  have hle := smooth_difference_L2_le hf.measurable hfc hM0 hM k t
  have hnn : 0 ≤ ∫ x, (smooth f k x - smooth f k (x + t)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  constructor <;> linarith

/-- The Lévy–sinh weight is continuous on the open positive half-line. -/
theorem continuousOn_archLevySinhWeight_pos_halfLine :
    ContinuousOn archLevySinhWeight (Ioi 0) := by
  unfold archLevySinhWeight
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousOn.div
    Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr hx).ne'

/-- **Lévy jump energy is continuous under mollification.** For a compact continuous source
with finite jump energy, the jump energies of its mollifications converge to its own. The
mollified integrands are dominated by the source integrand. -/
theorem biScaleLevyEnergy_smooth_tendsto (f : C_c(ℝ, ℝ))
    (hJ : IntegrableOn (fun x => (acorr f 0 - acorr f x) * archLevySinhWeight x) (Ioi 0)) :
    Tendsto (fun k => biScaleLevyEnergy (smooth f k)) atTop (𝓝 (biScaleLevyEnergy f)) := by
  have hfc : Continuous (f : ℝ → ℝ) := map_continuous f
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support f.hasCompactSupport
  have hM' : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  obtain ⟨R, -, hR⟩ := exists_vanishing_radius_of_hasCompactSupport f.hasCompactSupport
  have hf2 : MemLp (f : ℝ → ℝ) 2 volume := hfc.memLp_of_hasCompactSupport f.hasCompactSupport
  unfold biScaleLevyEnergy
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hJ (fun k => ?_) ?_
  · have hc := RHTower.ArchimedeanExactForm.continuous_autocorr (smooth_contDiff hf2 k)
      (smooth_compact f.hasCompactSupport k)
    exact ((continuous_const.sub hc).continuousOn.mul
      continuousOn_archLevySinhWeight_pos_halfLine).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨h0, h1⟩ := autocorr_smooth_sub_le hfc hM' hR k x
    have hw := (archLevySinhWeight_pos hx).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hw)]
    exact mul_le_mul_of_nonneg_right h1 hw
  · exact Eventually.of_forall fun x =>
      (((autocorr_smooth_tendsto hfc hM' hR 0).sub
        (autocorr_smooth_tendsto hfc hM' hR x)).mul_const _)

/-- **Prime and polar pairing continuity under mollification.** All mollified correlations
vanish beyond a common lag, so a fixed finite set of prime powers contributes, and the polar
integrals converge by dominated convergence on a common compact window. -/
theorem fullPairing_autocorr_smooth_tendsto (f : C_c(ℝ, ℝ)) :
    Tendsto (fun k => fullPairing (acorr (smooth f k))) atTop (𝓝 (fullPairing (acorr f))) := by
  have hfc : Continuous (f : ℝ → ℝ) := map_continuous f
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support f.hasCompactSupport
  have hM' : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  obtain ⟨R, hR0, hR⟩ := exists_vanishing_radius_of_hasCompactSupport f.hasCompactSupport
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  have hRk (k : ℕ) : ∀ x, R + 1 < |x| → smooth f k x = 0 := fun x hx =>
    smooth_eq_zero_of_far hR k hx
  have hMk (k : ℕ) : ∀ x, |smooth f k x| ≤ M := smooth_bound hM0 hM' k
  have hf2 : MemLp (f : ℝ → ℝ) 2 volume := hfc.memLp_of_hasCompactSupport f.hasCompactSupport
  have hck (k : ℕ) : Continuous (acorr (smooth f k)) :=
    RHTower.ArchimedeanExactForm.continuous_autocorr (smooth_contDiff hf2 k)
      (smooth_compact f.hasCompactSupport k)
  have hvan (k : ℕ) (t : ℝ) (ht : 2 * (R + 1) < |t|) : acorr (smooth f k) t = 0 :=
    autocorr_eq_zero_of_far (hRk k) ht
  have hvan0 (t : ℝ) (ht : 2 * (R + 1) < |t|) : acorr f t = 0 :=
    autocorr_eq_zero_of_far hR (by linarith)
  set N0 : ℕ := ⌈Real.exp (2 * (R + 1))⌉₊ with hN0
  have hlog : ∀ n : ℕ, n ∉ Finset.range (N0 + 1) → 2 * (R + 1) < |Real.log n| := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hn' : Real.exp (2 * (R + 1)) < (n : ℝ) := by
      have h1 := Nat.le_ceil (Real.exp (2 * (R + 1)))
      have h2 : ((N0 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hl := (Real.lt_log_iff_exp_lt hpos).mpr hn'
    rw [abs_of_pos (lt_of_le_of_lt (by positivity) hl)]
    exact hl
  have hprime (H : ℝ → ℝ) (hH : ∀ t, 2 * (R + 1) < |t| → H t = 0) :
      (∑' n, primeTerm H n) = ∑ n ∈ Finset.range (N0 + 1), primeTerm H n := by
    apply tsum_eq_sum
    intro n hn
    unfold primeTerm
    split_ifs
    · rw [hH _ (hlog n hn), mul_zero]
    · rfl
  set B : ℝ := ∫ u, (Icc (-(R + 1)) (R + 1)).indicator (fun _ => M ^ 2) u with hB
  have hbound : Integrable (fun x => (Icc 0 (2 * (R + 1))).indicator
      (fun x => polarDensity x * B) x) (volume.restrict (Ici 0)) :=
    (((continuous_polarDensity.mul continuous_const).integrableOn_Icc).integrable_indicator
      measurableSet_Icc).restrict
  have hpolar : Tendsto (fun k => ∫ x in Ici (0 : ℝ), polarDensity x * acorr (smooth f k) x)
      atTop (𝓝 (∫ x in Ici (0 : ℝ), polarDensity x * acorr f x)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbound (fun k => ?_) ?_
    · exact (continuous_polarDensity.mul (hck k)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      by_cases hxw : x ∈ Icc 0 (2 * (R + 1))
      · rw [indicator_of_mem hxw, norm_mul, Real.norm_of_nonneg (polarDensity_nonneg x),
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_autocorr_le_of_bound (hMk k) (hRk k) x)
          (polarDensity_nonneg x)
      · have hx' : 2 * (R + 1) < |x| := by
          rw [abs_of_nonneg (mem_Ici.mp hx)]
          exact lt_of_not_ge fun h => hxw ⟨mem_Ici.mp hx, h⟩
        rw [indicator_of_notMem hxw, hvan k x hx', mul_zero, norm_zero]
    · exact Eventually.of_forall fun x =>
        (autocorr_smooth_tendsto hfc hM' hR x).const_mul (polarDensity x)
  have hpr : Tendsto (fun k => ∑ n ∈ Finset.range (N0 + 1), primeTerm (acorr (smooth f k)) n)
      atTop (𝓝 (∑ n ∈ Finset.range (N0 + 1), primeTerm (acorr f) n)) := by
    refine tendsto_finsetSum _ fun n _ => ?_
    unfold primeTerm
    split_ifs
    · exact (autocorr_smooth_tendsto hfc hM' hR _).const_mul _
    · exact tendsto_const_nhds
  have he : (fun k => fullPairing (acorr (smooth f k))) = fun k =>
      (∑ n ∈ Finset.range (N0 + 1), primeTerm (acorr (smooth f k)) n) -
        ∫ x in Ici (0 : ℝ), polarDensity x * acorr (smooth f k) x := by
    funext k
    rw [fullPairing, hprime _ (hvan k)]
  rw [he, fullPairing, hprime _ hvan0]
  exact hpr.sub hpolar

/-- The mollified compact source packaged as a compactly supported continuous function. -/
def smoothCompactSource (f : C_c(ℝ, ℝ)) (k : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨smooth f k, (smooth_contDiff ((map_continuous f).memLp_of_hasCompactSupport
    f.hasCompactSupport) k).continuous⟩, smooth_compact f.hasCompactSupport k⟩

/-- **Complete Weil-energy continuity under mollification.** For a compact continuous real
source with finite Lévy jump energy, the literal complete Weil energies (archimedean, prime,
and polar terms) of its mollifications converge to its own complete Weil energy. -/
theorem re_weilFullFunctional_smooth_tendsto (f : C_c(ℝ, ℝ))
    (hJ : IntegrableOn (fun x => (acorr f 0 - acorr f x) * archLevySinhWeight x) (Ioi 0)) :
    Tendsto (fun k => (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (smooth f k u : ℂ)) (fun u => (smooth f k u : ℂ)))).re) atTop
      (𝓝 ((weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)) := by
  have hfc : Continuous (f : ℝ → ℝ) := map_continuous f
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support f.hasCompactSupport
  have hM' : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  obtain ⟨R, -, hR⟩ := exists_vanishing_radius_of_hasCompactSupport f.hasCompactSupport
  have hf2 : MemLp (f : ℝ → ℝ) 2 volume := hfc.memLp_of_hasCompactSupport f.hasCompactSupport
  have hk (k : ℕ) := re_weilFullFunctional_eq_of_compact_finite_jump (smoothCompactSource f k)
    (integrableOn_biScaleLevyIntegrand (smooth_contDiff hf2 k)
      (smooth_compact f.hasCompactSupport k))
  rw [re_weilFullFunctional_eq_of_compact_finite_jump f hJ]
  refine Tendsto.congr (fun k => (hk k).symm) ?_
  exact (((autocorr_smooth_tendsto hfc hM' hR 0).const_mul (EF.gammaBracket 0)).add
    (biScaleLevyEnergy_smooth_tendsto f hJ)).sub
      ((fullPairing_autocorr_smooth_tendsto f).const_mul 2)

/-- The convolution `η_k * r_n` is the corpus mollification of the factorial ramp. -/
theorem factorialMuntzSmoothedRamp_eq_smooth (n k : ℕ) :
    factorialMuntzSmoothedRamp n k = smooth (sourceFactorialRamp (n + 1)) k := by
  funext x
  rw [factorialMuntzSmoothedRamp, convolution_def]
  rfl

/-- The compact factorial ramp has finite Lévy jump energy. -/
theorem factorialRampSource_jump_integrable (n : ℕ) :
    IntegrableOn (fun x => (acorr (factorialRampSource n) 0 -
      acorr (factorialRampSource n) x) * archLevySinhWeight x) (Ioi 0) := by
  have h := factorialSourceLeft_jump_integrable n
  simpa only [factorialSourceLeft_autocorr_eq_ramp] using h

/-- **Unsmoothed ramp energy.** The literal complete Weil energy of the compact factorial ramp
`r_n = sourceFactorialRamp (n + 1)` equals the ramp diagonal `factorialSpanWeil n 1 0` of the
factorial span. -/
theorem factorialRamp_weilFullFunctional_eq (n : ℕ) :
    (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (EF.weilTest (fun u => (sourceFactorialRamp (n + 1) u : ℂ))
        (fun u => (sourceFactorialRamp (n + 1) u : ℂ)))).re = factorialSpanWeil n 1 0 := by
  have h1 := re_weilFullFunctional_eq_of_compact_finite_jump (factorialRampSource n)
    (factorialRampSource_jump_integrable n)
  have hf : acorr (factorialSourceLeft n) = acorr (factorialRampSource n) :=
    funext (factorialSourceLeft_autocorr_eq_ramp n)
  have hJ : biScaleLevyEnergy (factorialSourceLeft n) =
      biScaleLevyEnergy (factorialRampSource n) := by
    unfold biScaleLevyEnergy
    rw [hf]
  rw [factorialSpanWeil_eq_complete]
  simp only [one_smul, zero_smul, add_zero]
  rw [hf, hJ]
  exact h1

/-- **Full Weil-energy continuity for the factorial ramp.** For every arithmetic scale `n`,
the literal complete Weil energies of the smoothed ramps `η_k * r_n`
converge, as `k → ∞`, to the complete Weil energy of `r_n`, which is `factorialSpanWeil n 1 0`.
The prime, archimedean, and polar terms are all included. -/
theorem factorialMuntzSmoothedRamp_weilFullFunctional_tendsto (n : ℕ) :
    Tendsto (fun k => (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (EF.weilTest (fun u => (factorialMuntzSmoothedRamp n k u : ℂ))
        (fun u => (factorialMuntzSmoothedRamp n k u : ℂ)))).re) atTop
      (𝓝 ((weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (EF.weilTest (fun u => (sourceFactorialRamp (n + 1) u : ℂ))
          (fun u => (sourceFactorialRamp (n + 1) u : ℂ)))).re)) := by
  simp_rw [factorialMuntzSmoothedRamp_eq_smooth]
  exact re_weilFullFunctional_smooth_tendsto (factorialRampSource n)
    (factorialRampSource_jump_integrable n)

/-- The smoothed-ramp complete energies converge to the ramp diagonal of the factorial span. -/
theorem factorialMuntzSmoothedRamp_weilFullFunctional_tendsto_span (n : ℕ) :
    Tendsto (fun k => (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (EF.weilTest (fun u => (factorialMuntzSmoothedRamp n k u : ℂ))
        (fun u => (factorialMuntzSmoothedRamp n k u : ℂ)))).re) atTop
      (𝓝 (factorialSpanWeil n 1 0)) := by
  rw [← factorialRamp_weilFullFunctional_eq]
  exact factorialMuntzSmoothedRamp_weilFullFunctional_tendsto n

/-- The zero-side Weil diagonals of the smoothed ramps converge to the ramp diagonal of the
factorial span: on each smooth compact ramp the zero sum equals the complete physical energy. -/
theorem factorialMuntzSmoothedRamp_re_W_tendsto (n : ℕ) :
    Tendsto (fun k => (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))
      (fun x => (factorialMuntzSmoothedRamp n k x : ℂ))).re) atTop
      (𝓝 (factorialSpanWeil n 1 0)) := by
  refine (factorialMuntzSmoothedRamp_weilFullFunctional_tendsto_span n).congr fun k => ?_
  have hf2 : MemLp (sourceFactorialRamp (n + 1)) 2 volume :=
    (continuous_sourceFactorialRamp (n + 1)).memLp_of_hasCompactSupport
      (hasCompactSupport_sourceFactorialRamp (N := n + 1) (by omega))
  have hcd : ContDiff ℝ 2 (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) := by
    rw [factorialMuntzSmoothedRamp_eq_smooth]
    exact Complex.ofRealCLM.contDiff.comp (smooth_contDiff hf2 k)
  have hcs : HasCompactSupport (fun x => (factorialMuntzSmoothedRamp n k x : ℂ)) := by
    rw [factorialMuntzSmoothedRamp_eq_smooth]
    exact (smooth_compact (hasCompactSupport_sourceFactorialRamp (N := n + 1) (by omega)) k
      ).comp_left Complex.ofReal_zero
  rw [zeta_W_eq_weilFullFunctional_mixed hcd hcs hcd hcs]

/-- **Logarithmic size of the ramp diagonal.** There is an absolute `C > 0` such that
eventually in `n`,
`log(n + 1) / (4096 (n + 1)) ≤ factorialSpanWeil n 1 0 ≤ C (1 + log(n + 1)) / (n + 1)`. -/
theorem factorialSpanWeil_ramp_log_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.log ((n + 1 : ℕ) : ℝ) / (4096 * ((n + 1 : ℕ) : ℝ)) ≤ factorialSpanWeil n 1 0 ∧
      factorialSpanWeil n 1 0 ≤ C * (1 + Real.log (n + 1 : ℝ)) / (n + 1 : ℝ) :=
  factorialRamp_weil_limit_bounds_of_tendsto _ factorialMuntzSmoothedRamp_re_W_tendsto

/-- The factorial span energy is the binary Gram form of its ramp, mixed, and tent entries. -/
theorem factorialSpanWeil_eq_binaryGramForm (n : ℕ) (c d : ℝ) :
    binaryGramForm (factorialSpanWeil n 1 0) (factorialWeilMixed n) (factorialSpanWeil n 0 1)
      c d = factorialSpanWeil n c d := by
  rw [factorialSpanWeil_gram n c d]
  unfold binaryGramForm
  ring

/-- **Complete Weil margin on the factorial ramp–tent span.** Eventually in `n`, for all real
`c, d`,
`factorialSpanWeil n c d ≥ (log(n + 1) / (8192 (n + 1))) c^2 + ((n + 1) / 2) d^2`, and the
tent-optimized ramp energy satisfies `factorialWeilMinRamp n ≥ log(n + 1) / (8192 (n + 1))`. -/
theorem factorialSpanWeil_rampTent_margin :
    ∀ᶠ n : ℕ in atTop,
      (∀ c d : ℝ,
        Real.log ((n + 1 : ℕ) : ℝ) / (8192 * ((n + 1 : ℕ) : ℝ)) * c ^ 2 +
          (((n + 1 : ℕ) : ℝ) / 2) * d ^ 2 ≤ factorialSpanWeil n c d) ∧
      Real.log ((n + 1 : ℕ) : ℝ) / (8192 * ((n + 1 : ℕ) : ℝ)) ≤ factorialWeilMinRamp n := by
  have h := factorialRampTent_gram_margin_of_tendsto (fun n => factorialSpanWeil n 1 0)
    factorialWeilMixed (fun n => factorialSpanWeil n 0 1) factorialWeilMixedBound
    factorialMuntzSmoothedRamp_re_W_tendsto factorialTentWeil_eventually_ge_scale
    factorialWeilMixed_abs_le factorialWeilMixedBound_tendsto
  filter_upwards [h] with n hn
  refine ⟨fun c d => ?_, ?_⟩
  · rw [← factorialSpanWeil_eq_binaryGramForm]
    exact hn.1 c d
  · have he : binaryGramMinRamp (factorialSpanWeil n 1 0) (factorialWeilMixed n)
        (factorialSpanWeil n 0 1) = factorialWeilMinRamp n := by
      unfold binaryGramMinRamp factorialWeilMinRamp
      rw [factorialSpanWeil_eq_binaryGramForm]
    rw [← he]
    exact hn.2

end

end GaloisForLFunctions.ArithmeticPositivityTheory
