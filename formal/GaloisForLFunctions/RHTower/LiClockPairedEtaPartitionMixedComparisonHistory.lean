import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionMixedSignBoundary
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionRelativeVolterra
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# Mixed-kernel growth, Cesàro limit and the differentiated comparison identity

For the literal infinite mixed kernel `B_∞` with moment-ratio limit `λ`:

* the coefficient prefixes satisfy `A_j/(j+1) → λ` (Cesàro), with the exact split
  `A_j = λ(j+1) + σ - δ_j`;
* `B_∞(t)/(cosh 2t + t sinh 2t) → λ`, `e^{-2t} B_∞(t) → ∞` and `log B_∞(t)/t → 2`;
* the strict decrease `q_∞(b) < q_∞(a)` of the logarithmic derivative persists on open
  neighbourhoods of the witness pair, uniformly for all large finite prefixes.

For every finite prefix `N` and common regular source radius, the literal completed forcing
identity `J_N = 2 (F_N ⋆ B_N)` differentiates to the comparison identity

```text
F_N(t) = (B_N(t)/2) R_N'(t) + ∫_0^t F_N(s) B_N(t-s) [q_N(t) - q_N(t-s)] ds,   R_N = J_N/B_N,
```

for every `t > 0`, with `q_N = B_N'/B_N`.
-/

open Set Filter Topology MeasureTheory Complex RiemannGaussian
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Coefficient Cesàro limit -/

/-- The degree-zero moment ratio is one. -/
theorem liClockPairedEtaInfinitePartitionMomentRatio_zero :
    liClockPairedEtaInfinitePartitionMomentRatio 0 = 1 := by
  rw [liClockPairedEtaInfinitePartitionMomentRatio,
    liClockPairedEtaInfiniteSymmetrizedEvenMoment_zero,
    liClockPairedEtaHalfLineSymmetrizedEvenMoment_zero, div_one]

/-- No missing constant at the origin: `λ + σ - δ_0 = 1`. -/
theorem liClockPairedEtaInfinitePartitionMixed_profile_constant :
    liClockPairedEtaInfinitePartitionComparisonLimit +
        liClockPairedEtaInfinitePartitionMixedMomentErrorSum -
        liClockPairedEtaInfinitePartitionMixedMomentErrorTail 0 = 1 := by
  have h := (liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec 0).2
  simp only [zero_add, Finset.range_one, Finset.sum_singleton,
    liClockPairedEtaInfinitePartitionMomentRatio_zero] at h
  linarith

/-- Exact prefix split `A_j = λ(j+1) + σ - δ_j`. -/
theorem liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix_eq (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j =
      liClockPairedEtaInfinitePartitionComparisonLimit * (j + 1) +
        liClockPairedEtaInfinitePartitionMixedMomentErrorSum -
        liClockPairedEtaInfinitePartitionMixedMomentErrorTail j := by
  have h := (liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec j).2
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  unfold liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix
  push_cast at h
  linarith

/-- **Cesàro limit.**  `A_j/(j+1) → λ`. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix_div :
    Tendsto (fun j : ℕ => liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j / (j + 1))
      atTop (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have htail : Tendsto liClockPairedEtaInfinitePartitionMixedMomentErrorTail atTop (𝓝 0) := by
    have hg : Tendsto (fun j : ℕ => (liClockPairedEtaInfinitePartitionMomentErrorScale / 8) *
        (1 / 9 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
        (by norm_num)).const_mul (liClockPairedEtaInfinitePartitionMomentErrorScale / 8)
    exact squeeze_zero_norm (fun j => by
      rw [Real.norm_eq_abs]; exact (liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec j).1)
      hg
  have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (hinv.mul ((tendsto_const_nhds
    (x := liClockPairedEtaInfinitePartitionMixedMomentErrorSum)).sub htail)).const_add
    liClockPairedEtaInfinitePartitionComparisonLimit
  simp only [sub_zero, zero_mul, add_zero] at h
  refine h.congr fun j => ?_
  rw [liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix_eq]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Exponential growth of the complete kernel -/

private theorem comparisonLimit_half_pos :
    0 < liClockPairedEtaInfinitePartitionComparisonLimit / 2 :=
  half_pos liClockPairedEtaInfinitePartitionComparisonLimit_pos

/-- `e^{-2t} B_∞(t) → ∞`. -/
theorem tendsto_exp_neg_mul_liClockPairedEtaInfinitePartitionMixedBorelKernel_atTop :
    Tendsto (fun t : ℝ => Real.exp (-2 * t) * liClockPairedEtaInfinitePartitionMixedBorelKernel t)
      atTop atTop := by
  have h := tendsto_id.atTop_mul_pos comparisonLimit_half_pos
    tendsto_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_clock_exp
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [id]
  have ht0 := ht.ne'
  have hE := (Real.exp_pos (2 * t)).ne'
  rw [show -2 * t = -(2 * t) by ring, Real.exp_neg]
  field_simp

/-- `log B_∞(t)/t → 2`. -/
theorem tendsto_log_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_atTop :
    Tendsto (fun t : ℝ => Real.log (liClockPairedEtaInfinitePartitionMixedBorelKernel t) / t)
      atTop (𝓝 2) := by
  set ρ : ℝ → ℝ := fun t => liClockPairedEtaInfinitePartitionMixedBorelKernel t /
    (t * Real.exp (2 * t))
  have hρ : Tendsto ρ atTop (𝓝 (liClockPairedEtaInfinitePartitionComparisonLimit / 2)) :=
    tendsto_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_clock_exp
  have hlogρ : Tendsto (fun t => Real.log (ρ t) / t) atTop (𝓝 0) := by
    have hl := (Real.continuousAt_log comparisonLimit_half_pos.ne').tendsto.comp hρ
    simpa using hl.div_atTop tendsto_id
  have hlogt : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsum := (hlogρ.add hlogt).const_add 2
  rw [add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  have hρpos : ∀ᶠ t in atTop, 0 < ρ t := hρ.eventually (lt_mem_nhds comparisonLimit_half_pos)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hρpos] with t ht hpos
  have hB : liClockPairedEtaInfinitePartitionMixedBorelKernel t =
      ρ t * t * Real.exp (2 * t) := by
    simp only [ρ]; field_simp
  rw [hB, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hpos.ne' ht.ne',
    Real.log_exp]
  field_simp
  ring

/-- `B_∞(t)/(cosh 2t + t sinh 2t) → λ`, the hyperbolic comparison of the complete series. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_hyperbolic :
    Tendsto (fun t : ℝ => liClockPairedEtaInfinitePartitionMixedBorelKernel t /
      (Real.cosh (2 * t) + t * Real.sinh (2 * t))) atTop
      (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hD : Tendsto (fun t : ℝ => (Real.cosh (2 * t) + t * Real.sinh (2 * t)) /
      (t * Real.exp (2 * t))) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-4 * t)) / (2 * t)) atTop (𝓝 0) := by
      have := (he.const_add 1).div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
      simpa using this
    have h2 : Tendsto (fun t : ℝ => (1 - Real.exp (-4 * t)) / 2) atTop (𝓝 (1 / 2)) := by
      simpa using (he.const_sub 1).div_const 2
    refine (h1.add h2).congr' ?_ |>.trans (by rw [zero_add])
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.cosh_eq, Real.sinh_eq]
    have hx : Real.exp (2 * t) ≠ 0 := (Real.exp_pos _).ne'
    have hm : Real.exp (-(2 * t)) = Real.exp (-4 * t) * Real.exp (2 * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [hm]
    field_simp
  have h := tendsto_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_clock_exp.div hD
    (by norm_num)
  rw [show liClockPairedEtaInfinitePartitionComparisonLimit / 2 / (1 / 2) =
    liClockPairedEtaInfinitePartitionComparisonLimit by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hD0 : 0 < Real.cosh (2 * t) + t * Real.sinh (2 * t) := by
    have := Real.cosh_pos (2 * t)
    have : 0 ≤ t * Real.sinh (2 * t) := mul_nonneg ht.le (Real.sinh_nonneg_iff.2 (by linarith))
    linarith
  have hx : 0 < t * Real.exp (2 * t) := mul_pos ht (Real.exp_pos _)
  rw [Pi.div_apply]
  field_simp

/-! ## Open witness neighbourhoods -/

private theorem continuous_liClockPairedEtaInfinitePartitionMixedLogDerivative :
    Continuous liClockPairedEtaInfinitePartitionMixedLogDerivative := by
  have hB := contDiff_liClockPairedEtaInfinitePartitionMixedBorelKernel
  have hd : Continuous (deriv liClockPairedEtaInfinitePartitionMixedBorelKernel) :=
    hB.continuous_deriv (by simp)
  exact hd.div hB.continuous fun t =>
    (lt_of_lt_of_le zero_lt_one (one_le_liClockPairedEtaInfinitePartitionMixedBorelKernel t)).ne'

/-- The strict decrease of the logarithmic derivative holds on open neighbourhoods of the witness
pair, for the complete kernel and uniformly for every sufficiently large finite prefix. -/
theorem exists_liClockPairedEtaPartitionMixedLogDerivative_open_witness :
    ∃ a b ε : ℝ, 0 < ε ∧ 0 < a - ε ∧ a + ε < b - ε ∧
      (∀ a' ∈ Ioo (a - ε) (a + ε), ∀ b' ∈ Ioo (b - ε) (b + ε),
        liClockPairedEtaInfinitePartitionMixedLogDerivative b' <
          liClockPairedEtaInfinitePartitionMixedLogDerivative a') ∧
      ∀ᶠ N : ℕ in atTop, ∀ a' ∈ Ioo (a - ε) (a + ε), ∀ b' ∈ Ioo (b - ε) (b + ε),
        liClockPairedEtaPartitionMixedLogDerivative N b' <
          liClockPairedEtaPartitionMixedLogDerivative N a' := by
  obtain ⟨a, b, ha, hab, hq, -⟩ :=
    exists_liClockPairedEtaPartitionMixedLogDerivative_stable_window_witness
  set q := liClockPairedEtaInfinitePartitionMixedLogDerivative
  have hq' : Continuous q := continuous_liClockPairedEtaInfinitePartitionMixedLogDerivative
  set δ := (q a - q b) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨εa, hεa, hA⟩ := Metric.continuous_iff.1 hq' a δ hδ0
  obtain ⟨εb, hεb, hB⟩ := Metric.continuous_iff.1 hq' b δ hδ0
  set ε := min (min εa εb) (min (a / 2) ((b - a) / 4)) with hε
  have hε0 : 0 < ε := by
    rw [hε]; apply lt_min (lt_min hεa hεb) (lt_min (by linarith) (by linarith))
  have hεa' : ε ≤ εa := (min_le_left _ _).trans (min_le_left _ _)
  have hεb' : ε ≤ εb := (min_le_left _ _).trans (min_le_right _ _)
  have hεa2 : ε ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεab : ε ≤ (b - a) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hnear : ∀ a' ∈ Ioo (a - ε) (a + ε), ∀ b' ∈ Ioo (b - ε) (b + ε),
      q a - δ < q a' ∧ q b' < q b + δ := by
    intro a' ha' b' hb'
    have h1 : dist a' a < εa := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ha'.1, ha'.2]
    have h2 : dist b' b < εb := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hb'.1, hb'.2]
    have h3 := hA a' h1
    have h4 := hB b' h2
    rw [Real.dist_eq, abs_lt] at h3 h4
    exact ⟨by linarith [h3.1], by linarith [h4.2]⟩
  refine ⟨a, b, ε, hε0, by linarith, by linarith, fun a' ha' b' hb' => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hnear a' ha' b' hb'
    linarith
  · have hconv := tendstoUniformlyOn_liClockPairedEtaPartitionMixedLogDerivative (b + ε)
      (by linarith)
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv δ hδ0] with N hN a' ha' b' hb'
    obtain ⟨h1, h2⟩ := hnear a' ha' b' hb'
    have hmem : ∀ t ∈ Ioo (a - ε) (b + ε), t ∈ Metric.closedBall (0 : ℝ) (b + ε) := by
      intro t ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have ha'' := hN a' (hmem a' ⟨ha'.1, by linarith [ha'.2]⟩)
    have hb'' := hN b' (hmem b' ⟨by linarith [hb'.1], hb'.2⟩)
    rw [Real.dist_eq, abs_lt] at ha'' hb''
    linarith [ha''.1, hb''.2]

/-! ## The differentiated comparison identity -/

/-- Every positive finite prefix has a smooth literal mixed kernel. -/
theorem contDiff_liClockPairedEtaPartitionMixedBorelKernel {N : ℕ} (hN : 0 < N) :
    ContDiff ℝ ⊤ (liClockPairedEtaPartitionMixedBorelKernel N) := by
  have h0 : ContDiff ℂ ⊤ (liClockPairedEtaPartitionMixedBorelKernelComplex N) :=
    AnalyticOnNhd.contDiff (fun z _ => analyticAt_liClockPairedEtaPartitionMixedBorelKernelComplex hN z)
  have h := h0.real_of_complex
  have he : (fun t : ℝ => (liClockPairedEtaPartitionMixedBorelKernelComplex N (t : ℂ)).re) =
      liClockPairedEtaPartitionMixedBorelKernel N := by
    funext t
    rw [liClockPairedEtaPartitionMixedBorelKernelComplex_ofReal, Complex.ofReal_re]
  rw [he] at h
  exact h

/-- The literal relative forcing quotient `R_N = J_N / B_N`. -/
def liClockPairedEtaPartitionRelativeForcingQuotient (N : ℕ) (t : ℝ) : ℝ :=
  liClockPairedEtaPartitionRelativeForcing N t / liClockPairedEtaPartitionMixedBorelKernel N t

/-- **Differentiated comparison identity.**  For a common regular source radius and every
`t > 0`, with `F_N` the real gap clock response and `q_N = B_N'/B_N`,
`F_N(t) = (B_N(t)/2) R_N'(t) + ∫_0^t F_N(s) B_N(t-s) [q_N(t) - q_N(t-s)] ds`. -/
theorem liClockPairedEtaPartition_comparison_identity {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (hrhalf : r < 1 / 2)
    (hclosed : ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      pairedEtaFiniteLaplacePartition N (1 / 2 + z * I) ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (liClockPairedEtaPartitionRelativeForcingQuotient N)
      (2 * (liClockPairedEtaFiniteGapClockResponse N r (t : ℂ)).re /
          liClockPairedEtaPartitionMixedBorelKernel N t +
        2 / liClockPairedEtaPartitionMixedBorelKernel N t *
          ∫ s in (0 : ℝ)..t, (liClockPairedEtaFiniteGapClockResponse N r (s : ℂ)).re *
            liClockPairedEtaPartitionMixedBorelKernel N (t - s) *
            (liClockPairedEtaPartitionMixedLogDerivative N (t - s) -
              liClockPairedEtaPartitionMixedLogDerivative N t)) t ∧
    (liClockPairedEtaFiniteGapClockResponse N r (t : ℂ)).re =
      liClockPairedEtaPartitionMixedBorelKernel N t / 2 *
          deriv (liClockPairedEtaPartitionRelativeForcingQuotient N) t +
        ∫ s in (0 : ℝ)..t, (liClockPairedEtaFiniteGapClockResponse N r (s : ℂ)).re *
          liClockPairedEtaPartitionMixedBorelKernel N (t - s) *
          (liClockPairedEtaPartitionMixedLogDerivative N t -
            liClockPairedEtaPartitionMixedLogDerivative N (t - s)) := by
  set B := liClockPairedEtaPartitionMixedBorelKernel N with hBdef
  set F : ℝ → ℝ := fun s => (liClockPairedEtaFiniteGapClockResponse N r (s : ℂ)).re with hFdef
  set q := liClockPairedEtaPartitionMixedLogDerivative N with hqdef
  have hL : 0 < Real.log (2 * (N : ℝ)) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  have hBs := contDiff_liClockPairedEtaPartitionMixedBorelKernel hN
  have hBd : ∀ s, HasDerivAt B (deriv B s) s := fun s =>
    ((hBs.differentiable (by simp)) s).hasDerivAt
  have hB'c : Continuous (deriv B) := hBs.continuous_deriv (by simp)
  have hBpos : ∀ s, 0 < B s := liClockPairedEtaPartitionMixedBorelKernel_pos hN
  have hB0 : B 0 = 1 := liClockPairedEtaPartitionMixedBorelKernel_zero hN
  have hFc : Continuous F := by
    have hA := continuous_liClockPairedEtaPartitionClockResponseReal hr hclosed
    have hU := continuous_liClockPairedEtaContiguousPartitionClockReal hL hr hrhalf
    refine (hA.sub hU).congr fun s => ?_
    simp only [Pi.sub_apply, hFdef,
      liClockPairedEtaFiniteGapClockResponse_eq_partition_sub_contiguous hN hr
      hrhalf hclosed, Complex.sub_re, liClockPairedEtaPartitionClockResponseReal,
      liClockPairedEtaContiguousPartitionClockReal]
  -- `J = 2 (B ⋆ F)` near `t`
  have hJeq : ∀ u : ℝ, 0 ≤ u → liClockPairedEtaPartitionRelativeForcing N u =
      2 * volterraConv B F u := by
    intro u hu
    rw [← liClockPairedEtaPartitionRelativeForcing_volterra hN hr hrhalf hclosed hu, volterraConv]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hFdef, hBdef]
    ring
  have hJev : liClockPairedEtaPartitionRelativeForcing N =ᶠ[𝓝 t] fun u => 2 * volterraConv B F u :=
    (eventually_gt_nhds ht).mono fun u hu => hJeq u hu.le
  have hconv := hasDerivAt_volterraConv hBd hB'c hFc t
  have hJ : HasDerivAt (liClockPairedEtaPartitionRelativeForcing N)
      (2 * (B 0 * F t + volterraConv (deriv B) F t)) t :=
    (hconv.const_mul 2).congr_of_eventuallyEq hJev
  have hR := hJ.div (hBd t) (hBpos t).ne'
  have hvalue : (2 * (B 0 * F t + volterraConv (deriv B) F t) * B t -
      liClockPairedEtaPartitionRelativeForcing N t * deriv B t) / B t ^ 2 =
      2 * F t / B t + 2 / B t * ∫ s in (0 : ℝ)..t, F s * B (t - s) * (q (t - s) - q t) := by
    rw [hJeq t ht.le, hB0, one_mul]
    have hint : (∫ s in (0 : ℝ)..t, F s * B (t - s) * (q (t - s) - q t)) =
        volterraConv (deriv B) F t - volterraConv B F t * q t := by
      unfold volterraConv
      rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [hqdef, liClockPairedEtaPartitionMixedLogDerivative, ← hBdef]
        have := hBpos (t - s)
        have := hBpos t
        field_simp
      · exact (hB'c.comp (continuous_const.sub continuous_id)).mul hFc |>.intervalIntegrable _ _
      · exact ((hBs.continuous.comp (continuous_const.sub continuous_id)).mul hFc).mul_const _
          |>.intervalIntegrable _ _
    rw [hint]
    simp only [hqdef, liClockPairedEtaPartitionMixedLogDerivative, ← hBdef]
    have := hBpos t
    field_simp
    ring
  rw [hvalue] at hR
  have hR' : HasDerivAt (liClockPairedEtaPartitionRelativeForcingQuotient N)
      (2 * F t / B t + 2 / B t * ∫ s in (0 : ℝ)..t, F s * B (t - s) * (q (t - s) - q t)) t := hR
  refine ⟨hR', ?_⟩
  rw [hR'.deriv]
  have hBt := hBpos t
  have hneg : (∫ s in (0 : ℝ)..t, F s * B (t - s) * (q t - q (t - s))) =
      -∫ s in (0 : ℝ)..t, F s * B (t - s) * (q (t - s) - q t) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; funext s; ring
  rw [hneg]
  field_simp
  ring

end RHTower
