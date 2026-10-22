import GaloisForLFunctions.HTGeometry.DiskMultiplierBoundary
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex
import GaloisForLFunctions.HTGeometry.CircleSingularWitness
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# Boundary values of nonzero bounded analytic functions on the disk vanish only on a null set

This is the Privalov-type uniqueness statement for disk multipliers (bounded analytic functions on the
unit disk): if the function is not identically zero in the disk, its boundary function on the unit
circle is nonzero almost everywhere. The analytic input is an abstract no-extinction lemma: a uniformly
bounded sequence of functions on a probability space whose `log |F_n|` integrals are bounded below
cannot tend to zero on a set of positive measure. It is applied to the dilations `z ↦ g(r z)`, `r → 1`,
of the quotient `g = f / z^n` (`n` the order of vanishing of `f` at the origin, so `g(0) ≠ 0`), using
Jensen's lower bound for `log |g|` on circles.

## Main results

- `no_positive_measure_boundary_extinction_of_jensen_lower`: if `|F_n| ≤ B` a.e., `F_n` vanishes only on
  null sets, `log |F_n|` is integrable with `∫ log |F_n| ≥ L`, then `F_n` cannot converge to `0` almost
  everywhere on a set of positive measure.
- `diskMultiplierBoundary_ne_zero_ae`: a disk multiplier that is nonzero at some point of the open unit
  disk has boundary values that are nonzero for almost every point of the circle.

## Hypotheses

Unconditional. The extinction lemma takes as explicit hypotheses the uniform bound `B ≥ 1`, measurability,
null zero sets, integrability of `log |F_n|` and the uniform lower bound `L` on its integral, on a
probability space without atoms. The boundary theorem assumes only that the multiplier is not
identically zero in the disk.
-/

open MeasureTheory Filter Topology Complex Metric
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The backward shift by `n` on Hardy-space coefficient sequences: `(hardyBack n f)_k = f_(k+n)`. -/
def hardyBack (n : ℕ) (f : HardyDisk) : HardyDisk := backOp n f

@[simp] theorem hardyBack_apply (n : ℕ) (f : HardyDisk) (k : ℕ) :
    hardyBack n f k = f (k + n) := rfl

/-- Shifting the coefficient sequence forward by `n` multiplies the Hardy function by `z^n` in the
open unit disk. -/
theorem hardyFun_shiftFun (n : ℕ) (f : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun ⟨shiftFun n f, memℓp_shiftFun (lp.memℓp f) n⟩ z =
      z ^ n * hardyFun f z := by
  rw [hardyFun, hardyFun]
  have hs : Summable (fun k => shiftFun n f k * z ^ k) :=
    summable_hardyDisk_terms ⟨shiftFun n f, memℓp_shiftFun (lp.memℓp f) n⟩ hz
  rw [← hs.sum_add_tsum_nat_add n]
  have hhead : ∑ k ∈ Finset.range n, shiftFun n f k * z ^ k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [shiftFun_of_lt (Finset.mem_range.mp hk), zero_mul]
  rw [hhead, zero_add]
  calc
    ∑' k, shiftFun n f (k + n) * z ^ (k + n) =
        ∑' k, z ^ n * (f k * z ^ k) := by
          apply tsum_congr
          intro k
          rw [shiftFun_add, pow_add]
          ring
    _ = z ^ n * ∑' k, f k * z ^ k := tsum_mul_left

/-- The value of a Hardy function at the origin is its zeroth coefficient. -/
theorem hardyFun_zero (f : HardyDisk) : hardyFun f 0 = f 0 := by
  rw [hardyFun]
  rw [tsum_eq_single 0]
  · simp
  · intro b hb
    rw [zero_pow hb, mul_zero]

/-- No extinction on positive measure: on an atomless probability space, a sequence `F_n` with
`|F_n| ≤ B` (`B ≥ 1`), null zero sets, integrable `log |F_n|` and `∫ log |F_n| ≥ L` for all `n` cannot
tend to `0` almost everywhere on a measurable set of positive measure. -/
theorem no_positive_measure_boundary_extinction_of_jensen_lower
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    [NullSingletonClass μ]
    (F : ℕ → X → ℂ) (B L : ℝ) (hB : 1 ≤ B)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hFbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B)
    (hFzero : ∀ n, μ {x | F n x = 0} = 0)
    (hlogInt : ∀ n, Integrable (fun x => Real.log ‖F n x‖) μ)
    (hlower : ∀ n, L ≤ ∫ x, Real.log ‖F n x‖ ∂μ)
    {E : Set X} (hE : MeasurableSet E) (hEpos : 0 < μ.real E)
    (htend : ∀ᵐ x ∂μ.restrict E, Tendsto (fun n => F n x) atTop (nhds 0)) : False := by
  let m : ℝ := μ.real E
  have hm : 0 < m := hEpos
  let K : ℝ := (|Real.log B - L| + 2) / m
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let δ : ℝ := Real.exp (-K)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hK.le)
  let clip : ℂ → ℝ := fun y => Real.log (max δ ‖y‖)
  have hclip_cont : Continuous clip := by
    dsimp [clip]
    exact (continuous_const.max continuous_norm).log fun y =>
      (lt_of_lt_of_le hδ (le_max_left δ ‖y‖)).ne'
  have hlogδ : Real.log δ = -K := by simp [δ]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  let D : ℝ := max |Real.log δ| |Real.log B|
  have hclip_bound : ∀ n, ∀ᵐ x ∂μ, |clip (F n x)| ≤ D := by
    intro n
    filter_upwards [hFbound n] with x hx
    have hmaxpos : 0 < max δ ‖F n x‖ := lt_of_lt_of_le hδ (le_max_left _ _)
    have hmaxle : max δ ‖F n x‖ ≤ B := max_le (hδ1.trans hB) hx
    have hlo : Real.log δ ≤ clip (F n x) := by
      exact Real.log_le_log hδ (le_max_left _ _)
    have hhi : clip (F n x) ≤ Real.log B := by
      exact Real.log_le_log hmaxpos hmaxle
    exact (abs_le.mpr ⟨by
      exact le_trans (le_trans (neg_le_neg (le_max_left |Real.log δ| |Real.log B|))
        (neg_abs_le (Real.log δ))) hlo,
      le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))⟩)
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (le_max_left _ _)
  have hDint : Integrable (fun _ : X => D) (μ.restrict E) := integrable_const D
  have hclipMeas : ∀ n, AEStronglyMeasurable (fun x => clip (F n x)) μ := fun n =>
    hclip_cont.aestronglyMeasurable.comp_aemeasurable (hFmeas n).aemeasurable
  have hclipMeasE : ∀ n, AEStronglyMeasurable (fun x => clip (F n x)) (μ.restrict E) :=
    fun n => (hclipMeas n).mono_measure Measure.restrict_le_self
  have hclipBoundE : ∀ n, ∀ᵐ x ∂μ.restrict E, ‖clip (F n x)‖ ≤ D := by
    intro n
    filter_upwards [ae_mono Measure.restrict_le_self (hclip_bound n)] with x hx
    exact (show ‖clip (F n x)‖ ≤ D by
      simpa [Real.norm_eq_abs] using hx
    )
  have hclipLim : ∀ᵐ x ∂μ.restrict E,
      Tendsto (fun n => clip (F n x)) atTop (nhds (Real.log δ)) := by
    filter_upwards [htend] with x hx
    have hc := hclip_cont.tendsto 0 |>.comp hx
    simpa [Function.comp_def, clip, hδ.le] using hc
  have hintLim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : X => D) hclipMeasE hDint hclipBoundE hclipLim
  have hlimit : (∫ _ : X, Real.log δ ∂μ.restrict E) = m * Real.log δ := by
    rw [MeasureTheory.integral_const]
    simp [m, smul_eq_mul]
  have hevent : ∀ᶠ n in atTop,
      (∫ x, clip (F n x) ∂μ.restrict E) < m * Real.log δ + 1 := by
    rw [hlimit] at hintLim
    exact hintLim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := hevent.exists
  have hclipInt : Integrable (fun x => clip (F n x)) μ := by
    refine Integrable.mono' (integrable_const D) (hclipMeas n) ?_
    filter_upwards [hclip_bound n] with x hx
    simpa [Real.norm_eq_abs] using hx
  have hlog_le_clip : ∀ᵐ x ∂μ, Real.log ‖F n x‖ ≤ clip (F n x) := by
    have hne : ∀ᵐ x ∂μ, F n x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa only [not_ne_iff] using hFzero n
    filter_upwards [hne] with x hx
    apply Real.log_le_log (norm_pos_iff.mpr hx)
    exact le_max_right _ _
  have hlc : (∫ x, Real.log ‖F n x‖ ∂μ) ≤ ∫ x, clip (F n x) ∂μ :=
    MeasureTheory.integral_mono_ae (hlogInt n) hclipInt hlog_le_clip
  have hEc : MeasurableSet Eᶜ := hE.compl
  have hsplit : (∫ x, clip (F n x) ∂μ) =
      (∫ x, clip (F n x) ∂μ.restrict E) +
        ∫ x, clip (F n x) ∂μ.restrict Eᶜ := by
    rw [← MeasureTheory.integral_add_measure
      (hclipInt.mono_measure Measure.restrict_le_self)
      (hclipInt.mono_measure Measure.restrict_le_self),
      Measure.restrict_add_restrict_compl hE]
  have hcompBound : (∫ x, clip (F n x) ∂μ.restrict Eᶜ) ≤ Real.log B := by
    have hconstInt : Integrable (fun _ : X => Real.log B) (μ.restrict Eᶜ) :=
      integrable_const _
    have hclipIntEc : Integrable (fun x => clip (F n x)) (μ.restrict Eᶜ) :=
      hclipInt.mono_measure Measure.restrict_le_self
    have hle : ∀ᵐ x ∂μ.restrict Eᶜ, clip (F n x) ≤ Real.log B := by
      filter_upwards [ae_mono Measure.restrict_le_self (hFbound n)] with x hx
      have hmaxpos : 0 < max δ ‖F n x‖ := lt_of_lt_of_le hδ (le_max_left _ _)
      exact Real.log_le_log hmaxpos (max_le (hδ1.trans hB) hx)
    refine le_trans (MeasureTheory.integral_mono_ae hclipIntEc hconstInt hle) ?_
    rw [MeasureTheory.integral_const, smul_eq_mul]
    have hmass : (μ.restrict Eᶜ).real Set.univ ≤ 1 := by
      rw [Measure.real, Measure.restrict_apply_univ]
      have hmassENN : μ Eᶜ ≤ 1 := by
        calc
          μ Eᶜ ≤ μ Set.univ := measure_mono (Set.subset_univ Eᶜ)
          _ = 1 := measure_univ
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmassENN
    nlinarith
  have hKcalc : -K * m + Real.log B ≤ L - 2 := by
    dsimp [K]
    have hm0 : m ≠ 0 := hm.ne'
    have habs : Real.log B - L ≤ |Real.log B - L| := le_abs_self _
    field_simp [hm0]
    nlinarith
  have : L < L := by
    calc
      L ≤ ∫ x, Real.log ‖F n x‖ ∂μ := hlower n
      _ ≤ ∫ x, clip (F n x) ∂μ := hlc
      _ = (∫ x, clip (F n x) ∂μ.restrict E) +
          ∫ x, clip (F n x) ∂μ.restrict Eᶜ := hsplit
      _ < (m * Real.log δ + 1) + Real.log B := add_lt_add_of_lt_of_le hn hcompBound
      _ = -K * m + Real.log B + 1 := by rw [hlogδ]; ring
      _ ≤ L - 1 := by linarith
      _ < L := by linarith
  exact lt_irrefl L this

/-- A disk multiplier that is nonzero at some point of the open unit disk has boundary function nonzero
almost everywhere on the unit circle. -/
theorem diskMultiplierBoundary_ne_zero_ae
    (φ : DiskMultiplier)
    (hφ : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    ∀ᵐ z ∂circleLebesgue, diskMultiplierBoundaryFun φ z ≠ 0 := by
  let f : HardyDisk := hardyOf φ
  have hfne : f ≠ 0 := by
    intro hf0
    obtain ⟨z, hz, hφz⟩ := hφ
    have hval := hardyFun_hardyOf φ (by simpa [Metric.mem_ball, dist_zero_right] using hz)
    have hzero : hardyFun (0 : HardyDisk) z = 0 := by
      rw [hardyFun]
      simp
    apply hφz
    calc
      φ.fn z = hardyFun (hardyOf φ) z := hval.symm
      _ = hardyFun f z := rfl
      _ = hardyFun (0 : HardyDisk) z := by rw [hf0]
      _ = 0 := hzero
  have hfcoord : ∃ n, f n ≠ 0 := by
    by_contra h
    push Not at h
    apply hfne
    apply lp.ext
    funext n
    simpa using h n
  let n : ℕ := Nat.find hfcoord
  have hfn : f n ≠ 0 := Nat.find_spec hfcoord
  have hfbefore : ∀ k < n, f k = 0 := by
    intro k hk
    by_contra hfk
    have := Nat.find_min' hfcoord hfk
    omega
  let g : HardyDisk := hardyBack n f
  have hg0 : g 0 ≠ 0 := by
    simpa [g, n, Nat.zero_add] using hfn
  let sf : HardyDisk := ⟨shiftFun n g, memℓp_shiftFun (lp.memℓp g) n⟩
  have hfshift : f = sf := by
    apply lp.ext
    funext k
    change f k = shiftFun n g k
    by_cases hk : k < n
    · rw [shiftFun_of_lt hk, hfbefore k hk]
    · rw [shiftFun_of_le (Nat.le_of_not_gt hk)]
      simp only [g, hardyBack_apply]
      rw [Nat.sub_add_cancel (Nat.le_of_not_gt hk)]
  have hfactor {z : ℂ} (hz : ‖z‖ < 1) :
      φ.fn z = z ^ n * hardyFun g z := by
    rw [← hardyFun_hardyOf φ hz, show hardyOf φ = f from rfl, hfshift]
    exact hardyFun_shiftFun n g hz
  obtain ⟨ns, hns, hradial⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  have hradii : Tendsto (fun i => hardyDiskAbelRadius (ns i)) atTop (nhds 1) :=
    (tendsto_hardyDiskAbelRadius.mono_right inf_le_left).comp hns.tendsto_atTop
  have hrhalf : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ hardyDiskAbelRadius (ns i) :=
    hradii.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hrhalf)
  let idx : ℕ → ℕ := fun i => ns (i + N)
  let r : ℕ → ℝ := fun i => hardyDiskAbelRadius (idx i)
  have hr1 (i : ℕ) : r i < 1 := hardyDiskAbelRadius_lt_one _
  have hrhalf' (i : ℕ) : (1 / 2 : ℝ) ≤ r i := by
    exact hN (i + N) (by omega)
  have hr0 (i : ℕ) : 0 < r i := lt_of_lt_of_le (by norm_num) (hrhalf' i)
  let F : ℕ → Circle → ℂ := fun i z => hardyFun g ((r i : ℂ) * (z : ℂ))
  let B : ℝ := max 1 (φ.bd / (1 / 2 : ℝ) ^ n)
  have hB : 1 ≤ B := le_max_left _ _
  have hFbound : ∀ i z, ‖F i z‖ ≤ B := by
    intro i z
    have hzarg : ‖(r i : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i), Circle.norm_coe, mul_one]
      exact hr1 i
    have hfac := congrArg norm (hfactor hzarg)
    have hpowpos : 0 < (r i) ^ n := pow_pos (hr0 i) _
    have hφbd := φ.bd_le ((r i : ℂ) * (z : ℂ))
      (by simpa [Metric.mem_ball, dist_zero_right] using hzarg)
    have hnormarg : ‖(r i : ℂ) * (z : ℂ)‖ = r i := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i), Circle.norm_coe, mul_one]
    rw [norm_mul, norm_pow, hnormarg] at hfac
    have hgBound : ‖F i z‖ ≤ φ.bd / (r i) ^ n := by
      dsimp [F]
      apply (le_div_iff₀ hpowpos).2
      rw [mul_comm, ← hfac]
      exact hφbd
    have hden : (1 / 2 : ℝ) ^ n ≤ (r i) ^ n := by
      exact pow_le_pow_left₀ (by norm_num) (hrhalf' i) _
    have hφnonneg : 0 ≤ φ.bd := φ.bd_nonneg
    have hdiv : φ.bd / (r i) ^ n ≤ φ.bd / (1 / 2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left hφnonneg
        (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) hden
    exact hgBound.trans (hdiv.trans (le_max_right _ _))
  let R : ℕ → ℝ := fun i => (1 + (r i)⁻¹) / 2
  have hR1 (i : ℕ) : 1 < R i := by
    have hinvpos : 0 < (r i)⁻¹ := inv_pos.mpr (hr0 i)
    have hmul : r i * (r i)⁻¹ = 1 := mul_inv_cancel₀ (hr0 i).ne'
    have hgap := mul_pos (sub_pos.mpr (hr1 i)) hinvpos
    have hinv : 1 < (r i)⁻¹ := by nlinarith
    dsimp [R]
    linarith
  have hRinv (i : ℕ) : R i < (r i)⁻¹ := by
    have hinvpos : 0 < (r i)⁻¹ := inv_pos.mpr (hr0 i)
    have hmul : r i * (r i)⁻¹ = 1 := mul_inv_cancel₀ (hr0 i).ne'
    have hgap := mul_pos (sub_pos.mpr (hr1 i)) hinvpos
    have hinv : 1 < (r i)⁻¹ := by nlinarith
    dsimp [R]
    linarith
  have hrR (i : ℕ) : r i * R i < 1 := by
    calc
      r i * R i < r i * (r i)⁻¹ := mul_lt_mul_of_pos_left (hRinv i) (hr0 i)
      _ = 1 := mul_inv_cancel₀ (hr0 i).ne'
  let Fi : ℕ → ℂ → ℂ := fun i z => hardyFun g ((r i : ℂ) * z)
  have hFi (i : ℕ) : AnalyticOnNhd ℂ (Fi i) (Metric.ball 0 (R i)) := by
    intro z hz
    have hznorm : ‖z‖ < R i := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have harg : ‖(r i : ℂ) * z‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i)]
      exact (mul_lt_mul_of_pos_left hznorm (hr0 i)).trans (hrR i)
    have hgAn : AnalyticAt ℂ (hardyFun g) ((r i : ℂ) * z) :=
      (hasFPowerSeriesOnBall_hardyFun g).analyticAt_of_mem (by
        rw [eball_one_eq, Metric.mem_ball, dist_zero_right]
        exact harg)
    have hlin : AnalyticAt ℂ (fun w : ℂ => (r i : ℂ) * w) z :=
      analyticAt_const.mul analyticAt_id
    exact hgAn.comp hlin
  have hFi0 (i : ℕ) : Fi i 0 ≠ 0 := by
    simpa [Fi, hardyFun_zero] using hg0
  have hFmeas : ∀ i, AEStronglyMeasurable (F i) circleLebesgue := by
    intro i
    have hcont : Continuous (F i) := by
      change Continuous (fun z : Circle => Fi i (z : ℂ))
      exact (hFi i).continuousOn.comp_continuous (by fun_prop) fun z => by
        rw [Metric.mem_ball, dist_zero_right, Circle.norm_coe]
        exact hR1 i
    exact hcont.aestronglyMeasurable
  have hFzero : ∀ i, circleLebesgue {z | F i z = 0} = 0 := by
    intro i
    have hcountC : {w ∈ Metric.ball (0 : ℂ) (R i) | Fi i w = 0}.Countable :=
      Bottcher.analyticOnNhd_zeros_countable (hFi i) isPreconnected_ball
        (show (0 : ℂ) ∈ Metric.ball 0 (R i) by
          rw [Metric.mem_ball, dist_self]
          linarith [hR1 i]) (hFi0 i)
    have hcount : {z : Circle | F i z = 0}.Countable := by
      apply (hcountC.preimage (f := fun z : Circle => (z : ℂ)) Subtype.coe_injective).mono
      intro z hz
      exact ⟨by
        rw [Metric.mem_ball, dist_zero_right, Circle.norm_coe]
        exact hR1 i, hz⟩
    exact hcount.measure_zero circleLebesgue
  have hFiClosed (i : ℕ) :
      AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 (1 : ℝ)) :=
    (hFi i).mono fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]
      have hzle : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      exact hzle.trans_lt (hR1 i)
  have hFiMeas (i : ℕ) : Measurable (Fi i) := by
    dsimp [Fi, hardyFun]
    apply Measurable.tsum
    intro k
    fun_prop
  have hlogInt : ∀ i, Integrable (fun z => Real.log ‖F i z‖) circleLebesgue := by
    intro i
    refine integrable_circleLebesgue_of_intervalIntegrable
      (fun w => Real.log ‖Fi i w‖)
      (Real.measurable_log.comp (hFiMeas i).norm) ?_
    have ha : AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 |(1 : ℝ)|) := by
      simpa using hFiClosed i
    exact (ha.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hlower : ∀ i, Real.log ‖g 0‖ ≤
      ∫ z, Real.log ‖F i z‖ ∂circleLebesgue := by
    intro i
    have ha : AnalyticOnNhd ℂ (Fi i) (Metric.closedBall 0 |(1 : ℝ)|) := by
      simpa using hFiClosed i
    have hj := log_norm_center_le_circleAverage_log_norm (Fi i) ha (hFi0 i)
    have hmeas : AEStronglyMeasurable
        (fun z : Circle => Real.log ‖Fi i (z : ℂ)‖) circleLebesgue :=
      (hlogInt i).aestronglyMeasurable
    rw [← integral_circleLebesgue_eq_circleAverage
      (fun w => Real.log ‖Fi i w‖) hmeas] at hj
    simpa [F, Fi, hardyFun_zero] using hj
  let E : Set Circle := {z | diskMultiplierBoundaryMeasurableRep φ z = 0}
  have hE : MeasurableSet E := by
    change MeasurableSet (diskMultiplierBoundaryMeasurableRep φ ⁻¹' ({0} : Set ℂ))
    exact measurable_diskMultiplierBoundaryMeasurableRep φ (measurableSet_singleton 0)
  have hEzero : circleLebesgue E = 0 := by
    by_contra hEne
    have hEpos : 0 < circleLebesgue.real E := by
      rw [Measure.real]
      exact ENNReal.toReal_pos hEne (measure_ne_top circleLebesgue E)
    have hrtend : Tendsto r atTop (nhds 1) := by
      have hadd : StrictMono (fun i : ℕ => i + N) := by
        intro a b hab
        exact Nat.add_lt_add_right hab N
      exact hradii.comp hadd.tendsto_atTop
    have htend : ∀ᵐ z ∂circleLebesgue.restrict E,
        Tendsto (fun i => F i z) atTop (nhds 0) := by
      rw [MeasureTheory.ae_restrict_iff' hE]
      filter_upwards [hradial, diskMultiplierBoundaryMeasurableRep_ae φ] with z hzrad hzrep
      intro hzE
      have hboundary : diskMultiplierBoundaryFun φ z = 0 := by
        rw [← hzrep]
        exact hzE
      have hzrad0 : Tendsto
          (fun i => diskMultiplierRadialBoundaryFun (idx i) φ z) atTop (nhds 0) := by
        have hadd : StrictMono (fun i : ℕ => i + N) := by
          intro a b hab
          exact Nat.add_lt_add_right hab N
        have hc := hzrad.comp hadd.tendsto_atTop
        simpa [Function.comp_def, idx, hboundary] using hc
      have hden : Tendsto
          (fun i => (((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) atTop
          (nhds ((z : ℂ) ^ n)) := by
        have hrC : Tendsto (fun i => ((r i : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 1).comp hrtend
        simpa using (hrC.mul_const (z : ℂ)).pow n
      have hzpow : (z : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by
        rw [← norm_pos_iff, Circle.norm_coe]
        norm_num)
      have hdiv := hzrad0.div hden hzpow
      have hdiv0 : Tendsto
          ((fun i => diskMultiplierRadialBoundaryFun (idx i) φ z) /
            fun i => ((((r i : ℝ) : ℂ) * (z : ℂ)) ^ n)) atTop (nhds 0) := by
        simpa using hdiv
      apply hdiv0.congr'
      filter_upwards with i
      have harg : ‖((r i : ℝ) : ℂ) * (z : ℂ)‖ < 1 := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hr0 i), Circle.norm_coe, mul_one]
        exact hr1 i
      have hfac := hfactor harg
      change diskMultiplierRadialBoundaryFun (idx i) φ z /
        ((((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) = F i z
      rw [diskMultiplierRadialBoundaryFun]
      have hdenne : ((((r i : ℝ) : ℂ) * (z : ℂ)) ^ n) ≠ 0 := pow_ne_zero _ <|
        mul_ne_zero (ofReal_ne_zero.mpr (hr0 i).ne') (by
          rw [← norm_pos_iff, Circle.norm_coe]
          norm_num)
      apply (div_eq_iff hdenne).2
      simpa [F, mul_comm] using hfac
    exact no_positive_measure_boundary_extinction_of_jensen_lower
      F B (Real.log ‖g 0‖) hB hFmeas
      (fun i => Eventually.of_forall (hFbound i)) hFzero hlogInt hlower
      hE hEpos htend
  have hrepne : ∀ᵐ z ∂circleLebesgue,
      diskMultiplierBoundaryMeasurableRep φ z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_ne_iff, E] using hEzero
  filter_upwards [hrepne, diskMultiplierBoundaryMeasurableRep_ae φ] with z hz hrep
  rwa [← hrep]

end
end GaloisForLFunctions.HTGeometry
