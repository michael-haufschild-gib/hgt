import GaloisForLFunctions.InfiniteRankPurityTheory.AModeAccessibleFromInfinityIsEliminated
import GaloisForLFunctions.InfiniteRankPurityTheory.KroneckerOverTheIntegersNeedsNoDistinctModes
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# On the flow the weight filtration needs no chain condition

At the integers the growth form of the weight filtration needs the weights to have no ascending
chain; along one tower it needs an attained top or an accessible mode. These hypotheses come from
sampling the scaling flow at discrete levels. This module shows that on the whole flow none is
needed, for every module whose modes are locally finite.

A module `(b, ρ)` with `Σ ‖b_i‖ < ∞` and weights bounded above has the trace
`t(x) = Σ_i b_i x^{ρ_i}` for real `x ≥ 1`. Its Mellin transform `∫_1^∞ t(x) x^{−w−1} dx`
(`flowMellin`) is the resolvent `Σ_i b_i / (w − ρ_i)` right of all weights
(`flowMellin_eq_towerResolvent`), and a bound `‖t(x)‖ ≤ C x^s` on the flow continues it to
`Re w > s` (`analyticAt_flowMellin`).

**Theorem** (`mergedWeight_eq_zero_of_flow_bound`, `flow_bound_iff`). Let only finitely many modes
lie in every disc. Then `‖t(x)‖ ≤ C x^s` for all `x ≥ 1` exactly when no weight is carried at a mode
of weight `> s`.

**Proof.** A locally finite set of modes is closed and discrete, so it has no walls: from a mode
`ρ_j` a short vertical step followed by a horizontal segment at a height that avoids the finitely
many modes nearby reaches `Re w > A` without meeting a mode. Along this path the resolvent continues
past `ρ_j`, so the weight at `ρ_j` vanishes if `Re ρ_j > s`.

Local finiteness cannot be dropped: the Wolff module has bounded modes, trace `1` on the whole flow
and weight at `5/4` (`frobTrace_wolff`). For the zero motive of `ζ` with its lag weights the theorem
reads: the trace is `O(x^s)` on the flow exactly when every zero has real part `≤ s`
(`zeroMotive_flow_bound_iff`).
-/

open Filter Topology Complex Set MeasureTheory

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-! ### The trace on the flow and its Mellin transform -/

/-- The trace along the flow, cut off below the first Frobenius. -/
noncomputable def flowTrace (b ρ : ι → ℂ) : ℝ → ℂ := (Ici (1 : ℝ)).indicator (frobTrace b ρ)

/-- The Mellin transform of the trace: `∫_1^∞ t(x) x^{−w−1} dx`. -/
noncomputable def flowMellin (b ρ : ι → ℂ) (w : ℂ) : ℂ := mellin (flowTrace b ρ) (-w)

/-- The trace is continuous on `x ≥ 1`. -/
theorem continuousOn_frobTrace {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) : ContinuousOn (frobTrace b ρ) (Ici 1) := by
  intro x₀ hx₀
  have hx₀' : (1 : ℝ) ≤ x₀ := hx₀
  have hcomp : ContinuousOn (fun x : ℝ => ∑' i, b i * (x : ℂ) ^ ρ i) (Icc 1 (x₀ + 1)) := by
    refine continuousOn_tsum (u := fun i => ‖b i‖ * (x₀ + 1) ^ |A|) (fun i x hx => ?_)
      (hb.mul_right _) fun i x hx => ?_
    · have hx0 : x ≠ 0 := by
        have := hx.1
        intro h
        linarith
      exact ((Complex.continuousAt_ofReal_cpow_const x (ρ i) (Or.inr hx0)).const_mul
        (b i)).continuousWithinAt
    · have h1 := norm_frobTerm_le (b := b) hA hx.1 i
      have h2 : x ^ A ≤ (x₀ + 1) ^ |A| :=
        (Real.rpow_le_rpow_of_exponent_le hx.1 (le_abs_self A)).trans
          (Real.rpow_le_rpow (by linarith [hx.1]) hx.2 (abs_nonneg A))
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hmem : Icc 1 (x₀ + 1) ∈ 𝓝[Ici 1] x₀ := by
    rw [← Ici_inter_Iic]
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (lt_add_one x₀)))
  exact (hcomp x₀ ⟨hx₀', by linarith⟩).mono_of_mem_nhdsWithin hmem

theorem locallyIntegrableOn_flowTrace {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) : LocallyIntegrableOn (flowTrace b ρ) (Ioi 0) := by
  intro x _
  refine ⟨Iic (x + 1), mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (lt_add_one x)), ?_⟩
  have hint : IntegrableOn (frobTrace b ρ) (Icc 1 (x + 1)) :=
    ((continuousOn_frobTrace hb hA).mono Icc_subset_Ici_self).integrableOn_Icc
  rw [flowTrace, IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ici, Ici_inter_Iic]
  exact hint

theorem flowTrace_isBigO_atTop {b ρ : ι → ℂ} {C s : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → ‖frobTrace b ρ x‖ ≤ C * x ^ s) :
    flowTrace b ρ =O[atTop] fun x : ℝ => x ^ (-(-s)) := by
  refine Asymptotics.IsBigO.of_bound |C| ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [flowTrace, indicator_of_mem (show x ∈ Ici (1 : ℝ) from hx), neg_neg,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)]
  exact (hbound x hx).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0 _))

theorem flowTrace_isBigO_zero (b ρ : ι → ℂ) (β : ℝ) :
    flowTrace b ρ =O[𝓝[>] 0] fun x : ℝ => x ^ (-β) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  have hnot : x ∉ Ici (1 : ℝ) := fun h => absurd hx.2 (not_lt.mpr h)
  rw [flowTrace, indicator_of_notMem hnot, norm_zero]
  positivity

/-- **A bound on the flow continues the Mellin transform to `Re w > s`.** -/
theorem analyticAt_flowMellin {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) {C s : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → ‖frobTrace b ρ x‖ ≤ C * x ^ s) {w : ℂ} (hw : s < w.re) :
    AnalyticAt ℂ (flowMellin b ρ) w := by
  have hdiff : ∀ u : ℂ, s < u.re → DifferentiableAt ℂ (flowMellin b ρ) u := by
    intro u hu
    have h := mellin_differentiableAt_of_isBigO_rpow (a := -s) (b := (-u).re - 1) (s := -u)
      (locallyIntegrableOn_flowTrace hb hA) (flowTrace_isBigO_atTop hbound)
      (by simpa using hu) (flowTrace_isBigO_zero b ρ _) (by linarith)
    exact h.comp u differentiableAt_id.neg
  have hopen : IsOpen {u : ℂ | s < u.re} := isOpen_lt continuous_const Complex.continuous_re
  have hon : DifferentiableOn ℂ (flowMellin b ρ) {u : ℂ | s < u.re} := fun u hu =>
    (hdiff u hu).differentiableWithinAt
  exact hon.analyticAt (hopen.mem_nhds hw)

/-- **Right of all weights the Mellin transform is the resolvent.** -/
theorem flowMellin_eq_towerResolvent [Countable ι] {b ρ : ι → ℂ}
    (hb : Summable fun i => ‖b i‖) {A : ℝ} (hA : ∀ i, (ρ i).re ≤ A) {w : ℂ} (hw : A < w.re) :
    flowMellin b ρ w = towerResolvent b ρ w := by
  have hre : ∀ i, (ρ i - w - 1).re < -1 := fun i => by
    simp only [sub_re, one_re]
    linarith [hA i]
  -- the transform as an integral over `x > 1` of the series
  have hstep : flowMellin b ρ w =
      ∫ x in Ioi (1 : ℝ), ∑' i, b i * (x : ℂ) ^ (ρ i - w - 1) := by
    rw [flowMellin, mellin]
    have hind : ∀ x : ℝ, (x : ℂ) ^ (-w - 1) • flowTrace b ρ x =
        (Ici (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (-w - 1) * frobTrace b ρ x) x := by
      intro x
      by_cases hx : x ∈ Ici (1 : ℝ)
      · rw [flowTrace, indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul]
      · rw [flowTrace, indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    have hinter : Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 :=
      inter_eq_right.mpr fun x hx =>
        Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ x from hx))
    simp_rw [hind]
    rw [setIntegral_indicator measurableSet_Ici, hinter, integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one hx).ne'
    show (x : ℂ) ^ (-w - 1) * frobTrace b ρ x = ∑' i, b i * (x : ℂ) ^ (ρ i - w - 1)
    rw [frobTrace, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [show ρ i - w - 1 = (-w - 1) + ρ i by ring, Complex.cpow_add _ _ hx0]
    ring
  -- the series may be integrated term by term
  have hFint : ∀ i, Integrable (fun x : ℝ => b i * (x : ℂ) ^ (ρ i - w - 1))
      (volume.restrict (Ioi 1)) := fun i =>
    (integrableOn_Ioi_cpow_of_lt (hre i) one_pos).const_mul (b i)
  have hnormint : ∀ i, ∫ x in Ioi (1 : ℝ), ‖b i * (x : ℂ) ^ (ρ i - w - 1)‖ =
      ‖b i‖ / (w.re - (ρ i).re) := by
    intro i
    have h1 : ∫ x in Ioi (1 : ℝ), ‖b i * (x : ℂ) ^ (ρ i - w - 1)‖ =
        ∫ x in Ioi (1 : ℝ), ‖b i‖ * x ^ (ρ i - w - 1).re := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      show ‖b i * (x : ℂ) ^ (ρ i - w - 1)‖ = ‖b i‖ * x ^ (ρ i - w - 1).re
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
    have hne : (ρ i - w - 1).re + 1 ≠ 0 := by
      have := hre i
      intro h
      linarith
    have hval : (ρ i - w - 1).re + 1 = -(w.re - (ρ i).re) := by
      simp only [sub_re, one_re]
      ring
    rw [h1, integral_const_mul, integral_Ioi_rpow_of_lt (hre i) one_pos, Real.one_rpow, hval,
      neg_div_neg_eq, mul_one_div]
  have hsumnorm : Summable fun i => ∫ x in Ioi (1 : ℝ), ‖b i * (x : ℂ) ^ (ρ i - w - 1)‖ := by
    simp_rw [hnormint]
    refine Summable.of_nonneg_of_le (fun i => div_nonneg (norm_nonneg _) (by linarith [hA i]))
      (fun i => ?_) (hb.div_const (w.re - A))
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith [hA i])
  rw [hstep, ← integral_tsum_of_summable_integral_norm hFint hsumnorm, towerResolvent]
  refine tsum_congr fun i => ?_
  have hval : ρ i - w - 1 + 1 = -(w - ρ i) := by ring
  rw [integral_const_mul, integral_Ioi_cpow_of_lt (hre i) one_pos, Complex.ofReal_one,
    Complex.one_cpow, hval, neg_div_neg_eq, mul_one_div]

/-! ### Locally finite modes have no walls -/

theorem countable_of_locallyFinite {ρ : ι → ℂ} (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    Countable ι := by
  have hcover : (Set.univ : Set ι) = ⋃ n : ℕ, {i | ‖ρ i‖ ≤ n} := by
    ext i
    simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
    exact exists_nat_ge ‖ρ i‖
  have hcount : (Set.univ : Set ι).Countable := by
    rw [hcover]
    exact countable_iUnion fun n => (hfin n).countable
  exact countable_univ_iff.mp hcount

/-- A locally finite set of modes is closed. -/
theorem notMem_closure_range_of_locallyFinite {ρ : ι → ℂ}
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) {w : ℂ} (hw : w ∉ range ρ) :
    w ∉ closure (range ρ) := by
  intro hcl
  have hfinite : (Metric.ball w 1 ∩ range ρ).Finite := by
    refine ((hfin (‖w‖ + 1)).image ρ).subset ?_
    rintro _ ⟨hi, i, rfl⟩
    refine ⟨i, ?_, rfl⟩
    have h1 : ‖ρ i - w‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hi
    have h2 := norm_sub_norm_le (ρ i) w
    show ‖ρ i‖ ≤ ‖w‖ + 1
    linarith
  have h1 : w ∈ closure (Metric.ball w 1 ∩ range ρ) :=
    Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self one_pos, hcl⟩
  rw [hfinite.isClosed.closure_eq] at h1
  exact hw h1.2

/-- Every mode of a locally finite module is isolated. -/
theorem exists_isolation_of_locallyFinite {ρ : ι → ℂ}
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) (j : ι) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, ρ i ≠ ρ j → δ ≤ ‖ρ i - ρ j‖ := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Finset ℝ, D = insert 1
      (((hfin (‖ρ j‖ + 1)).toFinset.filter fun i => ρ i ≠ ρ j).image fun i => ‖ρ i - ρ j‖) :=
    ⟨_, rfl⟩
  have hDne : D.Nonempty := by
    rw [hD]
    exact Finset.insert_nonempty _ _
  have h1D : (1 : ℝ) ∈ D := by
    rw [hD]
    exact Finset.mem_insert_self _ _
  refine ⟨D.min' hDne, ?_, Finset.min'_le _ _ h1D, fun i hi => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro x hx
    rw [hD] at hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact one_pos
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hi).2)
  · by_cases hF : ‖ρ i‖ ≤ ‖ρ j‖ + 1
    · refine Finset.min'_le _ _ ?_
      rw [hD]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨(hfin _).mem_toFinset.mpr hF, hi⟩, rfl⟩)
    · have h1 : 1 < ‖ρ i - ρ j‖ := by
        have := norm_sub_norm_le (ρ i) (ρ j)
        linarith [not_le.mp hF]
      exact (Finset.min'_le _ _ h1D).trans h1.le

/-- The path from a mode: up by `ε`, then right by `L`. -/
noncomputable def flowPath (ρj : ℂ) (ε L : ℝ) (t : ℝ) : ℂ :=
  ρj + Complex.I * ((ε * min (2 * t) 1 : ℝ) : ℂ) + ((max (2 * t - 1) 0 * L : ℝ) : ℂ)

theorem continuous_flowPath (ρj : ℂ) (ε L : ℝ) : Continuous (flowPath ρj ε L) := by
  have h1 : Continuous fun t : ℝ => ε * min (2 * t) 1 :=
    continuous_const.mul ((continuous_const.mul continuous_id).min continuous_const)
  have h2 : Continuous fun t : ℝ => max (2 * t - 1) 0 * L :=
    (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).mul
      continuous_const
  exact (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp h1))).add
    (Complex.continuous_ofReal.comp h2)

theorem flowPath_zero (ρj : ℂ) (ε L : ℝ) : flowPath ρj ε L 0 = ρj := by
  simp [flowPath]

theorem flowPath_re (ρj : ℂ) (ε L t : ℝ) :
    (flowPath ρj ε L t).re = ρj.re + max (2 * t - 1) 0 * L := by
  simp [flowPath]

theorem flowPath_im (ρj : ℂ) (ε L t : ℝ) :
    (flowPath ρj ε L t).im = ρj.im + ε * min (2 * t) 1 := by
  simp [flowPath]

/-! ### The weight filtration on the flow -/

/-- **On the flow the growth of the trace bounds the weights of a locally finite module.** If only
finitely many modes lie in every disc and `‖t(x)‖ ≤ C x^s` for all `x ≥ 1`, no weight is carried at
a mode of weight `> s`. -/
theorem mergedWeight_eq_zero_of_flow_bound {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖)
    {A : ℝ} (hA : ∀ i, (ρ i).re ≤ A) (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) {C s : ℝ}
    (hbound : ∀ x : ℝ, 1 ≤ x → ‖frobTrace b ρ x‖ ≤ C * x ^ s) {j : ι} (hj : s < (ρ j).re) :
    (∑' i, if ρ i = ρ j then b i else 0) = 0 := by
  classical
  haveI := countable_of_locallyFinite hfin
  obtain ⟨δ, hδ, hδ1, hiso⟩ := exists_isolation_of_locallyFinite hfin j
  -- a height avoiding the modes near the horizontal part of the path
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |(ρ j).re| + |A + 1| + |(ρ j).im| + 1 := ⟨_, rfl⟩
  obtain ⟨ε, hεmem, hεbad⟩ := (Ioo_infinite hδ).exists_notMem_finset
    ((hfin B).toFinset.image fun i => (ρ i).im - (ρ j).im)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = A + 1 - (ρ j).re := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    rw [hL]
    linarith [hA j]
  -- the path avoids the modes
  have hfree : ∀ t ∈ Ioc (0 : ℝ) 1, flowPath (ρ j) ε L t ∉ range ρ := by
    rintro t ht ⟨i, hi⟩
    have hre := congrArg Complex.re hi
    have him := congrArg Complex.im hi
    rw [flowPath_re] at hre
    rw [flowPath_im] at him
    rcases le_or_gt (2 * t) 1 with h2 | h2
    · -- on the vertical part the path stays within `ε < δ` of `ρ_j`
      rw [max_eq_right (by linarith), zero_mul, add_zero] at hre
      rw [min_eq_left h2] at him
      have hne : ρ i ≠ ρ j := fun h => by
        rw [h] at him
        have : ε * (2 * t) = 0 := by linarith
        have hpos : 0 < ε * (2 * t) := mul_pos hεmem.1 (by linarith [ht.1])
        linarith
      have hnorm : ‖ρ i - ρ j‖ ≤ ε := by
        have hdiff : ρ i - ρ j = Complex.I * ((ε * (2 * t) : ℝ) : ℂ) := by
          apply Complex.ext
          · simp [hre]
          · simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul,
              zero_add]
            linarith
        rw [hdiff, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hεmem.1.le (by linarith [ht.1]))]
        nlinarith [hεmem.1, ht.1]
      linarith [hiso i hne, hεmem.2]
    · -- on the horizontal part the height `Im ρ_j + ε` carries no mode
      rw [max_eq_left (by linarith)] at hre
      rw [min_eq_right h2.le, mul_one] at him
      apply hεbad
      refine Finset.mem_image.mpr ⟨i, (hfin B).mem_toFinset.mpr ?_, by linarith⟩
      show ‖ρ i‖ ≤ B
      have h1 : |(ρ i).re| ≤ |(ρ j).re| + |A + 1| := by
        have hlow : (ρ j).re ≤ (ρ i).re := by
          have : 0 ≤ (2 * t - 1) * L := mul_nonneg (by linarith) hL0.le
          linarith
        have hupp : (ρ i).re ≤ A + 1 := by
          have h3 : (2 * t - 1) * L ≤ 1 * L :=
            mul_le_mul_of_nonneg_right (by linarith [ht.2]) hL0.le
          rw [hre]
          linarith [hL]
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (ρ j).re, abs_nonneg (A + 1)]
        · linarith [le_abs_self (A + 1), abs_nonneg (ρ j).re]
      have h2' : |(ρ i).im| ≤ |(ρ j).im| + 1 := by
        rw [him]
        calc |(ρ j).im + ε| ≤ |(ρ j).im| + |ε| := abs_add_le _ _
          _ ≤ |(ρ j).im| + 1 := by
              rw [abs_of_pos hεmem.1]
              linarith [hεmem.2]
      rw [hB]
      linarith [Complex.norm_le_abs_re_add_abs_im (ρ i)]
  have hreγ : ∀ t : ℝ, s < (flowPath (ρ j) ε L t).re := by
    intro t
    rw [flowPath_re]
    have : 0 ≤ max (2 * t - 1) 0 * L := mul_nonneg (le_max_right _ _) hL0.le
    linarith
  have hend : towerResolvent b ρ =ᶠ[𝓝 (flowPath (ρ j) ε L 1)] flowMellin b ρ := by
    have hopen : IsOpen {w : ℂ | A < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : flowPath (ρ j) ε L 1 ∈ {w : ℂ | A < w.re} := by
      show A < (flowPath (ρ j) ε L 1).re
      rw [flowPath_re, hL]
      norm_num
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact (flowMellin_eq_towerResolvent hb hA hw).symm
  exact merged_eq_zero_of_continuation hb (analyticAt_flowMellin hb hA hbound hj).continuousAt
    hδ hiso (continuous_flowPath _ _ _).continuousOn (flowPath_zero _ _ _)
    (fun t ht => notMem_closure_range_of_locallyFinite hfin (hfree t ht))
    (fun t _ => analyticAt_flowMellin hb hA hbound (hreγ t)) hend

/-- **On the flow the weight filtration of a locally finite module is its growth filtration.**
`‖t(x)‖ ≤ C x^s` for all `x ≥ 1` exactly when no weight is carried at a mode of weight `> s`. No
condition on the weights is needed. -/
theorem flow_bound_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) (s : ℝ) :
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖frobTrace b ρ x‖ ≤ C * x ^ s) ↔
      ∀ j, s < (ρ j).re → (∑' i, if ρ i = ρ j then b i else 0) = 0 := by
  constructor
  · rintro ⟨C, hC⟩ j hj
    exact mergedWeight_eq_zero_of_flow_bound hb hA hfin hC hj
  · intro hzero
    refine ⟨∑' k : Set.range ρ, ‖mergedWeight b ρ k‖, fun x hx => ?_⟩
    rw [← frobTrace_merged hb hA hx]
    refine norm_frobTrace_le_of_re_le (summable_norm_mergedWeight hb) (fun k hk => ?_) hx
    obtain ⟨j, hjk⟩ := k.2
    by_contra hlt
    apply hk
    show mergedWeight b ρ k = 0
    rw [mergedWeight, ← hjk]
    exact hzero j (by rw [hjk]; exact not_le.mp hlt)

/-! ### The zero motive -/

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown in
open GaloisForLFunctions.InfiniteRankWeilTheory renaming lagWeight → lagW,
  summable_norm_lagWeight → summable_norm_lagW, re_lagWeight_pos → re_lagW_pos in
/-- **The weight filtration of the zero motive on the flow.** With the lag weights `1/(ρ(1−ρ))`
the trace `Σ_ρ x^ρ/(ρ(1−ρ))` is `O(x^s)` on `x ≥ 1` exactly when every zero has real part `≤ s`.
The zeros are locally finite and their lag weights have positive real part; nothing else about them
is used. -/
theorem zeroMotive_flow_bound_iff (s : ℝ) :
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖frobTrace lagW (fun q : XiZeroCopy => (q.1 : ℂ)) x‖ ≤ C * x ^ s) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ s := by
  have hA : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 := fun q =>
    (re_lt_one_of_xi_eq_zero (xi_xiZeroCopy_eq_zero q)).le
  have hfin : ∀ B : ℝ, {q : XiZeroCopy | ‖(q.1 : ℂ)‖ ≤ B}.Finite := by
    intro B
    refine (finite_xiZeroCopy_band 0 (abs_nonneg B)).subset fun q hq => ?_
    have hq' : ‖(q.1 : ℂ)‖ ≤ B := hq
    show |(q.1 : ℂ).im - 0| ≤ |B|
    rw [sub_zero]
    exact (Complex.abs_im_le_norm _).trans (hq'.trans (le_abs_self B))
  rw [flow_bound_iff summable_norm_lagW hA hfin s]
  constructor
  · intro h q
    by_contra hlt
    exact merged_ne_zero_of_re_pos summable_norm_lagW (fun q => (re_lagW_pos q).le)
      (re_lagW_pos q) (h q (not_le.mp hlt))
  · intro h q hq
    exact absurd (h q) (not_le.mpr hq)

end GaloisForLFunctions.InfiniteRankPurityTheory
