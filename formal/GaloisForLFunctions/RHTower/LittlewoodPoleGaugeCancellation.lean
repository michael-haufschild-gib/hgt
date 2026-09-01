import GaloisForLFunctions.RHTower.LevinsonLittlewoodZeroCount

/-!
# Exact cancellation of the pole-clearing gauge in Littlewood's boundary

The entire Levinson detector is `G♯ = (s−1)²·G` with `G = ζ + λζ′` meromorphic at `s = 1`.  Only
the entire form admits Littlewood's identity, but estimating the gauge `(s−1)²` edge by edge would
introduce a spurious `Θ(L log T)` height growth in the budget — far larger than the whole Levinson
margin.

The gauge in fact contributes **exactly zero**.  Littlewood's boundary functional is additive over
products, and the identity applied to `u(s) = (s−1)²` on a rectangle that misses `s = 1` gives
`weightedLittlewoodBoundary u = 2π · 0 = 0`.  So the whole argument may be run on the boundary data
of the *meromorphic* detector, which has no height growth at all.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **The raw Littlewood zero-count inequality.**  The weighted zero mass to the right of `σ` is
bounded by the boundary functional, with no estimate yet applied to any edge. -/
theorem exists_entire_zeroCount_le_boundary
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∃ z : ℂ, f z ≠ 0)
    {c d σ T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hrightne : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      2 * Real.pi * ((σ - c) *
          (∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt f w).toNat : ℝ)))
        ≤ weightedLittlewoodBoundary f c d T₁ T₂ := by
  classical
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hf hne hcd hT hbot htop hrightne
  refine ⟨Z, hZ, ?_⟩
  have hZre : ∀ w ∈ Z, c ≤ w.re ∧ w.re ≤ d := by
    intro w hw
    have hmem := ((hZ w).mp hw).1
    have hre := (Complex.mem_reProdIm.mp hmem).1
    rw [uIcc_of_le hcd.le] at hre
    exact ⟨hre.1, hre.2⟩
  have hmass : (σ - c) *
      (∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt f w).toNat : ℝ))
      ≤ ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro w hw
      have hσw : σ ≤ w.re := (Finset.mem_filter.mp hw).2
      have hord : (0 : ℝ) ≤ ((analyticOrderAt f w).toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    · intro w hwZ _
      have hord : (0 : ℝ) ≤ ((analyticOrderAt f w).toNat : ℝ) := Nat.cast_nonneg _
      have hge := (hZre w hwZ).1
      have hnn : (0 : ℝ) ≤ w.re - c := by linarith
      positivity
  have hkey := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  rw [hident] at hkey
  exact hkey

/-- The pole-clearing gauge has no zero inside a rectangle that misses `s = 1`, so its Littlewood
boundary functional vanishes identically. -/
theorem weightedLittlewoodBoundary_poleGauge_eq_zero
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hone : (1 : ℂ) ∉ (uIcc c d ×ℂ uIcc T₁ T₂)) :
    weightedLittlewoodBoundary (fun z : ℂ => (z - 1) ^ 2) c d T₁ T₂ = 0 := by
  classical
  have hana : AnalyticOnNhd ℂ (fun z : ℂ => (z - 1) ^ 2) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr (by fun_prop)
  have hnezero : ∃ z : ℂ, (z - 1) ^ 2 ≠ 0 := ⟨0, by norm_num⟩
  have hzero_iff : ∀ z : ℂ, (z - 1) ^ 2 = 0 ↔ z = 1 := by
    intro z
    constructor
    · intro h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linear_combination this
    · intro h; rw [h]; ring
  have hedge : ∀ z : ℂ, z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) → (z - 1) ^ 2 ≠ 0 := by
    intro z hz h0
    exact hone ((hzero_iff z).mp h0 ▸ hz)
  have hmembot : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₁ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have : ((x : ℂ) + (T₁ : ℂ) * I).re = x := by simp
      rw [this]; exact hx
    · have : ((x : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
      rw [this]; exact left_mem_uIcc
  have hmemtop : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₂ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have : ((x : ℂ) + (T₂ : ℂ) * I).re = x := by simp
      rw [this]; exact hx
    · have : ((x : ℂ) + (T₂ : ℂ) * I).im = T₂ := by simp
      rw [this]; exact right_mem_uIcc
  have hmemright : ∀ t ∈ uIcc T₁ T₂, ((d : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have : ((d : ℂ) + (t : ℂ) * I).re = d := by simp
      rw [this]; exact right_mem_uIcc
    · have : ((d : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [this]; exact ht
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hana hnezero hcd hT
      (fun x hx => hedge _ (hmembot x hx)) (fun x hx => hedge _ (hmemtop x hx))
      (fun t ht => hedge _ (hmemright t ht))
  have hZempty : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    exact hedge w hwmem hwzero
  rw [hZempty] at hident
  simpa using hident.symm


/-! ## Additivity of the boundary functional over the pole gauge -/

theorem intervalIntegrable_log_norm_vertical_of_analyticAt {f : ℂ → ℂ} {a T₁ T₂ : ℝ}
    (hf : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ f ((a : ℂ) + (t : ℂ) * I)) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖f ((a : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t ht
  have hpath : AnalyticAt ℝ (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I)
    (hf t ht).restrictScalars hpath |>.meromorphicAt

theorem continuousOn_re_logDeriv_vertical {f : ℂ → ℂ} {a T₁ T₂ : ℝ}
    (hf : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ f ((a : ℂ) + (t : ℂ) * I))
    (hne : ∀ t ∈ uIcc T₁ T₂, f ((a : ℂ) + (t : ℂ) * I) ≠ 0) :
    ContinuousOn (fun t : ℝ => (logDeriv f ((a : ℂ) + (t : ℂ) * I)).re) (uIcc T₁ T₂) := by
  intro t ht
  have hA : AnalyticAt ℂ (logDeriv f) ((a : ℂ) + (t : ℂ) * I) := by
    rw [show logDeriv f = fun z => deriv f z / f z from rfl]
    exact (hf t ht).deriv.div (hf t ht) (hne t ht)
  have hc := ContinuousAt.comp (f := fun y : ℝ => (a : ℂ) + (y : ℂ) * I)
    hA.continuousAt (by fun_prop : ContinuousAt (fun y : ℝ => (a : ℂ) + (y : ℂ) * I) t)
  exact (Complex.continuous_re.continuousAt.comp hc).continuousWithinAt

theorem continuousOn_weighted_im_logDeriv_horizontal {f : ℂ → ℂ} {c d T : ℝ}
    (hf : ∀ x ∈ uIcc c d, AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hne : ∀ x ∈ uIcc c d, f ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => (x - c) * (logDeriv f ((x : ℂ) + (T : ℂ) * I)).im) (uIcc c d) := by
  refine (continuousOn_id.sub continuousOn_const).mul ?_
  intro x hx
  have hA : AnalyticAt ℂ (logDeriv f) ((x : ℂ) + (T : ℂ) * I) := by
    rw [show logDeriv f = fun z => deriv f z / f z from rfl]
    exact (hf x hx).deriv.div (hf x hx) (hne x hx)
  have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (T : ℂ) * I)
    hA.continuousAt (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * I) x)
  exact (Complex.continuous_im.continuousAt.comp hc).continuousWithinAt

/-- **The pole gauge drops out of the Littlewood boundary functional.** -/
theorem weightedLittlewoodBoundary_poleGauge_mul {g : ℂ → ℂ} {c d T₁ T₂ : ℝ}
    (hcd : c < d) (hT : T₁ < T₂)
    (hone : (1 : ℂ) ∉ (uIcc c d ×ℂ uIcc T₁ T₂))
    (hg : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), AnalyticAt ℂ g z)
    (hgbot : ∀ x ∈ uIcc c d, g ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (hgtop : ∀ x ∈ uIcc c d, g ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hgright : ∀ t ∈ uIcc T₁ T₂, g ((d : ℂ) + (t : ℂ) * I) ≠ 0)
    (hgleft : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((c : ℂ) + (t : ℂ) * I) = 0}.Finite) :
    weightedLittlewoodBoundary (fun z : ℂ => (z - 1) ^ 2 * g z) c d T₁ T₂
      = weightedLittlewoodBoundary g c d T₁ T₂ := by
  classical
  have hgauge := weightedLittlewoodBoundary_poleGauge_eq_zero hcd hT hone
  set u : ℂ → ℂ := fun z : ℂ => (z - 1) ^ 2 with hu
  have huana : ∀ z : ℂ, AnalyticAt ℂ u z := by
    intro z
    exact (analyticOnNhd_univ_iff_differentiable.mpr (by fun_prop : Differentiable ℂ u)) z
      (Set.mem_univ z)
  have hzero_iff : ∀ z : ℂ, u z = 0 ↔ z = 1 := by
    intro z
    constructor
    · intro h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linear_combination this
    · intro h; rw [hu]; simp [h]
  have hmembot : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₁ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((x : ℂ) + (T₁ : ℂ) * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
      rw [h]; exact left_mem_uIcc
  have hmemtop : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₂ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((x : ℂ) + (T₂ : ℂ) * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + (T₂ : ℂ) * I).im = T₂ := by simp
      rw [h]; exact right_mem_uIcc
  have hmemright : ∀ t ∈ uIcc T₁ T₂, ((d : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((d : ℂ) + (t : ℂ) * I).re = d := by simp
      rw [h]; exact right_mem_uIcc
    · have h : ((d : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hmemleft : ∀ t ∈ uIcc T₁ T₂, ((c : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((c : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hune : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), u z ≠ 0 := by
    intro z hz h0
    exact hone ((hzero_iff z).mp h0 ▸ hz)
  -- the logarithmic derivative splits on the three estimated edges
  have hsplitLD : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), g z ≠ 0 →
      logDeriv (fun w : ℂ => u w * g w) z = logDeriv u z + logDeriv g z := by
    intro z hz hgz
    exact logDeriv_mul z (hune z hz) hgz (huana z).differentiableAt (hg z hz).differentiableAt
  -- left edge
  have hleft : (∫ t in T₁..T₂, Real.log ‖u ((c : ℂ) + (t : ℂ) * I) * g ((c : ℂ) + (t : ℂ) * I)‖)
      = (∫ t in T₁..T₂, Real.log ‖u ((c : ℂ) + (t : ℂ) * I)‖)
        + ∫ t in T₁..T₂, Real.log ‖g ((c : ℂ) + (t : ℂ) * I)‖ := by
    have hui := intervalIntegrable_log_norm_vertical_of_analyticAt
      (f := u) (a := c) (T₁ := T₁) (T₂ := T₂) (fun t _ => huana _)
    have hgi := intervalIntegrable_log_norm_vertical_of_analyticAt
      (f := g) (a := c) (T₁ := T₁) (T₂ := T₂) (fun t ht => hg _ (hmemleft t ht))
    have hae : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.uIoc T₁ T₂ →
        Real.log ‖u ((c : ℂ) + (t : ℂ) * I) * g ((c : ℂ) + (t : ℂ) * I)‖
          = Real.log ‖u ((c : ℂ) + (t : ℂ) * I)‖ + Real.log ‖g ((c : ℂ) + (t : ℂ) * I)‖ := by
      have hnull : ∀ᵐ (t : ℝ) ∂volume,
          t ∉ {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((c : ℂ) + (t : ℂ) * I) = 0} :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hgleft.measure_zero volume)
      filter_upwards [hnull] with t ht htmem
      have htIcc : t ∈ uIcc T₁ T₂ := Set.uIoc_subset_uIcc htmem
      have hgz : g ((c : ℂ) + (t : ℂ) * I) ≠ 0 := fun h0 => ht ⟨htIcc, h0⟩
      have huz : u ((c : ℂ) + (t : ℂ) * I) ≠ 0 := hune _ (hmemleft t htIcc)
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) (norm_ne_zero_iff.mpr hgz)]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_add hui hgi]
  -- right edge, logarithm
  have hrightlog :
      (∫ t in T₁..T₂, Real.log ‖u ((d : ℂ) + (t : ℂ) * I) * g ((d : ℂ) + (t : ℂ) * I)‖)
      = (∫ t in T₁..T₂, Real.log ‖u ((d : ℂ) + (t : ℂ) * I)‖)
        + ∫ t in T₁..T₂, Real.log ‖g ((d : ℂ) + (t : ℂ) * I)‖ := by
    have hui := intervalIntegrable_log_norm_vertical_of_analyticAt
      (f := u) (a := d) (T₁ := T₁) (T₂ := T₂) (fun t _ => huana _)
    have hgi := intervalIntegrable_log_norm_vertical_of_analyticAt
      (f := g) (a := d) (T₁ := T₁) (T₂ := T₂) (fun t ht => hg _ (hmemright t ht))
    rw [← intervalIntegral.integral_add hui hgi]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hgz : g ((d : ℂ) + (t : ℂ) * I) ≠ 0 := hgright t ht
    have huz : u ((d : ℂ) + (t : ℂ) * I) ≠ 0 := hune _ (hmemright t ht)
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) (norm_ne_zero_iff.mpr hgz)]
  -- right edge, logarithmic derivative
  have hrightld :
      (∫ t in T₁..T₂, (logDeriv (fun w : ℂ => u w * g w) ((d : ℂ) + (t : ℂ) * I)).re)
      = (∫ t in T₁..T₂, (logDeriv u ((d : ℂ) + (t : ℂ) * I)).re)
        + ∫ t in T₁..T₂, (logDeriv g ((d : ℂ) + (t : ℂ) * I)).re := by
    have hui : IntervalIntegrable
        (fun t : ℝ => (logDeriv u ((d : ℂ) + (t : ℂ) * I)).re) volume T₁ T₂ :=
      (continuousOn_re_logDeriv_vertical (f := u) (a := d)
        (fun t _ => huana _) (fun t ht => hune _ (hmemright t ht))).intervalIntegrable
    have hgi : IntervalIntegrable
        (fun t : ℝ => (logDeriv g ((d : ℂ) + (t : ℂ) * I)).re) volume T₁ T₂ :=
      (continuousOn_re_logDeriv_vertical (f := g) (a := d)
        (fun t ht => hg _ (hmemright t ht)) (fun t ht => hgright t ht)).intervalIntegrable
    rw [← intervalIntegral.integral_add hui hgi]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hsplitLD _ (hmemright t ht) (hgright t ht), Complex.add_re]
  -- horizontal edges
  have hhoriz : ∀ (T : ℝ), T = T₁ ∨ T = T₂ →
      (∀ x ∈ uIcc c d, ((x : ℂ) + (T : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂)) →
      (∀ x ∈ uIcc c d, g ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∫ x in c..d, (x - c) * (logDeriv (fun w : ℂ => u w * g w) ((x : ℂ) + (T : ℂ) * I)).im)
        = (∫ x in c..d, (x - c) * (logDeriv u ((x : ℂ) + (T : ℂ) * I)).im)
          + ∫ x in c..d, (x - c) * (logDeriv g ((x : ℂ) + (T : ℂ) * I)).im := by
    intro T _ hmem hgne
    have hui : IntervalIntegrable
        (fun x : ℝ => (x - c) * (logDeriv u ((x : ℂ) + (T : ℂ) * I)).im) volume c d :=
      (continuousOn_weighted_im_logDeriv_horizontal (f := u) (c := c) (d := d) (T := T)
        (fun x _ => huana _) (fun x hx => hune _ (hmem x hx))).intervalIntegrable
    have hgi : IntervalIntegrable
        (fun x : ℝ => (x - c) * (logDeriv g ((x : ℂ) + (T : ℂ) * I)).im) volume c d :=
      (continuousOn_weighted_im_logDeriv_horizontal (f := g) (c := c) (d := d) (T := T)
        (fun x hx => hg _ (hmem x hx)) hgne).intervalIntegrable
    rw [← intervalIntegral.integral_add hui hgi]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hsplitLD _ (hmem x hx) (hgne x hx), Complex.add_im]
    ring
  have hbot := hhoriz T₁ (Or.inl rfl) hmembot hgbot
  have htop := hhoriz T₂ (Or.inr rfl) hmemtop hgtop
  unfold weightedLittlewoodBoundary at hgauge ⊢
  rw [hleft, hrightlog, hrightld, hbot, htop]
  linarith [hgauge]

end

end RHTower
