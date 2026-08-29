import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Karamata's uniform convergence theorem, additive form

A measurable `h : ℝ → ℝ` whose shifts vanish at infinity,

`h(x + u) − h(x) → 0`   as `x → ∞`, for every fixed `u`,

satisfies the convergence *uniformly* for `u` in a compact set.  This is the analytic core of
Karamata's theory of slowly varying functions; taking `h(t) = log L(e^t)` turns it into the
multiplicative statement `L(cx)/L(x) → 1` uniformly on compact `c`-sets.

The proof is the classical measure-theoretic one.  Dominated convergence makes the "bad" set
`{v ∈ [0,2] : |h(x+v) − h(x)| > c}` have small measure.  For `u ∈ [0,1]` the two good sets
`{v ∈ [u,2] : |h(x+v) − h(x)| ≤ c}` and `{v ∈ [u,2] : |h(x+u+(v−u)) − h(x+u)| ≤ c}` are subsets of
an interval of length `2 − u ≥ 1` and each miss at most `δ` of it, so for `δ < 1/2` they meet.  At
a common point `v` the identity `x + v = (x+u) + (v−u)` telescopes

`h(x+u) − h(x) = [h(x+v) − h(x)] − [h((x+u)+(v−u)) − h(x+u)]`,

bounding the shift by `2c`.  No boundedness or monotonicity of `h` is used.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

/-- A measurable function whose shifts vanish at infinity. -/
structure IsSlowShift (h : ℝ → ℝ) : Prop where
  meas : Measurable h
  shift : ∀ u : ℝ, Tendsto (fun x => h (x + u) - h x) atTop (𝓝 0)

/-- The set of shifts on which `h` moves by more than `c`, inside `[0,2]`. -/
def shiftBadSet (h : ℝ → ℝ) (c x : ℝ) : Set ℝ :=
  {v ∈ Icc (0 : ℝ) 2 | c < |h (x + v) - h x|}

theorem measurableSet_shiftBadSet {h : ℝ → ℝ} (hm : Measurable h) (c x : ℝ) :
    MeasurableSet (shiftBadSet h c x) := by
  have h1 : Measurable fun v : ℝ => h (x + v) := hm.comp (measurable_const_add x)
  have h1' : Measurable fun v : ℝ => h (x + v) - h x :=
    h1.sub (measurable_const : Measurable fun _ : ℝ => h x)
  have he : {v : ℝ | c < |h (x + v) - h x|}
      = {v : ℝ | c < h (x + v) - h x} ∪ {v : ℝ | c < -(h (x + v) - h x)} := by
    ext v
    simp [lt_abs]
  have h2 : MeasurableSet {v : ℝ | c < |h (x + v) - h x|} := by
    rw [he]
    exact (measurableSet_lt measurable_const h1').union
      (measurableSet_lt measurable_const h1'.neg)
  exact measurableSet_Icc.inter h2

theorem shiftBadSet_subset {h : ℝ → ℝ} (c x : ℝ) : shiftBadSet h c x ⊆ Icc (0 : ℝ) 2 :=
  fun _ hv => hv.1

/-- **The bad set is eventually small.** -/
theorem tendsto_volume_shiftBadSet {h : ℝ → ℝ} (hh : IsSlowShift h) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => (volume (shiftBadSet h c x)).toReal) atTop (𝓝 0) := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable
      ((shiftBadSet h c x).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    intro x
    exact ((measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).indicator
      (measurableSet_shiftBadSet hh.meas c x)).aestronglyMeasurable
  have hbound : Integrable ((Icc (0 : ℝ) 2).indicator (fun _ : ℝ => (1 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  have hdom : ∀ᶠ x in atTop, ∀ᵐ v : ℝ,
      ‖(shiftBadSet h c x).indicator (fun _ : ℝ => (1 : ℝ)) v‖
        ≤ (Icc (0 : ℝ) 2).indicator (fun _ : ℝ => (1 : ℝ)) v := by
    filter_upwards with x
    filter_upwards with v
    by_cases hv : v ∈ shiftBadSet h c x
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (shiftBadSet_subset c x hv)]
      norm_num
    · rw [Set.indicator_of_notMem hv]
      simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) v
  have hptw : ∀ᵐ v : ℝ, Tendsto
      (fun x : ℝ => (shiftBadSet h c x).indicator (fun _ : ℝ => (1 : ℝ)) v) atTop (𝓝 0) := by
    filter_upwards with v
    have hev : ∀ᶠ x in atTop, |h (x + v) - h x| ≤ c := by
      have := (hh.shift v).eventually (Metric.closedBall_mem_nhds (0 : ℝ) hc)
      filter_upwards [this] with x hx
      rw [Real.dist_eq, sub_zero] at hx
      exact hx
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with x hx
    rw [Set.indicator_of_notMem]
    rintro ⟨-, hlt⟩
    linarith
  have hdct := tendsto_integral_filter_of_dominated_convergence
    ((Icc (0 : ℝ) 2).indicator (fun _ : ℝ => (1 : ℝ)))
    (Eventually.of_forall hmeas) hdom hbound hptw
  simp only [integral_zero] at hdct
  refine Tendsto.congr' ?_ hdct
  filter_upwards with x
  rw [integral_indicator (measurableSet_shiftBadSet hh.meas c x)]
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]


/-- The complement of the bad set inside `[0,2]`. -/
def shiftGoodSet (h : ℝ → ℝ) (c x : ℝ) : Set ℝ :=
  {v ∈ Icc (0 : ℝ) 2 | |h (x + v) - h x| ≤ c}

theorem Icc_subset_good_union_bad (h : ℝ → ℝ) (c x : ℝ) :
    Icc (0 : ℝ) 2 ⊆ shiftGoodSet h c x ∪ shiftBadSet h c x := by
  intro v hv
  by_cases hle : |h (x + v) - h x| ≤ c
  · exact Or.inl ⟨hv, hle⟩
  · exact Or.inr ⟨hv, lt_of_not_ge hle⟩

theorem measurableSet_shiftGoodSet {h : ℝ → ℝ} (hm : Measurable h) (c x : ℝ) :
    MeasurableSet (shiftGoodSet h c x) := by
  have h1 : Measurable fun v : ℝ => h (x + v) := hm.comp (measurable_const_add x)
  have h1' : Measurable fun v : ℝ => h (x + v) - h x :=
    h1.sub (measurable_const : Measurable fun _ : ℝ => h x)
  have he : {v : ℝ | |h (x + v) - h x| ≤ c}
      = {v : ℝ | h (x + v) - h x ≤ c} ∩ {v : ℝ | -(h (x + v) - h x) ≤ c} := by
    ext v
    simp [abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  have h2 : MeasurableSet {v : ℝ | |h (x + v) - h x| ≤ c} := by
    rw [he]
    exact (measurableSet_le h1' measurable_const).inter
      (measurableSet_le h1'.neg measurable_const)
  exact measurableSet_Icc.inter h2

/-- **Karamata's uniform convergence theorem, unit step.** -/
theorem isSlowShift_uniform_unit {h : ℝ → ℝ} (hh : IsSlowShift h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ u ∈ Icc (0 : ℝ) 1, |h (x + u) - h x| ≤ ε := by
  set c : ℝ := ε / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hsmall : ∀ᶠ x in atTop, (volume (shiftBadSet h c x)).toReal < 1 / 4 := by
    have := (tendsto_volume_shiftBadSet hh hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    exact this
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hsmall
  filter_upwards [eventually_ge_atTop X₀] with x hx
  intro u hu
  have hu0 : (0 : ℝ) ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  set y : ℝ := x + u with hy
  have hyx : X₀ ≤ y := by rw [hy]; linarith
  -- measure bounds on the two bad sets
  have hbx : (volume (shiftBadSet h c x)).toReal < 1 / 4 := hX₀ x hx
  have hby : (volume (shiftBadSet h c y)).toReal < 1 / 4 := hX₀ y hyx
  have hbxfin : volume (shiftBadSet h c x) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (shiftBadSet_subset c x))
  have hbyfin : volume (shiftBadSet h c y) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (shiftBadSet_subset c y))
  have hbx' : volume (shiftBadSet h c x) ≤ ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_toReal hbxfin]
    exact ENNReal.ofReal_le_ofReal hbx.le
  have hby' : volume (shiftBadSet h c y) ≤ ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_toReal hbyfin]
    exact ENNReal.ofReal_le_ofReal hby.le
  -- the two candidate sets, both inside `[0, 2-u]`
  set C : Set ℝ := (fun w : ℝ => w + u) ⁻¹' shiftGoodSet h c x ∩ Icc 0 (2 - u) with hC
  set D : Set ℝ := shiftGoodSet h c y ∩ Icc 0 (2 - u) with hD
  have hmC : MeasurableSet C :=
    ((measurableSet_shiftGoodSet hh.meas c x).preimage (measurable_id.add_const u)).inter
      measurableSet_Icc
  have hmD : MeasurableSet D := (measurableSet_shiftGoodSet hh.meas c y).inter measurableSet_Icc
  have hIccvol : volume (Icc (0 : ℝ) (2 - u)) = ENNReal.ofReal (2 - u) := by
    rw [Real.volume_Icc, sub_zero]
  have hCsub : Icc (0 : ℝ) (2 - u) ⊆ C ∪ ((fun w : ℝ => w + u) ⁻¹' shiftBadSet h c x) := by
    intro w hw
    have hmem : w + u ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
    rcases Icc_subset_good_union_bad h c x hmem with hg | hb
    · exact Or.inl ⟨hg, hw⟩
    · exact Or.inr hb
  have hDsub : Icc (0 : ℝ) (2 - u) ⊆ D ∪ shiftBadSet h c y := by
    intro w hw
    have hmem : w ∈ Icc (0 : ℝ) 2 := ⟨hw.1, by linarith [hw.2]⟩
    rcases Icc_subset_good_union_bad h c y hmem with hg | hb
    · exact Or.inl ⟨hg, hw⟩
    · exact Or.inr hb
  have hCbound : ENNReal.ofReal (2 - u) ≤ volume C + ENNReal.ofReal (1 / 4) := by
    calc ENNReal.ofReal (2 - u) = volume (Icc (0 : ℝ) (2 - u)) := hIccvol.symm
      _ ≤ volume (C ∪ ((fun w : ℝ => w + u) ⁻¹' shiftBadSet h c x)) := measure_mono hCsub
      _ ≤ volume C + volume ((fun w : ℝ => w + u) ⁻¹' shiftBadSet h c x) := measure_union_le _ _
      _ = volume C + volume (shiftBadSet h c x) := by
          rw [measure_preimage_add_right volume u]
      _ ≤ volume C + ENNReal.ofReal (1 / 4) := add_le_add le_rfl hbx'
  have hDbound : ENNReal.ofReal (2 - u) ≤ volume D + ENNReal.ofReal (1 / 4) := by
    calc ENNReal.ofReal (2 - u) = volume (Icc (0 : ℝ) (2 - u)) := hIccvol.symm
      _ ≤ volume (D ∪ shiftBadSet h c y) := measure_mono hDsub
      _ ≤ volume D + volume (shiftBadSet h c y) := measure_union_le _ _
      _ ≤ volume D + ENNReal.ofReal (1 / 4) := add_le_add le_rfl hby'
  -- the two sets must meet
  have hmeet : (C ∩ D).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hdisj : Disjoint C D := Set.disjoint_iff_inter_eq_empty.2 hempty
    have hunion : volume C + volume D = volume (C ∪ D) := (measure_union hdisj hmD).symm
    have hUsub : C ∪ D ⊆ Icc (0 : ℝ) (2 - u) := Set.union_subset (fun w hw => hw.2)
      (fun w hw => hw.2)
    have hUle : volume C + volume D ≤ ENNReal.ofReal (2 - u) := by
      rw [hunion, ← hIccvol]
      exact measure_mono hUsub
    have hsum : ENNReal.ofReal (2 - u) + ENNReal.ofReal (2 - u)
        ≤ ENNReal.ofReal (2 - u) + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
      calc ENNReal.ofReal (2 - u) + ENNReal.ofReal (2 - u)
          ≤ (volume C + ENNReal.ofReal (1 / 4)) + (volume D + ENNReal.ofReal (1 / 4)) :=
            add_le_add hCbound hDbound
        _ = (volume C + volume D) + (ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)) := by
            ring
        _ ≤ ENNReal.ofReal (2 - u) + (ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)) :=
            add_le_add hUle le_rfl
        _ = ENNReal.ofReal (2 - u) + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
            ring
    have hcancel : ENNReal.ofReal (2 - u)
        ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
      have hfin : ENNReal.ofReal (2 - u) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [add_assoc] at hsum
      exact (ENNReal.add_le_add_iff_left hfin).1 hsum
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hcancel
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hcancel
    linarith
  obtain ⟨w, hwC, hwD⟩ := hmeet
  have h1 : |h (x + (w + u)) - h x| ≤ c := hwC.1.2
  have h2 : |h (y + w) - h y| ≤ c := hwD.1.2
  have hxy : y + w = x + (w + u) := by rw [hy]; ring
  rw [hxy] at h2
  have hkey : h y - h x = (h (x + (w + u)) - h x) - (h (x + (w + u)) - h y) := by ring
  calc |h y - h x| = |(h (x + (w + u)) - h x) - (h (x + (w + u)) - h y)| := by rw [hkey]
      _ ≤ |h (x + (w + u)) - h x| + |h (x + (w + u)) - h y| := abs_sub _ _
      _ ≤ c + c := add_le_add h1 h2
      _ = ε := by rw [hcdef]; ring


/-- **Chaining unit steps.**  A bound on unit shifts above `X₀` bounds every shift, at the cost of
one factor per unit of length. -/
theorem abs_sub_le_of_unit_steps {h : ℝ → ℝ} {X₀ δ : ℝ}
    (hstep : ∀ x : ℝ, X₀ ≤ x → ∀ u ∈ Icc (0 : ℝ) 1, |h (x + u) - h x| ≤ δ)
    {x u : ℝ} (hx : X₀ ≤ x) (hu0 : 0 ≤ u) {k : ℕ} (hk : 0 < k) (huk : u ≤ (k : ℝ)) :
    |h (x + u) - h x| ≤ (k : ℝ) * δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set s : ℝ := u / (k : ℝ) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hkR]
    exact huk
  have hks : (k : ℝ) * s = u := by rw [hs]; field_simp
  have htel : (∑ i ∈ Finset.range k,
      (h (x + ((i : ℝ) + 1) * s) - h (x + (i : ℝ) * s)))
      = h (x + (k : ℝ) * s) - h (x + (0 : ℝ) * s) := by
    have := Finset.sum_range_sub (fun i : ℕ => h (x + (i : ℝ) * s)) k
    simpa using this
  rw [zero_mul, add_zero, hks] at htel
  have hstep' : ∀ i ∈ Finset.range k,
      |h (x + ((i : ℝ) + 1) * s) - h (x + (i : ℝ) * s)| ≤ δ := by
    intro i _
    have hbase : X₀ ≤ x + (i : ℝ) * s := by
      have : (0 : ℝ) ≤ (i : ℝ) * s := by positivity
      linarith
    have hval := hstep (x + (i : ℝ) * s) hbase s ⟨hs0, hs1⟩
    have hid : x + (i : ℝ) * s + s = x + ((i : ℝ) + 1) * s := by ring
    rwa [hid] at hval
  have hsum : |h (x + u) - h x|
      ≤ ∑ i ∈ Finset.range k, |h (x + ((i : ℝ) + 1) * s) - h (x + (i : ℝ) * s)| := by
    rw [← htel]
    exact Finset.abs_sum_le_sum_abs _ _
  calc |h (x + u) - h x|
      ≤ ∑ i ∈ Finset.range k, |h (x + ((i : ℝ) + 1) * s) - h (x + (i : ℝ) * s)| := hsum
    _ ≤ ∑ _i ∈ Finset.range k, δ := Finset.sum_le_sum hstep'
    _ = (k : ℝ) * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Karamata's uniform convergence theorem, nonnegative shifts.** -/
theorem isSlowShift_uniform_nonneg {h : ℝ → ℝ} (hh : IsSlowShift h) (U : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x in atTop, ∀ u ∈ Icc (0 : ℝ) U, |h (x + u) - h x| ≤ ε := by
  set k : ℕ := ⌈U⌉₊ + 1 with hk
  have hk0 : 0 < k := Nat.succ_pos _
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hUk : U ≤ (k : ℝ) := by
    have h1 : U ≤ (⌈U⌉₊ : ℝ) := Nat.le_ceil U
    have h2 : ((⌈U⌉₊ : ℝ)) ≤ (k : ℝ) := by
      rw [hk]; push_cast; linarith
    linarith
  have hε' : 0 < ε / (k : ℝ) := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (isSlowShift_uniform_unit hh hε')
  filter_upwards [eventually_ge_atTop X₀] with x hx
  intro u hu
  have hchain := abs_sub_le_of_unit_steps (h := h) (X₀ := X₀) (δ := ε / (k : ℝ)) hX₀ hx hu.1
    hk0 (le_trans hu.2 hUk)
  have hfin : (k : ℝ) * (ε / (k : ℝ)) = ε := by field_simp
  linarith [hchain, hfin.le, hfin.ge]

/-- **Potter's bound, additive form.**  Above a threshold, the shift grows at most linearly. -/
theorem isSlowShift_potter {h : ℝ → ℝ} (hh : IsSlowShift h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ x y : ℝ, X₀ ≤ x → x ≤ y → |h y - h x| ≤ (y - x + 2) * δ := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (isSlowShift_uniform_unit hh hδ)
  refine ⟨X₀, fun x y hx hxy => ?_⟩
  set u : ℝ := y - x with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  set k : ℕ := ⌈u⌉₊ + 1 with hk
  have hk0 : 0 < k := Nat.succ_pos _
  have huk : u ≤ (k : ℝ) := by
    have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have h2 : ((⌈u⌉₊ : ℝ)) ≤ (k : ℝ) := by rw [hk]; push_cast; linarith
    linarith
  have hkle : (k : ℝ) ≤ u + 2 := by
    have h1 : (⌈u⌉₊ : ℝ) ≤ u + 1 := by
      have := Nat.ceil_lt_add_one hu0
      exact_mod_cast this.le
    rw [hk]; push_cast; linarith
  have hchain := abs_sub_le_of_unit_steps (h := h) hX₀ hx hu0 hk0 huk
  rw [hu, show x + (y - x) = y by ring] at hchain
  calc |h y - h x| ≤ (k : ℝ) * δ := hchain
    _ ≤ (u + 2) * δ := by nlinarith [hkle, hδ]
    _ = (y - x + 2) * δ := by rw [hu]

/-- **Karamata's uniform convergence theorem.** -/
theorem isSlowShift_uniform {h : ℝ → ℝ} (hh : IsSlowShift h) (U : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x in atTop, ∀ u ∈ Icc (-U) U, |h (x + u) - h x| ≤ ε := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (isSlowShift_uniform_nonneg hh U hε)
  filter_upwards [eventually_ge_atTop (X₀ + |U|)] with x hx
  intro u hu
  have hu1 : -U ≤ u := hu.1
  have hu2 : u ≤ U := hu.2
  have hUabs : U ≤ |U| := le_abs_self U
  have hUabs' : -|U| ≤ -U := by
    have := neg_abs_le U
    linarith
  rcases le_or_gt 0 u with hpos | hneg
  · exact hX₀ x (by linarith [abs_nonneg U]) u ⟨hpos, hu2⟩
  · have hx' : X₀ ≤ x + u := by linarith
    have hmem : -u ∈ Icc (0 : ℝ) U := ⟨by linarith, by linarith⟩
    have := hX₀ (x + u) hx' (-u) hmem
    rw [show x + u + -u = x by ring] at this
    rw [abs_sub_comm]
    exact this

end HTGeometry
