import GaloisForLFunctions.HTGeometry.ChronometricCausalDiamond
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Clock readings realize the diamond reconstruction

Clock-only reconstruction inside a causal diamond assumes the squared interval is known on every
timelike direction at every event of the diamond. A laboratory does not know squared intervals; it
reads clocks, and it can only carry a clock along a worldline that stays inside the diamond.

Both gaps close. The chronological diamond is open, so at every event of it and in *every*
direction the straight probe `s ↦ x + s • v` remains inside the diamond for a nonempty interval of
its own parameter: the required variations are all realized, none of them leaving the region. The
reading of such a probe is the integral of its proper-time rate, and by the fundamental theorem of
calculus that reading differentiates at the moment of passage to the instantaneous rate
`√(−g(x)(v,v))`, from which the squared interval is recovered.

Consequently two metrics whose clocks produce the same readings on every probe confined to the
diamond agree at every event of the diamond — a reconstruction theorem whose hypothesis is a set of
numbers a laboratory measures.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

namespace SmoothPseudoMetric

variable {d : ℕ}

/-! ## The metric in the event -/

/-- The squared interval of a fixed direction is continuous in the event, the metric coefficients
being smooth. -/
theorem continuous_squaredInterval_event (g : SmoothPseudoMetric d) (v : Fin d → ℝ) :
    Continuous fun x : Fin d → ℝ => g.squaredInterval x v := by
  simp only [squaredInterval]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((g.contDiff_metric i j).continuous.mul continuous_const).mul continuous_const

/-! ## The probe -/

/-- The straight probe through the event `x` with velocity `v`, parametrised by its own
parameter. -/
def clockSegment (x v : Fin d → ℝ) : ℝ → (Fin d → ℝ) := fun s => x + s • v

@[simp] theorem clockSegment_zero (x v : Fin d → ℝ) : clockSegment x v 0 = x := by
  simp [clockSegment]

theorem continuous_clockSegment (x v : Fin d → ℝ) : Continuous (clockSegment x v) :=
  continuous_const.add (continuous_id.smul continuous_const)

/-- **The probe passes the event with the prescribed velocity.** -/
theorem hasDerivAt_clockSegment (x v : Fin d → ℝ) (s : ℝ) :
    HasDerivAt (clockSegment x v) v s := by
  have h : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  exact h.const_add x

/-! ## Realization inside the diamond -/

/-- The directions at `x` realized by a probe that never leaves the diamond. -/
def realizedDirections (g : SmoothPseudoMetric (d + 1)) (p q x : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {v | ∀ᶠ s in nhds (0 : ℝ), clockSegment x v s ∈ chronoDiamond g p q}

/-- **Every direction at an interior event is realized.** The chronological diamond is open, so a
probe launched in any direction from any of its events stays inside it for a nonempty interval of
its own parameter. -/
theorem mem_realizedDirections (g : SmoothPseudoMetric (d + 1)) {p q x : Fin (d + 1) → ℝ}
    (hx : x ∈ chronoDiamond g p q) (v : Fin (d + 1) → ℝ) :
    v ∈ realizedDirections g p q x := by
  have hcont : ContinuousAt (clockSegment x v) 0 := (continuous_clockSegment x v).continuousAt
  have hmem : chronoDiamond g p q ∈ nhds (clockSegment x v 0) := by
    rw [clockSegment_zero]
    exact (isOpen_chronoDiamond g p q).mem_nhds hx
  exact hcont.preimage_mem_nhds hmem

/-- **The realized directions exhaust the whole direction space**, so the clock data the
reconstruction consumes are produced by probes that never leave the laboratory region. -/
theorem realizedDirections_eq_univ (g : SmoothPseudoMetric (d + 1)) {p q x : Fin (d + 1) → ℝ}
    (hx : x ∈ chronoDiamond g p q) : realizedDirections g p q x = Set.univ :=
  Set.eq_univ_of_forall fun v => mem_realizedDirections g hx v

theorem timelikeCone_subset_realizedDirections (g : SmoothPseudoMetric (d + 1))
    {p q x : Fin (d + 1) → ℝ} (hx : x ∈ chronoDiamond g p q) :
    g.timelikeCone x ⊆ realizedDirections g p q x := by
  rw [realizedDirections_eq_univ g hx]
  exact Set.subset_univ _

/-- A quantitative form of the realization: an explicit parameter interval on which the probe is
confined to the diamond. -/
theorem exists_pos_segment_subset_chronoDiamond (g : SmoothPseudoMetric (d + 1))
    {p q x : Fin (d + 1) → ℝ} (hx : x ∈ chronoDiamond g p q) (v : Fin (d + 1) → ℝ) :
    ∃ ε > 0, ∀ s : ℝ, |s| < ε → clockSegment x v s ∈ chronoDiamond g p q := by
  have h := mem_realizedDirections g hx v
  simp only [realizedDirections, Set.mem_setOf_eq] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε, hε, fun s hs => hball ?_⟩
  rwa [Real.dist_eq, sub_zero]

theorem abs_le_abs_of_mem_uIcc_zero {b s : ℝ} (hs : s ∈ Set.uIcc (0 : ℝ) b) : |s| ≤ |b| := by
  rcases le_total 0 b with hb | hb
  · rw [Set.uIcc_of_le hb] at hs
    obtain ⟨h1, h2⟩ := hs
    rw [abs_of_nonneg h1, abs_of_nonneg hb]
    exact h2
  · rw [Set.uIcc_of_ge hb] at hs
    obtain ⟨h1, h2⟩ := hs
    rw [abs_of_nonpos h2, abs_of_nonpos hb]
    linarith

/-- **A short enough run of the probe is confined to the diamond**, at every parameter it
traverses. -/
theorem eventually_uIcc_subset_chronoDiamond (g : SmoothPseudoMetric (d + 1))
    {p q x : Fin (d + 1) → ℝ} (hx : x ∈ chronoDiamond g p q) (v : Fin (d + 1) → ℝ) :
    ∀ᶠ b in nhds (0 : ℝ),
      ∀ s ∈ Set.uIcc (0 : ℝ) b, clockSegment x v s ∈ chronoDiamond g p q := by
  obtain ⟨ε, hε, hball⟩ := exists_pos_segment_subset_chronoDiamond g hx v
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun b hb s hs => hball s ?_⟩
  have hbabs : |b| < ε := by rwa [Real.dist_eq, sub_zero] at hb
  exact lt_of_le_of_lt (abs_le_abs_of_mem_uIcc_zero hs) hbabs

/-! ## The clock reading -/

/-- The instantaneous rate of a clock passing the event `x` with velocity `v`. -/
def properTimeRate (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) : ℝ :=
  Real.sqrt (-(g.squaredInterval x v))

theorem properTimeRate_pos (g : SmoothPseudoMetric d) {x v : Fin d → ℝ}
    (hv : v ∈ g.timelikeCone x) : 0 < g.properTimeRate x v :=
  Real.sqrt_pos.mpr (neg_pos.mpr hv)

/-- **The rate determines the squared interval on the timelike cone.** -/
theorem squaredInterval_eq_of_properTimeRate_eq {g h : SmoothPseudoMetric d} {x v : Fin d → ℝ}
    (hv : v ∈ g.timelikeCone x) (hrate : g.properTimeRate x v = h.properTimeRate x v) :
    g.squaredInterval x v = h.squaredInterval x v := by
  have hg : 0 < -(g.squaredInterval x v) := neg_pos.mpr hv
  have hgpos : 0 < g.properTimeRate x v := Real.sqrt_pos.mpr hg
  have hhpos : 0 < h.properTimeRate x v := by rw [← hrate]; exact hgpos
  have hh : 0 < -(h.squaredInterval x v) := Real.sqrt_pos.mp hhpos
  have hsq : g.properTimeRate x v ^ (2 : ℕ) = h.properTimeRate x v ^ (2 : ℕ) := by rw [hrate]
  rw [properTimeRate, properTimeRate, Real.sq_sqrt hg.le, Real.sq_sqrt hh.le] at hsq
  linarith

theorem continuous_properTimeRate_along (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) :
    Continuous fun s : ℝ => g.properTimeRate (clockSegment x v s) v := by
  simp only [properTimeRate]
  exact Real.continuous_sqrt.comp
    (((g.continuous_squaredInterval_event v).comp (continuous_clockSegment x v)).neg)

/-- The reading accumulated by a clock carried along the probe from parameter `a` to `b`. -/
def properTime (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) (a b : ℝ) : ℝ :=
  ∫ s in a..b, g.properTimeRate (clockSegment x v s) v

/-- **The reading differentiates to the instantaneous rate.** -/
theorem hasDerivAt_properTime (g : SmoothPseudoMetric d) (x v : Fin d → ℝ) (a t : ℝ) :
    HasDerivAt (fun b => g.properTime x v a b) (g.properTimeRate (clockSegment x v t) v) t :=
  ((continuous_properTimeRate_along g x v).integral_hasStrictDerivAt a t).hasDerivAt

/-- **Equal readings on arbitrarily short runs of the probe give equal rates at the event.** -/
theorem properTimeRate_eq_of_properTime_eventuallyEq {g h : SmoothPseudoMetric d}
    {x v : Fin d → ℝ}
    (hread : ∀ᶠ b in nhds (0 : ℝ), g.properTime x v 0 b = h.properTime x v 0 b) :
    g.properTimeRate x v = h.properTimeRate x v := by
  have hg : HasDerivAt (fun b => g.properTime x v 0 b) (g.properTimeRate x v) 0 := by
    have h0 := hasDerivAt_properTime g x v 0 0
    rwa [clockSegment_zero] at h0
  have hh : HasDerivAt (fun b => h.properTime x v 0 b) (h.properTimeRate x v) 0 := by
    have h0 := hasDerivAt_properTime h x v 0 0
    rwa [clockSegment_zero] at h0
  exact hg.unique (hh.congr_of_eventuallyEq hread)

/-! ## The dynamical half of diamond reconstruction -/

/-- **Clock readings inside the diamond determine the metric inside the diamond.**

The hypothesis is a set of laboratory numbers: for every event of the chronological diamond, every
direction, and every run of the straight probe that stays inside the diamond, the two metrics give
the clock the same reading. Every such run exists — the diamond is open — and the readings
differentiate to the squared interval, which determines the metric on the region. -/
theorem eqOn_chronoDiamond_of_clockReadings {g h : SmoothPseudoMetric (d + 1)}
    (p q : Fin (d + 1) → ℝ)
    (htimelike : ∀ x ∈ chronoDiamond g p q, (g.timelikeCone x).Nonempty)
    (hread : ∀ x ∈ chronoDiamond g p q, ∀ v : Fin (d + 1) → ℝ, ∀ b : ℝ,
      (∀ s ∈ Set.uIcc (0 : ℝ) b, clockSegment x v s ∈ chronoDiamond g p q) →
      g.properTime x v 0 b = h.properTime x v 0 b) :
    ∀ x ∈ chronoDiamond g p q, g.metric x = h.metric x := by
  refine eqOn_of_properTime_eqOn htimelike ?_
  intro x hx v hv
  refine squaredInterval_eq_of_properTimeRate_eq hv ?_
  refine properTimeRate_eq_of_properTime_eventuallyEq ?_
  exact (eventually_uIcc_subset_chronoDiamond g hx v).mono fun b hb => hread x hx v b hb

/-- **The clock-only diamond reconstruction theorem.** Two metrics whose clocks read alike on every
probe confined to the diamond have the same squared intervals there: the readings recover the
geometry of the region and claim nothing outside it. -/
theorem squaredInterval_eqOn_chronoDiamond_of_clockReadings {g h : SmoothPseudoMetric (d + 1)}
    (p q : Fin (d + 1) → ℝ)
    (htimelike : ∀ x ∈ chronoDiamond g p q, (g.timelikeCone x).Nonempty)
    (hread : ∀ x ∈ chronoDiamond g p q, ∀ v : Fin (d + 1) → ℝ, ∀ b : ℝ,
      (∀ s ∈ Set.uIcc (0 : ℝ) b, clockSegment x v s ∈ chronoDiamond g p q) →
      g.properTime x v 0 b = h.properTime x v 0 b) :
    ∀ x ∈ chronoDiamond g p q, ∀ v : Fin (d + 1) → ℝ,
      g.squaredInterval x v = h.squaredInterval x v := by
  intro x hx v
  have hmet := eqOn_chronoDiamond_of_clockReadings p q htimelike hread x hx
  simp only [squaredInterval, hmet]

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
