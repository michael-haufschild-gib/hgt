import GaloisForLFunctions.HTGeometry.CausalJordanDriftWord
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Titchmarsh causal support of a formed drift history

Section 5 of the causal Jordan formation card `ULF-CJFM-1`.

The elementary two-window response `(CJF.20)` of a single signed drift event carries a *definite
sign* immediately after its opening edge and immediately before its closing edge.  That property is
stable under convolution by an elementary positivity argument, so the essential-support endpoints of
a whole formed history add exactly:

* `(CJF.25)`  `ℓ(h_w) = B(w) - P(w)` and `r(h_w) = B(w) + T(w) + N(w)`;
* `(CJF.26)`  `r(h_w) - ℓ(h_w) = T(w) + V(w)`;
* `(CJF.27)`  causality of the formed history is `B(w) ≥ P(w)`;
* `(CJF.28)`, `(CJF.29)`  one delay admits a word and its functional-equation reflection exactly
  when it covers `Λ(w) = max(P, N) = |D(w)| + R(w)`.

No Titchmarsh convolution theorem is assumed: the exactness of the endpoints is *derived* from the
sign-definiteness of the elementary edges, which is all the concrete family needs.  Everything is
unconditional.
-/

open MeasureTheory
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Sign-definite causal edges -/

/-- `f` vanishes almost everywhere below `a` and carries the strict sign `σ` immediately above it:
`a` is exactly the left endpoint of the essential support of `f`. -/
structure LeftEdge (f : ℝ → ℝ) (a σ : ℝ) : Prop where
  vanish : ∀ᵐ t, t < a → f t = 0
  edge : ∃ ε > 0, ∀ᵐ t, t ∈ Set.Ioo a (a + ε) → 0 < σ * f t

/-- `f` vanishes almost everywhere above `r` and carries the strict sign `σ` immediately below it:
`r` is exactly the right endpoint of the essential support of `f`. -/
structure RightEdge (f : ℝ → ℝ) (r σ : ℝ) : Prop where
  vanish : ∀ᵐ t, r < t → f t = 0
  edge : ∃ ε > 0, ∀ᵐ t, t ∈ Set.Ioo (r - ε) r → 0 < σ * f t

theorem volume_map_neg_self : Measure.map (fun x : ℝ => -x) volume = volume := by
  have h := Real.smul_map_volume_mul_left (a := (-1 : ℝ)) (by norm_num)
  simpa using h

theorem measurePreserving_subLeft (t : ℝ) :
    MeasurePreserving (fun s : ℝ => t - s) volume volume := by
  have hneg : MeasurePreserving (fun s : ℝ => -s) volume volume :=
    ⟨measurable_neg, volume_map_neg_self⟩
  have := (measurePreserving_add_left volume t).comp hneg
  simpa [Function.comp_def, sub_eq_add_neg] using this

theorem ae_comp_sub_left {p : ℝ → Prop} (t : ℝ) (h : ∀ᵐ u, p u) : ∀ᵐ s, p (t - s) :=
  (measurePreserving_subLeft t).quasiMeasurePreserving.ae h

theorem ae_ne_point (a : ℝ) : ∀ᵐ s : ℝ, s ≠ a := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton a)] with s hs
  simpa using hs

theorem causal_convolution_apply (f g : ℝ → ℝ) (x : ℝ) :
    (f ⋆ g) x = ∫ s, f s * g (x - s) := by
  rw [convolution_def]
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- **Left causal endpoints add.**  For sign-definite edges this needs no Titchmarsh input. -/
theorem LeftEdge.convolution {f g : ℝ → ℝ} {a b σ τ : ℝ}
    (hf : LeftEdge f a σ) (hg : LeftEdge g b τ)
    (hex : ∀ x : ℝ, Integrable (fun s => f s * g (x - s))) :
    LeftEdge (f ⋆ g) (a + b) (σ * τ) := by
  obtain ⟨εf, hεf, hfe⟩ := hf.edge
  obtain ⟨εg, hεg, hge⟩ := hg.edge
  constructor
  · filter_upwards with t ht
    rw [causal_convolution_apply]
    refine integral_eq_zero_of_ae ?_
    have hgv : ∀ᵐ s : ℝ, t - s < b → g (t - s) = 0 := ae_comp_sub_left t hg.vanish
    filter_upwards [hf.vanish, hgv] with s hs hgs
    simp only [Pi.zero_apply]
    rcases lt_or_ge s a with h | h
    · rw [hs h, zero_mul]
    · rw [hgs (by linarith), mul_zero]
  · refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    filter_upwards with t ht
    have ht1 : a + b < t := ht.1
    have ht2 : t < a + b + min εf εg := ht.2
    have hgv : ∀ᵐ s : ℝ, t - s < b → g (t - s) = 0 := ae_comp_sub_left t hg.vanish
    have hge' : ∀ᵐ s : ℝ, t - s ∈ Set.Ioo b (b + εg) → 0 < τ * g (t - s) :=
      ae_comp_sub_left t hge
    have hpos : ∀ᵐ s : ℝ, s ∈ Set.Ioo a (t - b) →
        0 < σ * τ * (f s * g (t - s)) := by
      filter_upwards [hfe, hge'] with s hs1 hs2
      rintro ⟨hs3, hs4⟩
      have h1 : 0 < σ * f s :=
        hs1 ⟨hs3, by have := min_le_left εf εg; linarith⟩
      have h2 : 0 < τ * g (t - s) :=
        hs2 ⟨by linarith, by have := min_le_right εf εg; linarith⟩
      calc (0:ℝ) < (σ * f s) * (τ * g (t - s)) := mul_pos h1 h2
        _ = σ * τ * (f s * g (t - s)) := by ring
    have hnonneg : 0 ≤ᵐ[volume] fun s => σ * τ * (f s * g (t - s)) := by
      filter_upwards [hf.vanish, hgv, hpos, ae_ne_point a, ae_ne_point (t - b)] with s hs1 hs2 hs3 hs4 hs5
      simp only [Pi.zero_apply]
      rcases lt_trichotomy s a with h | h | h
      · rw [hs1 h]; simp
      · exact absurd h hs4
      · rcases lt_trichotomy s (t - b) with h' | h' | h'
        · exact le_of_lt (hs3 ⟨h, h'⟩)
        · exact absurd h' hs5
        · rw [hs2 (by linarith)]; simp
    have hsupp : 0 < volume (Function.support fun s => σ * τ * (f s * g (t - s))) := by
      have hsub : volume (Set.Ioo a (t - b))
          ≤ volume (Function.support fun s => σ * τ * (f s * g (t - s))) := by
        refine measure_mono_ae ?_
        filter_upwards [hpos] with s hs hmem
        exact ne_of_gt (hs hmem)
      refine lt_of_lt_of_le ?_ hsub
      rw [Real.volume_Ioo]
      simp only [ENNReal.ofReal_pos]
      linarith
    have hint : 0 < ∫ s, σ * τ * (f s * g (t - s)) := by
      rw [integral_pos_iff_support_of_nonneg_ae hnonneg ((hex t).const_mul _)]
      exact hsupp
    have hEq : ∫ s, σ * τ * (f s * g (t - s)) = σ * τ * (f ⋆ g) t := by
      rw [causal_convolution_apply, integral_const_mul]
    rwa [hEq] at hint

/-- **Right causal endpoints add.** -/
theorem RightEdge.convolution {f g : ℝ → ℝ} {a b σ τ : ℝ}
    (hf : RightEdge f a σ) (hg : RightEdge g b τ)
    (hex : ∀ x : ℝ, Integrable (fun s => f s * g (x - s))) :
    RightEdge (f ⋆ g) (a + b) (σ * τ) := by
  obtain ⟨εf, hεf, hfe⟩ := hf.edge
  obtain ⟨εg, hεg, hge⟩ := hg.edge
  constructor
  · filter_upwards with t ht
    rw [causal_convolution_apply]
    refine integral_eq_zero_of_ae ?_
    have hgv : ∀ᵐ s : ℝ, b < t - s → g (t - s) = 0 := ae_comp_sub_left t hg.vanish
    filter_upwards [hf.vanish, hgv] with s hs hgs
    simp only [Pi.zero_apply]
    rcases lt_or_ge a s with h | h
    · rw [hs h, zero_mul]
    · rw [hgs (by linarith), mul_zero]
  · refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    filter_upwards with t ht
    have ht1 : a + b - min εf εg < t := ht.1
    have ht2 : t < a + b := ht.2
    have hgv : ∀ᵐ s : ℝ, b < t - s → g (t - s) = 0 := ae_comp_sub_left t hg.vanish
    have hge' : ∀ᵐ s : ℝ, t - s ∈ Set.Ioo (b - εg) b → 0 < τ * g (t - s) :=
      ae_comp_sub_left t hge
    have hpos : ∀ᵐ s : ℝ, s ∈ Set.Ioo (t - b) a →
        0 < σ * τ * (f s * g (t - s)) := by
      filter_upwards [hfe, hge'] with s hs1 hs2
      rintro ⟨hs3, hs4⟩
      have h1 : 0 < σ * f s :=
        hs1 ⟨by have := min_le_left εf εg; linarith, hs4⟩
      have h2 : 0 < τ * g (t - s) :=
        hs2 ⟨by have := min_le_right εf εg; linarith, by linarith⟩
      calc (0:ℝ) < (σ * f s) * (τ * g (t - s)) := mul_pos h1 h2
        _ = σ * τ * (f s * g (t - s)) := by ring
    have hnonneg : 0 ≤ᵐ[volume] fun s => σ * τ * (f s * g (t - s)) := by
      filter_upwards [hf.vanish, hgv, hpos, ae_ne_point a, ae_ne_point (t - b)] with s hs1 hs2 hs3 hs4 hs5
      simp only [Pi.zero_apply]
      rcases lt_trichotomy a s with h | h | h
      · rw [hs1 h]; simp
      · exact absurd h.symm hs4
      · rcases lt_trichotomy (t - b) s with h' | h' | h'
        · exact le_of_lt (hs3 ⟨h', h⟩)
        · exact absurd h'.symm hs5
        · rw [hs2 (by linarith)]; simp
    have hsupp : 0 < volume (Function.support fun s => σ * τ * (f s * g (t - s))) := by
      have hsub : volume (Set.Ioo (t - b) a)
          ≤ volume (Function.support fun s => σ * τ * (f s * g (t - s))) := by
        refine measure_mono_ae ?_
        filter_upwards [hpos] with s hs hmem
        exact ne_of_gt (hs hmem)
      refine lt_of_lt_of_le ?_ hsub
      rw [Real.volume_Ioo]
      simp only [ENNReal.ofReal_pos]
      linarith
    have hint : 0 < ∫ s, σ * τ * (f s * g (t - s)) := by
      rw [integral_pos_iff_support_of_nonneg_ae hnonneg ((hex t).const_mul _)]
      exact hsupp
    have hEq : ∫ s, σ * τ * (f s * g (t - s)) = σ * τ * (f ⋆ g) t := by
      rw [causal_convolution_apply, integral_const_mul]
    rwa [hEq] at hint

/-! ## Integrability transport -/

theorem integrable_compSubLeft {g : ℝ → ℝ} (hg : Integrable g) (x : ℝ) :
    Integrable (fun s => g (x - s)) :=
  ((measurePreserving_subLeft x).integrable_comp hg.aestronglyMeasurable).mpr hg

theorem integrable_mul_comp_sub {f g : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume) (hfb : ∀ x, |f x| ≤ C) (hg : Integrable g) (x : ℝ) :
    Integrable (fun s => f s * g (x - s)) :=
  (integrable_compSubLeft hg x).bdd_mul hf
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfb y)

/-! ## The elementary causal event response -/

/-- `(CJF.20)`  Normalized two-window causal response of a single signed drift event: a unit
window opened at the displaced delay `b - δ` minus the same window at the reference delay `b`. -/
def eventResponse (δ b T : ℝ) (t : ℝ) : ℝ :=
  T⁻¹ * ((Set.Ico (b - δ) (b - δ + T)).indicator (fun _ => (1:ℝ)) t
    - (Set.Ico b (b + T)).indicator (fun _ => (1:ℝ)) t)

theorem measurable_eventResponse (δ b T : ℝ) : Measurable (eventResponse δ b T) :=
  ((measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)).const_mul _

theorem abs_eventResponse_le (δ b T : ℝ) (t : ℝ) : |eventResponse δ b T t| ≤ 2 * |T⁻¹| := by
  have h1 : |(Set.Ico (b - δ) (b - δ + T)).indicator (fun _ => (1:ℝ)) t
      - (Set.Ico b (b + T)).indicator (fun _ => (1:ℝ)) t| ≤ 2 := by
    by_cases hA : t ∈ Set.Ico (b - δ) (b - δ + T) <;>
      by_cases hB : t ∈ Set.Ico b (b + T) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB]
  rw [eventResponse, abs_mul]
  calc |T⁻¹| * |(Set.Ico (b - δ) (b - δ + T)).indicator (fun _ => (1:ℝ)) t
        - (Set.Ico b (b + T)).indicator (fun _ => (1:ℝ)) t|
      ≤ |T⁻¹| * 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = 2 * |T⁻¹| := by ring

theorem integrable_indicator_Ico (a c : ℝ) :
    Integrable ((Set.Ico a c).indicator (fun _ => (1:ℝ))) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  refine integrableOn_const ?_ ?_
  · simp [Real.volume_Ico]
  · simp

theorem integrable_eventResponse (δ b T : ℝ) : Integrable (eventResponse δ b T) :=
  (((integrable_indicator_Ico (b - δ) (b - δ + T)).sub
    (integrable_indicator_Ico b (b + T))).const_mul _)

/-- The sign carried by the causal response immediately after its opening edge. -/
def driftEdgeSign (δ : ℝ) : ℝ := if 0 < δ then 1 else -1

theorem driftEdgeSign_ne_zero (δ : ℝ) : driftEdgeSign δ ≠ 0 := by
  unfold driftEdgeSign; split <;> norm_num

/-- `(CJF.30)`  Exact opening edge of one event: the left endpoint is `b - δ⁺`. -/
theorem leftEdge_eventResponse {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T) :
    LeftEdge (eventResponse δ b T) (b - max δ 0) (driftEdgeSign δ) := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have hmax : max δ 0 = 0 := max_eq_right hneg.le
    have hsign : driftEdgeSign δ = -1 := by
      unfold driftEdgeSign; rw [if_neg (by linarith)]
    constructor
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [hmax, sub_zero] at ht
      rw [eventResponse, Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      ring
    · refine ⟨min T (-δ), lt_min hT (by linarith), Filter.Eventually.of_forall fun t ht => ?_⟩
      rw [hmax, sub_zero] at ht
      obtain ⟨h1, h2⟩ := ht
      have hle : min T (-δ) ≤ T := min_le_left _ _
      have hle' : min T (-δ) ≤ -δ := min_le_right _ _
      rw [hsign, eventResponse,
        Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_mem (by constructor <;> [linarith; linarith])]
      have : T⁻¹ * ((0:ℝ) - 1) = -T⁻¹ := by ring
      rw [this]
      have : (0:ℝ) < T⁻¹ := by positivity
      linarith
  · have hmax : max δ 0 = δ := max_eq_left hpos.le
    have hsign : driftEdgeSign δ = 1 := by
      unfold driftEdgeSign; rw [if_pos hpos]
    constructor
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [hmax] at ht
      rw [eventResponse, Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      ring
    · refine ⟨min T δ, lt_min hT hpos, Filter.Eventually.of_forall fun t ht => ?_⟩
      rw [hmax] at ht
      obtain ⟨h1, h2⟩ := ht
      have hle : min T δ ≤ T := min_le_left _ _
      have hle' : min T δ ≤ δ := min_le_right _ _
      rw [hsign, eventResponse,
        Set.indicator_of_mem (by constructor <;> [linarith; linarith]),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      have : T⁻¹ * ((1:ℝ) - 0) = T⁻¹ := by ring
      rw [this, one_mul]
      positivity

/-- `(CJF.30)`  Exact closing edge of one event: the right endpoint is `b + T + δ⁻`. -/
theorem rightEdge_eventResponse {δ b T : ℝ} (hδ : δ ≠ 0) (hT : 0 < T) :
    RightEdge (eventResponse δ b T) (b + T + max (-δ) 0) (-driftEdgeSign δ) := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have hmax : max (-δ) 0 = -δ := max_eq_left (by linarith)
    have hsign : -driftEdgeSign δ = 1 := by
      unfold driftEdgeSign; rw [if_neg (by linarith)]; ring
    constructor
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [hmax] at ht
      rw [eventResponse, Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      ring
    · refine ⟨min T (-δ), lt_min hT (by linarith), Filter.Eventually.of_forall fun t ht => ?_⟩
      rw [hmax] at ht
      obtain ⟨h1, h2⟩ := ht
      have hle : min T (-δ) ≤ T := min_le_left _ _
      have hle' : min T (-δ) ≤ -δ := min_le_right _ _
      rw [hsign, eventResponse,
        Set.indicator_of_mem (by constructor <;> [linarith; linarith]),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      have : T⁻¹ * ((1:ℝ) - 0) = T⁻¹ := by ring
      rw [this, one_mul]
      positivity
  · have hmax : max (-δ) 0 = 0 := max_eq_right (by linarith)
    have hsign : -driftEdgeSign δ = -1 := by
      unfold driftEdgeSign; rw [if_pos hpos]
    constructor
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [hmax, add_zero] at ht
      rw [eventResponse, Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_notMem (by simp; intro h; linarith)]
      ring
    · refine ⟨min T δ, lt_min hT hpos, Filter.Eventually.of_forall fun t ht => ?_⟩
      rw [hmax, add_zero] at ht
      obtain ⟨h1, h2⟩ := ht
      have hle : min T δ ≤ T := min_le_left _ _
      have hle' : min T δ ≤ δ := min_le_right _ _
      rw [hsign, eventResponse,
        Set.indicator_of_notMem (by simp; intro h; linarith),
        Set.indicator_of_mem (by constructor <;> [linarith; linarith])]
      have : T⁻¹ * ((0:ℝ) - 1) = -T⁻¹ := by ring
      rw [this]
      have : (0:ℝ) < T⁻¹ := by positivity
      linarith

/-! ## Causal formation histories of signed drift words -/

/-- One source intervention: a signed drift, a nonnegative delay, and a positive window width. -/
structure DriftEvent where
  drift : ℝ
  delay : ℝ
  width : ℝ

/-- The causal response of a single event. -/
def eventProfile (e : DriftEvent) : ℝ → ℝ := eventResponse e.drift e.delay e.width

/-- `(CJF.22)`  The formed causal history of a whole word is the convolution of its events. -/
def wordProfile : List DriftEvent → (ℝ → ℝ)
  | [] => fun _ => 0
  | [e] => eventProfile e
  | e :: rest => eventProfile e ⋆ wordProfile rest

/-- `(CJF.23)`  total delay of a word. -/
def totalDelay (w : List DriftEvent) : ℝ := (w.map DriftEvent.delay).sum

/-- `(CJF.23)`  total window width of a word. -/
def totalWidth (w : List DriftEvent) : ℝ := (w.map DriftEvent.width).sum

/-- The underlying signed drift word. -/
def drifts (w : List DriftEvent) : List ℝ := w.map DriftEvent.drift

/-- Sign carried immediately after the opening edge of a whole word. -/
def wordOpenSign (w : List DriftEvent) : ℝ := (w.map fun e => driftEdgeSign e.drift).prod

/-- Sign carried immediately before the closing edge of a whole word. -/
def wordCloseSign (w : List DriftEvent) : ℝ := (w.map fun e => -driftEdgeSign e.drift).prod

@[simp] theorem wordProfile_cons_cons (e e' : DriftEvent) (rest : List DriftEvent) :
    wordProfile (e :: e' :: rest) = eventProfile e ⋆ wordProfile (e' :: rest) := rfl

@[simp] theorem wordProfile_singleton (e : DriftEvent) : wordProfile [e] = eventProfile e := rfl

theorem integrable_wordProfile (w : List DriftEvent) : Integrable (wordProfile w) := by
  induction w with
  | nil => simp [wordProfile]
  | cons e rest ih =>
      cases rest with
      | nil => exact integrable_eventResponse _ _ _
      | cons e' rest' =>
          rw [wordProfile_cons_cons]
          exact (integrable_eventResponse _ _ _).integrable_convolution _ ih

theorem integrable_eventProfile_mul (e : DriftEvent) (rest : List DriftEvent) (x : ℝ) :
    Integrable (fun s => eventProfile e s * wordProfile rest (x - s)) :=
  integrable_mul_comp_sub (measurable_eventResponse _ _ _).aestronglyMeasurable
    (abs_eventResponse_le _ _ _) (integrable_wordProfile rest) x

/-- **Theorem 5.1, `(CJF.25)` opening half.**  The left endpoint of the essential support of the
formed causal history is exactly `B(w) - P(w)`. -/
theorem leftEdge_wordProfile (w : List DriftEvent) (hne : w ≠ [])
    (hδ : ∀ e ∈ w, e.drift ≠ 0) (hT : ∀ e ∈ w, 0 < e.width) :
    LeftEdge (wordProfile w) (totalDelay w - DriftWord.posLeg (drifts w)) (wordOpenSign w) := by
  induction w with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
      cases rest with
      | nil =>
          have h1 : totalDelay [e] - DriftWord.posLeg (drifts [e]) = e.delay - max e.drift 0 := by
            simp [totalDelay, drifts, DriftWord.posLeg]
          have h2 : wordOpenSign [e] = driftEdgeSign e.drift := by simp [wordOpenSign]
          rw [wordProfile_singleton, h1, h2]
          exact leftEdge_eventResponse (hδ e (by simp)) (hT e (by simp))
      | cons e' rest' =>
          have hrest := ih (by simp) (fun x hx => hδ x (by simp [hx]))
            (fun x hx => hT x (by simp [hx]))
          have hconv := (leftEdge_eventResponse (hδ e (by simp)) (hT e (by simp))).convolution
            hrest (integrable_eventProfile_mul e (e' :: rest'))
          have h1 : e.delay - max e.drift 0 +
              (totalDelay (e' :: rest') - DriftWord.posLeg (drifts (e' :: rest')))
              = totalDelay (e :: e' :: rest') - DriftWord.posLeg (drifts (e :: e' :: rest')) := by
            simp only [totalDelay, drifts, DriftWord.posLeg, List.map_cons, List.sum_cons]
            ring
          have h2 : driftEdgeSign e.drift * wordOpenSign (e' :: rest')
              = wordOpenSign (e :: e' :: rest') := by simp [wordOpenSign]
          rw [wordProfile_cons_cons, ← h1, ← h2]
          exact hconv

/-- **Theorem 5.1, `(CJF.25)` closing half.**  The right endpoint of the essential support is
exactly `B(w) + T(w) + N(w)`. -/
theorem rightEdge_wordProfile (w : List DriftEvent) (hne : w ≠ [])
    (hδ : ∀ e ∈ w, e.drift ≠ 0) (hT : ∀ e ∈ w, 0 < e.width) :
    RightEdge (wordProfile w)
      (totalDelay w + totalWidth w + DriftWord.negLeg (drifts w)) (wordCloseSign w) := by
  induction w with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
      cases rest with
      | nil =>
          have h1 : totalDelay [e] + totalWidth [e] + DriftWord.negLeg (drifts [e])
              = e.delay + e.width + max (-e.drift) 0 := by
            simp [totalDelay, totalWidth, drifts, DriftWord.negLeg]
          have h2 : wordCloseSign [e] = -driftEdgeSign e.drift := by simp [wordCloseSign]
          rw [wordProfile_singleton, h1, h2]
          exact rightEdge_eventResponse (hδ e (by simp)) (hT e (by simp))
      | cons e' rest' =>
          have hrest := ih (by simp) (fun x hx => hδ x (by simp [hx]))
            (fun x hx => hT x (by simp [hx]))
          have hconv := (rightEdge_eventResponse (hδ e (by simp)) (hT e (by simp))).convolution
            hrest (integrable_eventProfile_mul e (e' :: rest'))
          have h1 : e.delay + e.width + max (-e.drift) 0 +
              (totalDelay (e' :: rest') + totalWidth (e' :: rest')
                + DriftWord.negLeg (drifts (e' :: rest')))
              = totalDelay (e :: e' :: rest') + totalWidth (e :: e' :: rest')
                + DriftWord.negLeg (drifts (e :: e' :: rest')) := by
            simp only [totalDelay, totalWidth, drifts, DriftWord.negLeg, List.map_cons,
              List.sum_cons]
            ring
          have h2 : -driftEdgeSign e.drift * wordCloseSign (e' :: rest')
              = wordCloseSign (e :: e' :: rest') := by simp [wordCloseSign]
          rw [wordProfile_cons_cons, ← h1, ← h2]
          exact hconv

/-! ## Causal budgets and the functional-equation orientation -/

/-- `(CJF.25)`  Opening endpoint of the formed causal history. -/
def openEndpoint (w : List DriftEvent) : ℝ := totalDelay w - DriftWord.posLeg (drifts w)

/-- `(CJF.25)`  Closing endpoint of the formed causal history. -/
def closeEndpoint (w : List DriftEvent) : ℝ :=
  totalDelay w + totalWidth w + DriftWord.negLeg (drifts w)

/-- `(CJF.17)`  Functional-equation reflection of a whole event word. -/
def reflectEvents (w : List DriftEvent) : List DriftEvent :=
  w.map fun e => ⟨-e.drift, e.delay, e.width⟩

@[simp] theorem drifts_reflectEvents (w : List DriftEvent) :
    drifts (reflectEvents w) = DriftWord.reflectWord (drifts w) := by
  simp [drifts, reflectEvents, DriftWord.reflectWord, List.map_map, Function.comp_def]

@[simp] theorem totalDelay_reflectEvents (w : List DriftEvent) :
    totalDelay (reflectEvents w) = totalDelay w := by
  simp [totalDelay, reflectEvents, List.map_map, Function.comp_def]

@[simp] theorem totalWidth_reflectEvents (w : List DriftEvent) :
    totalWidth (reflectEvents w) = totalWidth w := by
  simp [totalWidth, reflectEvents, List.map_map, Function.comp_def]

/-- `(CJF.18)`  Reflection swaps the two causal endpoints' Jordan legs. -/
theorem openEndpoint_reflectEvents (w : List DriftEvent) :
    openEndpoint (reflectEvents w) = totalDelay w - DriftWord.negLeg (drifts w) := by
  simp [openEndpoint]

/-- **`(CJF.26)`.**  The formed support width is the total window width plus the total variation:
cancellation in the signed quotient is paid in full by causal support. -/
theorem closeEndpoint_sub_openEndpoint (w : List DriftEvent) :
    closeEndpoint w - openEndpoint w = totalWidth w + DriftWord.variation (drifts w) := by
  have h := DriftWord.posLeg_add_negLeg (drifts w)
  rw [closeEndpoint, openEndpoint]
  linarith

/-- **`(CJF.27)`.**  The formed history is causal exactly when the total delay covers the positive
leg. -/
theorem openEndpoint_nonneg_iff (w : List DriftEvent) :
    0 ≤ openEndpoint w ↔ DriftWord.posLeg (drifts w) ≤ totalDelay w := by
  rw [openEndpoint, sub_nonneg]

/-- **`(CJF.28)`, `(CJF.29)`.**  One delay admits a word and its functional-equation reflection
exactly when it covers the least common causal delay, which is the visible displacement plus the
hidden reserve. -/
theorem common_causal_iff (w : List DriftEvent) :
    (0 ≤ openEndpoint w ∧ 0 ≤ openEndpoint (reflectEvents w)) ↔
      DriftWord.commonDelay (drifts w) ≤ totalDelay w := by
  rw [openEndpoint_nonneg_iff, openEndpoint_reflectEvents, sub_nonneg, DriftWord.commonDelay,
    max_le_iff]

theorem commonDelay_drifts_eq (w : List DriftEvent) :
    DriftWord.commonDelay (drifts w)
      = |DriftWord.displacement (drifts w)| + DriftWord.reserve (drifts w) :=
  DriftWord.commonDelay_eq (drifts w)

/-- **Theorem 5.1 capstone.**  The formed causal history of a nonempty signed drift word has
essential-support endpoints exactly `B - P` and `B + T + N`; its support width is `T + V`; and one
delay admits both functional-equation orientations exactly when it covers `|D| + R`. -/
theorem titchmarshJordanFormation_certificate (w : List DriftEvent) (hne : w ≠ [])
    (hδ : ∀ e ∈ w, e.drift ≠ 0) (hT : ∀ e ∈ w, 0 < e.width) :
    LeftEdge (wordProfile w) (openEndpoint w) (wordOpenSign w) ∧
      RightEdge (wordProfile w) (closeEndpoint w) (wordCloseSign w) ∧
      closeEndpoint w - openEndpoint w = totalWidth w + DriftWord.variation (drifts w) ∧
      ((0 ≤ openEndpoint w ∧ 0 ≤ openEndpoint (reflectEvents w)) ↔
        |DriftWord.displacement (drifts w)| + DriftWord.reserve (drifts w) ≤ totalDelay w) := by
  refine ⟨leftEdge_wordProfile w hne hδ hT, rightEdge_wordProfile w hne hδ hT,
    closeEndpoint_sub_openEndpoint w, ?_⟩
  rw [common_causal_iff, commonDelay_drifts_eq]

/-! ## The bilateral Laplace transform of one event -/

theorem continuous_expWindow (z : ℂ) : Continuous fun t : ℝ => Complex.exp (-(z * t)) := by
  fun_prop

theorem integrable_expWindow (a T : ℝ) (z : ℂ) :
    Integrable ((Set.Ico a (a + T)).indicator fun t : ℝ => Complex.exp (-(z * t))) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact ((continuous_expWindow z).integrableOn_Icc (a := a) (b := a + T)).mono_set
    Set.Ico_subset_Icc_self

theorem integral_expWindow {a T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ≠ 0) :
    ∫ t in Set.Ico a (a + T), Complex.exp (-(z * t))
      = (Complex.exp (-(z * (a : ℂ))) - Complex.exp (-(z * ((a : ℂ) + (T : ℂ))))) / z := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hzz : (-z) ≠ 0 := neg_ne_zero.mpr hz
  have hcongr : (∫ t in a..a + T, Complex.exp (-(z * t)))
      = ∫ t in a..a + T, Complex.exp (-z * t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [neg_mul]
  rw [hcongr, integral_exp_mul_complex hzz]
  push_cast
  simp only [neg_mul]
  field_simp
  ring

/-- **`(CJF.21)`.**  The bilateral Laplace transform of the elementary event response is the
delayed product of a drift factor and a normalized window factor. -/
theorem laplace_eventResponse {δ b T : ℝ} (hT : 0 < T) {z : ℂ} (hz : z ≠ 0) :
    ∫ t : ℝ, (eventResponse δ b T t : ℂ) * Complex.exp (-(z * t))
      = Complex.exp (-(b * z)) * (Complex.exp (δ * z) - 1) *
        ((1 - Complex.exp (-(T * z))) / (T * z)) := by
  have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hfun : ∀ t : ℝ, ((eventResponse δ b T t : ℝ) : ℂ) * Complex.exp (-(z * t))
      = (T : ℂ)⁻¹ *
        (((Set.Ico (b - δ) (b - δ + T)).indicator (fun t : ℝ => Complex.exp (-(z * t))) t)
          - ((Set.Ico b (b + T)).indicator (fun t : ℝ => Complex.exp (-(z * t))) t)) := by
    intro t
    rw [eventResponse]
    by_cases h1 : t ∈ Set.Ico (b - δ) (b - δ + T) <;>
      by_cases h2 : t ∈ Set.Ico b (b + T) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2] <;> push_cast <;> ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_sub (integrable_expWindow (b - δ) T z)
    (integrable_expWindow b T z), integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ico, integral_expWindow hT.le hz,
    integral_expWindow hT.le hz]
  push_cast
  have e1 : Complex.exp (-(z * ((b : ℂ) - (δ : ℂ))))
      = Complex.exp (-((b : ℂ) * z)) * Complex.exp ((δ : ℂ) * z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-(z * ((b : ℂ) - (δ : ℂ) + (T : ℂ))))
      = Complex.exp (-((b : ℂ) * z)) * Complex.exp ((δ : ℂ) * z)
        * Complex.exp (-((T : ℂ) * z)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e3 : Complex.exp (-(z * (b : ℂ))) = Complex.exp (-((b : ℂ) * z)) := by congr 1; ring
  have e4 : Complex.exp (-(z * ((b : ℂ) + (T : ℂ))))
      = Complex.exp (-((b : ℂ) * z)) * Complex.exp (-((T : ℂ) * z)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2, e3, e4]
  field_simp

end

end GaloisForLFunctions.HTGeometry
