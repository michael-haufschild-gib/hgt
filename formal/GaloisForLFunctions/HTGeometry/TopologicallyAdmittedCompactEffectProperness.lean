import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabelSpectrum
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Complex.Liouville

/-!
# Compact-effect formation properness, singular category fracture and analytic escape

Let `μ₀, μ₁` be probability laws of full support on a compact space `X`.  No continuous effect
`e : X → [0, 1]` separates them perfectly: `|∫ e dμ₁ - ∫ e dμ₀| < 1`, and on a nonempty compact
family `E ⊆ C(X, [0, 1])` the contrast stays below `1 - η_E` with `η_E > 0`.  An exact depth-`d`
formation `K_d : X ⇝ Y^d` of a finite target pair `p₀, p₁` pulls a Neyman–Pearson event back to an
effect carrying the current `TV(p₀^{⊗d}, p₁^{⊗d}) ≥ 1 - A^d`, with `A` the Hellinger affinity.  If
the effects lie in `E` then `A^d ≥ η_E`, so `d ≤ log η_E / log A` when `0 < A < 1`, and a single
compact family forming every depth forces `p₀ = p₁`.  Hence nonneutral formation at unbounded depth
has non-relatively-compact, non-equicontinuous effects; uniformly Lipschitz effects, uniformly
bounded derivatives on an interval, or uniformly bounded holomorphic extensions are impossible.

For mutually singular laws every singular witness is dense with dense complement, and the kernel
switching between `p₁^{⊗d}` and `p₀^{⊗d}` on the witness is an exact measurable formation at every
depth whose nontrivial effects are discontinuous everywhere.  Homeomorphisms of the source and
bijections of the target preserve every quantity above.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Finite total variation -/

section FiniteTV

variable {Z : Type*} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Fintype Z] in
theorem measureReal_eq_sum_singleton (ρ : Measure Z) [IsFiniteMeasure ρ] (s : Finset Z) :
    ρ.real s = ∑ z ∈ s, ρ.real {z} := by
  rw [Measure.real_def, ← sum_measure_singleton,
    ENNReal.toReal_sum (fun z _ => measure_ne_top ρ _)]
  rfl

/-- **(TAF.9).**  `TV(u, v) = 1 - ∑_z min(u(z), v(z))` on a finite set. -/
theorem measurableHahnTV_eq_one_sub_sum_min (u v : Measure Z) [IsProbabilityMeasure u]
    [IsProbabilityMeasure v] :
    measurableHahnTV u v = 1 - ∑ z, min (u.real {z}) (v.real {z}) := by
  classical
  have htot : ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ], ∑ z, ρ.real {z} = 1 := by
    intro ρ _
    rw [← measureReal_eq_sum_singleton ρ Finset.univ, Finset.coe_univ, probReal_univ]
  apply le_antisymm
  · obtain ⟨⟨A, hA, hTV⟩, -⟩ := isGreatest_measurableHahnTV u v
    rw [hTV]
    have hAfin : A = ((A.toFinite.toFinset : Finset Z) : Set Z) := by simp
    rw [hAfin, measureReal_eq_sum_singleton v, measureReal_eq_sum_singleton u,
      ← Finset.sum_sub_distrib, ← htot v, ← Finset.sum_sub_distrib]
    calc ∑ z ∈ A.toFinite.toFinset, (v.real {z} - u.real {z})
        ≤ ∑ z ∈ A.toFinite.toFinset, (v.real {z} - min (u.real {z}) (v.real {z})) :=
          Finset.sum_le_sum fun z _ => by linarith [min_le_left (u.real {z}) (v.real {z})]
      _ ≤ ∑ z, (v.real {z} - min (u.real {z}) (v.real {z})) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun z _ _ => by linarith [min_le_right (u.real {z}) (v.real {z})]
  · set B : Finset Z := Finset.univ.filter fun z => u.real {z} ≤ v.real {z}
    have hBm : MeasurableSet (B : Set Z) := (B.finite_toSet).measurableSet
    have hTV := (isGreatest_measurableHahnTV u v).2 ⟨B, hBm, rfl⟩
    have hmin : 1 - (v.real B - u.real B) = ∑ z, min (u.real {z}) (v.real {z}) := by
      rw [measureReal_eq_sum_singleton v B, measureReal_eq_sum_singleton u B, ← htot v,
        ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun z => u.real {z} ≤ v.real {z}) (fun z => v.real {z}),
        ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun z => u.real {z} ≤ v.real {z}) (fun z => min (u.real {z}) (v.real {z}))]
      rw [Finset.sum_congr rfl fun z hz => min_eq_left (Finset.mem_filter.mp hz).2,
        Finset.sum_congr rfl fun z hz => min_eq_right (le_of_lt (not_le.mp
          (Finset.mem_filter.mp hz).2))]
      ring
    linarith

theorem hellingerAffinity_le_one (u v : Measure Z) [IsProbabilityMeasure u]
    [IsProbabilityMeasure v] : hellingerAffinity u v ≤ 1 := by
  have htot : ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ], ∑ z, ρ.real {z} = 1 := by
    intro ρ _
    rw [← measureReal_eq_sum_singleton ρ Finset.univ, Finset.coe_univ, probReal_univ]
  rw [hellingerAffinity, tsum_fintype]
  calc ∑ z, Real.sqrt ((u {z}).toReal * (v {z}).toReal)
      ≤ ∑ z, (u.real {z} + v.real {z}) / 2 :=
        Finset.sum_le_sum fun z _ => sqrt_mul_le_add_div_two measureReal_nonneg measureReal_nonneg
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, htot u, htot v]
        norm_num

/-- Equality in Cauchy–Schwarz: affinity one forces equal laws. -/
theorem eq_of_hellingerAffinity_eq_one (u v : Measure Z) [IsProbabilityMeasure u]
    [IsProbabilityMeasure v] (h : hellingerAffinity u v = 1) : u = v := by
  have htot : ∀ (ρ : Measure Z) [IsProbabilityMeasure ρ], ∑ z, ρ.real {z} = 1 := by
    intro ρ _
    rw [← measureReal_eq_sum_singleton ρ Finset.univ, Finset.coe_univ, probReal_univ]
  rw [hellingerAffinity, tsum_fintype] at h
  have hsq : ∑ z, (Real.sqrt (u.real {z}) - Real.sqrt (v.real {z})) ^ 2 = 0 := by
    have hexp : ∀ z, (Real.sqrt (u.real {z}) - Real.sqrt (v.real {z})) ^ 2
        = u.real {z} + v.real {z} - 2 * Real.sqrt ((u {z}).toReal * (v {z}).toReal) := by
      intro z
      rw [sub_sq, Real.sq_sqrt measureReal_nonneg, Real.sq_sqrt measureReal_nonneg,
        show (u {z}).toReal = u.real {z} from rfl, show (v {z}).toReal = v.real {z} from rfl,
        Real.sqrt_mul measureReal_nonneg]
      ring
    simp_rw [hexp]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h, htot u, htot v]
    norm_num
  have hz : ∀ z, u.real {z} = v.real {z} := by
    intro z
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => sq_nonneg
      (Real.sqrt (u.real {z}) - Real.sqrt (v.real {z}))).mp hsq z (Finset.mem_univ z)
    have h1 : Real.sqrt (u.real {z}) = Real.sqrt (v.real {z}) := by
      nlinarith [sq_nonneg (Real.sqrt (u.real {z}) - Real.sqrt (v.real {z}))]
    have := congrArg (· ^ 2) h1
    simpa [Real.sq_sqrt measureReal_nonneg] using this
  rw [Measure.ext_iff_singleton]
  intro z
  have := hz z
  rw [Measure.real_def, Measure.real_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top u _) (measure_ne_top v _)).mp this

/-- **(TAF.10).**  `TV(p₀^{⊗d}, p₁^{⊗d}) ≥ 1 - A^d`. -/
theorem one_sub_hellingerAffinity_pow_le {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (d : ℕ) :
    1 - hellingerAffinity p₀ p₁ ^ d
      ≤ measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁) := by
  rw [← hellingerAffinity_pi_const]
  have := one_sub_measurableHahnTV_le_hellingerAffinity (Measure.pi fun _ : Fin d => p₀)
    (Measure.pi fun _ : Fin d => p₁)
  linarith

end FiniteTV

/-! ## Exact formation -/

section Formation

variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- **(TAF.4).**  `K` forms `p^{⊗d}` exactly from `μ`: `∫ K(x, {y}) dμ = p^{⊗d}(y)`. -/
def IsExactFormation (μ : Measure X) {d : ℕ} (K : ProbabilityTheory.Kernel X (Fin d → Y))
    (p : Measure Y) : Prop :=
  ∀ y : Fin d → Y, ∫ x, (K x {y}).toReal ∂μ = (Measure.pi fun _ : Fin d => p).real {y}

theorem bind_eq_of_isExactFormation (μ : Measure X) [IsFiniteMeasure μ] {d : ℕ}
    (K : ProbabilityTheory.Kernel X (Fin d → Y)) [ProbabilityTheory.IsMarkovKernel K]
    (p : Measure Y) [IsProbabilityMeasure p] (h : IsExactFormation μ K p) :
    μ.bind K = Measure.pi fun _ : Fin d => p := by
  rw [Measure.ext_iff_singleton]
  intro y
  have hy := h y
  have hmeas : MeasurableSet ({y} : Set (Fin d → Y)) := measurableSet_singleton y
  rw [integral_toReal (K.measurable_coe hmeas).aemeasurable
    (Eventually.of_forall fun x => measure_lt_top (K x) _), ← Measure.bind_apply hmeas
    K.measurable.aemeasurable, Measure.real_def] at hy
  haveI : IsFiniteMeasure (μ.bind K) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
    simp
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hy

/-- **Theorem 4.1 (TAF.11).**  An exact formation pulls a Neyman–Pearson event back to an effect
carrying the full target current: `∫ e_d d(μ₁ - μ₀) = TV(p₀^{⊗d}, p₁^{⊗d}) ≥ 1 - A^d`. -/
theorem hahnEffectCurrent_formation (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] {d : ℕ} (K : ProbabilityTheory.Kernel X (Fin d → Y))
    [ProbabilityTheory.IsMarkovKernel K] (h₀ : IsExactFormation P K p₀)
    (h₁ : IsExactFormation Q K p₁) {B : Set (Fin d → Y)} (hB : MeasurableSet B)
    (hNP : (Measure.pi fun _ : Fin d => p₁).real B - (Measure.pi fun _ : Fin d => p₀).real B
      = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁)) :
    hahnEffectCurrent P Q (formationEffect K B)
        = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁) ∧
      1 - hellingerAffinity p₀ p₁ ^ d ≤ hahnEffectCurrent P Q (formationEffect K B) := by
  have hcur : hahnEffectCurrent P Q (formationEffect K B)
      = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁) := by
    rw [hahnEffectCurrent, integral_formationEffect Q K hB, integral_formationEffect P K hB,
      bind_eq_of_isExactFormation P K p₀ h₀, bind_eq_of_isExactFormation Q K p₁ h₁, hNP]
  exact ⟨hcur, hcur ▸ one_sub_hellingerAffinity_pow_le p₀ p₁ d⟩

end Formation

/-! ## The compact-effect gap -/

section Gap

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in
/-- A nonnegative continuous function with zero integral against a full-support law vanishes. -/
theorem eq_zero_of_integral_eq_zero (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hint : Integrable f μ)
    (h : ∫ x, f x ∂μ = 0) : ∀ x, f x = 0 := by
  have hae : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hf0 hint).mp h
  have := (Continuous.ae_eq_iff_eq μ hf continuous_const).mp hae
  exact fun x => congrFun this x

theorem integral_mem_Icc (μ : Measure X) [IsProbabilityMeasure μ] {e : X → ℝ}
    (he : Continuous e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    ∫ x, e x ∂μ ∈ Icc (0 : ℝ) 1 := by
  have hint : Integrable e μ := integrable_of_bound he.measurable (C := 1) fun x =>
    abs_le.mpr ⟨by linarith [(heb x).1], (heb x).2⟩
  refine ⟨integral_nonneg fun x => (heb x).1, ?_⟩
  calc ∫ x, e x ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := integral_mono hint (integrable_const 1) fun x => (heb x).2
    _ = 1 := by simp

/-- **Lemma 3.1 (TAF.6).**  No continuous effect separates two full-support laws perfectly. -/
theorem abs_hahnEffectCurrent_lt_one (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] {e : X → ℝ}
    (he : Continuous e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    |hahnEffectCurrent P Q e| < 1 := by
  have hint : ∀ (μ : Measure X) [IsProbabilityMeasure μ], Integrable e μ := fun μ _ =>
    integrable_of_bound he.measurable (C := 1) fun x =>
      abs_le.mpr ⟨by linarith [(heb x).1], (heb x).2⟩
  have hint1 : ∀ (μ : Measure X) [IsProbabilityMeasure μ], Integrable (fun x => 1 - e x) μ :=
    fun μ _ => (integrable_const 1).sub (hint μ)
  have hP := integral_mem_Icc P he heb
  have hQ := integral_mem_Icc Q he heb
  obtain ⟨x₀⟩ : Nonempty X := nonempty_of_isProbabilityMeasure P
  have hone : ∀ (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
      ∫ x, e x ∂μ = 1 → ∀ x, e x = 1 := by
    intro μ _ _ h1 x
    have h := eq_zero_of_integral_eq_zero μ (f := fun x => 1 - e x) (continuous_const.sub he)
      (fun x => by linarith [(heb x).2]) (hint1 μ) (by
        rw [integral_sub (integrable_const 1) (hint μ), h1]
        simp) x
    linarith
  have hzero : ∀ (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
      ∫ x, e x ∂μ = 0 → ∀ x, e x = 0 := fun μ _ _ h0 =>
    eq_zero_of_integral_eq_zero μ he (fun x => (heb x).1) (hint μ) h0
  rw [abs_lt, hahnEffectCurrent]
  by_contra hcon
  rw [not_and_or, not_lt, not_lt] at hcon
  rcases hcon with h | h
  · have h1 : ∫ x, e x ∂P = 1 := by linarith [hP.2, hQ.1]
    have h0 : ∫ x, e x ∂Q = 0 := by linarith [hP.2, hQ.1]
    have := (hone P h1 x₀).symm.trans (hzero Q h0 x₀)
    norm_num at this
  · have h1 : ∫ x, e x ∂Q = 1 := by linarith [hQ.2, hP.1]
    have h0 : ∫ x, e x ∂P = 0 := by linarith [hQ.2, hP.1]
    have := (hone Q h1 x₀).symm.trans (hzero P h0 x₀)
    norm_num at this

variable [CompactSpace X]

theorem abs_hahnEffectCurrent_sub_le (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (e e' : C(X, ℝ)) :
    |hahnEffectCurrent P Q e - hahnEffectCurrent P Q e'| ≤ 2 * ‖e - e'‖ := by
  have hint : ∀ (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X, ℝ)), Integrable f μ :=
    fun μ _ f => integrable_of_bound f.continuous.measurable (C := ‖f‖) fun x => by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hbd : ∀ (μ : Measure X) [IsProbabilityMeasure μ],
      |∫ x, e x ∂μ - ∫ x, e' x ∂μ| ≤ ‖e - e'‖ := by
    intro μ _
    rw [← integral_sub (hint μ e) (hint μ e')]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => e x - e' x)
      (C := ‖e - e'‖) (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using (e - e').norm_coe_le_norm x)
    simpa [Real.norm_eq_abs] using h
  have h1 := hbd Q
  have h2 := hbd P
  rw [hahnEffectCurrent, hahnEffectCurrent]
  calc |∫ x, e x ∂Q - ∫ x, e x ∂P - (∫ x, e' x ∂Q - ∫ x, e' x ∂P)|
      = |(∫ x, e x ∂Q - ∫ x, e' x ∂Q) - (∫ x, e x ∂P - ∫ x, e' x ∂P)| := by ring_nf
    _ ≤ |∫ x, e x ∂Q - ∫ x, e' x ∂Q| + |∫ x, e x ∂P - ∫ x, e' x ∂P| := abs_sub _ _
    _ ≤ 2 * ‖e - e'‖ := by linarith

theorem continuous_abs_hahnEffectCurrent (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    Continuous fun e : C(X, ℝ) => |hahnEffectCurrent P Q e| := by
  have hlip : LipschitzWith ⟨2, by norm_num⟩ fun e : C(X, ℝ) => hahnEffectCurrent P Q e :=
    LipschitzWith.of_dist_le_mul fun e e' => by
      rw [Real.dist_eq, dist_eq_norm]
      exact abs_hahnEffectCurrent_sub_le P Q e e'
  exact continuous_abs.comp hlip.continuous

/-- **(TAF.7).**  The gap `η_E = 1 - max_{e ∈ E} |∫ e d(μ₁ - μ₀)|` of an effect family. -/
def effectContrastGap (P Q : Measure X) (E : Set C(X, ℝ)) : ℝ :=
  1 - ⨆ e : E, |hahnEffectCurrent P Q e|

/-- **Lemma 3.2 (TAF.8).**  A nonempty compact family of continuous effects has a positive gap, and
every member's contrast is at most `1 - η_E`. -/
theorem effectContrastGap_pos (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] {E : Set C(X, ℝ)} (hEc : IsCompact E)
    (hEn : E.Nonempty) (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    0 < effectContrastGap P Q E ∧
      ∀ e ∈ E, |hahnEffectCurrent P Q e| ≤ 1 - effectContrastGap P Q E := by
  haveI : Nonempty E := hEn.to_subtype
  obtain ⟨e₀, he₀, hmax⟩ := hEc.exists_isMaxOn hEn
    (continuous_abs_hahnEffectCurrent P Q).continuousOn
  have hbdd : BddAbove (Set.range fun e : E => |hahnEffectCurrent P Q e|) :=
    ⟨|hahnEffectCurrent P Q e₀|, by rintro _ ⟨e, rfl⟩; exact hmax e.2⟩
  have hsup : ⨆ e : E, |hahnEffectCurrent P Q e| = |hahnEffectCurrent P Q e₀| :=
    le_antisymm (ciSup_le fun e => hmax e.2) (le_ciSup hbdd ⟨e₀, he₀⟩)
  refine ⟨?_, fun e he => ?_⟩
  · rw [effectContrastGap, hsup]
    have := abs_hahnEffectCurrent_lt_one P Q e₀.continuous (hb e₀ he₀)
    linarith
  · rw [effectContrastGap, sub_sub_cancel]
    exact le_ciSup hbdd ⟨e, he⟩

end Gap

/-! ## The depth bound -/

section DepthBound

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X]
variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- The Neyman–Pearson property of an event of `Y^d`. -/
def IsNeymanPearson (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁]
    {d : ℕ} (B : Set (Fin d → Y)) : Prop :=
  MeasurableSet B ∧
    (Measure.pi fun _ : Fin d => p₁).real B - (Measure.pi fun _ : Fin d => p₀).real B
      = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁)

/-- An exact depth-`d` formation whose Neyman–Pearson effect lies in `F`. -/
def FormsInFamily (P Q : Measure X) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (F : Set C(X, ℝ)) (d : ℕ) : Prop :=
  ∃ K : ProbabilityTheory.Kernel X (Fin d → Y), ProbabilityTheory.IsMarkovKernel K ∧
    IsExactFormation P K p₀ ∧ IsExactFormation Q K p₁ ∧
    ∃ B : Set (Fin d → Y), IsNeymanPearson p₀ p₁ B ∧
      ∃ f ∈ F, ∀ x, f x = formationEffect K B x

/-- **Theorem 5.1.**  If an exact depth-`d` formation has its Neyman–Pearson effect in a compact
family `E`, then `A^d ≥ η_E`. -/
theorem effectContrastGap_le_pow (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {E : Set C(X, ℝ)} (hEc : IsCompact E)
    (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1) {d : ℕ} (hform : FormsInFamily P Q p₀ p₁ E d) :
    effectContrastGap P Q E ≤ hellingerAffinity p₀ p₁ ^ d := by
  obtain ⟨K, hK, h₀, h₁, B, ⟨hB, hNP⟩, f, hfE, hf⟩ := hform
  have hcur := hahnEffectCurrent_formation P Q p₀ p₁ K h₀ h₁ hB hNP
  have hgap := (effectContrastGap_pos P Q hEc ⟨f, hfE⟩ hb).2 f hfE
  have hfeq : hahnEffectCurrent P Q f = hahnEffectCurrent P Q (formationEffect K B) := by
    rw [hahnEffectCurrent, hahnEffectCurrent]
    simp_rw [hf]
  rw [hfeq] at hgap
  have := le_abs_self (hahnEffectCurrent P Q (formationEffect K B))
  linarith [hcur.2]

/-- **Theorem 5.1 (TAF.12).**  `d ≤ log η_E / log A` when `0 < A < 1`. -/
theorem formation_depth_le_log (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {E : Set C(X, ℝ)} (hEc : IsCompact E)
    (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1) {d : ℕ} (hform : FormsInFamily P Q p₀ p₁ E d)
    (hA0 : 0 < hellingerAffinity p₀ p₁) (hA1 : hellingerAffinity p₀ p₁ < 1) :
    (d : ℝ) ≤ Real.log (effectContrastGap P Q E) / Real.log (hellingerAffinity p₀ p₁) := by
  obtain ⟨K, hK, h₀, h₁, B, hNP, f, hfE, hf⟩ := hform
  have hη := effectContrastGap_le_pow P Q p₀ p₁ hEc hb ⟨K, hK, h₀, h₁, B, hNP, f, hfE, hf⟩
  have hpos := (effectContrastGap_pos P Q hEc ⟨f, hfE⟩ hb).1
  have hlog := Real.log_le_log hpos hη
  rw [Real.log_pow] at hlog
  rw [le_div_iff_of_neg (Real.log_neg hA0 hA1)]
  linarith

/-- **Theorem 5.1, rigidity.**  One compact family admitting formations of arbitrarily large
depth forces `p₀ = p₁`. -/
theorem eq_of_formsInFamily_unbounded (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {E : Set C(X, ℝ)} (hEc : IsCompact E)
    (hb : ∀ e ∈ E, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ E d) : p₀ = p₁ := by
  obtain ⟨d₀, -, K₀, -, -, -, B₀, -, f₀, hf₀E, -⟩ := hform 0
  have hpos := (effectContrastGap_pos P Q hEc ⟨f₀, hf₀E⟩ hb).1
  have hA1 := hellingerAffinity_le_one p₀ p₁
  have hA0 := hellingerAffinity_nonneg p₀ p₁
  rcases hA1.lt_or_eq with hlt | heq
  · exfalso
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hA0 hlt
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    obtain ⟨d, hd, hformd⟩ := hform N
    have := effectContrastGap_le_pow P Q p₀ p₁ hEc hb hformd
    linarith [hN d hd]
  · exact eq_of_hellingerAffinity_eq_one p₀ p₁ heq

omit [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X] in
theorem isClosed_effects : IsClosed {f : C(X, ℝ) | ∀ x, f x ∈ Icc (0 : ℝ) 1} := by
  have : {f : C(X, ℝ) | ∀ x, f x ∈ Icc (0 : ℝ) 1} = ⋂ x, (fun f : C(X, ℝ) => f x) ⁻¹' Icc 0 1 := by
    ext f
    simp
  rw [this]
  exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)

/-- **Corollary 5.2.**  Nonneutral exact formation at unbounded depth has an effect family that is
not relatively compact. -/
theorem not_isCompact_closure_of_formsInFamily (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {F : Set C(X, ℝ)}
    (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ F d) : ¬ IsCompact (closure F) := by
  intro hc
  have hbE : ∀ e ∈ closure F, ∀ x, e x ∈ Icc (0 : ℝ) 1 := fun e he =>
    closure_minimal (fun f hf => hb f hf) isClosed_effects he
  refine hne (eq_of_formsInFamily_unbounded P Q p₀ p₁ hc hbE fun N => ?_)
  obtain ⟨d, hd, K, hK, h₀, h₁, B, hNP, f, hfF, hf⟩ := hform N
  exact ⟨d, hd, K, hK, h₀, h₁, B, hNP, f, subset_closure hfF, hf⟩

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Arzelà–Ascoli for `[0, 1]`-valued continuous functions on a compact space. -/
theorem isCompact_closure_of_equicontinuous {F : Set C(X, ℝ)}
    (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hF : Equicontinuous fun f : F => ((f : C(X, ℝ)) : X → ℝ)) : IsCompact (closure F) := by
  set Φ := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  set A : Set (X →ᵇ ℝ) := Φ '' F
  have hA : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) 1) isCompact_Icc A ?_ ?_
    · rintro _ x ⟨f, hf, rfl⟩
      exact hb f hf x
    · intro x U hU
      filter_upwards [hF x U hU] with x' hx'
      rintro ⟨_, ⟨f, hf, rfl⟩⟩
      exact hx' ⟨f, hf⟩
  have hcl : closure F = Φ.symm '' closure A := by
    have h1 : closure A = Φ '' closure F := by
      have := Φ.toHomeomorph.image_closure F
      simpa using this.symm
    rw [h1, Set.image_image]
    simp
  rw [hcl]
  exact hA.image Φ.symm.continuous

/-- **Corollary 5.2 (TAF.13).**  The pulled-back decision effects are not equicontinuous. -/
theorem not_equicontinuous_of_formsInFamily (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {F : Set C(X, ℝ)}
    (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ F d) :
    ¬ Equicontinuous fun f : F => ((f : C(X, ℝ)) : X → ℝ) := fun hF =>
  not_isCompact_closure_of_formsInFamily P Q p₀ p₁ hne hb hform
    (isCompact_closure_of_equicontinuous hb hF)

end DepthBound

/-! ## Singular category fracture -/

section Singular

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **Lemma 6.1.**  Every singular witness of two full-support laws is dense with dense
complement. -/
theorem dense_nullSet_of_singular {P Q : Measure X} [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    (hPQ : P ⟂ₘ Q) : Dense hPQ.nullSet ∧ Dense hPQ.nullSetᶜ := by
  constructor
  · rw [dense_iff_inter_open]
    intro U hU hne
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hsub : U ⊆ hPQ.nullSetᶜ := fun x hx hxS =>
      (Set.eq_empty_iff_forall_notMem.mp hemp) x ⟨hx, hxS⟩
    have := (hU.measure_pos Q hne).trans_le (measure_mono hsub)
    rw [hPQ.measure_compl_nullSet] at this
    exact lt_irrefl _ this
  · rw [dense_iff_inter_open]
    intro U hU hne
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hsub : U ⊆ hPQ.nullSet := fun x hx => by
      by_contra hxS
      exact (Set.eq_empty_iff_forall_notMem.mp hemp) x ⟨hx, hxS⟩
    have := (hU.measure_pos P hne).trans_le (measure_mono hsub)
    rw [hPQ.measure_nullSet] at this
    exact lt_irrefl _ this

omit [MeasurableSpace X] in
/-- A function with two distinct constant values on complementary dense sets is continuous
nowhere. -/
theorem not_continuousAt_of_dense_values {S : Set X} (hS : Dense S) (hSc : Dense Sᶜ) {f : X → ℝ}
    {a b : ℝ} (ha : ∀ x ∈ S, f x = a) (hb : ∀ x ∉ S, f x = b) (hab : a ≠ b) (x : X) :
    ¬ ContinuousAt f x := by
  intro hx
  have hε : 0 < |a - b| / 2 := by
    have := abs_pos.mpr (sub_ne_zero.mpr hab)
    linarith
  have hball := hx (Metric.ball_mem_nhds (f x) hε)
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hball
  obtain ⟨y, hyU, hyS⟩ := hS.inter_open_nonempty U hUo ⟨x, hxU⟩
  obtain ⟨z, hzU, hzS⟩ := hSc.inter_open_nonempty U hUo ⟨x, hxU⟩
  have hy := hUsub hyU
  have hz := hUsub hzU
  simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hy hz
  rw [ha y hyS] at hy
  rw [hb z hzS] at hz
  have : |a - b| < |a - b| := calc
    |a - b| = |(a - f x) - (b - f x)| := by ring_nf
    _ ≤ |a - f x| + |b - f x| := abs_sub _ _
    _ < |a - b| / 2 + |a - b| / 2 := add_lt_add hy hz
    _ = |a - b| := by ring
  exact lt_irrefl _ this

/-- The indicator of a singular witness is continuous nowhere. -/
theorem not_continuousAt_indicator_nullSet {P Q : Measure X} [P.IsOpenPosMeasure]
    [Q.IsOpenPosMeasure] (hPQ : P ⟂ₘ Q) (x : X) :
    ¬ ContinuousAt (hPQ.nullSet.indicator fun _ => (1 : ℝ)) x :=
  not_continuousAt_of_dense_values (dense_nullSet_of_singular hPQ).1
    (dense_nullSet_of_singular hPQ).2 (a := 1) (b := 0)
    (fun _y hy => indicator_of_mem hy _) (fun _y hy => indicator_of_notMem hy _) one_ne_zero x

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

open Classical in
/-- **(TAF.15).**  The kernel `x ↦ p₁^{⊗d}` on the singular witness and `p₀^{⊗d}` off it. -/
def singularWitnessFormation {P Q : Measure X} (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) (d : ℕ) :
    ProbabilityTheory.Kernel X (Fin d → Y) :=
  ProbabilityTheory.Kernel.piecewise hPQ.measurableSet_nullSet
    (ProbabilityTheory.Kernel.const X (Measure.pi fun _ : Fin d => p₁))
    (ProbabilityTheory.Kernel.const X (Measure.pi fun _ : Fin d => p₀))

instance {P Q : Measure X} (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (d : ℕ) :
    ProbabilityTheory.IsMarkovKernel (singularWitnessFormation hPQ p₀ p₁ d) := by
  unfold singularWitnessFormation
  infer_instance

omit [TopologicalSpace X] [Fintype Y] [MeasurableSingletonClass Y] in
open Classical in
theorem singularWitnessFormation_apply {P Q : Measure X} (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) (d : ℕ)
    (x : X) : singularWitnessFormation hPQ p₀ p₁ d x
      = if x ∈ hPQ.nullSet then Measure.pi (fun _ : Fin d => p₁)
        else Measure.pi (fun _ : Fin d => p₀) := by
  rw [singularWitnessFormation, ProbabilityTheory.Kernel.piecewise_apply]
  split_ifs <;> rfl

omit [TopologicalSpace X] [Fintype Y] [MeasurableSingletonClass Y] in
/-- **Theorem 6.2.**  The singular kernel is an exact measurable formation at every depth. -/
theorem isExactFormation_singularWitnessFormation {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (d : ℕ) :
    IsExactFormation P (singularWitnessFormation hPQ p₀ p₁ d) p₀ ∧
      IsExactFormation Q (singularWitnessFormation hPQ p₀ p₁ d) p₁ := by
  have hP : ∀ᵐ x ∂P, x ∉ hPQ.nullSet := by
    rw [ae_iff]
    simp
  have hQ : ∀ᵐ x ∂Q, x ∈ hPQ.nullSet := by
    rw [ae_iff]
    exact hPQ.measure_compl_nullSet
  constructor
  · intro y
    rw [integral_congr_ae (g := fun _ => ((Measure.pi fun _ : Fin d => p₀) {y}).toReal)]
    · simp [Measure.real_def]
    · filter_upwards [hP] with x hx
      rw [singularWitnessFormation_apply, if_neg hx]
  · intro y
    rw [integral_congr_ae (g := fun _ => ((Measure.pi fun _ : Fin d => p₁) {y}).toReal)]
    · simp [Measure.real_def]
    · filter_upwards [hQ] with x hx
      rw [singularWitnessFormation_apply, if_pos hx]

/-- **Theorem 6.2, escape.**  If `p₀ ≠ p₁` and `d > 0`, some event of `Y^d` pulls back to an
effect that is continuous at no point. -/
theorem exists_nowhere_continuous_singularWitnessFormation {P Q : Measure X} [P.IsOpenPosMeasure]
    [Q.IsOpenPosMeasure] (hPQ : P ⟂ₘ Q) (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {d : ℕ} (hd : 0 < d) :
    ∃ B : Set (Fin d → Y), MeasurableSet B ∧
      ∀ x, ¬ ContinuousAt (formationEffect (singularWitnessFormation hPQ p₀ p₁ d) B) x := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, p₀ {z} ≠ p₁ {z} := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hne (Measure.ext_iff_singleton.mpr h)
  set i₀ : Fin d := ⟨0, hd⟩
  set B : Set (Fin d → Y) := Function.eval i₀ ⁻¹' {z}
  have hBm : MeasurableSet B := (measurable_pi_apply i₀) (measurableSet_singleton z)
  have hpi : ∀ (p : Measure Y) [IsProbabilityMeasure p],
      (Measure.pi fun _ : Fin d => p) B = p {z} :=
    fun p _ => (measurePreserving_eval (fun _ : Fin d => p) i₀).measure_preimage
      (measurableSet_singleton z).nullMeasurableSet
  refine ⟨B, hBm, fun x => ?_⟩
  refine not_continuousAt_of_dense_values (dense_nullSet_of_singular hPQ).1
    (dense_nullSet_of_singular hPQ).2 (a := (p₁ {z}).toReal) (b := (p₀ {z}).toReal)
    (fun y hy => ?_) (fun y hy => ?_) ?_ x
  · rw [formationEffect, singularWitnessFormation_apply, if_pos hy, hpi]
  · rw [formationEffect, singularWitnessFormation_apply, if_neg hy, hpi]
  · intro h
    exact hz ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h).symm

end Singular

/-! ## Functional-equation neutrality -/

section Neutrality

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Pulling back by a homeomorphism is an isometry of the uniform norm. -/
theorem norm_comp_homeomorph [CompactSpace X] (h : X ≃ₜ X) (e : C(X, ℝ)) :
    ‖e.comp (h.symm : C(X, X))‖ = ‖e‖ := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg e)).mpr fun x => e.norm_coe_le_norm _
  · have h1 : e = (e.comp (h.symm : C(X, X))).comp (h : C(X, X)) := by
      ext x
      simp
    conv_lhs => rw [h1]
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x =>
      (e.comp (h.symm : C(X, X))).norm_coe_le_norm _

/-- Contrast is invariant under transport of the source by a homeomorphism. -/
theorem hahnEffectCurrent_homeomorph (P Q : Measure X) (h : X ≃ₜ X) {e : X → ℝ}
    (he : Measurable e) :
    hahnEffectCurrent (P.map h) (Q.map h) (e ∘ h.symm) = hahnEffectCurrent P Q e := by
  rw [← hahnEffectCurrent_comp P Q h.measurable (he.comp h.symm.measurable)]
  congr 1
  funext x
  simp

/-- Full support is transported by a homeomorphism. -/
theorem isOpenPosMeasure_map_homeomorph (P : Measure X) [P.IsOpenPosMeasure] (h : X ≃ₜ X) :
    (P.map h).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [Measure.map_apply h.measurable hU.measurableSet]
  exact (hU.preimage h.continuous).measure_ne_zero P (hne.preimage h.surjective)

/-- Exact formation is transported by precomposing the kernel with the inverse homeomorphism. -/
theorem isExactFormation_homeomorph {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (μ : Measure X) (h : X ≃ₜ X) {d : ℕ}
    (K : ProbabilityTheory.Kernel X (Fin d → Y)) (p : Measure Y) (hK : IsExactFormation μ K p) :
    IsExactFormation (μ.map h) (K.comap h.symm h.symm.measurable) p := by
  intro y
  have := integral_map_equiv (h.toMeasurableEquiv) (μ := μ)
    (fun x => ((K.comap h.symm h.symm.measurable) x {y}).toReal)
  simp only [Homeomorph.toMeasurableEquiv_coe] at this
  rw [this]
  simpa [ProbabilityTheory.Kernel.comap_apply] using hK y

/-- The compact-effect gap is invariant under a homeomorphism of the source. -/
theorem effectContrastGap_homeomorph [OpensMeasurableSpace X] (P Q : Measure X) (h : X ≃ₜ X)
    (E : Set C(X, ℝ)) :
    effectContrastGap (P.map h) (Q.map h) ((fun e : C(X, ℝ) => e.comp (h.symm : C(X, X))) '' E)
      = effectContrastGap P Q E := by
  rw [effectContrastGap, effectContrastGap]
  congr 1
  simp only [iSup]
  congr 1
  ext r
  constructor
  · rintro ⟨⟨_, ⟨e, he, rfl⟩⟩, rfl⟩
    refine ⟨⟨e, he⟩, ?_⟩
    change |hahnEffectCurrent P Q e| = |hahnEffectCurrent (P.map h) (Q.map h) (e ∘ h.symm)|
    rw [hahnEffectCurrent_homeomorph P Q h e.continuous.measurable]
  · rintro ⟨⟨e, he⟩, rfl⟩
    refine ⟨⟨e.comp (h.symm : C(X, X)), ⟨e, he, rfl⟩⟩, ?_⟩
    change |hahnEffectCurrent (P.map h) (Q.map h) (e ∘ h.symm)| = |hahnEffectCurrent P Q e|
    rw [hahnEffectCurrent_homeomorph P Q h e.continuous.measurable]

/-- A bijection of the finite target preserves the tensor total variation. -/
theorem measurableHahnTV_pi_map_equiv {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (β : Y ≃ Y) (d : ℕ) :
    measurableHahnTV (Measure.pi fun _ : Fin d => p₀.map β)
        (Measure.pi fun _ : Fin d => p₁.map β)
      = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁) := by
  let βm : Y ≃ᵐ Y := ⟨β, measurable_of_countable _, measurable_of_countable _⟩
  have hmap : ∀ (p : Measure Y) [IsProbabilityMeasure p],
      (Measure.pi fun _ : Fin d => p.map β)
        = (Measure.pi fun _ : Fin d => p).map (MeasurableEquiv.piCongrRight fun _ => βm) := by
    intro p _
    haveI : ∀ _ : Fin d, SigmaFinite (p.map β) := fun _ =>
      (Measure.isFiniteMeasure_map p β).toSigmaFinite
    rw [show ((MeasurableEquiv.piCongrRight fun _ => βm) : (Fin d → Y) → Fin d → Y)
        = fun y i => β (y i) from rfl,
      Measure.pi_map_pi (fun _ => (measurable_of_countable (β : Y → Y)).aemeasurable)]
  have h := measurableHahnTV_map_equiv (Measure.pi fun _ : Fin d => p₀)
    (Measure.pi fun _ : Fin d => p₁) (MeasurableEquiv.piCongrRight fun _ => βm)
  simp only [← hmap] at h
  exact h

end Neutrality

/-! ## Analytic and prolongation escape -/

section Escape

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- **Corollary 8.1.**  Nonneutral exact formation at unbounded depth admits no common Lipschitz
bound for its effects. -/
theorem not_uniformly_lipschitz_of_formsInFamily (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure] (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁) {F : Set C(X, ℝ)}
    (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ F d) :
    ¬ ∃ L : ℝ≥0, ∀ f ∈ F, LipschitzWith L f := by
  rintro ⟨L, hL⟩
  exact not_equicontinuous_of_formsInFamily P Q p₀ p₁ hne hb hform
    (LipschitzWith.uniformEquicontinuous _ L fun (f : F) => hL f f.2).equicontinuous

/-- **(TAF.17).**  On a compact interval, effects realized by differentiable functions with a
common derivative bound cannot carry nonneutral formation to unbounded depth. -/
theorem not_bounded_deriv_of_formsInFamily {a b : ℝ} (P Q : Measure (Icc a b))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁)
    {F : Set C(Icc a b, ℝ)} (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ F d) :
    ¬ ∃ M : ℝ≥0, ∀ f ∈ F, ∃ g : ℝ → ℝ, (∀ x : Icc a b, f x = g x) ∧
      (∀ x ∈ Icc a b, DifferentiableAt ℝ g x) ∧ ∀ x ∈ Icc a b, ‖deriv g x‖₊ ≤ M := by
  rintro ⟨M, hM⟩
  refine not_uniformly_lipschitz_of_formsInFamily P Q p₀ p₁ hne hb hform ⟨M, fun f hf => ?_⟩
  obtain ⟨g, hfg, hgd, hgM⟩ := hM f hf
  have hlip := (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hgd hgM |>.to_restrict
  have : (f : Icc a b → ℝ) = (Icc a b).restrict g := by
    funext x
    exact hfg x
  rw [this]
  exact hlip

/-- Uniformly bounded holomorphic extensions to one neighbourhood give a common Lipschitz bound on
a compact real set. -/
theorem exists_lipschitz_of_holomorphic_bound {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ}
    (hU : IsOpen U) (hKU : (fun x : ℝ => (x : ℂ)) '' K ⊆ U) {M : ℝ}
    {F : Set C(K, ℝ)} (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hG : ∀ f ∈ F, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z ∈ U, ‖G z‖ ≤ M) ∧
      ∀ x : K, G (x : ℂ) = (f x : ℂ)) :
    ∃ L : ℝ≥0, ∀ f ∈ F, LipschitzWith L f := by
  set K' : Set ℂ := (fun x : ℝ => (x : ℂ)) '' K
  have hK' : IsCompact K' := hK.image Complex.continuous_ofReal
  obtain ⟨δ, hδ, hsub⟩ := hK'.exists_cthickening_subset_open hU hKU
  set r : ℝ := δ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hball : ∀ z ∈ Metric.cthickening r K', Metric.closedBall z r ⊆ U := by
    intro z hz
    refine (Metric.closedBall_subset_cthickening hz r).trans ?_
    refine (Metric.cthickening_cthickening_subset hr.le hr.le K').trans ?_
    rw [show r + r = δ by rw [hrdef]; ring]
    exact hsub
  refine ⟨(max M 1 / r).toNNReal, fun f hf => ?_⟩
  obtain ⟨G, hGd, hGM, hGf⟩ := hG f hf
  have hderiv : ∀ z ∈ Metric.cthickening r K', ‖deriv G z‖ ≤ M / r := by
    intro z hz
    have hcl : DifferentiableOn ℂ G (closure (Metric.ball z r)) := by
      rw [closure_ball z hr.ne']
      exact hGd.mono (hball z hz)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl.diffContOnCl
      fun w hw => hGM w (hball z hz (Metric.sphere_subset_closedBall hw))
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
  rcases le_or_gt |(x : ℝ) - y| r with hxy | hxy
  · have hxK : ((x : ℝ) : ℂ) ∈ K' := ⟨x, x.2, rfl⟩
    have hs : Metric.closedBall ((x : ℝ) : ℂ) r ⊆ Metric.cthickening r K' :=
      Metric.closedBall_subset_cthickening hxK r
    have hdiff : ∀ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, DifferentiableAt ℂ G z := fun z hz =>
      hGd.differentiableAt (hU.mem_nhds (hball _ (Metric.mem_cthickening_of_dist_le _ _ _ _ hxK
        (Metric.mem_closedBall.mp hz)) (Metric.mem_closedBall_self hr.le)))
    have hy : ((y : ℝ) : ℂ) ∈ Metric.closedBall ((x : ℝ) : ℂ) r := by
      rw [Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]
      exact hxy
    have h := (convex_closedBall ((x : ℝ) : ℂ) r).norm_image_sub_le_of_norm_deriv_le hdiff
      (fun z hz => hderiv z (hs hz)) (Metric.mem_closedBall_self hr.le) hy
    rw [hGf x, hGf y, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_sub_comm (f x), abs_sub_comm (x : ℝ)] at *
    calc |f y - f x| ≤ M / r * |(y : ℝ) - x| := h
      _ ≤ max M 1 / r * |(y : ℝ) - x| := by
          gcongr
          exact le_max_left _ _
  · have h1 : |f x - f y| ≤ 1 := by
      obtain ⟨hx0, hx1⟩ := hb f hf x
      obtain ⟨hy0, hy1⟩ := hb f hf y
      rw [abs_le]
      constructor <;> linarith
    calc |f x - f y| ≤ 1 := h1
      _ ≤ max M 1 / r * |(x : ℝ) - y| := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr]
          calc 1 * r ≤ 1 * |(x : ℝ) - y| := by linarith
            _ ≤ max M 1 * |(x : ℝ) - y| := by gcongr; exact le_max_right _ _

/-- **Corollary 8.2.**  If the effects extend holomorphically to one fixed complex neighbourhood of
a compact real source set with a uniform bound, nonneutral formation at unbounded depth is
impossible. -/
theorem not_holomorphic_bound_of_formsInFamily {K : Set ℝ} (hK : IsCompact K)
    [MeasurableSpace K] [BorelSpace K] (P Q : Measure K) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁)
    {F : Set C(K, ℝ)} (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hform : ∀ N : ℕ, ∃ d ≥ N, FormsInFamily P Q p₀ p₁ F d) {U : Set ℂ} (hU : IsOpen U)
    (hKU : (fun x : ℝ => (x : ℂ)) '' K ⊆ U) :
    ¬ ∃ M : ℝ, ∀ f ∈ F, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z ∈ U, ‖G z‖ ≤ M) ∧
      ∀ x : K, G (x : ℂ) = (f x : ℂ) := by
  rintro ⟨M, hG⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact not_uniformly_lipschitz_of_formsInFamily P Q p₀ p₁ hne hb hform
    (exists_lipschitz_of_holomorphic_bound hK hU hKU hb hG)

end Escape

end GaloisForLFunctions.HTGeometry
