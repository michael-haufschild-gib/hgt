import Mathlib

/-!
# Finite Feller admission chamber

Lean infrastructure for ULF-TAFM-4. Finite-output Feller kernels are continuous simplex-valued
maps. Full source support forces the two pushed target laws to have exactly the same zero
coordinates. The converse classification is developed from singular separation and convex
exactification below.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/finite-feller-admission-chamber-and-cofinal-resolution-fracture-law.md`.
-/

open MeasureTheory
open Topology
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- A finite Feller kernel, represented by continuous unit-interval coordinates summing to one. -/
structure FiniteFellerKernel (X : Type u) (Y : Type v) [TopologicalSpace X] [Fintype Y] where
  coord : Y → C(X, unitInterval)
  sum_coord : ∀ x, ∑ y, ((coord y x : unitInterval) : ℝ) = 1

namespace FiniteFellerKernel

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fintype Y]

theorem coord_integrable (K : FiniteFellerKernel X Y) (μ : Measure X)
    [IsFiniteMeasure μ] (y : Y) :
    Integrable (fun x => ((K.coord y x : unitInterval) : ℝ)) μ := by
  have hcont : Continuous (fun x => ((K.coord y x : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp (K.coord y).continuous
  apply Integrable.of_bound hcont.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (K.coord y x).2.2
  · exact (K.coord y x).2.1

/-- Coordinate mass of the pushed finite law. -/
def pushMass (K : FiniteFellerKernel X Y) (μ : Measure X) (y : Y) : ℝ :=
  ∫ x, ((K.coord y x : unitInterval) : ℝ) ∂μ

omit [BorelSpace X] in
theorem pushMass_nonneg (K : FiniteFellerKernel X Y) (μ : Measure X)
    [IsFiniteMeasure μ] (y : Y) :
    0 ≤ K.pushMass μ y :=
  integral_nonneg fun x => (K.coord y x).2.1

theorem sum_pushMass (K : FiniteFellerKernel X Y) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    ∑ y, K.pushMass μ y = 1 := by
  simp only [pushMass]
  rw [← integral_finsetSum]
  · simp only [K.sum_coord]
    simp
  · intro y _
    exact K.coord_integrable μ y

/- Continuous almost-everywhere zero function vanishes on the whole support. -/
omit [BorelSpace X] in
theorem continuous_eq_zero_on_support {f : X → ℝ} (hf : Continuous f)
    (μ : Measure X) (hfzero : f =ᵐ[μ] 0) :
    ∀ x ∈ μ.support, f x = 0 := by
  intro x hx
  by_contra hfx
  have hopen : IsOpen {z : X | f z ≠ 0} :=
    (isClosed_eq hf continuous_const).isOpen_compl
  have hnhds : {z : X | f z ≠ 0} ∈ 𝓝 x :=
    hopen.mem_nhds hfx
  have hpos : 0 < μ {z : X | f z ≠ 0} :=
    (Measure.mem_support_iff_forall x).mp hx _ hnhds
  have hnull : μ {z : X | f z ≠ 0} = 0 := by
    change μ ({z : X | f z = 0}ᶜ) = 0
    exact mem_ae_iff.mp hfzero
  exact hpos.ne' hnull

/-- A nonnegative continuous Feller coordinate with zero full-support integral is identically zero. -/
theorem coord_eq_zero_of_pushMass_eq_zero (K : FiniteFellerKernel X Y)
    (μ : Measure X) [IsFiniteMeasure μ] (hfull : μ.support = Set.univ)
    (y : Y) (hy : K.pushMass μ y = 0) :
    ∀ x, ((K.coord y x : unitInterval) : ℝ) = 0 := by
  have hae :
      (fun x => ((K.coord y x : unitInterval) : ℝ)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => (K.coord y x).2.1) (K.coord_integrable μ y)).mp hy
  intro x
  apply continuous_eq_zero_on_support
    (continuous_subtype_val.comp (K.coord y).continuous) μ hae x
  rw [hfull]
  exact Set.mem_univ x

omit [BorelSpace X] in
theorem pushMass_eq_zero_of_coord_eq_zero (K : FiniteFellerKernel X Y)
    (μ : Measure X) (y : Y)
    (hy : ∀ x, ((K.coord y x : unitInterval) : ℝ) = 0) :
    K.pushMass μ y = 0 := by
  rw [pushMass]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  exact hy x

/-- Necessity half of the admission-chamber theorem: pushed zero sets agree exactly. -/
theorem pushMass_eq_zero_iff_of_fullSupport (K : FiniteFellerKernel X Y)
    (μ₀ μ₁ : Measure X) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (y : Y) :
    K.pushMass μ₀ y = 0 ↔ K.pushMass μ₁ y = 0 := by
  constructor
  · intro h
    exact K.pushMass_eq_zero_of_coord_eq_zero μ₁ y
      (K.coord_eq_zero_of_pushMass_eq_zero μ₀ hfull₀ y h)
  · intro h
    exact K.pushMass_eq_zero_of_coord_eq_zero μ₀ y
      (K.coord_eq_zero_of_pushMass_eq_zero μ₁ hfull₁ y h)

end FiniteFellerKernel

/-- A finite probability law in real simplex coordinates. -/
structure FiniteProbabilityLaw (Y : Type v) [Fintype Y] where
  prob : Y → ℝ
  nonneg : ∀ y, 0 ≤ prob y
  sum_prob : ∑ y, prob y = 1

namespace FiniteProbabilityLaw

variable {Y : Type v} [Fintype Y]

theorem prob_le_one (p : FiniteProbabilityLaw Y) (y : Y) : p.prob y ≤ 1 := by
  classical
  calc
    p.prob y ≤ ∑ z, p.prob z := by
      exact Finset.single_le_sum (fun z _ => p.nonneg z) (Finset.mem_univ y)
    _ = 1 := p.sum_prob

end FiniteProbabilityLaw

namespace FiniteFellerKernel

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fintype Y] [Nonempty Y]

/-- Rank-two continuous kernel interpolating two finite target laws. -/
def rankTwo (u : C(X, unitInterval))
    (q₀ q₁ : FiniteProbabilityLaw Y) : FiniteFellerKernel X Y where
  coord := fun y =>
    { toFun := fun x =>
        ⟨(u x : ℝ) * q₀.prob y + (1 - (u x : ℝ)) * q₁.prob y, by
          constructor
          · exact add_nonneg
              (mul_nonneg (u x).2.1 (q₀.nonneg y))
              (mul_nonneg (sub_nonneg.mpr (u x).2.2) (q₁.nonneg y))
          · calc
              (u x : ℝ) * q₀.prob y + (1 - (u x : ℝ)) * q₁.prob y ≤
                  (u x : ℝ) * 1 + (1 - (u x : ℝ)) * 1 := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (q₀.prob_le_one y) (u x).2.1)
                  (mul_le_mul_of_nonneg_left (q₁.prob_le_one y)
                    (sub_nonneg.mpr (u x).2.2))
              _ = 1 := by ring⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop }
  sum_coord := by
    intro x
    simp only [ContinuousMap.coe_mk, Subtype.coe_mk]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      q₀.sum_prob, q₁.sum_prob]
    ring

/-- Mean mixing coordinate under a source law. -/
def mixingMean (u : C(X, unitInterval)) (μ : Measure X) : ℝ :=
  ∫ x, (u x : ℝ) ∂μ

theorem mixingMean_integrable (u : C(X, unitInterval)) (μ : Measure X)
    [IsFiniteMeasure μ] :
    Integrable (fun x => (u x : ℝ)) μ := by
  have hcont : Continuous (fun x => (u x : ℝ)) :=
    continuous_subtype_val.comp u.continuous
  apply Integrable.of_bound hcont.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (u x).2.2
  · exact (u x).2.1

theorem mixingMean_mem_Icc (u : C(X, unitInterval)) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    mixingMean u μ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg fun x => (u x).2.1
  · have hmono :
        ∫ x, (u x : ℝ) ∂μ ≤ ∫ _ : X, (1 : ℝ) ∂μ := by
      apply integral_mono_ae
      · exact mixingMean_integrable u μ
      · exact integrable_const 1
      · exact Filter.Eventually.of_forall fun x => (u x).2.2
    simpa only [mixingMean, integral_const, probReal_univ, one_smul] using hmono

/- Rank-two pushforward formula. -/
omit [Nonempty Y] in
theorem rankTwo_pushMass (u : C(X, unitInterval))
    (q₀ q₁ : FiniteProbabilityLaw Y) (μ : Measure X) [IsProbabilityMeasure μ]
    (y : Y) :
    (rankTwo u q₀ q₁).pushMass μ y =
      mixingMean u μ * q₀.prob y + (1 - mixingMean u μ) * q₁.prob y := by
  rw [pushMass, rankTwo, mixingMean]
  simp only [ContinuousMap.coe_mk, Subtype.coe_mk]
  rw [integral_add]
  · rw [integral_mul_const]
    have hu := mixingMean_integrable u μ
    have hone : Integrable (fun _ : X => (1 : ℝ)) μ :=
      integrable_const 1
    rw [integral_mul_const, integral_sub hone hu, integral_const]
    simp
  · exact (mixingMean_integrable u μ).mul_const _
  · exact ((integrable_const 1).sub (mixingMean_integrable u μ)).mul_const _

/-- Extend a kernel from a target face by zero on all missing coordinates. -/
def extendByZero (p : Y → Prop) [DecidablePred p]
    (K : FiniteFellerKernel X {y // p y}) : FiniteFellerKernel X Y where
  coord := fun y => if hy : p y then K.coord ⟨y, hy⟩ else 0
  sum_coord := by
    intro x
    have hsplit :=
      Fintype.sum_subtype_add_sum_subtype p
        (fun y : Y => (((if hy : p y then K.coord ⟨y, hy⟩ else 0) x :
          unitInterval) : ℝ))
    have hpos :
        ∑ i : {y // p y},
            (((if hy : p (i : Y) then K.coord ⟨i, hy⟩ else 0) x :
              unitInterval) : ℝ) = 1 := by
      calc
        _ = ∑ i : {y // p y}, ((K.coord i x : unitInterval) : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [dif_pos i.2]
        _ = 1 := K.sum_coord x
    have hneg :
        ∑ i : {y // ¬p y},
            (((if hy : p (i : Y) then K.coord ⟨i, hy⟩ else 0) x :
              unitInterval) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [dif_neg i.2, ContinuousMap.zero_apply]
      rfl
    calc
      _ = (∑ i : {y // p y},
            (((if hy : p (i : Y) then K.coord ⟨i, hy⟩ else 0) x :
              unitInterval) : ℝ)) +
          ∑ i : {y // ¬p y},
            (((if hy : p (i : Y) then K.coord ⟨i, hy⟩ else 0) x :
              unitInterval) : ℝ) := hsplit.symm
      _ = 1 := by rw [hpos, hneg, add_zero]

omit [BorelSpace X] [Nonempty Y] in
theorem extendByZero_pushMass_of_mem (p : Y → Prop) [DecidablePred p]
    (K : FiniteFellerKernel X {y // p y}) (μ : Measure X)
    (y : Y) (hy : p y) :
    (extendByZero p K).pushMass μ y = K.pushMass μ ⟨y, hy⟩ := by
  simp [pushMass, extendByZero, hy]

omit [BorelSpace X] [Nonempty Y] in
theorem extendByZero_pushMass_of_not_mem (p : Y → Prop) [DecidablePred p]
    (K : FiniteFellerKernel X {y // p y}) (μ : Measure X)
    (y : Y) (hy : ¬p y) :
    (extendByZero p K).pushMass μ y = 0 := by
  simp [pushMass, extendByZero, hy]

/-- Singularity on a compact metric source produces continuous almost-separators in mean. -/
theorem exists_mixingMean_near_endpoints
    [CompactSpace X] (μ₀ μ₁ : Measure X)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ u : C(X, unitInterval),
      1 - η < mixingMean u μ₀ ∧ mixingMean u μ₁ < η := by
  let s : Set X := hsing.nullSet
  have hs : MeasurableSet s := hsing.measurableSet_nullSet
  have hμ₀s : μ₀ s = 0 := hsing.measure_nullSet
  have hμ₁sc : μ₁ sᶜ = 0 := hsing.measure_compl_nullSet
  have hμ₀sc : μ₀ sᶜ = 1 := by
    rw [measure_compl hs (measure_ne_top μ₀ s), hμ₀s, measure_univ]
    simp
  have hμ₁s : μ₁ s = 1 := by
    have hcomp := measure_compl hs (measure_ne_top μ₁ s)
    rw [hμ₁sc, measure_univ] at hcomp
    have hlo : (1 : ℝ≥0∞) ≤ μ₁ s :=
      (tsub_eq_zero_iff_le).mp hcomp.symm
    have hhi : μ₁ s ≤ 1 := by
      have hmono : μ₁ s ≤ μ₁ Set.univ := measure_mono (Set.subset_univ s)
      simpa only [measure_univ] using hmono
    exact le_antisymm hhi hlo
  have hcut : ENNReal.ofReal (1 - η) < 1 :=
    ENNReal.ofReal_lt_one.mpr (by linarith)
  let H₀ :=
    innerRegular_isCompact_isClosed_measurableSet_of_finite μ₀
  let H₁ :=
    innerRegular_isCompact_isClosed_measurableSet_of_finite μ₁
  obtain ⟨F₀, hF₀s, hF₀compact, hF₀mass⟩ :=
    H₀ hs.compl (ENNReal.ofReal (1 - η)) (by simpa [hμ₀sc] using hcut)
  obtain ⟨F₁, hF₁s, hF₁compact, hF₁mass⟩ :=
    H₁ hs (ENNReal.ofReal (1 - η)) (by simpa [hμ₁s] using hcut)
  have hF₀real : 1 - η < μ₀.real F₀ := by
    have hnonneg : 0 ≤ 1 - η := by linarith
    calc
      1 - η = (ENNReal.ofReal (1 - η)).toReal :=
        (ENNReal.toReal_ofReal hnonneg).symm
      _ < (μ₀ F₀).toReal :=
        (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ₀ F₀)).mpr hF₀mass
      _ = μ₀.real F₀ := (Measure.real_def μ₀ F₀).symm
  have hF₁real : 1 - η < μ₁.real F₁ := by
    have hnonneg : 0 ≤ 1 - η := by linarith
    calc
      1 - η = (ENNReal.ofReal (1 - η)).toReal :=
        (ENNReal.toReal_ofReal hnonneg).symm
      _ < (μ₁ F₁).toReal :=
        (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ₁ F₁)).mpr hF₁mass
      _ = μ₁.real F₁ := (Measure.real_def μ₁ F₁).symm
  have hdisj : Disjoint F₁ F₀ := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₀
    exact (hF₀s hx₀) (hF₁s hx₁)
  obtain ⟨f, hf₁, hf₀, hfrange⟩ :=
    exists_continuous_zero_one_of_isClosed hF₁compact.2 hF₀compact.2 hdisj
  let u : C(X, unitInterval) :=
    { toFun := fun x => ⟨f x, hfrange x⟩
      continuous_toFun := Continuous.subtype_mk f.continuous _ }
  have hindicator₀ :
      (F₀.indicator fun _ : X => (1 : ℝ)) ≤ fun x => (u x : ℝ) := by
    intro x
    by_cases hx : x ∈ F₀
    · simp only [Set.indicator_of_mem hx, u, ContinuousMap.coe_mk, Subtype.coe_mk]
      exact (hf₀ hx).ge
    · simp only [Set.indicator_of_notMem hx]
      exact (u x).2.1
  have hindicator₁ :
      (fun x => (u x : ℝ)) ≤ F₁ᶜ.indicator fun _ : X => (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ F₁
    · have hxc : x ∉ F₁ᶜ := by simpa
      simp only [Set.indicator_of_notMem hxc, u, ContinuousMap.coe_mk, Subtype.coe_mk]
      exact (hf₁ hx).le
    · have hxc : x ∈ F₁ᶜ := hx
      simp only [Set.indicator_of_mem hxc]
      exact (u x).2.2
  have hlow :
      μ₀.real F₀ ≤ mixingMean u μ₀ := by
    have hmono :
        ∫ x, F₀.indicator (fun _ : X => (1 : ℝ)) x ∂μ₀ ≤
          ∫ x, (u x : ℝ) ∂μ₀ := by
      apply integral_mono_ae
      · exact (integrable_const 1).indicator hF₀compact.2.measurableSet
      · exact mixingMean_integrable u μ₀
      · exact Filter.Eventually.of_forall hindicator₀
    have hind :
        ∫ x, F₀.indicator (fun _ : X => (1 : ℝ)) x ∂μ₀ = μ₀.real F₀ := by
      simpa using integral_indicator_const (μ := μ₀) (1 : ℝ)
        hF₀compact.2.measurableSet
    simpa only [mixingMean, hind] using hmono
  have hupp :
      mixingMean u μ₁ ≤ μ₁.real F₁ᶜ := by
    have hmono :
        ∫ x, (u x : ℝ) ∂μ₁ ≤
          ∫ x, F₁ᶜ.indicator (fun _ : X => (1 : ℝ)) x ∂μ₁ := by
      apply integral_mono_ae
      · exact mixingMean_integrable u μ₁
      · exact (integrable_const 1).indicator hF₁compact.2.measurableSet.compl
      · exact Filter.Eventually.of_forall hindicator₁
    have hind :
        ∫ x, F₁ᶜ.indicator (fun _ : X => (1 : ℝ)) x ∂μ₁ = μ₁.real F₁ᶜ := by
      simpa using integral_indicator_const (μ := μ₁) (1 : ℝ)
        hF₁compact.2.measurableSet.compl
    simpa only [mixingMean, hind] using hmono
  have hF₁compl : μ₁.real F₁ᶜ = 1 - μ₁.real F₁ := by
    rw [measureReal_compl hF₁compact.2.measurableSet, probReal_univ]
  refine ⟨u, lt_of_lt_of_le hF₀real hlow, ?_⟩
  rw [hF₁compl] at hupp
  linarith

end FiniteFellerKernel

namespace FiniteProbabilityLaw

variable {Y : Type v} [Fintype Y] [Nonempty Y]

/-- Left endpoint obtained by inverting a two-by-two mixing matrix. -/
def recoveredLeft (p₀ p₁ : FiniteProbabilityLaw Y) (a₀ a₁ : ℝ) (y : Y) : ℝ :=
  ((1 - a₁) * p₀.prob y - (1 - a₀) * p₁.prob y) / (a₀ - a₁)

/-- Right endpoint obtained by inverting a two-by-two mixing matrix. -/
def recoveredRight (p₀ p₁ : FiniteProbabilityLaw Y) (a₀ a₁ : ℝ) (y : Y) : ℝ :=
  (a₀ * p₁.prob y - a₁ * p₀.prob y) / (a₀ - a₁)

/- Near-diagonal mixing can be inverted inside the simplex for every strictly positive pair. -/
omit [Nonempty Y] in
theorem exists_exact_rankTwo_endpoints
    (p₀ p₁ : FiniteProbabilityLaw Y) (m η a₀ a₁ : ℝ)
    (hm0 : 0 < m) (hm1 : m ≤ 1)
    (hm₀ : ∀ y, m ≤ p₀.prob y) (hm₁ : ∀ y, m ≤ p₁.prob y)
    (hη0 : 0 < η) (hη4 : η < 1 / 4) (hηm : η < m / 4)
    (ha₀lo : 1 - η < a₀) (ha₀hi : a₀ ≤ 1)
    (ha₁lo : 0 ≤ a₁) (ha₁hi : a₁ < η) :
    ∃ q₀ q₁ : FiniteProbabilityLaw Y,
      (∀ y, a₀ * q₀.prob y + (1 - a₀) * q₁.prob y = p₀.prob y) ∧
      (∀ y, a₁ * q₀.prob y + (1 - a₁) * q₁.prob y = p₁.prob y) := by
  have hηhalf : η < 1 / 2 := by linarith
  have hD : 0 < a₀ - a₁ := by linarith
  have hηm_le : η * m ≤ η := by
    simpa using mul_le_mul_of_nonneg_left hm1 hη0.le
  have hbase : 0 < (1 - η) * m - η := by
    nlinarith
  have hleft_pos : ∀ y, 0 < recoveredLeft p₀ p₁ a₀ a₁ y := by
    intro y
    have hc₀ : 0 ≤ 1 - a₁ := by linarith
    have hc₁ : 0 ≤ 1 - a₀ := sub_nonneg.mpr ha₀hi
    have hp₀lower :
        (1 - a₁) * m ≤ (1 - a₁) * p₀.prob y :=
      mul_le_mul_of_nonneg_left (hm₀ y) hc₀
    have hp₁upper :
        (1 - a₀) * p₁.prob y ≤ (1 - a₀) * 1 :=
      mul_le_mul_of_nonneg_left (p₁.prob_le_one y) hc₁
    have hnumer :
        0 < (1 - a₁) * p₀.prob y - (1 - a₀) * p₁.prob y := by
      nlinarith
    exact div_pos hnumer hD
  have hright_pos : ∀ y, 0 < recoveredRight p₀ p₁ a₀ a₁ y := by
    intro y
    have ha₀nonneg : 0 ≤ a₀ := by linarith
    have hp₁lower : a₀ * m ≤ a₀ * p₁.prob y :=
      mul_le_mul_of_nonneg_left (hm₁ y) ha₀nonneg
    have hp₀upper : a₁ * p₀.prob y ≤ a₁ * 1 :=
      mul_le_mul_of_nonneg_left (p₀.prob_le_one y) ha₁lo
    have hnumer : 0 < a₀ * p₁.prob y - a₁ * p₀.prob y := by
      nlinarith
    exact div_pos hnumer hD
  let q₀ : FiniteProbabilityLaw Y :=
    { prob := recoveredLeft p₀ p₁ a₀ a₁
      nonneg := fun y => (hleft_pos y).le
      sum_prob := by
        simp only [recoveredLeft]
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, p₀.sum_prob, p₁.sum_prob]
        field_simp
        ring }
  let q₁ : FiniteProbabilityLaw Y :=
    { prob := recoveredRight p₀ p₁ a₀ a₁
      nonneg := fun y => (hright_pos y).le
      sum_prob := by
        simp only [recoveredRight]
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, p₀.sum_prob, p₁.sum_prob]
        field_simp }
  refine ⟨q₀, q₁, ?_, ?_⟩
  · intro y
    simp only [q₀, q₁, recoveredLeft, recoveredRight]
    field_simp
    ring
  · intro y
    simp only [q₀, q₁, recoveredLeft, recoveredRight]
    field_simp
    ring

/-- Two strictly positive finite laws have a common positive coordinate floor. -/
theorem exists_common_positive_lower_bound
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hp₀ : ∀ y, 0 < p₀.prob y) (hp₁ : ∀ y, 0 < p₁.prob y) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      (∀ y, m ≤ p₀.prob y) ∧ (∀ y, m ≤ p₁.prob y) := by
  classical
  let f : Y ⊕ Y → ℝ := fun z =>
    match z with
    | Sum.inl y => p₀.prob y
    | Sum.inr y => p₁.prob y
  obtain ⟨z, _, hz⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Y ⊕ Y)) f Finset.univ_nonempty
  let m := f z
  have hm0 : 0 < m := by
    cases z with
    | inl y => exact hp₀ y
    | inr y => exact hp₁ y
  have hm₀ : ∀ y, m ≤ p₀.prob y := by
    intro y
    exact hz (Sum.inl y) (Finset.mem_univ _)
  have hm₁ : ∀ y, m ≤ p₁.prob y := by
    intro y
    exact hz (Sum.inr y) (Finset.mem_univ _)
  let y₀ : Y := Classical.choice inferInstance
  have hm1 : m ≤ 1 :=
    (hm₀ y₀).trans (p₀.prob_le_one y₀)
  exact ⟨m, hm0, hm1, hm₀, hm₁⟩

end FiniteProbabilityLaw

namespace FiniteFellerKernel

variable {X : Type u} {Y : Type v}
  [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fintype Y] [Nonempty Y]

/-- Sufficiency on the full-support stratum: every strictly positive target pair is an exact
finite Feller image of any singular compact binary source. -/
theorem exists_pushMass_eq_of_mutuallySingular_of_target_pos
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hp₀ : ∀ y, 0 < p₀.prob y) (hp₁ : ∀ y, 0 < p₁.prob y) :
    ∃ K : FiniteFellerKernel X Y,
      (∀ y, K.pushMass μ₀ y = p₀.prob y) ∧
      (∀ y, K.pushMass μ₁ y = p₁.prob y) := by
  obtain ⟨m, hm0, hm1, hm₀, hm₁⟩ :=
    p₀.exists_common_positive_lower_bound p₁ hp₀ hp₁
  let η : ℝ := min (1 / 8 : ℝ) (m / 8)
  have hη0 : 0 < η := by
    rw [lt_min_iff]
    constructor <;> positivity
  have hη4 : η < 1 / 4 := by
    have hle : η ≤ 1 / 8 := min_le_left _ _
    linarith
  have hηm : η < m / 4 := by
    have hle : η ≤ m / 8 := min_le_right _ _
    linarith
  have hη1 : η < 1 := hη4.trans (by norm_num)
  obtain ⟨u, ha₀lo, ha₁hi⟩ :=
    exists_mixingMean_near_endpoints μ₀ μ₁ hsing η hη0 hη1
  let a₀ := mixingMean u μ₀
  let a₁ := mixingMean u μ₁
  have ha₀hi : a₀ ≤ 1 := (mixingMean_mem_Icc u μ₀).2
  have ha₁lo : 0 ≤ a₁ := (mixingMean_mem_Icc u μ₁).1
  obtain ⟨q₀, q₁, hq₀, hq₁⟩ :=
    p₀.exists_exact_rankTwo_endpoints p₁ m η a₀ a₁ hm0 hm1 hm₀ hm₁
      hη0 hη4 hηm ha₀lo ha₀hi ha₁lo ha₁hi
  refine ⟨rankTwo u q₀ q₁, ?_, ?_⟩
  · intro y
    rw [rankTwo_pushMass]
    exact hq₀ y
  · intro y
    rw [rankTwo_pushMass]
    exact hq₁ y

/- Full sufficiency theorem: equal target zero sets are exactly realizable by a finite Feller
kernel from every singular compact binary source. -/
omit [Nonempty Y] in
theorem exists_pushMass_eq_of_mutuallySingular_of_same_zero_set
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (p₀ p₁ : FiniteProbabilityLaw Y)
    (hzero : ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0) :
    ∃ K : FiniteFellerKernel X Y,
      (∀ y, K.pushMass μ₀ y = p₀.prob y) ∧
      (∀ y, K.pushMass μ₁ y = p₁.prob y) := by
  classical
  let P : Y → Prop := fun y => 0 < p₀.prob y
  letI : DecidablePred P := Classical.decPred P
  have hPexists : ∃ y, P y := by
    by_contra h
    push Not at h
    have hall : ∀ y, p₀.prob y = 0 := by
      intro y
      exact le_antisymm (not_lt.mp (h y)) (p₀.nonneg y)
    have hsum0 : ∑ y, p₀.prob y = 0 := by simp only [hall, Finset.sum_const_zero]
    linarith [p₀.sum_prob]
  letI : Nonempty {y // P y} :=
    ⟨⟨Classical.choose hPexists, Classical.choose_spec hPexists⟩⟩
  have hcompl₀ : ∀ i : {y // ¬P y}, p₀.prob i = 0 := by
    intro i
    exact le_antisymm (not_lt.mp i.2) (p₀.nonneg i)
  have hcompl₁ : ∀ i : {y // ¬P y}, p₁.prob i = 0 := by
    intro i
    exact (hzero i).mp (hcompl₀ i)
  let p₀P : FiniteProbabilityLaw {y // P y} :=
    { prob := fun y => p₀.prob y
      nonneg := fun y => p₀.nonneg y
      sum_prob := by
        have hsplit := Fintype.sum_subtype_add_sum_subtype P p₀.prob
        have hcomp : ∑ i : {y // ¬P y}, p₀.prob i = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact hcompl₀ i
        calc
          ∑ i : {y // P y}, p₀.prob i =
              (∑ i : {y // P y}, p₀.prob i) +
                ∑ i : {y // ¬P y}, p₀.prob i := by rw [hcomp, add_zero]
          _ = ∑ y, p₀.prob y := hsplit
          _ = 1 := p₀.sum_prob }
  let p₁P : FiniteProbabilityLaw {y // P y} :=
    { prob := fun y => p₁.prob y
      nonneg := fun y => p₁.nonneg y
      sum_prob := by
        have hsplit := Fintype.sum_subtype_add_sum_subtype P p₁.prob
        have hcomp : ∑ i : {y // ¬P y}, p₁.prob i = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact hcompl₁ i
        calc
          ∑ i : {y // P y}, p₁.prob i =
              (∑ i : {y // P y}, p₁.prob i) +
                ∑ i : {y // ¬P y}, p₁.prob i := by rw [hcomp, add_zero]
          _ = ∑ y, p₁.prob y := hsplit
          _ = 1 := p₁.sum_prob }
  have hp₀P : ∀ y, 0 < p₀P.prob y := by
    intro y
    exact y.2
  have hp₁P : ∀ y, 0 < p₁P.prob y := by
    intro y
    have hp₀ne : p₀.prob y ≠ 0 := ne_of_gt y.2
    have hp₁ne : p₁.prob y ≠ 0 := by
      intro hp₁zero
      exact hp₀ne ((hzero y).mpr hp₁zero)
    exact lt_of_le_of_ne (p₁.nonneg y) (Ne.symm hp₁ne)
  obtain ⟨KP, hKP₀, hKP₁⟩ :=
    exists_pushMass_eq_of_mutuallySingular_of_target_pos μ₀ μ₁ hsing
      p₀P p₁P hp₀P hp₁P
  refine ⟨extendByZero P KP, ?_, ?_⟩
  · intro y
    by_cases hy : P y
    · rw [extendByZero_pushMass_of_mem P KP μ₀ y hy]
      exact hKP₀ ⟨y, hy⟩
    · rw [extendByZero_pushMass_of_not_mem P KP μ₀ y hy]
      exact (le_antisymm (not_lt.mp hy) (p₀.nonneg y)).symm
  · intro y
    by_cases hy : P y
    · rw [extendByZero_pushMass_of_mem P KP μ₁ y hy]
      exact hKP₁ ⟨y, hy⟩
    · rw [extendByZero_pushMass_of_not_mem P KP μ₁ y hy]
      have hp₀zero : p₀.prob y = 0 :=
        le_antisymm (not_lt.mp hy) (p₀.nonneg y)
      exact ((hzero y).mp hp₀zero).symm

/- Exact finite Feller admission classification in zero-coordinate form. -/
omit [Nonempty Y] in
theorem exists_pushMass_eq_iff_same_zero_set
    (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hsing : μ₀ ⟂ₘ μ₁)
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (p₀ p₁ : FiniteProbabilityLaw Y) :
    (∃ K : FiniteFellerKernel X Y,
        (∀ y, K.pushMass μ₀ y = p₀.prob y) ∧
        (∀ y, K.pushMass μ₁ y = p₁.prob y)) ↔
      ∀ y, p₀.prob y = 0 ↔ p₁.prob y = 0 := by
  constructor
  · rintro ⟨K, hK₀, hK₁⟩ y
    rw [← hK₀ y, ← hK₁ y]
    exact K.pushMass_eq_zero_iff_of_fullSupport μ₀ μ₁ hfull₀ hfull₁ y
  · intro hzero
    exact exists_pushMass_eq_of_mutuallySingular_of_same_zero_set
      μ₀ μ₁ hsing p₀ p₁ hzero

end FiniteFellerKernel

end

end GaloisForLFunctions.HTGeometry

open Set Filter
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

namespace FiniteFellerKernel

variable {X : Type u}
  [PseudoMetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [Nonempty X]

omit [CompactSpace X] [Nonempty X] in
/-- Full support turns zero mean of a continuous unit effect into pointwise zero. -/
theorem mixingMean_eq_zero_iff_of_fullSupport
    (u : C(X, unitInterval)) (μ : Measure X) [IsProbabilityMeasure μ]
    (hfull : μ.support = Set.univ) :
    mixingMean u μ = 0 ↔ ∀ x, ((u x : unitInterval) : ℝ) = 0 := by
  constructor
  · intro hzero x
    have hae : (fun z => ((u z : unitInterval) : ℝ)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun z => (u z).2.1) (mixingMean_integrable u μ)).mp hzero
    apply continuous_eq_zero_on_support
      (continuous_subtype_val.comp u.continuous) μ hae x
    rw [hfull]
    exact Set.mem_univ x
  · intro hzero
    rw [mixingMean]
    apply integral_eq_zero_of_ae
    filter_upwards with x
    exact hzero x

omit [CompactSpace X] [Nonempty X] in
/-- Full support turns unit mean of a continuous unit effect into pointwise one. -/
theorem mixingMean_eq_one_iff_of_fullSupport
    (u : C(X, unitInterval)) (μ : Measure X) [IsProbabilityMeasure μ]
    (hfull : μ.support = Set.univ) :
    mixingMean u μ = 1 ↔ ∀ x, ((u x : unitInterval) : ℝ) = 1 := by
  constructor
  · intro hone
    have hcomp_int : ∫ x, (1 - ((u x : unitInterval) : ℝ)) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) (mixingMean_integrable u μ),
        integral_const]
      simpa only [mixingMean, probReal_univ, one_smul, sub_eq_zero] using hone.symm
    have hcomp_ae : (fun x => 1 - ((u x : unitInterval) : ℝ)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x => sub_nonneg.mpr (u x).2.2)
        ((integrable_const 1).sub (mixingMean_integrable u μ))).mp hcomp_int
    intro x
    have hx : 1 - ((u x : unitInterval) : ℝ) = 0 := by
      apply continuous_eq_zero_on_support
        (continuous_const.sub (continuous_subtype_val.comp u.continuous)) μ hcomp_ae x
      rw [hfull]
      exact Set.mem_univ x
    linarith
  · intro hone
    rw [mixingMean]
    calc
      ∫ x, ((u x : unitInterval) : ℝ) ∂μ = ∫ _ : X, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hone x
      _ = 1 := by simp

omit [CompactSpace X] in
/-- No continuous effect can perfectly distinguish two full-support probability laws. -/
theorem mixingMean_sub_lt_one_of_fullSupport
    (u : C(X, unitInterval)) (μ₀ μ₁ : Measure X)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ) :
    mixingMean u μ₁ - mixingMean u μ₀ < 1 := by
  have h₀ := mixingMean_mem_Icc u μ₀
  have h₁ := mixingMean_mem_Icc u μ₁
  apply lt_of_le_of_ne (by linarith [h₀.1, h₁.2])
  intro heq
  have hmean₀ : mixingMean u μ₀ = 0 := by
    apply le_antisymm
    · linarith [h₁.2, heq]
    · exact h₀.1
  have hmean₁ : mixingMean u μ₁ = 1 := by
    apply le_antisymm h₁.2
    linarith [h₀.1, heq]
  have hzero := (mixingMean_eq_zero_iff_of_fullSupport u μ₀ hfull₀).mp hmean₀
  have hone := (mixingMean_eq_one_iff_of_fullSupport u μ₁ hfull₁).mp hmean₁
  obtain ⟨x⟩ := ‹Nonempty X›
  linarith [hzero x, hone x]

omit [Nonempty X] in
/-- Uniform convergence of unit effects transports both source means. -/
theorem tendsto_mixingMean_of_bcf_tendsto
    (u : ℕ → C(X, unitInterval)) (g : X →ᵇ unitInterval) (μ : Measure X)
    [IsProbabilityMeasure μ]
    (hlim : Tendsto (fun n => BoundedContinuousFunction.mkOfCompact (u n))
      atTop (𝓝 g)) :
    Tendsto (fun n => mixingMean (u n) μ) atTop
      (𝓝 (∫ x, ((g x : unitInterval) : ℝ) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
  · intro n
    exact (continuous_subtype_val.comp (u n).continuous).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (u n x).2.2
    · exact (u n x).2.1
  · filter_upwards with x
    exact (continuous_subtype_val.tendsto (g x)).comp
      ((continuous_eval_const x).tendsto g |>.comp hlim)

/-- Contrast tending to one forces escape from every equicontinuous gauge. -/
theorem not_equicontinuous_of_mixingMean_sub_tendsto_one
    (u : ℕ → C(X, unitInterval)) (μ₀ μ₁ : Measure X)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (hcontrast : Tendsto
      (fun n => mixingMean (u n) μ₁ - mixingMean (u n) μ₀)
      atTop (𝓝 1)) :
    ¬ Equicontinuous (fun n x => u n x) := by
  intro hequi
  let bcfU : ℕ → X →ᵇ unitInterval := fun n =>
    BoundedContinuousFunction.mkOfCompact (u n)
  set A : Set (X →ᵇ unitInterval) := Set.range bcfU with hA
  have hsec : ∀ a : A, bcfU ((a.2).choose) = (a : X →ᵇ unitInterval) :=
    fun a => (a.2).choose_spec
  have hHcoe : ((↑) : A → X → unitInterval) =
      (fun n x => u n x) ∘ (fun a : A => (a.2).choose) := by
    funext a x
    exact (DFunLike.congr_fun (hsec a) x).symm
  have hH : Equicontinuous ((↑) : A → X → unitInterval) := by
    rw [hHcoe]
    exact hequi.comp _
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli Set.univ isCompact_univ A
      (fun _ x _ => Set.mem_univ x) hH
  have hmem : ∀ n, bcfU n ∈ closure A := fun n =>
    subset_closure (Set.mem_range_self n)
  obtain ⟨g, -, φ, hφmono, hφtends⟩ := hcompact.tendsto_subseq hmem
  have hmean₀ := tendsto_mixingMean_of_bcf_tendsto (fun n => u (φ n)) g μ₀ hφtends
  have hmean₁ := tendsto_mixingMean_of_bcf_tendsto (fun n => u (φ n)) g μ₁ hφtends
  have hcontrast_g := hmean₁.sub hmean₀
  have hcontrast_subseq := hcontrast.comp hφmono.tendsto_atTop
  have heq :
      (∫ x, ((g x : unitInterval) : ℝ) ∂μ₁) -
        (∫ x, ((g x : unitInterval) : ℝ) ∂μ₀) = 1 :=
    tendsto_nhds_unique hcontrast_g hcontrast_subseq
  let gc : C(X, unitInterval) := g.toContinuousMap
  have hlt := mixingMean_sub_lt_one_of_fullSupport gc μ₀ μ₁ hfull₀ hfull₁
  have hgc :
      mixingMean gc μ₁ - mixingMean gc μ₀ =
        (∫ x, ((g x : unitInterval) : ℝ) ∂μ₁) -
          (∫ x, ((g x : unitInterval) : ℝ) ∂μ₀) := rfl
  rw [hgc, heq] at hlt
  exact (lt_irrefl 1) hlt

/-- Every cofinal subsequence whose contrast tends to one is non-equicontinuous. -/
theorem no_equicontinuous_subsequence_of_mixingMean_sub_tendsto_one
    (u : ℕ → C(X, unitInterval)) (μ₀ μ₁ : Measure X)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (hcontrast : Tendsto
      (fun n => mixingMean (u n) μ₁ - mixingMean (u n) μ₀)
      atTop (𝓝 1))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ¬ Equicontinuous (fun n x => u (φ n) x) := by
  apply not_equicontinuous_of_mixingMean_sub_tendsto_one
    (fun n => u (φ n)) μ₀ μ₁ hfull₀ hfull₁
  exact hcontrast.comp hφ.tendsto_atTop

/-- Any certified Lipschitz constants for asymptotically perfect effects diverge. -/
theorem lipschitzConstants_tendsto_atTop_of_mixingMean_sub_tendsto_one
    (u : ℕ → C(X, unitInterval)) (L : ℕ → NNReal)
    (μ₀ μ₁ : Measure X)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (hfull₀ : μ₀.support = Set.univ) (hfull₁ : μ₁.support = Set.univ)
    (hcontrast : Tendsto
      (fun n => mixingMean (u n) μ₁ - mixingMean (u n) μ₀)
      atTop (𝓝 1))
    (hlip : ∀ n, LipschitzWith (L n) (u n)) :
    Tendsto L atTop atTop := by
  by_contra hL
  rw [tendsto_atTop_atTop] at hL
  push Not at hL
  obtain ⟨C, hC⟩ := hL
  have hfreq : ∃ᶠ n in atTop, L n ≤ C := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hnN, hnC⟩ := hC N
    exact ⟨n, hnN, le_of_lt hnC⟩
  obtain ⟨φ, hφ, hφbound⟩ := extraction_of_frequently_atTop hfreq
  have hequi : Equicontinuous (fun n x => u (φ n) x) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun r : ℝ => (C : ℝ) * r)
    · have hcont : Continuous (fun r : ℝ => (C : ℝ) * r) := by fun_prop
      simpa using hcont.tendsto 0
    · intro x y n
      calc
        dist (u (φ n) x) (u (φ n) y) ≤
            (L (φ n) : ℝ) * dist x y := (hlip (φ n)).dist_le_mul x y
        _ ≤ (C : ℝ) * dist x y := by
          gcongr
          exact_mod_cast hφbound n
  exact (no_equicontinuous_subsequence_of_mixingMean_sub_tendsto_one
    u μ₀ μ₁ hfull₀ hfull₁ hcontrast φ hφ) hequi

end FiniteFellerKernel

end

end GaloisForLFunctions.HTGeometry
