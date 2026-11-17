import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeylAverage
import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeakAveragePackets
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences

/-!+# Contractive averaging on a concrete closed observable space

Finite linear combinations of integer-frequency Weyl operators and rank-one
operators have integrable translation coefficients. Their exact averages
retain only zero-frequency translations. The norm bound makes this operation
intrinsic and extends it to the norm closure of that concrete span.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

abbrev Observable := Space →L[ℂ] Space
abbrev ObservableGenerator := (ℝ × ℤ) ⊕ (Space × Space)
abbrev ObservableSymbol := ObservableGenerator →₀ ℂ

/-- Actual Weyl and rank-one generators of the observable space. -/
def generatorObservable : ObservableGenerator → Observable
  | .inl (a, k) => weylWord a (2 * Real.pi * (k : ℝ))
  | .inr (x, y) => rankOne ℂ x y

/-- The zero-frequency part of an individual concrete generator. -/
def retainedGenerator : ObservableGenerator → Observable
  | .inl (a, k) => if k = 0 then translation a else 0
  | .inr _ => 0

def evaluateSymbol : ObservableSymbol →ₗ[ℂ] Observable :=
  Finsupp.linearCombination ℂ generatorObservable

def retainSymbol : ObservableSymbol →ₗ[ℂ] Observable :=
  Finsupp.linearCombination ℂ retainedGenerator

private theorem rankOne_shift_coefficient_ae_zero (x y u v : Space) :
    (fun t : ℝ => inner ℂ (shift t u) (rankOne ℂ x y (shift t v))) =ᵐ[volume] 0 := by
  filter_upwards [shift_inner_ae_zero u x] with t ht
  simp only [rankOne_apply, inner_smul_right, ht, Pi.zero_apply, mul_zero]

private theorem generator_coefficient_integrable (g : ObservableGenerator) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u)
      (generatorObservable g (shift t v))) (Set.Ioc 0 1) := by
  cases g with
  | inl p => exact weylWord_coefficient_integrableOn p.1 (2 * Real.pi * (p.2 : ℝ)) u v
  | inr p =>
    exact (integrable_congr (ae_restrict_of_ae
      (rankOne_shift_coefficient_ae_zero p.1 p.2 u v))).mpr (integrable_zero _ _ _)

private theorem integral_generator (g : ObservableGenerator) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (generatorObservable g (shift t v))) = inner ℂ u (retainedGenerator g v) := by
  cases g with
  | inl p =>
    rw [generatorObservable, interval_average_integer_weylWord, retainedGenerator]
    split_ifs <;> simp only [zero_apply, inner_zero_right]
  | inr p =>
    rw [generatorObservable, integral_congr_ae
      (ae_restrict_of_ae (rankOne_shift_coefficient_ae_zero p.1 p.2 u v))]
    simp only [Pi.zero_apply, integral_zero, retainedGenerator, zero_apply, inner_zero_right]

/-- Every coefficient of every finitely supported observable symbol is integrable. -/
theorem evaluateSymbol_coefficient_integrable (p : ObservableSymbol) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u)
      (evaluateSymbol p (shift t v))) (Set.Ioc 0 1) := by
  simp only [evaluateSymbol, Finsupp.linearCombination_apply, Finsupp.sum,
    _root_.sum_apply, smul_apply, inner_sum, inner_smul_right]
  exact integrable_finsetSum p.support fun g _ =>
    (generator_coefficient_integrable g u v).const_mul (p g)

/-- Averaging a formal combination returns its actual retained translation operator. -/
theorem integral_evaluateSymbol (p : ObservableSymbol) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (evaluateSymbol p (shift t v))) = inner ℂ u (retainSymbol p v) := by
  simp only [evaluateSymbol, retainSymbol, Finsupp.linearCombination_apply, Finsupp.sum,
    _root_.sum_apply, smul_apply, inner_sum, inner_smul_right]
  rw [integral_finsetSum _ (fun g _ =>
    (generator_coefficient_integrable g u v).const_mul (p g))]
  simp_rw [integral_const_mul, integral_generator]

private theorem retainSymbol_pairing_bound (p : ObservableSymbol) (u v : Space) :
    ‖inner ℂ u (retainSymbol p v)‖ ≤ ‖u‖ * (‖evaluateSymbol p‖ * ‖v‖) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [← integral_evaluateSymbol]
  calc
    _ ≤ ∫ t : ℝ in Set.Ioc 0 1,
        ‖inner ℂ (shift t u) (evaluateSymbol p (shift t v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _t : ℝ in Set.Ioc 0 1, ‖u‖ * (‖evaluateSymbol p‖ * ‖v‖) := by
      apply integral_mono (evaluateSymbol_coefficient_integrable p u v).norm (integrable_const _)
      intro t
      calc
        _ ≤ ‖shift t u‖ * ‖evaluateSymbol p (shift t v)‖ := norm_inner_le_norm _ _
        _ ≤ ‖shift t u‖ * (‖evaluateSymbol p‖ * ‖shift t v‖) :=
          mul_le_mul_of_nonneg_left ((evaluateSymbol p).le_opNorm _) (norm_nonneg _)
        _ = _ := by rw [norm_shift, norm_shift]
    _ = _ := by simp

/-- Frequency retention is bounded by the norm of the represented operator. -/
theorem norm_retainSymbol_le (p : ObservableSymbol) :
    ‖retainSymbol p‖ ≤ ‖evaluateSymbol p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  by_cases hv : retainSymbol p v = 0
  · rw [hv, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have h := retainSymbol_pairing_bound p (retainSymbol p v) v
    have hs : ‖inner ℂ (retainSymbol p v) (retainSymbol p v)‖ = ‖retainSymbol p v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      change ‖(‖retainSymbol p v‖ : ℂ) ^ 2‖ = ‖retainSymbol p v‖ ^ 2
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hs, pow_two] at h
    by_contra hn
    exact (not_lt_of_ge h)
      (mul_lt_mul_of_pos_left (lt_of_not_ge hn) (norm_pos_iff.mpr hv))

/-- The concrete norm closure of Weyl and rank-one linear combinations. -/
def observableDomain : Submodule ℂ Observable :=
  (LinearMap.range evaluateSymbol).topologicalClosure

/-- The generated domain with its inherited operator norm. -/
def ObservableDomain : Type := observableDomain

instance : NormedAddCommGroup ObservableDomain :=
  inferInstanceAs (NormedAddCommGroup observableDomain)

instance : NormedSpace ℂ ObservableDomain :=
  inferInstanceAs (NormedSpace ℂ observableDomain)

/-- The underlying bounded operator of a generated observable. -/
def ObservableDomain.val (A : ObservableDomain) : Observable := A.1

instance : Coe ObservableDomain Observable := ⟨ObservableDomain.val⟩

/-- Inclusion of the closed generated domain into bounded operators. -/
def observableInclusion : ObservableDomain →L[ℂ] Observable :=
  (observableDomain.subtype : ObservableDomain →ₗ[ℂ] Observable).mkContinuous 1
    (fun A => by rw [one_mul]; exact le_rfl)

def symbolEmbedding : ObservableSymbol →ₗ[ℂ] ObservableDomain :=
  evaluateSymbol.codRestrict observableDomain fun p =>
    (LinearMap.range evaluateSymbol).le_topologicalClosure ⟨p, rfl⟩

@[simp] theorem coe_symbolEmbedding (p : ObservableSymbol) :
    (symbolEmbedding p : Observable) = evaluateSymbol p := rfl

@[simp] theorem norm_symbolEmbedding (p : ObservableSymbol) :
    ‖symbolEmbedding p‖ = ‖evaluateSymbol p‖ := rfl

theorem generatorObservable_mem_domain (g : ObservableGenerator) :
    generatorObservable g ∈ observableDomain := by
  apply (LinearMap.range evaluateSymbol).le_topologicalClosure
  refine ⟨Finsupp.single g 1, ?_⟩
  simp only [evaluateSymbol, Finsupp.linearCombination_single, one_smul]

private theorem retainedGenerator_mem_domain (g : ObservableGenerator) :
    retainedGenerator g ∈ observableDomain := by
  cases g with
  | inl p =>
    rcases p with ⟨a, k⟩
    change (if k = 0 then translation a else 0) ∈ observableDomain
    split_ifs with h
    · have hm := generatorObservable_mem_domain (.inl (a, 0))
      simpa only [generatorObservable, Int.cast_zero, mul_zero,
        weylWord_zero_frequency] using hm
    · exact observableDomain.zero_mem
  | inr p => exact observableDomain.zero_mem

private theorem retainSymbol_mem_domain (p : ObservableSymbol) :
    retainSymbol p ∈ observableDomain := by
  rw [retainSymbol, Finsupp.linearCombination_apply, Finsupp.sum]
  exact observableDomain.sum_mem fun g _ =>
    observableDomain.smul_mem _ (retainedGenerator_mem_domain g)

/-- Finite symbols are dense in the explicitly generated observable domain. -/
theorem symbolEmbedding_denseRange : DenseRange symbolEmbedding := by
  apply Metric.denseRange_iff.mpr
  intro A ε hε
  have hA : (A : Observable) ∈ closure (Set.range evaluateSymbol) := A.property
  obtain ⟨B, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp hA ε hε
  refine ⟨p, ?_⟩
  rw [dist_eq_norm]
  change ‖(A : Observable) - evaluateSymbol p‖ < ε
  simpa only [dist_eq_norm] using hp

/-- The bounded extension of actual weak averaging to the generated norm closure. -/
def closedObservableAverage : ObservableDomain →L[ℂ] Observable :=
  retainSymbol.extendOfNorm symbolEmbedding

/-- The closed-domain average agrees with the exact integral on every finite symbol. -/
theorem closedObservableAverage_symbol (p : ObservableSymbol) :
    closedObservableAverage (symbolEmbedding p) = retainSymbol p := by
  exact LinearMap.extendOfNorm_eq (f := retainSymbol) symbolEmbedding_denseRange
    ⟨1, fun q => by rw [one_mul, norm_symbolEmbedding]; exact norm_retainSymbol_le q⟩ p

/-- The extension is contractive on its concrete closed domain. -/
theorem norm_closedObservableAverage_le_one : ‖closedObservableAverage‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le (f := retainSymbol) symbolEmbedding_denseRange (by norm_num)
    (fun p => by rw [one_mul, norm_symbolEmbedding]; exact norm_retainSymbol_le p)

/-- Averaging preserves the concrete closed observable domain. -/
theorem closedObservableAverage_mem_domain (A : ObservableDomain) :
    closedObservableAverage A ∈ observableDomain := by
  have hm : ∀ B : ObservableDomain, B ∈ Set.range symbolEmbedding →
      closedObservableAverage B ∈ observableDomain := by
    rintro B ⟨p, rfl⟩
    rw [closedObservableAverage_symbol]
    exact retainSymbol_mem_domain p
  have hc : IsClosed {B : ObservableDomain | closedObservableAverage B ∈ observableDomain} :=
    (LinearMap.range evaluateSymbol).isClosed_topologicalClosure.preimage
      closedObservableAverage.continuous
  exact symbolEmbedding_denseRange.induction hm hc A

/-- The closed average filters each Weyl generator and annihilates each rank-one generator. -/
theorem closedObservableAverage_generator (g : ObservableGenerator) :
    closedObservableAverage ⟨generatorObservable g, generatorObservable_mem_domain g⟩ =
      retainedGenerator g := by
  have he : symbolEmbedding (Finsupp.single g 1) =
      ⟨generatorObservable g, generatorObservable_mem_domain g⟩ := by
    apply Subtype.ext
    change evaluateSymbol (Finsupp.single g 1) = generatorObservable g
    simp only [evaluateSymbol, Finsupp.linearCombination_single, one_smul]
  rw [← he, closedObservableAverage_symbol]
  simp only [retainSymbol, Finsupp.linearCombination_single, one_smul]

private theorem symbol_approximation (A : ObservableDomain) :
    ∃ p : ℕ → ObservableSymbol,
      Tendsto (fun n => symbolEmbedding (p n)) atTop (𝓝 A) := by
  obtain ⟨B, hB, hlim⟩ := mem_closure_iff_seq_limit.mp (symbolEmbedding_denseRange A)
  choose p hp using hB
  refine ⟨p, ?_⟩
  simpa only [hp] using hlim

private theorem coefficient_continuous (u v : Space) (t : ℝ) :
    Continuous (fun A : ObservableDomain => inner ℂ (shift t u)
      ((A : Observable) (shift t v))) := by
  change Continuous (fun A => inner ℂ (shift t u) (observableInclusion A (shift t v)))
  fun_prop

private theorem coefficient_symbol_tendsto (A : ObservableDomain)
    (p : ℕ → ObservableSymbol)
    (hp : Tendsto (fun n => symbolEmbedding (p n)) atTop (𝓝 A)) (u v : Space) (t : ℝ) :
    Tendsto (fun n => inner ℂ (shift t u) (evaluateSymbol (p n) (shift t v))) atTop
      (𝓝 (inner ℂ (shift t u) ((A : Observable) (shift t v)))) := by
  have h := ((coefficient_continuous u v t).tendsto A).comp hp
  change Tendsto (fun n => inner ℂ (shift t u)
    ((symbolEmbedding (p n) : Observable) (shift t v))) atTop
      (𝓝 (inner ℂ (shift t u) ((A : Observable) (shift t v)))) at h
  simpa only [coe_symbolEmbedding] using h

private theorem coefficient_bound (A : Observable) (u v : Space) (t : ℝ) :
    ‖inner ℂ (shift t u) (A (shift t v))‖ ≤ ‖u‖ * (‖A‖ * ‖v‖) := by
  calc
    _ ≤ ‖shift t u‖ * ‖A (shift t v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖shift t u‖ * (‖A‖ * ‖shift t v‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [norm_shift, norm_shift]

/-- All weak translation coefficients on the concrete closed domain are integrable. -/
theorem observableDomain_coefficient_integrable (A : ObservableDomain) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u)
      ((A : Observable) (shift t v))) (Set.Ioc 0 1) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  obtain ⟨p, hp⟩ := symbol_approximation A
  have hm : AEStronglyMeasurable (fun t : ℝ => inner ℂ (shift t u)
      ((A : Observable) (shift t v))) (volume.restrict (Set.Ioc 0 1)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (evaluateSymbol_coefficient_integrable (p n) u v).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun t => coefficient_symbol_tendsto A p hp u v t
  apply (integrable_const (‖u‖ * (‖(A : Observable)‖ * ‖v‖))).mono hm
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact coefficient_bound A u v t

/-- The bounded extension equals the actual scalar integral on every observable in its domain. -/
theorem closedObservableAverage_integral (A : ObservableDomain) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      ((A : Observable) (shift t v))) = inner ℂ u (closedObservableAverage A v) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  obtain ⟨p, hp⟩ := symbol_approximation A
  have hn : ∀ᶠ n in atTop, ‖symbolEmbedding (p n)‖ ≤ ‖A‖ + 1 :=
    ((tendsto_order.mp hp.norm).2 (‖A‖ + 1) (lt_add_one _)).mono fun _ h => h.le
  simp only [norm_symbolEmbedding] at hn
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      Tendsto (fun n => inner ℂ (shift t u) (evaluateSymbol (p n) (shift t v))) atTop
        (𝓝 (inner ℂ (shift t u) ((A : Observable) (shift t v)))) :=
    Filter.Eventually.of_forall fun t => coefficient_symbol_tendsto A p hp u v t
  have hdom : ∀ᶠ n in atTop, ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖inner ℂ (shift t u) (evaluateSymbol (p n) (shift t v))‖ ≤
        ‖u‖ * ((‖A‖ + 1) * ‖v‖) := by
    filter_upwards [hn] with n hn
    exact Filter.Eventually.of_forall fun t => (coefficient_bound _ u v t).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (norm_nonneg _))
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => ‖u‖ * ((‖A‖ + 1) * ‖v‖))
    (Filter.Eventually.of_forall fun n =>
      (evaluateSymbol_coefficient_integrable (p n) u v).aestronglyMeasurable)
    hdom (integrable_const _) hlim
  have hc : Continuous (fun B : ObservableDomain =>
      inner ℂ u (closedObservableAverage B v)) := by fun_prop
  have he : Tendsto (fun n => inner ℂ u
      (closedObservableAverage (symbolEmbedding (p n)) v)) atTop
        (𝓝 (inner ℂ u (closedObservableAverage A v))) := (hc.tendsto A).comp hp
  simp only [integral_evaluateSymbol] at hi
  simp only [closedObservableAverage_symbol] at he
  exact tendsto_nhds_unique hi he

#print axioms evaluateSymbol_coefficient_integrable
#print axioms integral_evaluateSymbol
#print axioms norm_retainSymbol_le
#print axioms symbolEmbedding_denseRange
#print axioms closedObservableAverage_symbol
#print axioms norm_closedObservableAverage_le_one
#print axioms closedObservableAverage_mem_domain
#print axioms closedObservableAverage_generator
#print axioms observableDomain_coefficient_integrable
#print axioms closedObservableAverage_integral
end GaloisForLFunctions.HilbertMetric.ShiftAverage
