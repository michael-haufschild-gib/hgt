import GaloisForLFunctions.HTGeometry.InfiniteSupportPositiveAperture
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite negative support from bounded corrections

Indicators on a negative Hahn set turn repaired positivity into a quadratic
self-mass bound. Its positive mass floor excludes infinite support and gives
an exact positive finite Dirac decomposition.
-/

open MeasureTheory Set Finset

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [HereditarilyLindelofSpace X]

/-- A finite measure with a positive mass floor on every nonnull measurable
set has finite topological support. -/
theorem finite_support_of_positive_mass_floor (μ : Measure X) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε)
    (hfloor : ∀ s, MeasurableSet s → μ s ≠ 0 → ε ≤ μ.real s) :
    μ.support.Finite := by
  classical
  by_contra hfin
  have hinf : μ.support.Infinite := hfin
  let A := infiniteSupportPositivePieces μ hinf
  have hmeas (j : ℕ) : MeasurableSet (A j) :=
    measurableSet_infiniteSupportPositivePieces μ hinf j
  have hpos (j : ℕ) : μ (A j) ≠ 0 :=
    measure_infiniteSupportPositivePieces_ne_zero μ hinf Measure.support_mem_ae j
  have hdisj : Pairwise (fun i j => Disjoint (A i) (A j)) :=
    infiniteSupportPositivePieces_pairwiseDisjoint μ hinf
  obtain ⟨n, hn⟩ := exists_nat_gt (μ.real univ / ε)
  have hsum : (n : ℝ) * ε ≤ μ.real univ := by
    calc
      (n : ℝ) * ε = ∑ _j ∈ range n, ε := by simp
      _ ≤ ∑ j ∈ range n, μ.real (A j) :=
        sum_le_sum fun j _ => hfloor (A j) (hmeas j) (hpos j)
      _ = μ.real (⋃ j ∈ range n, A j) :=
        (measureReal_biUnion_finset (fun i _ j _ hij => hdisj hij)
          (fun j _ => hmeas j)).symm
      _ ≤ μ.real univ := measureReal_mono (subset_univ _)
  have hlt : μ.real univ < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  exact (not_lt_of_ge hsum) hlt

/-- A quadratic self-mass bound prohibits an infinite support. -/
theorem finite_support_of_measure_le_mul_sq (μ : Measure X) [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ s, MeasurableSet s → μ.real s ≤ C * (μ.real s) ^ 2) :
    μ.support.Finite := by
  apply finite_support_of_positive_mass_floor μ (ε := 1 / (C + 1)) (by positivity)
  intro s hs hpos
  have ha : 0 < μ.real s := ENNReal.toReal_pos hpos (measure_ne_top μ s)
  have hca : 1 ≤ C * μ.real s :=
    (mul_le_mul_iff_right₀ ha).mp (by nlinarith only [hquad s hs])
  apply (div_le_iff₀ (show 0 < C + 1 by positivity)).mpr
  nlinarith only [hca, ha]


/-- Finitely many bounded integral corrections force the negative part of
a repaired signed quadratic form to have finite support. -/
theorem finite_negative_support_of_bounded_corrections
    (P N : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure N] (hmut : P ⟂ₘ N)
    {m : ℕ} (q : Fin m → X → ℂ) {C : ℝ} (hq : ∀ i x, ‖q i x‖ ≤ C)
    (hrepair : ∀ f : X → ℂ, MemLp f 2 (P + N) →
      0 ≤ (∫ x, ‖f x‖ ^ 2 ∂P) - (∫ x, ‖f x‖ ^ 2 ∂N) +
        ∑ i, ‖(∫ x, q i x * f x ∂P) - ∫ x, q i x * f x ∂N‖ ^ 2) :
    N.support.Finite := by
  classical
  apply finite_support_of_measure_le_mul_sq N (C := m * C ^ 2) (by positivity)
  intro S hS
  let T := S ∩ hmut.nullSet
  have hT : MeasurableSet T := hS.inter hmut.measurableSet_nullSet
  have hPT : P T = 0 := measure_mono_null inter_subset_right hmut.measure_nullSet
  have hNT : N.real T = N.real S := by
    unfold Measure.real T
    rw [measure_inter_conull hmut.measure_compl_nullSet]
  let f : X → ℂ := T.indicator (fun _ => 1)
  have hf : MemLp f 2 (P + N) := (memLp_const (1 : ℂ)).indicator hT
  have hzP : f =ᵐ[P] fun _ => 0 := by
    have hs : ∀ᵐ x ∂P, x ∉ T := by simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hPT
    filter_upwards [hs] with x hx
    exact indicator_of_notMem hx _
  have he (μ : Measure X) : (∫ x, ‖f x‖ ^ 2 ∂μ) = μ.real T := by
    have heq : (fun x => ‖f x‖ ^ 2) = T.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ T
      · simp only [f, Set.indicator_of_mem hx, norm_one, one_pow]
      · simp only [f, Set.indicator_of_notMem hx, norm_zero, zero_pow two_ne_zero]
    rw [heq, integral_indicator_const 1 hT]
    simp only [smul_eq_mul, mul_one]
  have hpenergy : (∫ x, ‖f x‖ ^ 2 ∂P) = 0 := by
    rw [he, Measure.real, hPT, ENNReal.toReal_zero]
  have hp (i : Fin m) : (∫ x, q i x * f x ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzP] with x hx
    change q i x * f x = 0
    rw [hx, mul_zero]
  have hn (i : Fin m) : (∫ x, q i x * f x ∂N) = ∫ x in T, q i x ∂N := by
    rw [← integral_indicator hT]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ T
    · simp only [f, Set.indicator_of_mem hx, mul_one]
    · simp only [f, Set.indicator_of_notMem hx, mul_zero]
  have hr := hrepair f hf
  simp only [hpenergy, he N, hp, hn, zero_sub, norm_neg] at hr
  have hsum : (∑ i, ‖∫ x in T, q i x ∂N‖ ^ 2) ≤
      (m : ℝ) * C ^ 2 * (N.real T) ^ 2 := by
    calc
      (∑ i, ‖∫ x in T, q i x ∂N‖ ^ 2) ≤ ∑ _i : Fin m, (C * N.real T) ^ 2 :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_setIntegral_le_of_norm_le_const (measure_lt_top N T) (fun x _ => hq i x)) 2
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [← hNT]
  linarith only [hr, hsum]


/-- A finite support gives an exact finite positive Dirac decomposition. -/
theorem exists_positive_dirac_sum_of_finite_support (μ : Measure X) [IsFiniteMeasure μ]
    (hfin : μ.support.Finite) :
    ∃ s : Finset X, (∀ x ∈ s, 0 < μ.real {x}) ∧
      μ = ∑ x ∈ s, ENNReal.ofReal (μ.real {x}) • Measure.dirac x := by
  classical
  let S := hfin.toFinset
  have hfull : μ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
    have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := Measure.support_mem_ae
    have hs : ∀ᵐ x ∂μ, id x ∈ S := hsupp.mono fun x hx => by
      simpa only [id_eq, S, Set.Finite.mem_toFinset] using hx
    have h := (Measure.ae_mem_finset_iff_map_eq_sum_dirac
      (s := S) (f := id) aemeasurable_id).mp hs
    simpa only [Measure.map_id, Set.preimage_id] using h
  let s := S.filter fun x => μ {x} ≠ 0
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    exact ENNReal.toReal_pos (mem_filter.mp hx).2 (measure_ne_top μ {x})
  · have hfilter : (∑ x ∈ s, μ {x} • Measure.dirac x) =
        ∑ x ∈ S, μ {x} • Measure.dirac x := by
      apply sum_subset (filter_subset _ _)
      intro x _ hx
      have hz : μ {x} = 0 := by
        by_contra hne
        exact hx (mem_filter.mpr ⟨‹x ∈ S›, hne⟩)
      rw [hz, zero_smul]
    conv_lhs => rw [hfull, ← hfilter]
    apply sum_congr rfl
    intro x _
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ {x})]

end GaloisForLFunctions.HTGeometry
