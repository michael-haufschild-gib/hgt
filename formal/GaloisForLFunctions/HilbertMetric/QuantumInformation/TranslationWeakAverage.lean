import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Nonatomic weak averaging of translations

Translation of counting-measure square-summable real coordinates preserves
inner products, but each fixed-vector coefficient has countable support.
Lebesgue averaging therefore annihilates finite-rank observables while
preserving identity. On scalar identity plus finite rank, the normalized
unit-interval average extracts exactly the scalar part.

This is the countable-support mechanism behind singularising translation
averages in Dzhenzher, *Singularising quantum channels preserving
kappa-additivity*. Integrability is proved from the coefficient identities.
-/

noncomputable section
open MeasureTheory
open scoped lp BigOperators ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

abbrev Space := ℓ²(ℝ, ℂ)

/-- Translation of the counting-measure square-summable coordinates. -/
def shift (t : ℝ) : Space →ₗᵢ[ℂ] Space :=
  HTGeometry.lpDependentDomCongrIsometry (𝕜 := ℂ) (E := fun _ : ℝ => ℂ)
    (p := 2) (by norm_num) (Equiv.addLeft t)

theorem shift_apply (t : ℝ) (u : Space) (y : ℝ) : shift t u y = u (t + y) := rfl

theorem norm_shift (t : ℝ) (u : Space) : ‖shift t u‖ = ‖u‖ := (shift t).norm_map u

theorem countable_support (u : Space) : (Function.support u).Countable := by
  have h : Summable (fun t : ℝ => ‖u t‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa only [Function.support, ne_eq, sq_eq_zero_iff, norm_eq_zero] using h.countable_support

theorem shifted_coordinate_ae_zero (u : Space) (y : ℝ) :
    (fun t : ℝ => u (t + y)) =ᵐ[volume] 0 := by
  have hc : {t : ℝ | u (t + y) ≠ 0}.Countable := by
    apply ((countable_support u).image (fun s : ℝ => s - y)).mono
    intro t ht
    exact ⟨t + y, ht, by ring⟩
  rw [Filter.EventuallyEq, ae_iff]
  exact hc.measure_zero volume

/-- Matrix coefficients of translation have countable support in the translation parameter. -/
theorem countable_support_shift_inner (u v : Space) :
    (Function.support (fun t : ℝ => inner ℂ (shift t u) v)).Countable := by
  classical
  let D := (fun p : ℝ × ℝ => p.1 - p.2) ''
    (Function.support u ×ˢ Function.support v)
  have hD : D.Countable :=
    ((countable_support u).prod (countable_support v)).image _
  apply hD.mono
  intro t ht
  by_contra hnot
  apply ht
  change inner ℂ (shift t u) v = 0
  rw [lp.inner_eq_tsum]
  calc
    (∑' y : ℝ, inner ℂ (shift t u y) (v y)) = ∑' _ : ℝ, (0 : ℂ) := by
      apply tsum_congr
      intro y
      by_cases hv : v y = 0
      · simp only [hv, inner_zero_right]
      · have hu : u (t + y) = 0 := by
          by_contra hu
          apply hnot
          exact ⟨(t + y, y), ⟨hu, hv⟩, by dsimp; ring⟩
        simp only [shift_apply, hu, inner_zero_left]
    _ = 0 := tsum_zero

/-- Every fixed-vector translation coefficient vanishes almost everywhere. -/
theorem shift_inner_ae_zero (u v : Space) :
    (fun t : ℝ => inner ℂ (shift t u) v) =ᵐ[volume] 0 := by
  rw [Filter.EventuallyEq, ae_iff]
  exact (countable_support_shift_inner u v).measure_zero volume

private theorem separable_shift_inner_ae_zero (S : Set Space)
    (hS : TopologicalSpace.IsSeparable S) (u : Space) :
    ∀ᵐ t ∂volume, ∀ v ∈ S, inner ℂ (shift t u) v = 0 := by
  obtain ⟨C, hC, hSC⟩ := hS
  letI : Countable C := hC.to_subtype
  have hc : ∀ᵐ t ∂volume, ∀ v : C, inner ℂ (shift t u) v.val = 0 :=
    ae_all_iff.mpr fun v => shift_inner_ae_zero u v.val
  filter_upwards [hc] with t ht
  have hz : IsClosed {v : Space | inner ℂ (shift t u) v = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hclosure : closure C ⊆ {v : Space | inner ℂ (shift t u) v = 0} :=
    hz.closure_subset_iff.mpr fun v hv => ht ⟨v, hv⟩
  exact fun v hv => hclosure (hSC hv)

/-- Every translated finite-rank coefficient vanishes almost everywhere. -/
theorem finiteRankCoefficient_ae_zero {n : ℕ} (a b : Fin n → Space) (u v : Space) :
    (fun t : ℝ => inner ℂ (shift t u)
      (∑ i, inner ℂ (b i) (shift t v) • a i)) =ᵐ[volume] 0 := by
  have h : ∀ᵐ t ∂volume, ∀ i : Fin n, inner ℂ (shift t u) (a i) = 0 :=
    ae_all_iff.mpr fun i => shift_inner_ae_zero u (a i)
  filter_upwards [h] with t ht
  simp only [inner_sum, inner_smul_right, ht, mul_zero, Finset.sum_const_zero,
    Pi.zero_apply]

/-- Every finite-rank translation coefficient is integrable. -/
theorem finiteRankCoefficient_integrable {n : ℕ} (a b : Fin n → Space) (u v : Space) :
    Integrable (fun t : ℝ => inner ℂ (shift t u)
      (∑ i, inner ℂ (b i) (shift t v) • a i)) := by
  exact (integrable_congr (finiteRankCoefficient_ae_zero a b u v)).mpr (integrable_zero ℝ ℂ volume)

/-- Nonatomic weak averaging annihilates every explicit finite-rank observable. -/
theorem integral_finiteRankCoefficient {n : ℕ} (a b : Fin n → Space) (u v : Space) :
    ∫ t : ℝ, inner ℂ (shift t u)
      (∑ i, inner ℂ (b i) (shift t v) • a i) = 0 := by
  rw [integral_congr_ae (finiteRankCoefficient_ae_zero a b u v)]
  simp only [Pi.zero_apply, integral_zero]

/-- Probability averaging over a unit interval annihilates all finite-rank observables. -/
theorem interval_average_finiteRank {n : ℕ} (a b : Fin n → Space) (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (∑ i, inner ℂ (b i) (shift t v) • a i) = 0 := by
  rw [integral_congr_ae (ae_restrict_of_ae (finiteRankCoefficient_ae_zero a b u v))]
  simp only [Pi.zero_apply, integral_zero]

/-- The same normalized weak average preserves the identity observable. -/
theorem interval_average_identity (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u) (shift t v) = inner ℂ u v := by
  have hi (t : ℝ) : inner ℂ (shift t u) (shift t v) = inner ℂ u v :=
    (shift t).inner_map_map u v
  simp_rw [hi]
  simp

/-- On scalar identity plus finite rank, normalized weak averaging retains exactly the scalar. -/
theorem interval_average_scalar_add_finiteRank {n : ℕ} (c : ℂ)
    (a b : Fin n → Space) (u v : Space) :
    ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (shift t u)
      (c • shift t v + ∑ i, inner ℂ (b i) (shift t v) • a i) = c * inner ℂ u v := by
  have h : (fun t : ℝ => inner ℂ (shift t u)
      (c • shift t v + ∑ i, inner ℂ (b i) (shift t v) • a i)) =ᵐ[
        volume.restrict (Set.Ioc 0 1)] (fun _ => c * inner ℂ u v) := by
    filter_upwards [ae_restrict_of_ae (finiteRankCoefficient_ae_zero a b u v)] with t ht
    rw [inner_add_right, inner_smul_right, (shift t).inner_map_map, ht, Pi.zero_apply, add_zero]
  rw [integral_congr_ae h]
  simp

private theorem compact_range_isSeparable (K : Space →L[ℂ] Space)
    (hK : IsCompactOperator K) : TopologicalSpace.IsSeparable (Set.range K) := by
  have hs : TopologicalSpace.IsSeparable
      (⋃ n : ℕ, closure (K '' Metric.closedBall 0 (n : ℝ))) :=
    TopologicalSpace.IsSeparable.iUnion fun n =>
      (IsCompactOperator.isCompact_closure_image_closedBall
        (f := K.toLinearMap) hK (n : ℝ)).isSeparable
  apply hs.mono
  rintro y ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact Set.mem_iUnion.mpr ⟨n, subset_closure ⟨x,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le, rfl⟩⟩

private theorem compact_coefficient_ae_zero (K : Space →L[ℂ] Space)
    (hK : IsCompactOperator K) (u v : Space) :
    (fun t : ℝ => inner ℂ (shift t u) (K (shift t v))) =ᵐ[volume] 0 := by
  filter_upwards [separable_shift_inner_ae_zero (Set.range K)
    (compact_range_isSeparable K hK) u] with t ht
  exact ht (K (shift t v)) (Set.mem_range_self _)

/-- Matrix coefficient of a finite coordinate projection after simultaneous shifts. -/
def finiteProjectionCoefficient (F : Finset ℝ) (u v : Space) (t : ℝ) : ℂ :=
  ∑ y ∈ F, conj (u (t + y)) * v (t + y)

theorem finiteProjectionCoefficient_ae_zero (F : Finset ℝ) (u v : Space) :
    finiteProjectionCoefficient F u v =ᵐ[volume] 0 := by
  have h : ∀ᵐ t ∂volume, ∀ y : F, u (t + y) = 0 :=
    ae_all_iff.mpr fun y => shifted_coordinate_ae_zero u y
  filter_upwards [h] with t ht
  change ∑ y ∈ F, conj (u (t + y)) * v (t + y) = 0
  apply Finset.sum_eq_zero
  intro y hy
  rw [ht ⟨y, hy⟩, map_zero, zero_mul]

theorem integral_finiteProjectionCoefficient (F : Finset ℝ) (u v : Space) :
    ∫ t : ℝ, finiteProjectionCoefficient F u v t = 0 := by
  rw [integral_congr_ae (finiteProjectionCoefficient_ae_zero F u v)]
  simp only [Pi.zero_apply, integral_zero]

#print axioms countable_support
#print axioms shifted_coordinate_ae_zero
#print axioms countable_support_shift_inner
#print axioms shift_inner_ae_zero
#print axioms finiteRankCoefficient_ae_zero
#print axioms finiteRankCoefficient_integrable
#print axioms integral_finiteRankCoefficient
#print axioms interval_average_finiteRank
#print axioms interval_average_identity
#print axioms interval_average_scalar_add_finiteRank
#print axioms compact_coefficient_ae_zero
#print axioms finiteProjectionCoefficient_ae_zero
#print axioms integral_finiteProjectionCoefficient
end GaloisForLFunctions.HilbertMetric.ShiftAverage
