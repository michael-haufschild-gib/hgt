import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLog
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The actual global-unit logarithm fundamental domain

Mathlib's logarithmic coordinates omit one place and include its multiplicity.
Completing them to a weighted-zero place profile recovers the full logarithm
of every actual global unit. The actual unit-lattice parallelepiped is bounded
and measurable, has compact closure, and has volume equal to the regulator.
Its completed profiles therefore admit one uniform coordinate bound.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory Set
open NumberField.Units.dirichletUnitTheorem
open scoped Classical
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]

/-- Complete weighted logarithmic coordinates to a norm-zero place profile. -/
def numberFieldWeightedLogProfile : logSpace K →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun x v := if h : v = w₀ then -(∑ w, x w) / (mult v : ℝ)
    else x ⟨v, h⟩ / (mult v : ℝ)
  map_add' x y := by
    funext v
    by_cases h : v = w₀
    · simp only [h, dite_true, Pi.add_apply, Finset.sum_add_distrib, neg_add, add_div]
    · simp only [h, dite_false, Pi.add_apply, add_div]
  map_smul' r x := by
    funext v
    by_cases h : v = w₀
    · simp only [h, dite_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
      ring
    · simp only [h, dite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

/-- Every retained coordinate is divided by its archimedean multiplicity. -/
theorem numberFieldWeightedLogProfile_apply_ne (x : logSpace K)
    (v : {v : InfinitePlace K // v ≠ w₀}) :
    numberFieldWeightedLogProfile x v = x v / (mult v.1 : ℝ) := by
  exact dif_neg v.2

/-- The omitted coordinate is determined by the weighted-zero relation. -/
theorem numberFieldWeightedLogProfile_apply_eq (x : logSpace K) :
    numberFieldWeightedLogProfile x w₀ = -(∑ w, x w) / (mult (w₀ : InfinitePlace K) : ℝ) :=
  dif_pos rfl

/-- The completed logarithmic profile has zero weighted sum. -/
theorem sum_mult_numberFieldWeightedLogProfile (x : logSpace K) :
    ∑ v : InfinitePlace K, (mult v : ℝ) * numberFieldWeightedLogProfile x v = 0 := by
  calc
    _ = -(∑ w, x w) + ∑ w, x w := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, numberFieldWeightedLogProfile_apply_eq]
      congr 1
      · have hm : (mult (w₀ : InfinitePlace K) : ℝ) ≠ 0 := mult_coe_ne_zero
        field_simp
      · apply Finset.sum_congr rfl
        intro v _
        rw [numberFieldWeightedLogProfile_apply_ne]
        have hm : (mult v.1 : ℝ) ≠ 0 := mult_coe_ne_zero
        field_simp
    _ = 0 := neg_add_cancel _

/-- Completing the actual unit logarithm recovers its full unweighted place profile. -/
theorem numberFieldWeightedLogProfile_logEmbedding (u : (𝓞 K)ˣ) :
    numberFieldWeightedLogProfile (NumberField.Units.logEmbedding K (Additive.ofMul u)) =
      numberFieldUnitPlaceLogEmbeddings u := by
  funext v
  by_cases hv : v = w₀
  · subst v
    rw [numberFieldWeightedLogProfile_apply_eq, sum_logEmbedding_component]
    change -(-(mult (w₀ : InfinitePlace K) : ℝ) * Real.log (w₀ (u : K))) /
      (mult (w₀ : InfinitePlace K) : ℝ) = Real.log (w₀ (u : K))
    rw [neg_mul, neg_neg, mul_div_cancel_left₀ _ mult_coe_ne_zero]
  · rw [numberFieldWeightedLogProfile_apply_ne _ ⟨v, hv⟩, logEmbedding_component]
    change (mult v : ℝ) * Real.log (v (u : K)) / (mult v : ℝ) = Real.log (v (u : K))
    exact mul_div_cancel_left₀ _ mult_coe_ne_zero

/-- Profile completion is a continuous linear map on the finite-dimensional log space. -/
theorem continuous_numberFieldWeightedLogProfile :
    Continuous (numberFieldWeightedLogProfile (K := K)) :=
  numberFieldWeightedLogProfile.continuous_of_finiteDimensional

variable (K) in
/-- The actual fundamental parallelepiped of the global-unit logarithm lattice. -/
def numberFieldUnitLogDomain : Set (logSpace K) :=
  ZSpan.fundamentalDomain ((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ)

/-- The chosen unit domain tiles the weighted logarithmic space. -/
theorem isAddFundamentalDomain_numberFieldUnitLogDomain :
    IsAddFundamentalDomain (NumberField.Units.unitLattice K) (numberFieldUnitLogDomain K) :=
  ZLattice.isAddFundamentalDomain (NumberField.Units.basisUnitLattice K) volume

/-- The half-open unit parallelepiped is measurable. -/
theorem measurableSet_numberFieldUnitLogDomain : MeasurableSet (numberFieldUnitLogDomain K) :=
  ZSpan.fundamentalDomain_measurableSet _

/-- The unit domain is bounded, so its profile coordinates admit a common bound. -/
theorem isBounded_numberFieldUnitLogDomain : Bornology.IsBounded (numberFieldUnitLogDomain K) :=
  ZSpan.fundamentalDomain_isBounded _

/-- The unit-domain volume is the actual logarithmic lattice covolume. -/
theorem volume_numberFieldUnitLogDomain :
    volume.real (numberFieldUnitLogDomain K) = ZLattice.covolume (NumberField.Units.unitLattice K) :=
  (ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    isAddFundamentalDomain_numberFieldUnitLogDomain).symm

/-- The domain has positive volume in every unit rank, including rank zero. -/
theorem volume_numberFieldUnitLogDomain_pos : 0 < volume.real (numberFieldUnitLogDomain K) := by
  rw [volume_numberFieldUnitLogDomain]
  exact ZLattice.covolume_pos (NumberField.Units.unitLattice K) volume

/-- The exact unit-domain volume is the number-field regulator. -/
theorem volume_numberFieldUnitLogDomain_eq_regulator :
    volume.real (numberFieldUnitLogDomain K) = NumberField.Units.regulator K :=
  volume_numberFieldUnitLogDomain

/-- The unit domain has finite Haar measure. -/
theorem measure_numberFieldUnitLogDomain_lt_top : volume (numberFieldUnitLogDomain K) < ⊤ :=
  isBounded_numberFieldUnitLogDomain.measure_lt_top

/-- Its closure is compact in the finite-dimensional weighted log space. -/
theorem isCompact_closure_numberFieldUnitLogDomain : IsCompact (closure (numberFieldUnitLogDomain K)) :=
  isBounded_numberFieldUnitLogDomain.isCompact_closure

/-- One positive bound controls all completed profile coordinates on the unit domain. -/
theorem exists_bound_numberFieldWeightedLogProfile_unitDomain :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ numberFieldUnitLogDomain K,
      ∀ v : InfinitePlace K, |numberFieldWeightedLogProfile x v| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closure_numberFieldUnitLogDomain (K := K)).bddAbove_image
    ((continuous_numberFieldWeightedLogProfile (K := K)).norm.continuousOn)
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro x hx v
  have hnorm : ‖numberFieldWeightedLogProfile x‖ ≤ M := hM ⟨x, subset_closure hx, rfl⟩
  exact ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp le_rfl v).trans
    (hnorm.trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one)))

end GaloisForLFunctions.HTGeometry
