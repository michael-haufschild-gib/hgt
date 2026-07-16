import GaloisForLFunctions.HTGeometry.RankThreePeriodNonHausdorff
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Period-incidence multipliers and the discrete/nondiscrete phase transition

For a group of complex periods, the canonical bounded regularization
`z ↦ z / (1 + ‖z‖)` defines a diagonal incidence operator on the bounded
nonzero-period modes.  This module proves the exact topological dichotomy:

* a discrete period group has a uniform nonzero-period gap, so the incidence
  operator is surjective and has closed range;
* a nondiscrete period group supplies unit modes whose images converge to zero,
  so the injective incidence operator has nonclosed range;
* every finite nonzero diagonal truncation remains bijective.

Thus rank-three period geometry gives an unconditional, source-independent
example in which all finite modal problems are exact while the cofinal problem
has genuine closure-only solutions.
-/

open Filter
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

theorem not_isClosed_range_of_injective_of_unit_vectors_tendsto_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : Function.Injective T)
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ = 1)
    (hzero : Tendsto (fun n ↦ T (u n)) atTop (𝓝 0)) :
    ¬ IsClosed (Set.range T) := by
  intro hclosed
  let e : E ≃L[ℂ] T.range := T.equivRange hT hclosed
  have hsub : Tendsto (fun n ↦ (⟨T (u n), T.mem_range_self (u n)⟩ : T.range))
      atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    simpa using hzero
  have hinv := e.symm.continuous.continuousAt.tendsto.comp hsub
  have hu0 : Tendsto u atTop (𝓝 0) := by
    convert hinv using 1
    · funext n
      exact (T.equivRange_symm_apply hT hclosed (u n)).symm
    · simp
  have hnorm : Tendsto (fun n ↦ ‖u n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hu0
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [hu] using hnorm
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
  norm_num at h10

def NonzeroPeriod (L : Submodule ℤ ℂ) :=
  {q : L // (q.1 : ℂ) ≠ 0}

def regularizedPeriodWeight (z : ℂ) : ℂ :=
  z / ((1 + ‖z‖ : ℝ) : ℂ)

theorem regularizedPeriodWeight_ne_zero {z : ℂ} (hz : z ≠ 0) :
    regularizedPeriodWeight z ≠ 0 := by
  apply div_ne_zero hz
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖z‖).ne'

theorem norm_regularizedPeriodWeight_le_one (z : ℂ) :
    ‖regularizedPeriodWeight z‖ ≤ 1 := by
  rw [regularizedPeriodWeight, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)]
  exact (div_le_one (by positivity : (0 : ℝ) < 1 + ‖z‖)).2 (by linarith [norm_nonneg z])

theorem norm_regularizedPeriodWeight (z : ℂ) :
    ‖regularizedPeriodWeight z‖ = ‖z‖ / (1 + ‖z‖) := by
  rw [regularizedPeriodWeight, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)]

theorem norm_regularizedPeriodWeight_inv_le
    {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ε ≤ ‖z‖) :
    ‖(regularizedPeriodWeight z)⁻¹‖ ≤ 1 + ε⁻¹ := by
  have hzpos : 0 < ‖z‖ := hε.trans_le hz
  rw [norm_inv, norm_regularizedPeriodWeight]
  have heq : (‖z‖ / (1 + ‖z‖))⁻¹ = 1 + ‖z‖⁻¹ := by
    field_simp [hzpos.ne']
    ring
  rw [heq]
  simpa [one_div, add_comm] using
    add_le_add_left (one_div_le_one_div_of_le hε hz) 1

def periodWeightVector (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ regularizedPeriodWeight q.1.1,
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      exact norm_regularizedPeriodWeight_le_one q.1.1⟩⟩

def periodIncidenceMultiplier (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ →L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ where
  toFun x := periodWeightVector L * x
  map_add' x y := by rw [mul_add]
  map_smul' c x := by
    ext q
    simp [periodWeightVector, lp.infty_coeFn_mul, mul_comm, mul_left_comm]
  cont := continuous_const.mul continuous_id

@[simp] theorem periodIncidenceMultiplier_apply
    (L : Submodule ℤ ℂ) (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞)
    (q : NonzeroPeriod L) :
    periodIncidenceMultiplier L x q = regularizedPeriodWeight q.1.1 * x q := rfl

theorem periodIncidenceMultiplier_injective (L : Submodule ℤ ℂ) :
    Function.Injective (periodIncidenceMultiplier L) := by
  intro x y hxy
  apply lp.ext
  funext q
  have hq := congrArg (fun z : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ↦ z q) hxy
  simp only [periodIncidenceMultiplier_apply] at hq
  exact mul_left_cancel₀ (regularizedPeriodWeight_ne_zero q.2) hq

def periodUnitVector (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  by
    classical
    exact lp.single ∞ q 1

theorem norm_periodUnitVector (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    ‖periodUnitVector L q‖ = 1 := by
  classical
  rw [periodUnitVector, lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞)]
  norm_num

theorem periodIncidenceMultiplier_unitVector
    (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    periodIncidenceMultiplier L (periodUnitVector L q) =
      regularizedPeriodWeight q.1.1 • periodUnitVector L q := by
  classical
  apply lp.ext
  funext j
  by_cases hj : j = q
  · subst j
    simp [periodUnitVector, periodIncidenceMultiplier_apply]
  · change regularizedPeriodWeight j.1.1 *
        (Pi.single q (1 : ℂ) : NonzeroPeriod L → ℂ) j =
      regularizedPeriodWeight q.1.1 *
        (Pi.single q (1 : ℂ) : NonzeroPeriod L → ℂ) j
    rw [Pi.single_eq_of_ne hj]
    simp

theorem tendsto_regularizedPeriodWeight_zero
    {p : ℕ → ℂ} (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularizedPeriodWeight (p n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hnorm : Tendsto (fun n ↦ ‖p n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hp
  have hdiv : Tendsto (fun n ↦ ‖p n‖ / (1 + ‖p n‖)) atTop (𝓝 (0 / (1 + 0))) :=
    hnorm.div (tendsto_const_nhds.add hnorm) (by norm_num)
  have hnormeq : (fun n ↦ ‖regularizedPeriodWeight (p n)‖) =
      fun n ↦ ‖p n‖ / (1 + ‖p n‖) := by
    funext n
    rw [regularizedPeriodWeight, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖p n‖)]
  rw [hnormeq]
  simpa using hdiv

theorem periodIncidenceMultiplier_not_isClosed_range_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    ¬ IsClosed (Set.range (periodIncidenceMultiplier L)) := by
  classical
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    GaloisForLFunctions.exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
  let u : ℕ → lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ := fun n ↦ periodUnitVector L (q n)
  apply not_isClosed_range_of_injective_of_unit_vectors_tendsto_zero
    (periodIncidenceMultiplier L) (periodIncidenceMultiplier_injective L) u
  · intro n
    exact norm_periodUnitVector L (q n)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hweight := tendsto_regularizedPeriodWeight_zero hp0
    have hweightNorm : Tendsto (fun n ↦ ‖regularizedPeriodWeight (p n)‖)
        atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp hweight
    convert hweightNorm using 1
    funext n
    rw [periodIncidenceMultiplier_unitVector, norm_smul, norm_periodUnitVector, mul_one]

theorem exists_period_norm_gap_of_discrete
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖ := by
  have hopen : IsOpen ({0} : Set L) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.1 hopen) 0 (by simp)
  refine ⟨ε, hε, fun q ↦ ?_⟩
  by_contra hq
  have hmem : q.1 ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    simpa using lt_of_not_ge hq
  have hzero : q.1 = 0 := Set.mem_singleton_iff.mp (hball hmem)
  exact q.2 (congrArg Subtype.val hzero)

def periodInverseWeightVector (L : Submodule ℤ ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ (regularizedPeriodWeight q.1.1)⁻¹,
    memℓp_infty ⟨1 + ε⁻¹, by
      rintro _ ⟨q, rfl⟩
      exact norm_regularizedPeriodWeight_inv_le hε (hgap q)⟩⟩

def periodIncidenceInverse (L : Submodule ℤ ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ →L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ where
  toFun x := periodInverseWeightVector L ε hε hgap * x
  map_add' x y := by rw [mul_add]
  map_smul' c x := by
    ext q
    simp [periodInverseWeightVector, lp.infty_coeFn_mul, mul_comm, mul_left_comm]
  cont := continuous_const.mul continuous_id

@[simp] theorem periodIncidenceInverse_apply
    (L : Submodule ℤ ℂ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) (q : NonzeroPeriod L) :
    periodIncidenceInverse L ε hε hgap x q =
      (regularizedPeriodWeight q.1.1)⁻¹ * x q := rfl

theorem periodIncidenceMultiplier_surjective_of_gap
    (L : Submodule ℤ ℂ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖) :
    Function.Surjective (periodIncidenceMultiplier L) := by
  intro y
  refine ⟨periodIncidenceInverse L ε hε hgap y, ?_⟩
  apply lp.ext
  funext q
  rw [periodIncidenceMultiplier_apply, periodIncidenceInverse_apply,
    ← mul_assoc, mul_inv_cancel₀ (regularizedPeriodWeight_ne_zero q.2), one_mul]

theorem periodIncidenceMultiplier_isClosed_range_of_discrete
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    IsClosed (Set.range (periodIncidenceMultiplier L)) := by
  obtain ⟨ε, hε, hgap⟩ := exists_period_norm_gap_of_discrete L
  have hsurj := periodIncidenceMultiplier_surjective_of_gap L ε hε hgap
  have hrange : Set.range (periodIncidenceMultiplier L) = Set.univ :=
    Set.range_eq_univ.mpr hsurj
  rw [hrange]
  exact isClosed_univ

/-- Closed range is equivalent to discreteness of the period group.  This is the exact
topological phase discriminator for the regularized period-incidence operator. -/
theorem periodIncidenceMultiplier_isClosed_range_iff_discrete
    (L : Submodule ℤ ℂ) :
    IsClosed (Set.range (periodIncidenceMultiplier L)) ↔ DiscreteTopology L := by
  constructor
  · intro hclosed
    by_contra hnondiscrete
    exact periodIncidenceMultiplier_not_isClosed_range_of_not_discrete L hnondiscrete hclosed
  · intro hdiscrete
    letI : DiscreteTopology L := hdiscrete
    exact periodIncidenceMultiplier_isClosed_range_of_discrete L

/-- Surjectivity is equivalent to discreteness as well: a discrete period group has a bounded
diagonal inverse, while surjectivity would force the range to be closed. -/
theorem periodIncidenceMultiplier_surjective_iff_discrete
    (L : Submodule ℤ ℂ) :
    Function.Surjective (periodIncidenceMultiplier L) ↔ DiscreteTopology L := by
  constructor
  · intro hsurjective
    apply (periodIncidenceMultiplier_isClosed_range_iff_discrete L).mp
    rw [Set.range_eq_univ.mpr hsurjective]
    exact isClosed_univ
  · intro hdiscrete
    letI : DiscreteTopology L := hdiscrete
    obtain ⟨ε, hε, hgap⟩ := exists_period_norm_gap_of_discrete L
    exact periodIncidenceMultiplier_surjective_of_gap L ε hε hgap

theorem finiteNonzeroDiagonal_bijective {n : ℕ}
    (weight : Fin n → ℂ) (hweight : ∀ i, weight i ≠ 0) :
    Function.Bijective (fun x : Fin n → ℂ ↦ fun i ↦ weight i * x i) := by
  constructor
  · intro x y hxy
    funext i
    exact mul_left_cancel₀ (hweight i) (congrFun hxy i)
  · intro y
    refine ⟨fun i ↦ (weight i)⁻¹ * y i, ?_⟩
    funext i
    change weight i * ((weight i)⁻¹ * y i) = y i
    rw [← mul_assoc, mul_inv_cancel₀ (hweight i), one_mul]

theorem exists_mem_closure_not_mem_of_not_isClosed
    {E : Type*} [TopologicalSpace E] {s : Set E} (hs : ¬ IsClosed s) :
    ∃ x, x ∈ closure s ∧ x ∉ s := by
  by_contra h
  push Not at h
  have heq : closure s = s := Set.Subset.antisymm h subset_closure
  apply hs
  rw [← heq]
  exact isClosed_closure

theorem rankThreePeriodIncidenceMultiplier_not_isClosed_range
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ¬ IsClosed (Set.range
      (periodIncidenceMultiplier (Submodule.span ℤ (Set.range v)))) :=
  periodIncidenceMultiplier_not_isClosed_range_of_not_discrete _
    (GaloisForLFunctions.not_discrete_intSpan_fin_three v hv)

theorem exists_rankThreePeriodIncidence_closureOnly
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ∃ b,
      b ∈ closure (Set.range
        (periodIncidenceMultiplier (Submodule.span ℤ (Set.range v)))) ∧
      b ∉ Set.range
        (periodIncidenceMultiplier (Submodule.span ℤ (Set.range v))) :=
  exists_mem_closure_not_mem_of_not_isClosed
    (rankThreePeriodIncidenceMultiplier_not_isClosed_range v hv)

end

end Scratch
