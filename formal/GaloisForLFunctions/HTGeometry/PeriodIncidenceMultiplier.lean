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

theorem norm_regularizedPeriodWeight_lt_one (z : ℂ) :
    ‖regularizedPeriodWeight z‖ < 1 := by
  rw [norm_regularizedPeriodWeight]
  exact (div_lt_one (by positivity : (0 : ℝ) < 1 + ‖z‖)).2 (by linarith [norm_nonneg z])

/-- The bounded radial incidence symbol loses no period data. -/
theorem regularizedPeriodWeight_reconstruct (z : ℂ) :
    regularizedPeriodWeight z /
        ((1 - ‖regularizedPeriodWeight z‖ : ℝ) : ℂ) = z := by
  rw [norm_regularizedPeriodWeight, regularizedPeriodWeight]
  have hpos : (0 : ℝ) < 1 + ‖z‖ := by positivity
  have hreal : 1 - ‖z‖ / (1 + ‖z‖) = 1 / (1 + ‖z‖) := by
    field_simp [hpos.ne']
    ring
  rw [hreal]
  push_cast
  have hc' : (1 + (‖z‖ : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [norm_nonneg z]
  field_simp [hc']

theorem regularizedPeriodWeight_injective :
    Function.Injective regularizedPeriodWeight := by
  intro z w hzw
  calc
    z = regularizedPeriodWeight z /
        ((1 - ‖regularizedPeriodWeight z‖ : ℝ) : ℂ) :=
      (regularizedPeriodWeight_reconstruct z).symm
    _ = regularizedPeriodWeight w /
        ((1 - ‖regularizedPeriodWeight w‖ : ℝ) : ℂ) := by rw [hzw]
    _ = w := regularizedPeriodWeight_reconstruct w

def regularizedPeriodSpectrum (L : Submodule ℤ ℂ) : Set ℂ :=
  regularizedPeriodWeight '' (L : Set ℂ)

/-- The unordered bounded symbol spectrum reconstructs the embedded integral period module. -/
theorem regularizedPeriodSpectrum_eq_iff
    (L K : Submodule ℤ ℂ) :
    regularizedPeriodSpectrum L = regularizedPeriodSpectrum K ↔ L = K := by
  constructor
  · intro hLK
    apply le_antisymm
    · intro z hz
      have hwL : regularizedPeriodWeight z ∈ regularizedPeriodSpectrum L :=
        ⟨z, hz, rfl⟩
      rw [hLK] at hwL
      obtain ⟨w, hwK, hwz⟩ := hwL
      have hw : w = z := regularizedPeriodWeight_injective hwz
      simpa [hw] using hwK
    · intro z hz
      have hwK : regularizedPeriodWeight z ∈ regularizedPeriodSpectrum K :=
        ⟨z, hz, rfl⟩
      rw [← hLK] at hwK
      obtain ⟨w, hwL, hwz⟩ := hwK
      have hw : w = z := regularizedPeriodWeight_injective hwz
      simpa [hw] using hwL
  · rintro rfl
    rfl

/-- The positive half-density of the regularized period-incidence symbol. -/
def periodIncidenceHalfDensity (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ (Real.sqrt ‖regularizedPeriodWeight q.1.1‖ : ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      change ‖(Real.sqrt ‖regularizedPeriodWeight q.1.1‖ : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      apply (Real.sqrt_le_iff).2
      exact ⟨by norm_num, by
        simpa using norm_regularizedPeriodWeight_le_one q.1.1⟩⟩⟩

@[simp] theorem periodIncidenceHalfDensity_apply
    (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    periodIncidenceHalfDensity L q =
      (Real.sqrt ‖regularizedPeriodWeight q.1.1‖ : ℂ) := rfl

/-- The cutoff inverse of the half-density at symbol size `δ²`. -/
def periodIncidenceHalfDensityCutoffPreimage
    (L : Submodule ℤ ℂ) (δ : ℝ) (hδ : 0 < δ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ if δ ^ 2 ≤ ‖regularizedPeriodWeight q.1.1‖ then
      (Real.sqrt ‖regularizedPeriodWeight q.1.1‖ : ℂ) /
        regularizedPeriodWeight q.1.1
    else 0,
    memℓp_infty ⟨δ⁻¹, by
      rintro _ ⟨q, rfl⟩
      by_cases hq : δ ^ 2 ≤ ‖regularizedPeriodWeight q.1.1‖
      · simp only [if_pos hq]
        rw [norm_div, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        let a : ℝ := ‖regularizedPeriodWeight q.1.1‖
        have ha0 : 0 ≤ a := norm_nonneg _
        have hapos : 0 < a := lt_of_lt_of_le (sq_pos_of_pos hδ) hq
        have hspos : 0 < Real.sqrt a := Real.sqrt_pos.2 hapos
        have hδs : δ ≤ Real.sqrt a := by
          rw [← Real.sqrt_sq hδ.le]
          exact Real.sqrt_le_sqrt hq
        have heq : Real.sqrt a / a = (Real.sqrt a)⁻¹ := by
          conv_lhs => rhs; rw [← Real.sq_sqrt ha0]
          field_simp [hspos.ne']
        rw [heq]
        simpa [one_div] using one_div_le_one_div_of_le hδ hδs
      · simp [hq, inv_nonneg.mpr hδ.le]⟩⟩

theorem periodIncidenceMultiplier_halfDensityCutoff_apply
    (L : Submodule ℤ ℂ) (δ : ℝ) (hδ : 0 < δ) (q : NonzeroPeriod L) :
    periodIncidenceMultiplier L
        (periodIncidenceHalfDensityCutoffPreimage L δ hδ) q =
      if δ ^ 2 ≤ ‖regularizedPeriodWeight q.1.1‖ then
        periodIncidenceHalfDensity L q
      else 0 := by
  by_cases hq : δ ^ 2 ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [periodIncidenceMultiplier_apply]
    simp only [periodIncidenceHalfDensityCutoffPreimage, if_pos hq,
      periodIncidenceHalfDensity_apply]
    field_simp [regularizedPeriodWeight_ne_zero q.2]
  · simp [periodIncidenceMultiplier_apply,
      periodIncidenceHalfDensityCutoffPreimage, hq]

theorem norm_periodIncidenceMultiplier_halfDensityCutoff_sub_le
    (L : Submodule ℤ ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ‖periodIncidenceMultiplier L
          (periodIncidenceHalfDensityCutoffPreimage L δ hδ) -
        periodIncidenceHalfDensity L‖ ≤ δ := by
  apply lp.norm_le_of_forall_le hδ.le
  intro q
  change ‖periodIncidenceMultiplier L
      (periodIncidenceHalfDensityCutoffPreimage L δ hδ) q -
        periodIncidenceHalfDensity L q‖ ≤ δ
  by_cases hq : δ ^ 2 ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [periodIncidenceMultiplier_halfDensityCutoff_apply, if_pos hq]
    simpa using hδ.le
  · rw [periodIncidenceMultiplier_halfDensityCutoff_apply, if_neg hq]
    simp only [zero_sub, norm_neg, periodIncidenceHalfDensity_apply,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_lt' hδ).2 (lt_of_not_ge hq) |>.le

/-- The canonical half-density is always weakly attainable. -/
theorem periodIncidenceHalfDensity_mem_closure_range
    (L : Submodule ℤ ℂ) :
    periodIncidenceHalfDensity L ∈
      closure (Set.range (periodIncidenceMultiplier L)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  refine ⟨periodIncidenceMultiplier L
      (periodIncidenceHalfDensityCutoffPreimage L δ hδ),
    Set.mem_range_self _, ?_⟩
  rw [dist_eq_norm]
  have hbound :=
    norm_periodIncidenceMultiplier_halfDensityCutoff_sub_le L δ hδ
  rw [norm_sub_rev]
  exact hbound.trans_lt (half_lt_self hε)

/-- For a nondiscrete period group, the half-density has no bounded exact preimage. -/
theorem periodIncidenceHalfDensity_not_mem_range_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    periodIncidenceHalfDensity L ∉
      Set.range (periodIncidenceMultiplier L) := by
  classical
  rintro ⟨x, hx⟩
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
  let a : ℕ → ℝ := fun n ↦ ‖regularizedPeriodWeight (p n)‖
  have ha0 : Tendsto a atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp
      (tendsto_regularizedPeriodWeight_zero hp0)
  have hapos : ∀ n, 0 < a n := fun n ↦
    norm_pos_iff.mpr (regularizedPeriodWeight_ne_zero (hpne n))
  have hs0 : Tendsto (fun n ↦ Real.sqrt (a n)) atTop (𝓝 0) :=
    by
      simpa only [Function.comp_apply, Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp ha0
  have hsGT : Tendsto (fun n ↦ Real.sqrt (a n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨hs0, Eventually.of_forall fun n ↦ Real.sqrt_pos.2 (hapos n)⟩
  have hinv : Tendsto (fun n ↦ (Real.sqrt (a n))⁻¹) atTop atTop :=
    hsGT.inv_tendsto_nhdsGT_zero
  have hinv_eq : ∀ n, (Real.sqrt (a n))⁻¹ = ‖x (q n)‖ := by
    intro n
    have hcoord := congrArg
      (fun z : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ↦ z (q n)) hx
    have hnorm := congrArg norm hcoord
    simp only [periodIncidenceMultiplier_apply,
      periodIncidenceHalfDensity_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hnorm
    change a n * ‖x (q n)‖ = Real.sqrt (a n) at hnorm
    have hane : a n ≠ 0 := (hapos n).ne'
    have hsne : Real.sqrt (a n) ≠ 0 := (Real.sqrt_pos.2 (hapos n)).ne'
    calc
      (Real.sqrt (a n))⁻¹ = Real.sqrt (a n) / a n := by
        conv_rhs => rhs; rw [← Real.sq_sqrt (hapos n).le]
        field_simp [hsne]
      _ = ‖x (q n)‖ := by
        rw [← hnorm]
        field_simp [hane]
  have hevent : ∀ᶠ n in atTop, ‖x‖ < (Real.sqrt (a n))⁻¹ :=
    hinv.eventually (eventually_gt_atTop ‖x‖)
  obtain ⟨n, hn⟩ := hevent.exists
  rw [hinv_eq n] at hn
  exact (not_lt_of_ge (lp.norm_apply_le_norm ENNReal.top_ne_zero x (q n))) hn

theorem periodIncidenceHalfDensity_closureOnly_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    periodIncidenceHalfDensity L ∈
        closure (Set.range (periodIncidenceMultiplier L)) ∧
      periodIncidenceHalfDensity L ∉
        Set.range (periodIncidenceMultiplier L) :=
  ⟨periodIncidenceHalfDensity_mem_closure_range L,
    periodIncidenceHalfDensity_not_mem_range_of_not_discrete L hL⟩

/-- The symbol itself is the canonical exact target. -/
def periodIncidenceExactTarget (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  periodWeightVector L

theorem periodIncidenceExactTarget_mem_range (L : Submodule ℤ ℂ) :
    periodIncidenceExactTarget L ∈
      Set.range (periodIncidenceMultiplier L) := by
  refine ⟨1, ?_⟩
  apply lp.ext
  funext q
  simp [periodIncidenceExactTarget, periodIncidenceMultiplier_apply,
    periodWeightVector]

/-- The unweighted unit section is the canonical exterior target. -/
def periodIncidenceExteriorTarget (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  1

@[simp] theorem periodIncidenceExteriorTarget_apply
    (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    periodIncidenceExteriorTarget L q = 1 := rfl

theorem periodIncidenceExteriorTarget_distance_ge_one_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) :
    1 ≤ ‖periodIncidenceExteriorTarget L - periodIncidenceMultiplier L x‖ := by
  classical
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
  have hweight := tendsto_regularizedPeriodWeight_zero hp0
  have hweightNorm :
      Tendsto (fun n ↦ ‖regularizedPeriodWeight (p n)‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hweight
  have hproduct : Tendsto
      (fun n ↦ regularizedPeriodWeight (p n) * x (q n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
      (g := fun n ↦ ‖regularizedPeriodWeight (p n)‖ * ‖x‖)
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · exact Eventually.of_forall fun n ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x (q n)) (norm_nonneg _)
    · simpa using hweightNorm.mul_const ‖x‖
  have hcoordinate : Tendsto
      (fun n ↦ periodIncidenceMultiplier L x (q n)) atTop (𝓝 0) := by
    simpa [periodIncidenceMultiplier_apply, q] using hproduct
  have hnorm : Tendsto
      (fun n ↦ ‖periodIncidenceExteriorTarget L (q n) -
        periodIncidenceMultiplier L x (q n)‖) atTop (𝓝 1) := by
    have hsub :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1)).sub
        hcoordinate
    simpa using hsub.norm
  apply le_of_tendsto hnorm
  exact Eventually.of_forall fun n ↦ by
    have hpoint := lp.norm_apply_le_norm ENNReal.top_ne_zero
      (periodIncidenceExteriorTarget L - periodIncidenceMultiplier L x) (q n)
    exact hpoint

theorem periodIncidenceExteriorTarget_not_mem_closure_range_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    periodIncidenceExteriorTarget L ∉
      closure (Set.range (periodIncidenceMultiplier L)) := by
  intro hclosure
  obtain ⟨y, ⟨x, rfl⟩, hy⟩ :=
    Metric.mem_closure_iff.1 hclosure (1 / 2 : ℝ) (by norm_num)
  rw [dist_eq_norm] at hy
  have hge := periodIncidenceExteriorTarget_distance_ge_one_of_not_discrete L hL x
  linarith

theorem periodIncidenceHalfDensity_mem_range_iff_discrete
    (L : Submodule ℤ ℂ) :
    periodIncidenceHalfDensity L ∈ Set.range (periodIncidenceMultiplier L) ↔
      DiscreteTopology L := by
  constructor
  · intro hmem
    by_contra hL
    exact periodIncidenceHalfDensity_not_mem_range_of_not_discrete L hL hmem
  · intro hL
    exact (periodIncidenceMultiplier_surjective_iff_discrete L).2 hL
      (periodIncidenceHalfDensity L)

theorem periodIncidenceExteriorTarget_mem_closure_range_iff_discrete
    (L : Submodule ℤ ℂ) :
    periodIncidenceExteriorTarget L ∈
        closure (Set.range (periodIncidenceMultiplier L)) ↔
      DiscreteTopology L := by
  constructor
  · intro hmem
    by_contra hL
    exact periodIncidenceExteriorTarget_not_mem_closure_range_of_not_discrete L hL hmem
  · intro hL
    apply subset_closure
    exact (periodIncidenceMultiplier_surjective_iff_discrete L).2 hL
      (periodIncidenceExteriorTarget L)

/-- One nondiscrete source operator realizes all three incidence phases canonically. -/
theorem periodIncidenceCanonicalTrichotomy_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    periodIncidenceExactTarget L ∈ Set.range (periodIncidenceMultiplier L) ∧
      (periodIncidenceHalfDensity L ∈
          closure (Set.range (periodIncidenceMultiplier L)) ∧
        periodIncidenceHalfDensity L ∉
          Set.range (periodIncidenceMultiplier L)) ∧
      periodIncidenceExteriorTarget L ∉
        closure (Set.range (periodIncidenceMultiplier L)) :=
  ⟨periodIncidenceExactTarget_mem_range L,
    periodIncidenceHalfDensity_closureOnly_of_not_discrete L hL,
    periodIncidenceExteriorTarget_not_mem_closure_range_of_not_discrete L hL⟩

theorem rankThreePeriodIncidenceCanonicalTrichotomy
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    let L := Submodule.span ℤ (Set.range v)
    periodIncidenceExactTarget L ∈ Set.range (periodIncidenceMultiplier L) ∧
      (periodIncidenceHalfDensity L ∈
          closure (Set.range (periodIncidenceMultiplier L)) ∧
        periodIncidenceHalfDensity L ∉
          Set.range (periodIncidenceMultiplier L)) ∧
      periodIncidenceExteriorTarget L ∉
        closure (Set.range (periodIncidenceMultiplier L)) := by
  exact periodIncidenceCanonicalTrichotomy_of_not_discrete _
    (not_discrete_intSpan_fin_three v hv)

/-! ## Powered incidence and the full fractional phase law -/

/-- The order-`r` period symbol, retaining the physical contact multiplicity. -/
def poweredPeriodWeightVector (L : Submodule ℤ ℂ) (r : ℕ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ regularizedPeriodWeight q.1.1 ^ r,
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      change ‖regularizedPeriodWeight q.1.1 ^ r‖ ≤ 1
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _)
        (norm_regularizedPeriodWeight_le_one q.1.1)⟩⟩

@[simp] theorem poweredPeriodWeightVector_apply
    (L : Submodule ℤ ℂ) (r : ℕ) (q : NonzeroPeriod L) :
    poweredPeriodWeightVector L r q = regularizedPeriodWeight q.1.1 ^ r := rfl

/-- Multiplication by the full order-`r` physical period symbol `w^r`. -/
def poweredPeriodIncidenceMultiplier (L : Submodule ℤ ℂ) (r : ℕ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ →L[ℂ]
      lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ where
  toFun x := poweredPeriodWeightVector L r * x
  map_add' x y := by rw [mul_add]
  map_smul' c x := by
    ext q
    simp [poweredPeriodWeightVector, lp.infty_coeFn_mul, mul_comm, mul_left_comm]
  cont := continuous_const.mul continuous_id

@[simp] theorem poweredPeriodIncidenceMultiplier_apply
    (L : Submodule ℤ ℂ) (r : ℕ)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) (q : NonzeroPeriod L) :
    poweredPeriodIncidenceMultiplier L r x q =
      regularizedPeriodWeight q.1.1 ^ r * x q := rfl

/-- The positive target of vanishing order `β` relative to the atomic symbol `w`. -/
def periodIncidencePowerTarget
    (L : Submodule ℤ ℂ) (β : ℝ) (hβ : 0 ≤ β) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ ((‖regularizedPeriodWeight q.1.1‖ ^ β : ℝ) : ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      change ‖((‖regularizedPeriodWeight q.1.1‖ ^ β : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_one (norm_nonneg _)
        (norm_regularizedPeriodWeight_le_one q.1.1) hβ⟩⟩

@[simp] theorem periodIncidencePowerTarget_apply
    (L : Submodule ℤ ℂ) (β : ℝ) (hβ : 0 ≤ β)
    (q : NonzeroPeriod L) :
    periodIncidencePowerTarget L β hβ q =
      ((‖regularizedPeriodWeight q.1.1‖ ^ β : ℝ) : ℂ) := rfl

theorem norm_periodIncidencePowerTarget_div_pow
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (q : NonzeroPeriod L) :
    ‖periodIncidencePowerTarget L β hβ q /
        regularizedPeriodWeight q.1.1 ^ r‖ =
      ‖regularizedPeriodWeight q.1.1‖ ^ (β - r) := by
  rw [norm_div, periodIncidencePowerTarget_apply, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), norm_pow,
    ← Real.rpow_natCast,
    ← Real.rpow_sub (norm_pos_iff.mpr (regularizedPeriodWeight_ne_zero q.2))]

/-- The bounded exact inverse for every target whose vanishing order is at least `r`. -/
def periodIncidencePowerPreimage
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (hβr : (r : ℝ) ≤ β) : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ periodIncidencePowerTarget L β hβ q /
      regularizedPeriodWeight q.1.1 ^ r,
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      change ‖periodIncidencePowerTarget L β hβ q /
        regularizedPeriodWeight q.1.1 ^ r‖ ≤ 1
      rw [norm_periodIncidencePowerTarget_div_pow]
      exact Real.rpow_le_one (norm_nonneg _)
        (norm_regularizedPeriodWeight_le_one q.1.1) (sub_nonneg.mpr hβr)⟩⟩

theorem poweredPeriodIncidenceMultiplier_powerPreimage
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (hβr : (r : ℝ) ≤ β) :
    poweredPeriodIncidenceMultiplier L r
        (periodIncidencePowerPreimage L r β hβ hβr) =
      periodIncidencePowerTarget L β hβ := by
  apply lp.ext
  funext q
  change regularizedPeriodWeight q.1.1 ^ r *
      (periodIncidencePowerTarget L β hβ q /
        regularizedPeriodWeight q.1.1 ^ r) =
    periodIncidencePowerTarget L β hβ q
  field_simp [pow_ne_zero r (regularizedPeriodWeight_ne_zero q.2)]

theorem periodIncidencePowerTarget_mem_range_of_natCast_le
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (hβr : (r : ℝ) ≤ β) :
    periodIncidencePowerTarget L β hβ ∈
      Set.range (poweredPeriodIncidenceMultiplier L r) :=
  ⟨periodIncidencePowerPreimage L r β hβ hβr,
    poweredPeriodIncidenceMultiplier_powerPreimage L r β hβ hβr⟩

/-- Cut off division by `w^r` below atomic symbol size `δ`. -/
def periodIncidencePowerCutoffPreimage
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (δ : ℝ) (hδ : 0 < δ) : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ if δ ≤ ‖regularizedPeriodWeight q.1.1‖ then
      periodIncidencePowerTarget L β hβ q /
        regularizedPeriodWeight q.1.1 ^ r
    else 0,
    memℓp_infty ⟨max 1 (δ ^ (β - r)), by
      rintro _ ⟨q, rfl⟩
      by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
      · simp only [if_pos hq]
        rw [norm_periodIncidencePowerTarget_div_pow]
        by_cases hexp : 0 ≤ β - (r : ℝ)
        · exact (Real.rpow_le_one (norm_nonneg _)
            (norm_regularizedPeriodWeight_le_one q.1.1) hexp).trans
              (le_max_left _ _)
        · exact (Real.rpow_le_rpow_of_nonpos hδ hq (le_of_not_ge hexp)).trans
              (le_max_right _ _)
      · simp only [if_neg hq, norm_zero]
        exact (by positivity : (0 : ℝ) ≤ max 1 (δ ^ (β - r)))⟩⟩

theorem poweredPeriodIncidenceMultiplier_cutoff_apply
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (δ : ℝ) (hδ : 0 < δ) (q : NonzeroPeriod L) :
    poweredPeriodIncidenceMultiplier L r
        (periodIncidencePowerCutoffPreimage L r β hβ δ hδ) q =
      if δ ≤ ‖regularizedPeriodWeight q.1.1‖ then
        periodIncidencePowerTarget L β hβ q
      else 0 := by
  by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [poweredPeriodIncidenceMultiplier_apply]
    simp only [periodIncidencePowerCutoffPreimage, if_pos hq]
    field_simp [pow_ne_zero r (regularizedPeriodWeight_ne_zero q.2)]
  · simp [poweredPeriodIncidenceMultiplier_apply,
      periodIncidencePowerCutoffPreimage, hq]

theorem norm_poweredPeriodIncidenceMultiplier_cutoff_sub_le
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 ≤ β)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖poweredPeriodIncidenceMultiplier L r
          (periodIncidencePowerCutoffPreimage L r β hβ δ hδ) -
        periodIncidencePowerTarget L β hβ‖ ≤ δ ^ β := by
  apply lp.norm_le_of_forall_le (Real.rpow_nonneg hδ.le β)
  intro q
  change ‖poweredPeriodIncidenceMultiplier L r
      (periodIncidencePowerCutoffPreimage L r β hβ δ hδ) q -
        periodIncidencePowerTarget L β hβ q‖ ≤ δ ^ β
  by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [poweredPeriodIncidenceMultiplier_cutoff_apply, if_pos hq]
    simpa using Real.rpow_nonneg hδ.le β
  · rw [poweredPeriodIncidenceMultiplier_cutoff_apply, if_neg hq]
    simp only [zero_sub, norm_neg, periodIncidencePowerTarget_apply,
      Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (le_of_not_ge hq) hβ

/-- Every positive fractional target is approximable by bounded cutoff inverses. -/
theorem periodIncidencePowerTarget_mem_closure_range_of_pos
    (L : Submodule ℤ ℂ) (r : ℕ) (β : ℝ) (hβ : 0 < β) :
    periodIncidencePowerTarget L β hβ.le ∈
      closure (Set.range (poweredPeriodIncidenceMultiplier L r)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpowzero : Tendsto (fun n ↦ δ n ^ β) atTop (𝓝 0) := by
    have hcont :=
      (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp hδzero
    simpa [Real.zero_rpow hβ.ne'] using hcont
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpowzero) ε hε
  have hδpos : 0 < δ N := by
    dsimp [δ]
    positivity
  have hpowlt : δ N ^ β < ε := by
    have h := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (Real.rpow_nonneg hδpos.le β)] using h
  refine ⟨poweredPeriodIncidenceMultiplier L r
      (periodIncidencePowerCutoffPreimage L r β hβ.le (δ N) hδpos),
    Set.mem_range_self _, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_poweredPeriodIncidenceMultiplier_cutoff_sub_le
    L r β hβ.le (δ N) hδpos).trans_lt hpowlt

/-- Below order `r`, exact inversion would force an unbounded inverse source. -/
theorem periodIncidencePowerTarget_not_mem_range_of_lt_natCast
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (β : ℝ) (hβ : 0 < β) (hβr : β < (r : ℝ)) :
    periodIncidencePowerTarget L β hβ.le ∉
      Set.range (poweredPeriodIncidenceMultiplier L r) := by
  classical
  rintro ⟨x, hx⟩
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
  let a : ℕ → ℝ := fun n ↦ ‖regularizedPeriodWeight (p n)‖
  have ha0 : Tendsto a atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp
      (tendsto_regularizedPeriodWeight_zero hp0)
  have hapos : ∀ n, 0 < a n := fun n ↦
    norm_pos_iff.mpr (regularizedPeriodWeight_ne_zero (hpne n))
  let γ : ℝ := (r : ℝ) - β
  have hγ : 0 < γ := sub_pos.mpr hβr
  have hpow0 : Tendsto (fun n ↦ a n ^ γ) atTop (𝓝 0) := by
    have hcont :=
      (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp ha0
    simpa [Real.zero_rpow hγ.ne'] using hcont
  have hpowGT : Tendsto (fun n ↦ a n ^ γ) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨hpow0, Eventually.of_forall fun n ↦ Real.rpow_pos_of_pos (hapos n) γ⟩
  have hinv : Tendsto (fun n ↦ (a n ^ γ)⁻¹) atTop atTop :=
    hpowGT.inv_tendsto_nhdsGT_zero
  have hinv_eq : ∀ n, (a n ^ γ)⁻¹ = ‖x (q n)‖ := by
    intro n
    have hcoord := congrArg
      (fun z : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ↦ z (q n)) hx
    have hnorm := congrArg norm hcoord
    simp only [poweredPeriodIncidenceMultiplier_apply,
      periodIncidencePowerTarget_apply, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hnorm
    change a n ^ r * ‖x (q n)‖ = a n ^ β at hnorm
    calc
      (a n ^ γ)⁻¹ = a n ^ (-γ) :=
        (Real.rpow_neg (hapos n).le γ).symm
      _ = a n ^ (β - (r : ℝ)) := by
        congr 1
        dsimp [γ]
        ring
      _ = a n ^ β / a n ^ (r : ℝ) :=
        Real.rpow_sub (hapos n) β (r : ℝ)
      _ = ‖x (q n)‖ := by
        rw [Real.rpow_natCast, ← hnorm]
        field_simp [pow_ne_zero r (hapos n).ne']
  have hevent : ∀ᶠ n in atTop, ‖x‖ < (a n ^ γ)⁻¹ :=
    hinv.eventually (eventually_gt_atTop ‖x‖)
  obtain ⟨n, hn⟩ := hevent.exists
  rw [hinv_eq n] at hn
  exact (not_lt_of_ge (lp.norm_apply_le_norm ENNReal.top_ne_zero x (q n))) hn

theorem periodIncidencePowerTarget_closureOnly_of_between
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (β : ℝ) (hβ : 0 < β) (hβr : β < (r : ℝ)) :
    periodIncidencePowerTarget L β hβ.le ∈
        closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      periodIncidencePowerTarget L β hβ.le ∉
        Set.range (poweredPeriodIncidenceMultiplier L r) :=
  ⟨periodIncidencePowerTarget_mem_closure_range_of_pos L r β hβ,
    periodIncidencePowerTarget_not_mem_range_of_lt_natCast L hL r β hβ hβr⟩

theorem poweredPeriodIncidenceMultiplier_range_subset
    (L : Submodule ℤ ℂ) (r : ℕ) (hr : 1 ≤ r) :
    Set.range (poweredPeriodIncidenceMultiplier L r) ⊆
      Set.range (periodIncidenceMultiplier L) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨poweredPeriodWeightVector L (r - 1) * x, ?_⟩
  apply lp.ext
  funext q
  change regularizedPeriodWeight q.1.1 *
      (regularizedPeriodWeight q.1.1 ^ (r - 1) * x q) =
    regularizedPeriodWeight q.1.1 ^ r * x q
  rw [← mul_assoc, ← pow_succ']
  congr 2
  omega

theorem poweredPeriodIncidenceExteriorTarget_not_mem_closure_range
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (hr : 1 ≤ r) :
    periodIncidenceExteriorTarget L ∉
      closure (Set.range (poweredPeriodIncidenceMultiplier L r)) := by
  intro hmem
  exact periodIncidenceExteriorTarget_not_mem_closure_range_of_not_discrete L hL
    (closure_mono (poweredPeriodIncidenceMultiplier_range_subset L r hr) hmem)

/-- The order-`r` target corresponding to normalized fractional exponent `α`. -/
def poweredPeriodIncidenceFractionalTarget
    (L : Submodule ℤ ℂ) (r : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  periodIncidencePowerTarget L ((r : ℝ) * α)
    (mul_nonneg (Nat.cast_nonneg r) hα)

@[simp] theorem poweredPeriodIncidenceFractionalTarget_apply
    (L : Submodule ℤ ℂ) (r : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (q : NonzeroPeriod L) :
    poweredPeriodIncidenceFractionalTarget L r α hα q =
      ((‖regularizedPeriodWeight q.1.1‖ ^ ((r : ℝ) * α) : ℝ) : ℂ) := rfl

theorem poweredPeriodIncidenceFractionalTarget_zero
    (L : Submodule ℤ ℂ) (r : ℕ) :
    poweredPeriodIncidenceFractionalTarget L r 0 le_rfl =
      periodIncidenceExteriorTarget L := by
  apply lp.ext
  funext q
  simp [poweredPeriodIncidenceFractionalTarget,
    periodIncidenceExteriorTarget_apply]

/-- The exact `α=0`, closure-only `0<α<1`, exact `α≥1` phase law. -/
theorem poweredPeriodIncidenceFractionalPhaseLaw
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (hr : 1 ≤ r) (α : ℝ) (hα : 0 ≤ α) :
    (α = 0 → poweredPeriodIncidenceFractionalTarget L r α hα ∉
        closure (Set.range (poweredPeriodIncidenceMultiplier L r))) ∧
      (0 < α → α < 1 →
        poweredPeriodIncidenceFractionalTarget L r α hα ∈
            closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
          poweredPeriodIncidenceFractionalTarget L r α hα ∉
            Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      (1 ≤ α → poweredPeriodIncidenceFractionalTarget L r α hα ∈
        Set.range (poweredPeriodIncidenceMultiplier L r)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  constructor
  · intro hα0
    subst α
    simpa [poweredPeriodIncidenceFractionalTarget_zero] using
      poweredPeriodIncidenceExteriorTarget_not_mem_closure_range L hL r hr
  constructor
  · intro hαpos hαone
    have hβpos : 0 < (r : ℝ) * α := mul_pos hrpos hαpos
    have hβr : (r : ℝ) * α < (r : ℝ) := by
      simpa using mul_lt_mul_of_pos_left hαone hrpos
    simpa [poweredPeriodIncidenceFractionalTarget] using
      periodIncidencePowerTarget_closureOnly_of_between
        L hL r ((r : ℝ) * α) hβpos hβr
  · intro hαone
    have hβr : (r : ℝ) ≤ (r : ℝ) * α := by
      simpa using mul_le_mul_of_nonneg_left hαone hrpos.le
    exact periodIncidencePowerTarget_mem_range_of_natCast_le
      L r ((r : ℝ) * α) (mul_nonneg hrpos.le hα) hβr

/-- The normalized self-dual target `α=1/2`, with unnormalized order `r/2`. -/
def poweredPeriodIncidenceHalfDensity (L : Submodule ℤ ℂ) (r : ℕ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  poweredPeriodIncidenceFractionalTarget L r (1 / 2) (by norm_num)

theorem poweredPeriodIncidenceHalfDensity_apply
    (L : Submodule ℤ ℂ) (r : ℕ) (q : NonzeroPeriod L) :
    poweredPeriodIncidenceHalfDensity L r q =
      (Real.sqrt ‖regularizedPeriodWeight q.1.1 ^ r‖ : ℂ) := by
  change ((‖regularizedPeriodWeight q.1.1‖ ^ ((r : ℝ) * (1 / 2 : ℝ)) : ℝ) : ℂ) =
    (Real.sqrt ‖regularizedPeriodWeight q.1.1 ^ r‖ : ℂ)
  congr 1
  rw [Real.sqrt_eq_rpow, norm_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)]

theorem poweredPeriodIncidenceHalfDensity_closureOnly
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (hr : 1 ≤ r) :
    poweredPeriodIncidenceHalfDensity L r ∈
        closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      poweredPeriodIncidenceHalfDensity L r ∉
        Set.range (poweredPeriodIncidenceMultiplier L r) := by
  exact (poweredPeriodIncidenceFractionalPhaseLaw
    L hL r hr (1 / 2) (by norm_num)).2.1 (by norm_num) (by norm_num)

/-- The full physical symbol `w^r` is the canonical exact order-`r` target. -/
def poweredPeriodIncidenceExactTarget (L : Submodule ℤ ℂ) (r : ℕ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  poweredPeriodWeightVector L r

theorem poweredPeriodIncidenceExactTarget_mem_range
    (L : Submodule ℤ ℂ) (r : ℕ) :
    poweredPeriodIncidenceExactTarget L r ∈
      Set.range (poweredPeriodIncidenceMultiplier L r) := by
  refine ⟨1, ?_⟩
  apply lp.ext
  funext q
  simp [poweredPeriodIncidenceExactTarget,
    poweredPeriodIncidenceMultiplier_apply]

/-- Every positive order realizes the exact / half-density / exterior trichotomy. -/
theorem poweredPeriodIncidenceCanonicalTrichotomy
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (hr : 1 ≤ r) :
    poweredPeriodIncidenceExactTarget L r ∈
        Set.range (poweredPeriodIncidenceMultiplier L r) ∧
      (poweredPeriodIncidenceHalfDensity L r ∈
          closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        poweredPeriodIncidenceHalfDensity L r ∉
          Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      periodIncidenceExteriorTarget L ∉
        closure (Set.range (poweredPeriodIncidenceMultiplier L r)) :=
  ⟨poweredPeriodIncidenceExactTarget_mem_range L r,
    poweredPeriodIncidenceHalfDensity_closureOnly L hL r hr,
    poweredPeriodIncidenceExteriorTarget_not_mem_closure_range L hL r hr⟩

/-- The source-condition duality `α ↦ 1-α` has the unique fixed exponent `1/2`. -/
theorem periodIncidenceFractionalDuality_fixed_iff (α : ℝ) :
    1 - α = α ↔ α = 1 / 2 := by
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions
