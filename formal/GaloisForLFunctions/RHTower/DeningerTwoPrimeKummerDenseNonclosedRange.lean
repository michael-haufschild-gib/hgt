import GaloisForLFunctions.RHTower.DeningerMultiplier
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods
import GaloisForLFunctions.RHTower.DeningerBoundaryComplete
import GaloisForLFunctions.RHTower.DeningerBoundaryHodgeOperator

/-!
# Two-prime Kummer dense/nonclosed range

The bounded transform of the signed Kummer generator on the two-prime frequency group is injective
with dense, nonclosed range on `ℓ²`.  Every finite nonzero truncation remains bijective.  Therefore
its algebraic cokernel is closure-only while its reduced Hilbert cokernel vanishes.

These are the unconditional statements behind
`DAC_TWO_PRIME_KUMMER_DENSE_NONCLOSED_RANGE`.
-/

open Filter
open scoped ENNReal Topology

namespace RHTower

noncomputable section

variable {ι : Type*}

/-- A diagonal multiplier with no zero coordinate is injective. -/
theorem deningerMultiplier_injective {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1)
    (hgne : ∀ i, g i ≠ 0) :
    Function.Injective (deningerMultiplier hg) := by
  intro x y hxy
  apply lp.ext
  funext i
  have hi := congrArg (fun z : lp (fun _ : ι => ℂ) 2 => z i) hxy
  simp only [deningerMultiplier_apply] at hi
  exact mul_left_cancel₀ (hgne i) hi

/-- A diagonal multiplier sends a coordinate vector to its scalar-weighted copy. -/
theorem deningerMultiplier_single [DecidableEq ι]
    {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (i : ι) (c : ℂ) :
    deningerMultiplier hg (lp.single 2 i c) = lp.single 2 i (g i * c) := by
  apply lp.ext
  funext j
  rw [deningerMultiplier_apply]
  by_cases hji : j = i
  · subst j
    simp [lp.single_apply]
  · simp [lp.single_apply, hji]

/-- A nonvanishing diagonal multiplier has dense range on `ℓ²`. -/
theorem deningerMultiplier_denseRange_of_ne_zero
    {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (hgne : ∀ i, g i ≠ 0) :
    DenseRange (deningerMultiplier hg) := by
  classical
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hsum : HasSum (fun i : ι => lp.single 2 i (x i)) x :=
    lp.hasSum_single ENNReal.ofNat_ne_top x
  apply isClosed_closure.mem_of_tendsto hsum
  filter_upwards [] with S
  apply subset_closure
  let y : lp (fun _ : ι => ℂ) 2 :=
    ∑ i ∈ S, lp.single 2 i ((g i)⁻¹ * x i)
  refine ⟨y, ?_⟩
  rw [show y = ∑ i ∈ S, lp.single 2 i ((g i)⁻¹ * x i) by rfl, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [deningerMultiplier_single]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (hgne i), one_mul]

/-- Unit coordinate vectors along vanishing nonzero weights force nonclosed multiplier range. -/
theorem deningerMultiplier_not_isClosed_range_of_weights_tendsto_zero
    {g : ι → ℂ} (hg : ∀ i, ‖g i‖ ≤ 1) (hgne : ∀ i, g i ≠ 0)
    (q : ℕ → ι) (hzero : Tendsto (fun n => g (q n)) atTop (𝓝 0)) :
    ¬ IsClosed (Set.range (deningerMultiplier hg)) := by
  classical
  let u : ℕ → lp (fun _ : ι => ℂ) 2 := fun n => lp.single 2 (q n) 1
  apply GaloisForLFunctions.not_isClosed_range_of_injective_of_unit_vectors_tendsto_zero
    (deningerMultiplier hg) (deningerMultiplier_injective hg hgne) u
  · intro n
    rw [show u n = lp.single 2 (q n) 1 by rfl,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : Tendsto (fun n => ‖g (q n)‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hzero
    convert hnorm using 1
    funext n
    rw [show u n = lp.single 2 (q n) 1 by rfl,
      deningerMultiplier_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
      norm_mul, norm_one, mul_one]

/-- The two-prime real Kummer period pair. -/
def deningerPrimeLogPeriodPair : Fin 2 → ℂ :=
  ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)]

/-- Irrationality of `log 3 / log 2` makes the two-prime pair rationally independent. -/
theorem deningerPrimeLogPeriodPair_linearIndependent_rat :
    LinearIndependent ℚ deningerPrimeLogPeriodPair := by
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  change LinearIndependent ℚ
    ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)]
  rw [LinearIndependent.pair_iff' hlog2]
  intro a ha
  have hre : (a : ℝ) * Real.log 2 = Real.log 3 := by
    exact_mod_cast ha
  have hlog2r : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hratio : Real.log 3 / Real.log 2 = (a : ℝ) := by
    rw [div_eq_iff hlog2r]
    exact hre.symm
  exact (GaloisForLFunctions.RHTower.irrational_log_ratio
    (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)) ⟨a, hratio.symm⟩

/-- The same pair is real-linearly dependent because both periods lie on the real line. -/
theorem deningerPrimeLogPeriodPair_not_linearIndependent_real :
    ¬ LinearIndependent ℝ deningerPrimeLogPeriodPair := by
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  change ¬ LinearIndependent ℝ
    ![((Real.log 2 : ℝ) : ℂ), ((Real.log 3 : ℝ) : ℂ)]
  rw [LinearIndependent.pair_iff' hlog2]
  push Not
  refine ⟨Real.log 3 / Real.log 2, ?_⟩
  have hlog2r : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hreal : (Real.log 3 / Real.log 2) * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ hlog2r
  rw [Complex.real_smul]
  exact_mod_cast hreal

/-- Integer span of the signed two-prime Kummer frequencies. -/
def deningerPrimeLogPeriodGroup : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range deningerPrimeLogPeriodPair)

/-- The two-prime signed Kummer frequency group is nondiscrete. -/
theorem deningerPrimeLogPeriodGroup_not_discrete :
    ¬ DiscreteTopology deningerPrimeLogPeriodGroup :=
  GaloisForLFunctions.not_discrete_intSpan_fin_two_of_not_linearIndependent_real
    deningerPrimeLogPeriodPair
    deningerPrimeLogPeriodPair_linearIndependent_rat
    deningerPrimeLogPeriodPair_not_linearIndependent_real

/-- Nonzero signed two-prime Kummer modes. -/
abbrev DeningerPrimeLogMode :=
  GaloisForLFunctions.NonzeroPeriod deningerPrimeLogPeriodGroup

/-- Bounded transform `μ / (1 + |μ|)` of the signed two-prime Kummer generator on `ℓ²`. -/
noncomputable def deningerPrimeLogBoundedTransform :
    lp (fun _ : DeningerPrimeLogMode => ℂ) 2 →L[ℂ]
      lp (fun _ : DeningerPrimeLogMode => ℂ) 2 :=
  deningerMultiplier (fun q =>
    GaloisForLFunctions.norm_regularizedPeriodWeight_le_one q.1.1)

/-- The two-prime Kummer bounded transform has nonclosed range. -/
theorem deningerPrimeLogBoundedTransform_not_isClosed_range :
    ¬ IsClosed (Set.range deningerPrimeLogBoundedTransform) := by
  classical
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    GaloisForLFunctions.exists_small_nonzero_of_not_discrete_intSubmodule
      deningerPrimeLogPeriodGroup deningerPrimeLogPeriodGroup_not_discrete
  let q : ℕ → DeningerPrimeLogMode := fun n => ⟨⟨p n, hpL n⟩, hpne n⟩
  apply deningerMultiplier_not_isClosed_range_of_weights_tendsto_zero
    (g := fun q : DeningerPrimeLogMode =>
      GaloisForLFunctions.regularizedPeriodWeight q.1.1)
    (fun q => GaloisForLFunctions.norm_regularizedPeriodWeight_le_one q.1.1)
    (fun q => GaloisForLFunctions.regularizedPeriodWeight_ne_zero q.2)
    q
  exact GaloisForLFunctions.tendsto_regularizedPeriodWeight_zero hp0

/-- Nonvanishing of every frequency makes the same nonclosed range dense in `ℓ²`. -/
theorem deningerPrimeLogBoundedTransform_denseRange :
    DenseRange deningerPrimeLogBoundedTransform := by
  apply deningerMultiplier_denseRange_of_ne_zero
  exact fun q : DeningerPrimeLogMode =>
    GaloisForLFunctions.regularizedPeriodWeight_ne_zero q.2

/-- A concrete closure-only mode witnesses the unreduced/reduced Kummer cohomology split. -/
theorem exists_primeLog_closureOnly_mode :
    ∃ b,
      b ∈ closure (Set.range deningerPrimeLogBoundedTransform) ∧
      b ∉ Set.range deningerPrimeLogBoundedTransform :=
  GaloisForLFunctions.exists_mem_closure_not_mem_of_not_isClosed
    deningerPrimeLogBoundedTransform_not_isClosed_range

/-! ## Relative-domain repair on the same arithmetic frequency group -/

/-- Every two-prime Kummer period lies on the real axis. -/
theorem deningerPrimeLogPeriodGroup_im_eq_zero
    (z : deningerPrimeLogPeriodGroup) : (z : ℂ).im = 0 := by
  apply Submodule.span_induction (p := fun w : ℂ => w.im = 0) z.2
  · rintro w ⟨i, rfl⟩
    fin_cases i <;> simp [deningerPrimeLogPeriodPair]
  · simp
  · intro x y hx hy
    simp [hx, hy]
  · intro n x hx
    simp [hx]

/-- Signed real frequency of a nonzero two-prime Kummer mode. -/
def deningerPrimeLogFrequency (q : DeningerPrimeLogMode) : ℝ :=
  (q.1.1 : ℂ).re

theorem deningerPrimeLogFrequency_coe (q : DeningerPrimeLogMode) :
    ((deningerPrimeLogFrequency q : ℝ) : ℂ) = q.1.1 := by
  apply Complex.ext
  · rfl
  · simpa [deningerPrimeLogFrequency] using
      (deningerPrimeLogPeriodGroup_im_eq_zero q.1)

theorem deningerPrimeLogFrequency_ne_zero (q : DeningerPrimeLogMode) :
    deningerPrimeLogFrequency q ≠ 0 := by
  intro h
  apply q.2
  apply Subtype.ext
  have hc := deningerPrimeLogFrequency_coe q
  rw [h, Complex.ofReal_zero] at hc
  exact hc.symm

/-- The `log 2` mode in the signed two-prime frequency group. -/
def deningerLogTwoMode : DeningerPrimeLogMode := by
  let z : deningerPrimeLogPeriodGroup :=
    ⟨((Real.log 2 : ℝ) : ℂ), Submodule.subset_span ⟨0, by
      simp [deningerPrimeLogPeriodPair]⟩⟩
  exact ⟨z, by
    intro h
    have hc : ((Real.log 2 : ℝ) : ℂ) = 0 := congrArg Subtype.val h
    exact (show ((Real.log 2 : ℝ) : ℂ) ≠ 0 by
      exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne') hc⟩

/-- Unit coefficient at the `log 2` relative boundary mode. -/
def deningerPrimeLogBoundaryUnit : lp (fun _ : DeningerPrimeLogMode => ℂ) 2 :=
  lp.single 2 deningerLogTwoMode 1

theorem norm_deningerPrimeLogBoundaryUnit :
    ‖deningerPrimeLogBoundaryUnit‖ = 1 := by
  rw [deningerPrimeLogBoundaryUnit, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

/-- Concrete nonzero finite-energy boundary datum. -/
def deningerPrimeLogRelativeBoundaryUnit :
    deningerBoundarySubmodule deningerPrimeLogFrequency :=
  deningerBoundaryEquiv deningerPrimeLogFrequency
    deningerPrimeLogFrequency_ne_zero deningerPrimeLogBoundaryUnit

theorem deningerPrimeLogRelativeBoundaryUnit_normSq :
    deningerBoundaryNormSq deningerPrimeLogFrequency
      (deningerPrimeLogRelativeBoundaryUnit : DeningerPrimeLogMode → ℂ) = 1 := by
  rw [deningerPrimeLogRelativeBoundaryUnit,
    deningerBoundaryEquiv_normSq, norm_deningerPrimeLogBoundaryUnit]
  norm_num

theorem deningerPrimeLogRelativeBoundaryUnit_ne_zero :
    deningerPrimeLogRelativeBoundaryUnit ≠ 0 := by
  intro h
  have hnorm := deningerPrimeLogRelativeBoundaryUnit_normSq
  rw [h] at hnorm
  simp [deningerBoundaryNormSq] at hnorm

/-- The actual two-prime relative boundary norm is complete. -/
theorem deningerPrimeLogRelativeBoundary_complete
    (φ : ℕ → deningerBoundarySubmodule deningerPrimeLogFrequency)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      deningerBoundaryNorm deningerPrimeLogFrequency
        ((φ m : DeningerPrimeLogMode → ℂ) - (φ n : DeningerPrimeLogMode → ℂ)) < ε) :
    ∃ ω : deningerBoundarySubmodule deningerPrimeLogFrequency,
      Filter.Tendsto (fun n => deningerBoundaryNorm deningerPrimeLogFrequency
        ((φ n : DeningerPrimeLogMode → ℂ) - (ω : DeningerPrimeLogMode → ℂ)))
        Filter.atTop (nhds 0) :=
  deningerBoundary_complete deningerPrimeLogFrequency
    deningerPrimeLogFrequency_ne_zero φ hcauchy

/-- On the same arithmetic index, raw reduced cohomology vanishes while the relative boundary
cohomology is nonzero and complete. -/
theorem deningerTwoPrimeKummer_relative_raw_dichotomy :
    DenseRange deningerPrimeLogBoundedTransform ∧
    ¬ IsClosed (Set.range deningerPrimeLogBoundedTransform) ∧
    ∃ φ : deningerBoundarySubmodule deningerPrimeLogFrequency, φ ≠ 0 := by
  exact ⟨deningerPrimeLogBoundedTransform_denseRange,
    deningerPrimeLogBoundedTransform_not_isClosed_range,
    deningerPrimeLogRelativeBoundaryUnit, deningerPrimeLogRelativeBoundaryUnit_ne_zero⟩

/-- The relative boundary carries an odd Hodge operator on its `ℓ²` coefficient model. -/
theorem deningerPrimeLogRelativeHodge_sq
    (x : lp (fun _ : DeningerPrimeLogMode => ℂ) 2) :
    deningerBoundaryHodgeOperator deningerPrimeLogFrequency
        (deningerBoundaryHodgeOperator deningerPrimeLogFrequency x) = -x :=
  deningerBoundaryHodgeOperator_sq deningerPrimeLogFrequency x

/-- The actual two-prime relative Hodge operator is an isometry. -/
theorem deningerPrimeLogRelativeHodge_isometry
    (x : lp (fun _ : DeningerPrimeLogMode => ℂ) 2) :
    ‖deningerBoundaryHodgeOperator deningerPrimeLogFrequency x‖ = ‖x‖ :=
  deningerBoundaryHodgeOperator_isometry deningerPrimeLogFrequency x

end


end RHTower
