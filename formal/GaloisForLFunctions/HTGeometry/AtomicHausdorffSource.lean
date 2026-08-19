import GaloisForLFunctions.HTGeometry.HausdorffMomentTheorem
import GaloisForLFunctions.HTGeometry.CompactMomentDeterminacy

/-!
# Atomic Hausdorff sources and moment inversion

A summable nonnegative family carried by the unit interval defines a finite atomic source on
`[0,1]` whose moments are the corresponding weighted power sums.  Comparing such a source with a
power-density tilt of an arbitrary finite source turns an identity between high moments into an
identity between atoms, and hence into summability at the bottom of the moment range.

This is the measure-theoretic consumer of the Hausdorff moment theorem: knowing that a completely
monotone sequence agrees with `∑ⱼ Bⱼ xⱼⁿ` only for large `n` already forces `∑ⱼ Bⱼ` to converge,
because the Hausdorff source of the *whole* sequence is finite.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-! ## The atomic source -/

/-- The atomic source of a nonnegative weighted family in the unit interval. -/
def atomicHausdorffSource (b : ι → ℝ) (x : ι → HausdorffSourceSpace) :
    Measure HausdorffSourceSpace :=
  Measure.sum (fun j => ENNReal.ofReal (b j) • Measure.dirac (x j))

theorem atomicHausdorffSource_apply (b : ι → ℝ) (x : ι → HausdorffSourceSpace)
    {s : Set HausdorffSourceSpace} (hs : MeasurableSet s) :
    atomicHausdorffSource b x s =
      ∑' j, ENNReal.ofReal (b j) * Set.indicator s (fun _ => (1 : ℝ≥0∞)) (x j) := by
  rw [atomicHausdorffSource, Measure.sum_apply _ hs]
  refine tsum_congr (fun j => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  congr 1

theorem atomicHausdorffSource_univ (b : ι → ℝ) (x : ι → HausdorffSourceSpace) :
    atomicHausdorffSource b x Set.univ = ∑' j, ENNReal.ofReal (b j) := by
  rw [atomicHausdorffSource_apply b x MeasurableSet.univ]
  exact tsum_congr (fun j => by simp)

theorem isFiniteMeasure_atomicHausdorffSource {b : ι → ℝ} {x : ι → HausdorffSourceSpace}
    (hb : ∀ j, 0 ≤ b j) (hsum : Summable b) :
    IsFiniteMeasure (atomicHausdorffSource b x) := by
  constructor
  rw [atomicHausdorffSource_univ, ← ENNReal.ofReal_tsum_of_nonneg hb hsum]
  exact ENNReal.ofReal_lt_top

/-- **The atoms of an atomic source.**  With injective nodes the mass of a node is its weight. -/
theorem atomicHausdorffSource_singleton {b : ι → ℝ} {x : ι → HausdorffSourceSpace}
    (hinj : Function.Injective x) (j : ι) :
    atomicHausdorffSource b x {x j} = ENNReal.ofReal (b j) := by
  rw [atomicHausdorffSource_apply b x (measurableSet_singleton (x j))]
  rw [tsum_eq_single j]
  · simp
  · intro k hk
    have : x k ∉ ({x j} : Set HausdorffSourceSpace) := by
      simp only [Set.mem_singleton_iff]
      exact fun h => hk (hinj h)
    rw [Set.indicator_of_notMem this, mul_zero]

/-! ## Integration against an atomic source -/

theorem integral_atomicHausdorffSource [Countable ι] {b : ι → ℝ} {x : ι → HausdorffSourceSpace}
    (hb : ∀ j, 0 ≤ b j) (hsum : Summable b) {g : HausdorffSourceSpace → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    ∫ y, g y ∂(atomicHausdorffSource b x) = ∑' j, b j * g (x j) := by
  have hterm : ∀ j : ι, ∫ y, g y ∂(ENNReal.ofReal (b j) • Measure.dirac (x j)) = b j * g (x j) := by
    intro j
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hb j), smul_eq_mul]
  have hnormterm : ∀ j : ι,
      ∫ y, ‖g y‖ ∂(ENNReal.ofReal (b j) • Measure.dirac (x j)) = b j * ‖g (x j)‖ := by
    intro j
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hb j), smul_eq_mul]
  have hint : Integrable g (atomicHausdorffSource b x) := by
    refine integrable_sum_measure (fun j => ?_) ?_
    · exact (integrable_of_continuous (Measure.dirac (x j)) hg).smul_measure ENNReal.ofReal_ne_top
    · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hsum.mul_left C)
      · rw [hnormterm j]
        exact mul_nonneg (hb j) (norm_nonneg _)
      · rw [hnormterm j, mul_comm C (b j)]
        exact mul_le_mul_of_nonneg_left (hC (x j)) (hb j)
  rw [atomicHausdorffSource, integral_sum_measure hint]
  exact tsum_congr hterm

/-- The moments of an atomic source are the weighted power sums of its nodes. -/
theorem hausdorffMoment_atomicHausdorffSource [Countable ι] {b : ι → ℝ} {x : ι → HausdorffSourceSpace}
    (hb : ∀ j, 0 ≤ b j) (hsum : Summable b) (m : ℕ) :
    hausdorffMoment (atomicHausdorffSource b x) m = ∑' j, b j * (x j : ℝ) ^ m := by
  refine integral_atomicHausdorffSource hb hsum (by fun_prop) (C := 1) (fun y => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg y.2.1]
  exact pow_le_one₀ y.2.1 y.2.2

/-! ## The power-density tilt -/

/-- The density `y ↦ yᴺ` on the unit interval. -/
def hausdorffPowerDensity (N : ℕ) : HausdorffSourceSpace → ℝ≥0 :=
  fun y => Real.toNNReal ((y : ℝ) ^ N)

theorem measurable_hausdorffPowerDensity (N : ℕ) : Measurable (hausdorffPowerDensity N) := by
  unfold hausdorffPowerDensity; fun_prop

theorem coe_hausdorffPowerDensity (N : ℕ) (y : HausdorffSourceSpace) :
    ((hausdorffPowerDensity N y : ℝ≥0) : ℝ) = (y : ℝ) ^ N :=
  Real.coe_toNNReal _ (pow_nonneg y.2.1 N)

theorem hausdorffPowerDensity_le_one (N : ℕ) (y : HausdorffSourceSpace) :
    ((hausdorffPowerDensity N y : ℝ≥0) : ℝ≥0∞) ≤ 1 := by
  rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_hausdorffPowerDensity]
  exact_mod_cast pow_le_one₀ y.2.1 y.2.2

/-- The tilt of a finite source by `yᴺ`. -/
def hausdorffPowerTilt (μ : Measure HausdorffSourceSpace) (N : ℕ) :
    Measure HausdorffSourceSpace :=
  μ.withDensity (fun y => ((hausdorffPowerDensity N y : ℝ≥0) : ℝ≥0∞))

theorem isFiniteMeasure_hausdorffPowerTilt (μ : Measure HausdorffSourceSpace) [IsFiniteMeasure μ]
    (N : ℕ) : IsFiniteMeasure (hausdorffPowerTilt μ N) := by
  constructor
  rw [hausdorffPowerTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine lt_of_le_of_lt (le_trans (lintegral_mono (hausdorffPowerDensity_le_one N)) ?_)
    (measure_lt_top μ Set.univ)
  rw [lintegral_const, one_mul]

/-- **Tilting shifts the moment index.** -/
theorem hausdorffMoment_hausdorffPowerTilt (μ : Measure HausdorffSourceSpace) (N m : ℕ) :
    hausdorffMoment (hausdorffPowerTilt μ N) m = hausdorffMoment μ (N + m) := by
  rw [hausdorffMoment, hausdorffMoment, hausdorffPowerTilt,
    integral_withDensity_eq_integral_smul (measurable_hausdorffPowerDensity N)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (hausdorffPowerDensity N y) • ((y : ℝ) ^ m) = (y : ℝ) ^ (N + m)
  rw [NNReal.smul_def, smul_eq_mul, coe_hausdorffPowerDensity, pow_add]

/-- **The atoms of a tilt.** -/
theorem hausdorffPowerTilt_singleton (μ : Measure HausdorffSourceSpace) (N : ℕ)
    (y₀ : HausdorffSourceSpace) :
    hausdorffPowerTilt μ N {y₀} = ENNReal.ofReal ((y₀ : ℝ) ^ N) * μ {y₀} := by
  rw [hausdorffPowerTilt, withDensity_apply _ (measurableSet_singleton y₀),
    ← lintegral_indicator (measurableSet_singleton y₀)]
  have hind : (Set.indicator {y₀} (fun y => ((hausdorffPowerDensity N y : ℝ≥0) : ℝ≥0∞))) =
      Set.indicator {y₀} (fun _ => ((hausdorffPowerDensity N y₀ : ℝ≥0) : ℝ≥0∞)) := by
    funext y
    rcases eq_or_ne y y₀ with rfl | h
    · rfl
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem (by simpa using h)]
  rw [hind, lintegral_indicator_const (measurableSet_singleton y₀)]
  congr 1

/-! ## Moment inversion -/

/-- **The atoms of a Hausdorff source that agrees with a power sum in high degree.**  If a finite
source on `[0,1]` reproduces `∑ⱼ Bⱼ xⱼⁿ` for all `n ≥ N` with distinct positive nodes `xⱼ`, then
its mass at `xⱼ` is exactly `Bⱼ`.

Tilting the source by `yᴺ` shifts its moment index by `N`, so the tilt has exactly the moments of
the atomic source of weights `Bⱼ xⱼᴺ`; uniqueness of the Hausdorff source identifies the two, and
the node masses are read off by cancelling the strictly positive factor `xⱼᴺ`. -/
theorem hausdorffSource_singleton_of_moments [Countable ι] {B : ι → ℝ}
    {x : ι → HausdorffSourceSpace} (hB : ∀ j, 0 ≤ B j) (hx0 : ∀ j, 0 < (x j : ℝ))
    (hinj : Function.Injective x) {μ : Measure HausdorffSourceSpace} [IsFiniteMeasure μ] {N : ℕ}
    (hsumN : Summable (fun j => B j * (x j : ℝ) ^ N))
    (hmom : ∀ m : ℕ, hausdorffMoment μ (N + m) = ∑' j, B j * (x j : ℝ) ^ (N + m)) (j : ι) :
    μ {x j} = ENNReal.ofReal (B j) := by
  classical
  set b : ι → ℝ := fun k => B k * (x k : ℝ) ^ N with hb_def
  have hb : ∀ k, 0 ≤ b k := fun k => mul_nonneg (hB k) (pow_nonneg (hx0 k).le N)
  haveI hfinσ : IsFiniteMeasure (atomicHausdorffSource b x) :=
    isFiniteMeasure_atomicHausdorffSource hb hsumN
  haveI hfinτ : IsFiniteMeasure (hausdorffPowerTilt μ N) := isFiniteMeasure_hausdorffPowerTilt μ N
  have hmoments : ∀ m : ℕ,
      hausdorffMoment (atomicHausdorffSource b x) m = hausdorffMoment (hausdorffPowerTilt μ N) m := by
    intro m
    rw [hausdorffMoment_atomicHausdorffSource hb hsumN, hausdorffMoment_hausdorffPowerTilt, hmom]
    refine tsum_congr (fun k => ?_)
    rw [hb_def, pow_add]
    ring
  have heq : atomicHausdorffSource b x = hausdorffPowerTilt μ N :=
    hausdorffSource_eq_of_moments_eq hmoments
  have hsingle : ENNReal.ofReal (b j) = ENNReal.ofReal ((x j : ℝ) ^ N) * μ {x j} := by
    rw [← atomicHausdorffSource_singleton (b := b) hinj j, heq, hausdorffPowerTilt_singleton]
  have hpow : ENNReal.ofReal ((x j : ℝ) ^ N) ≠ 0 := by
    simpa using pow_pos (hx0 j) N
  have hcancel : ENNReal.ofReal ((x j : ℝ) ^ N) * ENNReal.ofReal (B j) =
      ENNReal.ofReal ((x j : ℝ) ^ N) * μ {x j} := by
    rw [← hsingle, hb_def, ENNReal.ofReal_mul (hB j), mul_comm]
  exact ((ENNReal.mul_right_inj hpow ENNReal.ofReal_ne_top).mp hcancel).symm

/-- **Summability at the bottom of the moment range.**  A finite Hausdorff source whose moments
agree with `∑ⱼ Bⱼ xⱼⁿ` from some index on forces `∑ⱼ Bⱼ` itself to converge. -/
theorem summable_of_hausdorffMoment_eq_atomic [Countable ι] {B : ι → ℝ}
    {x : ι → HausdorffSourceSpace} (hB : ∀ j, 0 ≤ B j) (hx0 : ∀ j, 0 < (x j : ℝ))
    (hinj : Function.Injective x) {μ : Measure HausdorffSourceSpace} [IsFiniteMeasure μ] {N : ℕ}
    (hsumN : Summable (fun j => B j * (x j : ℝ) ^ N))
    (hmom : ∀ m : ℕ, hausdorffMoment μ (N + m) = ∑' j, B j * (x j : ℝ) ^ (N + m)) :
    Summable B := by
  classical
  have hatom : ∀ j, μ {x j} = ENNReal.ofReal (B j) :=
    hausdorffSource_singleton_of_moments hB hx0 hinj hsumN hmom
  refine summable_of_sum_le (c := (μ Set.univ).toReal) (fun j => hB j) (fun s => ?_)
  have hdisj : (↑s : Set ι).PairwiseDisjoint (fun k => ({x k} : Set HausdorffSourceSpace)) := by
    intro i _ k _ hik
    exact Set.disjoint_singleton.mpr (fun h => hik (hinj h))
  have hunion : μ (⋃ k ∈ s, ({x k} : Set HausdorffSourceSpace)) = ∑ k ∈ s, μ {x k} :=
    measure_biUnion_finset hdisj (fun k _ => measurableSet_singleton (x k))
  have hle : ENNReal.ofReal (∑ k ∈ s, B k) ≤ μ Set.univ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hB k)]
    calc ∑ k ∈ s, ENNReal.ofReal (B k) = ∑ k ∈ s, μ {x k} := by
          exact Finset.sum_congr rfl (fun k _ => (hatom k).symm)
      _ = μ (⋃ k ∈ s, ({x k} : Set HausdorffSourceSpace)) := hunion.symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ Set.univ)).mp hle


end

end GaloisForLFunctions.HTGeometry
