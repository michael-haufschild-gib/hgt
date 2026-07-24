import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularSeam
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Arithmetic non-divisibility of the theta likelihood carrier

The fixed modular-seam likelihood measure has a rigid square-gap atomic sector.  After any
positive exponential tilt it has an atom at the first gap `3`, but no atom at `6 = 3 + 3`.
Consequently its atom support is not additively closed, even after multiplication by an arbitrary
nonzero normalization scalar.

This is the exact source obstruction behind the paper theorem that the normalized seam likelihood
law is not infinitely divisible: an infinitely divisible probability law on `ℝ≥0` with an atom at
zero is compound Poisson, while compound-Poisson atom support is additively closed.  The latter
probability-theory implication is not asserted in Lean here; this module formalizes its complete
theta-specific premise.

All statements are unconditional and exact.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal MeasureTheory

namespace RHTower

noncomputable section

/-! ### Exact atomic sector of the fixed higher-tail measure -/

/-- A single theta likelihood atom-ray carrier charges a singleton only at its square gap. -/
theorem thetaCuspAtomLikelihoodSpectralMeasure_singleton (n : ℕ) (y : ℝ) :
    thetaCuspAtomLikelihoodSpectralMeasure n {y} =
      if thetaCuspLikelihoodGap n = y then
        ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) else 0 := by
  by_cases h : thetaCuspLikelihoodGap n = y
  · subst y
    simp [thetaCuspAtomLikelihoodSpectralMeasure]
  · simp [thetaCuspAtomLikelihoodSpectralMeasure, h]

private theorem thetaCuspLikelihoodGap_shift_ne_zero (k : ℕ) :
    thetaCuspLikelihoodGap (k + 2) ≠ 0 := by
  have hk : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ k + 2 by omega)
  unfold thetaCuspLikelihoodGap
  nlinarith

private theorem thetaCuspLikelihoodGap_shift_eq_three_iff (k : ℕ) :
    thetaCuspLikelihoodGap (k + 2) = 3 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h3 : (3 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ k + 2 by omega)
    unfold thetaCuspLikelihoodGap at h
    nlinarith
  · rintro rfl
    norm_num [thetaCuspLikelihoodGap]

private theorem thetaCuspLikelihoodGap_shift_ne_six (k : ℕ) :
    thetaCuspLikelihoodGap (k + 2) ≠ 6 := by
  intro h
  by_cases hk : k = 0
  · subst k
    norm_num [thetaCuspLikelihoodGap] at h
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h3 : (3 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ k + 2 by omega)
    unfold thetaCuspLikelihoodGap at h
    nlinarith

/-- The higher-tail measure has no atom at the first-atom coordinate `0`. -/
theorem thetaCuspHigherLikelihoodSpectralMeasure_singleton_zero :
    thetaCuspHigherLikelihoodSpectralMeasure {0} = 0 := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    Measure.sum_apply _ (measurableSet_singleton (0 : ℝ))]
  simp_rw [thetaCuspAtomLikelihoodSpectralMeasure_singleton]
  simp [thetaCuspLikelihoodGap_shift_ne_zero]

/-- The atom at the first higher square gap `3 = 2² - 1` has its exact positive weight. -/
theorem thetaCuspHigherLikelihoodSpectralMeasure_singleton_three :
    thetaCuspHigherLikelihoodSpectralMeasure {3} =
      ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    Measure.sum_apply _ (measurableSet_singleton (3 : ℝ))]
  simp_rw [thetaCuspAtomLikelihoodSpectralMeasure_singleton]
  rw [tsum_eq_single 0]
  · norm_num [thetaCuspLikelihoodGap]
  · intro k hk
    have hgap : thetaCuspLikelihoodGap (k + 2) ≠ 3 := by
      simpa [thetaCuspLikelihoodGap_shift_eq_three_iff] using hk
    simp [hgap]

/-- There is no square gap at `6`; the Lebesgue rays contribute no singleton mass. -/
theorem thetaCuspHigherLikelihoodSpectralMeasure_singleton_six :
    thetaCuspHigherLikelihoodSpectralMeasure {6} = 0 := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    Measure.sum_apply _ (measurableSet_singleton (6 : ℝ))]
  simp_rw [thetaCuspAtomLikelihoodSpectralMeasure_singleton]
  simp [thetaCuspLikelihoodGap_shift_ne_six]

/-! ### Exponential tilt and additive-atom obstruction -/

/-- Unnormalized seam Gibbs carrier: first theta atom plus the exponentially tilted higher tail. -/
def thetaCuspLikelihoodSeamTiltedMeasure (B : ℝ) : Measure ℝ :=
  Measure.dirac 0 + thetaCuspHigherLikelihoodTiltedMeasure B

/-- Exponential tilt preserves the unit atom at the seam origin. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_singleton_zero (B : ℝ) :
    thetaCuspLikelihoodSeamTiltedMeasure B {0} = 1 := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply]
  have hdirac : Measure.dirac (0 : ℝ) {0} = 1 := by simp
  rw [hdirac, thetaCuspHigherLikelihoodTiltedMeasure,
    withDensity_apply _ (measurableSet_singleton (0 : ℝ))]
  simp [thetaCuspHigherLikelihoodSpectralMeasure_singleton_zero]

/-- Exact tilted mass of the first higher atom. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_singleton_three (B : ℝ) :
    thetaCuspLikelihoodSeamTiltedMeasure B {3} =
      ((thetaCuspHigherLikelihoodTiltDensity B 3 : NNReal) : ENNReal) *
        ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply]
  have hdirac : Measure.dirac (0 : ℝ) {3} = 0 := by simp
  rw [hdirac, zero_add, thetaCuspHigherLikelihoodTiltedMeasure,
    withDensity_apply _ (measurableSet_singleton (3 : ℝ))]
  simp [thetaCuspHigherLikelihoodSpectralMeasure_singleton_three, mul_comm]

/-- The first higher atom remains nonzero under every real exponential tilt. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero (B : ℝ) :
    thetaCuspLikelihoodSeamTiltedMeasure B {3} ≠ 0 := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure_singleton_three]
  apply mul_ne_zero
  · exact ENNReal.coe_ne_zero.mpr (ne_of_gt
      (Real.toNNReal_pos.mpr (Real.exp_pos _)))
  · rw [ENNReal.ofReal_ne_zero_iff]
    exact thetaCuspLikelihoodAtomWeight_pos (n := 2) (by norm_num)

/-- Exponential tilt cannot create an atom at the missing sum `6 = 3 + 3`. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_singleton_six (B : ℝ) :
    thetaCuspLikelihoodSeamTiltedMeasure B {6} = 0 := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply]
  have hdirac : Measure.dirac (0 : ℝ) {6} = 0 := by simp
  rw [hdirac, zero_add, thetaCuspHigherLikelihoodTiltedMeasure,
    withDensity_apply _ (measurableSet_singleton (6 : ℝ))]
  simp [thetaCuspHigherLikelihoodSpectralMeasure_singleton_six]

/-- A measure has additively closed atom support when sums of charged singletons are charged. -/
def AdditivelyClosedAtomSupport (μ : Measure ℝ) : Prop :=
  ∀ x y : ℝ, μ {x} ≠ 0 → μ {y} ≠ 0 → μ {x + y} ≠ 0

/-- **Square-gap obstruction.** The tilted seam carrier does not have additively closed atom
support: it charges `3` but not `3 + 3 = 6`. -/
theorem not_additivelyClosedAtomSupport_thetaCuspLikelihoodSeamTiltedMeasure (B : ℝ) :
    ¬ AdditivelyClosedAtomSupport (thetaCuspLikelihoodSeamTiltedMeasure B) := by
  intro hclosed
  have h6 := hclosed 3 3
    (thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero B)
    (thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero B)
  norm_num at h6
  exact h6 (thetaCuspLikelihoodSeamTiltedMeasure_singleton_six B)

/-- The obstruction survives every nonzero scalar normalization, in particular normalization to a
probability measure whenever `B > 0`. -/
theorem not_additivelyClosedAtomSupport_smul_thetaCuspLikelihoodSeamTiltedMeasure
    (B : ℝ) {c : ENNReal} (hc : c ≠ 0) :
    ¬ AdditivelyClosedAtomSupport (c • thetaCuspLikelihoodSeamTiltedMeasure B) := by
  intro hclosed
  have h3 : (c • thetaCuspLikelihoodSeamTiltedMeasure B) {3} ≠ 0 := by
    rw [Measure.smul_apply, thetaCuspLikelihoodSeamTiltedMeasure_singleton_three]
    exact mul_ne_zero hc (mul_ne_zero
      (ENNReal.coe_ne_zero.mpr (ne_of_gt
        (Real.toNNReal_pos.mpr (Real.exp_pos _))))
      (ENNReal.ofReal_ne_zero_iff.mpr
        (thetaCuspLikelihoodAtomWeight_pos (n := 2) (by norm_num))))
  have h6 := hclosed 3 3 h3 h3
  norm_num at h6
  exact h6.2 (thetaCuspLikelihoodSeamTiltedMeasure_singleton_six B)

/-- **Atoms add under convolution.**  For measures `μ, ν` on an additive monoid, the convolution
puts at least mass `μ{a}·ν{b}` on `a + b`.  Reusable primitive behind two-particle atom creation. -/
theorem measure_singleton_le_conv {M : Type*} [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableSingletonClass M] (μ ν : Measure M) [SFinite ν] (a b : M) :
    μ {a} * ν {b} ≤ (μ ∗ ν) {a + b} := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  calc μ {a} * ν {b} = (μ.prod ν) ({a} ×ˢ {b}) := (Measure.prod_prod _ _).symm
    _ ≤ (μ.prod ν) ((fun x => x.1 + x.2) ⁻¹' {a + b}) := by
        apply measure_mono
        rintro ⟨x, y⟩ hxy
        simp only [Set.mem_prod, Set.mem_singleton_iff] at hxy
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hxy.1, hxy.2]

/-! ### Positive survivor: birth of a two-particle atom -/

/-- **Two-particle square-gap birth.** Although the one-particle tilted carrier has no atom at
`6`, its self-convolution has a nonzero atom there, generated by the pair `(3, 3)`. This is the
first exact latent sector that cannot be collapsed back to the original one-particle carrier. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero (B : ℝ) :
    (thetaCuspLikelihoodSeamTiltedMeasure B ∗
      thetaCuspLikelihoodSeamTiltedMeasure B) {6} ≠ 0 := by
  let μ := thetaCuspLikelihoodSeamTiltedMeasure B
  letI : SFinite μ := by
    dsimp [μ, thetaCuspLikelihoodSeamTiltedMeasure,
      thetaCuspHigherLikelihoodTiltedMeasure,
      thetaCuspHigherLikelihoodSpectralMeasure,
      thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  have hbound : μ {3} * μ {3} ≤ (μ ∗ μ) {6} := by
    have := measure_singleton_le_conv μ μ (3 : ℝ) 3
    norm_num at this
    exact this
  intro hzero
  have hleft : μ {3} * μ {3} = 0 := nonpos_iff_eq_zero.mp (hbound.trans_eq hzero)
  exact mul_ne_zero
    (thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero B)
    (thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero B) hleft

end

end RHTower
