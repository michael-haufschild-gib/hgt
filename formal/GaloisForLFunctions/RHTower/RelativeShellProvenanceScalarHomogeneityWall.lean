import GaloisForLFunctions.RHTower.RelativeShellProvenanceCoordinateTopology

/-!
# Scalar-homogeneity wall for exact support coordinates

The per-label `0/1` provenance gauges separate the transverse additive
quotient, but a nuclear Deninger/Meyer coefficient space must be a complex
topological vector space.  This file proves the exact incompatibility.

Canonical support is unchanged by every nonzero complex scalar.  Hence each
label gauge is scale-invariant rather than absolutely homogeneous.  It cannot
be a complex seminorm, cannot be the norm of a complex-linear functional, and
cannot even be continuous for any topology on the shell field making complex
scalar multiplication continuous.

The last claim uses the path `a ↦ a • H_m`: the label gauge is zero at `a = 0`
and one at every `a ≠ 0`.  Along `a_n = 2⁻ⁿ`, continuity would force the same
sequence to converge both to zero and to one.

Thus coordinate provenance is an exact algebraic/discrete support invariant,
not a defining locally convex seminorm family.  A viable relevant complex must
transport support strata algebraically while building its nuclear topology
from genuinely homogeneous coefficient/Hodge seminorms.
-/

open Set Filter
open scoped Classical Topology
open scoped Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex scalar multiplication cannot introduce a private shell label. -/
theorem relativeShellObservableSupport_smul_subset
    (a : ℂ) (x : RelativeShellFullObservable) :
    relativeShellObservableSupport (a • x) ⊆
      relativeShellObservableSupport x := by
  rw [←
    mem_relativeShellSubsetDifferentialField_iff_support_subset]
  change
    (a • (x : upperEndMeroField)) ∈
      relativeShellSubsetDifferentialField
        (relativeShellObservableSupport x)
  have hx :=
    relativeShellObservableSupport_mem x
  have hsmul :=
    IntermediateField.smul_mem
      (relativeShellSubsetDifferentialField
        (relativeShellObservableSupport x))
      hx
      (x :=
        algebraMap ℂ upperEndRationalCoordinateField a)
  rw [IsScalarTower.algebraMap_smul] at hsmul
  exact hsmul

/-- Every nonzero complex scalar preserves canonical support exactly. -/
theorem relativeShellObservableSupport_smul
    {a : ℂ} (ha : a ≠ 0)
    (x : RelativeShellFullObservable) :
    relativeShellObservableSupport (a • x) =
      relativeShellObservableSupport x := by
  apply Set.Subset.antisymm
  · exact relativeShellObservableSupport_smul_subset a x
  · have hback :=
      relativeShellObservableSupport_smul_subset
        a⁻¹ (a • x)
    simpa [smul_smul, ha] using hback

/-- Exact label coordinates are invariant under nonzero complex scaling. -/
theorem relativeShellLabelCoordinateSize_smul
    (m : RelativeShellLabel)
    {a : ℂ} (ha : a ≠ 0)
    (x : RelativeShellFullObservable) :
    relativeShellLabelCoordinateSize m (a • x) =
      relativeShellLabelCoordinateSize m x := by
  simp [relativeShellLabelCoordinateSize,
    relativeShellObservableSupport_smul ha x]

/-- The full finite provenance vector is invariant under nonzero scaling. -/
theorem relativeShellProvenanceVector_smul
    {a : ℂ} (ha : a ≠ 0)
    (x : RelativeShellFullObservable) :
    relativeShellProvenanceVector (a • x) =
      relativeShellProvenanceVector x := by
  ext m
  simp [relativeShellLabelCoordinateSize_smul m ha x]

/--
No complex seminorm can equal one exact `0/1` label gauge: absolute
homogeneity at scalar two contradicts scale invariance on `H_m`.
-/
theorem no_complexSeminorm_eq_relativeShellLabelCoordinateSize
    (m : RelativeShellLabel) :
    ¬ ∃ p : Seminorm ℂ RelativeShellFullObservable,
      ∀ x,
        p x = relativeShellLabelCoordinateSize m x := by
  rintro ⟨p, hp⟩
  let x := relativeShellMultiplierObservable m
  have hx :
      relativeShellLabelCoordinateSize m x = 1 := by
    simp [x, relativeShellLabelCoordinateSize_multiplier]
  have hscaled := p.smul' (2 : ℂ) x
  change
    p ((2 : ℂ) • x) = ‖(2 : ℂ)‖ * p x
      at hscaled
  rw [hp, hp,
    relativeShellLabelCoordinateSize_smul
      m (by norm_num : (2 : ℂ) ≠ 0),
    hx] at hscaled
  norm_num at hscaled

/--
No complex-linear scalar coefficient has magnitude equal to an exact label
gauge on every observable.
-/
theorem no_complexLinearFunctional_norm_eq_relativeShellLabelCoordinateSize
    (m : RelativeShellLabel) :
    ¬ ∃ L :
        RelativeShellFullObservable →ₗ[ℂ] ℂ,
      ∀ x,
        ‖L x‖ =
          relativeShellLabelCoordinateSize m x := by
  rintro ⟨L, hL⟩
  let x := relativeShellMultiplierObservable m
  have hx :
      relativeShellLabelCoordinateSize m x = 1 := by
    simp [x, relativeShellLabelCoordinateSize_multiplier]
  have hscaled := hL ((2 : ℂ) • x)
  rw [LinearMap.map_smul, norm_smul, hL,
    relativeShellLabelCoordinateSize_smul
      m (by norm_num : (2 : ℂ) ≠ 0),
    hx] at hscaled
  norm_num at hscaled

/--
For any topology making complex scalar multiplication continuous, an exact
label coordinate is discontinuous.  This rules out using the `0/1` provenance
family itself as defining seminorms of a complex topological vector space.
-/
theorem not_continuous_relativeShellLabelCoordinateSize
    [TopologicalSpace RelativeShellFullObservable]
    [ContinuousSMul ℂ RelativeShellFullObservable]
    (m : RelativeShellLabel) :
    ¬ Continuous
      (relativeShellLabelCoordinateSize m) := by
  intro hcontinuous
  let x := relativeShellMultiplierObservable m
  have hx :
      relativeShellLabelCoordinateSize m x = 1 := by
    simp [x, relativeShellLabelCoordinateSize_multiplier]
  have hcurve :
      Continuous
        (fun a : ℂ =>
          relativeShellLabelCoordinateSize m (a • x)) :=
    hcontinuous.comp
      (continuous_id.smul continuous_const)
  have ht :
      Tendsto (fun n : ℕ => ((2 : ℂ)⁻¹) ^ n)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num)
  have hzero :
      Tendsto
        (fun n : ℕ =>
          relativeShellLabelCoordinateSize m
            ((((2 : ℂ)⁻¹) ^ n) • x))
        atTop (𝓝 0) := by
    change
      Tendsto
        ((fun a : ℂ =>
          relativeShellLabelCoordinateSize m (a • x)) ∘
            (fun n : ℕ => ((2 : ℂ)⁻¹) ^ n))
        atTop (𝓝 0)
    simpa only [zero_smul,
      relativeShellLabelCoordinateSize_zero] using
      hcurve.continuousAt.tendsto.comp ht
  have hone :
      Tendsto
        (fun n : ℕ =>
          relativeShellLabelCoordinateSize m
            ((((2 : ℂ)⁻¹) ^ n) • x))
        atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    have hn :
        ((2 : ℂ)⁻¹) ^ n ≠ 0 := by
      exact pow_ne_zero _ (inv_ne_zero (by norm_num))
    rw [relativeShellLabelCoordinateSize_smul m hn, hx]
  have hfalse : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hzero hone
  norm_num at hfalse

end

end RHTower
