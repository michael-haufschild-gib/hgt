import GaloisForLFunctions.RHTower.Suzuki.SuzukiV2CharacteristicTarget

/-!
# Corrected meromorphic and spherical convergence for Suzuki v2

Suzuki v2's displayed target has genuine poles, so compact-open convergence on all of `ℂ` is
impossible.  This file records the two coherent replacements.

* `SuzukiV2PoleFreeConvergenceOn Ω W` is ordinary locally uniform convergence on a preconnected
  finite chart where the target is analytic and which retains the whole centered-Xi divisor.
* `SuzukiV2SphericalAtlasCharacteristicLimitWall` adds an infinity chart.  On that chart the
  reciprocals converge locally uniformly and the approximants are eventually zero-free on every
  compactum.  The zero-free clause is indispensable because inversion is totalized in Lean:
  without it, reciprocal convergence would not distinguish finite zeros from escape to infinity.

The spherical-atlas wall implies the pole-free wall and therefore RH.  These are closed conditional
theorems about the corrected convergence notions; they do not assert existence of the actual
Suzuki cofinal producer.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- Eventual zero-freeness locally uniformly on compact subsets of an open chart.  This is the
chart-admissibility condition needed before applying the reciprocal coordinate. -/
def EventuallyZeroFreeOnCompacta (W : ℕ → ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∀ᶠ n in atTop, ∀ z ∈ K, W n z ≠ 0

/-- Ordinary compact-open convergence on a pole-free finite chart retaining every centered-Xi
zero.  `AnalyticOnNhd` rather than denominator nonvanishing is intentional: common numerator and
denominator zeros may be removable. -/
def SuzukiV2PoleFreeConvergenceOn
    (Ω : Set ℂ) (W : ℕ → ℂ → ℂ) : Prop :=
  IsOpen Ω ∧ IsPreconnected Ω ∧
  {z : ℂ | XiC z = 0} ⊆ Ω ∧
  AnalyticOnNhd ℂ suzukiV2CharacteristicTarget Ω ∧
  TendstoLocallyUniformlyOn W suzukiV2CharacteristicTarget atTop Ω ∧
  (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
  (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0) ∧
  0 ∈ Ω

/-- The existing corrected meromorphic wall is exactly existence of pole-free convergence on one
finite chart. -/
theorem suzukiV2MeromorphicCharacteristicLimitWall_iff_exists_poleFreeConvergenceOn :
    SuzukiV2MeromorphicCharacteristicLimitWall ↔
      ∃ (Ω : Set ℂ) (W : ℕ → ℂ → ℂ), SuzukiV2PoleFreeConvergenceOn Ω W := by
  rfl

/-- Two-chart compact convergence into the Riemann sphere.  `Ω₀` is the finite chart and `Ωinf` the
reciprocal chart.  Their union covers the plane, so genuine poles are transported through the
infinity chart rather than deleted from the convergence statement. -/
def SuzukiV2SphericalAtlasCharacteristicLimitWall : Prop :=
  ∃ (Ω₀ Ωinf : Set ℂ) (W : ℕ → ℂ → ℂ),
    SuzukiV2PoleFreeConvergenceOn Ω₀ W ∧
    IsOpen Ωinf ∧
    Ω₀ ∪ Ωinf = Set.univ ∧
    AnalyticOnNhd ℂ (fun z => (suzukiV2CharacteristicTarget z)⁻¹) Ωinf ∧
    TendstoLocallyUniformlyOn
      (fun n z => (W n z)⁻¹)
      (fun z => (suzukiV2CharacteristicTarget z)⁻¹) atTop Ωinf ∧
    EventuallyZeroFreeOnCompacta W Ωinf

/-- Spherical-atlas convergence contains the complete finite-chart convergence datum. -/
theorem suzukiV2SphericalAtlasCharacteristicLimitWall_implies_meromorphicWall :
    SuzukiV2SphericalAtlasCharacteristicLimitWall →
      SuzukiV2MeromorphicCharacteristicLimitWall := by
  rintro ⟨Ω₀, Ωinf, W, hfinite, _, _, _, _, _⟩
  exact
    suzukiV2MeromorphicCharacteristicLimitWall_iff_exists_poleFreeConvergenceOn.mpr
      ⟨Ω₀, W, hfinite⟩

/-- The globally spherical correction to Suzuki v2 remains RH-bearing. -/
theorem suzukiV2SphericalAtlasCharacteristicLimitWall_implies_riemannHypothesis :
    SuzukiV2SphericalAtlasCharacteristicLimitWall → RiemannHypothesis := by
  intro h
  exact suzukiV2MeromorphicCharacteristicLimitWall_implies_riemannHypothesis
    (suzukiV2SphericalAtlasCharacteristicLimitWall_implies_meromorphicWall h)

end

end RHTower
