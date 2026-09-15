import GaloisForLFunctions.RHTower.CCMActualHeadExteriorCosineDualMassWall

/-!
# Scale-covariant Jordan-mass wall for exterior CCM gauges

The exterior-gauge obstruction must persist when the physical aperture moves: an aperture-
dependent completion is not exempt merely because its exterior support threshold is changed at
each stage.  This module removes that loophole.

For an arbitrary positive scale `u N = delta N * H0 N` tending to infinity, any signed finite
exterior-measure gauge which approximates the constant mode with fixed error on the corresponding
Sonin window has Jordan mass exceeding every fixed power of `u N`.  No rate relation between the
window width and the moving exterior threshold is imposed beyond the physically necessary scale
escape `u N -> infinity`.

This is an obstruction theorem only.  It does not assert that a source-adapted completion has the
constant-approximation property, and it does not infer RH.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- **Scale-covariant exterior Jordan-mass wall.**  Let both the exterior support threshold and
the Sonin-window scale vary.  If their product escapes to infinity, then fixed-error approximation
of the constant mode by a positive-minus-positive exterior cosine gauge forces the combined Jordan
mass to dominate every fixed power of that product. -/
theorem tendsto_exteriorCosineMeasureGauge_mass_div_scalePow_atTop_of_variable_constant_approximation
    {H₀ delta : ℕ → ℝ} {ε : ℝ}
    (hH₀ : ∀ N : ℕ, 0 < H₀ N)
    (hdelta : ∀ N : ℕ, 0 < delta N)
    (hscale : Tendsto (fun N : ℕ => delta N * H₀ N) atTop atTop)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (μ ν : ℕ → FiniteMeasure ℝ)
    (hμ : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(μ N : Measure ℝ), H₀ N ≤ h)
    (hν : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(ν N : Measure ℝ), H₀ N ≤ h)
    (happrox : ∀ N : ℕ, ∀ x : ℝ,
      soninScaledAnnulusBump 0 (delta N) x ≠ 0 →
        |1 - (ccmActualHeadExteriorCosineMeasureGauge (μ N : Measure ℝ) x -
          ccmActualHeadExteriorCosineMeasureGauge (ν N : Measure ℝ) x)| ≤ ε)
    (p : ℕ) :
    Tendsto (fun N : ℕ =>
      ((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) /
        (delta N * H₀ N) ^ p) atTop atTop := by
  let u : ℕ → ℝ := fun N => delta N * H₀ N
  let S : ℕ → ℝ := fun N => u N ^ p * soninRefTailSup (u N)
  let M : ℕ → ℝ := fun N =>
    ((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) /
      u N ^ p
  let A : ℝ := (1 - ε) * ∫ y : ℝ, soninUnitBumpData y
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (sub_pos.mpr hε1) integral_soninUnitBumpData_pos
  have hu : ∀ N : ℕ, 0 < u N := fun N => by
    dsimp only [u]
    exact mul_pos (hdelta N) (hH₀ N)
  have hS : Tendsto S atTop (nhds 0) := by
    exact (tendsto_pow_mul_soninRefTailSup_atTop p).comp hscale
  have hS0 : ∀ N : ℕ, 0 ≤ S N := fun N => by
    dsimp only [S]
    exact mul_nonneg (pow_nonneg (hu N).le p) (soninRefTailSup_nonneg _)
  have hlower : ∀ N : ℕ, A ≤ 2 * S N * M N := by
    intro N
    have hbase :=
      exteriorCosineMeasureGauge_mass_lower_bound_of_constant_approximation
        0 (delta N) (H₀ N) ε (hdelta N) (hH₀ N).le hε0
        (μ N : Measure ℝ) (ν N : Measure ℝ) (hμ N) (hν N) (happrox N)
    have hupow : (delta N * H₀ N) ^ p ≠ 0 :=
      pow_ne_zero p (mul_ne_zero (hdelta N).ne' (hH₀ N).ne')
    dsimp only [A, S, M]
    change A ≤ 2 * ((delta N * H₀ N) ^ p *
      soninRefTailSup (delta N * H₀ N)) *
        (((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) /
          (delta N * H₀ N) ^ p)
    convert hbase using 1
    field_simp [hupow]
  change Tendsto M atTop atTop
  exact tendsto_atTop_of_nonneg_vanishing_mul_lower hA hS0 hS hlower

end RHTower
