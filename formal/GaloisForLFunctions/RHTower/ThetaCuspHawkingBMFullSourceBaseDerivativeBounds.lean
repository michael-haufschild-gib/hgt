import GaloisForLFunctions.RHTower.SelbergScatteringSourceBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth

/-! Weighted first base derivatives of the literal Xi Fourier tail.

The B2 differentiated-cap problem needs a global source-jet estimate, not
mere local smoothness.  The existing Bessel family differentiates horizontally
into the same signed family with one index weight; this file records that
closed weighted estimate.  It retains both signed tails and makes no
circle-average, transport, cap-limit, or RH claim.
-/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff MatrixGroups
namespace RHTower.D4BMFullSourceBaseDerivativeBounds
open D4BMAngularSeries D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem value_horizontal_eq (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (value u nu a d negative) z =
      horizontalRate negative * value u nu a (d + 1) negative z := by
  rw [coordDeriv, (value_hasFDerivAt u nu a d negative z hz).fderiv]
  simp [valueGradient, D4BMAngularSeries.gradient]

private theorem tail_horizontal_eq (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (tail u) z =
      2 * (horizontalRate false * value u u (1 / 2) 1 false z +
        horizontalRate true * value u u (1 / 2) 1 true z) := by
  have he : tail u =ᶠ[𝓝 z] (fun v =>
      2 * (value u u (1 / 2) 0 false v + value u u (1 / 2) 0 true v)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    simp only [tail, d4BMCompletedEisensteinCuspTailPart,
      d4BMCompletedEisensteinFullSignedZeroWord, signedTail_eq_value _ _ _ _ _ v hv,
      Nat.cast_zero, zero_add]
  have h0 := (value_hasFDerivAt u u (1 / 2) 0 false z hz).differentiableAt
  have h1 := (value_hasFDerivAt u u (1 / 2) 0 true z hz).differentiableAt
  unfold coordDeriv
  rw [he.fderiv_eq, fderiv_const_mul (h0.add h1), fderiv_fun_add h0 h1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [value_horizontal_eq u u (1 / 2) 0 false z hz,
    value_horizontal_eq u u (1 / 2) 0 true z hz]
  ring

/-- The complete signed Xi tail has a uniform weighted horizontal derivative
on every positive-height half-strip. -/
theorem weighted_tail_horizontal_bounded (u w : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * coordDeriv 0 (tail u) z‖ ≤ C := by
  obtain ⟨A, hA, hbA⟩ := weighted_value_bounded u u w (1 / 2) 1 false l hl
  obtain ⟨B, hB, hbB⟩ := weighted_value_bounded u u w (1 / 2) 1 true l hl
  refine ⟨2 * (‖horizontalRate false‖ * A + ‖horizontalRate true‖ * B),
    by positivity, ?_⟩
  intro z hz
  rw [tail_horizontal_eq u z (hl.trans_le hz)]
  have he : (z 1 : ℂ)^w *
      (2 * (horizontalRate false * value u u (1 / 2) 1 false z +
        horizontalRate true * value u u (1 / 2) 1 true z)) =
      2 * (horizontalRate false * ((z 1 : ℂ)^w * value u u (1 / 2) 1 false z) +
        horizontalRate true * ((z 1 : ℂ)^w * value u u (1 / 2) 1 true z)) := by
    ring
  rw [he, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ‖horizontalRate false * ((z 1 : ℂ)^w * value u u (1 / 2) 1 false z)‖ +
        ‖horizontalRate true * ((z 1 : ℂ)^w * value u u (1 / 2) 1 true z)‖ :=
      norm_add_le _ _
    _ = ‖horizontalRate false‖ *
          ‖(z 1 : ℂ)^w * value u u (1 / 2) 1 false z‖ +
        ‖horizontalRate true‖ *
          ‖(z 1 : ℂ)^w * value u u (1 / 2) 1 true z‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hbA z hz) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hbB z hz) (norm_nonneg _))

/-- Both literal first Fourier-tail base derivatives have uniform weighted
half-strip bounds. -/
theorem weighted_tail_base_bounded (u w : ℂ) (l : ℝ) (hl : 0 < l) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * coordDeriv 0 (tail u) z‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * coordDeriv 1 (tail u) z‖ ≤ C) :=
  ⟨weighted_tail_horizontal_bounded u w l hl,
    SelbergScatteringSourceBounds.weighted_tail_vertical_bounded u w l hl⟩

end
end RHTower.D4BMFullSourceBaseDerivativeBounds
