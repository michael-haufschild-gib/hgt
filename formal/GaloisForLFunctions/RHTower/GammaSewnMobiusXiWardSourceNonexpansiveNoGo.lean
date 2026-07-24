import GaloisForLFunctions.RHTower.MobiusDoubledParityHardyTransverseGram

/-!
# The singular Möbius--Gamma/Xi graph is not source-nonexpansive

The existing Ward transport is contractive as a Hardy multiplier in its target variable.  That is
not source-side contractivity.  Its squarefree graph stage divides a source score by
`epsilon * overlap`.

At the base aperture the overlap is exactly one.  Therefore the affine dependence of the complete
Möbius--Gamma/Xi transport on a source vector has exact Lipschitz gain `1 / (2|epsilon|)`.  Along
the physical critical ray `epsilon = sigma - 1`, this exceeds one for every
`1 < sigma < 3/2`.

Consequently the already-constructed `V` cannot transport Hilbert Gram positivity in the ambient
source norm.  Any successful four-unit lift must put this division inside a genuinely singular
graph norm; target Hardy multiplier nonexpansiveness cannot replace that missing source theorem.
-/

open Complex
open scoped ComplexOrder

namespace RHTower

noncomputable section

private theorem squarefreeBoundaryOverlap_base
    {sigma epsilon : ℂ} (hsigma : 1 < sigma.re) :
    GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon 0 = 1 := by
  rw [GaloisForLFunctions.squarefreeBoundaryOverlap]
  simp only [zero_mul, add_zero]
  exact div_self
    (GaloisForLFunctions.squarefreePartition_ne_zero hsigma)

/-- Affine base-aperture response of the complete graph transport to a source vector. -/
def mobiusGammaXiWardBaseSourceMap
    (sigma : ℝ) (epsilon : ℂ) (hsigma : 1 < sigma)
    (x : lp (fun _ : ℕ => ℂ) 2) : ℂ :=
  squarefreeMobiusGammaXiWardTransportV
    (sigma : ℂ) epsilon
    (fun _ =>
      inner ℂ x (infiniteMobiusSignedWeightLp sigma hsigma))
    0

/-- Exact affine gain of the graph transport at the base aperture. -/
theorem mobiusGammaXiWardBaseSourceMap_sub
    {sigma : ℝ} {epsilon : ℂ} (hsigma : 1 < sigma)
    (hepsilon : epsilon ≠ 0)
    (x y : lp (fun _ : ℕ => ℂ) 2) :
    mobiusGammaXiWardBaseSourceMap sigma epsilon hsigma x -
        mobiusGammaXiWardBaseSourceMap sigma epsilon hsigma y =
      (I / (2 * epsilon)) *
        (inner ℂ x (infiniteMobiusSignedWeightLp sigma hsigma) -
          inner ℂ y (infiniteMobiusSignedWeightLp sigma hsigma)) := by
  simp only [mobiusGammaXiWardBaseSourceMap,
    squarefreeMobiusGammaXiWardTransportV,
    squarefreeMobiusGammaCurrentTransportV]
  rw [squarefreeBoundaryOverlap_base
    (by simpa using hsigma)]
  field_simp [hepsilon]
  ring

/-- The normalized source vector is amplified by exactly the singular gain. -/
theorem mobiusGammaXiWardBaseSourceMap_source_sub_zero
    {sigma : ℝ} {epsilon : ℂ} (hsigma : 1 < sigma)
    (hepsilon : epsilon ≠ 0) :
    mobiusGammaXiWardBaseSourceMap sigma epsilon hsigma
          (infiniteMobiusSignedWeightLp sigma hsigma) -
        mobiusGammaXiWardBaseSourceMap sigma epsilon hsigma 0 =
      I / (2 * epsilon) := by
  rw [mobiusGammaXiWardBaseSourceMap_sub hsigma hepsilon,
    inner_zero_left, sub_zero, inner_self_eq_norm_sq_to_K,
    norm_infiniteMobiusSignedWeightLp hsigma]
  norm_num

/-- On the critical ray the source gain is already expansive before the endpoint. -/
theorem norm_mobiusGammaXiWardBaseSourceMap_source_sub_zero_gt_one
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma < 3 / 2) :
    1 <
      ‖mobiusGammaXiWardBaseSourceMap sigma ((sigma - 1 : ℝ) : ℂ) hsigma
            (infiniteMobiusSignedWeightLp sigma hsigma) -
          mobiusGammaXiWardBaseSourceMap sigma ((sigma - 1 : ℝ) : ℂ) hsigma 0‖ := by
  have hepsilon : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  rw [mobiusGammaXiWardBaseSourceMap_source_sub_zero hsigma hepsilon,
    norm_div, norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hsigma)]
  norm_num
  rw [one_div]
  have hden : 0 < 2 * (sigma - 1) := by linarith
  rw [← mul_inv, mul_comm (sigma - 1) 2]
  apply (one_lt_inv₀ hden).2
  linarith

/-- **Source nonexpansiveness no-go for the fixed `V`.**  For every critical parameter below
`3/2`, the base-aperture affine source map violates the one-Lipschitz inequality on two explicit
source vectors. -/
theorem not_mobiusGammaXiWardBaseSourceMap_nonexpansive
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma < 3 / 2) :
    ¬ ∀ x y : lp (fun _ : ℕ => ℂ) 2,
        ‖mobiusGammaXiWardBaseSourceMap sigma ((sigma - 1 : ℝ) : ℂ) hsigma x -
            mobiusGammaXiWardBaseSourceMap sigma ((sigma - 1 : ℝ) : ℂ) hsigma y‖ ≤
          ‖x - y‖ := by
  intro hnonexpansive
  have hle := hnonexpansive
    (infiniteMobiusSignedWeightLp sigma hsigma) 0
  rw [sub_zero, norm_infiniteMobiusSignedWeightLp hsigma] at hle
  exact (not_lt_of_ge hle)
    (norm_mobiusGammaXiWardBaseSourceMap_source_sub_zero_gt_one
      hsigma hsigmaUpper)

/-! ## Normal-cone blow-up does not repair source gain -/

/-- Euler-normal blow-up of the fixed base-aperture source graph.  The
subtraction-free definition is intentional: affine constants disappear when
testing Lipschitz gain. -/
def mobiusGammaXiWardNormalConeBaseSourceMap
    (sigma : ℝ) (hsigma : 1 < sigma)
    (x : lp (fun _ : ℕ => ℂ) 2) : ℂ :=
  mobiusGammaXiWardBaseSourceMap sigma
      ((sigma - 1 : ℝ) : ℂ) hsigma x /
    ((sigma - 1 : ℝ) : ℂ)

/-- **Normal-cone gain-squaring law.**  Blowing up the scalar source graph
by its Euler normal parameter changes the exact physical Lipschitz gain from
`1 / (2 (sigma - 1))` to `1 / (2 (sigma - 1)^2)`.  Analytic removal of the
base zero therefore amplifies, rather than absorbs, the source-norm defect. -/
theorem mobiusGammaXiWardNormalConeBaseSourceMap_source_sub_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma
          (infiniteMobiusSignedWeightLp sigma hsigma) -
        mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma 0 =
      I / (2 * (((sigma - 1 : ℝ) : ℂ) ^ 2)) := by
  have hepsilon : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  simp only [mobiusGammaXiWardNormalConeBaseSourceMap]
  rw [← sub_div,
    mobiusGammaXiWardBaseSourceMap_source_sub_zero hsigma hepsilon]
  field_simp [hepsilon]

/-- On the physical critical ray, the normal-cone source graph is strictly
expansive on the same explicit unit source vector. -/
theorem norm_mobiusGammaXiWardNormalConeBaseSourceMap_source_sub_zero_gt_one
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma < 3 / 2) :
    1 <
      ‖mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma
            (infiniteMobiusSignedWeightLp sigma hsigma) -
          mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma 0‖ := by
  rw [mobiusGammaXiWardNormalConeBaseSourceMap_source_sub_zero hsigma,
    norm_div, norm_I, norm_mul, Complex.norm_ofNat, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hsigma)]
  norm_num
  have heps : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hepsHalf : sigma - 1 < 1 / 2 := by linarith
  have hsq : 2 * (sigma - 1) ^ 2 < 1 := by
    nlinarith [sq_nonneg (sigma - 1), mul_self_lt_mul_self heps.le hepsHalf]
  rw [show ((sigma - 1) ^ 2)⁻¹ * (1 / 2 : ℝ) =
      1 / (2 * (sigma - 1) ^ 2) by field_simp]
  exact (one_lt_div₀ (by positivity)).2 hsq

/-- **Normal-cone nonexpansiveness no-go.**  The analytic Euler blow-up of
the fixed scalar graph is not a contraction in the physical source norm.
Thus normal-cone regularity alone cannot supply the missing CCM source
transport. -/
theorem not_mobiusGammaXiWardNormalConeBaseSourceMap_nonexpansive
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma < 3 / 2) :
    ¬ ∀ x y : lp (fun _ : ℕ => ℂ) 2,
        ‖mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma x -
            mobiusGammaXiWardNormalConeBaseSourceMap sigma hsigma y‖ ≤
          ‖x - y‖ := by
  intro hnonexpansive
  have hle := hnonexpansive
    (infiniteMobiusSignedWeightLp sigma hsigma) 0
  rw [sub_zero, norm_infiniteMobiusSignedWeightLp hsigma] at hle
  exact (not_lt_of_ge hle)
    (norm_mobiusGammaXiWardNormalConeBaseSourceMap_source_sub_zero_gt_one
      hsigma hsigmaUpper)

end

end RHTower
