import GaloisForLFunctions.RHTower.DeningerArithmeticGammaRankRegular

/-!
# Weight-one positive cup normalization no-go

On one complementary pair of complex eigendirections, weight-one flow covariance,
nondegeneracy, an odd Hodge operator, and strict cup--Hodge positivity leave a positive scalar
normalization undetermined.  Consequently these formal axioms cannot replace the arithmetic
Green--Paugam trace comparison required by Route L.

This is finite-dimensional source-side algebra.  It uses no Xi zero, spectral divisor, numerical
computation, or RH premise.
-/

namespace RHTower

noncomputable section

/-- One complementary pair of complex flow eigendirections. -/
abbrev DeningerComplementaryPlane := ℂ × ℂ

/-- Infinitesimal complementary-weight flow with eigenvalues `s` and `1 - s`. -/
def deningerComplementaryTheta (s : ℂ) (x : DeningerComplementaryPlane) :
    DeningerComplementaryPlane :=
  (s * x.1, (1 - s) * x.2)

/-- Positive-scale family of alternating cups on a complementary plane. -/
def deningerComplementaryCup (c : ℝ)
    (x y : DeningerComplementaryPlane) : ℂ :=
  (c : ℂ) * (x.1 * y.2 - x.2 * y.1)

/-- Anti-linear odd Hodge operator on a complementary plane. -/
def deningerComplementaryHodge (x : DeningerComplementaryPlane) :
    DeningerComplementaryPlane :=
  (-(starRingEnd ℂ) x.2, (starRingEnd ℂ) x.1)

/-- The cup is additive in its first variable. -/
theorem deningerComplementaryCup_add_left (c : ℝ)
    (x y z : DeningerComplementaryPlane) :
    deningerComplementaryCup c (x + y) z =
      deningerComplementaryCup c x z + deningerComplementaryCup c y z := by
  simp [deningerComplementaryCup]
  ring

/-- The cup is complex-linear in its first variable. -/
theorem deningerComplementaryCup_smul_left (c : ℝ) (a : ℂ)
    (x y : DeningerComplementaryPlane) :
    deningerComplementaryCup c (a • x) y =
      a * deningerComplementaryCup c x y := by
  simp [deningerComplementaryCup]
  ring

/-- The cup is additive in its second variable. -/
theorem deningerComplementaryCup_add_right (c : ℝ)
    (x y z : DeningerComplementaryPlane) :
    deningerComplementaryCup c x (y + z) =
      deningerComplementaryCup c x y + deningerComplementaryCup c x z := by
  simp [deningerComplementaryCup]
  ring

/-- The cup is complex-linear in its second variable. -/
theorem deningerComplementaryCup_smul_right (c : ℝ) (a : ℂ)
    (x y : DeningerComplementaryPlane) :
    deningerComplementaryCup c x (a • y) =
      a * deningerComplementaryCup c x y := by
  simp [deningerComplementaryCup]
  ring

/-- Every scaled complementary cup is alternating. -/
@[simp]
theorem deningerComplementaryCup_self (c : ℝ)
    (x : DeningerComplementaryPlane) :
    deningerComplementaryCup c x x = 0 := by
  simp only [deningerComplementaryCup]
  ring

/-- A nonzero scale gives a left-nondegenerate cup. -/
theorem deningerComplementaryCup_left_nondegenerate
    {c : ℝ} (hc : c ≠ 0) {x : DeningerComplementaryPlane}
    (hx : ∀ y, deningerComplementaryCup c x y = 0) :
    x = 0 := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  apply Prod.ext
  · have h := hx (0, 1)
    simpa [deningerComplementaryCup, hc'] using h
  · have h := hx (1, 0)
    simpa [deningerComplementaryCup, hc'] using h

/-- Complementary eigenweights give the exact weight-one derivation law. -/
theorem deningerComplementaryCup_weight_one (c : ℝ) (s : ℂ)
    (x y : DeningerComplementaryPlane) :
    deningerComplementaryCup c (deningerComplementaryTheta s x) y +
        deningerComplementaryCup c x (deningerComplementaryTheta s y) =
      deningerComplementaryCup c x y := by
  simp [deningerComplementaryCup, deningerComplementaryTheta]
  ring

/-- The anti-linear complementary Hodge operator squares to minus the identity. -/
@[simp]
theorem deningerComplementaryHodge_sq (x : DeningerComplementaryPlane) :
    deningerComplementaryHodge (deningerComplementaryHodge x) = -x := by
  rcases x with ⟨x₁, x₂⟩
  ext <;> simp [deningerComplementaryHodge]

/-- Cup followed by Hodge is exactly the scaled sum of coordinate norm-squares. -/
theorem deningerComplementaryCup_hodge_re (c : ℝ)
    (x : DeningerComplementaryPlane) :
    (deningerComplementaryCup c x (deningerComplementaryHodge x)).re =
      c * (Complex.normSq x.1 + Complex.normSq x.2) := by
  simp [deningerComplementaryCup, deningerComplementaryHodge,
    Complex.mul_conj]

/-- Positive scale makes the cup--Hodge diagonal strictly positive away from zero. -/
theorem deningerComplementaryCup_hodge_pos
    {c : ℝ} (hc : 0 < c) {x : DeningerComplementaryPlane} (hx : x ≠ 0) :
    0 < (deningerComplementaryCup c x (deningerComplementaryHodge x)).re := by
  rw [deningerComplementaryCup_hodge_re]
  apply mul_pos hc
  by_cases hx₁ : x.1 = 0
  · have hx₂ : x.2 ≠ 0 := by
      intro h
      apply hx
      exact Prod.ext hx₁ h
    exact add_pos_of_nonneg_of_pos
      (Complex.normSq_nonneg x.1) (Complex.normSq_pos.mpr hx₂)
  · exact add_pos_of_pos_of_nonneg
      (Complex.normSq_pos.mpr hx₁) (Complex.normSq_nonneg x.2)

/-- Distinct real scales already differ on the two coordinate generators. -/
theorem deningerComplementaryCup_distinct_scale
    {c d : ℝ} (hcd : c ≠ d) :
    deningerComplementaryCup c ≠ deningerComplementaryCup d := by
  intro h
  have hw := congrFun (congrFun h ((1 : ℂ), (0 : ℂ))) ((0 : ℂ), (1 : ℂ))
  simp [deningerComplementaryCup] at hw
  exact hcd hw

end

end RHTower
