import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux

/-!
# Suzuki's physical-to-Weyl Carleman coordinate phase

Suzuki's positive-half-line screw multiplier is not the scalar-normalized centered multiplier
used by the existing pole algebra.  With `XiC z = xi (1/2 + I*z)`, the source multiplier is

`M_phys,0 = I * suzukiShiftedXiMultiplier 0`.

The distinction becomes essential after a real form shift.  The positive-half-line transform of
the global Neumann representative `r₀(t)=-|t|/2` is `1/(2*z²)`, so the exact one-sided centered
parameter is `eta=-I*lambda/2`.  Thus

`M_phys,lambda = I * suzukiShiftedXiMultiplier eta`.

Consequently a physical sheet `M_phys W-T_phys` enters the existing Xi-real pole algebra only
after multiplication by `-I`; its interval input is `-I*T_phys`, not `T_phys`.  This phase
converts the purely imaginary physical source flux into the real flux constrained by Herglotz
positivity.  Hence source quadrature does not falsify the normalized scalar jump-Pick conjecture.

This file proves the exact parameter, multiplier, sheet, central-flux, source-quadrature, and
Neumann-cancellation connectors.  The half-line integration identities motivating the source
definitions are proved on paper; no integration or computation is postulated here.

No RH assumption, positivity premise, estimate, or numerical computation is used.
-/

open Complex Filter Topology GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Exact one-sided source coordinate -/

/-- Exact centered parameter of Suzuki's positive-half-line sheet for real form shift `lambda`.
The factor `1/2` is the half-line share of the global Neumann symbol. -/
def suzukiOneSidedCenteredShiftParameter (lambda : ℝ) : ℂ :=
  -(I / 2) * (lambda : ℂ)

/-- The old boundary-free/bilateral projective coordinate is twice the one-sided coordinate. -/
theorem suzukiCenteredShiftParameter_eq_two_mul_oneSided (lambda : ℝ) :
    suzukiCenteredShiftParameter lambda =
      2 * suzukiOneSidedCenteredShiftParameter lambda := by
  simp only [suzukiCenteredShiftParameter, suzukiOneSidedCenteredShiftParameter]
  ring

/-- Passing to the exact one-sided centered coordinate loses no real source shift. -/
theorem suzukiOneSidedCenteredShiftParameter_injective :
    Function.Injective suzukiOneSidedCenteredShiftParameter := by
  intro alpha beta h
  apply suzukiCenteredShiftParameter_injective
  rw [suzukiCenteredShiftParameter_eq_two_mul_oneSided,
    suzukiCenteredShiftParameter_eq_two_mul_oneSided, h]

/-- Source-normalized physical multiplier of the shifted positive Carleman half-sheet. -/
def suzukiPhysicalRightCarlemanMultiplier (lambda : ℝ) (z : ℂ) : ℂ :=
  I * suzukiShiftedXiMultiplier (suzukiOneSidedCenteredShiftParameter lambda) z

/-- Away from the Xi divisor, the physical shifted multiplier is the zero-shift physical
multiplier minus exactly half the real Neumann symbol. -/
theorem suzukiPhysicalRightCarlemanMultiplier_eq
    (lambda : ℝ) {z : ℂ} (hXi : XiC z ≠ 0) :
    suzukiPhysicalRightCarlemanMultiplier lambda z =
      I * suzukiShiftedXiMultiplier 0 z - (lambda : ℂ) / (2 * z ^ (2 : ℕ)) := by
  simp only [suzukiPhysicalRightCarlemanMultiplier, suzukiShiftedXiMultiplier_eq,
    suzukiShiftedXiDenominator, suzukiOneSidedCenteredShiftParameter,
    zero_mul, sub_zero]
  field_simp [hXi]
  calc
    I * (deriv XiC z * 2 - -(I * (lambda : ℂ) * XiC z)) / z ^ (2 : ℕ) =
        (I * deriv XiC z * 2 + (I * I) * (lambda : ℂ) * XiC z) / z ^ (2 : ℕ) := by
          ring
    _ = (I * deriv XiC z * 2 - (lambda : ℂ) * XiC z) / z ^ (2 : ℕ) := by
          rw [I_mul_I]
          ring

/-! ## Physical sheet versus Xi-real Weyl normalization -/

/-- Canonical interval input for the Xi-real pole coordinate. -/
def suzukiWeylNormalizedRightTriangle (physicalTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  -I * physicalTriangle z

/-- Actual positive-half-line exterior convolution sheet. -/
def suzukiPhysicalRightCarlemanExterior
    (lambda : ℝ) (W physicalTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiPhysicalRightCarlemanMultiplier lambda z * W z - physicalTriangle z

/-- **Canonical phase law.** Multiplication of the physical sheet by `-I` gives exactly the
existing centered exterior algebra, provided its triangle is also rephased by `-I`. -/
theorem neg_I_mul_suzukiPhysicalRightCarlemanExterior
    (lambda : ℝ) (W physicalTriangle : ℂ → ℂ) (z : ℂ) :
    -I * suzukiPhysicalRightCarlemanExterior lambda W physicalTriangle z =
      suzukiRightCarlemanExterior
        (suzukiOneSidedCenteredShiftParameter lambda) W
        (suzukiWeylNormalizedRightTriangle physicalTriangle) z := by
  simp only [suzukiPhysicalRightCarlemanExterior, suzukiPhysicalRightCarlemanMultiplier,
    suzukiRightCarlemanExterior, suzukiWeylNormalizedRightTriangle]
  ring_nf
  rw [show I ^ (2 : ℕ) = (-1 : ℂ) by norm_num]
  ring

/-! ## Central physical flux and the corrected Herglotz threshold -/

/-- Affine central chord written in the real physical form-shift coordinate. -/
def suzukiPhysicalAffineSewnCentralSourceFlux
    (alpha beta : ℝ) (a b rightAlphaZero rightBetaZero : ℂ) : ℂ :=
  (((beta : ℂ) * b * rightAlphaZero -
      (alpha : ℂ) * a * rightBetaZero) /
    (((beta : ℂ) - alpha) * a * b))

/-- Rephasing both physical triangles by `-I` rephases the complete affine central flux by
`-I`; the common factor `-I/2` in the shift parameters cancels. -/
theorem suzukiWeylNormalizedCentralSourceFlux_eq_neg_I_mul_physical
    (alpha beta : ℝ) (a b rightAlphaZero rightBetaZero : ℂ) :
    suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        a b (-I * rightAlphaZero) (-I * rightBetaZero) =
      -I * suzukiPhysicalAffineSewnCentralSourceFlux
        alpha beta a b rightAlphaZero rightBetaZero := by
  simp only [suzukiAffineSewnCentralSourceFlux, suzukiOneSidedCenteredShiftParameter,
    suzukiPhysicalAffineSewnCentralSourceFlux]
  let c : ℂ := -(I / 2)
  let N : ℂ := (beta : ℂ) * b * rightAlphaZero -
    (alpha : ℂ) * a * rightBetaZero
  let D : ℂ := ((beta : ℂ) - alpha) * a * b
  rw [show -(I / 2) * (beta : ℂ) - -(I / 2) * (alpha : ℂ) =
      c * ((beta : ℂ) - alpha) by simp only [c]; ring]
  rw [show -(I / 2) * (beta : ℂ) * b * (-I * rightAlphaZero) -
      -(I / 2) * (alpha : ℂ) * a * (-I * rightBetaZero) =
      c * (-I * N) by simp only [c, N]; ring]
  rw [show (c * ((beta : ℂ) - alpha)) * a * b = c * D by
    simp only [D]; ring]
  rw [mul_div_mul_left (-I * N) D (by
    simp only [c]
    exact neg_ne_zero.mpr (div_ne_zero I_ne_zero (by norm_num)))]
  simp only [N, D]
  ring

/-- The real part constrained by Herglotz positivity is exactly the imaginary part of the
physical source flux. -/
theorem suzukiWeylNormalizedCentralSourceFlux_re_eq_physical_im
    (alpha beta : ℝ) (a b rightAlphaZero rightBetaZero : ℂ) :
    (suzukiAffineSewnCentralSourceFlux
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        a b (-I * rightAlphaZero) (-I * rightBetaZero)).re =
      (suzukiPhysicalAffineSewnCentralSourceFlux
        alpha beta a b rightAlphaZero rightBetaZero).im := by
  rw [suzukiWeylNormalizedCentralSourceFlux_eq_neg_I_mul_physical]
  simp [Complex.mul_re]

/-- Under Suzuki's actual source quadrature—real characteristic jets and purely imaginary
physical triangle values—the correctly normalized flux is real, not purely imaginary.  Thus
quadrature supplies no scalar Herglotz no-go. -/
theorem suzukiWeylNormalizedCentralSourceFlux_im_eq_zero_of_source_quadrature
    (alpha beta a b rightAlpha rightBeta : ℝ) :
    (suzukiAffineSewnCentralSourceFlux
      (suzukiOneSidedCenteredShiftParameter alpha)
      (suzukiOneSidedCenteredShiftParameter beta)
      (a : ℂ) (b : ℂ)
      (-I * (I * (rightAlpha : ℂ)))
      (-I * (I * (rightBeta : ℂ)))).im = 0 := by
  rw [suzukiWeylNormalizedCentralSourceFlux_eq_neg_I_mul_physical]
  have hval :
      -I * suzukiPhysicalAffineSewnCentralSourceFlux alpha beta (a : ℂ) (b : ℂ)
          (I * (rightAlpha : ℂ)) (I * (rightBeta : ℂ)) =
        (((beta * b * rightAlpha - alpha * a * rightBeta) /
          ((beta - alpha) * a * b) : ℝ) : ℂ) := by
    simp only [suzukiPhysicalAffineSewnCentralSourceFlux]
    push_cast
    field_simp
    rw [show I ^ (2 : ℕ) = (-1 : ℂ) by norm_num]
    ring
  rw [hval]
  change ((((beta * b * rightAlpha - alpha * a * rightBeta) /
    ((beta - alpha) * a * b) : ℝ) : ℂ)).im = 0
  exact Complex.ofReal_im _

/-- Source-form corollary of the central residue obstruction.  Herglotz positivity of the
correctly normalized sheet constrains the imaginary part of the physical flux. -/
theorem suzukiPhysicalCentralSourceFlux_im_le_XiC_curvature_of_normalized_herglotz
    {WAlpha WBeta physicalRightAlpha physicalRightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ physicalRightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ physicalRightBeta 0)
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (hHerglotz : ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient
        (suzukiOneSidedCenteredShiftParameter alpha)
        (suzukiOneSidedCenteredShiftParameter beta)
        WAlpha WBeta (suzukiWeylNormalizedRightTriangle physicalRightAlpha)
        (suzukiWeylNormalizedRightTriangle physicalRightBeta) z).im) :
    (suzukiPhysicalAffineSewnCentralSourceFlux alpha beta a b
      (physicalRightAlpha 0) (physicalRightBeta 0)).im ≤
      (deriv (deriv XiC) 0 / XiC 0).re := by
  have habCentered : suzukiOneSidedCenteredShiftParameter alpha ≠
      suzukiOneSidedCenteredShiftParameter beta :=
    suzukiOneSidedCenteredShiftParameter_injective.ne hab
  have hnormAlpha : DifferentiableAt ℂ
      (suzukiWeylNormalizedRightTriangle physicalRightAlpha) 0 := by
    exact (differentiableAt_const (-I)).mul hRightAlpha
  have hnormBeta : DifferentiableAt ℂ
      (suzukiWeylNormalizedRightTriangle physicalRightBeta) 0 := by
    exact (differentiableAt_const (-I)).mul hRightBeta
  have hflux := suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
    hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hnormAlpha hnormBeta habCentered hHerglotz
  change (suzukiAffineSewnCentralSourceFlux
    (suzukiOneSidedCenteredShiftParameter alpha)
    (suzukiOneSidedCenteredShiftParameter beta) a b
    (-I * physicalRightAlpha 0) (-I * physicalRightBeta 0)).re ≤ _ at hflux
  rw [suzukiWeylNormalizedCentralSourceFlux_re_eq_physical_im] at hflux
  exact hflux

/-! ## Correct one-sided Neumann cancellation -/

/-- In the exact one-sided centered coordinate `eta=-I*lambda/2`, the normalized direct Neumann
channel has slope `I*aperture`.  It still cancels identically under affine sewing. -/
theorem suzukiAffineSewnCentralSourceFlux_oneSided_neumann_channel_cancels
    (alpha beta a b gammaAlphaZero gammaBetaZero aperture : ℂ) :
    suzukiAffineSewnCentralSourceFlux alpha beta a b
        (gammaAlphaZero + (I * aperture) * alpha * a)
        (gammaBetaZero + (I * aperture) * beta * b) =
      suzukiAffineSewnCentralSourceFlux alpha beta a b
        gammaAlphaZero gammaBetaZero :=
  suzukiAffineSewnCentralSourceFlux_linear_shift_channel_cancels
    alpha beta a b gammaAlphaZero gammaBetaZero (I * aperture)

end

end RHTower
