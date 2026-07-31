import GaloisForLFunctions.RHTower.RectangularGammaIntervalCellBridge

/-!
# Signed width-normal lift of rectangular tomography

The rectangular amplitude has a canonical source orientation in its width:

`∂_L A_L(w) = exp (-Lw)`.

Therefore differentiating the multiplicity-weighted squared residue model
`2m A_L(w)^2`, then multiplying by `exp(Lw) / 4`, recovers the unsquared
signed cell `m A_L(w)`.  The recovery uses no square-root branch and no
zero-dependent normalization.

This file proves the exact local width-normal algebra.  It does not prove
that width differentiation commutes with the cutoff-free global Dirichlet
continuation; that distributional continuation theorem remains open.
-/

open Complex

namespace RHTower

noncomputable section

/-- Rectangular amplitude with a complexified width parameter. -/
def rectangularWindowAmplitudeComplex (L w : ℂ) : ℂ :=
  if w = 0 then L else (1 - Complex.exp (-L * w)) / w

@[simp] theorem rectangularWindowAmplitudeComplex_zero (L : ℂ) :
    rectangularWindowAmplitudeComplex L 0 = L := by
  simp [rectangularWindowAmplitudeComplex]

theorem rectangularWindowAmplitudeComplex_ofReal
    (L : ℝ) (w : ℂ) :
    rectangularWindowAmplitudeComplex (L : ℂ) w =
      rectangularWindowAmplitude L w := by
  by_cases hw : w = 0
  · subst w
    simp
  · simp [rectangularWindowAmplitudeComplex,
      rectangularWindowAmplitude, hw]

/-- Complex-width rectangular amplitude is the same entire
Gamma/co-Poisson interval cell. -/
theorem rectangularWindowAmplitudeComplex_eq_gammaCoPoissonIntervalCell
    (L w : ℂ) :
    rectangularWindowAmplitudeComplex L w =
      gammaCoPoissonIntervalCell L (1 / 2) (1 / 2 - w) := by
  by_cases hw : w = 0
  · subst w
    simp only [sub_zero]
    rw [rectangularWindowAmplitudeComplex_zero,
      gammaCoPoissonIntervalCell_self]
    simp
  · rw [gammaCoPoissonIntervalCell_eq_dividedDifference]
    · simp only [rectangularWindowAmplitudeComplex, hw, if_false]
      congr 1
      · rw [show ((1 / 2 : ℂ) - 1 / 2) * L = 0 by ring,
          Complex.exp_zero]
        congr 1
        congr 1
        ring
      · ring
    · intro h
      apply hw
      linear_combination h

/-- Width-normal derivative of the rectangular amplitude. -/
theorem hasDerivAt_rectangularWindowAmplitudeComplex_width
    (L w : ℂ) :
    HasDerivAt (fun U => rectangularWindowAmplitudeComplex U w)
      (Complex.exp (-L * w)) L := by
  by_cases hw : w = 0
  · subst w
    have heq :
        (fun U : ℂ => rectangularWindowAmplitudeComplex U 0) =
          fun U : ℂ => U := by
      funext U
      simp [rectangularWindowAmplitudeComplex]
    rw [heq]
    rw [show Complex.exp (-L * 0) = 1 by simp]
    have hid : (fun U : ℂ => U) = id := by
      funext U
      rfl
    rw [hid]
    exact hasDerivAt_id L
  · have hinner :
        HasDerivAt (fun U : ℂ => (-U) * w) (-w) L := by
      simpa [id_eq] using
        (hasDerivAt_id L).neg.mul_const w
    have hnum :
        HasDerivAt (fun U : ℂ => 1 - Complex.exp ((-U) * w))
          (w * Complex.exp (-L * w)) L := by
      have hraw := (hasDerivAt_const L (1 : ℂ)).sub hinner.cexp
      have hfun :
          (fun U : ℂ => 1 - Complex.exp ((-U) * w)) =
            (fun x : ℂ => 1) -
              fun x : ℂ => Complex.exp ((-x) * w) := by
        funext U
        rfl
      have hder :
          w * Complex.exp (-L * w) =
            0 - Complex.exp (-L * w) * -w := by ring
      rw [hfun, hder]
      exact hraw
    have hquot :
        HasDerivAt
          (fun U : ℂ => (1 - Complex.exp ((-U) * w)) / w)
          ((w * Complex.exp (-L * w)) / w) L :=
      hnum.div_const w
    have heq :
        (fun U : ℂ => rectangularWindowAmplitudeComplex U w) =
          fun U : ℂ => (1 - Complex.exp ((-U) * w)) / w := by
      funext U
      simp [rectangularWindowAmplitudeComplex, hw]
    rw [heq]
    convert hquot using 1
    field_simp [hw]

/-- Local model of the already-proved tomography residue `2m A_L(w)^2`. -/
def rectangularTomographyResidueModel
    (m : ℕ) (L w : ℂ) : ℂ :=
  2 * (m : ℂ) * rectangularWindowAmplitudeComplex L w ^ 2

theorem hasDerivAt_rectangularTomographyResidueModel_width
    (m : ℕ) (L w : ℂ) :
    HasDerivAt (fun U => rectangularTomographyResidueModel m U w)
      (4 * (m : ℂ) * rectangularWindowAmplitudeComplex L w *
        Complex.exp (-L * w)) L := by
  have hA := hasDerivAt_rectangularWindowAmplitudeComplex_width L w
  change HasDerivAt
    (fun U =>
      2 * (m : ℂ) * rectangularWindowAmplitudeComplex U w ^ 2)
    _ L
  have hmodel := (hA.pow 2).const_mul (2 * (m : ℂ))
  have hfun :
      (fun U =>
        2 * (m : ℂ) * rectangularWindowAmplitudeComplex U w ^ 2) =
        fun y =>
          2 * (m : ℂ) *
            ((fun U => rectangularWindowAmplitudeComplex U w) ^ 2) y := by
    funext U
    rfl
  have hder :
      4 * (m : ℂ) * rectangularWindowAmplitudeComplex L w *
          Complex.exp (-L * w) =
        2 * (m : ℂ) *
          ((2 : ℂ) * rectangularWindowAmplitudeComplex L w ^ (2 - 1) *
            Complex.exp (-L * w)) := by
    norm_num
    ring
  rw [hfun, hder]
  exact hmodel

/-- Width-normal transgression of the squared residue model. -/
def rectangularSignedWidthLift
    (m : ℕ) (L w : ℂ) : ℂ :=
  Complex.exp (L * w) / 4 *
    deriv (fun U => rectangularTomographyResidueModel m U w) L

/-- Width-normal transgression recovers the signed amplitude. -/
theorem rectangularSignedWidthLift_eq
    (m : ℕ) (L w : ℂ) :
    rectangularSignedWidthLift m L w =
      (m : ℂ) * rectangularWindowAmplitudeComplex L w := by
  rw [rectangularSignedWidthLift,
    (hasDerivAt_rectangularTomographyResidueModel_width m L w).deriv]
  have hcancel :
      Complex.exp (L * w) * Complex.exp (-L * w) = 1 := by
    rw [← Complex.exp_add, show L * w + -L * w = 0 by ring,
      Complex.exp_zero]
  calc
    Complex.exp (L * w) / 4 *
          (4 * (m : ℂ) * rectangularWindowAmplitudeComplex L w *
            Complex.exp (-L * w)) =
        (m : ℂ) * rectangularWindowAmplitudeComplex L w *
          (Complex.exp (L * w) * Complex.exp (-L * w)) := by ring
    _ = (m : ℂ) * rectangularWindowAmplitudeComplex L w := by
      rw [hcancel, mul_one]

/-- The recovered signed amplitude is exactly the Gamma/co-Poisson cell. -/
theorem rectangularSignedWidthLift_eq_gammaCoPoissonIntervalCell
    (m : ℕ) (L w : ℂ) :
    rectangularSignedWidthLift m L w =
      (m : ℂ) *
        gammaCoPoissonIntervalCell L (1 / 2) (1 / 2 - w) := by
  rw [rectangularSignedWidthLift_eq,
    rectangularWindowAmplitudeComplex_eq_gammaCoPoissonIntervalCell]

/-- The interval cell vanishes at collapsed width. -/
theorem rectangularWindowAmplitudeComplex_zero_width (w : ℂ) :
    rectangularWindowAmplitudeComplex 0 w = 0 := by
  by_cases hw : w = 0
  · subst w
    simp
  · simp [rectangularWindowAmplitudeComplex, hw]

/-- First width derivative of the squared tomography residue. -/
def rectangularTomographyResidueFirstWidthDerivative
    (m : ℕ) (L w : ℂ) : ℂ :=
  4 * (m : ℂ) * rectangularWindowAmplitudeComplex L w *
    Complex.exp (-L * w)

theorem deriv_rectangularTomographyResidueModel_width
    (m : ℕ) (L w : ℂ) :
    deriv (fun U => rectangularTomographyResidueModel m U w) L =
      rectangularTomographyResidueFirstWidthDerivative m L w := by
  exact (hasDerivAt_rectangularTomographyResidueModel_width m L w).deriv

/-- Second width derivative of the squared tomography residue. -/
def rectangularTomographyResidueSecondWidthDerivative
    (m : ℕ) (L w : ℂ) : ℂ :=
  4 * (m : ℂ) *
    (Complex.exp (-2 * L * w) -
      w * rectangularWindowAmplitudeComplex L w *
        Complex.exp (-L * w))

theorem hasDerivAt_rectangularTomographyResidueFirstWidthDerivative
    (m : ℕ) (L w : ℂ) :
    HasDerivAt
      (fun U => rectangularTomographyResidueFirstWidthDerivative m U w)
      (rectangularTomographyResidueSecondWidthDerivative m L w) L := by
  have hA := hasDerivAt_rectangularWindowAmplitudeComplex_width L w
  have hE : HasDerivAt (fun U : ℂ => Complex.exp (-U * w))
      (-w * Complex.exp (-L * w)) L := by
    simpa [mul_comm] using ((hasDerivAt_id L).neg.mul_const w).cexp
  have hprod := hA.mul hE
  have hscaled := hprod.const_mul (4 * (m : ℂ))
  have hsq :
      Complex.exp (-L * w) * Complex.exp (-L * w) =
        Complex.exp (-2 * L * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hfun :
      (fun U => rectangularTomographyResidueFirstWidthDerivative m U w) =
        fun U =>
          4 * (m : ℂ) *
            (((fun V => rectangularWindowAmplitudeComplex V w) *
              fun V => Complex.exp (-V * w)) U) := by
    funext U
    unfold rectangularTomographyResidueFirstWidthDerivative
    simp only [Pi.mul_apply]
    ring
  rw [hfun]
  apply hscaled.congr_deriv
  simp only [rectangularTomographyResidueSecondWidthDerivative]
  rw [hsq]
  ring

theorem hasDerivAt_deriv_rectangularTomographyResidueModel_width
    (m : ℕ) (L w : ℂ) :
    HasDerivAt
      (fun U => deriv (fun V => rectangularTomographyResidueModel m V w) U)
      (rectangularTomographyResidueSecondWidthDerivative m L w) L := by
  have heq :
      (fun U => deriv (fun V => rectangularTomographyResidueModel m V w) U) =
        fun U => rectangularTomographyResidueFirstWidthDerivative m U w := by
    funext U
    exact deriv_rectangularTomographyResidueModel_width m U w
  rw [heq]
  exact hasDerivAt_rectangularTomographyResidueFirstWidthDerivative m L w

/-- The second collapsed-width jet recovers analytic multiplicity. -/
theorem rectangularTomographyResidue_secondWidthJet
    (m : ℕ) (w : ℂ) :
    deriv
      (fun U => deriv (fun V => rectangularTomographyResidueModel m V w) U)
      0 = 4 * (m : ℂ) := by
  rw [(hasDerivAt_deriv_rectangularTomographyResidueModel_width m 0 w).deriv]
  simp [rectangularTomographyResidueSecondWidthDerivative,
    rectangularWindowAmplitudeComplex_zero_width]

/-- Third width derivative of the squared tomography residue. -/
def rectangularTomographyResidueThirdWidthDerivative
    (m : ℕ) (L w : ℂ) : ℂ :=
  4 * (m : ℂ) *
    (-2 * w * Complex.exp (-2 * L * w) -
      w *
        (Complex.exp (-2 * L * w) -
          w * rectangularWindowAmplitudeComplex L w *
            Complex.exp (-L * w)))

theorem hasDerivAt_rectangularTomographyResidueSecondWidthDerivative
    (m : ℕ) (L w : ℂ) :
    HasDerivAt
      (fun U => rectangularTomographyResidueSecondWidthDerivative m U w)
      (rectangularTomographyResidueThirdWidthDerivative m L w) L := by
  have hE2 : HasDerivAt (fun U : ℂ => Complex.exp ((-2 * U) * w))
      ((-2 * w) * Complex.exp (-2 * L * w)) L := by
    have hi : HasDerivAt (fun U : ℂ => (-2 * U) * w) (-2 * w) L := by
      simpa using ((hasDerivAt_id L).const_mul (-2 : ℂ)).mul_const w
    have hce := hi.cexp
    have hfun :
        (fun U : ℂ => Complex.exp ((-2 * U) * w)) =
          fun U => Complex.exp ((fun V : ℂ => (-2 * V) * w) U) := by
      rfl
    rw [hfun]
    apply hce.congr_deriv
    ring
  have hA := hasDerivAt_rectangularWindowAmplitudeComplex_width L w
  have hE : HasDerivAt (fun U : ℂ => Complex.exp (-U * w))
      (-w * Complex.exp (-L * w)) L := by
    simpa [mul_comm] using ((hasDerivAt_id L).neg.mul_const w).cexp
  have hAE := hA.mul hE
  have hinside := hE2.sub (hAE.const_mul w)
  have hscaled := hinside.const_mul (4 * (m : ℂ))
  have hsq :
      Complex.exp (-L * w) * Complex.exp (-L * w) =
        Complex.exp (-2 * L * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hfun :
      (fun U => rectangularTomographyResidueSecondWidthDerivative m U w) =
        fun U =>
          4 * (m : ℂ) *
            (((fun V => Complex.exp (-2 * V * w)) -
              fun V =>
                w *
                  (((fun W => rectangularWindowAmplitudeComplex W w) *
                    fun W => Complex.exp (-W * w)) V)) U) := by
    funext U
    unfold rectangularTomographyResidueSecondWidthDerivative
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun]
  apply hscaled.congr_deriv
  simp only [rectangularTomographyResidueThirdWidthDerivative]
  rw [hsq]
  ring

theorem hasDerivAt_secondDeriv_rectangularTomographyResidueModel_width
    (m : ℕ) (L w : ℂ) :
    HasDerivAt
      (fun U =>
        deriv
          (fun V => deriv
            (fun W => rectangularTomographyResidueModel m W w) V) U)
      (rectangularTomographyResidueThirdWidthDerivative m L w) L := by
  have heq :
      (fun U =>
        deriv
          (fun V => deriv
            (fun W => rectangularTomographyResidueModel m W w) V) U) =
        fun U => rectangularTomographyResidueSecondWidthDerivative m U w := by
    funext U
    exact (hasDerivAt_deriv_rectangularTomographyResidueModel_width m U w).deriv
  rw [heq]
  exact hasDerivAt_rectangularTomographyResidueSecondWidthDerivative m L w

/-- The third collapsed-width jet recovers multiplicity times the signed centered zero. -/
theorem rectangularTomographyResidue_thirdWidthJet
    (m : ℕ) (w : ℂ) :
    deriv
      (fun U =>
        deriv
          (fun V => deriv
            (fun W => rectangularTomographyResidueModel m W w) V) U)
      0 = -12 * (m : ℂ) * w := by
  rw [(hasDerivAt_secondDeriv_rectangularTomographyResidueModel_width
    m 0 w).deriv]
  simp [rectangularTomographyResidueThirdWidthDerivative,
    rectangularWindowAmplitudeComplex_zero_width]
  ring

/-- Branch-free recovery of multiplicity from the collapsed-width polar germ. -/
theorem rectangularTomographyResidue_widthJet_recovers_multiplicity
    (m : ℕ) (w : ℂ) :
    (1 / 4 : ℂ) *
      deriv
        (fun U => deriv (fun V => rectangularTomographyResidueModel m V w) U)
        0 = (m : ℂ) := by
  rw [rectangularTomographyResidue_secondWidthJet]
  ring

/-- Branch-free linear recovery of the oriented multiplicity-weighted centered zero. -/
theorem rectangularTomographyResidue_widthJet_recovers_orientedZero
    (m : ℕ) (w : ℂ) :
    (-1 / 12 : ℂ) *
      deriv
        (fun U =>
          deriv
            (fun V => deriv
              (fun W => rectangularTomographyResidueModel m W w) V) U)
        0 = (m : ℂ) * w := by
  rw [rectangularTomographyResidue_thirdWidthJet]
  ring

/-- Entire normal-cone extension of one actual observable polar coefficient
through collapsed width.  Positive real widths agree with the arithmetic
cutoff-free continuation below; width zero is its polar blow-up, not the
ordinary trailing coefficient of the degenerate holomorphic function. -/
def xiRectangularPolarWidthGerm (q : XiRightZeroCopy) (L : ℂ) : ℂ :=
  rectangularTomographyResidueModel
    (xiRightMultiplicity q) L (xiRightCenteredZero q)

/-- At every positive real width, the normal-cone germ is the actual
cutoff-free tomography residue. -/
theorem xiRectangularPolarWidthGerm_ofReal_eq_fullObservableResidue
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    xiRectangularPolarWidthGerm q (L : ℂ) =
      meromorphicTrailingCoeffAt
        (xiRectangularWeilFullContinuation L)
        (xiRightShiftedPole q) := by
  rw [meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation hL q]
  simp only [xiRectangularPolarWidthGerm,
    rectangularTomographyResidueModel, xiRectangularRightCoefficient]
  rw [rectangularWindowAmplitudeComplex_ofReal]

/-- The second source-width jet of the actual polar normal-cone germ recovers
analytic multiplicity. -/
theorem xiRectangularPolarWidthGerm_secondJet
    (q : XiRightZeroCopy) :
    deriv
      (fun U => deriv (xiRectangularPolarWidthGerm q) U) 0 =
      4 * (xiRightMultiplicity q : ℂ) := by
  exact rectangularTomographyResidue_secondWidthJet
    (xiRightMultiplicity q) (xiRightCenteredZero q)

/-- The third source-width jet is the signed multiplicity-weighted centered
zero. -/
theorem xiRectangularPolarWidthGerm_thirdJet
    (q : XiRightZeroCopy) :
    deriv
      (fun U => deriv (fun V => deriv (xiRectangularPolarWidthGerm q) V) U)
      0 =
      -12 * (xiRightMultiplicity q : ℂ) * xiRightCenteredZero q := by
  exact rectangularTomographyResidue_thirdWidthJet
    (xiRightMultiplicity q) (xiRightCenteredZero q)

/-- Universal linear normal-jet recovery of the oriented polar coordinate
from the actual observable polar germ. -/
theorem xiRectangularPolarWidthGerm_recovers_orientedZero
    (q : XiRightZeroCopy) :
    (-1 / 12 : ℂ) *
      deriv
        (fun U => deriv
          (fun V => deriv (xiRectangularPolarWidthGerm q) V) U)
        0 =
      (xiRightMultiplicity q : ℂ) * xiRightCenteredZero q := by
  exact rectangularTomographyResidue_widthJet_recovers_orientedZero
    (xiRightMultiplicity q) (xiRightCenteredZero q)

end

end RHTower
