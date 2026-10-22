import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEKGChiralStressAngularMixing

/-!
# Laurent-graded theta-Eisenstein stress channels

For normalized Eisenstein constant term

`E(s;u) = exp(su) + phi(s) exp((1-s)u) + exponentially decaying modes`,

a theta divisor makes `phi` singular at `s=rho/2`. Pole-residue jets carry
outgoing weight `1-s`; normalized finite part retains incoming coefficient
`exp(su)`. Quadratic chiral stress therefore has three distinct power weights:

`2-rho` from residue squared, `1` from residue--finite mixing, and `rho`
from finite part squared.

The three corresponding horizon Casimirs behave differently. Residue-square
Casimir is nonreal at every Xi divisor, mixed Casimir is zero, and finite-square
Casimir is real exactly on critical line. Hence RH-sensitive source is canonical
finite-part associated-graded channel, not physical pole residue.

**[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Outgoing cusp weight carried by Eisenstein pole-residue jets. -/
def d4ThetaHawkingEisensteinLaurentResidueWeight (z : ℂ) : ℂ :=
  1 - d4ThetaTeukolskyLinearCuspWeight z

/-- Quadratic power weight of two outgoing residue factors. -/
def d4ThetaHawkingEisensteinLaurentResidueSquareWeight (z : ℂ) : ℂ :=
  2 * d4ThetaHawkingEisensteinLaurentResidueWeight z

/-- Quadratic power weight of one residue and one finite incoming factor. -/
def d4ThetaHawkingEisensteinLaurentMixedWeight (z : ℂ) : ℂ :=
  d4ThetaHawkingEisensteinLaurentResidueWeight z +
    d4ThetaTeukolskyLinearCuspWeight z

/-- Quadratic power weight of two normalized finite-part incoming factors. -/
def d4ThetaHawkingEisensteinLaurentFiniteSquareWeight (z : ℂ) : ℂ :=
  d4ThetaTeukolskyQuadraticChiralCuspWeight z

/-- Hyperbolic cusp Casimir attached to a power weight. -/
def d4ThetaHawkingCuspCasimir (weight : ℂ) : ℂ :=
  weight * (1 - weight)

/-- Chiral stress coefficient of squared outgoing residue term. -/
def d4ThetaHawkingEisensteinLaurentResidueStressCoefficient (z : ℂ) : ℂ :=
  d4ThetaHawkingEisensteinLaurentResidueWeight z ^ (2 : ℕ) / 2

/-- Chiral stress coefficient of residue--finite cross term, excluding residue amplitude. -/
def d4ThetaHawkingEisensteinLaurentMixedStressCoefficient (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z *
    d4ThetaHawkingEisensteinLaurentResidueWeight z

theorem d4ThetaHawkingEisensteinLaurentResidueSquareWeight_eq (z : ℂ) :
    d4ThetaHawkingEisensteinLaurentResidueSquareWeight z =
      2 - d4ThetaTeukolskyRho z := by
  rw [d4ThetaHawkingEisensteinLaurentResidueSquareWeight,
    d4ThetaHawkingEisensteinLaurentResidueWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho]
  ring

theorem d4ThetaHawkingEisensteinLaurentMixedWeight_eq_one (z : ℂ) :
    d4ThetaHawkingEisensteinLaurentMixedWeight z = 1 := by
  unfold d4ThetaHawkingEisensteinLaurentMixedWeight
    d4ThetaHawkingEisensteinLaurentResidueWeight
  ring

theorem d4ThetaHawkingEisensteinLaurentFiniteSquareWeight_eq (z : ℂ) :
    d4ThetaHawkingEisensteinLaurentFiniteSquareWeight z =
      d4ThetaTeukolskyRho z := by
  exact d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho z

/-- Theta shadow exchanges residue-square and finite-square weights. -/
theorem d4ThetaHawkingEisensteinLaurentResidueSquareWeight_shadow (z : ℂ) :
    d4ThetaHawkingEisensteinLaurentResidueSquareWeight z =
      d4ThetaHawkingEisensteinLaurentFiniteSquareWeight
        (thetaCuspHawkingOpticalCuspShadow z) := by
  rw [d4ThetaHawkingEisensteinLaurentResidueSquareWeight_eq,
    d4ThetaHawkingEisensteinLaurentFiniteSquareWeight_eq,
    d4ThetaTeukolskyRho_shadow]

theorem d4ThetaHawkingEisensteinLaurentFiniteSquareWeight_shadow (z : ℂ) :
    d4ThetaHawkingEisensteinLaurentFiniteSquareWeight z =
      d4ThetaHawkingEisensteinLaurentResidueSquareWeight
        (thetaCuspHawkingOpticalCuspShadow z) := by
  rw [d4ThetaHawkingEisensteinLaurentFiniteSquareWeight_eq,
    d4ThetaHawkingEisensteinLaurentResidueSquareWeight_eq,
    d4ThetaTeukolskyRho_shadow]
  ring

/-- At Xi divisor, squared residue stress has coefficient `(2-rho)^(2 : ℕ)/8`. -/
theorem d4ThetaHawkingEisensteinLaurentResidueStressCoefficient_xi_eq
    (q : XiZeroCopy) :
    d4ThetaHawkingEisensteinLaurentResidueStressCoefficient
        (xiSpectralPoint q) =
      (2 - (q.1 : ℂ)) ^ (2 : ℕ) / 8 := by
  rw [d4ThetaHawkingEisensteinLaurentResidueStressCoefficient,
    d4ThetaHawkingEisensteinLaurentResidueWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  ring

/-- Mixed Laurent layer has coefficient `rho(2-rho)/4`, before residue amplitude. -/
theorem d4ThetaHawkingEisensteinLaurentMixedStressCoefficient_xi_eq
    (q : XiZeroCopy) :
    d4ThetaHawkingEisensteinLaurentMixedStressCoefficient
        (xiSpectralPoint q) =
      (q.1 : ℂ) * (2 - (q.1 : ℂ)) / 4 := by
  rw [d4ThetaHawkingEisensteinLaurentMixedStressCoefficient,
    d4ThetaHawkingEisensteinLaurentResidueWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  ring

private lemma d4XiRho_ne_one_laurent (q : XiZeroCopy) : (q.1 : ℂ) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  norm_num at hre
  linarith

/-- Three quadratic Laurent weights are pairwise distinct on actual Xi divisor. -/
theorem d4ThetaHawkingEisensteinLaurentQuadraticWeights_pairwise_ne
    (q : XiZeroCopy) :
    d4ThetaHawkingEisensteinLaurentResidueSquareWeight
          (xiSpectralPoint q) ≠
        d4ThetaHawkingEisensteinLaurentMixedWeight (xiSpectralPoint q) ∧
      d4ThetaHawkingEisensteinLaurentMixedWeight (xiSpectralPoint q) ≠
        d4ThetaHawkingEisensteinLaurentFiniteSquareWeight
          (xiSpectralPoint q) ∧
      d4ThetaHawkingEisensteinLaurentResidueSquareWeight
          (xiSpectralPoint q) ≠
        d4ThetaHawkingEisensteinLaurentFiniteSquareWeight
          (xiSpectralPoint q) := by
  rw [d4ThetaHawkingEisensteinLaurentResidueSquareWeight_eq,
    d4ThetaHawkingEisensteinLaurentMixedWeight_eq_one,
    d4ThetaHawkingEisensteinLaurentFiniteSquareWeight_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  have hne := d4XiRho_ne_one_laurent q
  constructor
  · intro h
    apply hne
    linear_combination -h
  constructor
  · exact hne.symm
  · intro h
    apply hne
    have htwo : (2 : ℂ) * ((q.1 : ℂ) - 1) = 0 := by
      linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

theorem d4ThetaHawkingEisensteinLaurentResidueSquareCasimir_eq (z : ℂ) :
    d4ThetaHawkingCuspCasimir
        (d4ThetaHawkingEisensteinLaurentResidueSquareWeight z) =
      (2 - d4ThetaTeukolskyRho z) * (d4ThetaTeukolskyRho z - 1) := by
  rw [d4ThetaHawkingCuspCasimir,
    d4ThetaHawkingEisensteinLaurentResidueSquareWeight_eq]
  ring

theorem d4ThetaHawkingEisensteinLaurentMixedCasimir_eq_zero (z : ℂ) :
    d4ThetaHawkingCuspCasimir
        (d4ThetaHawkingEisensteinLaurentMixedWeight z) = 0 := by
  rw [d4ThetaHawkingEisensteinLaurentMixedWeight_eq_one]
  simp [d4ThetaHawkingCuspCasimir]

theorem d4ThetaHawkingEisensteinLaurentFiniteSquareCasimir_eq (z : ℂ) :
    d4ThetaHawkingCuspCasimir
        (d4ThetaHawkingEisensteinLaurentFiniteSquareWeight z) =
      d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z := by
  rw [d4ThetaHawkingCuspCasimir,
    d4ThetaHawkingEisensteinLaurentFiniteSquareWeight]
  change d4ThetaTeukolskyQuadraticChiralAngularEigenvalue z =
    d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z
  rw [d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq]

/-- Physical pole-residue square has nonreal Casimir at every Xi divisor, including RH ones. -/
theorem d4ThetaHawkingEisensteinLaurentResidueSquareCasimir_xi_im_ne_zero
    (q : XiZeroCopy) :
    (d4ThetaHawkingCuspCasimir
      (d4ThetaHawkingEisensteinLaurentResidueSquareWeight
        (xiSpectralPoint q))).im ≠ 0 := by
  rw [d4ThetaHawkingEisensteinLaurentResidueSquareCasimir_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  have him :
      (((2 : ℂ) - (q.1 : ℂ)) * ((q.1 : ℂ) - 1)).im =
        (q.1 : ℂ).im * (3 - 2 * (q.1 : ℂ).re) := by
    simp [Complex.mul_im]
    ring
  rw [him]
  apply mul_ne_zero (xi_divisor_support_im_ne_zero q.1)
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  exact ne_of_gt (by linarith [hstrip.2])

/-- Finite-square associated-graded channel is physical exactly on critical line. -/
theorem d4ThetaHawkingEisensteinLaurentFiniteSquareCasimir_xi_im_eq_zero_iff
    (q : XiZeroCopy) :
    (d4ThetaHawkingCuspCasimir
      (d4ThetaHawkingEisensteinLaurentFiniteSquareWeight
        (xiSpectralPoint q))).im = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [d4ThetaHawkingEisensteinLaurentFiniteSquareCasimir_eq]
  exact d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q

/-- Exact divisor-wise trichotomy: outgoing pole layer is nonphysical, mixed layer is
zero-Casimir, and normalized finite-square layer detects critical line. -/
theorem d4ThetaHawkingEisensteinLaurentCasimir_trichotomy
    (q : XiZeroCopy) :
    (d4ThetaHawkingCuspCasimir
      (d4ThetaHawkingEisensteinLaurentResidueSquareWeight
        (xiSpectralPoint q))).im ≠ 0 ∧
      d4ThetaHawkingCuspCasimir
        (d4ThetaHawkingEisensteinLaurentMixedWeight
          (xiSpectralPoint q)) = 0 ∧
      ((d4ThetaHawkingCuspCasimir
        (d4ThetaHawkingEisensteinLaurentFiniteSquareWeight
          (xiSpectralPoint q))).im = 0 ↔
        (xiSpectralPoint q).im = 0) := by
  exact ⟨
    d4ThetaHawkingEisensteinLaurentResidueSquareCasimir_xi_im_ne_zero q,
    d4ThetaHawkingEisensteinLaurentMixedCasimir_eq_zero _,
    d4ThetaHawkingEisensteinLaurentFiniteSquareCasimir_xi_im_eq_zero_iff q⟩

end

end RHTower
