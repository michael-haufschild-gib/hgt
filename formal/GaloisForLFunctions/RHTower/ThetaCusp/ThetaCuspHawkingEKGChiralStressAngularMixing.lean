import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyTiltedAngularLeakage

/-!
# EKG chiral cusp stress and forced Teukolsky angular mixing

Write the hyperbolic cusp metric as `du² + exp(-2u) dx²`. The constant term of
an Eisenstein mode of weight `s` is `Y_s = exp(su)`. In the orthonormal chiral
direction `m = (e_u + i e_x)/sqrt(2)`,

`m Y_s = (s/sqrt(2)) Y_s`.

For Klein--Gordon stress, the trace and mass terms vanish in the null component,
so

`T_mm = (m Y_s)² = (s²/2) exp(2su)`.

At a theta scattering pole `s=rho/2`, pole residue is outgoing and has weight
`1-s`. Incoming term above instead survives canonically in renormalized finite
part. Its chiral square has weight `rho` and coefficient `rho²/8`, nonzero at
every nontrivial Xi divisor. Laurent-layer classification is formalized
separately; this module isolates finite-part incoming source.

For an off-line FE pair, select the member with real part below `1/2`. Its
hyperbolic cusp norm density is `exp(-(1-2 re(rho))u)`, hence integrable. The
symmetric-horizon residual identity then forces this nonzero chiral source out
of its one-sector Teukolsky eigenchannel.

This proves the EKG angular principal coefficient and tilted-sector leakage.
It does not compute the radial Teukolsky projection or exclude cancellation by
other contributions of the same perturbative bidegree.

**[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set MeasureTheory
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Chiral `T_mm` coefficient of squared finite-part incoming cusp term. -/
def d4ThetaHawkingEKGChiralCuspStressCoefficient (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z ^ (2 : ℕ) / 2

/-- At a divisor, the chiral stress coefficient is `rho²/8`. -/
theorem d4ThetaHawkingEKGChiralCuspStressCoefficient_xi_eq (q : XiZeroCopy) :
    d4ThetaHawkingEKGChiralCuspStressCoefficient (xiSpectralPoint q) =
      (q.1 : ℂ) ^ (2 : ℕ) / 8 := by
  rw [d4ThetaHawkingEKGChiralCuspStressCoefficient,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  ring

/-- Every nontrivial Xi divisor has a nonzero doubled EKG chiral stress
coefficient. -/
theorem d4ThetaHawkingEKGChiralCuspStressCoefficient_xi_ne_zero
    (q : XiZeroCopy) :
    d4ThetaHawkingEKGChiralCuspStressCoefficient (xiSpectralPoint q) ≠ 0 := by
  rw [d4ThetaHawkingEKGChiralCuspStressCoefficient_xi_eq]
  apply div_ne_zero (pow_ne_zero 2 ?_) (by norm_num)
  intro hzero
  have hre := congrArg Complex.re hzero
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  simp at hre
  linarith

/-- FE orientation whose doubled cusp source decays in hyperbolic `L²`. -/
def d4ThetaHawkingEKGChiralCuspL2Copy (q : XiZeroCopy) : XiZeroCopy :=
  if (q.1 : ℂ).re < 1 / 2 then q else xiZeroCopyReflectEquiv q

/-- Every tilted FE orbit has a unique selected side strictly below the cusp
`L²` threshold. -/
theorem d4ThetaHawkingEKGChiralCuspL2Copy_re_lt_half
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ((d4ThetaHawkingEKGChiralCuspL2Copy q).1 : ℂ).re < 1 / 2 := by
  rw [d4ThetaHawkingEKGChiralCuspL2Copy]
  split_ifs with hleft
  · exact hleft
  · rw [xiZeroCopyReflectEquiv_rho]
    simp only [sub_re, one_re]
    have hge : 1 / 2 ≤ (q.1 : ℂ).re := le_of_not_gt hleft
    have hgt : 1 / 2 < (q.1 : ℂ).re := lt_of_le_of_ne hge htilt.symm
    linarith

/-- Positive exponential decay rate of the selected doubled stress norm. -/
def d4ThetaHawkingEKGChiralCuspL2DecayRate (q : XiZeroCopy) : ℝ :=
  1 - 2 * ((d4ThetaHawkingEKGChiralCuspL2Copy q).1 : ℂ).re

theorem d4ThetaHawkingEKGChiralCuspL2DecayRate_pos
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4ThetaHawkingEKGChiralCuspL2DecayRate q := by
  rw [d4ThetaHawkingEKGChiralCuspL2DecayRate]
  have h := d4ThetaHawkingEKGChiralCuspL2Copy_re_lt_half q htilt
  linarith

/-- Hyperbolic cusp norm density of the selected doubled principal source. -/
def d4ThetaHawkingEKGChiralCuspL2Density (q : XiZeroCopy) (u : ℝ) : ℝ :=
  Real.exp (-(d4ThetaHawkingEKGChiralCuspL2DecayRate q * u))

/-- Off-line selected chiral stress has integrable hyperbolic cusp norm. -/
theorem integrableOn_d4ThetaHawkingEKGChiralCuspL2Density
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    IntegrableOn (d4ThetaHawkingEKGChiralCuspL2Density q) (Ioi (0 : ℝ)) := by
  have hrate := d4ThetaHawkingEKGChiralCuspL2DecayRate_pos q htilt
  change IntegrableOn
    (fun u : ℝ => Real.exp
      (-(d4ThetaHawkingEKGChiralCuspL2DecayRate q * u))) (Ioi (0 : ℝ))
  simpa only [neg_mul] using
    (integrableOn_exp_mul_Ioi
      (a := -d4ThetaHawkingEKGChiralCuspL2DecayRate q)
      (neg_lt_zero.mpr hrate) 0)

/-- The selected copy remains tilted in centered Teukolsky momentum. -/
theorem d4ThetaHawkingEKGChiralCuspL2Copy_spectralPoint_im_ne_zero
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (xiSpectralPoint (d4ThetaHawkingEKGChiralCuspL2Copy q)).im ≠ 0 := by
  have hleft := d4ThetaHawkingEKGChiralCuspL2Copy_re_lt_half q htilt
  rw [xiSpectralPoint_im_eq]
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Principal chiral stress vector, including quadratic field amplitude. -/
def d4ThetaHawkingEKGChiralCuspStressVector
    (amplitude : ℂ) (profile : H) (q : XiZeroCopy) : H :=
  (amplitude ^ (2 : ℕ) *
    d4ThetaHawkingEKGChiralCuspStressCoefficient
      (xiSpectralPoint (d4ThetaHawkingEKGChiralCuspL2Copy q))) • profile

theorem d4ThetaHawkingEKGChiralCuspStressVector_ne_zero
    (amplitude : ℂ) (profile : H) (q : XiZeroCopy)
    (ha : amplitude ≠ 0) (hprofile : profile ≠ 0) :
    d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q ≠ 0 := by
  unfold d4ThetaHawkingEKGChiralCuspStressVector
  apply smul_ne_zero
  · exact mul_ne_zero (pow_ne_zero 2 ha)
      (d4ThetaHawkingEKGChiralCuspStressCoefficient_xi_ne_zero _)
  · exact hprofile

/-- Source-specific mixing theorem: every nonzero off-line EKG chiral cusp
stress has nonzero residual against a symmetric horizon angular operator. -/
theorem d4ThetaHawkingEKGChiralCuspStress_tilted_forces_angularLeakage
    (A : H → H) (amplitude : ℂ) (profile : H) (q : XiZeroCopy)
    (hsa :
      ⟪d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q,
        A (d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q)⟫_ℂ =
      ⟪A (d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q),
        d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q⟫_ℂ)
    (ha : amplitude ≠ 0) (hprofile : profile ≠ 0)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    A (d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q) -
        d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
          (xiSpectralPoint (d4ThetaHawkingEKGChiralCuspL2Copy q)) •
            d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q ≠ 0 := by
  exact d4ThetaTeukolsky_tiltedAngularSource_forces_leakage
    A (d4ThetaHawkingEKGChiralCuspStressVector amplitude profile q)
    (d4ThetaHawkingEKGChiralCuspL2Copy q) hsa
    (d4ThetaHawkingEKGChiralCuspStressVector_ne_zero
      amplitude profile q ha hprofile)
    (d4ThetaHawkingEKGChiralCuspL2Copy_spectralPoint_im_ne_zero q htilt)

end

end RHTower
