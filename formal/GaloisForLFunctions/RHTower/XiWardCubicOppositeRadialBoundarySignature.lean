import GaloisForLFunctions.RHTower.XiAntipodalShiftPhaseSplittingUniversalityLaw
import GaloisForLFunctions.RHTower.XiWardCubicKreinOppositeRadialPairIncidence

/-!
# Cubic Ward opposite-radial boundary signature

W-H187 realizes every raw cubic zero-pair entry as iterated residues of one signed completed
primitive-depth current at opposite radial orientations.  This module determines the global
functional-equation signature of that current.

Multiplication by `I`, forced by the literal CCM/Krein source, changes the completed Xi conormal
reflection from a Hermitian symmetry into an anti-Hermitian one.  The opposite-radial reflected
product is therefore the negative of a norm square on the continuation boundary, even though its
iterated divisor residues are the positive W-H186 Gram entries.  Consequently the missing global
trace contraction cannot be a pointwise positive boundary estimate.  It must be an oriented
residue or polar--Gamma shorting identity retaining the signed pre-Hilbert current through
continuation.

The module also proves that on the Euler-convergent half-plane the literal pole-filled
primitive-depth trace and conormal column are exactly this signed completed-Xi column.  Thus the
signature is attached to the actual source carrier, not a fitted divisor-side model.
-/

open Complex

namespace RHTower

noncomputable section

/-- Signed completed-Xi conormal column in the `s` coordinate.  The factor `I` is the exact
CCM/Krein source phase. -/
def xiWardCubicSignedCompletedConormalColumn (s : ℂ) (r : ℝ) : ℂ :=
  I * logDeriv xi s * routePXiBaseConormalResidueFeature s r

/-- Opposite radial orientation intertwines line reflection with minus Hermitian conjugation on
the base conormal feature. -/
theorem routePXiBaseConormalResidueFeature_one_sub_star_neg
    (s : ℂ) (r : ℝ) :
    routePXiBaseConormalResidueFeature (1 - star s) (-r) =
      -star (routePXiBaseConormalResidueFeature s r) := by
  rw [Complex.star_def]
  rw [routePXiBaseConormalResidueFeature,
    routePXiBaseConormalResidueFeature]
  change (((-r : ℝ) : ℂ) * Complex.exp
      (-((1 - star s - 1 / 2) * (((-r : ℝ) : ℂ))))) =
    -((starRingEnd ℂ) ((r : ℂ) *
      Complex.exp (-((s - 1 / 2) * (r : ℂ)))))
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_sub, map_one, map_div₀,
    _root_.map_ofNat, Complex.conj_ofReal]
  rw [show
    -((1 - star s - 1 / 2) * (((-r : ℝ) : ℂ))) =
      -(star s - 1 / 2) * (r : ℂ) by
        push_cast
        ring]
  push_cast
  rw [Complex.star_def]
  ring_nf

/-- **W-H188 anti-Hermitian continuation law.**  Functional-equation reflection and radial
orientation reversal send the literal signed completed conormal column to minus its Hermitian
conjugate. -/
theorem xiWardCubicSignedCompletedConormalColumn_reflection
    (s : ℂ) (r : ℝ) :
    xiWardCubicSignedCompletedConormalColumn (1 - star s) (-r) =
      -star (xiWardCubicSignedCompletedConormalColumn s r) := by
  rw [xiWardCubicSignedCompletedConormalColumn,
    xiWardCubicSignedCompletedConormalColumn, logDeriv_xi_reciprocity]
  rw [show logDeriv xi (star s) = star (logDeriv xi s) by
    exact logDeriv_xi_conj_global s]
  rw [routePXiBaseConormalResidueFeature_one_sub_star_neg]
  rw [Complex.star_def]
  rw [map_mul, map_mul, Complex.conj_I]
  ring

/-- The reflected opposite-radial source product is a negative norm square.  This is the exact
boundary-sign obstruction hidden by positive post-residue polarization. -/
theorem xiWardCubicSignedCompletedConormalColumn_reflection_pair
    (s : ℂ) (r : ℝ) :
    xiWardCubicSignedCompletedConormalColumn (1 - star s) (-r) *
        xiWardCubicSignedCompletedConormalColumn s r =
      -((Complex.normSq
        (xiWardCubicSignedCompletedConormalColumn s r) : ℝ) : ℂ) := by
  rw [xiWardCubicSignedCompletedConormalColumn_reflection]
  calc
    -star (xiWardCubicSignedCompletedConormalColumn s r) *
        xiWardCubicSignedCompletedConormalColumn s r =
        -(star (xiWardCubicSignedCompletedConormalColumn s r) *
          xiWardCubicSignedCompletedConormalColumn s r) := by ring
    _ = -((Complex.normSq
        (xiWardCubicSignedCompletedConormalColumn s r) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      change -(star (xiWardCubicSignedCompletedConormalColumn s r) *
          xiWardCubicSignedCompletedConormalColumn s r) =
        -(star (xiWardCubicSignedCompletedConormalColumn s r) *
          xiWardCubicSignedCompletedConormalColumn s r)
      ring

/-- On the Euler-convergent half-plane, the literal pole-filled primitive-depth trace is exactly
the signed completed-Xi logarithmic derivative. -/
theorem xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_signedXi
    {u : ℂ} (hu : 0 < u.re) :
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u =
      I * logDeriv xi (u + 1) := by
  have huNegOne : -1 < u.re := by linarith
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  have hs : 1 < (u + 1).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hzeta : riemannZeta (u + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  let z : ℂ := criticalMellinToCenteredXi u
  have hcoord : 1 / 2 + z * I = u + 1 :=
    criticalMellinToCenteredXi_mul_I u
  have hspos : 0 < (1 / 2 + z * I).re := by
    rw [hcoord]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    rw [hcoord]
    intro h
    apply hu0
    linear_combination h
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 (by
      rwa [hcoord])
  calc
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u =
        xiRelativeResolventTrace z :=
      xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_xiRelativeResolventTrace
        huNegOne hu0 hzeta
    _ = logDeriv XiC z :=
      (logDeriv_XiC_eq_relativeResolventTrace hXi).symm
    _ = I * logDeriv xi (u + 1) := by
      rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]

/-- Exact source identification before divisor restriction: the W-H187 literal CCM/Krein column
is the signed completed-Xi conormal column throughout its Euler-convergent domain. -/
theorem frankensteinKreinCCMRoutePSignedConormalColumn_eq_signedXi
    {u : ℂ} (hu : 0 < u.re) (r : ℝ) :
    frankensteinKreinCCMRoutePSignedConormalColumn u r =
      xiWardCubicSignedCompletedConormalColumn (u + 1) r := by
  rw [frankensteinKreinCCMRoutePSignedConormalColumn,
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_signedXi hu,
    xiWardCubicSignedCompletedConormalColumn]

/-- The complete opposite-radial quadratic current is the product of two signed completed-Xi
columns on the Euler-convergent source chamber. -/
theorem xiWardCubicKreinOppositeRadialPairCurrent_eq_signedXi
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (r : ℝ) :
    xiWardCubicKreinOppositeRadialPairCurrent u v r =
      xiWardCubicSignedCompletedConormalColumn (u + 1) (-r) *
        xiWardCubicSignedCompletedConormalColumn (v + 1) r := by
  rw [xiWardCubicKreinOppositeRadialPairCurrent,
    frankensteinKreinCCMRoutePSignedConormalColumn_eq_signedXi hu,
    frankensteinKreinCCMRoutePSignedConormalColumn_eq_signedXi hv]

end

end RHTower
