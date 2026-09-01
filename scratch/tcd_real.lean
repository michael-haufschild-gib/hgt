import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveDrift

open Real

namespace HTGeometry

noncomputable section

abbrev ModularThetaSourcePositiveRealPolynomial :=
  MvPolynomial ModularThetaSourcePositiveState ℝ

def modularThetaSourcePositiveRealGap : ModularThetaSourcePositiveRealPolynomial :=
  MvPolynomial.C 16 * MvPolynomial.X .Q + MvPolynomial.C 6 -
    MvPolynomial.C 6 * MvPolynomial.X .B ^ 2

def modularThetaSourcePositiveRealVectorField :
    ModularThetaSourcePositiveState → ModularThetaSourcePositiveRealPolynomial
  | .U => MvPolynomial.C (9 / 2 : ℝ) +
      MvPolynomial.C 4 * MvPolynomial.X .Q +
      MvPolynomial.C (3 / 2 : ℝ) * MvPolynomial.X .B ^ 2 +
      MvPolynomial.C 2 * MvPolynomial.X .B * MvPolynomial.X .U
  | .B => MvPolynomial.C (1 / 2 : ℝ) +
      MvPolynomial.C 4 * MvPolynomial.X .Q -
      MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X .B ^ 2
  | .Q => MvPolynomial.C (3 / 4 : ℝ) * MvPolynomial.X .B *
        (MvPolynomial.C (1 / 2 : ℝ) +
          MvPolynomial.C 4 * MvPolynomial.X .Q -
          MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X .B ^ 2) -
      MvPolynomial.C (1 / 8 : ℝ) * modularThetaSourcePositiveRealGap *
        (MvPolynomial.X .U + MvPolynomial.X .B)

def modularThetaSourcePositiveRealLie
    (P : ModularThetaSourcePositiveRealPolynomial) :
    ModularThetaSourcePositiveRealPolynomial :=
  ∑ i, MvPolynomial.pderiv i P * modularThetaSourcePositiveRealVectorField i

def modularThetaSourcePositiveRealNormalizedLie
    (P : ModularThetaSourcePositiveRealPolynomial) :
    ModularThetaSourcePositiveRealPolynomial :=
  modularThetaSourcePositiveRealLie P +
    MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X .B * P

def modularThetaSourcePositiveRealNormalizedSourceJet :
    ℕ → ModularThetaSourcePositiveRealPolynomial
  | 0 => MvPolynomial.X .Q
  | n + 1 => modularThetaSourcePositiveRealNormalizedLie
      (modularThetaSourcePositiveRealNormalizedSourceJet n)

def modularThetaSourcePositiveRealReflectedEighthPolynomial :
    ModularThetaSourcePositiveRealPolynomial :=
  let f := modularThetaSourcePositiveRealNormalizedSourceJet
  let p0 := f 0 ^ 2
  let p2 := MvPolynomial.C 2 * (f 0 * f 2 - f 1 ^ 2)
  let p4 := MvPolynomial.C 2 * f 0 * f 4 - MvPolynomial.C 8 * f 1 * f 3 +
    MvPolynomial.C 6 * f 2 ^ 2
  let p6 := MvPolynomial.C 2 * f 0 * f 6 - MvPolynomial.C 12 * f 1 * f 5 +
    MvPolynomial.C 30 * f 2 * f 4 - MvPolynomial.C 20 * f 3 ^ 2
  let p8 := MvPolynomial.C 2 * f 0 * f 8 - MvPolynomial.C 16 * f 1 * f 7 +
    MvPolynomial.C 56 * f 2 * f 6 - MvPolynomial.C 112 * f 3 * f 5 +
    MvPolynomial.C 70 * f 4 ^ 2
  p0 * p4 * p8 - p0 * p6 ^ 2 - p2 ^ 2 * p8 +
    MvPolynomial.C 2 * p2 * p4 * p6 - p4 ^ 3

def modularThetaSourcePositiveRealProjectiveDriftPolynomial :
    ModularThetaSourcePositiveRealPolynomial :=
  MvPolynomial.X .Q * modularThetaSourcePositiveRealLie
      modularThetaSourcePositiveRealReflectedEighthPolynomial -
    MvPolynomial.C 6 * modularThetaSourcePositiveRealReflectedEighthPolynomial *
      modularThetaSourcePositiveRealVectorField .Q

def modularThetaSourcePositivePhysicalConeState (R z v : ℝ) :
    ModularThetaSourcePositiveState → ℝ
  | .U => R * v
  | .B => R * (z - v) / 3
  | .Q => R ^ 2 * (1 - z ^ 2) / 16 - 3 / 8 +
      R ^ 2 * (z - v) ^ 2 / 24

def modularThetaSourcePositivePhysicalConeProjectiveDrift
    (R z v : ℝ) : ℝ :=
  MvPolynomial.eval (modularThetaSourcePositivePhysicalConeState R z v)
    modularThetaSourcePositiveRealProjectiveDriftPolynomial

def modularThetaSourcePositivePhysicalConeJet (R z v : ℝ) (n : ℕ) : ℝ :=
  MvPolynomial.eval (modularThetaSourcePositivePhysicalConeState R z v)
    (modularThetaSourcePositiveRealNormalizedSourceJet n)

def modularThetaSourcePositivePhysicalConeShiftVariation (R z v : ℝ) : ℝ :=
  HilbertMetric.signedEvenHankelThreeShiftVariation
    (modularThetaSourcePositivePhysicalConeJet R z v)

def modularThetaSourcePositivePhysicalConeDet (R z v : ℝ) : ℝ :=
  MvPolynomial.eval (modularThetaSourcePositivePhysicalConeState R z v)
    modularThetaSourcePositiveRealReflectedEighthPolynomial

end

end HTGeometry

namespace HTGeometry

set_option maxHeartbeats 2000000 in
theorem modularThetaSourcePositivePhysicalConeShiftVariation_lowerFace_pos_of_singular
    {R z : ℝ} (hR : 0 < R) (hz : 0 < z) (hzupper : z < 3 / 10)
    (hscale : 191 / 10 + (37 / 5 : ℝ) * z ^ 2 < R ^ 2)
    (hzero : modularThetaSourcePositivePhysicalConeDet R z
      ((13 / 32 + z ^ 2 / 32 : ℝ) * z) = 0) :
    0 < modularThetaSourcePositivePhysicalConeShiftVariation R z
      ((13 / 32 + z ^ 2 / 32 : ℝ) * z) := by
  unfold modularThetaSourcePositivePhysicalConeShiftVariation
    HilbertMetric.signedEvenHankelThreeShiftVariation
    HilbertMetric.signedEvenHankelThreeFirstVariation
    HilbertMetric.reflectedProductZeroJetShift
    HilbertMetric.reflectedProductSecondJetShift
    HilbertMetric.reflectedProductFourthJetShift
    HilbertMetric.reflectedProductSixthJetShift
    HilbertMetric.reflectedProductEighthJetShift
    HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet
    HilbertMetric.reflectedProductSixthJet
    HilbertMetric.reflectedProductEighthJet
    modularThetaSourcePositivePhysicalConeJet
  unfold modularThetaSourcePositivePhysicalConeDet at hzero
  simp (config := { maxSteps := 2000000 }) [
    modularThetaSourcePositiveRealReflectedEighthPolynomial,
    modularThetaSourcePositiveRealNormalizedSourceJet,
    modularThetaSourcePositiveRealNormalizedLie,
    modularThetaSourcePositiveRealLie,
    modularThetaSourcePositivePhysicalConeState,
    modularThetaSourcePositiveRealVectorField, modularThetaSourcePositiveRealGap] at hzero ⊢
  ring_nf
  have hzsq : z ^ 2 < (9 / 100 : ℝ) := by nlinarith
  have hz4 : z ^ 4 < (9 / 100 : ℝ) ^ 2 := by nlinarith [sq_nonneg (z ^ 2)]
  have hz6 : z ^ 6 < (9 / 100 : ℝ) ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hz) (sub_pos.mpr hz4)]
  nlinarith [sq_nonneg (R ^ 2 - (191 / 10 + (37 / 5 : ℝ) * z ^ 2))]

end HTGeometry
