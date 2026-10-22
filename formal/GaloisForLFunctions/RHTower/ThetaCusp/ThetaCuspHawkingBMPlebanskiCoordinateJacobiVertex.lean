import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullPoincareDerivativePullback

/-!
# Coordinate-space Plebanski Jacobi vertex

Chowdhury--Doran--Lipstein--Monteiro--Nagy--Singh Eq. (63) gives the self-dual AdS
interaction before any Poincare plane-wave specialization.  For scaled legs `f,g`, it is

`{{f,g}}_* = (f_uu g_ww + g_uu f_ww)/2 - f_uw g_uw`

`  + 1/(u-v) * (f_uw g_w + f_w g_uw - f_ww g_u - f_u g_ww)`.

This module implements that literal symmetric bidifferential operator on arbitrary light-cone
two-jets.  On plane-wave eigenjets with derivatives `partial_u = i p`, `partial_w = i h`, it
proves the exact factorization

`{{f,g}}_* = X(p,h;q,k) * (X(p,h;q,k)-2i inverseUV (h-k))/2 * f*g`,

which is precisely the existing momentum-space self-dual AdS vertex.  Hence the fixed-momentum
formula is now a theorem-level specialization of a coordinate-space operator, not an assumption
about BM separated modes.

The remaining chart burden is exact and finite: pull `uu`, `uw`, and `ww` through the rapidity
inverse Jacobian constructed in the preceding module.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [COORDINATE JACOBI VERTEX]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Value and the five light-cone derivatives used by the Plebanski Jacobi double bracket. -/
structure D4PlebanskiLightConeTwoJet where
  value : ℂ
  u : ℂ
  w : ℂ
  uu : ℂ
  uw : ℂ
  ww : ℂ

/-- Literal coordinate-space deformed Plebanski double bracket, Eq. (63). -/
def ads4PlebanskiJacobiDoubleBracketOnTwoJets
    (inverseUV : ℂ)
    (P Q : D4PlebanskiLightConeTwoJet) : ℂ :=
  (1 / 2 : ℂ) * (P.uu * Q.ww + Q.uu * P.ww) - P.uw * Q.uw +
    inverseUV *
      (P.uw * Q.w + P.w * Q.uw - (P.ww * Q.u + P.u * Q.ww))

/-- The coordinate-space gravity bracket is symmetric in its two positive-helicity legs. -/
theorem ads4PlebanskiJacobiDoubleBracketOnTwoJets_exchange
    (inverseUV : ℂ) (P Q : D4PlebanskiLightConeTwoJet) :
    ads4PlebanskiJacobiDoubleBracketOnTwoJets inverseUV Q P =
      ads4PlebanskiJacobiDoubleBracketOnTwoJets inverseUV P Q := by
  simp [ads4PlebanskiJacobiDoubleBracketOnTwoJets]
  ring

/-- Poincare plane-wave light-cone jet with `partial_u = i p` and `partial_w = i h`. -/
def ads4PlebanskiPlaneWaveLightConeTwoJet
    (p h amplitude : ℂ) : D4PlebanskiLightConeTwoJet where
  value := amplitude
  u := Complex.I * p * amplitude
  w := Complex.I * h * amplitude
  uu := -(p ^ (2 : ℕ)) * amplitude
  uw := -(p * h) * amplitude
  ww := -(h ^ (2 : ℕ)) * amplitude

/-- Flat Hessian polarization on two plane-wave jets is one half the square of the kinematic
bracket. -/
theorem ads4PlebanskiJacobiDoubleBracket_flat_planeWave
    (p h q k P Q : ℂ) :
    (1 / 2 : ℂ) *
          ((ads4PlebanskiPlaneWaveLightConeTwoJet p h P).uu *
              (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).ww +
            (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).uu *
              (ads4PlebanskiPlaneWaveLightConeTwoJet p h P).ww) -
        (ads4PlebanskiPlaneWaveLightConeTwoJet p h P).uw *
          (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).uw =
      (1 / 2 : ℂ) * ads4SelfDualKinematicBracket p h q k ^ (2 : ℕ) * P * Q := by
  simp [ads4PlebanskiPlaneWaveLightConeTwoJet, ads4SelfDualKinematicBracket]
  ring

/-- The curvature part of the coordinate Jacobi bracket factors by the same kinematic bracket
and the transverse-charge difference. -/
theorem ads4PlebanskiJacobiDoubleBracket_curvature_planeWave
    (inverseUV p h q k P Q : ℂ) :
    inverseUV *
        ((ads4PlebanskiPlaneWaveLightConeTwoJet p h P).uw *
            (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).w +
          (ads4PlebanskiPlaneWaveLightConeTwoJet p h P).w *
            (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).uw -
          ((ads4PlebanskiPlaneWaveLightConeTwoJet p h P).ww *
              (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).u +
            (ads4PlebanskiPlaneWaveLightConeTwoJet p h P).u *
              (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q).ww)) =
      -Complex.I * inverseUV * ads4SelfDualKinematicBracket p h q k *
        (h - k) * P * Q := by
  simp [ads4PlebanskiPlaneWaveLightConeTwoJet, ads4SelfDualKinematicBracket]
  ring

/-- Exact compatibility theorem: the coordinate-space Eq. (63) bracket specializes to the
corpus's curvature-corrected self-dual AdS plane-wave vertex. -/
theorem ads4PlebanskiJacobiDoubleBracket_planeWave_eq_selfDualVertex
    (inverseUV p h q k P Q : ℂ) :
    ads4PlebanskiJacobiDoubleBracketOnTwoJets inverseUV
        (ads4PlebanskiPlaneWaveLightConeTwoJet p h P)
        (ads4PlebanskiPlaneWaveLightConeTwoJet q k Q) =
      ads4SelfDualPlaneWaveVertex (2 * Complex.I * inverseUV) p h q k * P * Q := by
  simp [ads4PlebanskiJacobiDoubleBracketOnTwoJets,
    ads4PlebanskiPlaneWaveLightConeTwoJet,
    ads4SelfDualPlaneWaveVertex, ads4SelfDualKinematicBracket]
  ring

/-- Diagonal form of the Jacobi double bracket. -/
theorem ads4PlebanskiJacobiDoubleBracketOnTwoJets_self
    (inverseUV : ℂ) (P : D4PlebanskiLightConeTwoJet) :
    ads4PlebanskiJacobiDoubleBracketOnTwoJets inverseUV P P =
      P.uu * P.ww - P.uw ^ (2 : ℕ) +
        2 * inverseUV * (P.uw * P.w - P.ww * P.u) := by
  simp [ads4PlebanskiJacobiDoubleBracketOnTwoJets]
  ring

end

end RHTower
