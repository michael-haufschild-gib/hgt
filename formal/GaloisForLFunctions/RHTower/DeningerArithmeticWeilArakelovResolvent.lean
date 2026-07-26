import GaloisForLFunctions.RHTower.DeningerArithmeticCochainComplex

/-!
# Source resolvent for Weil--Arakelov specializations

Flach--Morin identify arithmetic cohomology at weight `n` with the mapping fiber of
`Theta - n` on Deninger's dynamical cohomology.  The source entire quotient admits an explicit
Bezout inverse for every centered weight `1/2 + I * alpha` away from the completed Xi divisor.
Thus its middle Weil--Arakelov specialization is acyclic off the source-defined spectrum.

No zero enumeration, positivity assumption, or Riemann-hypothesis premise occurs here.
-/

open Complex

namespace RHTower

noncomputable section

/--
Explicit inverse class for `Theta - (1/2 + I * alpha)` away from the completed Xi divisor.
The factor `-I` converts the coordinate resolvent into the Frobenius-coordinate resolvent.
-/
def deningerEntireThetaCenteredResolvent (alpha : ℂ) :
    DeningerEntireH1 :=
  algebraMap ℂ DeningerEntireH1 (-Complex.I) *
    deningerEntireCoordinateResolvent alpha

/-- Frobenius shift factors through the centered coordinate shift. -/
theorem deningerEntireThetaClass_sub_centered
    (alpha : ℂ) :
    deningerEntireThetaClass -
        algebraMap ℂ DeningerEntireH1
          (1 / 2 + Complex.I * alpha) =
      algebraMap ℂ DeningerEntireH1 Complex.I *
        (deningerEntireCoordinateClass -
          algebraMap ℂ DeningerEntireH1 alpha) := by
  rw [deningerEntireThetaClass_eq,
    (algebraMap ℂ DeningerEntireH1).map_add,
    (algebraMap ℂ DeningerEntireH1).map_mul, mul_sub]
  abel

/-- The explicit centered Frobenius resolvent is a right inverse off the Xi divisor. -/
theorem deningerEntireThetaCenteredResolvent_mul
    {alpha : ℂ} (hXi : XiC alpha ≠ 0) :
    (deningerEntireThetaClass -
        algebraMap ℂ DeningerEntireH1
          (1 / 2 + Complex.I * alpha)) *
      deningerEntireThetaCenteredResolvent alpha = 1 := by
  rw [deningerEntireThetaCenteredResolvent,
    deningerEntireThetaClass_sub_centered]
  have hcoord :=
    deningerEntireCoordinateResolvent_mul hXi
  calc
    (algebraMap ℂ DeningerEntireH1 Complex.I *
          (deningerEntireCoordinateClass -
            algebraMap ℂ DeningerEntireH1 alpha)) *
        (algebraMap ℂ DeningerEntireH1 (-Complex.I) *
          deningerEntireCoordinateResolvent alpha) =
      algebraMap ℂ DeningerEntireH1 Complex.I *
        (algebraMap ℂ DeningerEntireH1 (-Complex.I) *
          ((deningerEntireCoordinateClass -
              algebraMap ℂ DeningerEntireH1 alpha) *
            deningerEntireCoordinateResolvent alpha)) := by
              rw [mul_assoc]
              congr 1
              rw [← mul_assoc, mul_comm
                (deningerEntireCoordinateClass -
                  algebraMap ℂ DeningerEntireH1 alpha)
                (algebraMap ℂ DeningerEntireH1 (-Complex.I)),
                mul_assoc]
    _ =
      (algebraMap ℂ DeningerEntireH1 Complex.I *
          algebraMap ℂ DeningerEntireH1 (-Complex.I)) *
        ((deningerEntireCoordinateClass -
            algebraMap ℂ DeningerEntireH1 alpha) *
          deningerEntireCoordinateResolvent alpha) := by
            rw [mul_assoc]
    _ = 1 := by
      rw [hcoord, mul_one, ← map_mul]
      norm_num

/-- Linear Frobenius shift used in the middle Weil--Arakelov mapping fiber. -/
def deningerEntireThetaCenteredShift (alpha : ℂ) :
    Module.End ℂ DeningerEntireH1 :=
  deningerEntireTheta -
    (1 / 2 + Complex.I * alpha) • LinearMap.id

@[simp]
theorem deningerEntireThetaCenteredShift_apply
    (alpha : ℂ) (x : DeningerEntireH1) :
    deningerEntireThetaCenteredShift alpha x =
      (deningerEntireThetaClass -
        algebraMap ℂ DeningerEntireH1
          (1 / 2 + Complex.I * alpha)) * x := by
  change deningerEntireThetaClass * x -
      algebraMap ℂ DeningerEntireH1
        (1 / 2 + Complex.I * alpha) * x =
    (deningerEntireThetaClass -
      algebraMap ℂ DeningerEntireH1
        (1 / 2 + Complex.I * alpha)) * x
  exact (sub_mul deningerEntireThetaClass
    (algebraMap ℂ DeningerEntireH1
      (1 / 2 + Complex.I * alpha)) x).symm

/--
Off the Xi divisor, the middle Frobenius shift is a linear equivalence with the explicit
source resolvent as inverse.
-/
def deningerEntireThetaCenteredShiftEquiv
    {alpha : ℂ} (hXi : XiC alpha ≠ 0) :
    DeningerEntireH1 ≃ₗ[ℂ] DeningerEntireH1 where
  toFun := deningerEntireThetaCenteredShift alpha
  map_add' := map_add _
  map_smul' := map_smul _
  invFun :=
    LinearMap.mulLeft ℂ
      (deningerEntireThetaCenteredResolvent alpha)
  left_inv x := by
    rw [deningerEntireThetaCenteredShift_apply]
    change deningerEntireThetaCenteredResolvent alpha *
        ((deningerEntireThetaClass -
          algebraMap ℂ DeningerEntireH1
            (1 / 2 + Complex.I * alpha)) * x) = x
    rw [← mul_assoc,
      mul_comm (deningerEntireThetaCenteredResolvent alpha),
      deningerEntireThetaCenteredResolvent_mul hXi, one_mul]
  right_inv x := by
    rw [deningerEntireThetaCenteredShift_apply]
    change
      (deningerEntireThetaClass -
          algebraMap ℂ DeningerEntireH1
            (1 / 2 + Complex.I * alpha)) *
        (deningerEntireThetaCenteredResolvent alpha * x) = x
    rw [← mul_assoc,
      deningerEntireThetaCenteredResolvent_mul hXi, one_mul]

/--
The middle map in the Weil--Arakelov specialization is bijective at every centered point away
from the source-defined Xi divisor.
-/
theorem deningerEntireThetaCenteredShift_bijective
    {alpha : ℂ} (hXi : XiC alpha ≠ 0) :
    Function.Bijective
      (deningerEntireThetaCenteredShift alpha) :=
  (deningerEntireThetaCenteredShiftEquiv hXi).bijective

end

end RHTower
