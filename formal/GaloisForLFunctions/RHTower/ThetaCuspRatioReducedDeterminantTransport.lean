import GaloisForLFunctions.RHTower.ThetaCuspRatioUpperSeamPower

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open RHTower.ThetaCuspModularRatio

private theorem squareLie_mul (P Q : Poly) :
    squareLie (P*Q)=squareLie P*Q+P*squareLie Q := flow_mul squareField P Q

private theorem squareLie_X (i : Coord) : squareLie (X i)=squareField i :=
  flow_X squareField i

theorem squareLie_U_pow (n : ℕ) :
    squareLie ((X Coord.U)^n)=12*(n:Poly)*(X Coord.U)^n*X .K*(9-X .U) := by
  induction n with
  | zero => simp [squareLie,flow]
  | succ n ih =>
      rw [pow_succ,squareLie_mul,ih,squareLie_X]
      simp only [squareField,Nat.cast_add,Nat.cast_one]
      ring

def upperDeterminantCoreTransport (c : ℂ) : Poly :=
  X Coord.K*squareLie (upperDeterminantCore c)-
    34*squareField .K*upperDeterminantCore c

theorem upper_determinant_transport_factor (c : ℂ) :
    X Coord.K*squareLie (upperCenterDeterminant c)-
      26*X Coord.K*(12*X Coord.K*(9-X Coord.U))*upperCenterDeterminant c-
      34*squareField .K*upperCenterDeterminant c=
        (X Coord.U)^26*upperDeterminantCoreTransport c := by
  rw [upper_determinant_core_eq,squareLie_mul,squareLie_U_pow]
  norm_num only
  unfold upperDeterminantCoreTransport
  ring

theorem actual_upper_determinant_core_identity (c : ℂ) (x : ℝ) :
    (eval (actualSquarePoint x) (upperCenterDeterminant c)).re=
      (u x)^52*(eval (actualSquarePoint x) (upperDeterminantCore c)).re := by
  rw [upper_determinant_core_eq,map_mul,map_pow,eval_X]
  change (((u x:ℂ)^2)^26*eval (actualSquarePoint x) (upperDeterminantCore c)).re=_
  rw [←pow_mul]
  norm_num only
  rw [←Complex.ofReal_pow,Complex.re_ofReal_mul]

end
end HTGeometry.ThetaRatioWeightedSquare
