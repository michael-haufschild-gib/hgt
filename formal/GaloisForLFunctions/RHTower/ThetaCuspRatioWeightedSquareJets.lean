import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareFlow
import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerIncidence

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

/-- Multiplication by U^n makes every source jet polynomial in squared drift. -/
def weightedJet : ℕ → Poly
  | 0 => 6*X .K-1
  | n+1 => squareLie (weightedJet n)-6*(n:Poly)*X .K*(9-X .U)*weightedJet n+
      X .U*(1-12*X .K)*weightedJet n

theorem chartLie_mul (P Q : Poly) : chartLie (P*Q)=chartLie P*Q+P*chartLie Q :=
  flow_mul chartField P Q

theorem chartLie_X (i : Coord) : chartLie (X i)=chartField i := flow_X chartField i

theorem chartLie_U_pow (n : ℕ) :
    chartLie ((X Coord.U)^n)=6*(n:Poly)*(X Coord.U)^n*X .K*(9-(X .U)^2) := by
  induction n with
  | zero => simp [chartLie,flow]
  | succ n ih =>
      rw [pow_succ,chartLie_mul,ih,chartLie_X]
      simp only [chartField,Nat.cast_add,Nat.cast_one]
      ring

theorem weightedJet_eq (n : ℕ) :
    square (weightedJet n)=(X Coord.U)^n*shear (integerJet n) := by
  induction n with
  | zero => norm_num [weightedJet,integerJet,squareCoord,shearCoord,map_ofNat]
  | succ n ih =>
      rw [weightedJet]
      simp only [map_add,map_sub,map_mul,map_natCast,map_ofNat,map_one,square_X]
      rw [←chartLie_square,ih,chartLie_mul,chartLie_U_pow,chartLie_shear]
      simp only [integerJet,integerStep,map_add,map_mul,map_sub,map_one,map_ofNat,
        shear_X,squareCoord,shearCoord,pow_succ]
      ring

def weightedReflection (n : ℕ) : Poly :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:Poly)*(-1:Poly)^(n-i)*
    weightedJet i*weightedJet (n-i)

theorem weightedReflection_eq (n : ℕ) :
    square (weightedReflection n)=(X Coord.U)^n*shear (integerReflection n) := by
  unfold weightedReflection integerReflection
  simp only [map_sum,map_mul,map_pow,map_natCast,map_neg,map_one,weightedJet_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hp : (X Coord.U:Poly)^i*(X Coord.U)^(n-i)=(X Coord.U)^n := by
    rw [←pow_add,Nat.add_sub_of_le hin]
  calc
    _ = (n.choose i:Poly)*(-1:Poly)^(n-i)*
        ((X Coord.U)^i*(X Coord.U)^(n-i))*
        shear (integerJet i)*shear (integerJet (n-i)) := by ring
    _ = _ := by rw [hp]; ring

def weightedMoment (r : ℕ) : Poly := (-1:Poly)^r*weightedReflection (2*r)

theorem weightedMoment_eq (r : ℕ) :
    square (weightedMoment r)=(X Coord.U)^(2*r)*shear (integerSignedMoment r) := by
  simp only [weightedMoment,integerSignedMoment,map_mul,map_pow,map_neg,map_one,
    weightedReflection_eq]
  ring

end
end HTGeometry.ThetaRatioWeightedSquare
