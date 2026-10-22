import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerJets
/-! # Exact squared-coordinate algebra for the full modular third slope. -/

namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource

/-- The intermediate chart keeps U and replaces the original J by U*Z. -/
def shearCoord : Coord → Poly
  | .U => X .U
  | .K => X .K
  | .J => X .U*X .J

def squareCoord : Coord → Poly
  | .U => (X .U)^2
  | .K => X .K
  | .J => X .J

def shear : Poly →+* Poly := eval₂Hom C shearCoord
def square : Poly →+* Poly := eval₂Hom C squareCoord

def squareField : Coord → Poly
  | .U => 12*X .U*X .K*(9-X .U)
  | .K => (12*X .K+4)*X .U*X .J
  | .J => 6*(X .K)^2*(9-X .U)-36*X .K-24+
      (12*X .K+8)*X .U*X .J-6*X .J*X .K*(9-X .U)

def chartField : Coord → Poly
  | .U => 6*X .U*X .K*(9-(X .U)^2)
  | .K => (12*X .K+4)*(X .U)^2*X .J
  | .J => 6*(X .K)^2*(9-(X .U)^2)-36*X .K-24+
      (12*X .K+8)*(X .U)^2*X .J-6*X .J*X .K*(9-(X .U)^2)

def flow (f : Coord → Poly) (P : Poly) : Poly := ∑ i, pderiv i P*f i
abbrev squareLie := flow squareField
abbrev chartLie := flow chartField

private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

@[simp] theorem shear_C (c : ℂ) : shear (C c)=C c := by simp [shear]
@[simp] theorem shear_X (i : Coord) : shear (X i)=shearCoord i := by simp [shear]
@[simp] theorem square_C (c : ℂ) : square (C c)=C c := by simp [square]
@[simp] theorem square_X (i : Coord) : square (X i)=squareCoord i := by simp [square]

theorem flow_C (f : Coord → Poly) (c : ℂ) : flow f (C c)=0 := by simp [flow]
theorem flow_add (f : Coord → Poly) (P Q : Poly) :
    flow f (P+Q)=flow f P+flow f Q := by
  simp [flow,add_mul,Finset.sum_add_distrib]
theorem flow_mul (f : Coord → Poly) (P Q : Poly) :
    flow f (P*Q)=flow f P*Q+P*flow f Q := by
  unfold flow
  simp_rw [pderiv_mul,add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (·+·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem flow_X (f : Coord → Poly) (i : Coord) : flow f (X i)=f i := by
  unfold flow
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [pderiv_X,hji]
  · simp

private theorem field_shear (i : Coord) :
    chartLie (shearCoord i)=X Coord.U*shear (integerField i) := by
  cases i <;> apply MvPolynomial.funext <;> intro v
  all_goals simp [chartLie,flow,chartField,shearCoord,shear,integerField,
    univ_eq,pderiv_X,Pi.single_apply,map_ofNat]
  all_goals ring

private theorem field_square (i : Coord) :
    chartLie (squareCoord i)=square (squareField i) := by
  cases i <;> apply MvPolynomial.funext <;> intro v
  all_goals simp [chartLie,flow,chartField,squareCoord,square,squareField,
    univ_eq,pderiv_X,Pi.single_apply,map_ofNat]
  all_goals ring

/-- The sheared derivation is exactly U times the original integer derivation. -/
theorem chartLie_shear (P : Poly) : chartLie (shear P)=X Coord.U*shear (integerLie P) := by
  change flow chartField (shear P)=X Coord.U*shear (flow integerField P)
  induction P using MvPolynomial.induction_on with
  | C c => simp only [shear_C,flow_C,map_zero,mul_zero]
  | add P Q hP hQ =>
      rw [map_add,flow_add,flow_add,map_add,hP,hQ,mul_add]
  | mul_X P i hP =>
      simp only [map_mul,flow_mul,flow_X,map_add,shear_X,hP,field_shear]
      ring

/-- The same derivation preserves the square-drift polynomial chart. -/
theorem chartLie_square (P : Poly) : chartLie (square P)=square (squareLie P) := by
  change flow chartField (square P)=square (flow squareField P)
  induction P using MvPolynomial.induction_on with
  | C c => simp only [square_C,flow_C,map_zero]
  | add P Q hP hQ =>
      rw [map_add,flow_add,flow_add,map_add,hP,hQ]
  | mul_X P i hP =>
      simp only [map_mul,flow_mul,flow_X,map_add,square_X,hP,field_square]

end
end HTGeometry.ThetaRatioSquare
