import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactSourceJets
import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveChartEquivalence

/-! # All-order source jets in modular ratio coordinates

The exact polynomial change of coordinates removes the common drift-gap
factor from every source derivative. No sign assertion is assumed.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

inductive Coord | U | K | J
  deriving DecidableEq, Fintype
abbrev Poly := MvPolynomial Coord ℂ
private def q : Poly := C (1/6:ℂ)
def tau : Poly := 9-(X Coord.U)^2

def field : Coord → Poly
  | .U => X .K*tau
  | .K => 2*(X .K+2*q)*X .J
  | .J => (X .K)^2*tau-6*X .K-4+2*X .U*(X .K+4*q)*X .J

def lie (P : Poly) : Poly := ∑ i, pderiv i P*field i

def normalizedLie (P : Poly) : Poly := lie P+X Coord.U*(q-2*X .K)*P

def sourceJet : ℕ → Poly
  | 0 => X .K-q
  | n+1 => normalizedLie (sourceJet n)

def coordinate : ModularThetaLyapunovState → Poly
  | .S => -X .U
  | .A => 8*q*tau*(X .K+2*q)
  | .W => X .U*X .K-X .J

def pullback : ModularThetaLyapunovPolynomial →+* Poly := eval₂Hom C coordinate

def amplitudeFactor : Poly := 3*q^2*tau

private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

private theorem lie_C (c : ℂ) : lie (C c)=0 := by simp [lie]
private theorem lie_add (P Q : Poly) : lie (P+Q)=lie P+lie Q := by
  simp [lie,add_mul,Finset.sum_add_distrib]
private theorem lie_mul (P Q : Poly) : lie (P*Q)=lie P*Q+P*lie Q := by
  unfold lie
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

private theorem lie_X (i : Coord) : lie (X i)=field i := by
  unfold lie
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [pderiv_X,hji]
  · simp

@[simp] private theorem pullback_C (c : ℂ) : pullback (C c)=C c := by simp [pullback]
@[simp] private theorem pullback_X (i : ModularThetaLyapunovState) :
    pullback (X i)=coordinate i := by simp [pullback]

private theorem pd2 (i : Coord) : pderiv i (2:Poly)=0 := (pderiv i).map_natCast 2
private theorem pd3 (i : Coord) : pderiv i (3:Poly)=0 := (pderiv i).map_natCast 3
private theorem pd4 (i : Coord) : pderiv i (4:Poly)=0 := (pderiv i).map_natCast 4
private theorem pd6 (i : Coord) : pderiv i (6:Poly)=0 := (pderiv i).map_natCast 6
private theorem pd8 (i : Coord) : pderiv i (8:Poly)=0 := (pderiv i).map_natCast 8
private theorem pd9 (i : Coord) : pderiv i (9:Poly)=0 := (pderiv i).map_natCast 9
attribute [local simp] pd2 pd3 pd4 pd6 pd8 pd9

private theorem field_pullback (i : ModularThetaLyapunovState) :
    pullback (modularThetaLyapunovVectorField i)=lie (coordinate i) := by
  cases i <;> apply MvPolynomial.funext <;> intro v
  all_goals simp [modularThetaLyapunovVectorField,pullback,coordinate,lie,field,tau,q,
    univ_eq,pderiv_X,Pi.single_apply]
  all_goals ring

private theorem lie_pullback (P : ModularThetaLyapunovPolynomial) :
    pullback (modularThetaLyapunovLie P)=lie (pullback P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [modularThetaLyapunovLie_C_local,pullback_C,lie_C,map_zero]
  | add P Q hP hQ =>
      rw [modularThetaLyapunovLie_add_local,map_add,hP,hQ,map_add,lie_add]
  | mul_X P i hP =>
      rw [modularThetaLyapunovLie_mul_local,modularThetaLyapunovLie_X_local,
        map_add,map_mul,map_mul,hP,pullback_X,map_mul,pullback_X,lie_mul,field_pullback]

private theorem factor_lie : lie amplitudeFactor=-2*X Coord.U*X .K*amplitudeFactor := by
  apply MvPolynomial.funext
  intro v
  simp [amplitudeFactor,lie,field,tau,q,univ_eq,pderiv_X,Pi.single_apply]
  ring

private theorem normalized_pullback (P : ModularThetaLyapunovPolynomial) :
    pullback (modularThetaLyapunovNormalizedLie P)=
      lie (pullback P)+X Coord.U*q*pullback P := by
  unfold modularThetaLyapunovNormalizedLie
  rw [map_add,lie_pullback]
  simp only [map_mul,pullback_C,pullback_X,coordinate,q]
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_mul,map_neg,eval_C,eval_X]
  ring

private theorem normalized_factor (P : Poly) :
    lie (amplitudeFactor*P)+X Coord.U*q*(amplitudeFactor*P)=
      amplitudeFactor*normalizedLie P := by
  rw [lie_mul,factor_lie]
  unfold normalizedLie
  ring

/-- The existing mass factor is removed at every source order, not only at the seam. -/
theorem sourceJet_pullback (n : ℕ) :
    pullback (modularThetaLyapunovNormalizedSourceJet n)=amplitudeFactor*sourceJet n := by
  induction n with
  | zero =>
      rw [oddCompactSourceJet0_eq]
      apply MvPolynomial.funext
      intro v
      simp [pullback,coordinate,oddCompactSourceJet0,amplitudeFactor,sourceJet,tau,q]
      ring
  | succ n ih =>
      rw [modularThetaLyapunovNormalizedSourceJet_succ,normalized_pullback,ih,
        normalized_factor,sourceJet]

theorem coordinate_eval (v : Coord → ℂ) (i : ModularThetaLyapunovState) :
    eval v (coordinate i) = match i with
      | .S => -v .U
      | .A => (4/3)*(9-(v .U)^2)*(v .K+1/3)
      | .W => v .U*v .K-v .J := by
  cases i <;> simp [coordinate,q,tau] <;> ring

theorem amplitudeFactor_eval (v : Coord → ℂ) :
    eval v amplitudeFactor=(9-(v .U)^2)/12 := by
  simp [amplitudeFactor,q,tau]
  ring

theorem sourceJet_zero_eval (v : Coord → ℂ) : eval v (sourceJet 0)=v .K-1/6 := by
  simp [sourceJet,q]

end
end HTGeometry.ThetaRatioSource
