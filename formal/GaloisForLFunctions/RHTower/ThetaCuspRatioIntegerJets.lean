import GaloisForLFunctions.RHTower.ThetaCuspRatioSourceJets
/-! # Integer gauge for the exact all-order ratio-source jets. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

def integerField : Coord → Poly
  | .U => 6*X .K*(9-(X .U)^2)
  | .K => (12*X .K+4)*X .J
  | .J => 6*(X .K)^2*(9-(X .U)^2)-36*X .K-24+(12*X .K+8)*X .U*X .J

def integerLie (P : Poly) : Poly := ∑ i, pderiv i P*integerField i
def integerStep (P : Poly) : Poly := integerLie P+X Coord.U*(1-12*X .K)*P
def integerJet : ℕ → Poly
  | 0 => 6*X .K-1
  | n+1 => integerStep (integerJet n)

private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

private theorem integerStep_Cmul (c : ℂ) (P : Poly) :
    integerStep (C c*P)=C c*integerStep P := by
  unfold integerStep integerLie
  simp only [pderiv_mul,pderiv_C,zero_mul,zero_add]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

private theorem integerStep_eq (P : Poly) : integerStep P=6*normalizedLie P := by
  apply MvPolynomial.funext
  intro v
  have hq := sourceJet_zero_eval v
  simp only [sourceJet,map_sub,eval_X] at hq
  have hq' := sub_right_inj.mp hq
  simp [integerStep,integerLie,normalizedLie,lie,univ_eq,integerField,field,tau]
  rw [hq']
  ring

theorem integerJet_eq (n : ℕ) :
    integerJet n=C ((6:ℂ)^(n+1))*sourceJet n := by
  induction n with
  | zero =>
      apply MvPolynomial.funext
      intro v
      simp only [map_mul,eval_C,sourceJet_zero_eval]
      simp [integerJet]
      ring
  | succ n ih =>
      rw [integerJet,ih,integerStep_Cmul,integerStep_eq,sourceJet]
      simp only [pow_succ,map_mul,map_ofNat]
      ring

def jetNorm0 : {P : Poly // integerJet 0=P} := by
  have h : integerJet 0=integerJet 0 := rfl
  conv at h => rhs; rw [integerJet]
  exact ⟨_,h⟩

def jetNorm1 : {P : Poly // integerJet 1=P} := by
  have h : integerJet 1=integerJet 1 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm0.property]
    dsimp only [jetNorm0]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm2 : {P : Poly // integerJet 2=P} := by
  have h : integerJet 2=integerJet 2 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm1.property]
    dsimp only [jetNorm1]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm3 : {P : Poly // integerJet 3=P} := by
  have h : integerJet 3=integerJet 3 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm2.property]
    dsimp only [jetNorm2]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm4 : {P : Poly // integerJet 4=P} := by
  have h : integerJet 4=integerJet 4 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm3.property]
    dsimp only [jetNorm3]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm5 : {P : Poly // integerJet 5=P} := by
  have h : integerJet 5=integerJet 5 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm4.property]
    dsimp only [jetNorm4]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm6 : {P : Poly // integerJet 6=P} := by
  have h : integerJet 6=integerJet 6 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm5.property]
    dsimp only [jetNorm5]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm7 : {P : Poly // integerJet 7=P} := by
  have h : integerJet 7=integerJet 7 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm6.property]
    dsimp only [jetNorm6]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

def jetNorm8 : {P : Poly // integerJet 8=P} := by
  have h : integerJet 8=integerJet 8 := rfl
  conv at h =>
    rhs
    rw [integerJet,jetNorm7.property]
    dsimp only [jetNorm7]
    simp [integerStep,integerLie,integerField,univ_eq,pderiv_X,Pi.single_apply]
    ring_nf
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
