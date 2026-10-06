import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerJets
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

-- The target K and J slots now mean Y and T. U is fixed to three.
def y : Poly := X Coord.K
def t : Poly := X Coord.J

def pullCoord : Coord → Poly
  | .U => 3
  | .K => C (1/3:ℂ)*(y-1)
  | .J => t+y+1

def pull : Poly →+* Poly := eval₂Hom C pullCoord

@[simp] theorem pull_C (c : ℂ) : pull (C c)=C c := by simp [pull]
@[simp] theorem pull_X (i : Coord) : pull (X i)=pullCoord i := by simp [pull]

def delta (P : Poly) : Poly := y*(y+t+1)*pderiv Coord.K P+t*pderiv Coord.J P
def step (P : Poly) : Poly := delta P+(C (5/4:ℂ)-y)*P
def adapted (P : Poly) : Poly := delta P+(C (1/4:ℂ)-y)*P

@[simp] theorem delta_C (c : ℂ) : delta (C c)=0 := by simp [delta]
@[simp] theorem delta_add (P Q : Poly) : delta (P+Q)=delta P+delta Q := by
  simp only [delta,map_add]
  ring
@[simp] theorem delta_sub (P Q : Poly) : delta (P-Q)=delta P-delta Q := by
  simp only [delta,map_sub]
  ring
theorem delta_mul (P Q : Poly) : delta (P*Q)=delta P*Q+P*delta Q := by
  simp only [delta,pderiv_mul]
  ring
theorem delta_C_mul (c : ℂ) (P : Poly) : delta (C c*P)=C c*delta P := by
  simp only [delta,pderiv_C_mul]
  ring
@[simp] theorem delta_y : delta y=y*(y+t+1) := by
  simp [delta,y,t,pderiv_X]
@[simp] theorem delta_t : delta t=t := by
  simp [delta,y,t,pderiv_X]

private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

private theorem nativeLie_mul (P Q : Poly) :
    integerLie (P*Q)=integerLie P*Q+P*integerLie Q := by
  simp [integerLie,univ_eq]
  ring

private theorem nativeLie_X (i : Coord) : integerLie (X i)=integerField i := by
  simp [integerLie,pderiv_X,Pi.single_apply]

theorem pull_field (i : Coord) : pull (integerField i)=12*delta (pull (X i)) := by
  have hKJ : Coord.K≠Coord.J := by decide
  have hJK : Coord.J≠Coord.K := by decide
  cases i <;> apply MvPolynomial.funext <;> intro v <;>
    norm_num [integerField,pullCoord,delta,y,t,pderiv_X,Pi.single_apply,
      hKJ,hJK,map_ofNat] <;> ring

-- This is the complete native field, not its homogeneous approximation.
theorem pull_lie (P : Poly) : pull (integerLie P)=12*delta (pull P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [integerLie]
  | add P Q hP hQ =>
    have h : integerLie (P+Q)=integerLie P+integerLie Q := by
      simp [integerLie,add_mul,Finset.sum_add_distrib]
    rw [h,map_add,hP,hQ,map_add,delta_add]
    ring
  | mul_X P i ih =>
    rw [nativeLie_mul]
    simp only [map_add,map_mul]
    rw [ih,nativeLie_X,pull_field,delta_mul]
    ring

theorem pull_step (P : Poly) : pull (integerStep P)=12*step (pull P) := by
  simp only [integerStep,map_add,map_sub,map_mul,map_one,map_ofNat,pull_lie,pull_X]
  unfold pullCoord step
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one,eval_C]
  ring

theorem step_C_mul (c : ℂ) (P : Poly) : step (C c*P)=C c*step P := by
  unfold step
  rw [delta_C_mul]
  ring

def jet : ℕ → Poly
  | 0 => 2*y-3
  | n+1 => step (jet n)

theorem pull_integerJet (n : ℕ) : pull (integerJet n)=C ((12:ℂ)^n)*jet n := by
  induction n with
  | zero =>
    simp [integerJet,jet,pullCoord,map_ofNat]
    apply MvPolynomial.funext
    intro v
    simp only [map_sub,map_mul,map_ofNat,map_one,eval_C]
    ring
  | succ n ih =>
    rw [integerJet,pull_step,ih,step_C_mul,jet,pow_succ,map_mul]
    simp only [map_ofNat]
    ring

-- Shifted Bell polynomials, defined by their literal differential recurrence.
def bell (a : ℂ) : ℕ → Poly
  | 0 => 1
  | n+1 => t*pderiv Coord.J (bell a n)+(t+C a)*bell a n

theorem bell_pderiv_y (a : ℂ) (n : ℕ) : pderiv Coord.K (bell a n)=0 := by
  induction n with
  | zero => simp [bell]
  | succ n ih =>
    simp only [bell,map_add,pderiv_mul]
    rw [GaloisForLFunctions.pderiv_comm Coord.K Coord.J (bell a n),ih]
    simp [t,pderiv_X]

theorem delta_bell (a : ℂ) (n : ℕ) : delta (bell a n)=t*pderiv Coord.J (bell a n) := by
  simp [delta,bell_pderiv_y]

theorem adapted_add (P Q : Poly) : adapted (P+Q)=adapted P+adapted Q := by
  simp only [adapted,delta_add]
  ring
theorem adapted_sub (P Q : Poly) : adapted (P-Q)=adapted P-adapted Q := by
  simp only [adapted,delta_sub]
  ring
theorem adapted_C_mul (c : ℂ) (P : Poly) : adapted (C c*P)=C c*adapted P := by
  simp only [adapted,delta_C_mul]
  ring

theorem t_step (P : Poly) : t*step P=adapted (t*P) := by
  unfold step adapted
  rw [delta_mul,delta_t]
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_sub,map_mul,eval_C]
  ring

theorem adapted_y_t_bell (n : ℕ) :
    adapted (y*t*bell (9/4) n)=y*t*bell (9/4) (n+1) := by
  unfold adapted
  rw [delta_mul,delta_mul,delta_y,delta_t,delta_bell]
  rw [bell]
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_sub,map_mul,map_one,eval_C]
  ring

theorem adapted_y_bell (n : ℕ) :
    adapted (y*bell (5/4) n)=y*bell (5/4) (n+1) := by
  unfold adapted
  rw [delta_mul,delta_y,delta_bell,bell]
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_sub,map_mul,map_one,eval_C]
  ring

theorem adapted_t_add_y : adapted (t+y)=C (5/4:ℂ)*(t+y) := by
  simp only [adapted,delta_add,delta_t,delta_y]
  apply MvPolynomial.funext
  intro v
  simp only [map_add,map_sub,map_mul,map_one,eval_C]
  ring

-- Exact all-order source formula, valid also on T=0 because no T is divided out.
theorem jet_cleared (n : ℕ) :
    t*jet n=2*y*t*bell (9/4) n+3*y*bell (5/4) n-
      3*(t+y)*C ((5/4:ℂ)^n) := by
  induction n with
  | zero => simp [jet,bell]; ring
  | succ n ih =>
    rw [jet,t_step,ih]
    have h2 : 2*y*t*bell (9/4) n=C (2:ℂ)*(y*t*bell (9/4) n) := by
      simp only [map_ofNat]; ring
    have h3 : 3*y*bell (5/4) n=C (3:ℂ)*(y*bell (5/4) n) := by
      simp only [map_ofNat]; ring
    have h5 : 3*(t+y)*C ((5/4:ℂ)^n)=C (3*(5/4:ℂ)^n)*(t+y) := by
      simp only [map_mul,map_ofNat]
      ring
    rw [h2,h3,h5,adapted_sub,adapted_add,adapted_C_mul,adapted_C_mul,
      adapted_C_mul,adapted_y_t_bell,adapted_y_bell,adapted_t_add_y,pow_succ,map_mul]
    simp only [map_ofNat,map_mul]
    ring

theorem native_jet_cleared (n : ℕ) :
    t*pull (integerJet n)=C ((12:ℂ)^n)*
      (2*y*t*bell (9/4) n+3*y*bell (5/4) n-3*(t+y)*C ((5/4:ℂ)^n)) := by
  rw [pull_integerJet]
  calc
    _ = C ((12:ℂ)^n)*(t*jet n) := by ring
    _ = _ := by rw [jet_cleared]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
