import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierAlgebra
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
/-! Exact partial derivatives and first forcing decomposition. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def hFieldCore (h v q : ℝ) : ℝ := -(4/3)*h*(3+h)*(h-q*(9-v))
def forcingFactor (v q : ℝ) : ℝ := 1-2*(9-v)*q

theorem hFieldCore_eq (h v q : ℝ) : fieldH h v q=v*hFieldCore h v q := by
  unfold fieldH hFieldCore
  ring

theorem qField_forcing_split (h v q : ℝ) :
    forcingFactor v q*qField h v q=
      6*(9-v)*quadraticBoundaryCore h v q+
        6*forcingFactor v q*A h v q*quadraticError h v q-
          (7/72)*fieldH h v q-12*v*(9-v)*q^2 := by
  unfold qField forcingFactor
  have he := quadraticField_split h v q
  unfold quadraticField at he
  linear_combination he

/-- The exact V-remainder after the forcing and error terms have been isolated. -/
def forcingRemainder (h v q rh rv rq : ℝ) : ℝ :=
  forcingFactor v q*(rh*hFieldCore h v q+12*(9-v)*rv)+
    rq*(-(7/72)*hFieldCore h v q-12*(9-v)*q^2)

/-- This identity keeps the error term's sign explicit; it is not discarded. -/
theorem forcing_direction_split (h v q rh rv rq : ℝ) :
    forcingFactor v q*(rh*fieldH h v q+rv*fieldV v+rq*qField h v q)=
      6*(9-v)*rq*quadraticBoundaryCore h v q+
        6*forcingFactor v q*A h v q*rq*quadraticError h v q+
          v*forcingRemainder h v q rh rv rq := by
  have he := qField_forcing_split h v q
  rw [hFieldCore_eq] at he ⊢
  unfold fieldV forcingRemainder
  linear_combination rq*he

def Ah (h v q : ℝ) : ℝ :=
  (2/9)*v*(3-2*h)+(2/9)*v*(9-v)*(q+b h)+(7/324)*v*h*(9-v)
def Av (h v q : ℝ) : ℝ :=
  5+(2/9)*h*(3-h)+(2/3)*(9-2*v)*(1+h/3)*(q+b h)+
    (7/108)*(9-2*v)*h*(1+h/3)
def Aq (h v : ℝ) : ℝ := (2/3)*v*(1+h/3)*(9-v)
def Hhh (h v q : ℝ) : ℝ :=
  -(4/3)*v*((3+2*h)*(h-q*(9-v))+h*(3+h))
def Hhv (h v q : ℝ) : ℝ := -(4/3)*h*(3+h)*(h-q*(9-2*v))
def Hhq (h v : ℝ) : ℝ := (4/3)*h*(3+h)*v*(9-v)
def Rh (h v q : ℝ) : ℝ :=
  forcingFactor v q*(Dh h v+q^2*Ah h v q)+(7/216)*q*Hhh h v q
def Rv (h v q : ℝ) : ℝ :=
  2*q*(D h v+q^2*A h v q)+forcingFactor v q*(Dv h+q^2*Av h v q)+
    (7/216)*q*Hhv h v q+2*q^2
def Rq (h v q : ℝ) : ℝ :=
  -2*(9-v)*(D h v+q^2*A h v q)+forcingFactor v q*(2*q*A h v q+q^2*Aq h v)+
    (7/216)*(fieldH h v q+q*Hhq h v)+4*v*q


theorem dRh (h v q : ℝ) : HasDerivAt (fun s => quadraticBoundaryCore s v q) (Rh h v q) h := by
  have hd : DifferentiableAt ℝ (fun s => quadraticBoundaryCore s v q) h := by
    unfold quadraticBoundaryCore D A b fieldH
    fun_prop
  convert hd.hasDerivAt using 1 <;> first | rfl | skip
  change Rh h v q=deriv (fun s : ℝ => quadraticBoundaryCore s v q) h
  simp only [quadraticBoundaryCore,D,A,b,fieldH,Rh,Rv,Rq,Ah,Av,Aq,Hhh,Hhv,Hhq,Dh,Dv,forcingFactor]
  simp (disch := fun_prop) [deriv_add,deriv_sub,deriv_mul,deriv_div_const,deriv_pow]
  ring

theorem dRv (h v q : ℝ) : HasDerivAt (fun s => quadraticBoundaryCore h s q) (Rv h v q) v := by
  have hd : DifferentiableAt ℝ (fun s => quadraticBoundaryCore h s q) v := by
    unfold quadraticBoundaryCore D A b fieldH
    fun_prop
  convert hd.hasDerivAt using 1 <;> first | rfl | skip
  change Rv h v q=deriv (fun s : ℝ => quadraticBoundaryCore h s q) v
  simp only [quadraticBoundaryCore,D,A,b,fieldH,Rh,Rv,Rq,Ah,Av,Aq,Hhh,Hhv,Hhq,Dh,Dv,forcingFactor]
  simp (disch := fun_prop) [deriv_add,deriv_sub,deriv_mul,deriv_div_const,deriv_pow]
  ring

theorem dRq (h v q : ℝ) : HasDerivAt (fun s => quadraticBoundaryCore h v s) (Rq h v q) q := by
  have hd : DifferentiableAt ℝ (fun s => quadraticBoundaryCore h v s) q := by
    unfold quadraticBoundaryCore D A b fieldH
    fun_prop
  convert hd.hasDerivAt using 1 <;> first | rfl | skip
  change Rq h v q=deriv (fun s : ℝ => quadraticBoundaryCore h v s) q
  simp only [quadraticBoundaryCore,D,A,b,fieldH,Rh,Rv,Rq,Ah,Av,Aq,Hhh,Hhv,Hhq,Dh,Dv,forcingFactor]
  simp (disch := fun_prop) [deriv_add,deriv_sub,deriv_mul,deriv_div_const,deriv_pow]
  ring

end
end HTGeometry.ThetaCriticalBarrier
