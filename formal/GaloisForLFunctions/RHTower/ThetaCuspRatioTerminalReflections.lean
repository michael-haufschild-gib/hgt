import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalKineticJets
import GaloisForLFunctions.RHTower.ThetaCuspRatioIntegerReflections

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def reflection (n : ℕ) : Poly :=
  ∑ i ∈ Finset.range (n+1), (n.choose i:Poly)*(-1:Poly)^(n-i)*jet i*jet (n-i)

def clearedJet (n : ℕ) : Poly :=
  2*y*t*bell (9/4) n+3*y*bell (5/4) n-3*(t+y)*C ((5/4:ℂ)^n)

theorem pull_integerReflection (n : ℕ) :
    pull (integerReflection n)=C ((12:ℂ)^n)*reflection n := by
  simp only [integerReflection,reflection,map_sum,map_mul,map_pow,map_natCast,
    map_neg,map_one,pull_integerJet,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hp : C ((12:ℂ)^i)*C ((12:ℂ)^(n-i))=(C ((12:ℂ)^n):Poly) := by
    rw [←map_mul,←pow_add,Nat.add_sub_of_le hi']
  simp only [map_pow] at hp
  calc
    _ = ((C (12:ℂ))^i*(C (12:ℂ))^(n-i))*
      ((n.choose i:Poly)*(-1:Poly)^(n-i)*jet i*jet (n-i)) := by ring
    _ = _ := by rw [hp]

theorem reflection_cleared (n : ℕ) :
    t^2*reflection n=
      ∑ i ∈ Finset.range (n+1),
        (n.choose i:Poly)*(-1:Poly)^(n-i)*clearedJet i*clearedJet (n-i) := by
  unfold reflection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (n.choose i:Poly)*(-1:Poly)^(n-i)*(t*jet i)*(t*jet (n-i)) := by ring
    _ = _ := by rw [jet_cleared,jet_cleared]; rfl

theorem native_reflection_cleared (n : ℕ) :
    t^2*pull (integerReflection n)=C ((12:ℂ)^n)*
      (∑ i ∈ Finset.range (n+1),
        (n.choose i:Poly)*(-1:Poly)^(n-i)*clearedJet i*clearedJet (n-i)) := by
  rw [pull_integerReflection]
  calc
    _ = C ((12:ℂ)^n)*(t^2*reflection n) := by ring
    _ = _ := by rw [reflection_cleared]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
