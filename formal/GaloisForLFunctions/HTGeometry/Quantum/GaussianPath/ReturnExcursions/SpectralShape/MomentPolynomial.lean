import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import Mathlib.Tactic.ComputeDegree

/-! # A scale-invariant spectral constraint on a Gaussian path -/

open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section

/-- The third energy moment with normalized counting measure on all levels. -/
def thirdMoment {n : ℕ} (h : PathShell n) : ℝ :=
  ((pathHamiltonian h)^3).trace.re/(2:ℝ)^(n+2)

/-- Vanishing is invariant under rescaling the Hamiltonian. When the variance
is positive it prescribes the square of the standardized third moment. -/
def skewConstraint {n : ℕ} (c : ℝ) (h : PathShell n) : ℝ :=
  thirdMoment h^2-c*(‖h‖^2)^3

private theorem cubic_line {n : ℕ} (y v : PathShell n) :
    ∃ a b : ℝ, ∀ t : ℝ, thirdMoment (y+t • v)=
      thirdMoment y+a*t+b*t^2+thirdMoment v*t^3 := by
  let A := pathHamiltonian y
  let B := pathHamiltonian v
  let D := (2:ℝ)^(n+2)
  let tr (M : Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := M.trace.re/D
  refine ⟨tr (B*A*A)+tr (A*B*A)+tr (A*A*B),
    tr (A*B*B)+tr (B*A*B)+tr (B*B*A),?_⟩
  intro t
  have he : pathHamiltonian (y+t • v)=A+t • B := by
    change pathHamiltonianLM n (y+t • v)=_
    rw [map_add,map_smul]
    rfl
  unfold thirdMoment
  rw [he]
  change ((A+t • B)^3).trace.re/D=tr (A^3)+_+_+tr (B^3)*t^3
  dsimp only [tr]
  simp only [pow_succ,pow_zero,one_mul,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.trace_add,Matrix.trace_smul,Complex.add_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- On any parallel line the sixth coefficient of the constraint depends only
on the direction. All coefficients below it may depend on the base point. -/
theorem constraint_polynomial {n : ℕ} (c : ℝ) (y v : PathShell n) :
    ∃ P : ℂ[X], P.natDegree≤6 ∧ P.coeff 6=(skewConstraint c v:ℂ) ∧
      ∀ t : ℝ, P.eval (t:ℂ)=(skewConstraint c (y+t • v):ℂ) := by
  obtain ⟨a,b,hab⟩ := cubic_line y v
  let m := thirdMoment y
  let g := thirdMoment v
  let d := ‖y‖^2
  let e := 2*inner ℝ y v
  let f := ‖v‖^2
  let M : ℂ[X] := C (m:ℂ)+C (a:ℂ)*X+C (b:ℂ)*X^2+C (g:ℂ)*X^3
  let V : ℂ[X] := C (d:ℂ)+C (e:ℂ)*X+C (f:ℂ)*X^2
  have hdM : M.natDegree≤3 := by dsimp only [M]; compute_degree
  have hdV : V.natDegree≤2 := by dsimp only [V]; compute_degree
  have hm : M.coeff 3=(g:ℂ) := by dsimp only [M]; compute_degree!
  have hv : V.coeff 2=(f:ℂ) := by dsimp only [V]; compute_degree!
  refine ⟨M^2-C (c:ℂ)*V^3,(natDegree_sub_le _ _).trans (max_le ?_ ?_),?_,?_⟩
  · exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hdM)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (Nat.mul_le_mul_left 3 hdV))
  · rw [coeff_sub,coeff_C_mul,show (6:ℕ)=2*3 by rfl,coeff_pow_of_natDegree_le hdM,
        show (2*3:ℕ)=3*2 by rfl,coeff_pow_of_natDegree_le hdV,hm,hv]
    simp [skewConstraint,g,f]
  · intro t
    have hv' : ‖y+t • v‖^2=d+e*t+f*t^2 := by
      rw [norm_add_sq_real,real_inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      dsimp only [d,e,f]
      ring
    simp [M,V,skewConstraint,hab,hv',m,g]

#print axioms constraint_polynomial
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
