import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.ShellPhases
import GaloisForLFunctions.HTGeometry.IsogenyFunctionFieldLevel

/-! # Totally real length ratios in a triangle with torsion directions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open scoped ComplexConjugate
open Complex IntermediateField

def phaseDet {K : Type*} [Field K] (U V : K) := U*V⁻¹-U⁻¹*V

/-- Real coefficient of the first direction in the decomposition of 1. -/
def phaseRatio {K : Type*} [Field K] (U V : K) := (V⁻¹-V)/phaseDet U V

theorem conjugate_torsion {z : ℂ} {m : ℕ} (hm : 0 < m) (unit : z^m=1) : conj z=z⁻¹ := by
  have n := phase_norm hm unit
  have h := Complex.mul_conj z
  rw [← Complex.sq_norm,n,one_pow,Complex.ofReal_one] at h
  have nz : z ≠ 0 := norm_pos_iff.mp (by rw [n]; exact zero_lt_one)
  rw [← one_div,eq_div_iff nz,mul_comm]
  exact h

private theorem real_ratio {U V : ℂ} (hu : conj U=U⁻¹) (hv : conj V=V⁻¹) :
    conj (phaseRatio U V)=phaseRatio U V := by
  simp only [phaseRatio,phaseDet,map_div₀,map_sub,map_mul,map_inv₀,hu,hv,inv_inv]
  rw [← neg_sub (V⁻¹) V,← neg_sub (U*V⁻¹) (U⁻¹*V),neg_div_neg_eq]

/-- The linear system and its conjugate recover the coefficient if its
determinant is nonzero. If it vanishes, both unit directions are real. -/
theorem triangle_equations {x y : ℝ} {U V : ℂ} {m : ℕ} (hm : 0 < m)
    (hu : U^m=1) (hv : V^m=1) (eq : (x : ℂ)*U+(y : ℂ)*V=1) :
    (x : ℂ)*phaseDet U V=V⁻¹-V ∧ (y : ℂ)*phaseDet U V=U-U⁻¹ := by
  have back := congrArg conj eq
  simp only [map_add,map_mul,map_one,Complex.conj_ofReal,conjugate_torsion hm hu,
    conjugate_torsion hm hv] at back
  unfold phaseDet
  constructor
  · linear_combination V⁻¹*eq-V*back
  · linear_combination U*back-U⁻¹*eq

theorem torsion_algebraic (K : Type*) [Field K] [Algebra K ℂ] {U : ℂ} {m : ℕ} (hm : 0 < m)
    (hu : U^m=1) : IsAlgebraic K U := by
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow hm
  rw [hu]
  exact isIntegral_one

private theorem norm_determines_sq {z w : ℂ} (zr : conj z=z) (wr : conj w=w) (h : ‖z‖=‖w‖) :
    z^2=w^2 := by
  have scalar : (Complex.normSq z : ℂ)=(Complex.normSq w : ℂ) := by
    rw [← Complex.sq_norm,← Complex.sq_norm,h]
  rwa [← Complex.mul_conj,← Complex.mul_conj,zr,wr,← sq,← sq] at scalar

/-- A power of a torsion triangle length in a subfield forces its square
into the same subfield. Under every embedding the length remains real. -/
theorem ratio_square_mem (K : IntermediateField ℚ ℂ) {U V : ℂ} {m n : ℕ}
    (hm : 0 < m) (hU : U^m=1) (hV : V^m=1) (hn : 0<n) (power : (phaseRatio U V)^n ∈ K) :
    (phaseRatio U V)^2 ∈ K := by
  let L := algebraicClosure K ℂ
  let u : L := ⟨U,mem_algebraicClosure_iff.mpr (torsion_algebraic K hm hU)⟩
  let v : L := ⟨V,mem_algebraicClosure_iff.mpr (torsion_algebraic K hm hV)⟩
  let x := phaseRatio u v
  have repr : (x : ℂ)=phaseRatio U V := rfl
  have uPow : u^m=1 := Subtype.ext hU
  have vPow : v^m=1 := Subtype.ext hV
  let c : K := ⟨(phaseRatio U V)^n,power⟩
  have lift : x^n=algebraMap K L c := by apply Subtype.ext; exact congrArg (·^n) repr
  have realX := real_ratio (conjugate_torsion hm hU) (conjugate_torsion hm hV)
  have fixed (f : L →ₐ[K] ℂ) : f (x^2)=algebraMap L ℂ (x^2) := by
    have eq : f x^n=(phaseRatio U V)^n := by rw [← map_pow,lift,AlgHom.commutes]; rfl
    have normEq : ‖f x‖=‖phaseRatio U V‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn.ne').mp
      (by rw [← norm_pow,← norm_pow,eq])
    have image : f x=phaseRatio (f u) (f v) := by simp only [x,phaseRatio,phaseDet,map_div₀,map_sub,map_inv₀,map_mul]
    have ur := conjugate_torsion hm (show (f u)^m=1 by rw [← map_pow,uPow,map_one])
    have vr := conjugate_torsion hm (show (f v)^m=1 by rw [← map_pow,vPow,map_one])
    have realImage : conj (f x)=f x := by rw [image]; exact real_ratio ur vr
    change f (x^2)=((x : ℂ)^2)
    rw [map_pow,repr]
    exact norm_determines_sq realImage realX normEq
  obtain ⟨r,hr⟩ := GaloisForLFunctions.HTGeometry.mem_range_of_forall_algHom_eq (x^2) fixed
  have eq : (r : ℂ)=(phaseRatio U V)^2 := (congrArg ((↑) : L → ℂ) hr).trans (congrArg (·^2) repr)
  exact eq ▸ r.property

#print axioms triangle_equations
#print axioms ratio_square_mem

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
