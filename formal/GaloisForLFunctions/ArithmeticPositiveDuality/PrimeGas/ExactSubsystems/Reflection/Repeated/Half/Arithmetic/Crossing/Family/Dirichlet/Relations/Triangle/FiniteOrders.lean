import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.PhaseBounds
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound

/-! # Finiteness of the orders of one three-term mixed relation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set
open GaloisForLFunctions.HTGeometry.ExpZeroBound (expPoly card_lt_of_expPoly_eq_zero')

/-- Signed orders admitting the triangle after a finite-order twist of its directions. -/
def triangleOrders (E F : ℝ) (a b : ℚ) : Set ℝ :=
  {v | ∃ (U V : ℂ) (m : ℕ), 0 < m ∧ U^m=1 ∧ V^m=1 ∧
    (a : ℂ)*gapExp E v*U+(b : ℂ)*gapExp F v*V=1}

private theorem real_roots (E F A B : ℝ) (e : 0<E) (f : 0<F) (different : E ≠ F) :
    {v : ℝ | A*exp (v*E)+B*exp (v*F)=1}.Finite := by
  classical
  let rate : Fin 3 → ℝ := ![E,F,0]
  let coeff : Fin 3 → Polynomial ℝ := ![Polynomial.C A,Polynomial.C B,Polynomial.C (-1)]
  have inj : Function.Injective rate := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rate,different,different.symm,e.ne',f.ne',e.ne,f.ne]
  have live : ∃ i, coeff i ≠ 0 := ⟨2,by simp [coeff]⟩
  by_contra inf
  obtain ⟨S,sub,card⟩ := Set.Infinite.exists_subset_card_eq inf (∑ i, ((coeff i).natDegree+1))
  have bound := card_lt_of_expPoly_eq_zero' rate coeff inj live S (fun v hv => by
    have eq : A*exp (v*E)+B*exp (v*F)=1 := sub hv
    simp only [expPoly,rate,coeff,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Polynomial.eval_C,zero_mul,exp_zero,
      mul_one,mul_comm E v,mul_comm F v]
    linarith only [eq])
  exact bound.ne card

/-- Finiteness follows from the common torsion exponent and the real
exponential-polynomial zero bound for each fixed pair of angles. -/
theorem independent_triangle_finite {E F : ℝ} (e : 0<E) (f : 0<F) (different : E ≠ F)
    (ind : independentGaps E F) (one : algebraicPair E F 1) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (triangleOrders E F a b).Finite := by
  classical
  obtain ⟨N,pos,bounded⟩ := uniform_triangle_exponent ind one a b ha hb
  let S := Polynomial.nthRootsFinset N (1 : ℂ)
  let Z (U V : ℂ) := {v : ℝ | ((a : ℝ)*U.re)*exp (v*E)+((b : ℝ)*V.re)*exp (v*F)=1}
  have unionFinite : (⋃ U ∈ (↑S : Set ℂ), ⋃ V ∈ (↑S : Set ℂ), Z U V).Finite :=
    S.finite_toSet.biUnion (fun U _ => S.finite_toSet.biUnion (fun V _ => real_roots E F _ _ e f different))
  apply unionFinite.subset
  rintro v ⟨U,V,m,hm,hu,hv,eq⟩
  obtain ⟨up,vp⟩ := bounded v U V m hm hu hv eq
  have mem (z : ℂ) (h : z^N=1) : z ∈ (↑S : Set ℂ) := (Polynomial.mem_nthRootsFinset pos 1).mpr h
  refine Set.mem_iUnion.mpr ⟨U,Set.mem_iUnion.mpr ⟨mem U up,Set.mem_iUnion.mpr ⟨V,Set.mem_iUnion.mpr ⟨mem V vp,?_⟩⟩⟩⟩
  have realEq := congrArg Complex.re eq
  simp only [gapExp,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ratCast_re,Complex.ratCast_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.one_re] at realEq
  change _+_=1
  linear_combination realEq

#print axioms independent_triangle_finite

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
