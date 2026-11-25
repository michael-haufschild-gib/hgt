import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LineActions
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Balanced spectral charges of monomials away from a closing pair -/

open Finset MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

abbrev Outside {I : Type*} (i j : I) := {k : I // k≠i ∧ k≠j}

/-- A monomial contributes its multiplicity at each free energy and
subtracts the total multiplicity at the reference energy. -/
def monomialWeight {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (d : Outside i j →₀ ℕ) (k : I) : ℝ :=
  ∑ l : Outside i j, (d l:ℝ)*((if k=l.val then 1 else 0)-(if k=j then 1 else 0))

theorem monomialWeight_balanced {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (d : Outside i j →₀ ℕ) :
    ∑ k, monomialWeight i j d k=0 := by
  unfold monomialWeight
  rw [sum_comm]
  simp only [←mul_sum,sum_sub_distrib,sum_ite_eq',mem_univ,if_true,sub_self,mul_zero,sum_const_zero]

theorem monomialWeight_outside {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (d : Outside i j →₀ ℕ)
    (l : Outside i j) : monomialWeight i j d l.val=(d l:ℝ) := by
  simp [monomialWeight,l.property.2,Subtype.val_inj,mul_ite]

theorem monomialWeight_action {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (d : Outside i j →₀ ℕ)
    (E : I → ℝ) : normalizedAction (monomialWeight i j d) E i j =
      ∑ l : Outside i j, (d l:ℝ)*((E l.val-E j)/(E i-E j)) := by
  unfold normalizedAction
  have he : ∑ k, monomialWeight i j d k*E k=∑ l : Outside i j, (d l:ℝ)*(E l.val-E j) := by
    simp only [monomialWeight,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    simp only [mul_assoc,←mul_sum,sub_mul,ite_mul,one_mul,zero_mul,sum_sub_distrib,
      sum_ite_eq',mem_univ,if_true]
  rw [he,sum_div]
  exact sum_congr rfl fun _ _ => mul_div_assoc .. 

/-- Evaluating a phase polynomial gives an exponential sum over its
actual support with precisely these balanced actions. -/
theorem normalized_polynomial_expansion {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [Algebra K ℂ]
    (i j : I) (p : MvPolynomial (Outside i j) K) (E : I → ℝ) (χ : ℂ) :
    aeval (fun l : Outside i j => Complex.exp (χ*(((E l.val-E j)/(E i-E j):ℝ):ℂ))) p =
      ∑ d : p.support, algebraMap K ℂ (p.coeff d.val)*Complex.exp (χ*(normalizedAction (monomialWeight i j d.val) E i j:ℝ)) := by
  classical
  rw [Finset.sum_coe_sort p.support (fun d => algebraMap K ℂ (p.coeff d)*
    Complex.exp (χ*(normalizedAction (monomialWeight i j d) E i j:ℝ))),aeval_def,eval₂_eq']
  apply sum_congr rfl
  intro d _
  change algebraMap K ℂ (p.coeff d)*(∏ l : Outside i j, Complex.exp (χ*(((E l.val-E j)/(E i-E j):ℝ):ℂ))^(d l))=_
  congr 1
  simp only [←Complex.exp_nat_mul,←Complex.exp_sum,monomialWeight_action,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_natCast,mul_sum]
  congr 1
  exact sum_congr rfl fun _ _ => by ring

#print axioms normalized_polynomial_expansion
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
