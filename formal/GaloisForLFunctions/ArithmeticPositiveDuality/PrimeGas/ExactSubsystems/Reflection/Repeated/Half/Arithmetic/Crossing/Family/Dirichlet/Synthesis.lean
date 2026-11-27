import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Zeros
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Responses

/-! # Realizing a signed Dirichlet polynomial by a positive integer-shell spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real MvPolynomial

private theorem pair_exp (t x y : ℝ) :
    exp (t*(x-y))=exp (t*x)*exp (-t*y) := by
  rw [← exp_add]
  congr 1
  ring

/-- Double summation symmetrizes the signed coefficients. Each summand is a
direct sum of reflected or unreflected copies of a symmetric tensor product. -/
theorem reciprocal_product (P : PolynomialRing) :
    (fun t => 2*originTrace t*value t P*value (-t) P) ∈ responses := by
  classical
  let c (i : Exponent) := coeff i P
  let x (i : Exponent) := energy (label i)
  let block (i j : Exponent) : ℝ → ℝ :=
    (c i*c j) • (fun t => (exp (t*(x i-x j))+exp (-t*(x i-x j)))*originTrace t)
  have blocks (i j : Exponent) : block i j ∈ responses :=
    responses.zsmul_mem (pair_mem origin_mem (gap_mem (label i) (label j))) _
  have total : (∑ i ∈ P.support, ∑ j ∈ P.support, block i j) ∈ responses :=
    responses.sum_mem fun i _ => responses.sum_mem fun j _ => blocks i j
  convert total using 1
  funext t
  let w (s : ℝ) (i : Exponent) := (c i : ℝ)*exp (s*x i)
  have evaluation (s : ℝ) : value s P=∑ i ∈ P.support, w s i := by
    simp only [value_sum,w,c,x,shellPower_exp]
  let A (i j : Exponent) := w t i*w (-t) j*originTrace t
  have entry (i j : Exponent) : block i j t = A i j+A j i := by
    change (c i*c j) • ((exp (t*(x i-x j))+exp (-t*(x i-x j)))*originTrace t)=_
    simp only [zsmul_eq_mul,Int.cast_mul,A,w,pair_exp,neg_neg]
    ring
  have direct : (∑ i ∈ P.support, ∑ j ∈ P.support, A i j)=
      (value t P*value (-t) P)*originTrace t := by
    rw [evaluation,evaluation]
    simp only [A,sum_mul,mul_sum]
    exact sum_comm
  have reversed : (∑ i ∈ P.support, ∑ j ∈ P.support, A j i)=
      ∑ i ∈ P.support, ∑ j ∈ P.support, A i j := sum_comm
  simp only [Finset.sum_apply,entry,sum_add_distrib]
  rw [reversed,direct]
  ring

/-- The positive blind set is exactly the set of positive absolute values of
real roots of the polynomial restricted to the prime powers. -/
theorem polynomial_spectrum (P : PolynomialRing) (hp : P ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → ℕ+), ¬Reflects (energy ∘ a) ∧
      ∀ t : ℝ, 0<t → (agrees (energy ∘ a) t ↔ value t P=0 ∨ value (-t) P=0) := by
  obtain ⟨n,a,trace⟩ := integer_shells (reciprocal_product P)
  have test (t : ℝ) (ht : 0<t) : agrees (energy ∘ a) t ↔ value t P=0 ∨ value (-t) P=0 := by
    rw [agrees_odd,trace]
    simp only [mul_eq_zero,(origin_pos ht).ne',OfNat.ofNat_ne_zero,false_or]
  obtain ⟨u,hu,h₁,h₂⟩ := detecting_order hp
  exact ⟨n,a,fun h => ((test u hu).mp (reflection_agrees h u)).elim h₁ h₂,test⟩

#print axioms reciprocal_product
#print axioms polynomial_spectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
