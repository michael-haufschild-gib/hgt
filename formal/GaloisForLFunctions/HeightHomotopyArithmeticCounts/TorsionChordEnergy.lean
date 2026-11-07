import GaloisForLFunctions.HeightHomotopyArithmeticCounts.RadialLogarithmicKernel
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Exact inverse-chord energy of roots of unity

The first two derivatives of the geometric-sum polynomial at one determine
its reciprocal-root sums. On the unit circle, the inverse squared chord is
the difference of those reciprocal powers. The resulting energy is
`(L²-1)/12` for the nontrivial roots of unity of positive order `L`.
-/

noncomputable section
open Finset Polynomial Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

private theorem logarithmicJet_step (x p s t : ℂ) (hx : x ≠ 0) :
    p+x*(p*s) = x*p*(x⁻¹+s) ∧
    p*s+(p*s+x*(p*(s^2-t))) =
      x*p*((x⁻¹+s)^2-((x^2)⁻¹+t)) := by
  constructor
  · field_simp [hx]
  · field_simp [hx]
    ring

/-- Division-free identities for the first two logarithmic derivatives of a finite product. -/
private theorem polynomial_product_jets {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℂ) (w : ℂ) (hne : ∀ i ∈ S, w-a i ≠ 0) :
    eval w (derivative (∏ i ∈ S, (X-C (a i)))) =
      eval w (∏ i ∈ S, (X-C (a i))) * ∑ i ∈ S, (w-a i)⁻¹ ∧
    eval w (derivative (derivative (∏ i ∈ S, (X-C (a i))))) =
      eval w (∏ i ∈ S, (X-C (a i))) *
        ((∑ i ∈ S, (w-a i)⁻¹)^2 - ∑ i ∈ S, ((w-a i)^2)⁻¹) := by
  revert hne
  induction S using Finset.induction_on with
  | empty => intro hne; simp
  | @insert j S hj ih =>
    intro hne
    obtain ⟨hfirst, hsecond⟩ := ih (fun i hi => hne i (mem_insert_of_mem hi))
    have hx := hne j (mem_insert_self j S)
    simp only [prod_insert hj, sum_insert hj, derivative_mul, derivative_add,
      derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C]
    rw [hfirst, hsecond]
    exact logarithmicJet_step (w-a j) (eval w (∏ i ∈ S, (X-C (a i))))
      (∑ i ∈ S, (w-a i)⁻¹) (∑ i ∈ S, ((w-a i)^2)⁻¹) hx

private def geometricPolynomial (n : ℕ) : Polynomial ℂ := ∑ k ∈ range (n+1), X^k

private theorem geometricPolynomial_succ (n : ℕ) :
    geometricPolynomial (n+1) = geometricPolynomial n + X^(n+1) := by
  unfold geometricPolynomial
  rw [sum_range_succ]

/-- The first three polynomial moments at one, obtained by adjoining a monomial. -/
private theorem geometricPolynomial_values (n : ℕ) :
    eval 1 (geometricPolynomial n) = (n:ℂ)+1 ∧
    2*eval 1 (derivative (geometricPolynomial n)) = (n:ℂ)*(n+1) ∧
    3*eval 1 (derivative (derivative (geometricPolynomial n))) =
      (n:ℂ)*(n+1)*(n-1) := by
  induction n with
  | zero => simp [geometricPolynomial]
  | succ n ih =>
    simp only [geometricPolynomial_succ, derivative_add, derivative_X_pow,
      derivative_C_mul, Nat.add_sub_cancel, eval_add, eval_mul, eval_C,
      eval_pow, eval_X, one_pow, mul_one]
    push_cast
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2

private theorem geometricPolynomial_factorization (n : ℕ) :
    geometricPolynomial n =
      ∏ u ∈ (nthRootsFinset (n+1) (1:ℂ)).erase 1, (X-C u) := by
  classical
  have hm : (1:ℂ) ∈ nthRootsFinset (n+1) 1 :=
    (mem_nthRootsFinset (Nat.succ_pos n) 1).mpr (one_pow _)
  have h := Polynomial.X_pow_sub_one_eq_prod (Nat.succ_pos n)
    (Complex.isPrimitiveRoot_exp (n+1) (Nat.succ_ne_zero n))
  rw [← mul_geom_sum, ← Finset.mul_prod_erase _ _ hm, C_1] at h
  exact mul_left_cancel₀ (by simpa only [C_1] using Polynomial.X_sub_C_ne_zero (1:ℂ)) h

/-- On the unit circle, inverse squared distance is a difference of reciprocal powers. -/
private theorem unit_inverse_chord (u : ℂ) (hu : ‖u‖=1) (hne : u≠1) :
    (1:ℂ)/(‖1-u‖:ℂ)^2 = (1-u)⁻¹-((1-u)^2)⁻¹ := by
  have huc : u*conj u=1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hd := Complex.mul_conj (1-u)
  rw [Complex.normSq_eq_norm_sq] at hd
  push_cast at hd
  simp only [map_sub, map_one] at hd
  have hpoly : -u*(‖1-u‖:ℂ)^2=(1-u)^2 := by
    rw [← hd]
    calc -u*((1-u)*(1-conj u)) = (1-u)*(u*conj u-u) := by ring
      _ = (1-u)*(1-u) := by rw [huc]
      _ = (1-u)^2 := by ring
  have hdne : (‖1-u‖:ℂ)≠0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
  field_simp [hdne, sub_ne_zero.mpr hne.symm]
  linear_combination -hpoly

/-- Full inverse-chord energy with the singular point one removed. -/
def unityChordEnergy (L : ℕ) : ℝ :=
  ∑ u ∈ (nthRootsFinset L (1:ℂ)).erase 1, 1/‖1-u‖^2

/-- The exact inverse-chord energy of all nontrivial roots of unity. -/
theorem unityChordEnergy_succ (n : ℕ) :
    unityChordEnergy (n+1) = (n:ℝ)*(n+2)/12 := by
  classical
  let U := (nthRootsFinset (n+1) (1:ℂ)).erase 1
  let A : ℂ := ∑ u ∈ U, (1-u)⁻¹
  let B : ℂ := ∑ u ∈ U, ((1-u)^2)⁻¹
  have hne : ∀ u ∈ U, 1-u ≠ 0 := fun u hu =>
    sub_ne_zero.mpr (ne_of_mem_erase hu).symm
  have hjets := polynomial_product_jets U (fun u => u) 1 hne
  have hfac := geometricPolynomial_factorization n
  rw [← hfac] at hjets
  obtain ⟨h0, h1, h2⟩ := geometricPolynomial_values n
  rw [h0] at hjets
  rw [hjets.1] at h1
  rw [hjets.2] at h2
  have hn : (n:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
  have hA : A=(n:ℂ)/2 := by
    apply mul_left_cancel₀ hn
    linear_combination (1/2:ℂ)*h1
  change 3*((n+1)*(A^2-B)) = (n:ℂ)*(n+1)*(n-1) at h2
  rw [hA] at h2
  have hsum : (∑ u ∈ U, (1:ℂ)/(‖1-u‖:ℂ)^2) = A-B := by
    calc
      (∑ u ∈ U, (1:ℂ)/(‖1-u‖:ℂ)^2) =
          ∑ u ∈ U, ((1-u)⁻¹-((1-u)^2)⁻¹) := by
        apply sum_congr rfl
        intro u hu
        have hunit := Complex.norm_eq_one_of_pow_eq_one
          ((mem_nthRootsFinset (Nat.succ_pos n) 1).mp (mem_of_mem_erase hu))
          (Nat.succ_ne_zero n)
        exact unit_inverse_chord u hunit (ne_of_mem_erase hu)
      _ = A-B := sum_sub_distrib _ _
  apply Complex.ofReal_injective
  unfold unityChordEnergy
  push_cast
  rw [hsum, hA]
  apply mul_left_cancel₀ hn
  linear_combination (1/3:ℂ)*h2

/-- The full-root energy in terms of its positive conductor. -/
theorem unityChordEnergy_of_pos (L : ℕ) (hL : 0 < L) :
    unityChordEnergy L = ((L:ℝ)^2-1)/12 := by
  cases L with
  | zero => exact (Nat.not_lt_zero _ hL).elim
  | succ n =>
    rw [unityChordEnergy_succ]
    push_cast
    ring

#print axioms unityChordEnergy_succ
#print axioms unityChordEnergy_of_pos
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
