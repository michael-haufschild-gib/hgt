import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticTraceNorm
import Mathlib.NumberTheory.GaussSum

/-!
# Quadratic lifting of finite-field Gauss sums

Ordered base-field pairs and quadratic trace-and-norm fibers have total
multiplicity two. Summing any weight over this identity gives quadratic
Gauss lifting. The correction term vanishes as soon as either character
is nontrivial. The argument works in every characteristic.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset
open scoped Classical
variable {K L R : Type*} [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [CommRing R]
variable (hdegree : Module.finrank K L = 2)

private theorem sum_comp_fiber_card {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (F : B → R) :
    (∑ a : A, F (f a)) =
      ∑ b : B, ((Finset.univ.filter (fun a : A => f a = b)).card : R) * F b := by
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := f)
    (fun a _ => Finset.mem_univ (f a)) (fun a => F (f a))
  rw [← h]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ a ∈ Finset.univ.filter (fun a : A => f a = b), F (f a)) =
        ∑ _a ∈ Finset.univ.filter (fun a : A => f a = b), F b :=
      Finset.sum_congr rfl (fun a ha => congrArg F (Finset.mem_filter.mp ha).2)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Every weight has total multiplicity two across ordered base-field pairs and quadratic trace-and-norm fibers. -/
theorem finiteField_quadratic_weighted_fibers (F : K × K → R) :
    (∑ x : K × K, F (x.1 + x.2, x.1 * x.2)) +
      (∑ x : L, F (Algebra.trace K L x, Algebra.norm K x)) = 2 * ∑ v : K × K, F v := by
  let f : K × K → K × K := fun x => (x.1 + x.2, x.1 * x.2)
  let g : L → K × K := fun x => (Algebra.trace K L x, Algebra.norm K x)
  change (∑ x : K × K, F (f x)) + (∑ x : L, F (g x)) = _
  rw [sum_comp_fiber_card f F, sum_comp_fiber_card g F, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rcases v with ⟨t, n⟩
  have hv : (Finset.univ.filter (fun x : K × K => f x = (t, n))).card +
      (Finset.univ.filter (fun x : L => g x = (t, n))).card = 2 := by
    simpa only [f, g, Prod.mk.injEq] using finiteField_quadratic_trace_norm_fiber_card hdegree t n
  rw [← add_mul, ← Nat.cast_add, hv]

/-- The exact quadratic lifting identity includes an explicit correction for two trivial characters. -/
theorem finiteField_quadratic_gauss_formula (χ : MulChar K R) (ψ : AddChar K R) :
    (∑ x : L, χ (Algebra.norm K x) * ψ (Algebra.trace K L x)) =
      2 * ((∑ x : K, χ x) * ∑ x : K, ψ x) - (gaussSum χ ψ) ^ 2 := by
  have h := finiteField_quadratic_weighted_fibers hdegree (fun v : K × K => χ v.2 * ψ v.1)
  have hfirst : (∑ x : K × K, χ (x.1 * x.2) * ψ (x.1 + x.2)) = (gaussSum χ ψ) ^ 2 := by
    rw [Fintype.sum_prod_type, gaussSum, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [map_mul, AddChar.map_add_eq_mul]
    ring
  have htotal : (∑ v : K × K, χ v.2 * ψ v.1) = (∑ x : K, χ x) * ∑ x : K, ψ x := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
  rw [hfirst, htotal] at h
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact h

/-- A nontrivial multiplicative or additive character gives quadratic Gauss lifting with the negative square. -/
theorem finiteField_quadratic_gauss_lift [IsDomain R] (χ : MulChar K R) (ψ : AddChar K R)
    (h : χ ≠ 1 ∨ ψ ≠ 1) :
    (∑ x : L, χ (Algebra.norm K x) * ψ (Algebra.trace K L x)) = -((gaussSum χ ψ) ^ 2) := by
  rcases h with hχ | hψ
  · rw [finiteField_quadratic_gauss_formula hdegree, MulChar.sum_eq_zero_of_ne_one hχ,
      zero_mul, mul_zero, zero_sub]
  · rw [finiteField_quadratic_gauss_formula hdegree, AddChar.sum_eq_zero_of_ne_one hψ,
      mul_zero, mul_zero, zero_sub]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
