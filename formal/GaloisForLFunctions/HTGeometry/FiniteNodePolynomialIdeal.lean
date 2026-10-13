import GaloisForLFunctions.HTGeometry.LinearPartialFractions
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

/-! Distinct finite nodes identify polynomial observables modulo their monic nodal polynomial. -/

namespace GaloisForLFunctions.HTGeometry

theorem finite_node_polynomial_eval_zero_iff_dvd
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (p : Polynomial ℝ) :
    (∀ i, p.eval (x i) = 0) ↔ Lagrange.nodal Finset.univ x ∣ p := by
  classical
  constructor
  · intro h
    exact prod_X_sub_C_dvd_of_isRoot hx (fun i _ => h i)
  · rintro ⟨q, hq⟩ i
    rw [hq, Polynomial.eval_mul, Lagrange.eval_nodal_at_node (Finset.mem_univ i), zero_mul]

theorem finite_node_polynomial_eval_eq_iff_dvd
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (p q : Polynomial ℝ) :
    (∀ i, p.eval (x i) = q.eval (x i)) ↔ Lagrange.nodal Finset.univ x ∣ p - q := by
  simpa only [Polynomial.eval_sub, sub_eq_zero] using
    finite_node_polynomial_eval_zero_iff_dvd x hx (p - q)

theorem finite_node_polynomial_remainder_eval
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (p : Polynomial ℝ) (i : ι) :
    (p %ₘ Lagrange.nodal Finset.univ x).eval (x i) = p.eval (x i) := by
  rw [Polynomial.modByMonic_eq_sub_mul_div]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Lagrange.eval_nodal_at_node (Finset.mem_univ i), zero_mul, sub_zero]

theorem finite_node_polynomial_eval_eq_iff_remainder
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x) (p q : Polynomial ℝ) :
    (∀ i, p.eval (x i) = q.eval (x i)) ↔
      p %ₘ Lagrange.nodal Finset.univ x = q %ₘ Lagrange.nodal Finset.univ x := by
  constructor
  · intro h
    exact Polynomial.modByMonic_eq_of_dvd_sub Lagrange.nodal_monic
      ((finite_node_polynomial_eval_eq_iff_dvd x hx p q).mp h)
  · intro h i
    calc
      p.eval (x i) = (p %ₘ Lagrange.nodal Finset.univ x).eval (x i) :=
        (finite_node_polynomial_remainder_eval x p i).symm
      _ = (q %ₘ Lagrange.nodal Finset.univ x).eval (x i) :=
        congrArg (fun t : Polynomial ℝ => t.eval (x i)) h
      _ = q.eval (x i) := finite_node_polynomial_remainder_eval x q i

theorem finite_node_polynomial_constant_iff_unique_factor
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : Function.Injective x)
    (i₀ : ι) (p : Polynomial ℝ) :
    (∀ i, p.eval (x i) = p.eval (x i₀)) ↔
      ∃! q : Polynomial ℝ,
        p = Polynomial.C (p.eval (x i₀)) + Lagrange.nodal Finset.univ x * q := by
  classical
  constructor
  · intro h
    have hdiv := (finite_node_polynomial_eval_eq_iff_dvd x hx p
      (Polynomial.C (p.eval (x i₀)))).mp (by simpa only [Polynomial.eval_C] using h)
    obtain ⟨q, hq⟩ := hdiv
    have hdecomp : p = Polynomial.C (p.eval (x i₀)) + Lagrange.nodal Finset.univ x * q := by
      simpa only [add_comm] using sub_eq_iff_eq_add.mp hq
    refine ⟨q, hdecomp, ?_⟩
    intro q' hq'
    have hN : Lagrange.nodal Finset.univ x ≠ 0 := Lagrange.nodal_ne_zero
    exact mul_left_cancel₀ hN (add_left_cancel (hq'.symm.trans hdecomp))
  · rintro ⟨q, hq, _⟩ i
    have h := congrArg (fun t : Polynomial ℝ => t.eval (x i)) hq
    simpa only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Lagrange.eval_nodal_at_node (Finset.mem_univ i), zero_mul, add_zero] using h

end GaloisForLFunctions.HTGeometry
