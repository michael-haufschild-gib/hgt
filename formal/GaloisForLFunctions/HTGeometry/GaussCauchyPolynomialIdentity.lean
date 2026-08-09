import GaloisForLFunctions.HTGeometry.GaussNodeDenominator

/-!
# The finite-stage Cauchy transform as a polynomial identity

The finite-stage closed form `∑ₓ χ(x)/(x − z) = −s₀·q_{n+1}(z)/p_{n+1}(z)` holds for every real `z`
off the nodes.  Clearing both denominators turns it into an identity of *polynomials*,

`N_n · p_{n+1} = −s₀ · q_{n+1} · D_n`,

where `N_n` is the cleared Cauchy numerator and `D_n = ∏_{y ∈ nodes} (y − X)`.  A polynomial
identity valid off a finite set is valid identically, so the same relation holds after any ring
map — in particular at every complex point.  This is what carries the finite stage of the Weyl-disc
argument from the real line to the complex plane.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The cleared numerator of the finite-stage Cauchy transform, as a polynomial. -/
noncomputable def gaussCauchyNumerator (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ x ∈ gaussNodes s n,
    C (christoffel s n x) * ∏ y ∈ (gaussNodes s n).erase x, (C y - X)

/-- The node product `∏_{y} (y − X)`. -/
noncomputable def gaussNodeProduct (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ y ∈ gaussNodes s n, (C y - X)

theorem eval_gaussNodeProduct (s : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (gaussNodeProduct s n).eval z = ∏ y ∈ gaussNodes s n, (y - z) := by
  rw [gaussNodeProduct, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun y _ => by simp

theorem eval_gaussCauchyNumerator (s : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (gaussCauchyNumerator s n).eval z
      = ∑ x ∈ gaussNodes s n,
          christoffel s n x * ∏ y ∈ (gaussNodes s n).erase x, (y - z) := by
  rw [gaussCauchyNumerator, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  exact Finset.prod_congr rfl fun y _ => by simp

/-- Clearing the denominator of the finite-stage Cauchy sum, over the reals. -/
theorem gaussSum_mul_nodeProduct (s : ℕ → ℝ) (n : ℕ) {z : ℝ}
    (hz : ∀ y ∈ gaussNodes s n, y - z ≠ 0) :
    (∑ x ∈ gaussNodes s n, christoffel s n x / (x - z)) * ∏ y ∈ gaussNodes s n, (y - z)
      = ∑ x ∈ gaussNodes s n,
          christoffel s n x * ∏ y ∈ (gaussNodes s n).erase x, (y - z) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mul_prod_erase (gaussNodes s n) (fun y => y - z) hx]
  have hxz : x - z ≠ 0 := hz x hx
  rw [mul_comm (x - z), div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self hxz, mul_one]

/-- **The finite-stage closed form as a polynomial identity.**  Valid identically, hence after any
ring map — in particular at every complex point. -/
theorem gaussCauchy_polynomial_identity (h : PositiveMomentForm s) (n : ℕ) :
    gaussCauchyNumerator s n * monicOrtho s (n + 1)
      = C (-(s 0)) * secondKind s (n + 1) * gaussNodeProduct s n := by
  classical
  set S : Set ℝ := {z : ℝ | (monicOrtho s (n + 1)).eval z ≠ 0} with hS
  have hSinf : S.Infinite := by
    have hfin : {z : ℝ | (monicOrtho s (n + 1)).eval z = 0}.Finite := by
      have hsub : {z : ℝ | (monicOrtho s (n + 1)).eval z = 0}
          ⊆ (monicOrtho s (n + 1)).roots.toFinset := by
        intro z hz
        simp only [Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset,
          Polynomial.mem_roots (monicOrtho_ne_zero s (n + 1))]
        exact hz
      exact Set.Finite.subset ((monicOrtho s (n + 1)).roots.toFinset).finite_toSet hsub
    have := Set.Finite.infinite_compl hfin
    refine this.mono ?_
    intro z hz
    simpa [hS] using hz
  refine Polynomial.eq_of_infinite_eval_eq _ _ (hSinf.mono ?_)
  intro z hz
  have hzne : (monicOrtho s (n + 1)).eval z ≠ 0 := hz
  have hnodes : ∀ y ∈ gaussNodes s n, y - z ≠ 0 := by
    intro y hy hcon
    apply hzne
    have : y = z := by linarith [sub_eq_zero.mp hcon]
    rw [← this]
    exact (mem_gaussNodes_iff n y).mp hy
  have hratio := gaussSum_cauchy_eq_secondKind_ratio h n hzne
  have hclear := gaussSum_mul_nodeProduct s n hnodes
  have hprodne : ∏ y ∈ gaussNodes s n, (y - z) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hnodes
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C,
    eval_gaussCauchyNumerator, eval_gaussNodeProduct]
  rw [← hclear, hratio]
  field_simp

end HTGeometry
