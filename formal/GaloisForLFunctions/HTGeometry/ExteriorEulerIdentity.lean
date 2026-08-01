import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The exterior Euler identity

Summing creation against contraction over a basis multiplies a homogeneous exterior element by its
degree:

`∑ i, e i ∧ ι_{e i}ᵛ x = p · x` for `x` of exterior degree `p`.

This is the exterior half of the Koszul Euler identity `dh + hd = (r + p)·id`; the symmetric half
is mathlib's `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`.

The proof is an induction on a product of generators, using the creation--annihilation relation
`CliffordAlgebra.contractLeft_ι_mul` and the anticommutation of two generators.

* `ExteriorAlgebra.ι_mul_ι_add_swap_eq_zero` : anticommutation.
* `sum_ι_mul_contractLeft_listProd` : the Euler identity on a product of generators.
-/

namespace GaloisForLFunctions.HTGeometry

open CliffordAlgebra ExteriorAlgebra

section ExteriorEuler

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Two exterior generators anticommute. -/
theorem ExteriorAlgebra.ι_mul_ι_add_swap_eq_zero (a c : M) :
    ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R c
      + ExteriorAlgebra.ι R c * ExteriorAlgebra.ι R a = 0 := by
  simp

/-- Creation against a generator commutes past a contraction up to sign. -/
theorem ι_mul_ι_mul (a c : M) (y : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R c * (ExteriorAlgebra.ι R a * y)
      = -(ExteriorAlgebra.ι R a * (ExteriorAlgebra.ι R c * y)) := by
  have h := ExteriorAlgebra.ι_mul_ι_add_swap_eq_zero (R := R) a c
  have hc : ExteriorAlgebra.ι R c * ExteriorAlgebra.ι R a
      = -(ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R c) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  calc ExteriorAlgebra.ι R c * (ExteriorAlgebra.ι R a * y)
      = (ExteriorAlgebra.ι R c * ExteriorAlgebra.ι R a) * y := by rw [mul_assoc]
    _ = (-(ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R c)) * y := by rw [hc]
    _ = -(ExteriorAlgebra.ι R a * (ExteriorAlgebra.ι R c * y)) := by
        rw [neg_mul, mul_assoc]

/-- **The creation--annihilation relation.**  Contraction and creation anticommute up to the
value of the dual vector. -/
theorem contractLeft_ι_mul_add (d : Module.Dual R M) (a : M) (y : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (R := R) d (ExteriorAlgebra.ι R a * y)
      + ExteriorAlgebra.ι R a * (CliffordAlgebra.contractLeft (R := R) d y) = d a • y := by
  rw [CliffordAlgebra.contractLeft_ι_mul]
  abel

variable {n : Type*} [Fintype n]

/-- **The exterior Euler identity on a product of generators.**  Summing creation against
contraction over a basis multiplies a product of `k` generators by `k`. -/
theorem sum_ι_mul_contractLeft_listProd (b : Module.Basis n R M) (l : List M) :
    ∑ i, ExteriorAlgebra.ι R (b i)
        * (CliffordAlgebra.contractLeft (R := R) (b.coord i)
            ((l.map (ExteriorAlgebra.ι R)).prod))
      = l.length • ((l.map (ExteriorAlgebra.ι R)).prod) := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have hprod : ((a :: l).map (ExteriorAlgebra.ι R)).prod
          = ExteriorAlgebra.ι R a * ((l.map (ExteriorAlgebra.ι R)).prod) := by
        simp
      set P : ExteriorAlgebra R M := (l.map (ExteriorAlgebra.ι R)).prod with hP
      have hstep : ∀ i : n,
          ExteriorAlgebra.ι R (b i)
              * (CliffordAlgebra.contractLeft (R := R) (b.coord i)
                  (ExteriorAlgebra.ι R a * P))
            = (b.coord i) a • ExteriorAlgebra.ι R (b i) * P
              + ExteriorAlgebra.ι R a
                * (ExteriorAlgebra.ι R (b i)
                    * CliffordAlgebra.contractLeft (R := R) (b.coord i) P) := by
        intro i
        rw [CliffordAlgebra.contractLeft_ι_mul, mul_sub, smul_mul_assoc,
          ι_mul_ι_mul (R := R) a (b i)]
        noncomm_ring
      rw [hprod, Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib]
      have hfirst : ∑ i, (b.coord i) a • ExteriorAlgebra.ι R (b i) * P
          = ExteriorAlgebra.ι R a * P := by
        rw [← Finset.sum_mul]
        congr 1
        have hsum : ∑ i, (b.coord i) a • ExteriorAlgebra.ι R (b i)
            = ExteriorAlgebra.ι R (∑ i, (b.coord i) a • b i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
        rw [hsum]
        congr 1
        simp only [Module.Basis.coord_apply]
        exact b.sum_repr a
      have hsecond : ∑ i, ExteriorAlgebra.ι R a
            * (ExteriorAlgebra.ι R (b i)
              * CliffordAlgebra.contractLeft (R := R) (b.coord i) P)
          = ExteriorAlgebra.ι R a * (l.length • P) := by
        rw [← Finset.mul_sum, ih]
      rw [hfirst, hsecond, List.length_cons, mul_smul_comm, succ_nsmul, add_comm]

/-- **The exterior Euler identity on the `p`-th exterior power.**  Summing creation against
contraction over a basis is multiplication by the degree. -/
theorem sum_ι_mul_contractLeft_of_mem_exteriorPower (b : Module.Basis n R M) (p : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ (⋀[R]^p M)) :
    ∑ i, ExteriorAlgebra.ι R (b i)
        * (CliffordAlgebra.contractLeft (R := R) (b.coord i) x) = p • x := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      have hlist := sum_ι_mul_contractLeft_listProd b (List.ofFn v)
      rw [List.map_ofFn, List.length_ofFn] at hlist
      rw [ExteriorAlgebra.ιMulti_apply]
      exact hlist
  | zero => simp
  | add y z _ _ hy hz =>
      have hsplit : ∀ i : n, ExteriorAlgebra.ι R (b i)
          * (CliffordAlgebra.contractLeft (R := R) (b.coord i) (y + z))
          = ExteriorAlgebra.ι R (b i)
              * (CliffordAlgebra.contractLeft (R := R) (b.coord i) y)
            + ExteriorAlgebra.ι R (b i)
              * (CliffordAlgebra.contractLeft (R := R) (b.coord i) z) := by
        intro i
        rw [map_add, mul_add]
      rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hy, hz, smul_add]
  | smul a y _ hy =>
      have hsplit : ∀ i : n, ExteriorAlgebra.ι R (b i)
          * (CliffordAlgebra.contractLeft (R := R) (b.coord i) (a • y))
          = a • (ExteriorAlgebra.ι R (b i)
              * (CliffordAlgebra.contractLeft (R := R) (b.coord i) y)) := by
        intro i
        rw [map_smul, mul_smul_comm]
      rw [Finset.sum_congr rfl fun i _ => hsplit i, ← Finset.smul_sum, hy, smul_comm]

end ExteriorEuler

end GaloisForLFunctions.HTGeometry
