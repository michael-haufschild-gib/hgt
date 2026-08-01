import GaloisForLFunctions.HTGeometry.ExteriorEulerIdentity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The Koszul Euler identity

On `Sym(L*) ⊗ Λ L`, the Koszul differential `d = ∑ᵢ Xᵢ ⊗ ι_{eᵢ*}` and the homotopy
`h = ∑ᵢ ∂ᵢ ⊗ (eᵢ ∧ ·)` satisfy

`d h + h d = (r + p) · id`

on the summand of bidegree `(r, p)`.  Expanding the double sum, the polynomial Leibniz rule
`∂ⱼ(Xᵢ f) = Xᵢ ∂ⱼ f + δᵢⱼ f` and the creation--annihilation relation collapse it to
`(∑ᵢ Xᵢ∂ᵢ) ⊗ id + id ⊗ (∑ᵢ eᵢ ∧ ι_{eᵢ*})`, which is `r + p` by the two Euler identities.

* `koszul_euler_tmul` : the identity on a pure tensor of a homogeneous polynomial and a
  homogeneous exterior element.
-/

namespace GaloisForLFunctions.HTGeometry

open CliffordAlgebra ExteriorAlgebra TensorProduct

section KoszulEuler

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The dual basis pairing is the Kronecker delta. -/
theorem coord_basis_apply (b : Module.Basis n R M) (i j : n) :
    (b.coord i) (b j) = if i = j then (1 : R) else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The Koszul Euler identity on a pure tensor.** -/
theorem koszul_euler_tmul (b : Module.Basis n R M) {f : MvPolynomial n R} {r : ℕ}
    (hf : f.IsHomogeneous r) {x : ExteriorAlgebra R M} {p : ℕ} (hx : x ∈ (⋀[R]^p M)) :
    ∑ i : n, ∑ j : n,
        ((MvPolynomial.X i * (MvPolynomial.pderiv j) f) ⊗ₜ[R]
            (CliffordAlgebra.contractLeft (R := R) (b.coord i)
              (ExteriorAlgebra.ι R (b j) * x))
          + ((MvPolynomial.pderiv j) (MvPolynomial.X i * f)) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (b j)
              * CliffordAlgebra.contractLeft (R := R) (b.coord i) x))
      = (r + p) • (f ⊗ₜ[R] x) := by
  have hterm : ∀ i j : n,
      ((MvPolynomial.X i * (MvPolynomial.pderiv j) f) ⊗ₜ[R]
          (CliffordAlgebra.contractLeft (R := R) (b.coord i)
            (ExteriorAlgebra.ι R (b j) * x))
        + ((MvPolynomial.pderiv j) (MvPolynomial.X i * f)) ⊗ₜ[R]
          (ExteriorAlgebra.ι R (b j)
            * CliffordAlgebra.contractLeft (R := R) (b.coord i) x))
      = (MvPolynomial.X i * (MvPolynomial.pderiv j) f) ⊗ₜ[R]
            ((if i = j then (1 : R) else 0) • x)
        + ((if j = i then (1 : R) else 0) • f) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (b j)
              * CliffordAlgebra.contractLeft (R := R) (b.coord i) x) := by
    intro i j
    have hleib : (MvPolynomial.pderiv j) (MvPolynomial.X i * f)
        = MvPolynomial.X i * (MvPolynomial.pderiv j) f
          + (if j = i then (1 : R) else 0) • f := by
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases h : j = i
      · simp [h]
        ring
      · simp [h, Ne.symm h]
    rw [hleib, TensorProduct.add_tmul, ← add_assoc, ← TensorProduct.tmul_add,
      contractLeft_ι_mul_add, coord_basis_apply]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  have hinner : ∀ i : n,
      ∑ j : n, ((MvPolynomial.X i * (MvPolynomial.pderiv j) f) ⊗ₜ[R]
            ((if i = j then (1 : R) else 0) • x)
          + ((if j = i then (1 : R) else 0) • f) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (b j)
              * CliffordAlgebra.contractLeft (R := R) (b.coord i) x))
      = (MvPolynomial.X i * (MvPolynomial.pderiv i) f) ⊗ₜ[R] x
        + f ⊗ₜ[R] (ExteriorAlgebra.ι R (b i)
            * CliffordAlgebra.contractLeft (R := R) (b.coord i) x) := by
    intro i
    rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h) |>.trans ?_
      · rw [if_neg (Ne.symm hj), zero_smul, TensorProduct.tmul_zero]
      · rw [if_pos rfl, one_smul]
    · refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h) |>.trans ?_
      · rw [if_neg hj, zero_smul, TensorProduct.zero_tmul]
      · rw [if_pos rfl, one_smul]
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_add_distrib,
    ← TensorProduct.sum_tmul, ← TensorProduct.tmul_sum,
    hf.sum_X_mul_pderiv, sum_ι_mul_contractLeft_of_mem_exteriorPower b p hx,
    TensorProduct.tmul_smul, add_smul]
  simp [TensorProduct.smul_tmul']

end KoszulEuler

end GaloisForLFunctions.HTGeometry
