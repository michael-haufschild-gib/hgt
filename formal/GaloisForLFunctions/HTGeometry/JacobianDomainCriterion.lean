import GaloisForLFunctions.HTGeometry.ArithmeticFunctionJacobianCriterion
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Jacobian criterion with a nonzero domain-valued determinant

The scalar-Jacobian criterion is insufficient for prime-power-supported arithmetic functions:
their basic derivatives are point masses, so the Jacobian lives in the arithmetic-function
domain rather than in the scalar field.  A nonzero determinant is nevertheless enough.  Cramer's
adjugate identity kills every evaluated partial derivative in an integral domain.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial

noncomputable section

variable {K R ι : Type*} [Field K] [CommRing R] [Algebra K R]
  [Fintype ι] [DecidableEq ι]

/-- A square matrix over an integral domain with nonzero determinant has trivial kernel. -/
theorem vec_zero_of_det_ne_zero
    [IsDomain R] (M : Matrix ι ι R) (hM : M.det ≠ 0) (w : ι → R)
    (h : ∀ i, ∑ j, M i j * w j = 0) : ∀ j, w j = 0 := by
  classical
  have hmul : M *ᵥ w = 0 := by
    funext i
    simpa [Matrix.mulVec] using h i
  intro j
  by_contra hw
  have hreg : w j ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hw
  exact hM (M.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hmul hreg)

/-- **Domain-valued derivation-Jacobian criterion.**  A finite family whose Jacobian has nonzero
determinant in an integral-domain ambient algebra is algebraically independent over the scalar
field killed by the derivations. -/
theorem algebraicIndependent_of_domain_jacobian
    [CharZero K] [IsDomain R]
    (g : ι → R) (D : ι → (R → R))
    (hadd : ∀ i a b, D i (a + b) = D i a + D i b)
    (hleib : ∀ i a b, D i (a * b) = a * D i b + b * D i a)
    (hconst : ∀ i (c : K), D i (algebraMap K R c) = 0)
    (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (hDg : ∀ i j, D i (g j) = M i j) :
    AlgebraicIndependent K g := by
  classical
  rw [algebraicIndependent_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    GaloisForLFunctions.Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hker
  have hPeval : MvPolynomial.aeval g P = 0 := RingHom.mem_ker.mp hPI
  have hjac : ∀ i,
      ∑ j, M i j * MvPolynomial.aeval g (MvPolynomial.pderiv j P) = 0 := by
    intro i
    have hchain := jacobian_aeval_eq_sum_pderiv
      (D i) (hadd i) (hleib i) (hconst i) g P
    have hD0 : D i 0 = 0 := by
      have hzero := hadd i 0 0
      simp only [add_zero] at hzero
      linear_combination -hzero
    rw [hPeval, hD0] at hchain
    calc
      ∑ j, M i j * MvPolynomial.aeval g (MvPolynomial.pderiv j P) =
          ∑ j, MvPolynomial.aeval g (MvPolynomial.pderiv j P) * D i (g j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hDg i j]
        ring
      _ = 0 := hchain.symm
  have hpder0 : ∀ j, MvPolynomial.aeval g (MvPolynomial.pderiv j P) = 0 :=
    vec_zero_of_det_ne_zero M hM
      (fun j => MvPolynomial.aeval g (MvPolynomial.pderiv j P)) hjac
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap K R (P.coeff 0) = 0 := by simpa using hPeval
    have hc : P.coeff 0 = 0 := FaithfulSMul.algebraMap_injective K R (by simpa using hcmap)
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    GaloisForLFunctions.pderiv_ne_zero_of_mem_support hsP his
  have hpI : MvPolynomial.pderiv i P ∈ RingHom.ker (MvPolynomial.aeval g).toRingHom :=
    RingHom.mem_ker.mpr (hpder0 i)
  have hle := hmin hpI hpderiv0
  have hlt := GaloisForLFunctions.totalDegree_pderiv_lt P i hpderiv0
  exact (not_lt_of_ge hle) hlt

end

end GaloisForLFunctions.HTGeometry
