import GaloisForLFunctions.HTGeometry.GammaBellSubstitution

/-!
# The Bell chain for an abstract derivation

For a derivation `δ` and a terminal-linear element `x` satisfying `δ x = A*x`, every iterate of
`x` is `x` times the corresponding complete Bell polynomial in the iterates of `A`.  This is the
abstract algebraic bridge from actual Lie derivatives to the universal polynomial output family.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- The multivariate chain rule specialized to an algebra derivation. -/
theorem derivation_aeval_eq_sum_pderiv
    {K R ι : Type*} [Field K] [CommRing R] [Algebra K R]
    [Fintype ι] [DecidableEq ι]
    (δ : Derivation K R R) (g : ι → R) (P : MvPolynomial ι K) :
    δ (aeval g P) = ∑ j, aeval g (pderiv j P) * δ (g j) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [map_add, δ.map_add, hP, hQ, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_add, map_add, add_mul]
  | mul_X P k hP =>
      rw [map_mul, aeval_X, Derivation.leibniz, hP, Finset.mul_sum]
      simp only [smul_eq_mul]
      symm
      rw [show
          (∑ j, aeval g (pderiv j (P * X k)) * δ (g j)) =
            ∑ j, (aeval g (pderiv j P) * δ (g j) * g k +
              (if j = k then aeval g P * δ (g j) else 0)) from by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = k
        · subst h
          rw [pderiv_mul, map_add, pderiv_X, Pi.single_eq_same,
            map_mul, aeval_X, mul_one, add_mul, if_pos rfl]
          ring
        · rw [pderiv_mul, map_add, pderiv_X,
            Pi.single_eq_of_ne (Ne.symm h), mul_zero, _root_.map_zero, add_zero,
            map_mul, aeval_X, if_neg h, add_zero]
          ring]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k
        (fun j => aeval g P * δ (g j)), if_pos (Finset.mem_univ k)]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- One derivation step advances an iterated jet. -/
theorem derivation_iterate_succ
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) (m : ℕ) (x : R) :
    ((δ : R → R)^[m + 1]) x = δ (((δ : R → R)^[m]) x) := by
  exact Function.iterate_succ_apply' (δ : R → R) m x

/-- Evaluating the Bell recurrence on the iterated `A`-jet gives its algebraic chain-rule
recurrence. -/
theorem aeval_bellCore_succ_derivationIterate
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (A : R) (m : ℕ) :
    aeval (fun i : Fin (m + 1) => ((δ : R → R)^[(i : ℕ)]) A) (bellCore (m + 1)) =
      A * aeval (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A) (bellCore m) +
        ∑ j : Fin m,
          aeval (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A)
              (pderiv j (bellCore m)) *
            ((δ : R → R)^[(j : ℕ) + 1]) A := by
  rw [bellCore_succ]
  simp only [map_add, map_mul, aeval_X, aeval_rename, map_sum, Fin.val_zero, Fin.val_succ]
  have hrestrict :
      ((fun i : Fin (m + 1) => ((δ : R → R)^[(i : ℕ)]) A) ∘ Fin.castSucc) =
        (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A) := rfl
  rw [hrestrict]
  simp

/-- **Abstract terminal-linear Bell chain.**  If `δx=A*x`, then
`δ^m x = x*B_m(A,δA,...,δ^(m-1)A)` for every `m`. -/
theorem derivation_iterate_terminalLinear_eq_bellCore
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (x A : R) (hδx : δ x = A * x) :
    ∀ m : ℕ,
      ((δ : R → R)^[m]) x =
        x * aeval (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A) (bellCore m) := by
  intro m
  induction m with
  | zero => simp [bellCore_zero]
  | succ m ih =>
      rw [derivation_iterate_succ, ih, Derivation.leibniz, hδx]
      simp only [smul_eq_mul]
      rw [derivation_aeval_eq_sum_pderiv]
      have hjet (j : Fin m) :
          δ (((δ : R → R)^[(j : ℕ)]) A) =
            ((δ : R → R)^[(j : ℕ) + 1]) A := by
        exact (derivation_iterate_succ δ (j : ℕ) A).symm
      simp_rw [hjet]
      rw [aeval_bellCore_succ_derivationIterate]
      ring

end GaloisForLFunctions

end
