import GaloisForLFunctions.HTGeometry.RationalModelTransfer

/-!
# The chain rule with a cleared denominator

A cascade whose law has denominators still has a *polynomial* law after multiplying by one common
denominator, provided one stays inside the polynomials in the coordinates the cascade actually uses.
On that subalgebra the cleared law computes both the complex derivative and the rational model's
derivation:

`Dtot(states)·(d/dz)[P(states)] = (δ̃P)(states)`   and   `Dtot·δ(P) = δ̃P`,

by the same induction — generators, constants, sums, products — with no condition on supports beyond
membership in the subalgebra.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Y : ℕ → ℂ → ℂ}

/-- The subalgebra of polynomials in the coordinates up to `N`. -/
noncomputable def lowPoly (N : ℕ) : Subalgebra ℂ (MvPolynomial ℕ ℂ) :=
  Algebra.adjoin ℂ {P : MvPolynomial ℕ ℂ | ∃ k, k ≤ N ∧ P = MvPolynomial.X k}

theorem X_mem_lowPoly {k N : ℕ} (h : k ≤ N) : MvPolynomial.X k ∈ lowPoly N :=
  Algebra.subset_adjoin ⟨k, h, rfl⟩

theorem lowPoly_mono {N N' : ℕ} (h : N ≤ N') : lowPoly N ≤ lowPoly N' := by
  rw [lowPoly, lowPoly]
  refine Algebra.adjoin_mono ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, by omega, rfl⟩

/-- **The cleared chain rule for the complex derivative.** -/
theorem deriv_evalAt_cleared (hY : ∀ k, Differentiable ℂ (Y k))
    {δp : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)} {Dtot : MvPolynomial ℕ ℂ} {N : ℕ}
    (hlaw : ∀ k, k ≤ N → ∀ z : ℂ,
      evalAt Y z Dtot * deriv (Y k) z = evalAt Y z (δp (MvPolynomial.X k)))
    {P : MvPolynomial ℕ ℂ} (hP : P ∈ lowPoly N) (z : ℂ) :
    evalAt Y z Dtot * deriv (fun w => evalAt Y w P) z = evalAt Y z (δp P) := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      have hfun : (fun w => evalAt Y w (MvPolynomial.X k)) = Y k := by
        funext w
        exact evalAt_X Y w k
      rw [hfun]
      exact hlaw k hk z
  | algebraMap c =>
      have hfun : (fun w => evalAt Y w (algebraMap ℂ (MvPolynomial ℕ ℂ) c)) = fun _ : ℂ => c := by
        funext w
        show evalAt Y w (MvPolynomial.C c) = c
        simp [evalAt]
      rw [hfun, δp.map_algebraMap]
      simp
  | add x y hx hy ihx ihy =>
      have h1 : HasDerivAt (fun w => evalAt Y w x)
          (deriv (fun w => evalAt Y w x) z) z :=
        ((differentiable_evalAt hY x) z).hasDerivAt
      have h2 : HasDerivAt (fun w => evalAt Y w y)
          (deriv (fun w => evalAt Y w y) z) z :=
        ((differentiable_evalAt hY y) z).hasDerivAt
      have hfun : (fun w => evalAt Y w (x + y))
          = fun w => evalAt Y w x + evalAt Y w y := by
        funext w
        simp [map_add]
      have hd : deriv (fun w => evalAt Y w x + evalAt Y w y) z
          = deriv (fun w => evalAt Y w x) z + deriv (fun w => evalAt Y w y) z :=
        (h1.add h2).deriv
      rw [hfun, hd, map_add, mul_add, ihx, ihy, map_add]
  | mul x y hx hy ihx ihy =>
      have h1 : HasDerivAt (fun w => evalAt Y w x)
          (deriv (fun w => evalAt Y w x) z) z :=
        ((differentiable_evalAt hY x) z).hasDerivAt
      have h2 : HasDerivAt (fun w => evalAt Y w y)
          (deriv (fun w => evalAt Y w y) z) z :=
        ((differentiable_evalAt hY y) z).hasDerivAt
      have hfun : (fun w => evalAt Y w (x * y))
          = fun w => evalAt Y w x * evalAt Y w y := by
        funext w
        simp [map_mul]
      have hd : deriv (fun w => evalAt Y w x * evalAt Y w y) z
          = deriv (fun w => evalAt Y w x) z * evalAt Y z y
            + evalAt Y z x * deriv (fun w => evalAt Y w y) z :=
        (h1.mul h2).deriv
      rw [hfun, hd, Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      rw [show evalAt Y z Dtot
          * (deriv (fun w => evalAt Y w x) z * evalAt Y z y
            + evalAt Y z x * deriv (fun w => evalAt Y w y) z)
          = (evalAt Y z Dtot * deriv (fun w => evalAt Y w x) z) * evalAt Y z y
            + evalAt Y z x * (evalAt Y z Dtot * deriv (fun w => evalAt Y w y) z) by ring,
        ihx, ihy]
      ring

/-- **The cleared chain rule in the rational model.** -/
theorem algebraMap_cleared {δ : Derivation ℂ CascadeField CascadeField}
    {δp : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)} {Dtot : MvPolynomial ℕ ℂ} {N : ℕ}
    (hlaw : ∀ k, k ≤ N →
      algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot * δ (fx k)
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp (MvPolynomial.X k)))
    {P : MvPolynomial ℕ ℂ} (hP : P ∈ lowPoly N) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot
        * δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField P)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp P) := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hlaw k hk
  | algebraMap c =>
      rw [← IsScalarTower.algebraMap_apply ℂ (MvPolynomial ℕ ℂ) CascadeField,
        δ.map_algebraMap, δp.map_algebraMap, map_zero, mul_zero]
  | add x y hx hy ihx ihy =>
      have hlhs : δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField (x + y))
          = δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField x)
            + δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField y) := by
        rw [map_add, map_add]
      rw [hlhs, mul_add, ihx, ihy, map_add]
      exact (map_add (algebraMap (MvPolynomial ℕ ℂ) CascadeField) (δp x) (δp y)).symm
  | mul x y hx hy ihx ihy =>
      have hlhs : δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField (x * y))
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField x
              * δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField y)
            + algebraMap (MvPolynomial ℕ ℂ) CascadeField y
              * δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField x) := by
        rw [map_mul, Derivation.leibniz]
        simp [smul_eq_mul]
      have hrhs : algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp (x * y))
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField x
              * algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp y)
            + algebraMap (MvPolynomial ℕ ℂ) CascadeField y
              * algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp x) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul, map_add, map_mul]
      rw [hlhs, hrhs, mul_add, ← ihx, ← ihy]
      ring

end GaloisForLFunctions.HTGeometry
