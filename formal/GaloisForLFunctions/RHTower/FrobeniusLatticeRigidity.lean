import GaloisForLFunctions.RHTower.SixExponentials.PrimePowers
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw

/-!
# Frobenius eigen-characters on integral lattices

An endomorphism `F` of a finite free `ℤ`-module satisfies its characteristic polynomial, a monic
integer polynomial (Cayley–Hamilton).  Any nonzero `ℤ`-linear functional `φ : A → ℂ` with
`φ ∘ F = λ φ` therefore has `λ` a root of that polynomial, hence an algebraic integer.

Consequences for candidate cohomologies of the arithmetic curve over `𝔽₁`:

* the zeros of ξ cannot be joint eigen-characters of Frobenii at three distinct primes on any
  finite free `ℤ`-lattice, because `p^ρ, q^ρ, r^ρ` are not all algebraic for a nonreal `ρ`;
* a Frobenius on a finite free `ℤ`-lattice all of whose complex eigenvalues are unimodular is of
  finite order on every eigen-character (Kronecker): unitary integral Frobenii are torsion.

So an integral structure carrying the zeros must be of infinite rank, and its integrality must be
that of the coefficients acting (the Dirichlet ring), not of the eigenvalues.
-/

open Polynomial

namespace RHTower

section Lattice

variable {A : Type*} [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A]

omit [Module.Free ℤ A] [Module.Finite ℤ A] in
/-- A functional intertwining `F` with the scalar `μ` intertwines every polynomial in `F` with the
corresponding value. -/
theorem eigenfunctional_aeval (F : A →ₗ[ℤ] A) (φ : A →ₗ[ℤ] ℂ) (μ : ℂ)
    (h : ∀ a, φ (F a) = μ * φ a) (P : ℤ[X]) (a : A) :
    φ ((aeval F P) a) = (aeval μ P) * φ a := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
    ring
  | monomial n c =>
    have hpow : ∀ k : ℕ, ∀ b : A, φ ((F ^ k) b) = μ ^ k * φ b := by
      intro k
      induction k with
      | zero => intro b; simp
      | succ k ih =>
        intro b
        rw [pow_succ', Module.End.mul_apply, h, ih]
        ring
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_zsmul, hpow]
    simp only [zsmul_eq_mul, eq_intCast]
    ring

/-- **Eigenvalues of integral Frobenii are algebraic integers.**  A nonzero functional
intertwining an endomorphism of a finite free `ℤ`-module with a scalar has an integral scalar. -/
theorem isIntegral_of_eigenfunctional (F : A →ₗ[ℤ] A) (φ : A →ₗ[ℤ] ℂ) (hφ : φ ≠ 0) (μ : ℂ)
    (h : ∀ a, φ (F a) = μ * φ a) : IsIntegral ℤ μ := by
  refine ⟨F.charpoly, F.charpoly_monic, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (LinearMap.ext hcon)
  have h0 : aeval F F.charpoly = (0 : A →ₗ[ℤ] A) := LinearMap.aeval_self_charpoly F
  have h1 := eigenfunctional_aeval F φ μ h F.charpoly a
  rw [h0, LinearMap.zero_apply, map_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact h2
  · exact absurd h2 ha

theorem isAlgebraic_of_eigenfunctional (F : A →ₗ[ℤ] A) (φ : A →ₗ[ℤ] ℂ) (hφ : φ ≠ 0) (μ : ℂ)
    (h : ∀ a, φ (F a) = μ * φ a) : IsAlgebraic ℚ μ :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (isIntegral_of_eigenfunctional F φ hφ μ h).isAlgebraic

/-- **No finite free `ℤ`-lattice carries the zeros as joint Frobenius eigen-characters at three
primes.**  For nonreal `ρ` and distinct primes `p, q, r`, no nonzero functional intertwines three
endomorphisms of a finite free `ℤ`-module with `p^ρ, q^ρ, r^ρ` simultaneously. -/
theorem not_exists_joint_eigenfunctional_three_primes {ρ : ℂ} (hρ : ρ.im ≠ 0) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (Fp Fq Fr : A →ₗ[ℤ] A) :
    ¬ ∃ φ : A →ₗ[ℤ] ℂ, φ ≠ 0 ∧ (∀ a, φ (Fp a) = (p : ℂ) ^ ρ * φ a) ∧
      (∀ a, φ (Fq a) = (q : ℂ) ^ ρ * φ a) ∧ (∀ a, φ (Fr a) = (r : ℂ) ^ ρ * φ a) := by
  rintro ⟨φ, hφ, hp', hq', hr'⟩
  exact GaloisForLFunctions.RHTower.SixExponentials.not_all_three_prime_cpow_isAlgebraic hρ hp hq hr
    hpq hpr hqr ⟨isAlgebraic_of_eigenfunctional Fp φ hφ _ hp',
      isAlgebraic_of_eigenfunctional Fq φ hφ _ hq', isAlgebraic_of_eigenfunctional Fr φ hφ _ hr'⟩

/-- **Unitary integral Frobenii are torsion.**  If every complex root of the characteristic
polynomial of `F` is unimodular, every eigen-character of `F` is a root of unity. -/
theorem exists_pow_eq_one_of_eigenfunctional_of_unimodular_charpoly (F : A →ₗ[ℤ] A)
    (hunit : ∀ z ∈ (F.charpoly.map (Int.castRingHom ℂ)).roots, ‖z‖ = 1)
    (φ : A →ₗ[ℤ] ℂ) (hφ : φ ≠ 0) (μ : ℂ) (h : ∀ a, φ (F a) = μ * φ a) :
    ∃ n : ℕ, 0 < n ∧ μ ^ n = 1 := by
  have hint := isIntegral_of_eigenfunctional F φ hφ μ h
  refine exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one hint ?_
  intro z hz
  apply hunit
  -- `z` is a root of the minimal polynomial of `μ` over `ℚ`, which divides the characteristic
  -- polynomial mapped to `ℚ`, so `z` is a root of the characteristic polynomial.
  have hmin : aeval z (minpoly ℚ μ) = 0 := (Polynomial.mem_rootSet.mp hz).2
  have hchar0 : aeval μ F.charpoly = 0 := by
    obtain ⟨P, hmonic, hP⟩ := hint
    -- reuse the Cayley–Hamilton evaluation
    have h0 : aeval F F.charpoly = (0 : A →ₗ[ℤ] A) := LinearMap.aeval_self_charpoly F
    obtain ⟨a, ha⟩ : ∃ a, φ a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφ (LinearMap.ext hcon)
    have h2 := eigenfunctional_aeval F φ μ h F.charpoly a
    rw [h0, LinearMap.zero_apply, map_zero] at h2
    rcases mul_eq_zero.mp h2.symm with h3 | h3
    · exact h3
    · exact absurd h3 ha
  have hchar : aeval μ (F.charpoly.map (algebraMap ℤ ℚ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hchar0
  have hdvd : minpoly ℚ μ ∣ F.charpoly.map (algebraMap ℤ ℚ) := minpoly.dvd ℚ μ hchar
  obtain ⟨g, hg⟩ := hdvd
  have hzero : aeval z F.charpoly = 0 := by
    have h1 : aeval z (F.charpoly.map (algebraMap ℤ ℚ)) = 0 := by
      rw [hg, map_mul, hmin, zero_mul]
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hne : F.charpoly.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_monic_ne_zero F.charpoly_monic)
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def] at hzero
  exact hzero

end Lattice

end RHTower
