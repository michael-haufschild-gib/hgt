import GaloisForLFunctions.RHTower.DeningerArithmeticPureSuspensionNoGo

/-!
# Transport of a scalar flow and the scalar point spectrum

If a comparison map induces a flow-equivariant isomorphism, a scalar flow on one side is a scalar
flow on the other.  A scalar generator has at most one point eigenvalue, its weight, so a set with
two distinct elements — in particular an infinite one — cannot be its point spectrum.

Together with the dense-time rigidity already proved for the pure suspension, this is the
consequence half of the coarse/stack no-go: a coefficient whose comparison is an isomorphism has
scalar flow, hence cannot realize a spectrum with two distinct points.

* `deningerScalarFlow_transport` : scalarity crosses an equivariant equivalence.
* `deningerScalarGenerator_pointSpectrum_subset` : the point spectrum is at most the weight.
* `deningerScalarGenerator_no_two_eigenvalues` : two distinct eigenvalues are impossible.
-/

namespace RHTower

section Transport

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- **Scalarity crosses an equivariant equivalence.**  If a comparison induces an isomorphism
intertwining the two flows and the target flow is scalar, the source flow is scalar with the same
scalars. -/
theorem deningerScalarFlow_transport (Φ : A ≃ₗ[ℂ] B) (T : ℝ → A →ₗ[ℂ] A) (S : ℝ → B →ₗ[ℂ] B)
    (hint : ∀ t a, Φ (T t a) = S t (Φ a)) (c : ℝ → ℂ) (hS : ∀ t b, S t b = c t • b)
    (t : ℝ) (a : A) : T t a = c t • a := by
  refine Φ.injective ?_
  rw [hint t a, hS t (Φ a), map_smul]

end Transport

section ScalarSpectrum

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The point spectrum of an operator. -/
def deningerPointSpectrum (theta : V →ₗ[ℂ] V) : Set ℂ :=
  {lam | ∃ x : V, x ≠ 0 ∧ theta x = lam • x}

/-- **A scalar generator has at most its weight in the point spectrum.** -/
theorem deningerScalarGenerator_pointSpectrum_subset (theta : V →ₗ[ℂ] V) (weight : ℂ)
    (htheta : ∀ x, theta x = weight • x) : deningerPointSpectrum theta ⊆ {weight} := by
  rintro lam ⟨x, hx, hlam⟩
  have hsmul : (weight - lam) • x = 0 := by
    rw [sub_smul, ← htheta x, hlam, sub_self]
  have hweight : weight - lam = 0 := (smul_eq_zero.mp hsmul).resolve_right hx
  exact (sub_eq_zero.mp hweight).symm

/-- **A scalar generator cannot have two distinct eigenvalues.**  So a spectrum with two distinct
points — in particular the infinite zeta divisor — is not the point spectrum of a scalar flow
generator. -/
theorem deningerScalarGenerator_no_two_eigenvalues (theta : V →ₗ[ℂ] V) (weight : ℂ)
    (htheta : ∀ x, theta x = weight • x) {lam mu : ℂ} (hlam : lam ∈ deningerPointSpectrum theta)
    (hmu : mu ∈ deningerPointSpectrum theta) : lam = mu := by
  have h1 := deningerScalarGenerator_pointSpectrum_subset theta weight htheta hlam
  have h2 := deningerScalarGenerator_pointSpectrum_subset theta weight htheta hmu
  rw [Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

/-- **The no-go in its contrapositive form.**  If the point spectrum contains two distinct points,
the generator is not scalar; so a coefficient realizing a spectrum with two distinct points has a
nonzero comparison defect. -/
theorem deningerScalarGenerator_not_scalar_of_two_eigenvalues (theta : V →ₗ[ℂ] V) {lam mu : ℂ}
    (hne : lam ≠ mu) (hlam : lam ∈ deningerPointSpectrum theta)
    (hmu : mu ∈ deningerPointSpectrum theta) : ¬ ∃ weight : ℂ, ∀ x, theta x = weight • x := by
  rintro ⟨weight, htheta⟩
  exact hne (deningerScalarGenerator_no_two_eigenvalues theta weight htheta hlam hmu)

end ScalarSpectrum

end RHTower
