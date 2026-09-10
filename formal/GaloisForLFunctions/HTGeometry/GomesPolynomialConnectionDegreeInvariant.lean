import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionIndex

/-!
# Degree distinguishes polynomial connections with identical spectra

A linear intertwining equivalence transports the literal missing-output quotient.
Its dimension therefore recovers the coefficient degree, which the algebraic spectrum
can entirely miss. The monomial coefficient family gives pairwise inequivalent models
with identical all-real spectra and identical empty polynomial point spectra.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- An actual invertible linear change of polynomial coordinates intertwining two connections. -/
abbrev GomesPolynomialConnectionIntertwiner (A B : ℝ[X]) :=
  {e : ℝ[X] ≃ₗ[ℝ] ℝ[X] // e.toLinearMap.comp (gomesPolynomialFirstOrderLinearMap A) =
    (gomesPolynomialFirstOrderLinearMap B).comp e.toLinearMap}

/-- An intertwining equivalence transports precisely the generated-output range. -/
theorem gomesPolynomialConnectionIntertwiner_range (A B : ℝ[X])
    (E : GomesPolynomialConnectionIntertwiner A B) :
    (LinearMap.range (gomesPolynomialFirstOrderLinearMap A)).map E.val.toLinearMap =
      LinearMap.range (gomesPolynomialFirstOrderLinearMap B) := by
  rw [← LinearMap.range_comp, E.property, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr E.val.surjective

/-- Every connection equivalence induces a concrete equivalence of obstruction quotients. -/
def gomesPolynomialConnectionIntertwiner_cokernelEquiv (A B : ℝ[X])
    (E : GomesPolynomialConnectionIntertwiner A B) :
    GomesPolynomialConnectionCokernel A ≃ₗ[ℝ] GomesPolynomialConnectionCokernel B :=
  Submodule.Quotient.equiv _ _ E.val (gomesPolynomialConnectionIntertwiner_range A B E)

/-- Coefficient degree is preserved by every invertible linear intertwiner. -/
theorem gomesPolynomialConnectionIntertwiner_degree (A B : ℝ[X])
    (E : GomesPolynomialConnectionIntertwiner A B) : A.natDegree = B.natDegree := by
  rw [← gomesPolynomialConnectionCokernel_finrank_all A,
    ← gomesPolynomialConnectionCokernel_finrank_all B]
  exact (gomesPolynomialConnectionIntertwiner_cokernelEquiv A B E).finrank_eq

/-- Different coefficient degrees cannot be hidden by any linear coordinate equivalence. -/
theorem gomesPolynomialConnection_no_different_degree_intertwiner :
    ¬ ∃ A B : ℝ[X], A.natDegree ≠ B.natDegree ∧
      Nonempty (GomesPolynomialConnectionIntertwiner A B) := by
  rintro ⟨A, B, h, ⟨E⟩⟩
  exact h (gomesPolynomialConnectionIntertwiner_degree A B E)

/-- Every positive monomial degree supplies an explicit nonconstant polynomial connection. -/
def gomesPolynomialMonomialConnectionCoefficient (n : ℕ) : GomesNonconstantPolynomialCoefficient :=
  ⟨X ^ (n + 1), by rw [derivative_ne_zero, natDegree_X_pow]; exact Nat.succ_ne_zero n⟩

/-- Every member of the monomial family has the entire real algebraic spectrum. -/
theorem gomesPolynomialMonomialConnection_spectrum (n : ℕ) :
    spectrum ℝ (gomesPolynomialFirstOrderLinearMap (X ^ (n + 1))) = Set.univ :=
  gomesPolynomialFirstOrderLinearMap_nonconstant_spectrum (gomesPolynomialMonomialConnectionCoefficient n)

/-- Every member also has empty polynomial point spectrum. -/
theorem gomesPolynomialMonomialConnection_eigenvalues (n : ℕ) :
    gomesPolynomialFirstOrderEigenvalues (X ^ (n + 1)) = ∅ :=
  gomesPolynomialFirstOrderEigenvalues_nonconstant (gomesPolynomialMonomialConnectionCoefficient n)

/-- Their missing-output dimensions nevertheless distinguish every monomial degree. -/
theorem gomesPolynomialMonomialConnection_cokernel_finrank (n : ℕ) :
    Module.finrank ℝ (GomesPolynomialConnectionCokernel (X ^ (n + 1))) = n + 1 := by
  rw [gomesPolynomialConnectionCokernel_finrank_all, natDegree_X_pow]

/-- Two members of the explicit family are linearly equivalent exactly when their degrees agree. -/
theorem gomesPolynomialMonomialConnection_intertwiner_iff (n m : ℕ) :
    Nonempty (GomesPolynomialConnectionIntertwiner (X ^ (n + 1)) (X ^ (m + 1))) ↔ n = m := by
  constructor
  · rintro ⟨E⟩
    have hd := gomesPolynomialConnectionIntertwiner_degree _ _ E
    rw [natDegree_X_pow, natDegree_X_pow] at hd
    exact Nat.add_right_cancel hd
  · rintro rfl
    refine ⟨⟨LinearEquiv.refl ℝ ℝ[X], ?_⟩⟩
    apply LinearMap.ext
    intro Q
    rfl

/-- Identical spectra coexist with a complete infinite family of inequivalent polynomial connections. -/
theorem gomesPolynomialMonomialConnection_spectral_reconstruction_boundary (n m : ℕ) :
    spectrum ℝ (gomesPolynomialFirstOrderLinearMap (X ^ (n + 1))) =
      spectrum ℝ (gomesPolynomialFirstOrderLinearMap (X ^ (m + 1))) ∧
    gomesPolynomialFirstOrderEigenvalues (X ^ (n + 1)) =
      gomesPolynomialFirstOrderEigenvalues (X ^ (m + 1)) ∧
    (Nonempty (GomesPolynomialConnectionIntertwiner (X ^ (n + 1)) (X ^ (m + 1))) ↔ n = m) := by
  rw [gomesPolynomialMonomialConnection_spectrum, gomesPolynomialMonomialConnection_spectrum,
    gomesPolynomialMonomialConnection_eigenvalues, gomesPolynomialMonomialConnection_eigenvalues]
  exact ⟨rfl, rfl, gomesPolynomialMonomialConnection_intertwiner_iff n m⟩

end GaloisForLFunctions.HTGeometry
