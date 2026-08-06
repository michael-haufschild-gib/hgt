import GaloisForLFunctions.HTGeometry.SchemeHorizonExpansion

/-!
# Expansion from the numerical class

The expansion step reads a positive integer as an eigenvalue.  A totally invariant prime divisor
satisfies `f^* E = e E`, so its numerical class is an eigenvector of the pullback with eigenvalue
the ramification index; if that class is nonzero and every eigenvalue of the pullback has modulus
greater than one, the index exceeds one.

The two geometric facts this consumes -- that the numerical class of a prime divisor is nonzero,
and that an int-amplified endomorphism acts on the numerical class group with all eigenvalues of
modulus greater than one -- are inputs, stated here as hypotheses.  What is proved is that they
combine to give the expansion hypothesis of the horizon theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

/-- **A positive integer eigenvalue of a map whose eigenvalues all exceed one in modulus exceeds
one.** -/
theorem one_lt_of_eigen_class {N : Type*} [AddCommGroup N] [Module ℝ N]
    (T : N →ₗ[ℝ] N) (hspec : ∀ (μ : ℝ) (w : N), w ≠ 0 → T w = μ • w → 1 < |μ|)
    {v : N} (hv : v ≠ 0) {e : ℕ} (hact : T v = (e : ℝ) • v) :
    1 < e := by
  have h := hspec (e : ℝ) v hv hact
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ))] at h
  exact_mod_cast h

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The expansion hypothesis from the numerical class.**  With a class map sending each component
of the horizon to a nonzero eigenvector of the pullback with eigenvalue its ramification index, and
with every eigenvalue of the pullback exceeding one in modulus, every component of the horizon is
ramified. -/
theorem forall_one_lt_of_numerical_class {N : Type*} [AddCommGroup N] [Module ℝ N]
    (T : N →ₗ[ℝ] N) (hspec : ∀ (μ : ℝ) (w : N), w ≠ 0 → T w = μ • w → 1 < |μ|)
    (e : CodimOnePoint X → ℕ) (g : X.functionField) (cls : CodimOnePoint X → N)
    (hnz : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → cls z ≠ 0)
    (hact : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → T (cls z) = (e z : ℝ) • cls z) :
    ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → 1 < e z :=
  fun z hz => one_lt_of_eigen_class T hspec (hnz z hz) (hact z hz)

end GaloisForLFunctions.HTGeometry
