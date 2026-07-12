import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetDerivatives
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Factorial diagonal equivalence between normalized and differential jets

The actual derivative packet is obtained from the normalized Cauchy packet by multiplying the
order-`j` coordinate by `j!`.  Diagonal substitution by nonzero scalars is injective on the
multivariate polynomial ring.  Hence no algebraic relation is lost when polynomial escape is
performed in normalized coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Diagonal variable scaling on a complex multivariate polynomial ring. -/
noncomputable def mvPolynomialDiagonalScale {σ : Type*} (c : σ → ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.bind₁ (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)

/-- Scaling by coordinatewise nonzero constants is inverted by reciprocal scaling. -/
theorem mvPolynomialDiagonalScale_inv_apply
    {σ : Type*} (c : σ → ℂ) (hc : ∀ i, c i ≠ 0) (P : MvPolynomial σ ℂ) :
    mvPolynomialDiagonalScale (fun i => (c i)⁻¹) (mvPolynomialDiagonalScale c P) = P := by
  rw [mvPolynomialDiagonalScale, mvPolynomialDiagonalScale,
    MvPolynomial.bind₁_bind₁]
  have hg : (fun i => MvPolynomial.bind₁
      (fun j => MvPolynomial.C ((c j)⁻¹) * MvPolynomial.X j)
      (MvPolynomial.C (c i) * MvPolynomial.X i)) = MvPolynomial.X := by
    funext i
    simp only [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    simp [hc i]
  rw [hg, MvPolynomial.bind₁_X_left]
  rfl

/-- Diagonal scaling by nonzero constants preserves nonzero polynomials. -/
theorem mvPolynomialDiagonalScale_ne_zero
    {σ : Type*} (c : σ → ℂ) (hc : ∀ i, c i ≠ 0)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    mvPolynomialDiagonalScale c P ≠ 0 := by
  intro h
  have hzero := congrArg (mvPolynomialDiagonalScale (fun i => (c i)⁻¹)) h
  rw [mvPolynomialDiagonalScale_inv_apply c hc P] at hzero
  simp at hzero
  exact hP hzero

theorem eval_mvPolynomialDiagonalScale
    {σ : Type*} (c x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (mvPolynomialDiagonalScale c P) =
      MvPolynomial.eval (fun i => c i * x i) P := by
  rw [mvPolynomialDiagonalScale]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x
      (MvPolynomial.bind₁ (fun i => MvPolynomial.C (c i) * MvPolynomial.X i) P) =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => c i * x i) P
  rw [MvPolynomial.eval₂Hom_bind₁]
  simp

/-- Factorial diagonal scaling for a finite translated jet packet. -/
noncomputable def jetFactorialScale
    {ι : Type*} (orders : ι → ℕ) :
    MvPolynomial (Σ i, Fin (orders i)) ℂ →ₐ[ℂ]
      MvPolynomial (Σ i, Fin (orders i)) ℂ :=
  mvPolynomialDiagonalScale fun s => (s.2.1.factorial : ℂ)

/-- Factorial scaling preserves every nonzero jet polynomial. -/
theorem jetFactorialScale_ne_zero
    {ι : Type*} (orders : ι → ℕ)
    {P : MvPolynomial (Σ i, Fin (orders i)) ℂ} (hP : P ≠ 0) :
    jetFactorialScale orders P ≠ 0 := by
  apply mvPolynomialDiagonalScale_ne_zero _ _ hP
  intro s
  exact_mod_cast Nat.factorial_ne_zero s.2.1

/-- The actual differential-jet packet of the prime-log Herglotz source. -/
noncomputable def primeLogDifferentialJetPacket
    {ι : Type*} (u : Nat.Primes → ℝ) (nodes : ι → ℂ) (orders : ι → ℕ) :
    (Σ i, Fin (orders i)) → ℂ :=
  fun s => iteratedDeriv s.2.1 (primeLogHerglotz u) (nodes s.1)

/-- Evaluating a factorial-scaled polynomial on normalized Cauchy jets is exactly evaluation of the
original polynomial on the actual differential jets. -/
theorem eval_jetFactorialScale_primeLogCauchyJetPacket
    {ι : Type*} (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ) :
    MvPolynomial.eval (primeLogCauchyJetPacket u nodes orders)
        (jetFactorialScale orders P) =
      MvPolynomial.eval (primeLogDifferentialJetPacket u nodes orders) P := by
  rw [jetFactorialScale, eval_mvPolynomialDiagonalScale]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext s
  exact (iteratedDeriv_primeLogHerglotz_eq_factorial_mul_packet
    u C hu nodes hupper orders s).symm

end GaloisForLFunctions.HTGeometry
