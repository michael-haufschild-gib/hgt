import GaloisForLFunctions.HTGeometry.LineJetTransfer
import GaloisForLFunctions.HTGeometry.PolynomialImplicitField

/-!
# The line form of a polynomial jet relation

Restricting a holomorphic function to a vertical line multiplies its `k`-th jet by `i^k`, so a
polynomial relation among the complex jets becomes a polynomial relation among the jets of the line
restriction, with the variables rescaled by the inverse powers of `i`.  The rescaling is invertible,
so it destroys neither the relation nor its nontriviality.
-/

open Filter Topology MvPolynomial

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- Rescaling the variables of a polynomial. -/
noncomputable def scaleVars {m : ℕ} (c : Fin m → ℂ) (P : MvPolynomial (Fin m) ℂ) :
    MvPolynomial (Fin m) ℂ :=
  MvPolynomial.bind₁ (fun k => MvPolynomial.C (c k) * MvPolynomial.X k) P

theorem eval_scaleVars {m : ℕ} (c : Fin m → ℂ) (P : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ) :
    MvPolynomial.eval v (scaleVars c P) = MvPolynomial.eval (fun k => c k * v k) P := by
  show MvPolynomial.aeval v (scaleVars c P) = MvPolynomial.aeval (fun k => c k * v k) P
  have harg : (fun i : Fin m => (MvPolynomial.aeval v) (MvPolynomial.C (c i) * MvPolynomial.X i))
      = fun k : Fin m => c k * v k := by
    funext k
    simp
  rw [scaleVars, MvPolynomial.aeval_bind₁, harg]

/-- Rescaling by nonzero scalars keeps a polynomial nonzero. -/
theorem scaleVars_ne_zero {m : ℕ} {c : Fin m → ℂ} (hc : ∀ k, c k ≠ 0)
    {P : MvPolynomial (Fin m) ℂ} (hP : P ≠ 0) : scaleVars c P ≠ 0 := by
  intro h0
  refine hP ?_
  refine MvPolynomial.funext fun v => ?_
  have h := eval_scaleVars c P (fun k => (c k)⁻¹ * v k)
  rw [h0] at h
  simp only [map_zero] at h
  have hv : (fun k => c k * ((c k)⁻¹ * v k)) = v := by
    funext k
    rw [← mul_assoc, mul_inv_cancel₀ (hc k), one_mul]
  rw [hv] at h
  simpa using h.symm

/-- **The line form of a jet relation.** -/
theorem eval_scaleVars_line {σ R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun k : Fin m => iteratedDeriv (k : ℕ) g z) P = 0) (t : ℝ) :
    MvPolynomial.eval
        (fun k : Fin m => iteratedDeriv (k : ℕ)
          (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t)
        (scaleVars (fun k : Fin m => (Complex.I ^ (k : ℕ))⁻¹) P) = 0 := by
  rw [eval_scaleVars]
  have hpt : (fun k : Fin m => (Complex.I ^ (k : ℕ))⁻¹ *
      iteratedDeriv (k : ℕ) (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t)
      = fun k : Fin m => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext k
    rw [iteratedDeriv_line_restriction hR hg (k : ℕ) t, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  rw [hpt]
  exact hrel _ (mem_verticalStrip_line hR σ t)

end GaloisForLFunctions
