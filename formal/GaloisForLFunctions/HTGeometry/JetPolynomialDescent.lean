import GaloisForLFunctions.HTGeometry.JetPolynomialDerivative
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# Descent for jet polynomial relations

The partial derivative of a jet polynomial in one jet coordinate is again a jet polynomial: the
coefficients are multiplied by the exponent and that exponent drops by one.  A jet polynomial of a
holomorphic function is holomorphic, so a jet polynomial relation valid on the central line of a
strip is valid on the whole strip.

Together these are the descent step for a differential relation that is degenerate in its top jet
everywhere: the solution then satisfies the derived relation, of strictly smaller degree in that jet.
-/

open Filter Topology

namespace GaloisForLFunctions

variable {N M : ℕ}

/-- The coefficients of the `k`-th partial derivative of a jet polynomial. -/
noncomputable def jetPolyPartialCoeffs (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (k : Fin M) :
    Fin N → ℂ := fun α => d α * (e α k : ℂ)

/-- The exponents of the `k`-th partial derivative of a jet polynomial. -/
def jetPolyPartialExps (e : Fin N → Fin M → ℕ) (k : Fin M) : Fin N → Fin M → ℕ :=
  fun α j => if j = k then e α j - 1 else e α j

theorem partialCoeff_jetPolyDeriv_eq (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (k : Fin M)
    (y : Fin M → ℂ) :
    partialCoeff (jetPolyDeriv d e y) k
      = jetPoly (jetPolyPartialCoeffs d e k) (jetPolyPartialExps e k) y := by
  classical
  rw [partialCoeff_jetPolyDeriv, jetPoly]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hsplit : ∏ j : Fin M, (y j) ^ (jetPolyPartialExps e k α j)
      = (y k) ^ (e α k - 1) * ∏ j ∈ (Finset.univ : Finset (Fin M)).erase k,
          (y j) ^ (e α j) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin M))
      (fun j => (y j) ^ (jetPolyPartialExps e k α j)) (Finset.mem_univ k)]
    congr 1
    · simp [jetPolyPartialExps]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [jetPolyPartialExps, hjk]
  rw [hsplit, jetPolyPartialCoeffs]
  ring

variable {σ R : ℝ}

/-- A jet polynomial of a holomorphic function is holomorphic. -/
theorem differentiableOn_jetPoly_jets {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) :
    DifferentiableOn ℂ
      (fun z : ℂ => jetPoly d e (fun j : Fin M => iteratedDeriv (j : ℕ) Φ z))
      (verticalStrip σ R) := by
  classical
  have hjet : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j Φ) (verticalStrip σ R) :=
    differentiableOn_iteratedDeriv_verticalStrip hΦ
  have hprod : ∀ α : Fin N, DifferentiableOn ℂ
      (fun z : ℂ => ∏ j : Fin M, (iteratedDeriv (j : ℕ) Φ z) ^ (e α j)) (verticalStrip σ R) := by
    intro α
    have h1 : DifferentiableOn ℂ
        (∏ j : Fin M, fun z : ℂ => (iteratedDeriv (j : ℕ) Φ z) ^ (e α j)) (verticalStrip σ R) :=
      DifferentiableOn.finsetProd fun (j : Fin M) _ => (hjet (j : ℕ)).pow (e α j)
    have h2 : (∏ j : Fin M, fun z : ℂ => (iteratedDeriv (j : ℕ) Φ z) ^ (e α j))
        = fun z : ℂ => ∏ j : Fin M, (iteratedDeriv (j : ℕ) Φ z) ^ (e α j) := by
      funext z
      simp [Finset.prod_apply]
    rwa [h2] at h1
  have h1 : DifferentiableOn ℂ
      (∑ α : Fin N, fun z : ℂ => d α * ∏ j : Fin M, (iteratedDeriv (j : ℕ) Φ z) ^ (e α j))
      (verticalStrip σ R) :=
    DifferentiableOn.sum fun α _ => (hprod α).const_mul _
  have h2 : (∑ α : Fin N, fun z : ℂ => d α * ∏ j : Fin M, (iteratedDeriv (j : ℕ) Φ z) ^ (e α j))
      = fun z : ℂ => jetPoly d e (fun j : Fin M => iteratedDeriv (j : ℕ) Φ z) := by
    funext z
    simp [jetPoly, Finset.sum_apply]
  rwa [h2] at h1

/-- **A jet polynomial relation valid on the central line is valid on the strip.** -/
theorem jetPoly_eqOn_zero_of_line (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ)
    (hline : ∀ t : ℝ, jetPoly d e
      (fun j : Fin M => iteratedDeriv (j : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    {z : ℂ} (hz : z ∈ verticalStrip σ R) :
    jetPoly d e (fun j : Fin M => iteratedDeriv (j : ℕ) Φ z) = 0 := by
  have h := eqOn_of_eqOn_line hR (differentiableOn_jetPoly_jets hΦ d e)
    (differentiableOn_const (0 : ℂ)) (fun t => by simpa using hline t) hz
  simpa using h

end GaloisForLFunctions
