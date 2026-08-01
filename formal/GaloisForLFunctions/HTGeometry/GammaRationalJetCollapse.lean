import GaloisForLFunctions.HTGeometry.GammaRationalCollapse
import GaloisForLFunctions.HTGeometry.JetMonomialAlmostPeriodic

/-!
# The Gamma-rational collapse for an almost periodic solution

A finite differential relation with Gamma-rational coefficients, satisfied by a strip almost periodic
holomorphic function, collapses to a nontrivial constant-coefficient relation between the jets of the
solution at the centre of the strip.

Both sides of the collapse are now unconditional: the coefficient ratios converge because `Γ` decays
on vertical lines, and the jet monomials return to their values along the common return times of the
solution's jets.  No analytic hypothesis is left except the almost periodicity of the solution.
-/

open Filter Topology

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Eq. (27) → (29) for an almost periodic solution of a Gamma-rational relation**, with the
limit coefficient vector named. -/
theorem recurrence_collapse_gamma_rational_jets_explicit {n m : ℕ} {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ r))
    (hap : IsStripAlmostPeriodic Φ σ r) (e : Fin n → Fin m → ℕ)
    (F : Fin n → ℂ → ℂ) (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hQ0 : ∀ α, (Q α).eval 0 ≠ 0) (hP0 : ∀ α, (P α).eval 0 ≠ 0)
    (hF : ∀ (α : Fin n) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (u α)
            * (P α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))
          / ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (v α)
            * (Q α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β) :
    (∑ α, gammaRatioLimit P Q u v β α *
        ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ (σ : ℂ)) ^ (e α j) = 0) ∧
      gammaRatioLimit P Q u v β β = 1 := by
  refine recurrence_collapse_gamma_rational_explicit hσ F
    (fun α s => ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j))
    P Q u v β hQ0 hP0 hF hrel
    (fun α => (isBohrAlmostPeriodic_jetMonomial hr hΦ hap (e α)).1)
    (fun α => (isBohrAlmostPeriodic_jetMonomial hr hΦ hap (e α)).2) hmin


/-- **Eq. (27) → (29) for an almost periodic solution of a Gamma-rational relation.** -/
theorem recurrence_collapse_gamma_rational_jets {n m : ℕ} {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ r))
    (hap : IsStripAlmostPeriodic Φ σ r) (e : Fin n → Fin m → ℕ)
    (F : Fin n → ℂ → ℂ) (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hQ0 : ∀ α, (Q α).eval 0 ≠ 0) (hP0 : ∀ α, (P α).eval 0 ≠ 0)
    (hF : ∀ (α : Fin n) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (u α)
            * (P α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))
          / ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (v α)
            * (Q α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β) :
    ∃ d : Fin n → ℂ,
      (∑ α, d α * ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ (σ : ℂ)) ^ (e α j) = 0) ∧ d β = 1 :=
  ⟨gammaRatioLimit P Q u v β, recurrence_collapse_gamma_rational_jets_explicit hσ hr hΦ hap e F
    P Q u v β hQ0 hP0 hF hrel hmin⟩

end GaloisForLFunctions
