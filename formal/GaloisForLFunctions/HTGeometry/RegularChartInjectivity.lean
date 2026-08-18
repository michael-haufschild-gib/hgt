import GaloisForLFunctions.HTGeometry.StripJetSeparation

/-!
# The jet chart is injective on a regular piece

At a sample time where the annihilating relation is dominant in the top jet, the lower jets of a
strip-holomorphic solution determine it.  Packaged as an `InjOn` statement for a whole family of
solutions, this is the chart hypothesis that the frequency-rank bound consumes: on each piece of a
finite closed cover, one full jet separates the points of the carrier.

The separation itself is the strip jet theorem; what is added here is the passage from "two
solutions with equal jets agree on the strip" to injectivity of the jet map on a family whose
members are determined by their restriction to the strip.
-/

open Set

namespace GaloisForLFunctions

variable {σ R : ℝ} {n : ℕ}

/-- **The lower-jet chart separates strip solutions of a dominant implicit relation.** -/
theorem injOn_lineJet_of_implicit_dominant (hR : 0 < R) (hn : 0 < n)
    {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hPd : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) {t₀ : ℝ}
    (X : Set (ℂ → ℂ))
    (hdiff : ∀ g ∈ X, DifferentiableOn ℂ g (verticalStrip σ R))
    (hXS : ∀ g ∈ X, ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hXP : ∀ g ∈ X, ∀ᶠ t : ℝ in nhds t₀, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hdet : ∀ g ∈ X, ∀ h ∈ X, Set.EqOn g h (verticalStrip σ R) → g = h) :
    Set.InjOn (fun g : ℂ → ℂ => fun k : Fin n =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) X := by
  intro g hg h hh hjet
  refine hdet g hg h hh ?_
  refine eqOn_of_line_jet_eq_implicit_local hR hn (hdiff g hg) (hdiff h hh) hS hPd hC hbound hdom
    (hXS g hg) (hXP g hg) (hXS h hh) (hXP h hh) ?_
  intro k
  exact congrFun hjet k

/-- The same statement restricted to a subfamily: a piece of a cover inherits the chart. -/
theorem injOn_lineJet_of_implicit_dominant_subset (hR : 0 < R) (hn : 0 < n)
    {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hPd : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) {t₀ : ℝ}
    (X F : Set (ℂ → ℂ)) (hFX : F ⊆ X)
    (hdiff : ∀ g ∈ X, DifferentiableOn ℂ g (verticalStrip σ R))
    (hXS : ∀ g ∈ X, ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hXP : ∀ g ∈ X, ∀ᶠ t : ℝ in nhds t₀, P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hdet : ∀ g ∈ X, ∀ h ∈ X, Set.EqOn g h (verticalStrip σ R) → g = h) :
    Set.InjOn (fun g : ℂ → ℂ => fun k : Fin n =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) F :=
  (injOn_lineJet_of_implicit_dominant hR hn hS hPd hC hbound hdom X hdiff hXS hXP hdet).mono hFX

end GaloisForLFunctions
