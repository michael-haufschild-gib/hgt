import GaloisForLFunctions.HTGeometry.CarrierRepresentative
import GaloisForLFunctions.HTGeometry.StripJetSeparationTimeDep

/-!
# Separation of carrier points inside one fibre

Two points of a joint carrier whose representatives have the same first component — the fibre
condition — are separated by the jets of the second component alone: on that fibre both second
components solve one and the same relation with varying coefficients, so a finite jet at one time
determines them, and the joint representatives then agree.

This is the relative form of the jet separation used by an absolute frequency-rank bound: nothing is
asked of the first component beyond that it is shared.
-/

open Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r : ℝ}

/-- **Regular jets of the second component separate carrier points of one fibre.** -/
theorem carrier_eq_of_jet_eq_rel {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [CompleteSpace E₁] (hRpos : 0 < r)
    {p : ℝ →ᵇ (E₁ × ℂ)} (hpu : UniformContinuous (fun x => p x))
    {n : ℕ} (hn : 0 < n) {G H : ℂ → E₁ × ℂ}
    (hGdiff : DifferentiableOn ℂ G (verticalStrip σ r))
    (hHdiff : DifferentiableOn ℂ H (verticalStrip σ r))
    (hcoef : Set.EqOn (fun z => (G z).1) (fun z => (H z).1) (verticalStrip σ r))
    {P : ℝ → (Fin (n + 1) → ℂ) → ℂ}
    {P' : ℝ → (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S)
    (hPd : ∀ t, ∀ y ∈ S, HasFDerivWithinAt (P t) ((P' t y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ∀ y ∈ S, ‖P' t y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖)
    (hGS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hGP : ∀ t : ℝ, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hHS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hHP : ∀ t : ℝ, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n,
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
        = iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
    {x y : BohrHull p}
    (hGx : ∀ t : ℝ, G ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    (hHy : ∀ t : ℝ, H ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (y + bohrIota p t)) :
    x = y := by
  have hG2 : DifferentiableOn ℂ (fun z => (G z).2) (verticalStrip σ r) :=
    (ContinuousLinearMap.snd ℂ E₁ ℂ).differentiable.comp_differentiableOn hGdiff
  have hH2 : DifferentiableOn ℂ (fun z => (H z).2) (verticalStrip σ r) :=
    (ContinuousLinearMap.snd ℂ E₁ ℂ).differentiable.comp_differentiableOn hHdiff
  have hsecond : Set.EqOn (fun z => (G z).2) (fun z => (H z).2) (verticalStrip σ r) :=
    eqOn_of_line_jet_eq_implicit_timeDep hRpos hn hG2 hH2 hS hPd hC hbound hdom
      hGS hGP hHS hHP hjet
  have heq : Set.EqOn G H (verticalStrip σ r) := by
    intro z hz
    exact Prod.ext (hcoef hz) (hsecond hz)
  refine bohrHull_ext hpu fun t => ?_
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ r := by
    show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| < r
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    simpa using hRpos
  have h := heq hmem
  rw [hGx t, hHy t] at h
  exact h

/-- **Local form: regularity near one sample time suffices.** -/
theorem carrier_eq_of_jet_eq_local_rel {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [CompleteSpace E₁] (hRpos : 0 < r)
    {p : ℝ →ᵇ (E₁ × ℂ)} (hpu : UniformContinuous (fun x => p x))
    {n : ℕ} (hn : 0 < n) {G H : ℂ → E₁ × ℂ}
    (hGdiff : DifferentiableOn ℂ G (verticalStrip σ r))
    (hHdiff : DifferentiableOn ℂ H (verticalStrip σ r))
    (hcoef : Set.EqOn (fun z => (G z).1) (fun z => (H z).1) (verticalStrip σ r))
    {P : ℝ → (Fin (n + 1) → ℂ) → ℂ}
    {P' : ℝ → (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) {t₀ : ℝ}
    (hPd : ∀ᶠ t : ℝ in nhds t₀, ∀ y ∈ S,
      HasFDerivWithinAt (P t) ((P' t y).restrictScalars ℝ) S y)
    (hbound : ∀ᶠ t : ℝ in nhds t₀, ∀ y ∈ S, ‖P' t y - L‖ ≤ C)
    (hGS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hGP : ∀ᶠ t : ℝ in nhds t₀, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hHS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hHP : ∀ᶠ t : ℝ in nhds t₀, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hjet : ∀ k : Fin n,
      iteratedDeriv (k : ℕ) (fun z => (G z).2) ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
        = iteratedDeriv (k : ℕ) (fun z => (H z).2) ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
    {x y : BohrHull p}
    (hGx : ∀ t : ℝ, G ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    (hHy : ∀ t : ℝ, H ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (y + bohrIota p t)) :
    x = y := by
  have hG2 : DifferentiableOn ℂ (fun z => (G z).2) (verticalStrip σ r) :=
    (ContinuousLinearMap.snd ℂ E₁ ℂ).differentiable.comp_differentiableOn hGdiff
  have hH2 : DifferentiableOn ℂ (fun z => (H z).2) (verticalStrip σ r) :=
    (ContinuousLinearMap.snd ℂ E₁ ℂ).differentiable.comp_differentiableOn hHdiff
  have hsecond : Set.EqOn (fun z => (G z).2) (fun z => (H z).2) (verticalStrip σ r) :=
    eqOn_of_line_jet_eq_implicit_local_timeDep hRpos hn hG2 hH2 hS hC hdom hPd hbound
      hGS hGP hHS hHP hjet
  have heq : Set.EqOn G H (verticalStrip σ r) := by
    intro z hz
    exact Prod.ext (hcoef hz) (hsecond hz)
  refine bohrHull_ext hpu fun t => ?_
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ r := by
    show |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| < r
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hre]
    simpa using hRpos
  have h := heq hmem
  rw [hGx t, hHy t] at h
  exact h


end GaloisForLFunctions
