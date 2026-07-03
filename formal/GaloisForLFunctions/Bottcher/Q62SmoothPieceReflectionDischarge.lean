/-
# Discharging smooth-piece rigidity through the harmonic reflection

`SmoothPieceRigidity c₁ c₂` (`HbothconnAssembly.lean`) is the P6 gatekeeper of the both-connected
q62 lane: no relatively-open piece of `J_{c₁}` lies in the modulus-one locus of one branch of a
separable analytic-coefficient root family.  The whole harmonic Schwarz-reflection stack
(`continuesAcross_of_basinBranch`, `BottcherArcExtension.lean`) discharges it from a single geometric
datum: at a frontier point of the piece, the matched branch `wfam kk` **equals the Böttcher branch**
`β` on the basin side and is a non-critical local biholomorphism.  From that, `β` continues across the
frontier point, contradicting the natural boundary `hnb_of_mem_mandelbrot_connected`.

This file isolates exactly that datum as `SmoothPieceReflectionData` and proves
`smoothPieceRigidity_of_reflectionData`.  The residual `SmoothPieceReflectionData` is the shared deep
content of the both-connected endgame — the branch-boundary identification on a one-sided basin
neighbourhood (co-countable for connected `c₁`) — the same input the disk-model route consumes; every
analytic ingredient (the Dirichlet problem, harmonic max principle, line and circle Koebe reflection,
Green boundary regularity, the global modulus, the local inverse, the arc-is-frontier separation) is
discharged upstream.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.HbothconnAssembly
import GaloisForLFunctions.Bottcher.BottcherArcExtension
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb

open Polynomial Set Metric Filter Topology

namespace Bottcher

/-- **The reflection datum for smooth-piece rigidity.**  For the smooth-piece configuration (the
`SmoothPieceRigidity` hypotheses) and a Böttcher branch `β` on the basin, a frontier point `z₀` of the
piece at which some root branch `wfam kk` is a non-critical local biholomorphism (`AnalyticAt`,
`deriv ≠ 0`, `‖·‖ = 1`) and **equals `β` on the basin side** (`hgβ`).  This is the branch-boundary
identification on a one-sided basin neighbourhood — the residual deep content of the both-connected
endgame, isolated from all of the analytic reflection machinery. -/
def SmoothPieceReflectionData (c₁ c₂ : ℂ) (β : ℂ → ℂ) : Prop :=
  ∀ (a : ℕ → ℂ → ℂ) (sT : Finset ℕ) (N : ℕ) (wfam : Fin N → ℂ → ℂ) (z₁ : ℂ) (ρ ρ₂ : ℝ)
    (k : Fin N) (Uop S : Set ℂ),
    sT ⊆ Finset.range (N + 1) → N ∈ sT → 1 ≤ N → 0 < ρ → 0 < ρ₂ →
    (∀ i ∈ sT, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ) →
    a N z₁ ≠ 0 → (fibrePoly a sT z₁).Separable →
    (∀ ζ : ℂ, ‖ζ‖ = 1 → ¬ ∀ z ∈ (filledJulia c₂)ᶜ, ∑ i ∈ sT, a i z * ζ ^ i = 0) →
    (∀ k', ContinuousOn (wfam k') (Metric.ball z₁ ρ)) →
    (∀ z ∈ Metric.ball z₁ ρ, ∀ k' l, k' ≠ l → wfam k' z ≠ wfam l z) →
    (∀ z ∈ Metric.ball z₁ ρ, (fibrePoly a sT z).natDegree = N) →
    (∀ k', ∀ z ∈ Metric.ball z₁ ρ, ∑ i ∈ sT, a i z * (wfam k' z) ^ i = 0) →
    z₁ ∈ frontier (filledJulia c₁) →
    IsClosed S → S.Nonempty → S ⊆ frontier (filledJulia c₁) → S ⊆ Metric.ball z₁ ρ →
    S ⊆ (filledJulia c₂)ᶜ →
    S = frontier (filledJulia c₁) ∩ Metric.closedBall z₁ ρ₂ →
    IsOpen Uop → (Uop ∩ S).Nonempty → (∀ x ∈ Uop ∩ S, ‖wfam k x‖ = 1) →
    ∃ (z₀ : ℂ) (kk : Fin N), z₀ ∈ frontier (filledJulia c₁) ∧
      AnalyticAt ℂ (wfam kk) z₀ ∧ deriv (wfam kk) z₀ ≠ 0 ∧ ‖wfam kk z₀‖ = 1 ∧
      (∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c₁)ᶜ → wfam kk z = β z)

/-- **Smooth-piece rigidity from the reflection datum.**  For connected `c₁ ∈ mandelbrot ∖ {0,-2}`, if
every Böttcher branch admits the reflection datum, then `SmoothPieceRigidity c₁ c₂` holds: the datum's
basin-branch identification feeds `continuesAcross_of_basinBranch`, producing a continuation of `β`
across a frontier point that contradicts the natural boundary.  This lands the entire harmonic
Schwarz-reflection stack on the both-connected gatekeeper, reducing it to exactly the branch-boundary
identification `SmoothPieceReflectionData`. -/
theorem smoothPieceRigidity_of_reflectionData {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hdata : ∀ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        SmoothPieceReflectionData c₁ c₂ β) :
    SmoothPieceRigidity c₁ c₂ := by
  obtain ⟨β, hβan, _hβesc, hβmod, hnb⟩ := hnb_of_mem_mandelbrot_connected hc₁M hc₁0 hc₁2 hconn₁
  intro a sT N wfam z₁ ρ ρ₂ k Uop S hsupp hN hN1 hρ hρ₂ ha haN hsep hunit hcont hdist hdeg
    hroot hz₁front hSclosed hSne hSfront hSball hSK₂ hSshape hUopen hUSne hmod1
  obtain ⟨z₀, kk, hz₀front, hφAt, hd0, hmod, hgβ⟩ :=
    hdata β hβan hβmod a sT N wfam z₁ ρ ρ₂ k Uop S hsupp hN hN1 hρ hρ₂ ha haN hsep hunit hcont
      hdist hdeg hroot hz₁front hSclosed hSne hSfront hSball hSK₂ hSshape hUopen hUSne hmod1
  exact hnb z₀ hz₀front (continuesAcross_of_basinBranch hφAt hd0 hmod hz₀front hgβ hβan hβmod)

end Bottcher
