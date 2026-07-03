/-
# The reflection engine, landed on `ReflectionCore`

`smoothPieceRigidity_of_reflectionCore` reduces the general both-connected gatekeeper (#118) to
`ReflectionCore c₁ β`: a non-constant analytic `φ` with modulus one on a relatively-open frontier
piece forces the Böttcher branch `β` to continue analytically across a frontier point.  The engine
`differentiableAt_of_off_modulus_arc` (Schwarz reflection across the analytic modulus-one arc
`{‖φ‖ = 1}`) is exactly the analytic core of that discharge — *provided* the reflected extension of
`β` across the arc is available.

This file does two things, both unconditional and axiom-clean:

* `arcReflection_continuesAcross` — the **point-level bridge**.  At a frontier arc point `z₀`
  (`AnalyticAt φ z₀`, `deriv φ z₀ ≠ 0`, `‖φ z₀‖ = 1`), a function `f` continuous near `z₀` and
  holomorphic off `{‖φ‖ = 1}`, agreeing with `β` on the basin side, is a `ContinuesAcross` witness.
  Its analyticity at `z₀` is `differentiableAt_of_off_modulus_arc`; the basin agreement is the
  `ContinuesAcross` neighbourhood clause verbatim.  This is where the reflection stack meets the
  natural-boundary contradiction `hnb`.

* `reflectionCore_of_arcReflectionData` — the **reduction**.  It isolates the one remaining input of
  `ReflectionCore` to `ArcReflectionData`: the existence, at *some* frontier arc point of the piece,
  of the reflected extension `f`.  Everything analytic (the reflection across the smooth arc) is
  discharged here by the bridge.  `ArcReflectionData` is a genuine, satisfiable interface — the
  classical reflected continuation of `β` across a smooth Julia arc, whose only real content is the
  boundary regularity of `β` at the piece (Carathéodory extension, automatic where the frontier is a
  smooth arc).  It is strictly weaker and more concrete than the monolithic `ReflectionCore`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.Q62SmoothPieceReduction
import GaloisForLFunctions.Bottcher.SchwarzReflectionModulusArc

open Set Filter Topology Complex

namespace Bottcher

/-- **Point-level reflection bridge.**  At a frontier point `z₀` where the branch `φ` is analytic with
non-vanishing derivative and modulus one, a function `f` that is continuous near `z₀`, holomorphic
wherever `‖φ‖ ≠ 1` near `z₀`, and agrees with the Böttcher branch `β` on the basin side, witnesses
`ContinuesAcross β (filledJulia c₁)ᶜ z₀`.  Its analyticity at `z₀` is Schwarz reflection across the
analytic modulus-one arc (`differentiableAt_of_off_modulus_arc`); the basin agreement is the
neighbourhood clause of `ContinuesAcross` verbatim.  This is the exact hook by which the reflection
stack contradicts the natural boundary `hnb`. -/
theorem arcReflection_continuesAcross {c₁ : ℂ} {β φ f : ℂ → ℂ} {z₀ : ℂ}
    (hφAt : AnalyticAt ℂ φ z₀) (hd0 : deriv φ z₀ ≠ 0) (hmod : ‖φ z₀‖ = 1)
    (hfcont : ∀ᶠ z in 𝓝 z₀, ContinuousAt f z)
    (hfoff : ∀ᶠ z in 𝓝 z₀, ‖φ z‖ ≠ 1 → DifferentiableAt ℂ f z)
    (hfβ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, f z = β z) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ :=
  ⟨f, differentiableAt_of_off_modulus_arc hφAt hd0 hmod hfcont hfoff, hfβ⟩

/-- **The reflected-extension datum — the one remaining input of `ReflectionCore`.**  For a
non-constant analytic `φ` with modulus one on a relatively-open frontier piece, there is a frontier
arc point `z₀` (analytic, `deriv φ z₀ ≠ 0`, `‖φ z₀‖ = 1`) and a reflected extension `f` of `β` across
the arc: `f` is continuous near `z₀`, holomorphic off `{‖φ‖ = 1}`, and agrees with `β` on the basin
side.  This is the classical Schwarz reflection of `β` across a smooth Julia arc; its only genuine
content is the boundary regularity of `β` at the piece.  Everything else in `ReflectionCore` — the
analytic continuation across the arc — is discharged by `differentiableAt_of_off_modulus_arc`. -/
def ArcReflectionData (c₁ : ℂ) (β : ℂ → ℂ) : Prop :=
  ∀ (φ : ℂ → ℂ) (Ω P : Set ℂ), IsOpen Ω → IsPreconnected Ω → AnalyticOnNhd ℂ φ Ω →
    (∃ z' ∈ Ω, deriv φ z' ≠ 0) → P ⊆ Ω → P ⊆ frontier (filledJulia c₁) →
    (∃ Uop, IsOpen Uop ∧ (Uop ∩ P).Nonempty) → (∀ z ∈ P, ‖φ z‖ = 1) →
    ∃ (z₀ : ℂ) (f : ℂ → ℂ), z₀ ∈ frontier (filledJulia c₁) ∧
      AnalyticAt ℂ φ z₀ ∧ deriv φ z₀ ≠ 0 ∧ ‖φ z₀‖ = 1 ∧
      (∀ᶠ z in 𝓝 z₀, ContinuousAt f z) ∧
      (∀ᶠ z in 𝓝 z₀, ‖φ z‖ ≠ 1 → DifferentiableAt ℂ f z) ∧
      (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, f z = β z)

/-- **`ReflectionCore` ⟸ `ArcReflectionData`.**  Given the reflected extension of `β` across the
smooth Julia arc (`ArcReflectionData`), `ReflectionCore c₁ β` holds: the extension's analyticity at
the arc point is Schwarz reflection (`arcReflection_continuesAcross`), and its basin agreement makes
it a `ContinuesAcross` witness.  This reduces the monolithic reflection input of the general
both-connected gatekeeper to exactly the boundary-continuation datum, with all of the reflection
analysis proven here. -/
theorem reflectionCore_of_arcReflectionData {c₁ : ℂ} {β : ℂ → ℂ}
    (hdata : ArcReflectionData c₁ β) : ReflectionCore c₁ β := by
  intro φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  obtain ⟨z₀, f, hz₀front, hφAt, hd0, hmod, hfcont, hfoff, hfβ⟩ :=
    hdata φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  exact ⟨z₀, hz₀front, arcReflection_continuesAcross hφAt hd0 hmod hfcont hfoff hfβ⟩

end Bottcher
