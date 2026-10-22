import GaloisForLFunctions.RHTower.Deninger.DeningerEulerDepletionTower
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonPreimage

/-!
# The depleted Poisson embedding

The Poisson operator is injective: two members of Meyer's space with the same Poisson sum agree on
the ray, hence everywhere by evenness.  Composing with a depletion operator therefore stays
injective, and the one-prime conservativity law is exactly that injectivity.

* `deningerPoissonSource_injective` : **`Z` is injective.**
* `deningerDepletedPoisson_injective` : **`(9)`/`(17)`: `Z^{(S)}` is injective.**
* `deningerOnePrimeConservativity` : **`(14)`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- **The Poisson operator is injective.** -/
theorem deningerPoissonSource_injective : Function.Injective deningerPoissonSource := by
  intro f g hfg
  have hray : ∀ x : ℝ, 0 < x →
      deningerPoissonValue ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
        = deningerPoissonValue ((g : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x := by
    intro x hx
    have hf := congrArg
      (fun u : DeningerExpSchwartz => ((u : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log x)) hfg
    rw [deningerPoissonSource_apply, deningerPoissonSource_apply,
      deningerPoissonLog_eq, deningerPoissonLog_eq, Real.exp_log hx] at hf
    exact hf
  have hpt := deningerPoissonValue_injOn (deningerMeyerCap_zero f.2)
    (deningerMeyerCap_zero g.2) hray
  refine Subtype.ext (SchwartzMap.ext fun x => ?_)
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx : (0 : ℝ) < -x := by linarith
    have h := hpt (-x) hx
    rw [deningerMeyerCap_even f.2 x, deningerMeyerCap_even g.2 x] at h
    exact h
  · rw [hzero, deningerMeyerCap_zero f.2, deningerMeyerCap_zero g.2]
  · exact hpt x hpos

/-- The depleted Poisson embedding `Z^{(S)} = Δ_S ∘ Z`. -/
def deningerDepletedPoisson (S : List ℝ) (f : DeningerMeyerCap) : DeningerExpSchwartz :=
  deningerDepletion S (deningerPoissonSource f)

/-- **`(9)`/`(17)`: the depleted Poisson embedding is injective.** -/
theorem deningerDepletedPoisson_injective (S : List ℝ) (hS : ∀ L ∈ S, 0 < L) :
    Function.Injective (deningerDepletedPoisson S) := fun _ _ hab =>
  deningerPoissonSource_injective (deningerDepletion_injective S hS hab)

/-- **`(14)`: the exact one-prime conservative boundary law.** -/
theorem deningerOnePrimeConservativity {L : ℝ} (hL : 0 < L) (g : DeningerExpSchwartz) :
    deningerPeriodizationDefect L g ∈ Set.range (fun f : DeningerMeyerCap =>
        deningerPeriodizationDefect L (deningerPoissonSource f))
      ↔ g ∈ Set.range deningerPoissonSource := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (deningerPeriodizationDefect_injective hL hf).symm ▸ rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- The depleted admitted sector of a finite list of periods. -/
theorem deningerDepletion_conservativity (S : List ℝ) (hS : ∀ L ∈ S, 0 < L)
    (g : DeningerExpSchwartz) :
    deningerDepletion S g ∈ Set.range (deningerDepletedPoisson S)
      ↔ g ∈ Set.range deningerPoissonSource := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (deningerDepletion_injective S hS hf).symm ▸ rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

end

end RHTower
