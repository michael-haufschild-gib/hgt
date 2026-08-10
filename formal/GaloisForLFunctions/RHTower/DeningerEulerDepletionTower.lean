import GaloisForLFunctions.RHTower.DeningerGreenSumSource
import GaloisForLFunctions.RHTower.DeningerEulerDepletedKernel

/-!
# The finite Euler-depletion tower

The periodization defects of distinct primes commute, because translations do, so a finite set of
primes gives a single depletion operator independent of any ordering.  Each factor is injective on
the source, hence so is the product, and the depleted Poisson embedding `Z^{(S)} = Δ_S Z` is
injective for every finite `S`.

The one-prime conservativity law `(14)` — `Δ_p g` is a depleted boundary exactly when `g` is a
boundary — is injectivity of `Δ_p` and nothing more.

* `deningerPeriodizationDefect_comm` : the defects commute.
* `deningerDepletion` : the depletion operator `Δ_S` of a finite set of periods.
* `deningerDepletion_injective` : **every `Δ_S` is injective.**
* `deningerPoissonSource_injective` : `Z` is injective.
* `deningerOnePrimeConservativity` : **`(14)`.**
* `deningerDepletedPoisson_injective` : **`(9)`/`(17)`: `Z^{(S)}` is injective.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-! ## Commuting defects -/

theorem deningerExpShiftSource_comm (L M : ℝ) (f : DeningerExpSchwartz) :
    deningerExpShiftSource L (deningerExpShiftSource M f)
      = deningerExpShiftSource M (deningerExpShiftSource L f) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  show ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + L + M)
    = ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + M + L)
  congr 1
  ring

/-- **The periodization defects of two periods commute.** -/
theorem deningerPeriodizationDefect_comm (L M : ℝ) (f : DeningerExpSchwartz) :
    deningerPeriodizationDefect L (deningerPeriodizationDefect M f)
      = deningerPeriodizationDefect M (deningerPeriodizationDefect L f) := by
  simp only [deningerPeriodizationDefect, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [deningerExpShiftSource_comm L M f]
  abel

/-! ## The depletion operator of a finite set of periods -/

/-- The depletion operator `Δ_S = ∏_{L ∈ S} Δ_L` of a list of periods. -/
def deningerDepletion : List ℝ → DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz
  | [] => LinearMap.id
  | L :: Ls => (deningerPeriodizationDefect L).comp (deningerDepletion Ls)

@[simp]
theorem deningerDepletion_nil : deningerDepletion [] = LinearMap.id := rfl

@[simp]
theorem deningerDepletion_cons (L : ℝ) (Ls : List ℝ) :
    deningerDepletion (L :: Ls) = (deningerPeriodizationDefect L).comp (deningerDepletion Ls) :=
  rfl

/-- **Every depletion operator is injective**, provided each period is positive. -/
theorem deningerDepletion_injective : ∀ {S : List ℝ}, (∀ L ∈ S, 0 < L) →
    Function.Injective (deningerDepletion S)
  | [], _ => by
    rw [deningerDepletion_nil]
    exact fun a b h => h
  | L :: Ls, hS => by
    rw [deningerDepletion_cons]
    refine Function.Injective.comp ?_ ?_
    · exact deningerPeriodizationDefect_injective (hS L (List.mem_cons_self))
    · exact deningerDepletion_injective fun M hM => hS M (List.mem_cons_of_mem L hM)

/-! ## Injectivity of the Poisson embedding -/

/-- **The Poisson operator is injective.**  Two members of Meyer's space with the same Poisson sum
agree on the ray, hence everywhere by evenness and continuity. -/
theorem deningerPoissonSource_injective : Function.Injective deningerPoissonSource := by
  intro f g hfg
  have hray : ∀ x : ℝ, 0 < x →
      deningerPoissonValue ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
        = deningerPoissonValue ((g : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x := by
    intro x hx
    have hf := congrArg
      (fun u : DeningerExpSchwartz => ((u : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log x)) hfg
    simp only [deningerPoissonSource_apply] at hf
    rw [deningerPoissonLog_eq, deningerPoissonLog_eq, Real.exp_log hx] at hf
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

/-! ## The depleted Poisson embedding -/

/-- The depleted Poisson embedding `Z^{(S)} = Δ_S ∘ Z`. -/
def deningerDepletedPoisson (S : List ℝ) (f : DeningerMeyerCap) : DeningerExpSchwartz :=
  deningerDepletion S (deningerPoissonSource f)

/-- **`(9)`/`(17)`: the depleted Poisson embedding is injective.** -/
theorem deningerDepletedPoisson_injective {S : List ℝ} (hS : ∀ L ∈ S, 0 < L) :
    Function.Injective (deningerDepletedPoisson S) :=
  Function.Injective.comp (deningerDepletion_injective hS) deningerPoissonSource_injective

/-- **`(14)`: the exact one-prime conservative boundary law.**  A depleted value is a depleted
boundary exactly when the undepleted value is a boundary. -/
theorem deningerOnePrimeConservativity {L : ℝ} (hL : 0 < L) (g : DeningerExpSchwartz) :
    deningerPeriodizationDefect L g ∈ Set.range (fun f : DeningerMeyerCap =>
        deningerPeriodizationDefect L (deningerPoissonSource f))
      ↔ g ∈ Set.range deningerPoissonSource := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (deningerPeriodizationDefect_injective hL hf).symm ▸ rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- The depleted admitted sector of a finite set of periods. -/
theorem deningerDepletion_conservativity {S : List ℝ} (hS : ∀ L ∈ S, 0 < L)
    (g : DeningerExpSchwartz) :
    deningerDepletion S g ∈ Set.range (deningerDepletedPoisson S)
      ↔ g ∈ Set.range deningerPoissonSource := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    exact (deningerDepletion_injective hS hf).symm ▸ rfl
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

end

end RHTower
