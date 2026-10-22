import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationSplit
import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedPoisson

/-!
# The depleted Meyer quotient and its periodization sequence

Deleting the `p`-Euler orbit replaces the admitted sector `Z(H_∩)` by `Δ_p Z(H_∩)`.  Because `Δ_p`
is injective, a class survives the depletion exactly when it was already admitted, so the induced
map on quotients is injective; and because `Δ_p H_- = ker Per_p`, its image is exactly the kernel of
the descended periodization.

* `DeningerMeyerQuotient` : `M_ζ = H_- / Z(H_∩)`.
* `DeningerDepletedQuotient` : `M_ζ^{(p)} = H_- / Δ_p Z(H_∩)`.
* `deningerIota` : `ι_p([g]) = [Δ_p g]`, **injective**.
* `deningerPerBar` : the descended periodization, **surjective**.
* `deningerIota_range_eq_perBar_ker` : **the admitted sector is exactly the kernel.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- Meyer's admitted sector `Z(H_∩)`. -/
def deningerPoissonRangeSubmodule : Submodule ℂ DeningerExpSchwartz :=
  LinearMap.range deningerPoissonSourceLM

/-- The depleted admitted sector `Δ_p Z(H_∩)`. -/
def deningerDepletedPoissonRange (L : ℝ) : Submodule ℂ DeningerExpSchwartz :=
  LinearMap.range ((deningerPeriodizationDefect L).comp deningerPoissonSourceLM)

/-- The Meyer quotient `M_ζ`. -/
abbrev DeningerMeyerQuotient := DeningerExpSchwartz ⧸ deningerPoissonRangeSubmodule

/-- The depleted Meyer quotient `M_ζ^{(p)}`. -/
abbrev DeningerDepletedQuotient (L : ℝ) :=
  DeningerExpSchwartz ⧸ deningerDepletedPoissonRange L

theorem deningerPoissonRange_le_comap (L : ℝ) :
    deningerPoissonRangeSubmodule
      ≤ Submodule.comap (deningerPeriodizationDefect L) (deningerDepletedPoissonRange L) := by
  rintro g hg
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hg
  exact LinearMap.mem_range.2 ⟨f, rfl⟩

theorem deningerDepletedRange_le_ker {L : ℝ} (hL : 0 < L) :
    deningerDepletedPoissonRange L ≤ LinearMap.ker (deningerPeriodizationMap hL) := by
  rintro h hh
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hh
  rw [deningerPeriodizationMap_ker hL]
  exact LinearMap.mem_range.2 ⟨deningerPoissonSourceLM f, rfl⟩

/-- **The depletion map on quotients**, `ι_p([g]) = [Δ_p g]`. -/
def deningerIota (L : ℝ) : DeningerMeyerQuotient →ₗ[ℂ] DeningerDepletedQuotient L :=
  Submodule.mapQ _ _ (deningerPeriodizationDefect L) (deningerPoissonRange_le_comap L)

theorem deningerIota_mk (L : ℝ) (g : DeningerExpSchwartz) :
    deningerIota L (Submodule.Quotient.mk g)
      = Submodule.Quotient.mk (deningerPeriodizationDefect L g) := rfl

/-- **The descended periodization** `Per̄_p([h]) = Per_p h`. -/
def deningerPerBar {L : ℝ} (hL : 0 < L) :
    DeningerDepletedQuotient L →ₗ[ℂ] DeningerSmoothPeriodic L :=
  Submodule.liftQ _ (deningerPeriodizationMap hL) (deningerDepletedRange_le_ker hL)

theorem deningerPerBar_mk {L : ℝ} (hL : 0 < L) (h : DeningerExpSchwartz) :
    deningerPerBar hL (Submodule.Quotient.mk h) = deningerPeriodizationMap hL h := rfl

/-- **The depletion map on quotients is injective.**  A depleted class is admitted exactly when the
original class was, because `Δ_p` is injective. -/
theorem deningerIota_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (deningerIota L) := by
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.eq_bot_iff _ |>.2 fun x hx => ?_
  induction x using Submodule.Quotient.induction_on with
  | H g =>
    rw [LinearMap.mem_ker, deningerIota_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨f, hf⟩ := LinearMap.mem_range.1 hx
    have hmem : deningerPeriodizationDefect L g ∈ Set.range (fun f : DeningerMeyerCap =>
        deningerPeriodizationDefect L (deningerPoissonSource f)) := ⟨f, hf⟩
    have hg := (deningerOnePrimeConservativity hL g).1 hmem
    obtain ⟨f₀, hf₀⟩ := hg
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.2 ⟨f₀, hf₀⟩

/-- **The descended periodization is surjective.** -/
theorem deningerPerBar_surjective {L : ℝ} (hL : 0 < L) :
    Function.Surjective (deningerPerBar hL) := by
  intro F
  obtain ⟨h, hh⟩ := deningerPeriodizationMap_surjective hL F
  exact ⟨Submodule.Quotient.mk h, by rw [deningerPerBar_mk]; exact hh⟩

/-- **The admitted middle sector is canonical**: the image of the depletion map is exactly the
kernel of the descended periodization. -/
theorem deningerIota_range_eq_perBar_ker {L : ℝ} (hL : 0 < L) :
    LinearMap.range (deningerIota L) = LinearMap.ker (deningerPerBar hL) := by
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    induction y using Submodule.Quotient.induction_on with
    | H g =>
      rw [LinearMap.mem_ker, deningerIota_mk, deningerPerBar_mk]
      have : deningerPeriodizationDefect L g ∈ LinearMap.ker (deningerPeriodizationMap hL) := by
        rw [deningerPeriodizationMap_ker hL]
        exact LinearMap.mem_range.2 ⟨g, rfl⟩
      exact LinearMap.mem_ker.1 this
  · rintro x hx
    induction x using Submodule.Quotient.induction_on with
    | H h =>
      rw [LinearMap.mem_ker, deningerPerBar_mk] at hx
      have hker : h ∈ LinearMap.ker (deningerPeriodizationMap hL) := LinearMap.mem_ker.2 hx
      rw [deningerPeriodizationMap_ker hL] at hker
      obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hker
      exact LinearMap.mem_range.2 ⟨Submodule.Quotient.mk g, by rw [deningerIota_mk, hg]⟩

/-- **The depleted periodization sequence.**  `0 → M_ζ → M_ζ^{(p)} → C^∞(ℝ/Lℤ) → 0` is exact. -/
theorem deningerDepletedSequence_exact {L : ℝ} (hL : 0 < L) :
    Function.Injective (deningerIota L)
      ∧ LinearMap.range (deningerIota L) = LinearMap.ker (deningerPerBar hL)
      ∧ Function.Surjective (deningerPerBar hL) :=
  ⟨deningerIota_injective hL, deningerIota_range_eq_perBar_ker hL, deningerPerBar_surjective hL⟩

end

end RHTower
