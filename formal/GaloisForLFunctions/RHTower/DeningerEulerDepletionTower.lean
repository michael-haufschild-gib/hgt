import GaloisForLFunctions.RHTower.DeningerMeyerPeriodization
import GaloisForLFunctions.RHTower.DeningerEulerDepletedKernel

/-!
# The finite Euler-depletion tower

The periodization defects of distinct periods commute, because translations do, so a finite list of
periods gives a single depletion operator independent of any ordering.  Each factor is injective on
the source, hence so is the product.

* `deningerPeriodizationDefect_comm` : **the defects commute.**
* `deningerDepletion` : the depletion operator `Δ_S` of a finite list of periods.
* `deningerDepletion_injective` : **every `Δ_S` is injective.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

theorem deningerExpShiftSource_comm (L M : ℝ) (f : DeningerExpSchwartz) :
    deningerExpShiftSource L (deningerExpShiftSource M f)
      = deningerExpShiftSource M (deningerExpShiftSource L f) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerExpShiftSource_apply, deningerExpShiftSource_apply,
    deningerExpShiftSource_apply, deningerExpShiftSource_apply,
    show t + L + M = t + M + L by ring]

/-- **The periodization defects of two periods commute.** -/
theorem deningerPeriodizationDefect_comm (L M : ℝ) (f : DeningerExpSchwartz) :
    deningerPeriodizationDefect L (deningerPeriodizationDefect M f)
      = deningerPeriodizationDefect M (deningerPeriodizationDefect L f) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerPeriodizationDefect_apply, deningerPeriodizationDefect_apply,
    deningerPeriodizationDefect_apply, deningerPeriodizationDefect_apply,
    deningerPeriodizationDefect_apply, deningerPeriodizationDefect_apply,
    show t + L + M = t + M + L by ring]
  ring

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
theorem deningerDepletion_injective (S : List ℝ) (hS : ∀ L ∈ S, 0 < L) :
    Function.Injective (deningerDepletion S) := by
  induction S with
  | nil => exact fun a b h => h
  | cons L Ls ih =>
    have hLpos : 0 < L := hS L List.mem_cons_self
    have hrest : ∀ M ∈ Ls, 0 < M := fun M hM => hS M (List.mem_cons_of_mem L hM)
    intro a b hab
    rw [deningerDepletion_cons, LinearMap.comp_apply, LinearMap.comp_apply] at hab
    exact ih hrest (deningerPeriodizationDefect_injective hLpos hab)

end

end RHTower
