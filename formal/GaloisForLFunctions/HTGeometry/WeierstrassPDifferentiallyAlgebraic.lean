import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# The Weierstrass `℘` function is differentially algebraic

The elliptic branch of the period-rank law rests on the Weierstrass differential equation
`℘'² = 4℘³ − g₂℘ − g₃`.  Mathlib now proves that equation off the lattice
(`PeriodPair.derivWeierstrassP_sq`), and `deriv ℘ = ℘'` globally.  This file turns those into the
statement the differential-algebra side needs: `℘` satisfies a **global** algebraic differential
relation, hence is differentially algebraic and not hypertranscendental.

The only subtlety is the lattice points, where `℘` carries junk values (`℘ l = 0`) and the
Weierstrass equation itself fails.  Multiplying the equation by the value slot repairs this: the
relation

`(y₁² − 4y₀³ + g₂ y₀ + g₃) · y₀`

vanishes off the lattice because the first factor does, and at a lattice point because `y₀ = ℘ l = 0`.
It is a nonzero polynomial, as one evaluation shows.

This is the first half of the elliptic input to the scalar Stanley–Reisner principalization law: the
remaining half is that *every* function with a lattice of periods lies in `ℂ(℘, ℘')`.
-/

open MvPolynomial

namespace GaloisForLFunctions

variable (L : PeriodPair)

/-- The order-one differential relation satisfied by `℘` on the whole plane: the Weierstrass
equation multiplied by the value slot, which absorbs the junk values at the lattice points. -/
noncomputable def weierstrassPRelation : MvPolynomial (Fin 3) ℂ :=
  (X 2 ^ 2 - 4 * X 1 ^ 3 + C L.g₂ * X 1 + C L.g₃) * X 1

theorem weierstrassPRelation_ne_zero : weierstrassPRelation L ≠ 0 := by
  have key : ∀ a b : ℂ, MvPolynomial.eval ![(0 : ℂ), a, b] (weierstrassPRelation L)
      = (b ^ 2 - 4 * a ^ 3 + L.g₂ * a + L.g₃) * a := by
    intro a b
    simp [weierstrassPRelation]
  intro h
  have e0 := key 1 0
  have e1 := key 1 1
  rw [h, map_zero] at e0 e1
  have hone : (1 : ℂ) = 0 := by linear_combination e0 - e1
  exact one_ne_zero hone

/-- **The Weierstrass `℘` function is differentially algebraic.**  Off the lattice this is the
Weierstrass equation; at a lattice point the value slot vanishes and absorbs the junk value. -/
theorem differentiallyAlgebraic_weierstrassP :
    DifferentiallyAlgebraic (fun z => L.weierstrassP z) := by
  refine ⟨1, weierstrassPRelation L, weierstrassPRelation_ne_zero L, fun z => ?_⟩
  have key : ∀ a b : ℂ, MvPolynomial.eval ![z, a, b] (weierstrassPRelation L)
      = (b ^ 2 - 4 * a ^ 3 + L.g₂ * a + L.g₃) * a := by
    intro a b
    simp [weierstrassPRelation]
  have hpt : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (fun w => L.weierstrassP w) z))
      = ![z, L.weierstrassP z, L.derivWeierstrassP z] := by
    funext i
    fin_cases i
    · simp
    · simp [iteratedDeriv_zero]
    · have h2 : ((Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ)
          (fun w => L.weierstrassP w) z) : Fin 3 → ℂ)) (Fin.succ 1)
          = L.derivWeierstrassP z := by
        rw [Fin.cons_succ]
        simp [iteratedDeriv_one, L.deriv_weierstrassP]
      exact h2
  rw [hpt, key]
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassP_coe ⟨z, hz⟩]
    ring
  · rw [L.derivWeierstrassP_sq z hz]
    ring

/-- Consequently `℘` is not hypertranscendental: the Weierstrass equation is an algebraic
differential equation for it. -/
theorem not_hypertranscendental_weierstrassP :
    ¬ Hypertranscendental (fun z => L.weierstrassP z) :=
  fun h => h (differentiallyAlgebraic_weierstrassP L)

end GaloisForLFunctions
