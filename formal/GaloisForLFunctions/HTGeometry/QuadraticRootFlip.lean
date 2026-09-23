import GaloisForLFunctions.HTGeometry.QuadraticTowerSquareClasses

/-!
# The block flip transposes exactly one pair of quadratic roots

A product of monic quadratics with discriminants `ρ_z²` has roots `(s_z ± ρ_z)/2`, indexed by
`ι × Bool`.  A field automorphism fixing every `s_z`, fixing `ρ_z` for `z ≠ z₀` and negating
`ρ_{z₀}` therefore acts on those roots as the transposition of `(z₀, true)` with `(z₀, false)`.

This is the residue-side half of the deformation argument: composed with
`PowerSeriesSimpleRootLift.map_lift_eq_of_perm` it says that the block flip permutes the *deformed*
roots by the same transposition.

## Main results

* `quadRoot` — the two roots of the `z`-th quadratic.
* `prod_quadratic_eq_prod_quadRoot` — the product of the quadratics splits into those linear
  factors.
* `map_quadRoot_of_flip` — the automorphism permutes them by `Equiv.swap (z₀, true) (z₀, false)`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {L : Type*} [Field L] {ι : Type*}

/-- The two roots of the quadratic `X² − s_z X + p_z` whose discriminant is `ρ_z²`. -/
def quadRoot (s ρ : ι → L) (p : ι × Bool) : L :=
  (s p.1 + (if p.2 then ρ p.1 else -ρ p.1)) / 2

@[simp] theorem quadRoot_true (s ρ : ι → L) (z : ι) :
    quadRoot s ρ (z, true) = (s z + ρ z) / 2 := rfl

@[simp] theorem quadRoot_false (s ρ : ι → L) (z : ι) :
    quadRoot s ρ (z, false) = (s z - ρ z) / 2 := by
  show (s z + -ρ z) / 2 = (s z - ρ z) / 2
  ring_nf

theorem prod_quadratic_eq_prod_quadRoot [Fintype ι] (h2 : (2 : L) ≠ 0)
    (s q ρ : ι → L) (hρ : ∀ z, ρ z * ρ z = s z * s z - 4 * q z) :
    (∏ z, (X ^ (2 : ℕ) - C (s z) * X + C (q z)))
      = ∏ p : ι × Bool, (X - C (quadRoot s ρ p)) := by
  classical
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [quadratic_eq_prod_linear h2 (s z) (q z) (ρ z) (hρ z), Fintype.prod_bool,
    quadRoot_true, quadRoot_false]

/-- **The flip transposes exactly one pair.** -/
theorem map_quadRoot_of_flip [DecidableEq ι] (s ρ : ι → L) (z₀ : ι) (σ : L ≃+* L)
    (hs : ∀ z, σ (s z) = s z)
    (hfix : ∀ z, z ≠ z₀ → σ (ρ z) = ρ z) (hneg : σ (ρ z₀) = -ρ z₀)
    (p : ι × Bool) :
    σ (quadRoot s ρ p) = quadRoot s ρ (Equiv.swap ((z₀, true) : ι × Bool) (z₀, false) p) := by
  classical
  obtain ⟨z, b⟩ := p
  have h2σ : σ (2 : L) = 2 := by
    simpa using map_ofNat σ 2
  by_cases hz : z = z₀
  · subst hz
    rcases b with _ | _
    · rw [show Equiv.swap ((z, true) : ι × Bool) (z, false) (z, false) = (z, true) by
        simp [Equiv.swap_apply_right], quadRoot_false, quadRoot_true,
        map_div₀, map_sub, hneg, hs z, h2σ]
      ring
    · rw [show Equiv.swap ((z, true) : ι × Bool) (z, false) (z, true) = (z, false) by
        simp [Equiv.swap_apply_left], quadRoot_true, quadRoot_false,
        map_div₀, map_add, hneg, hs z, h2σ]
      ring
  · have hne1 : ((z, b) : ι × Bool) ≠ (z₀, true) := fun h => hz (congrArg Prod.fst h)
    have hne2 : ((z, b) : ι × Bool) ≠ (z₀, false) := fun h => hz (congrArg Prod.fst h)
    rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    rcases b with _ | _
    · rw [quadRoot_false, map_div₀, map_sub, hfix z hz, hs z, h2σ]
    · rw [quadRoot_true, map_div₀, map_add, hfix z hz, hs z, h2σ]

end GaloisForLFunctions.HTGeometry
