import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingUp

/-! Height one is preserved by contraction in the integral normalization
of a normal chart. -/

namespace GlobalTheory.PD

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra.HasGoingDown A B]

/-- A prime divisor of an integral extension with going down contracts
to a prime divisor. -/
theorem height_comap_eq_one_of_integral (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1) :
    (Q.comap (algebraMap A B)).height = 1 := by
  let p := Q.comap (algebraMap A B)
  letI : p.IsPrime := Ideal.comap_isPrime _ Q
  letI : Q.LiesOver p := ⟨rfl⟩
  have hp : p ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A (Q.ne_bot_of_height_eq_one hQ)
  have hle : p.height ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q]
    exact le_self_add
  exact le_antisymm (hQ ▸ hle)
    (Order.one_le_iff_ne_zero.mpr ((Ideal.height_eq_zero_iff_eq_bot).not.mpr hp))

end GlobalTheory.PD
