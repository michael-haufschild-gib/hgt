import GaloisForLFunctions.HTGeometry.MahlerPerfectDerivation

/-!
# The commuting derivation of the Mahler model

The Euler derivation of the `w`-grading does not commute with the Mahler substitution: it obeys
`δσ = p·σδ`.  Multiplying it by the inverse of the twisting coordinate — which the substitution
scales by exactly `p` — produces a derivation that commutes with the substitution on the nose.
That is the derivation for which the automorphism-family criterion applies verbatim, and it
differs from the Euler derivation by a unit of the base field.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The inverse of the twisting coordinate. -/
def mahlerCoordInv (k : Type*) [Field k] : MahlerAmbient k := HahnSeries.single (-1) 1

theorem mahlerCoord_mul_coordInv : mahlerCoord k * mahlerCoordInv k = 1 := by
  rw [mahlerCoord, mahlerCoordInv, HahnSeries.single_mul_single]
  norm_num

theorem mahlerCoordInv_ne_zero : (mahlerCoordInv k) ≠ 0 := by
  intro h
  have := congrArg (fun x : MahlerAmbient k => x.coeff (-1)) h
  rw [mahlerCoordInv, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem C_C_natCast_mul_inv [CharZero k] {p : ℕ} (hp : 1 < p) :
    (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
      * HahnSeries.C (HahnSeries.C ((p : k))) = 1 := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  rw [← map_mul, ← map_mul, inv_mul_cancel₀ hpk, map_one, map_one]

/-- **The substitution scales the inverse twisting coordinate by `p`.** -/
theorem mahlerDilation_mahlerCoordInv [CharZero k] (p : ℕ) (hp : 1 < p) :
    mahlerDilation p hp (mahlerCoordInv k)
      = HahnSeries.C (HahnSeries.C ((p : k))) * mahlerCoordInv k := by
  have h1 : mahlerDilation p hp (mahlerCoord k) * mahlerDilation p hp (mahlerCoordInv k) = 1 := by
    rw [← map_mul, mahlerCoord_mul_coordInv, map_one]
  rw [mahlerDilation_mahlerCoord] at h1
  have h2 : ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) * mahlerCoord k)
      * (HahnSeries.C (HahnSeries.C ((p : k))) * mahlerCoordInv k) = 1 := by
    calc ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) * mahlerCoord k)
        * (HahnSeries.C (HahnSeries.C ((p : k))) * mahlerCoordInv k)
        = ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
            * HahnSeries.C (HahnSeries.C ((p : k))))
          * (mahlerCoord k * mahlerCoordInv k) := by ring
      _ = 1 := by rw [C_C_natCast_mul_inv hp, mahlerCoord_mul_coordInv, one_mul]
  have hne : ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) * mahlerCoord k) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact zero_ne_one h2
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- The commuting derivation: the Euler derivation divided by the twisting coordinate. -/
def mahlerCommDeriv [CharZero k] : MahlerAmbient k →+ MahlerAmbient k where
  toFun f := mahlerCoordInv k * mahlerAmbientDeriv f
  map_zero' := by rw [map_zero, mul_zero]
  map_add' x y := by rw [map_add, mul_add]

@[simp]
theorem mahlerCommDeriv_apply [CharZero k] (f : MahlerAmbient k) :
    mahlerCommDeriv f = mahlerCoordInv k * mahlerAmbientDeriv f := rfl

theorem mahlerCommDeriv_leibniz [CharZero k] (x y : MahlerAmbient k) :
    mahlerCommDeriv (x * y) = mahlerCommDeriv x * y + x * mahlerCommDeriv y := by
  rw [mahlerCommDeriv_apply, mahlerAmbientDeriv_leibniz, mahlerCommDeriv_apply,
    mahlerCommDeriv_apply, mul_add]
  ring

/-- The differential structure of the Mahler ambient for the commuting derivation. -/
@[reducible] def mahlerCommDifferential [CharZero k] : Differential (MahlerAmbient k) := by
  letI : Algebra ℤ (MahlerAmbient k) := Ring.toIntAlgebra _
  exact ⟨Derivation.mk' (mahlerCommDeriv (k := k)).toIntLinearMap (by
    intro x y
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul, mahlerCommDeriv_leibniz]
    ring)⟩

theorem mahlerCommDifferential_deriv [CharZero k] (f : MahlerAmbient k) :
    (mahlerCommDifferential (k := k)).deriv f = mahlerCommDeriv f := rfl

/-- **The substitution and the commuting derivation commute exactly.** -/
theorem mahlerDilation_mahlerCommDeriv [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) :
    mahlerDilation p hp (mahlerCommDeriv f) = mahlerCommDeriv (mahlerDilation p hp f) := by
  have hderiv : mahlerDilation p hp (mahlerAmbientDeriv f)
      = HahnSeries.C (HahnSeries.C (((p : k))⁻¹))
        * mahlerAmbientDeriv (mahlerDilation p hp f) := by
    have h := mahlerDilation_deriv_iterate p hp 1 f
    simpa using h
  rw [mahlerCommDeriv_apply, map_mul, mahlerDilation_mahlerCoordInv, hderiv,
    mahlerCommDeriv_apply]
  calc (HahnSeries.C (HahnSeries.C ((p : k))) : MahlerAmbient k) * mahlerCoordInv k
        * (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) * mahlerAmbientDeriv (mahlerDilation p hp f))
      = ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
          * HahnSeries.C (HahnSeries.C ((p : k))))
        * (mahlerCoordInv k * mahlerAmbientDeriv (mahlerDilation p hp f)) := by ring
    _ = mahlerCoordInv k * mahlerAmbientDeriv (mahlerDilation p hp f) := by
        rw [C_C_natCast_mul_inv hp, one_mul]

end

end GaloisForLFunctions.HTGeometry
