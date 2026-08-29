import GaloisForLFunctions.HTGeometry.MahlerPerfectEmbedding

/-!
# The Euler derivation of the perfect rational base

The Euler operator `w d/dw` of the Hahn field preserves every ramified level `k(w^(1/pⁿ))`,
because on that level it is `p^(-n)` times the Euler operator of the level coordinate.  Hence it
preserves the perfect base, which therefore is a differential field, and the ambient derivation of
the Mahler model restricts to it.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc Differential

noncomputable section

variable {k : Type*} [Field k]

theorem coeff_ramifiedLevelHom (p : ℕ) (hp : 0 < p) (n : ℕ) (r : RatFunc k) (γ : ℚ) :
    (ramifiedLevelHom p hp n r).coeff γ = (ratFuncToHahn r).coeff (((p : ℚ)) ^ n * γ) := by
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.ne'
  have h := HahnSeries.embDomain_coeff
    (f := (⟨⟨qShrinkHom p n, qShrinkHom_injective hp n⟩, qShrinkHom_le_iff hp n _ _⟩ : ℚ ↪o ℚ))
    (x := ratFuncToHahn r) (a := ((p : ℚ)) ^ n * γ)
  rw [show (⟨⟨qShrinkHom p n, qShrinkHom_injective hp n⟩, qShrinkHom_le_iff hp n _ _⟩ : ℚ ↪o ℚ)
      (((p : ℚ)) ^ n * γ) = γ from by
    show ((p : ℚ) ^ n)⁻¹ * (((p : ℚ)) ^ n * γ) = γ
    field_simp] at h
  exact h

theorem ratFuncToHahn_smul (c : k) (r : RatFunc k) :
    ratFuncToHahn (c • r) = (HahnSeries.C c : HahnSeries ℚ k) * ratFuncToHahn r := by
  rw [Algebra.smul_def, map_mul, ratFuncToHahn_const]

/-- **The Euler operator preserves each ramified level.** -/
theorem hahnQEuler_ramifiedLevelHom [CharZero k] (p : ℕ) (hp : 0 < p) (n : ℕ) (r : RatFunc k) :
    hahnQEuler (ramifiedLevelHom p hp n r)
      = ramifiedLevelHom p hp n ((((p : k)) ^ n)⁻¹ • ratFuncEulerOp r) := by
  have hpk : ((p : k)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  rw [coeff_hahnQEuler, coeff_ramifiedLevelHom p hp, coeff_ramifiedLevelHom p hp,
    ratFuncToHahn_smul, coeff_C_mul_hahn, ratFuncToHahn_eulerOp, coeff_hahnQEuler]
  rw [← mul_assoc]
  congr 1
  push_cast
  field_simp

theorem hahnQEuler_mem_perfectBase [CharZero k] (p : ℕ) (hp : 1 < p) {x : HahnSeries ℚ k}
    (hx : x ∈ perfectBase p hp) : hahnQEuler x ∈ perfectBase p hp := by
  obtain ⟨n, r, rfl⟩ := hx
  rw [hahnQEuler_ramifiedLevelHom p (by omega)]
  exact ⟨n, _, rfl⟩

/-- The Euler derivation restricted to the perfect base. -/
def perfectBaseDeriv [CharZero k] (p : ℕ) (hp : 1 < p) :
    perfectBase (k := k) p hp →+ perfectBase (k := k) p hp where
  toFun x := ⟨hahnQEuler (x : HahnSeries ℚ k), hahnQEuler_mem_perfectBase p hp x.2⟩
  map_zero' := Subtype.ext (by simpa using map_zero (hahnQEuler (k := k)))
  map_add' x y := Subtype.ext (by simpa using map_add (hahnQEuler (k := k)) _ _)

@[simp]
theorem perfectBaseDeriv_coe [CharZero k] (p : ℕ) (hp : 1 < p) (x : perfectBase (k := k) p hp) :
    ((perfectBaseDeriv p hp x : perfectBase (k := k) p hp) : HahnSeries ℚ k)
      = hahnQEuler (x : HahnSeries ℚ k) := rfl

theorem perfectBaseDeriv_leibniz [CharZero k] (p : ℕ) (hp : 1 < p)
    (x y : perfectBase (k := k) p hp) :
    perfectBaseDeriv p hp (x * y)
      = perfectBaseDeriv p hp x * y + x * perfectBaseDeriv p hp y := by
  refine Subtype.ext ?_
  show hahnQEuler ((x : HahnSeries ℚ k) * (y : HahnSeries ℚ k))
    = hahnQEuler (x : HahnSeries ℚ k) * (y : HahnSeries ℚ k)
      + (x : HahnSeries ℚ k) * hahnQEuler (y : HahnSeries ℚ k)
  exact hahnQEuler_leibniz _ _

/-- The differential structure of the perfect base. -/
@[reducible] def perfectDifferential [CharZero k] (p : ℕ) (hp : 1 < p) :
    Differential (perfectBase (k := k) p hp) := by
  letI : Algebra ℤ (perfectBase (k := k) p hp) := Ring.toIntAlgebra _
  exact ⟨Derivation.mk' (perfectBaseDeriv p hp).toIntLinearMap (by
    intro x y
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul, perfectBaseDeriv_leibniz]
    ring)⟩

theorem perfectDifferential_deriv [CharZero k] (p : ℕ) (hp : 1 < p)
    (x : perfectBase (k := k) p hp) :
    (perfectDifferential p hp).deriv x = perfectBaseDeriv p hp x := rfl

end

end GaloisForLFunctions.HTGeometry
