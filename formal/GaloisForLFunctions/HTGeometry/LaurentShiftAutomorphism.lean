import Mathlib

/-!
# The translation automorphism of the formal Laurent field at infinity

In the coordinate `X = s⁻¹` the translation `s ↦ s + h` is the substitution `X ↦ X/(1 + hX)`.
It is an automorphism of `ℂ⟦X⟧` with inverse the substitution attached to `-h`, hence extends to
the Laurent field `ℂ((X)) = ℂ((s⁻¹))`, where it sends the coordinate `s = X⁻¹` to `s + h`.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The power series `X / (1 + h X)`: the coordinate `X = s⁻¹` seen after the translation
`s ↦ s + h`. -/
def laurentShiftSubst (h : ℂ) : PowerSeries ℂ :=
  PowerSeries.X * (1 + PowerSeries.C h * PowerSeries.X)⁻¹

theorem constantCoeff_one_add (h : ℂ) :
    PowerSeries.constantCoeff (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) = 1 := by
  simp

theorem laurentShiftSubst_mul (h : ℂ) :
    laurentShiftSubst h * (1 + PowerSeries.C h * PowerSeries.X) = PowerSeries.X := by
  have hne : PowerSeries.constantCoeff (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    rw [constantCoeff_one_add]
    exact one_ne_zero
  rw [laurentShiftSubst, mul_assoc, mul_comm ((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹),
    PowerSeries.mul_inv_cancel _ hne, mul_one]

theorem constantCoeff_shiftSubst (h : ℂ) :
    PowerSeries.constantCoeff (laurentShiftSubst h) = 0 := by
  rw [laurentShiftSubst, map_mul, PowerSeries.constantCoeff_X, zero_mul]

theorem hasSubst_shiftSubst (h : ℂ) : PowerSeries.HasSubst (laurentShiftSubst h) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_shiftSubst h)

/-- The translation substitution as an algebra homomorphism of power series. -/
def shiftPS (h : ℂ) : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  PowerSeries.substAlgHom (hasSubst_shiftSubst h)

theorem shiftPS_apply (h : ℂ) (F : PowerSeries ℂ) :
    shiftPS h F = PowerSeries.subst (laurentShiftSubst h) F := by
  rw [shiftPS, PowerSeries.coe_substAlgHom]

theorem shiftPS_X (h : ℂ) : shiftPS h PowerSeries.X = laurentShiftSubst h := by
  rw [shiftPS_apply]
  exact PowerSeries.subst_X (hasSubst_shiftSubst h)

theorem shiftPS_C (h : ℂ) (c : ℂ) : shiftPS h (PowerSeries.C c) = PowerSeries.C c := by
  rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes]

theorem powerSeries_inv_eq_of_mul_eq_one {u v : PowerSeries ℂ}
    (hu : PowerSeries.constantCoeff u ≠ 0) (huv : u * v = 1) : v = u⁻¹ := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact hu rfl
  refine mul_left_cancel₀ hu0 ?_
  rw [huv, PowerSeries.mul_inv_cancel u hu]

theorem laurentShiftSubst_mul_neg (h : ℂ) :
    laurentShiftSubst (-h) * (1 - PowerSeries.C h * PowerSeries.X) = PowerSeries.X := by
  have := laurentShiftSubst_mul (-h)
  rw [map_neg, neg_mul, ← sub_eq_add_neg] at this
  exact this

theorem one_add_C_mul_shiftSubst_neg (h : ℂ) :
    (1 + PowerSeries.C h * laurentShiftSubst (-h)) * (1 - PowerSeries.C h * PowerSeries.X) = 1 := by
  have hb := laurentShiftSubst_mul_neg h
  calc (1 + PowerSeries.C h * laurentShiftSubst (-h)) * (1 - PowerSeries.C h * PowerSeries.X)
      = (1 - PowerSeries.C h * PowerSeries.X)
        + PowerSeries.C h * (laurentShiftSubst (-h) * (1 - PowerSeries.C h * PowerSeries.X)) := by ring
    _ = 1 := by rw [hb]; ring

theorem map_inv_of_constantCoeff_ne_zero (φ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ)
    {u : PowerSeries ℂ} (hu : PowerSeries.constantCoeff u ≠ 0)
    (hφu : PowerSeries.constantCoeff (φ u) ≠ 0) : φ u⁻¹ = (φ u)⁻¹ := by
  refine powerSeries_inv_eq_of_mul_eq_one hφu ?_
  rw [← map_mul, PowerSeries.mul_inv_cancel u hu, map_one]

/-- **The translation substitutions compose to the identity.** -/
theorem shiftPS_shiftSubst (h : ℂ) : shiftPS (-h) (laurentShiftSubst h) = PowerSeries.X := by
  have hunit : PowerSeries.constantCoeff
      (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    rw [constantCoeff_one_add]
    exact one_ne_zero
  have himg : shiftPS (-h) (1 + PowerSeries.C h * PowerSeries.X)
      = 1 + PowerSeries.C h * laurentShiftSubst (-h) := by
    rw [map_add, map_one, map_mul, shiftPS_C, shiftPS_X]
  have hcc : PowerSeries.constantCoeff (shiftPS (-h) (1 + PowerSeries.C h * PowerSeries.X)) ≠ 0 := by
    rw [himg, map_add, map_one, map_mul, constantCoeff_shiftSubst, mul_zero, add_zero]
    exact one_ne_zero
  rw [laurentShiftSubst, map_mul, shiftPS_X,
    map_inv_of_constantCoeff_ne_zero (shiftPS (-h)) hunit hcc, himg]
  have hinv : (1 + PowerSeries.C h * laurentShiftSubst (-h))⁻¹
      = 1 - PowerSeries.C h * PowerSeries.X := by
    have h1 := one_add_C_mul_shiftSubst_neg h
    have hcc2 : PowerSeries.constantCoeff
        (1 + PowerSeries.C h * laurentShiftSubst (-h) : PowerSeries ℂ) ≠ 0 := by
      rw [map_add, map_one, map_mul, constantCoeff_shiftSubst, mul_zero, add_zero]
      exact one_ne_zero
    exact (powerSeries_inv_eq_of_mul_eq_one hcc2 h1).symm
  rw [hinv]
  exact laurentShiftSubst_mul_neg h

theorem shiftPS_comp (h : ℂ) (F : PowerSeries ℂ) : shiftPS (-h) (shiftPS h F) = F := by
  rw [shiftPS_apply, shiftPS_apply,
    PowerSeries.subst_comp_subst_apply (hasSubst_shiftSubst h) (hasSubst_shiftSubst (-h)),
    ← shiftPS_apply, shiftPS_shiftSubst]
  exact PowerSeries.X_subst F

/-- **The translation is an automorphism of the power series ring.** -/
def shiftPSEquiv (h : ℂ) : PowerSeries ℂ ≃+* PowerSeries ℂ where
  toFun := shiftPS h
  invFun := shiftPS (-h)
  left_inv := fun F => shiftPS_comp h F
  right_inv := fun F => by
    have := shiftPS_comp (-h) F
    rwa [neg_neg] at this
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] theorem shiftPSEquiv_apply (h : ℂ) (F : PowerSeries ℂ) :
    shiftPSEquiv h F = shiftPS h F := rfl

private theorem map_nonZeroDivisors_of_ringEquiv {R : Type*} [CommRing R] [IsDomain R] (e : R ≃+* R) :
    Submonoid.map e.toMonoidHom (nonZeroDivisors R) = nonZeroDivisors R := by
  ext x
  simp only [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using fun hc => hy (e.injective (by simpa using hc))
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    simp only [ne_eq]
    intro hc
    exact hx (by rw [← e.apply_symm_apply x, hc, map_zero])

/-- **The translation automorphism of the formal Laurent field at infinity.** -/
def shiftLaurent (h : ℂ) : LaurentSeries ℂ ≃+* LaurentSeries ℂ :=
  IsLocalization.ringEquivOfRingEquiv (M := nonZeroDivisors (PowerSeries ℂ))
    (LaurentSeries ℂ) (LaurentSeries ℂ) (shiftPSEquiv h)
    (map_nonZeroDivisors_of_ringEquiv (shiftPSEquiv h))

theorem shiftLaurent_algebraMap (h : ℂ) (F : PowerSeries ℂ) :
    shiftLaurent h (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) F)
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (shiftPS h F) := by
  rw [shiftLaurent, IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

/-- The coordinate `X` inside the Laurent field. -/
def laurentX : LaurentSeries ℂ := algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) PowerSeries.X

/-- A complex constant inside the Laurent field. -/
def laurentC (c : ℂ) : LaurentSeries ℂ :=
  algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (PowerSeries.C c)

theorem algebraMap_powerSeries_injective :
    Function.Injective (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)) :=
  IsFractionRing.injective _ _

theorem algebraMap_powerSeries_ne_zero {F : PowerSeries ℂ} (hF : F ≠ 0) :
    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) F ≠ 0 := by
  intro hc
  exact hF (algebraMap_powerSeries_injective (by rw [hc, map_zero]))

theorem laurentX_ne_zero : laurentX ≠ 0 :=
  algebraMap_powerSeries_ne_zero PowerSeries.X_ne_zero

/-- The coordinate `s = X⁻¹` of the Laurent field at infinity. -/
def coordS : LaurentSeries ℂ := laurentX⁻¹

theorem coordS_mul_laurentX : coordS * laurentX = 1 := by
  rw [coordS, inv_mul_cancel₀ laurentX_ne_zero]

theorem algebraMap_powerSeries_inv (u : PowerSeries ℂ)
    (hu : PowerSeries.constantCoeff u ≠ 0) :
    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) u⁻¹
      = (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) u)⁻¹ := by
  have hmul : algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) u *
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) u⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel u hu, map_one]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm]
  exact hmul

/-- **The translation acts on the coordinate by `s ↦ s + h`.** -/
theorem shiftLaurent_coordS (h : ℂ) :
    shiftLaurent h coordS = coordS + laurentC h := by
  have hunit : PowerSeries.constantCoeff
      (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    rw [constantCoeff_one_add]; exact one_ne_zero
  have hshift : shiftLaurent h laurentX
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (laurentShiftSubst h) := by
    rw [laurentX, shiftLaurent_algebraMap, shiftPS_X]
  have hs : algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (laurentShiftSubst h)
      = laurentX * (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
        (1 + PowerSeries.C h * PowerSeries.X))⁻¹ := by
    rw [laurentShiftSubst, map_mul, algebraMap_powerSeries_inv _ hunit, laurentX]
  rw [coordS, map_inv₀, hshift, hs, mul_inv, inv_inv, map_add, map_one, map_mul,
    ← laurentC, ← laurentX, ← coordS]
  have hcs := coordS_mul_laurentX
  calc coordS * (1 + laurentC h * laurentX)
      = coordS + laurentC h * (coordS * laurentX) := by ring
    _ = coordS + laurentC h := by rw [hcs, mul_one]

/-! ### The chain-rule identity of the translation substitution -/

/-- **The substitution `X ↦ X/(1+hX)` satisfies `X² a′ = a²`**, the identity that makes the
translation commute with the derivation `d/ds = -X² d/dX`. -/
theorem sq_mul_derivative_shiftSubst (h : ℂ) :
    PowerSeries.X ^ (2 : ℕ) * (d⁄dX ℂ) (laurentShiftSubst h) = (laurentShiftSubst h) ^ (2 : ℕ) := by
  set a : PowerSeries ℂ := laurentShiftSubst h with ha
  set u : PowerSeries ℂ := 1 + PowerSeries.C h * PowerSeries.X with hu
  have hau : a * u = PowerSeries.X := laurentShiftSubst_mul h
  have hdu : (d⁄dX ℂ) u = PowerSeries.C h := by
    rw [hu, map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz]
    simp
  have hd : (d⁄dX ℂ) a * u + a * PowerSeries.C h = 1 := by
    have := congrArg (d⁄dX ℂ) hau
    rw [Derivation.leibniz, PowerSeries.derivative_X, hdu] at this
    have h2 : a * PowerSeries.C h + u * (d⁄dX ℂ) a = 1 := by
      simpa [smul_eq_mul, mul_comm] using this
    linear_combination h2
  have hstep : (d⁄dX ℂ) a * u ^ (2 : ℕ) = 1 := by
    have hexp : (d⁄dX ℂ) a * u ^ (2 : ℕ) = ((d⁄dX ℂ) a * u + a * PowerSeries.C h) * u
        - PowerSeries.C h * (a * u) := by ring
    rw [hexp, hd, hau, one_mul, hu]
    ring
  have hkey : PowerSeries.X ^ (2 : ℕ) * (d⁄dX ℂ) a * u ^ (2 : ℕ) = a ^ (2 : ℕ) * u ^ (2 : ℕ) := by
    calc PowerSeries.X ^ (2 : ℕ) * (d⁄dX ℂ) a * u ^ (2 : ℕ)
        = PowerSeries.X ^ (2 : ℕ) * ((d⁄dX ℂ) a * u ^ (2 : ℕ)) := by ring
      _ = PowerSeries.X ^ (2 : ℕ) := by rw [hstep, mul_one]
      _ = (a * u) ^ (2 : ℕ) := by rw [hau]
      _ = a ^ (2 : ℕ) * u ^ (2 : ℕ) := by ring
  have hune : u ^ (2 : ℕ) ≠ 0 := by
    intro hc
    have hcc := congrArg (PowerSeries.constantCoeff) hc
    rw [map_pow, hu, constantCoeff_one_add] at hcc
    simp at hcc
  exact mul_right_cancel₀ hune hkey

/-! ### The derivation `d/ds` and its commutation with the translation -/

/-- The derivation `d/ds = -X² d/dX` on power series in `X = s⁻¹`. -/
def coordDerivPS (F : PowerSeries ℂ) : PowerSeries ℂ := -(PowerSeries.X ^ (2 : ℕ)) * (d⁄dX ℂ) F

/-- **The translation commutes with `d/ds` on power series.** -/
theorem shiftPS_coordDerivPS (h : ℂ) (F : PowerSeries ℂ) :
    shiftPS h (coordDerivPS F) = coordDerivPS (shiftPS h F) := by
  have hchain := PowerSeries.derivative_subst (A := ℂ) (f := F) (hasSubst_shiftSubst h)
  have hkey := sq_mul_derivative_shiftSubst h
  rw [coordDerivPS, coordDerivPS, map_mul, map_neg, map_pow, shiftPS_X, shiftPS_apply,
    shiftPS_apply, hchain]
  calc -(laurentShiftSubst h) ^ (2 : ℕ) * PowerSeries.subst (laurentShiftSubst h) ((d⁄dX ℂ) F)
      = -(PowerSeries.X ^ (2 : ℕ) * (d⁄dX ℂ) (laurentShiftSubst h))
        * PowerSeries.subst (laurentShiftSubst h) ((d⁄dX ℂ) F) := by rw [hkey]
    _ = -PowerSeries.X ^ (2 : ℕ) *
        (PowerSeries.subst (laurentShiftSubst h) ((d⁄dX ℂ) F) * (d⁄dX ℂ) (laurentShiftSubst h)) := by ring

end

end GaloisForLFunctions.HTGeometry
