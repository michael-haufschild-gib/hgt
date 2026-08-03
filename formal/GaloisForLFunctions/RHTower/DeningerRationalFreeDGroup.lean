import GaloisForLFunctions.RHTower.DeningerRationalPower

/-!
# The rationalization of the integers is the rationals

`Multiplicative ℚ` is the free group with unique roots on one generator: a homomorphism out of it is
determined by the image `h` of the generator, and conversely every `h` in a group with unique roots
determines one, by the rational power operation.  Since the rationalization has the same universal
property, `Bau(ℤ) ≅ ℚ`.

* `deningerRatPow_unique` : the universal property of `Multiplicative ℚ`.
* `deningerBauIntEquivRat` : `Bau(Multiplicative ℤ) ≅ Multiplicative ℚ`.
-/

namespace RHTower

section RationalFreeDGroup

variable {H : Type*} [Group H] (hH : DeningerUniquelyDivisible H) (h : H)

@[simp]
theorem deningerRoot_zero : deningerRoot hH 0 h = h :=
  (deningerRoot_unique hH 0 (pow_one h)).symm

@[simp]
theorem deningerRatPow_ofAdd_one :
    deningerRatPow hH h (Multiplicative.ofAdd (1 : ℚ)) = h := by
  show deningerRoot hH ((1 : ℚ).den - 1) h ^ (1 : ℚ).num = h
  norm_num

/-- **The universal property of `Multiplicative ℚ`**: a homomorphism out of it into a group with
unique roots is determined by the image of the generator. -/
theorem deningerRatPow_unique (F : Multiplicative ℚ →* H)
    (hF : F (Multiplicative.ofAdd (1 : ℚ)) = h) : F = deningerRatPow hH h := by
  refine MonoidHom.ext fun q => ?_
  set r : ℚ := Multiplicative.toAdd q with hr
  have hden : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero.2 r.den_nz
  have hpow : F (Multiplicative.ofAdd ((r.den : ℚ)⁻¹)) ^ r.den = h := by
    rw [← map_pow, ← hF]
    congr 1
    refine congrArg Multiplicative.ofAdd ?_
    show (r.den : ℕ) • ((r.den : ℚ))⁻¹ = (1 : ℚ)
    rw [nsmul_eq_mul]
    field_simp
  have hroot : F (Multiplicative.ofAdd ((r.den : ℚ)⁻¹)) = deningerRoot hH (r.den - 1) h := by
    refine deningerRoot_unique hH (r.den - 1) ?_
    have hd : r.den - 1 + 1 = r.den := by
      have := r.pos
      omega
    rw [hd]
    exact hpow
  have hq : q = (Multiplicative.ofAdd ((r.den : ℚ))⁻¹) ^ r.num := by
    refine (Multiplicative.toAdd).injective ?_
    have hnum : (r.num : ℚ) * ((r.den : ℚ))⁻¹ = r := by
      rw [← div_eq_mul_inv]
      exact Rat.num_div_den r
    show r = r.num • ((r.den : ℚ))⁻¹
    rw [zsmul_eq_mul, hnum]
  calc F q = F ((Multiplicative.ofAdd ((r.den : ℚ))⁻¹) ^ r.num) := by rw [← hq]
    _ = (F (Multiplicative.ofAdd ((r.den : ℚ))⁻¹)) ^ r.num := map_zpow _ _ _
    _ = deningerRoot hH (r.den - 1) h ^ r.num := by rw [hroot]
    _ = deningerRatPow hH h q := rfl

end RationalFreeDGroup

section BauInt

/-- The inclusion of the integers into the rationals, multiplicatively. -/
noncomputable def deningerIntToRat : Multiplicative ℤ →* Multiplicative ℚ :=
  AddMonoidHom.toMultiplicative (Int.castAddHom ℚ)

/-- **`Bau(ℤ) ≅ ℚ`.** -/
noncomputable def deningerBauIntEquivRat :
    DeningerBau (Multiplicative ℤ) ≃* Multiplicative ℚ where
  toFun := deningerBauLift (deningerMultiplicative_uniquelyDivisible (A := ℚ)) deningerIntToRat
  invFun := deningerRatPow DeningerBau.uniquelyDivisible
    (DeningerBau.of (Multiplicative.ofAdd (1 : ℤ)))
  left_inv := by
    have hcomp : (deningerRatPow DeningerBau.uniquelyDivisible
          (DeningerBau.of (Multiplicative.ofAdd (1 : ℤ)))).comp
        (deningerBauLift (deningerMultiplicative_uniquelyDivisible (A := ℚ)) deningerIntToRat) =
        MonoidHom.id (DeningerBau (Multiplicative ℤ)) := by
      refine (deningerBauLift_unique DeningerBau.uniquelyDivisible
        (DeningerBau.of : Multiplicative ℤ →* DeningerBau (Multiplicative ℤ)) _ ?_).trans
        (deningerBauLift_unique DeningerBau.uniquelyDivisible
          (DeningerBau.of : Multiplicative ℤ →* DeningerBau (Multiplicative ℤ))
          (MonoidHom.id _) (fun _ => rfl)).symm
      intro a
      show deningerRatPow DeningerBau.uniquelyDivisible _
        (deningerIntToRat a) = DeningerBau.of a
      show deningerRoot DeningerBau.uniquelyDivisible
          (((Multiplicative.toAdd a : ℤ) : ℚ).den - 1)
          (DeningerBau.of (Multiplicative.ofAdd (1 : ℤ))) ^
        (((Multiplicative.toAdd a : ℤ) : ℚ)).num = DeningerBau.of a
      rw [Rat.den_intCast, Rat.num_intCast]
      show deningerRoot DeningerBau.uniquelyDivisible 0
          (DeningerBau.of (Multiplicative.ofAdd (1 : ℤ))) ^ (Multiplicative.toAdd a) = _
      rw [deningerRoot_zero, ← map_zpow]
      refine congrArg DeningerBau.of ?_
      refine Multiplicative.toAdd.injective ?_
      show Multiplicative.toAdd a • (1 : ℤ) = Multiplicative.toAdd a
      rw [smul_eq_mul, mul_one]
    exact fun x => DFunLike.congr_fun hcomp x
  right_inv := by
    have hcomp : (deningerBauLift (deningerMultiplicative_uniquelyDivisible (A := ℚ))
          deningerIntToRat).comp
        (deningerRatPow DeningerBau.uniquelyDivisible
          (DeningerBau.of (Multiplicative.ofAdd (1 : ℤ)))) =
        MonoidHom.id (Multiplicative ℚ) := by
      refine (deningerRatPow_unique (deningerMultiplicative_uniquelyDivisible (A := ℚ))
        (Multiplicative.ofAdd (1 : ℚ)) _ ?_).trans
        (deningerRatPow_unique (deningerMultiplicative_uniquelyDivisible (A := ℚ))
          (Multiplicative.ofAdd (1 : ℚ)) (MonoidHom.id _) rfl).symm
      show deningerBauLift _ deningerIntToRat
        (deningerRatPow DeningerBau.uniquelyDivisible _ (Multiplicative.ofAdd (1 : ℚ))) = _
      rw [deningerRatPow_ofAdd_one, deningerBauLift_of]
      rfl
    exact fun x => DFunLike.congr_fun hcomp x
  map_mul' := map_mul _

end BauInt

end RHTower
