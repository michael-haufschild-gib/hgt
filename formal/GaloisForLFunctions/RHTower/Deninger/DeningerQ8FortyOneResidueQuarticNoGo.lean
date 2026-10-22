import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFiveTateEpsilon

/-!
# The forty-one-adic direct tame-transport boundary

An order-four character of `(ZMod 41)ˣ` has value `1` at `-1`.  Consequently
its pullback along every map `C₄ → (ZMod 41)ˣ` has exponent at most two.  Thus
ordinary tame-ratio pullback cannot recover a literal order-four SST source at
`41`; a dual/Kummer pairing is mathematically necessary.

The positive survivor is exact: every order-four residue character has
same-additive Gauss product `41`, exact conductor `41`, and Tate phase-pair
product `+1`.
-/

namespace RHTower

noncomputable section

local instance q8FortyOneResidueFactPrimeFortyOne : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- Every quartic residue character modulo `41` is even.  The explicit fourth
root `3⁴ = -1` makes this independent of a chosen cyclic generator. -/
theorem zmodFortyOne_orderFourMulChar_neg_one_eq_one
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4) :
    χ (-1) = 1 := by
  have hχ4 : χ ^ 4 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  let u3 : (ZMod 41)ˣ := Units.mk0 3 (by
    intro h
    change ((3 : ℤ) : ZMod 41) = ((0 : ℤ) : ZMod 41) at h
    rw [ZMod.intCast_eq_intCast_iff'] at h
    norm_num at h)
  have heval := congrArg (fun ψ : MulChar (ZMod 41) ℂ => ψ u3) hχ4
  have hevalUnit : χ (u3 : ZMod 41) ^ 4 = 1 := by
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using heval
  have hu3 : (u3 : ZMod 41) = 3 := rfl
  have heval' : χ (3 : ZMod 41) ^ 4 = 1 := by
    rw [← hu3]
    exact hevalUnit
  have hthree : (3 : ZMod 41) ^ 4 = -1 := by
    calc
      (3 : ZMod 41) ^ 4 = 81 := by ring
      _ = -1 := by
        change ((81 : ℤ) : ZMod 41) = ((-1 : ℤ) : ZMod 41)
        rw [ZMod.intCast_eq_intCast_iff']
        norm_num
  calc
    χ (-1) = χ ((3 : ZMod 41) ^ 4) := congrArg χ hthree.symm
    _ = χ (3 : ZMod 41) ^ 4 := map_pow χ 3 4
    _ = 1 := heval'

/-- A quartic residue character is at most quadratic on every fourth root of
unity in `F₄₁`. -/
theorem zmodFortyOne_orderFourMulChar_on_fourthRoot_sq_eq_one
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4)
    (u : (ZMod 41)ˣ) (hu : u ^ 4 = 1) :
    χ (u : ZMod 41) ^ 2 = 1 := by
  have huval : (u : ZMod 41) ^ 4 = 1 := congrArg Units.val hu
  have hfactor :
      ((u : ZMod 41) ^ 2 - 1) * ((u : ZMod 41) ^ 2 + 1) = 0 := by
    calc
      ((u : ZMod 41) ^ 2 - 1) * ((u : ZMod 41) ^ 2 + 1) =
          (u : ZMod 41) ^ 4 - 1 := by ring
      _ = 0 := by rw [huval]; ring
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hu2 : (u : ZMod 41) ^ 2 = 1 := sub_eq_zero.mp hplus
    rw [← map_pow, hu2]
    exact map_one χ
  · have hu2 : (u : ZMod 41) ^ 2 = -1 :=
      eq_neg_of_add_eq_zero_left hminus
    rw [← map_pow, hu2, zmodFortyOne_orderFourMulChar_neg_one_eq_one χ hχ]

/-- Exact direct-transport boundary: every pullback of a quartic residue
character along a `C₄` carrier squares to the trivial character. -/
theorem zmodFortyOne_orderFourMulChar_pullback_c4_sq_eq_one
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4)
    (e : Multiplicative (ZMod 4) →* (ZMod 41)ˣ) :
    (χ.toUnitHom.comp e) ^ 2 = 1 := by
  apply MonoidHom.ext
  intro x
  have hx4 : x ^ 4 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hcard : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      calc
        Nat.card (Multiplicative (ZMod 4)) = Nat.card (ZMod 4) :=
          Nat.card_congr (Equiv.refl _)
        _ = 4 := Nat.card_zmod 4
    simpa only [hcard] using (orderOf_dvd_natCard x)
  have hex4 : e x ^ 4 = 1 := by
    rw [← map_pow, hx4, map_one]
  apply Units.ext
  simpa [MonoidHom.comp_apply, MonoidHom.one_apply, MonoidHom.mul_apply] using
    zmodFortyOne_orderFourMulChar_on_fourthRoot_sq_eq_one χ hχ (e x) hex4

/-- No direct tame-ratio pullback from a quartic `F₄₁×` character can retain
an order-four source orientation. -/
theorem zmodFortyOne_orderFourMulChar_pullback_c4_orderOf_ne_four
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4)
    (e : Multiplicative (ZMod 4) →* (ZMod 41)ˣ) :
    orderOf (χ.toUnitHom.comp e) ≠ 4 := by
  intro horder
  have hdvd : orderOf (χ.toUnitHom.comp e) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one
      (zmodFortyOne_orderFourMulChar_pullback_c4_sq_eq_one χ hχ e)
  rw [horder] at hdvd
  norm_num at hdvd

/-- The positive Gaussian survivor: every quartic residue character modulo
`41` has same-additive Gauss product `41`. -/
theorem zmodFortyOne_quarticSameAdditiveGaussProduct_eq_fortyOne
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = 41 := by
  have hne : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hχ
    norm_num at hχ
  have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (χ := χ) (ψ := ZMod.stdAddChar) hne (ZMod.isPrimitive_stdAddChar 41)
  rw [hχ] at h
  norm_num [zmodFortyOne_orderFourMulChar_neg_one_eq_one χ hχ] at h ⊢
  have hfour : χ ^ 4 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  have hthree : χ ^ 3 = χ⁻¹ := by
    calc
      χ ^ 3 = χ ^ 3 * 1 := (mul_one _).symm
      _ = χ ^ 3 * (χ * χ⁻¹) := by simp
      _ = χ ^ 4 * χ⁻¹ := by rw [← mul_assoc, ← pow_succ]
      _ = χ⁻¹ := by rw [hfour, one_mul]
  simpa [hthree] using h

/-- An order-four residue character at the prime modulus `41` has exact
conductor `41`. -/
theorem zmodFortyOne_orderFourMulChar_isPrimitive
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4) :
    DirichletCharacter.IsPrimitive (χ : DirichletCharacter ℂ 41) := by
  have hne : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hχ
    norm_num at hχ
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor
      (χ : DirichletCharacter ℂ 41) ∣ 41 :=
    DirichletCharacter.conductor_dvd_level (χ : DirichletCharacter ℂ 41)
  rcases (Nat.dvd_prime (by norm_num)).mp hdiv with h | h
  · exact (hne ((DirichletCharacter.eq_one_iff_conductor_eq_one
      (χ := (χ : DirichletCharacter ℂ 41))).mpr h)).elim
  · exact h

/-- Quartic residue character packaged at its exact field-one Tate
conductor. -/
noncomputable def zmodFortyOneQuarticTateCharacter
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4) :
    GaloisForLFunctions.RHTower.FieldOnePadicPrimitiveAngularCharacter 41 1 :=
  ⟨χ, by simpa using zmodFortyOne_orderFourMulChar_isPrimitive χ hχ⟩

/-- Exact analytic survivor: the two quartic residue Tate orientations at
`41` have phase-pair product `+1`. -/
theorem fieldOnePadicFortyOneQuarticTatePhasePair_eq_one
    (χ : MulChar (ZMod 41) ℂ) (hχ : orderOf χ = 4) :
    GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
        (zmodFortyOneQuarticTateCharacter χ hχ) 1 *
      GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
        (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
          (zmodFortyOneQuarticTateCharacter χ hχ)) 1 = 1 := by
  rw [GaloisForLFunctions.RHTower.fieldOnePadicPrimeRamifiedTatePhase_mul_inverse_eq_gaussianPhase]
  change (41 : ℂ)⁻¹ *
    (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) = 1
  rw [zmodFortyOne_quarticSameAdditiveGaussProduct_eq_fortyOne χ hχ]
  norm_num

end
end RHTower
