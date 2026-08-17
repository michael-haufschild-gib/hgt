import GaloisForLFunctions.HTGeometry.RationalPadicResidue

/-!
# The tame symbol on `K_2^M(ℚ)` at a prime, with residue field `ZMod p`

The `p`-adic valuation of a rational unit and the reduction of a `p`-unit assemble into a
`TameData ℚ (ZMod p)`: the four Steinberg clauses are elementary congruences once the residue is
computed from a presentation.

* a `p`-unit is exactly a rational of `p`-adic valuation zero;
* positive valuation means `p ∣ num` and `p ∤ den`, negative valuation the reverse;
* `1 - q = (den - num)/den`, so the residue of `1 - q` is `1 - res q` whenever `p ∤ den`.

With those, `1 - a` has residue `1` when `v(a) > 0`; `res a = 1` when `v(a) = 0` and `v(1-a) > 0`;
and `a (1-a)^{-1} = num/(den - num)` has residue `-1` when `v(a) < 0`, because `den ≡ 0`.

The resulting `tameHom` is the tame symbol at `p` on `K_2^M(ℚ)` with values in `(ZMod p)ˣ`.
-/

namespace GaloisForLFunctions.HTGeometry

section RationalTame

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Numerator and denominator against `p` -/

omit hp in
theorem padicValRat_eq_sub (q : ℚ) :
    padicValRat p q = (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) := rfl

theorem not_dvd_num_and_den (q : ℚ) : ¬ (p ∣ q.num.natAbs ∧ p ∣ q.den) := by
  rintro ⟨h1, h2⟩
  have hg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 h2
  rw [q.reduced] at hg
  exact Nat.Prime.one_lt hp.out |>.ne' (Nat.dvd_one.mp hg)

theorem num_zmod_eq_zero_iff (q : ℚ) : ((q.num : ZMod p) = 0) ↔ p ∣ q.num.natAbs := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd

theorem den_zmod_eq_zero_iff (q : ℚ) : ((q.den : ZMod p) = 0) ↔ p ∣ q.den :=
  natCast_zmod_eq_zero_iff

/-- **A rational is a `p`-unit exactly when its `p`-adic valuation vanishes.** -/
theorem padicValRat_eq_zero_iff {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q = 0 ↔ IsPadicUnit p q := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.2 hq
  have hnat : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hnum
  have hden : q.den ≠ 0 := q.den_nz
  rw [padicValRat_eq_sub, IsPadicUnit, Ne, Ne, num_zmod_eq_zero_iff, den_zmod_eq_zero_iff]
  constructor
  · intro h
    have hnd : ¬ p ∣ q.num.natAbs := by
      intro hdvd
      have hA : 1 ≤ padicValNat p q.num.natAbs := one_le_padicValNat_of_dvd hnat hdvd
      have hB : 1 ≤ padicValNat p q.den := by omega
      exact not_dvd_num_and_den q ⟨hdvd, by
        by_contra hcon
        rw [padicValNat.eq_zero_of_not_dvd hcon] at hB
        omega⟩
    have hA0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnd
    have hB0 : padicValNat p q.den = 0 := by omega
    refine ⟨hnd, ?_⟩
    intro hdvd
    have := one_le_padicValNat_of_dvd hden hdvd
    omega
  · rintro ⟨h1, h2⟩
    rw [padicValNat.eq_zero_of_not_dvd h1, padicValNat.eq_zero_of_not_dvd h2]
    simp

/-- Positive valuation: `p` meets the numerator and misses the denominator. -/
theorem props_of_padicValRat_pos {q : ℚ} (hq : q ≠ 0) (h : 0 < padicValRat p q) :
    ((q.num : ZMod p) = 0) ∧ ((q.den : ZMod p) ≠ 0) := by
  have hnat : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hq)
  have hden : q.den ≠ 0 := q.den_nz
  rw [padicValRat_eq_sub] at h
  have hnd : ¬ p ∣ q.den := by
    intro hdvd
    have hB : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd hden hdvd
    have hnum : ¬ p ∣ q.num.natAbs := fun hc => not_dvd_num_and_den q ⟨hc, hdvd⟩
    rw [padicValNat.eq_zero_of_not_dvd hnum] at h
    omega
  have hB0 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hnd
  rw [hB0] at h
  have hA : padicValNat p q.num.natAbs ≠ 0 := by omega
  refine ⟨?_, ?_⟩
  · rw [num_zmod_eq_zero_iff]
    by_contra hc
    exact hA (padicValNat.eq_zero_of_not_dvd hc)
  · rw [Ne, den_zmod_eq_zero_iff]
    exact hnd

/-- Negative valuation: `p` misses the numerator and meets the denominator. -/
theorem props_of_padicValRat_neg {q : ℚ} (hq : q ≠ 0) (h : padicValRat p q < 0) :
    ((q.num : ZMod p) ≠ 0) ∧ ((q.den : ZMod p) = 0) := by
  have hnat : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hq)
  have hden : q.den ≠ 0 := q.den_nz
  rw [padicValRat_eq_sub] at h
  have hnd : ¬ p ∣ q.num.natAbs := by
    intro hdvd
    have hA : 1 ≤ padicValNat p q.num.natAbs := one_le_padicValNat_of_dvd hnat hdvd
    have hden' : ¬ p ∣ q.den := fun hc => not_dvd_num_and_den q ⟨hdvd, hc⟩
    rw [padicValNat.eq_zero_of_not_dvd hden'] at h
    omega
  have hA0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnd
  rw [hA0] at h
  have hB : padicValNat p q.den ≠ 0 := by omega
  refine ⟨?_, ?_⟩
  · rw [Ne, num_zmod_eq_zero_iff]
    exact hnd
  · rw [den_zmod_eq_zero_iff]
    by_contra hc
    exact hB (padicValNat.eq_zero_of_not_dvd hc)

/-! ## The residue of `1 - q` -/

theorem ratRes_one_sub {q : ℚ} (hden : ((q.den : ZMod p) ≠ 0)) :
    ratRes p (1 - q) = 1 - ratRes p q := by
  have hdQ : ((q.den : ℚ)) ≠ 0 := den_cast_ne_zero q
  have hd : ((((q.den : ℤ)) : ZMod p) ≠ 0) := by push_cast; exact hden
  have hpres : (1 - q) = ((((q.den : ℤ) - q.num : ℤ)) : ℚ) / (((q.den : ℤ)) : ℚ) := by
    push_cast
    rw [num_eq_mul_den q]
    field_simp
  rw [ratRes_of_eq_div hd hpres]
  simp only [ratRes]
  push_cast
  field_simp

/-! ## The valuation and residue homomorphisms -/

/-- The `p`-adic valuation of a rational unit. -/
def ratPadicValHom (p : ℕ) [Fact p.Prime] : ℚˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (padicValRat p ((a : ℚˣ) : ℚ))
  map_one' := by
    show Multiplicative.ofAdd (padicValRat p ((1 : ℚˣ) : ℚ)) = 1
    rw [Units.val_one, padicValRat.one]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (padicValRat p (((a * b : ℚˣ)) : ℚ)) = _
    rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero]
    rfl

theorem ratPadicValHom_toAdd (a : ℚˣ) :
    Multiplicative.toAdd (ratPadicValHom p a) = padicValRat p ((a : ℚˣ) : ℚ) := rfl

theorem mem_ratPadicValHom_ker_iff {a : ℚˣ} :
    a ∈ (ratPadicValHom p).ker ↔ padicValRat p ((a : ℚˣ) : ℚ) = 0 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa [ratPadicValHom_toAdd] using this
  · intro h
    show Multiplicative.ofAdd (padicValRat p ((a : ℚˣ) : ℚ)) = 1
    rw [h]
    rfl

theorem isPadicUnit_of_mem_ker {a : ℚˣ} (h : a ∈ (ratPadicValHom p).ker) :
    IsPadicUnit p ((a : ℚˣ) : ℚ) :=
  (padicValRat_eq_zero_iff a.ne_zero).1 (mem_ratPadicValHom_ker_iff.1 h)

/-- The residue homomorphism on the rational units of `p`-adic valuation zero. -/
noncomputable def ratResHom (p : ℕ) [Fact p.Prime] :
    (ratPadicValHom p).ker →* (ZMod p)ˣ where
  toFun a := Units.mk0 (ratRes p ((a.1 : ℚˣ) : ℚ)) (isPadicUnit_of_mem_ker a.2).ratRes_ne_zero
  map_one' := by
    refine Units.ext ?_
    show ratRes p ((1 : ℚˣ) : ℚ) = 1
    rw [Units.val_one, ratRes_one]
  map_mul' a b := by
    refine Units.ext ?_
    show ratRes p (((a.1 * b.1 : ℚˣ)) : ℚ) = _
    rw [Units.val_mul,
      ratRes_mul (isPadicUnit_of_mem_ker a.2) (isPadicUnit_of_mem_ker b.2)]
    rfl

theorem ratResHom_val {a : ℚˣ} (h : a ∈ (ratPadicValHom p).ker) :
    ((ratResHom p ⟨a, h⟩ : (ZMod p)ˣ) : ZMod p) = ratRes p ((a : ℚˣ) : ℚ) := rfl

theorem padicValInt_eq_zero_of_ne {m : ℤ} (h : ((m : ZMod p) ≠ 0)) : padicValInt p m = 0 := by
  refine padicValNat.eq_zero_of_not_dvd ?_
  intro hdvd
  exact h (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.natCast_dvd.2 hdvd)

theorem intCast_ne_zero_of_zmod {m : ℤ} (h : ((m : ZMod p) ≠ 0)) : ((m : ℚ)) ≠ 0 := by
  intro hcon
  refine h ?_
  have : m = 0 := by exact_mod_cast hcon
  rw [this]
  simp

/-! ## The tame symbol data -/

/-- **The tame symbol data of `ℚ` at a prime, with residue field `ZMod p`.** -/
noncomputable def ratTameData (p : ℕ) [Fact p.Prime] : TameData ℚ (ZMod p) where
  val := ratPadicValHom p
  res := ratResHom p
  res_neg_one := by
    intro h
    refine Units.ext ?_
    rw [ratResHom_val]
    have hval : (((-1 : ℚˣ)) : ℚ) = ((-1 : ℤ) : ℚ) := by norm_num
    rw [hval, ratRes_intCast]
    push_cast
    rfl
  oneSub_of_pos := by
    intro a ha hpos
    rw [ratPadicValHom_toAdd] at hpos
    obtain ⟨hnum, hden⟩ := props_of_padicValRat_pos a.ne_zero hpos
    have hres0 : ratRes p ((a : ℚˣ) : ℚ) = 0 := by
      simp only [ratRes, hnum, zero_div]
    have hone : ratRes p (1 - ((a : ℚˣ) : ℚ)) = 1 := by
      rw [ratRes_one_sub hden, hres0, sub_zero]
    have hval : ((oneSubUnit ha : ℚˣ) : ℚ) = 1 - ((a : ℚˣ) : ℚ) := oneSubUnit_val ha
    have hunit : IsPadicUnit p ((oneSubUnit ha : ℚˣ) : ℚ) := by
      refine isPadicUnit_of_ratRes_ne_zero ?_
      rw [hval, hone]
      exact one_ne_zero
    have hmem : oneSubUnit ha ∈ (ratPadicValHom p).ker := by
      rw [mem_ratPadicValHom_ker_iff]
      exact (padicValRat_eq_zero_iff (oneSubUnit ha).ne_zero).2 hunit
    refine ⟨hmem, ?_⟩
    refine Units.ext ?_
    rw [ratResHom_val, hval, hone]
    rfl
  oneSub_of_zero := by
    intro a ha h
    have hunit := isPadicUnit_of_mem_ker h
    have hden : ((((a : ℚˣ) : ℚ).den : ZMod p) ≠ 0) := hunit.2
    have hval : ((oneSubUnit ha : ℚˣ) : ℚ) = 1 - ((a : ℚˣ) : ℚ) := oneSubUnit_val ha
    have hdQ : (((((a : ℚˣ) : ℚ)).den : ℚ)) ≠ 0 := den_cast_ne_zero _
    have hd : (((((((a : ℚˣ) : ℚ)).den : ℤ)) : ZMod p) ≠ 0) := by push_cast; exact hden
    have hpres : ((oneSubUnit ha : ℚˣ) : ℚ)
        = (((((((a : ℚˣ) : ℚ)).den : ℤ) - (((a : ℚˣ) : ℚ)).num : ℤ)) : ℚ)
          / ((((((a : ℚˣ) : ℚ)).den : ℤ)) : ℚ) := by
      rw [hval]
      push_cast
      rw [num_eq_mul_den ((a : ℚˣ) : ℚ)]
      field_simp
    have hdenone : (((oneSubUnit ha : ℚˣ) : ℚ).den : ZMod p) ≠ 0 :=
      den_ne_zero_of_eq_div hd hpres
    have hnonneg : 0 ≤ Multiplicative.toAdd (ratPadicValHom p (oneSubUnit ha)) := by
      rw [ratPadicValHom_toAdd, padicValRat_eq_sub]
      have : padicValNat p (((oneSubUnit ha : ℚˣ) : ℚ)).den = 0 := by
        refine padicValNat.eq_zero_of_not_dvd ?_
        intro hdvd
        exact hdenone ((den_zmod_eq_zero_iff _).2 hdvd)
      rw [this]
      simp
    refine ⟨hnonneg, ?_⟩
    intro hposv
    rw [ratPadicValHom_toAdd] at hposv
    obtain ⟨hnum0, -⟩ := props_of_padicValRat_pos (oneSubUnit ha).ne_zero hposv
    have hres0 : ratRes p ((oneSubUnit ha : ℚˣ) : ℚ) = 0 := by
      simp only [ratRes, hnum0, zero_div]
    rw [hval, ratRes_one_sub hden] at hres0
    refine Units.ext ?_
    rw [ratResHom_val]
    have : ratRes p ((a : ℚˣ) : ℚ) = 1 := by linear_combination -hres0
    rw [this]
    rfl
  oneSub_of_neg := by
    intro a ha hneg
    rw [ratPadicValHom_toAdd] at hneg
    obtain ⟨hnum, hden0⟩ := props_of_padicValRat_neg a.ne_zero hneg
    set q : ℚ := ((a : ℚˣ) : ℚ) with hq
    have hval : ((oneSubUnit ha : ℚˣ) : ℚ) = 1 - q := oneSubUnit_val ha
    have hdQ : ((q.den : ℚ)) ≠ 0 := den_cast_ne_zero q
    have hdiff : (((q.den : ℤ) - q.num : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      rw [hden0, zero_sub]
      exact neg_ne_zero.2 hnum
    have hdiffQ : ((((q.den : ℤ) - q.num : ℤ)) : ℚ) ≠ 0 := intCast_ne_zero_of_zmod hdiff
    have hpres : ((oneSubUnit ha : ℚˣ) : ℚ)
        = ((((q.den : ℤ) - q.num : ℤ)) : ℚ) / (((q.den : ℤ)) : ℚ) := by
      rw [hval]
      push_cast
      rw [num_eq_mul_den q]
      field_simp
    -- the valuation is unchanged
    have hdenQ : ((((q.den : ℤ)) : ℚ)) ≠ 0 := by push_cast; exact hdQ
    have hvalcalc : padicValRat p ((oneSubUnit ha : ℚˣ) : ℚ) = padicValRat p q := by
      rw [hpres, padicValRat.div hdiffQ hdenQ, padicValRat.of_int, padicValRat.of_int,
        padicValInt_eq_zero_of_ne hdiff, padicValRat_eq_sub q,
        padicValNat.eq_zero_of_not_dvd (by
          intro hdvd
          exact hnum ((num_zmod_eq_zero_iff q).2 hdvd))]
      have hnat : ((q.den : ℤ)).natAbs = q.den := by simp
      show (0 : ℤ) - (padicValInt p ((q.den : ℤ)) : ℤ) = _
      rw [padicValInt, hnat]
      ring
    refine ⟨by rw [ratPadicValHom_toAdd, ratPadicValHom_toAdd, hvalcalc], ?_⟩
    -- the quotient has residue −1
    have hquot : ((a * (oneSubUnit ha)⁻¹ : ℚˣ) : ℚ)
        = ((q.num : ℤ) : ℚ) / ((((q.den : ℤ) - q.num : ℤ)) : ℚ) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hval]
      rw [eq_div_iff hdiffQ]
      push_cast
      rw [num_eq_mul_den q]
      field_simp
      ring
    have hres : ratRes p ((a * (oneSubUnit ha)⁻¹ : ℚˣ) : ℚ) = -1 := by
      rw [ratRes_of_eq_div hdiff hquot]
      push_cast
      rw [hden0, zero_sub, div_neg, div_self hnum]
    have hmem : (a * (oneSubUnit ha)⁻¹ : ℚˣ) ∈ (ratPadicValHom p).ker := by
      rw [mem_ratPadicValHom_ker_iff]
      refine (padicValRat_eq_zero_iff (a * (oneSubUnit ha)⁻¹).ne_zero).2 ?_
      refine isPadicUnit_of_ratRes_ne_zero ?_
      rw [hres]
      exact neg_ne_zero.2 one_ne_zero
    refine ⟨hmem, ?_⟩
    refine Units.ext ?_
    rw [ratResHom_val, hres]
    push_cast
    ring

/-- **The tame symbol at `p` on `K_2^M(ℚ)`.** -/
noncomputable def ratTameHom (p : ℕ) [Fact p.Prime] :
    MilnorKDeg ℚ 2 →+ Additive (ZMod p)ˣ := (ratTameData p).tameHom

theorem ratTameHom_symbol (a b : ℚˣ) :
    ratTameHom p (milnorClassDeg ℚ 2 ⟨[a, b], rfl⟩)
      = Additive.ofMul ((ratTameData p).tame a b) :=
  (ratTameData p).tameHom_symbol a b

/-! ## Valuation arithmetic on units -/

theorem padicValRat_mul_units (a b : ℚˣ) :
    padicValRat p (((a * b : ℚˣ)) : ℚ)
      = padicValRat p ((a : ℚˣ) : ℚ) + padicValRat p ((b : ℚˣ) : ℚ) := by
  rw [Units.val_mul, padicValRat.mul a.ne_zero b.ne_zero]

theorem padicValRat_zpow_units (a : ℚˣ) (n : ℤ) :
    padicValRat p (((a ^ n : ℚˣ)) : ℚ) = n * padicValRat p ((a : ℚˣ) : ℚ) := by
  simp

theorem padicValRat_self_prime : padicValRat p ((p : ℚ)) = 1 :=
  padicValRat.self (Fact.out (p := p.Prime)).one_lt

end RationalTame

end GaloisForLFunctions.HTGeometry
