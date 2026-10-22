import GaloisForLFunctions.RHTower.FieldOneFiniteStageModuleOneFundamentalDomain
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalPrimeFactorization
import GaloisForLFunctions.RHTower.Deninger.DeningerSUnitEndpointPage

/-!
# Integral coordinates on the literal finite-stage CCM S-unit subgroup

The positive rational `S`-units in the Connes--Marcolli finite-stage carrier
are the free abelian group on the selected finite places.  This file proves the
statement on the literal subgroup used in the idele quotient, rather than on a
parallel arithmetic model:

`Additive (Q_S^* \cap Q_{>0}) \simeq+ (S \to Z)`.

For all `S`-units, the exponent map is onto and two elements have the same
coordinates exactly when their rational absolute values agree.  Thus its only
fiber ambiguity is the sign subgroup `{+-1}`.  This is the exact lattice input
used in Connes--Marcolli Lemma 2.29 to obtain logarithmic orbit growth.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open _root_.RHTower

/-- Rational units whose exponent at `p` vanishes. -/
def fieldOneRationalExponentZeroSubgroup (p : ℕ) : Subgroup ℚˣ where
  carrier := {q | deningerRatExp (q : ℚ) p = 0}
  one_mem' := by simp
  mul_mem' := by
    intro q r hq hr
    change deningerRatExp (((q * r : ℚˣ) : ℚ)) p = 0
    rw [Units.val_mul,
      deningerRatExp_mul (Units.ne_zero q) (Units.ne_zero r), Finsupp.add_apply,
      hq, hr, add_zero]
  inv_mem' := by
    intro q hq
    change deningerRatExp (((q⁻¹ : ℚˣ) : ℚ)) p = 0
    rw [Units.val_inv_eq_inv_val,
      deningerRatExp_inv (Units.ne_zero q), Finsupp.neg_apply, hq, neg_zero]

/-- A literal CCM `S`-unit has zero prime exponent outside `S`. -/
theorem fieldOneSUnit_exponent_outside
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (p : Nat.Primes)
    (hp : (Rat.HeightOneSpectrum.primesEquiv.symm p) ∉ S) :
    deningerRatExp (q.1 : ℚ) p.1 = 0 := by
  have hle : fieldOneSUnitSubgroup S ≤
      fieldOneRationalExponentZeroSubgroup p.1 := by
    rw [fieldOneSUnitSubgroup]
    apply (Subgroup.closure_le (fieldOneRationalExponentZeroSubgroup p.1)).2
    intro r hr
    rcases hr with (rfl | ⟨v, rfl⟩)
    · simp [fieldOneRationalExponentZeroSubgroup]
    · change deningerRatExp
          ((fieldOneRationalPrimeUnit v.1 : ℚˣ) : ℚ) p.1 = 0
      rw [show ((fieldOneRationalPrimeUnit v.1 : ℚˣ) : ℚ) =
          ((Rat.HeightOneSpectrum.primesEquiv v.1 : Nat.Primes) : ℕ) by rfl,
        deningerRatExp_natCast_prime
          (Rat.HeightOneSpectrum.primesEquiv v.1).2,
        Finsupp.single_apply]
      rw [if_neg]
      intro heq
      apply hp
      have hev : Rat.HeightOneSpectrum.primesEquiv v.1 = p := by
        apply Subtype.ext
        exact heq
      have hev' : Rat.HeightOneSpectrum.primesEquiv.symm p = v.1 := by
        rw [← hev]
        exact Equiv.symm_apply_apply _ _
      rw [hev']
      exact v.2
  exact hle q.2

/-- Prime-exponent coordinates of a literal CCM `S`-unit. -/
def fieldOneSUnitExponent
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (v : ↥S) : ℤ :=
  deningerRatExp (q.1 : ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-- Rational `S`-unit with prescribed integral prime exponents. -/
def fieldOneSUnitProduct
    (S : Finset (HeightOneSpectrum ℤ))
    (n : ↥S → ℤ) : ℚˣ :=
  ∏ v : ↥S, fieldOneRationalPrimeUnit v.1 ^ n v

theorem fieldOneSUnitProduct_mem
    (S : Finset (HeightOneSpectrum ℤ)) (n : ↥S → ℤ) :
    fieldOneSUnitProduct S n ∈ fieldOneSUnitSubgroup S := by
  classical
  apply Subgroup.prod_mem
  intro v _
  exact Subgroup.zpow_mem (fieldOneSUnitSubgroup S)
    (fieldOne_prime_mem_sUnitSubgroup S v) _

/-- Prescribed prime exponents are recovered exactly. -/
theorem fieldOneSUnitExponent_product
    (S : Finset (HeightOneSpectrum ℤ)) (n : ↥S → ℤ) :
    fieldOneSUnitExponent S
      ⟨fieldOneSUnitProduct S n, fieldOneSUnitProduct_mem S n⟩ = n := by
  classical
  funext v
  unfold fieldOneSUnitExponent
  let P : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v.1
  letI : Fact P.1.Prime := ⟨P.2⟩
  rw [deningerRatExp_apply_of_prime P.2]
  have hprod := _root_.RHTower.deningerPadicValRat_prod
    (q := P.1) (s := (Finset.univ : Finset ↥S))
    (fun w => fieldOneRationalPrimeUnit w.1 ^ n w)
  have hterm (w : ↥S) :
      padicValRat P.1
          (((fieldOneRationalPrimeUnit w.1 ^ n w : ℚˣ) : ℚ)) =
        if w = v then n w else 0 := by
    rw [Units.val_zpow_eq_zpow_val, padicValRat.zpow]
    change n w * padicValRat P.1
        (((_root_.RHTower.deningerPrimeUnit
          (Rat.HeightOneSpectrum.primesEquiv w.1) : ℚˣ) : ℚ)) = _
    rw [_root_.RHTower.deningerPadicValRat_primeUnit]
    by_cases hw : w = v
    · subst w
      simp [P]
    · have hpne : Rat.HeightOneSpectrum.primesEquiv w.1 ≠ P := by
        intro hp
        apply hw
        apply Subtype.ext
        exact Rat.HeightOneSpectrum.primesEquiv.injective hp
      simp [hw, hpne]
  calc
    padicValRat P.1
        (((fieldOneSUnitProduct S n : ℚˣ) : ℚ)) =
        ∑ w : ↥S, padicValRat P.1
          (((fieldOneRationalPrimeUnit w.1 ^ n w : ℚˣ) : ℚ)) := by
            simpa [fieldOneSUnitProduct] using hprod
    _ = ∑ w : ↥S, if w = v then n w else 0 := by
      exact Finset.sum_congr rfl (fun w _ => hterm w)
    _ = n v := by simp

theorem fieldOneSUnitProduct_pos
    (S : Finset (HeightOneSpectrum ℤ)) (n : ↥S → ℤ) :
    (0 : ℚ) < (fieldOneSUnitProduct S n : ℚ) := by
  classical
  have hpos : ∀ v : ↥S,
      (0 : ℚ) < ((fieldOneRationalPrimeUnit v.1 : ℚˣ) : ℚ) ^ n v := by
    intro v
    change 0 < (((Rat.HeightOneSpectrum.primesEquiv v.1 : Nat.Primes) : ℕ) : ℚ) ^ n v
    exact zpow_pos (by exact_mod_cast
      (Rat.HeightOneSpectrum.primesEquiv v.1).2.pos) _
  simpa [fieldOneSUnitProduct] using
    (Finset.prod_pos (s := Finset.univ) (fun v _ => hpos v))

/-- The product reconstructed from an `S`-unit's coordinates has the same full
prime-exponent vector as its positive representative. -/
theorem fieldOneSUnitProduct_exponent_eq_abs
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) :
    deningerRatExp
        (fieldOneSUnitProduct S (fieldOneSUnitExponent S q) : ℚ) =
      deningerRatExp |(q.1 : ℚ)| := by
  ext p
  by_cases hprime : p.Prime
  · let P : Nat.Primes := ⟨p, hprime⟩
    by_cases hp : Rat.HeightOneSpectrum.primesEquiv.symm P ∈ S
    · let v : ↥S := ⟨Rat.HeightOneSpectrum.primesEquiv.symm P, hp⟩
      have hvp : Rat.HeightOneSpectrum.primesEquiv v.1 = P := by simp [v]
      have hcoord := congrFun
        (fieldOneSUnitExponent_product S (fieldOneSUnitExponent S q)) v
      change deningerRatExp
          (fieldOneSUnitProduct S (fieldOneSUnitExponent S q) : ℚ)
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 =
        deningerRatExp (q.1 : ℚ)
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 at hcoord
      rw [deningerRatExp_abs]
      simpa [hvp] using hcoord
    · have hout := fieldOneSUnit_exponent_outside S q P hp
      have hprodMem := fieldOneSUnitProduct_mem S (fieldOneSUnitExponent S q)
      have houtProd := fieldOneSUnit_exponent_outside S
        ⟨fieldOneSUnitProduct S (fieldOneSUnitExponent S q), hprodMem⟩ P hp
      rw [deningerRatExp_abs]
      exact houtProd.trans hout.symm
  · rw [deningerRatExp_apply_of_not_prime hprime,
      deningerRatExp_apply_of_not_prime hprime]

/-- Exact reconstruction of the positive representative of a literal CCM
`S`-unit from its prime exponents. -/
theorem fieldOneSUnitProduct_exponent_eq_abs_value
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) :
    (fieldOneSUnitProduct S (fieldOneSUnitExponent S q) : ℚ) =
      |(q.1 : ℚ)| := by
  apply deningerRatExp_injOn_pos (fieldOneSUnitProduct_pos S _)
    (abs_pos.mpr (Units.ne_zero q.1))
  exact fieldOneSUnitProduct_exponent_eq_abs S q

theorem fieldOneSUnitExponent_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (q r : fieldOneSUnitSubgroup S) :
    fieldOneSUnitExponent S (q * r) =
      fieldOneSUnitExponent S q + fieldOneSUnitExponent S r := by
  funext v
  unfold fieldOneSUnitExponent
  rw [Subgroup.coe_mul, Units.val_mul,
    deningerRatExp_mul (Units.ne_zero q.1) (Units.ne_zero r.1),
    Finsupp.add_apply]
  rfl

/-- Positive part of the literal rational CCM `S`-unit subgroup. -/
def fieldOnePositiveSUnitSubgroup
    (S : Finset (HeightOneSpectrum ℤ)) : Subgroup ℚˣ where
  carrier := {q | q ∈ fieldOneSUnitSubgroup S ∧ 0 < (q : ℚ)}
  one_mem' := ⟨(fieldOneSUnitSubgroup S).one_mem, by norm_num⟩
  mul_mem' := by
    rintro q r ⟨hqS, hq⟩ ⟨hrS, hr⟩
    exact ⟨(fieldOneSUnitSubgroup S).mul_mem hqS hrS, by
      rw [Units.val_mul]
      exact mul_pos hq hr⟩
  inv_mem' := by
    rintro q ⟨hqS, hq⟩
    exact ⟨(fieldOneSUnitSubgroup S).inv_mem hqS, by
      rw [Units.val_inv_eq_inv_val]
      exact inv_pos.mpr hq⟩

def fieldOnePositiveSUnitToSUnit
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOnePositiveSUnitSubgroup S) : fieldOneSUnitSubgroup S :=
  ⟨q.1, q.2.1⟩

/-- Literal Connes--Marcolli lattice theorem:
`Q_S^* / {+-1} \simeq Z^S`, represented by positive `S`-units. -/
noncomputable def fieldOnePositiveSUnitsEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    Additive ↥(fieldOnePositiveSUnitSubgroup S) ≃+
      (↥S → ℤ) :=
  AddEquiv.mk'
    { toFun := fun q => fieldOneSUnitExponent S
        (fieldOnePositiveSUnitToSUnit S (Additive.toMul q))
      invFun := fun n => Additive.ofMul
        (⟨fieldOneSUnitProduct S n,
          fieldOneSUnitProduct_mem S n,
          fieldOneSUnitProduct_pos S n⟩ : fieldOnePositiveSUnitSubgroup S)
      left_inv := by
        intro q
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        have h := fieldOneSUnitProduct_exponent_eq_abs_value S
          (fieldOnePositiveSUnitToSUnit S (Additive.toMul q))
        simpa [fieldOnePositiveSUnitToSUnit,
          abs_of_pos (Additive.toMul q).2.2] using h
      right_inv := by
        intro n
        exact fieldOneSUnitExponent_product S n }
    (by
      intro q r
      exact fieldOneSUnitExponent_mul S
        (fieldOnePositiveSUnitToSUnit S (Additive.toMul q))
        (fieldOnePositiveSUnitToSUnit S (Additive.toMul r)))

theorem fieldOneSUnitExponent_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneSUnitExponent S) := by
  intro n
  exact ⟨⟨fieldOneSUnitProduct S n, fieldOneSUnitProduct_mem S n⟩,
    fieldOneSUnitExponent_product S n⟩

/-- Fibers of the full exponent map are exactly the sign pairs. -/
theorem fieldOneSUnitExponent_eq_iff_abs_eq
    (S : Finset (HeightOneSpectrum ℤ))
    (q r : fieldOneSUnitSubgroup S) :
    fieldOneSUnitExponent S q = fieldOneSUnitExponent S r ↔
      |(q.1 : ℚ)| = |(r.1 : ℚ)| := by
  constructor
  · intro h
    have hq := fieldOneSUnitProduct_exponent_eq_abs_value S q
    have hr := fieldOneSUnitProduct_exponent_eq_abs_value S r
    rw [h] at hq
    exact hq.symm.trans hr
  · intro h
    have he := congrArg deningerRatExp h
    rw [deningerRatExp_abs, deningerRatExp_abs] at he
    funext v
    exact congrArg (fun z : ℕ →₀ ℤ =>
      z (Rat.HeightOneSpectrum.primesEquiv v.1).1) he

/-- Sign bit of a rational `S`-unit. -/
def fieldOneSUnitPositiveSign
    {S : Finset (HeightOneSpectrum ℤ)}
    (q : fieldOneSUnitSubgroup S) : Bool :=
  decide ((0 : ℚ) < (q.1 : ℚ))

/-- Sign together with all selected prime exponents. -/
def fieldOneSUnitSignedExponent
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) : Bool × (↥S → ℤ) :=
  (fieldOneSUnitPositiveSign q, fieldOneSUnitExponent S q)

/-- Sign and exponent coordinates identify a literal rational CCM `S`-unit
uniquely. -/
theorem fieldOneSUnitSignedExponent_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective (fieldOneSUnitSignedExponent S) := by
  intro q r h
  have hsign : fieldOneSUnitPositiveSign q =
      fieldOneSUnitPositiveSign r := congrArg Prod.fst h
  have hexp : fieldOneSUnitExponent S q =
      fieldOneSUnitExponent S r := congrArg Prod.snd h
  have habs := (fieldOneSUnitExponent_eq_iff_abs_eq S q r).1 hexp
  apply Subtype.ext
  apply Units.ext
  by_cases hq : (0 : ℚ) < (q.1 : ℚ)
  · have hr : (0 : ℚ) < (r.1 : ℚ) := by
      by_contra hr
      have : fieldOneSUnitPositiveSign q ≠
          fieldOneSUnitPositiveSign r := by
        simp [fieldOneSUnitPositiveSign, hq, hr]
      exact this hsign
    simpa [abs_of_pos hq, abs_of_pos hr] using habs
  · have hqneg : (q.1 : ℚ) < 0 := lt_of_le_of_ne
        (le_of_not_gt hq) (Units.ne_zero q.1)
    have hrnot : ¬ (0 : ℚ) < (r.1 : ℚ) := by
      intro hr
      have : fieldOneSUnitPositiveSign q ≠
          fieldOneSUnitPositiveSign r := by
        simp [fieldOneSUnitPositiveSign, hq, hr]
      exact this hsign
    have hrneg : (r.1 : ℚ) < 0 := lt_of_le_of_ne
      (le_of_not_gt hrnot) (Units.ne_zero r.1)
    simpa [abs_of_neg hqneg, abs_of_neg hrneg] using habs

end

end GaloisForLFunctions.RHTower
