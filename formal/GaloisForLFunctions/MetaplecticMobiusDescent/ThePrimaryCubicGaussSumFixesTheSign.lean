/-
Portions adapted from OpenAI’s Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The primary cubic Gauss sum fixes the Möbius sign

The cubic residue character is constructed by lifting Euler’s power from each
residue field. Its Jacobi sum lies in the prime ideal, has the same norm, and
is minus one modulo `(omega − 1)²`. Consequently it is minus the unique primary
generator. No generator-existence or Jacobi-normalization input is assumed.

The Gauss–Jacobi identity then gives `G³ = −p · #F`. Normalizing gives
`gamma³ = −p / |p|`; the result holds for every primitive additive character.
An invertible additive shift changes `G` by a cubic root, so leaves its cube
unchanged. Multiplication over distinct primes therefore exposes the Möbius
sign, once the composite Gauss sum is identified through Chinese remaindering.
-/

noncomputable section
open scoped BigOperators
open Finset NumberField

namespace GaloisForLFunctions.MetaplecticMobiusDescent

namespace CubicResidue

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
private theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj

private noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

/-- Binomial expansion reduces the Jacobi polynomial to finite-field power sums below degree `#F − 1`. -/
theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

private def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

private noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

/-- Reduction recovers the Euler power on units. -/
theorem cubicResidueChar_reduce_unit (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) (u : Fˣ) :
    ρ (cubicResidueChar ρ ζ hζ hζF m hq (u : F)) = (u : F) ^ m := by
  let e := cubic_roots_equiv ρ ζ hζ hζF
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m
  have he := e.apply_symm_apply (euler_to_roots m hq u)
  have he' := congrArg (fun v : rootsOfUnity 3 F => ((v : Fˣ) : F)) he
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (((euler_to_roots m hq u : rootsOfUnity 3 F) : Fˣ) : F) at he'
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m at he'
  exact he'

/-- The lifted Euler character takes values in the cubic roots of unity. -/
theorem cubicResidueChar_pow_three (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    cubicResidueChar ρ ζ hζ hζF m hq ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [(cubicResidueChar ρ ζ hζ hζF m hq).pow_apply_coe,
    MulChar.one_apply_coe]
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  let v : rootsOfUnity 3 R :=
    (cubic_roots_equiv ρ ζ hζ hζF).symm (euler_to_roots m hq u)
  change (((v : Rˣ) : R) ^ 3) = 1
  exact (mem_rootsOfUnity' 3 (v : Rˣ)).mp v.property

end CubicResidue

namespace Eisenstein

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- A fixed primitive cubic root in the Eisenstein integers. -/
def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

/-- A generator of the ramified prime above three. -/
def lambda : O := omega - 1

noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

def traceLambda : O := 1 + 2 * omega

theorem traceLambda_eq_unit_mul_lambda : traceLambda = -omega * lambda := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  dsimp [traceLambda, lambda]
  linear_combination hrel

theorem neg_omega_isUnit : IsUnit (-omega) :=
  (omega_primitive.isUnit (by decide)).neg

theorem traceLambda_mem_iff (P : Ideal O) : traceLambda ∈ P ↔ lambda ∈ P := by
  rw [traceLambda_eq_unit_mul_lambda, mul_comm]
  exact P.mul_unit_mem_iff_mem neg_omega_isUnit

theorem traceLambda_sq_dvd_iff (x : O) :
    traceLambda ^ 2 ∣ x ↔ lambda ^ 2 ∣ x := by
  rw [traceLambda_eq_unit_mul_lambda, mul_pow]
  exact (neg_omega_isUnit.pow 2).mul_left_dvd

/-- Away from the ramified prime, reduction preserves the order of the cubic root. -/
theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow

/-- Residue-field unit groups contain the three cubic roots of unity. -/
theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

/-- The cubic residue character lifted from Euler’s power in the residue field. -/
noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact CubicResidue.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

/-- Euler’s criterion, including the zero residue class. -/
theorem cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (CubicResidue.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(CubicResidue.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact CubicResidue.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u

/-- The actual residue character has exponent three. -/
theorem cubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change CubicResidue.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact CubicResidue.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq

/-- Euler’s power cannot be identically one on the residue-field units. -/
theorem cubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  intro hχ
  have hall : ∀ u : (O ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    have hr := cubicChar_reduce P hgood (u : O ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at hr
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      Nat.card_eq_fintype_card] using hr.symm
  have hdvd := (FiniteField.forall_pow_eq_one_iff (O ⧸ P) m).mp hall
  rw [hq] at hdvd
  have hle := Nat.le_of_dvd hm hdvd
  omega

/-- The actual residue character has exact order three. -/
theorem cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd : orderOf (cubicChar P hgood) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  · exact h3


/-- The cubic Jacobi sum is minus one modulo the square of the ramified prime. -/
theorem cubicJacobi_primary (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood)
      omega_primitive)

/-- Euler reduction and vanishing power sums place the Jacobi sum in the original prime. -/
theorem cubicJacobi_mem_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact CubicResidue.euler_jacobi_sum_zero m hm

/-- The Jacobi sum times its inverse-character sum equals the residue-field cardinality. -/
theorem cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let ι : O →+* K := algebraMap O K
  let ψ := (cubicChar P hgood).ringHomComp ι
  have hchar : ringChar K ≠ ringChar (O ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (O ⧸ P) (ringChar (O ⧸ P))).ne_zero.symm
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr
      (cubicChar_ne_one P hgood)
  have hχ2 : cubicChar P hgood * cubicChar P hgood ≠ 1 := by
    intro h
    have hd : orderOf (cubicChar P hgood) ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hψ2 : ψ * ψ ≠ 1 := by
    rw [show ψ * ψ =
      (cubicChar P hgood * cubicChar P hgood).ringHomComp ι by
        exact (MulChar.ringHomComp_mul _ _ _).symm]
    exact (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr hχ2
  have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hψ hψ2
  apply RingOfIntegers.coe_injective
  change ι (jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹) =
    ι (Nat.card (O ⧸ P) : O)
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp,
    ← MulChar.ringHomComp_inv]
  simpa only [ψ, Nat.card_eq_fintype_card, map_natCast] using hprod

private noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

/-- Complex conjugation on the Eisenstein integers, defined algebraically. -/
noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

/-- The nontrivial automorphism squares the cubic root. -/
theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

private theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  simp only [← pow_mul]
  rw [Nat.mul_comm]

/-- Conjugation inverts the cubic residue character. -/
theorem cubicChar_conj_eq_inv (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, map_zero, zero_pow (by decide)]
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3

/-- Conjugating the Jacobi sum inverts both characters. -/
theorem cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by
  classical
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_conj_eq_inv P hgood]
  rfl

/-- The Jacobi sum has the norm of the prime ideal. -/
theorem cubicJacobi_mul_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood

/-- The ramified prime above three does not divide two. -/
theorem lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd : ringChar (O ⧸ I) ∣ 2 := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hcard] at heven
  norm_num at heven


private theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

private theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

private theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

private theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simpa using h

/-- The integer norm in the Eisenstein field is the product of the two conjugates. -/
theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  exact h

/-- Containment and equality of ideal norms show that the Jacobi sum generates the prime. -/
theorem cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hnormJ : Algebra.norm ℤ J = (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
    change ((Algebra.norm ℤ J : ℤ) : O) = (Nat.card (O ⧸ P) : O)
    rw [norm_int_eq_mul_conjO]
    exact cubicJacobi_mul_conj P hgood
  have habsJ : Ideal.absNorm (Ideal.span {J}) = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_span_singleton, hnormJ]
    simp
  have habsP : Ideal.absNorm P = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hle : Ideal.span {J} ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr (cubicJacobi_mem_prime P hgood)
  obtain ⟨Q, hQ⟩ := (Ideal.dvd_iff_le).mpr hle
  have hq : Nat.card (O ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hQnorm : Ideal.absNorm Q = 1 := by
    have heq : Nat.card (O ⧸ P) = Nat.card (O ⧸ P) * Ideal.absNorm Q := by
      calc
        Nat.card (O ⧸ P) = Ideal.absNorm (Ideal.span {J}) := habsJ.symm
        _ = Ideal.absNorm (P * Q) := by rw [hQ]
        _ = Ideal.absNorm P * Ideal.absNorm Q := map_mul Ideal.absNorm P Q
        _ = Nat.card (O ⧸ P) * Ideal.absNorm Q := by rw [habsP]
    exact (mul_left_cancel₀ hq (heq.symm.trans (by ring)))
  have hQtop : Q = ⊤ := Ideal.absNorm_eq_one_iff.mp hQnorm
  change P = Ideal.span {J}
  rw [hQ, hQtop, ← Ideal.one_eq_top, mul_one]

/-- Negating the Jacobi sum produces a primary generator at every prime away from three. -/
theorem cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  refine ⟨-J, ?_, ?_, by simp [J]⟩
  · have h := cubicJacobi_generates_prime P hgood
    simpa only [J, Ideal.span_singleton_neg] using h
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring

/-- The Jacobi sum differs from any generator only by a unit. -/
theorem cubicJacobi_unit_multiple_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  have hspan := hP.symm.trans (cubicJacobi_generates_prime P hgood)
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨u, hu.symm⟩

/-- The Jacobi sum is exactly minus the primary generator: the congruence determines the unit. -/
theorem cubicJacobi_eq_neg_primary_generator_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple_of_principal P hgood p hP
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu


/-- The actual cubic Gauss sum has cube `−p · #F` for every primitive additive character. -/
theorem cubicGauss_cube {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

private noncomputable def complexEmbedding : K →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

/-- A fixed complex embedding of the Eisenstein integers. -/
noncomputable def ringComplex : O →+* ℂ :=
  complexEmbedding.toRingHom.comp (algebraMap O K)

theorem ringComplex_injective : Function.Injective ringComplex :=
  complexEmbedding.injective.comp NumberField.RingOfIntegers.coe_injective

private theorem ringComplex_conjO (x : O) :
    ringComplex (conjO x) = star (ringComplex x) := by
  let z := ringComplex omega
  have hz3 : z ^ 3 = 1 := by
    change ringComplex omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ringComplex.comp conjO.toRingHom = (starRingEnd ℂ).comp ringComplex := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ringComplex (conjO omega) = star (ringComplex omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

/-- A definite primitive complex additive character realizes the prime Gauss-cube identity. -/
theorem cubicGauss_cube_complex (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) ^ 3 =
      -(ringComplex p) * (Nat.card (O ⧸ P) : ℂ) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact cubicGauss_cube ringComplex ringComplex_injective P hgood p hP hprimary
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P))
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P))

/-- The primary generator has norm equal to its residue-field cardinality. -/
theorem primary_generator_mul_conj_eq_card (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simpa only [neg_mul_neg] using h

/-- Normalization leaves precisely minus the angular part of the primary generator. -/
theorem cubicGauss_normalized_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      ψ /
      (‖ringComplex p‖ : ℂ)) ^ 3 =
      -(ringComplex p) / (‖ringComplex p‖ : ℂ) := by
  let z := ringComplex p
  let g := gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
    ψ
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ringComplex hnormO
  rw [map_mul, ringComplex_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube ringComplex ringComplex_injective P hgood p hP hprimary ψ hψ
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp

/-- The normalized identity for a definite primitive complex additive character. -/
theorem cubicGauss_normalized_cube_complex (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) /
      (‖ringComplex p‖ : ℂ)) ^ 3 =
      -(ringComplex p) / (‖ringComplex p‖ : ℂ) :=
  cubicGauss_normalized_cube P hgood p hP hprimary _
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P))

/-- Cubing erases the phase from every invertible additive shift. -/
theorem cubicGauss_cube_mulShift {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (ψ : AddChar (O ⧸ P) E) (a : (O ⧸ P)ˣ) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) (ψ.mulShift a) ^ 3 =
      gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := (cubicChar P hgood).ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := by
    change ((cubicChar P hgood).ringHomComp ι) ^ 3 = 1
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three P hgood,
      MulChar.ringHomComp_one]
  have hχinv3 : (χ⁻¹ a) ^ 3 = 1 := by
    have h : (χ⁻¹) ^ 3 = 1 := by rw [inv_pow, hχ3, inv_one]
    rw [← (χ⁻¹).pow_apply_coe, h, MulChar.one_apply_coe]
  change gaussSum χ (ψ.mulShift a) ^ 3 = gaussSum χ ψ ^ 3
  rw [gaussSum_mulShift_eq, mul_pow, hχinv3, one_mul]

/-- The primary generator obtained directly from the cubic Jacobi sum. -/
def primaryGenerator (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) : O :=
  -jacobiSum (cubicChar P hgood) (cubicChar P hgood)

/-- The Jacobi construction generates the given prime and is congruent to one
modulo the square of the ramified prime. -/
theorem primaryGenerator_spec (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    P = Ideal.span {primaryGenerator P hgood} ∧
      lambda ^ 2 ∣ primaryGenerator P hgood - 1 := by
  constructor
  · simpa only [primaryGenerator, Ideal.span_singleton_neg] using
      cubicJacobi_generates_prime P hgood
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    rw [primaryGenerator, hJ]
    ring

/-- Primary normalization removes every unit ambiguity. -/
theorem primaryGenerator_unique (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) : p = primaryGenerator P hgood := by
  rw [primaryGenerator,
    cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary, neg_neg]

/-- A definite complex Gauss sum at each prime away from three, normalized
by the absolute value of its primary generator. -/
def normalizedCubicGauss (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) : ℂ :=
  gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) /
      (‖ringComplex (primaryGenerator P hgood)‖ : ℂ)

/-- The canonical normalized cubic Gauss sum has cube equal to minus the
angular part of the canonical primary generator. -/
theorem normalizedCubicGauss_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    normalizedCubicGauss P hgood ^ 3 =
      -ringComplex (primaryGenerator P hgood) /
        (‖ringComplex (primaryGenerator P hgood)‖ : ℂ) :=
  cubicGauss_normalized_cube_complex P hgood (primaryGenerator P hgood)
    (primaryGenerator_spec P hgood).1 (primaryGenerator_spec P hgood).2

end
end Eisenstein
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.cubicChar_order
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.cubicJacobi_eq_neg_primary_generator_of_principal
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.primaryGenerator_spec
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.primaryGenerator_unique
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.cubicGauss_normalized_cube
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.normalizedCubicGauss_cube
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.cubicGauss_cube_mulShift
