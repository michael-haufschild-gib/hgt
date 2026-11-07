/-
The quadratic Jacobi and sextic Gauss identities are adapted from OpenAI’s
formalization, Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheTorsionCharacteristics
import GaloisForLFunctions.MetaplecticMobiusDescent.CubingTheCompositeGaussSumRecoversMobius
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Möbius becomes a cubic Gauss coefficient

Counting the fibres of the square map gives the quadratic Jacobi identity.
The Gauss–Jacobi identities then give Hasse–Davenport for sextic characters.
At an Eisenstein prime, the primary cubic Gauss identity fixes its sign:
`chi(4) G₁ G₂ = −p G₃`.

Chinese remaindering assembles this identity over distinct primes. Combining
it with the exact Gauss norm gives `mu(I) conjugate(G₁) = c(I) G₂`, where the
explicit factor `c(I)` has norm one and contains only primary generators,
sextic values at four, and quadratic Gauss sums. The additive character may be
any primitive character on the actual quotient. A definite character supplies
a canonical endpoint as well.

This is an arithmetic conversion of coefficients. Identifying the resulting
cubic coefficients with an automorphic theta expansion is a separate step.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace JacobiQuadratic

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring

private def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring

private theorem square_fiber (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) :
    (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
  classical
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, (#{t : F | t ^ 2 = y}.toFinset : ℂ) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun t : F => t ^ 2) (f := fun t : F => χ (1 - t ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht])]
    simp
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact_mod_cast quadraticChar_card_sqrts hchar y

/-- Square-fibre counting and the substitution `t = 2x − 1` identify the quadratic Jacobi sum. -/
theorem jacobi_quadratic (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  classical
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 := by
    have ht := (Equiv.sum_comp (oneSub (F := F)) χ)
    change (∑ y : F, χ ((oneSub (F := F)) y)) = 0
    exact ht.trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber := square_fiber χ hchar
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ x : F, χ (4 * x * (1 - x)) := by
    have ht := Equiv.sum_comp (affineDouble (F := F) hchar)
      (fun t : F => χ (1 - t ^ 2))
    convert ht.symm using 1
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      change 4 * x * (1 - x) = 1 - (2 * x - 1) ^ 2
      ring
  calc
    jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ map_mul]
      ring

/-- Hasse–Davenport for a sextic character: the sextic Gauss sum is related to cubic and quadratic sums. -/
theorem gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1) :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    simpa only [J13, J11, hχ3] using jacobi_quadratic χ hchar hχ1
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  have hbasic : g1 * g3 * g2 = χ (4 : F) * g4 * g1 ^ 2 := by
    calc
      g1 * g3 * g2 = (g4 * J13) * g2 := by rw [hJ13]
      _ = χ (4 : F) * g4 * (g2 * J11) := by rw [hJquad]; ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := by rw [hJ12]; ring
  have hbasic' : g3 * g2 = χ (4 : F) * g4 * g1 := by
    apply mul_left_cancel₀ hg1ne
    calc
      g1 * (g3 * g2) = g1 * g3 * g2 := by ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := hbasic
      _ = g1 * (χ (4 : F) * g4 * g1) := by ring
  calc
    χ (4 : F) * g1 * (Fintype.card F : ℂ) =
        χ (4 : F) * g1 * (g2 * g4) := by rw [hG24]
    _ = (χ (4 : F) * g4 * g1) * g2 := by ring
    _ = g3 * g2 ^ 2 := by rw [← hbasic']; ring

/-- The sextic relation after division by a square root of the residue-field cardinality. -/
theorem normalized_gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1)
    (s : ℂ) (hs : s ^ 2 = (Fintype.card F : ℂ)) (hs0 : s ≠ 0) :
    χ (4 : F) * (gaussSum χ ψ / s) * (gaussSum (χ ^ 2) ψ / s) =
      (gaussSum (χ ^ 3) ψ / s) * (gaussSum (χ ^ 2) ψ / s) ^ 3 := by
  have hraw := gauss_sextic_relation χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6
  rw [← hs] at hraw
  field_simp
  linear_combination (gaussSum (χ ^ 2) ψ) * hraw

end JacobiQuadratic
namespace Eisenstein

/-- A complex cubic residue character. -/
def complexCubicChar (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    MulChar (O ⧸ P) ℂ := (cubicChar P hgood).ringHomComp ringComplex

/-- The quadratic residue character with complex values. -/
def complexQuadraticChar (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ := by
  classical
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)

/-- The sextic residue character whose square is the cubic residue character. -/
def complexSexticChar (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    MulChar (O ⧸ P) ℂ := complexCubicChar P hgood ^ 2 * complexQuadraticChar P

/-- The complex cubic character has exponent three. -/
theorem complexCubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : complexCubicChar P hgood ^ 3 = 1 := by
  rw [complexCubicChar, MulChar.ringHomComp_pow, cubicChar_pow_three,
    MulChar.ringHomComp_one]

/-- The cubic residue character remains nontrivial under the complex embedding. -/
theorem complexCubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : complexCubicChar P hgood ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff ringComplex_injective).mpr (cubicChar_ne_one P hgood)

/-- The square and cube of the sextic residue character recover the cubic and quadratic characters. -/
theorem complexSexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    complexSexticChar P hgood ^ 2 = complexCubicChar P hgood ∧
    complexSexticChar P hgood ^ 3 = complexQuadraticChar P ∧
    complexSexticChar P hgood ^ 6 = 1 := by
  classical
  let c := complexCubicChar P hgood
  let q := complexQuadraticChar P
  have hc : c ^ 3 = 1 := complexCubicChar_pow_three P hgood
  have hq : q ^ 2 = 1 :=
    ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom ℂ)).sq_eq_one
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 3 * c * q ^ 2 := by rw [mul_pow]; group
      _ = c := by rw [hc, hq]; group
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * q ^ 2 * q := by rw [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  change (c ^ 2 * q) ^ 6 = 1
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by rw [hthree, hq]

/-- The primary cubic identity turns Hasse–Davenport into an exact signed
product of sextic, cubic, and quadratic Gauss sums. -/
theorem sextic_cubic_gauss_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    complexSexticChar P hgood (4 : O ⧸ P) *
      gaussSum (complexSexticChar P hgood) ψ *
      gaussSum (complexCubicChar P hgood) ψ =
    -ringComplex (primaryGenerator P hgood) *
      gaussSum (complexQuadraticChar P) ψ := by
  classical
  let χ := complexSexticChar P hgood
  let c := complexCubicChar P hgood
  have hc3 : c ^ 3 = 1 := complexCubicChar_pow_three P hgood
  have hcne : c ≠ 1 := complexCubicChar_ne_one P hgood
  obtain ⟨h2, h3, h6⟩ := complexSexticChar_powers P hgood
  have hχ1 : χ ≠ 1 := by
    intro h
    exact hcne (by simpa only [χ, h, one_pow] using h2.symm)
  have hχ2 : χ ^ 2 ≠ 1 := by
    simpa only [χ, h2] using hcne
  have hχ4 : χ ^ 4 ≠ 1 := by
    intro h
    have hc2 : c ^ 2 = 1 := by
      calc
        c ^ 2 = (χ ^ 2) ^ 2 := by rw [h2]
        _ = χ ^ 4 := by group
        _ = 1 := h
    apply hcne
    calc
      c = c ^ 2 * c := by rw [hc2, one_mul]
      _ = c ^ 3 := by group
      _ = 1 := hc3
  have hd := JacobiQuadratic.gauss_sextic_relation χ ψ hchar hψ
    hχ1 hχ2 hχ4 h3 h6
  rw [h2, h3] at hd
  have hcub := cubicGauss_cube ringComplex ringComplex_injective P hgood
    (primaryGenerator P hgood) (primaryGenerator_spec P hgood).1
    (primaryGenerator_spec P hgood).2 ψ hψ
  change gaussSum c ψ ^ 3 = _ at hcub
  have hq : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_right_cancel₀ hq
  calc
    (χ 4 * gaussSum χ ψ * gaussSum c ψ) * (Fintype.card (O ⧸ P) : ℂ) =
        (χ 4 * gaussSum χ ψ * (Fintype.card (O ⧸ P) : ℂ)) * gaussSum c ψ := by ring
    _ = gaussSum (complexQuadraticChar P) ψ * gaussSum c ψ ^ 3 := by rw [hd]; ring
    _ = (-ringComplex (primaryGenerator P hgood) *
        gaussSum (complexQuadraticChar P) ψ) * (Fintype.card (O ⧸ P) : ℂ) := by
      rw [hcub, Nat.card_eq_fintype_card]
      ring

/-- The nontrivial cubic square makes the sextic character nontrivial. -/
theorem complexSexticChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : complexSexticChar P hgood ≠ 1 := by
  intro h
  have h2 := (complexSexticChar_powers P hgood).1
  rw [h, one_pow] at h2
  exact complexCubicChar_ne_one P hgood h2.symm

/-- In odd residue characteristic, the quadratic character is nontrivial. -/
theorem complexQuadraticChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : complexQuadraticChar P ≠ 1 := by
  classical
  exact (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
    (quadraticChar_ne_one hchar)

/-- The primary generator has the square-root norm of the residue-field size. -/
theorem norm_primaryGenerator (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    ‖ringComplex (primaryGenerator P hgood)‖ = Real.sqrt (Fintype.card (O ⧸ P)) := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P)
  have hg := ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card
    (complexCubicChar_ne_one P hgood) hψ
  have hc := cubicGauss_cube ringComplex ringComplex_injective P hgood
    (primaryGenerator P hgood) (primaryGenerator_spec P hgood).1
    (primaryGenerator_spec P hgood).2 ψ hψ
  change gaussSum (complexCubicChar P hgood) ψ ^ 3 = _ at hc
  rw [Nat.card_eq_fintype_card] at hc
  have hn := congrArg norm hc
  rw [norm_pow, norm_mul, norm_neg, Complex.norm_natCast, hg] at hn
  have hq : (Fintype.card (O ⧸ P) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mul_right_cancel₀ hq
  calc
    ‖ringComplex (primaryGenerator P hgood)‖ * (Fintype.card (O ⧸ P) : ℝ) =
        Real.sqrt (Fintype.card (O ⧸ P)) ^ 3 := hn.symm
    _ = Real.sqrt (Fintype.card (O ⧸ P)) * (Fintype.card (O ⧸ P) : ℝ) := by
      rw [pow_succ, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

/-- The explicit angular and quadratic factor converting a Möbius-weighted
conjugate sextic Gauss sum into a cubic Gauss sum. -/
def gaussConversionFactor (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (ψ : AddChar (O ⧸ P) ℂ) : ℂ :=
  complexSexticChar P hgood (4 : O ⧸ P) * (Fintype.card (O ⧸ P) : ℂ) /
    (ringComplex (primaryGenerator P hgood) * gaussSum (complexQuadraticChar P) ψ)

/-- The local Möbius sign converts the conjugate sextic Gauss sum into a cubic Gauss sum. -/
theorem neg_star_sexticGauss_eq_cubic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    -star (gaussSum (complexSexticChar P hgood) ψ) =
      gaussConversionFactor P hgood ψ * gaussSum (complexCubicChar P hgood) ψ := by
  let g1 := gaussSum (complexSexticChar P hgood) ψ
  let g2 := gaussSum (complexCubicChar P hgood) ψ
  let g3 := gaussSum (complexQuadraticChar P) ψ
  let p := ringComplex (primaryGenerator P hgood)
  let z := complexSexticChar P hgood (4 : O ⧸ P)
  have hq : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : p ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_primaryGenerator]
    exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  have hg3 : g3 ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hq (complexQuadraticChar_ne_one P hchar) hψ
  have hprod : z * g1 * g2 = -p * g3 :=
    sextic_cubic_gauss_product P hgood hchar ψ hψ
  have hstar : g1 * star g1 = (Fintype.card (O ⧸ P) : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card (complexSexticChar_ne_one P hgood) hψ
    rw [← star_gaussSum_eq] at h
    exact h
  change -star g1 = (z * (Fintype.card (O ⧸ P) : ℂ) / (p * g3)) * g2
  apply mul_left_cancel₀ (mul_ne_zero hp hg3)
  calc
    (p * g3) * -star g1 = (z * g1 * g2) * star g1 := by rw [hprod]; ring
    _ = z * (g1 * star g1) * g2 := by ring
    _ = (p * g3) * (z * (Fintype.card (O ⧸ P) : ℂ) / (p * g3) * g2) := by
      rw [hstar]
      field_simp

/-- Exact Gauss norms make the explicit conversion factor a unit in modulus. -/
theorem norm_gaussConversionFactor (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussConversionFactor P hgood ψ‖ = 1 := by
  have htwo : (2 : O ⧸ P) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : O ⧸ P) ≠ 0 := by
    convert pow_ne_zero 2 htwo using 1
    norm_num
  have hpow : complexSexticChar P hgood (4 : O ⧸ P) ^ 6 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0),
      (complexSexticChar_powers P hgood).2.2]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hfour)
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow (by decide : (6 : ℕ) ≠ 0)
  rw [gaussConversionFactor, norm_div, norm_mul, norm_mul, hnorm, one_mul,
    Complex.norm_natCast, norm_primaryGenerator,
    ArithmeticEffectivityTheory.norm_gaussSum_eq_sqrt_card
      (complexQuadraticChar_ne_one P hchar) hψ,
    ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

section Composite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (P : ι → Ideal O) [∀ i, (P i).IsMaximal]

/-- A Gauss sum on the composite residue ring with the product residue character. -/
def residueGauss (hinj : Function.Injective P)
    (χ : ∀ i, MulChar (O ⧸ P i) ℂ) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) : ℂ := by
  classical
  let e := primeCRT P hinj
  letI : Fintype (O ⧸ ∏ i, P i) :=
    Fintype.ofEquiv (∀ i, O ⧸ P i) e.symm.toEquiv
  exact ∑ x : O ⧸ ∏ i, P i, (∏ i, χ i (e x i)) * ψ x

/-- CRT factors the actual composite residue sum into the local Gauss sums. -/
theorem residueGauss_factorization (hinj : Function.Injective P)
    (χ : ∀ i, MulChar (O ⧸ P i) ℂ) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) :
    residueGauss P hinj χ ψ =
      ∏ i, gaussSum (χ i) (ProductGauss.localChar (fun i => O ⧸ P i)
        (ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom) i) := by
  classical
  let e := primeCRT P hinj
  letI : Fintype (O ⧸ ∏ i, P i) :=
    Fintype.ofEquiv (∀ i, O ⧸ P i) e.symm.toEquiv
  exact ProductGauss.factorization_equiv (fun i => O ⧸ P i) e χ ψ

/-- The `j`th power of the sextic character in the actual composite Gauss sum. -/
def sexticResidueGauss (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (j : ℕ)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) : ℂ :=
  residueGauss P hinj (fun i => complexSexticChar (P i) (hgood i) ^ j) ψ

/-- Hasse–Davenport and the primary cubic sign assemble over the actual CRT
quotient, recovering the ideal Möbius coefficient. -/
theorem sexticResidueGauss_product (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (hψ : ψ.IsPrimitive) :
    (∏ i, complexSexticChar (P i) (hgood i) (4 : O ⧸ P i)) *
      sexticResidueGauss P hinj hgood 1 ψ * sexticResidueGauss P hinj hgood 2 ψ =
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
      ringComplex (∏ i, primaryGenerator (P i) (hgood i)) *
      sexticResidueGauss P hinj hgood 3 ψ := by
  let η := ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom
  have hη : η.IsPrimitive := ProductGauss.primitive_comp_ringEquiv _ ψ hψ
  have hlocal (i : ι) :
      complexSexticChar (P i) (hgood i) (4 : O ⧸ P i) *
        gaussSum (complexSexticChar (P i) (hgood i) ^ 1)
          (ProductGauss.localChar (fun i => O ⧸ P i) η i) *
        gaussSum (complexSexticChar (P i) (hgood i) ^ 2)
          (ProductGauss.localChar (fun i => O ⧸ P i) η i) =
      -ringComplex (primaryGenerator (P i) (hgood i)) *
        gaussSum (complexSexticChar (P i) (hgood i) ^ 3)
          (ProductGauss.localChar (fun i => O ⧸ P i) η i) := by
    rw [pow_one, (complexSexticChar_powers (P i) (hgood i)).1,
      (complexSexticChar_powers (P i) (hgood i)).2.1]
    exact sextic_cubic_gauss_product (P i) (hgood i) (hchar i) _
      (ProductGauss.localChar_primitive (fun i => O ⧸ P i) η hη i)
  simp only [sexticResidueGauss, residueGauss_factorization]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  trans ∏ i, -ringComplex (primaryGenerator (P i) (hgood i)) *
    gaussSum (complexSexticChar (P i) (hgood i) ^ 3)
      (ProductGauss.localChar (fun i => O ⧸ P i) η i)
  · exact Finset.prod_congr rfl fun i _ => hlocal i
  · rw [Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_univ,
      primeProduct_moebius P hinj, map_prod]

/-- The exact sextic–cubic–quadratic identity for the constructed primitive
character, with every character-existence input discharged. -/
theorem canonicalSexticResidueGauss_product (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    (∏ i, complexSexticChar (P i) (hgood i) (4 : O ⧸ P i)) *
      sexticResidueGauss P hinj hgood 1 (canonicalProductAddChar P hinj) *
      sexticResidueGauss P hinj hgood 2 (canonicalProductAddChar P hinj) =
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
      ringComplex (∏ i, primaryGenerator (P i) (hgood i)) *
      sexticResidueGauss P hinj hgood 3 (canonicalProductAddChar P hinj) :=
  sexticResidueGauss_product P hinj hgood hchar _
    (canonicalProductAddChar_primitive P hinj)

/-- The product of the explicit angular and quadratic local factors. -/
def compositeConversionFactor (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) : ℂ :=
  ∏ i, gaussConversionFactor (P i) (hgood i)
    (ProductGauss.localChar (fun i => O ⧸ P i)
      (ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom) i)

/-- The conversion factor has unit modulus for every primitive additive
character on the composite quotient. -/
theorem norm_compositeConversionFactor (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (hψ : ψ.IsPrimitive) :
    ‖compositeConversionFactor P hinj hgood ψ‖ = 1 := by
  rw [compositeConversionFactor, norm_prod]
  apply Finset.prod_eq_one
  intro i _
  exact norm_gaussConversionFactor (P i) (hgood i) (hchar i) _
    (ProductGauss.localChar_primitive (fun i => O ⧸ P i) _
      (ProductGauss.primitive_comp_ringEquiv _ ψ hψ) i)

/-- Möbius-weighted conjugate sextic Gauss sums become cubic Gauss sums with
an explicit factor of unit modulus. The factor uses only the primary generator,
the sextic value at four, and the quadratic Gauss sum. -/
theorem moebius_star_sexticGauss_eq_cubic (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (hψ : ψ.IsPrimitive) :
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
      star (sexticResidueGauss P hinj hgood 1 ψ) =
    compositeConversionFactor P hinj hgood ψ * sexticResidueGauss P hinj hgood 2 ψ := by
  let η := ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom
  let ψi := ProductGauss.localChar (fun i => O ⧸ P i) η
  have hη : η.IsPrimitive := ProductGauss.primitive_comp_ringEquiv _ ψ hψ
  calc
    _ = ∏ i, -star (gaussSum (complexSexticChar (P i) (hgood i)) (ψi i)) := by
      rw [sexticResidueGauss, residueGauss_factorization, star_prod, Finset.prod_neg,
        Finset.card_univ, primeProduct_moebius P hinj]
      simp only [pow_one, ψi, η]
    _ = ∏ i, gaussConversionFactor (P i) (hgood i) (ψi i) *
        gaussSum (complexCubicChar (P i) (hgood i)) (ψi i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact neg_star_sexticGauss_eq_cubic (P i) (hgood i) (hchar i) _
        (ProductGauss.localChar_primitive (fun i => O ⧸ P i) η hη i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, compositeConversionFactor, sexticResidueGauss,
        residueGauss_factorization]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [(complexSexticChar_powers (P i) (hgood i)).1]

/-- The definite composite character gives the exact coefficient conversion
and its unit-modulus factor with no unspecified finite-character input. -/
theorem canonical_moebius_conversion (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        star (sexticResidueGauss P hinj hgood 1 (canonicalProductAddChar P hinj)) =
      compositeConversionFactor P hinj hgood (canonicalProductAddChar P hinj) *
        sexticResidueGauss P hinj hgood 2 (canonicalProductAddChar P hinj) ∧
    ‖compositeConversionFactor P hinj hgood (canonicalProductAddChar P hinj)‖ = 1 :=
  ⟨moebius_star_sexticGauss_eq_cubic P hinj hgood hchar _
      (canonicalProductAddChar_primitive P hinj),
    norm_compositeConversionFactor P hinj hgood hchar _
      (canonicalProductAddChar_primitive P hinj)⟩

end Composite

end Eisenstein

end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.JacobiQuadratic.jacobi_quadratic
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.JacobiQuadratic.gauss_sextic_relation
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.sextic_cubic_gauss_product
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.sexticResidueGauss_product
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.neg_star_sexticGauss_eq_cubic
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.norm_compositeConversionFactor
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.moebius_star_sexticGauss_eq_cubic
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.canonical_moebius_conversion
