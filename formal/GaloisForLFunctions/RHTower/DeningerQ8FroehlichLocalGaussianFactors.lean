import GaloisForLFunctions.RHTower.DeningerQ8ActualMonomialSourceLaw
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Local Gaussian factors in Fröhlich's Q8 root-number calculation

This file formalizes the two finite Gaussian mechanisms occurring after selecting
`E = ℚ(√41)` in Fröhlich's Section 5--6 calculation for the actual SST quaternion field.

At the split prime `5`, the literal order-four Q8 source character is transported to the
cyclic residue-unit group. Its inverse/conjugate Gauss pair, with inverse additive
orientation, has exact normalized product one. The character is proved to have order four,
so no quadratic replacement is hidden in the construction.

At `41`, the canonical quadratic residue character has Gauss square `41`. A finite
square-fibre expansion reduces its real part to ten explicit cosines. Strict cosine
monotonicity then proves the classical positive orientation, so the Gauss sum is exactly
`√41` and its normalized phase is exactly `1`.

No declaration in this file calls either finite factor a global Artin root number.
-/

namespace RHTower

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

noncomputable def deningerQ8FiveResidueSourceEquiv :
    Multiplicative (ZMod 4) ≃* (ZMod 5)ˣ := by
  letI : IsCyclic (ZMod 5)ˣ := ZMod.isCyclic_units_prime (by norm_num)
  exact mulEquivOfCyclicCardEq (by norm_num [Nat.totient_prime Nat.prime_five])

noncomputable def deningerQ8FiveResidueQuarticChar : MulChar (ZMod 5) ℂ :=
  MulChar.ofUnitHom
    (q8OrderFourCharacter.comp deningerQ8FiveResidueSourceEquiv.symm.toMonoidHom)

theorem deningerQ8FiveResidueQuarticChar_sourceGenerator :
    deningerQ8FiveResidueQuarticChar
        (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5) =
      Complex.I := by
  rw [deningerQ8FiveResidueQuarticChar, MulChar.ofUnitHom_coe]
  change ((q8OrderFourCharacter
    (deningerQ8FiveResidueSourceEquiv.symm
      (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)))) : ℂˣ) : ℂ) = _
  rw [deningerQ8FiveResidueSourceEquiv.symm_apply_apply]
  rw [q8OrderFourCharacter_apply]
  rw [ZMod.val_one'' (by norm_num : 4 ≠ 1), pow_one]

theorem deningerQ8FiveResidueQuarticChar_ne_one :
    deningerQ8FiveResidueQuarticChar ≠ 1 := by
  intro h
  have he := congrArg
    (fun χ : MulChar (ZMod 5) ℂ =>
      χ (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5)) h
  rw [deningerQ8FiveResidueQuarticChar_sourceGenerator] at he
  have him := congrArg Complex.im he
  norm_num at him

theorem deningerQ8FiveResidueQuarticChar_sq_ne_one :
    deningerQ8FiveResidueQuarticChar ^ 2 ≠ 1 := by
  intro h
  have he := congrArg
    (fun χ : MulChar (ZMod 5) ℂ =>
      χ (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5)) h
  rw [deningerQ8FiveResidueQuarticChar.pow_apply_coe, MulChar.one_apply_coe] at he
  rw [deningerQ8FiveResidueQuarticChar_sourceGenerator, Complex.I_sq] at he
  norm_num at he

theorem deningerQ8FiveResidueQuarticChar_fourth_eq_one :
    deningerQ8FiveResidueQuarticChar ^ 4 = 1 := by
  apply MulChar.ext
  intro u
  rw [deningerQ8FiveResidueQuarticChar.pow_apply_coe, MulChar.one_apply_coe]
  rw [deningerQ8FiveResidueQuarticChar, MulChar.ofUnitHom_coe]
  have hu : (deningerQ8FiveResidueSourceEquiv.symm u) ^ 4 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    rw [nsmul_eq_mul]
    rw [ZMod.natCast_self, zero_mul]
  have hmap :
      (q8OrderFourCharacter.comp
          deningerQ8FiveResidueSourceEquiv.symm.toMonoidHom u) ^ 4 = 1 := by
    change q8OrderFourCharacter (deningerQ8FiveResidueSourceEquiv.symm u) ^ 4 = 1
    rw [← map_pow, hu, map_one]
  exact congrArg Units.val hmap

theorem deningerQ8FiveResidueQuarticChar_orderOf_eq_four :
    orderOf deningerQ8FiveResidueQuarticChar = 4 := by
  change orderOf deningerQ8FiveResidueQuarticChar = 2 ^ 2
  apply orderOf_eq_prime_pow
  · simpa using deningerQ8FiveResidueQuarticChar_sq_ne_one
  · simpa using deningerQ8FiveResidueQuarticChar_fourth_eq_one

def deningerQ8FroehlichSplitFiveGaussianPair : ℂ :=
  (5 : ℂ)⁻¹ *
    (gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar *
      gaussSum deningerQ8FiveResidueQuarticChar⁻¹ ZMod.stdAddChar⁻¹)

theorem deningerQ8FiveResidueQuarticGaussProduct_eq_five :
    gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar *
        gaussSum deningerQ8FiveResidueQuarticChar⁻¹ ZMod.stdAddChar⁻¹ = 5 := by
  simpa using gaussSum_mul_gaussSum_eq_card
    deningerQ8FiveResidueQuarticChar_ne_one (ZMod.isPrimitive_stdAddChar 5)

theorem deningerQ8FroehlichSplitFiveGaussianPair_eq_one :
    deningerQ8FroehlichSplitFiveGaussianPair = 1 := by
  rw [deningerQ8FroehlichSplitFiveGaussianPair,
    deningerQ8FiveResidueQuarticGaussProduct_eq_five]
  norm_num

noncomputable def deningerQ8FortyOneQuadraticChar : MulChar (ZMod 41) ℂ :=
  (quadraticChar (ZMod 41)).ringHomComp (Int.castRingHom ℂ)

theorem deningerQ8FortyOneQuadraticChar_ne_one :
    deningerQ8FortyOneQuadraticChar ≠ 1 := by
  rw [deningerQ8FortyOneQuadraticChar]
  apply (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2
  apply quadraticChar_ne_one
  norm_num [ZMod.ringChar_zmod_n]

theorem deningerQ8FortyOneQuadraticChar_neg_one_eq_one :
    deningerQ8FortyOneQuadraticChar (-1) = 1 := by
  rw [deningerQ8FortyOneQuadraticChar, MulChar.ringHomComp_apply]
  have hneg : (-1 : ZMod 41) ≠ 0 := by norm_num
  have hq : quadraticChar (ZMod 41) (-1) = 1 :=
    (quadraticChar_one_iff_isSquare hneg).2 ⟨9, by
      change ((-1 : ℤ) : ZMod 41) = ((81 : ℤ) : ZMod 41)
      rw [ZMod.intCast_eq_intCast_iff']
      norm_num⟩
  rw [hq, map_one]

theorem deningerQ8FortyOneQuadraticGaussSum_sq_eq_fortyOne :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar ^ 2 = 41 := by
  have h := gaussSum_sq deningerQ8FortyOneQuadraticChar_ne_one
    ((quadraticChar_isQuadratic (ZMod 41)).comp (Int.castRingHom ℂ))
    (ZMod.isPrimitive_stdAddChar 41)
  rw [deningerQ8FortyOneQuadraticChar_neg_one_eq_one, one_mul] at h
  simpa using h

theorem deningerQ8FortyOneQuadraticChar_inv_eq_self :
    deningerQ8FortyOneQuadraticChar⁻¹ = deningerQ8FortyOneQuadraticChar := by
  exact ((quadraticChar_isQuadratic (ZMod 41)).comp (Int.castRingHom ℂ)).inv

theorem deningerQ8FortyOneQuadraticGaussSum_invAdd_eq_self :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar⁻¹ =
      gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar := by
  have h := mul_gaussSum_inv_eq_gaussSum
    deningerQ8FortyOneQuadraticChar ZMod.stdAddChar
  rw [deningerQ8FortyOneQuadraticChar_neg_one_eq_one, one_mul] at h
  exact h

theorem deningerQ8FortyOneQuadraticGaussSum_star_eq_self :
    star (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar) =
      gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar := by
  rw [star_gaussSum_eq, deningerQ8FortyOneQuadraticChar_inv_eq_self,
    deningerQ8FortyOneQuadraticGaussSum_invAdd_eq_self]

theorem deningerQ8FortyOneQuadraticGaussSum_im_eq_zero :
    (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).im = 0 := by
  have h := congrArg Complex.im deningerQ8FortyOneQuadraticGaussSum_star_eq_self
  have h' :
      -(gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).im =
        (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).im := by
    simpa only [← starRingEnd_apply, Complex.conj_im] using h
  linarith

theorem deningerQ8FortyOneQuadraticGaussSum_eq_pos_or_neg_sqrt :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar =
        (Real.sqrt 41 : ℂ) ∨
      gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar =
        -(Real.sqrt 41 : ℂ) := by
  let g := gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar
  have hgim : g.im = 0 := deningerQ8FortyOneQuadraticGaussSum_im_eq_zero
  have hg : g = (g.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hgim
  have hsqC : ((g.re : ℂ) ^ 2) = (41 : ℂ) := by
    rw [← hg]
    exact deningerQ8FortyOneQuadraticGaussSum_sq_eq_fortyOne
  have hsqR : g.re ^ 2 = (41 : ℝ) := by
    exact Complex.ofReal_injective (by simpa using hsqC)
  have hsqrt : (Real.sqrt 41) ^ 2 = (41 : ℝ) := by
    rw [sq, Real.mul_self_sqrt]
    norm_num
  have hor : g.re = Real.sqrt 41 ∨ g.re = -Real.sqrt 41 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 (hsqR.trans hsqrt.symm)
  rcases hor with hpos | hneg
  · left
    change g = (Real.sqrt 41 : ℂ)
    exact hg.trans (congrArg Complex.ofReal hpos)
  · right
    change g = -(Real.sqrt 41 : ℂ)
    rw [hg, hneg, Complex.ofReal_neg]

private theorem deningerQ8FortyOneStdAddChar_intCast_re (j : ℤ) :
    (ZMod.stdAddChar (j : ZMod 41)).re = Real.cos (2 * Real.pi * j / 41) := by
  rw [ZMod.stdAddChar_coe]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / ((41 : ℕ) : ℂ) =
        ((2 * Real.pi * j / 41 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

private def deningerQ8FortyOneHalfSquareResidue : Fin 20 → ℤ :=
  ![1, 4, 9, 16, -16, -5, 8, -18, -1, 18,
    -2, -20, 5, -9, 20, 10, 2, -4, -8, -10]

private theorem deningerQ8FortyOneCos_eq_of_modEq (a r : ℤ)
    (h : a ≡ r [ZMOD 41]) :
    Real.cos (2 * Real.pi * a / 41) = Real.cos (2 * Real.pi * r / 41) := by
  obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h
  have ha : a = r - 41 * q := by linarith
  rw [ha]
  have hangle :
      2 * Real.pi * (r - 41 * q : ℤ) / 41 =
        2 * Real.pi * r / 41 - (q : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hangle, Real.cos_sub_int_mul_two_pi]

private theorem deningerQ8FortyOneHalfSquareCos_spec (k : Fin 20) :
    Real.cos (2 * Real.pi * (((k.1 + 1) ^ 2 : ℕ) : ℤ) / 41) =
      Real.cos (2 * Real.pi * deningerQ8FortyOneHalfSquareResidue k / 41) := by
  apply deningerQ8FortyOneCos_eq_of_modEq
  fin_cases k <;>
    norm_num [deningerQ8FortyOneHalfSquareResidue, Int.ModEq]

private theorem deningerQ8FortyOneHalfSquareAddChar_re (k : Fin 20) :
    (ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2))).re =
      Real.cos (2 * Real.pi * deningerQ8FortyOneHalfSquareResidue k / 41) := by
  calc
    (ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2))).re =
        (ZMod.stdAddChar (((((k.1 + 1) ^ 2 : ℕ) : ℤ) : ZMod 41))).re := by
      rw [Int.cast_natCast, Nat.cast_pow]
    _ = Real.cos (2 * Real.pi * (((k.1 + 1) ^ 2 : ℕ) : ℤ) / 41) := by
      exact deningerQ8FortyOneStdAddChar_intCast_re _
    _ = Real.cos (2 * Real.pi * deningerQ8FortyOneHalfSquareResidue k / 41) :=
      deningerQ8FortyOneHalfSquareCos_spec k

private def deningerQ8FortyOnePositiveHalfResidue : Fin 10 → ℤ :=
  ![1, 2, 4, 5, 8, 9, 10, 16, 18, 20]

private theorem deningerQ8FortyOne_sum_halfSquareResidue_cos :
    (∑ k : Fin 20,
        Real.cos (2 * Real.pi * deningerQ8FortyOneHalfSquareResidue k / 41)) =
      2 * ∑ j : Fin 10,
        Real.cos (2 * Real.pi * deningerQ8FortyOnePositiveHalfResidue j / 41) := by
  simp [Fin.sum_univ_succ, deningerQ8FortyOneHalfSquareResidue,
    deningerQ8FortyOnePositiveHalfResidue]
  simp only [neg_div, Real.cos_neg]
  ring

private theorem deningerQ8FortyOneQuadraticGaussSum_eq_squareSum :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar =
      ∑ x : ZMod 41, ZMod.stdAddChar (x ^ 2) := by
  have hchar : ringChar (ZMod 41) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hzero : ∑ a : ZMod 41, ZMod.stdAddChar a = 0 := by
    apply AddChar.sum_eq_zero_of_ne_one
    intro h
    have he := congrArg (fun ψ : AddChar (ZMod 41) ℂ => ψ 1) h
    have hiff := (ZMod.isPrimitive_stdAddChar 41).zmod_char_eq_one_iff 41 1
    have hz : (1 : ZMod 41) = 0 := hiff.mp (by simpa using he)
    norm_num at hz
  rw [gaussSum]
  symm
  calc
    (∑ x : ZMod 41, ZMod.stdAddChar (x ^ 2)) =
        ∑ a : ZMod 41, ∑ x : {x : ZMod 41 // x ^ 2 = a},
          ZMod.stdAddChar (x.1 ^ 2) :=
      (Fintype.sum_fiberwise (fun x : ZMod 41 => x ^ 2)
        (fun x => ZMod.stdAddChar (x ^ 2))).symm
    _ = ∑ a : ZMod 41,
        (({x : ZMod 41 | x ^ 2 = a}.toFinset.card : ℕ) : ℂ) * ZMod.stdAddChar a := by
      apply Fintype.sum_congr
      intro a
      have hpoint : ∀ x : {x : ZMod 41 // x ^ 2 = a},
          ZMod.stdAddChar (x.1 ^ 2) = ZMod.stdAddChar a := fun x => congrArg _ x.2
      simp_rw [hpoint]
      change (Finset.univ.sum (fun _x : {x : ZMod 41 // x ^ 2 = a} =>
        ZMod.stdAddChar a)) = _
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : Fintype.card {x : ZMod 41 // x ^ 2 = a} =
          {x : ZMod 41 | x ^ 2 = a}.toFinset.card :=
        (Set.toFinset_card {x : ZMod 41 | x ^ 2 = a}).symm
      rw [hc]
    _ = ∑ a : ZMod 41,
        ((quadraticChar (ZMod 41) a + 1 : ℤ) : ℂ) * ZMod.stdAddChar a := by
      apply Fintype.sum_congr
      intro a
      congr 1
      exact_mod_cast quadraticChar_card_sqrts hchar a
    _ = (∑ a : ZMod 41,
          ((quadraticChar (ZMod 41) a : ℤ) : ℂ) * ZMod.stdAddChar a) +
        ∑ a : ZMod 41, ZMod.stdAddChar a := by
      simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
    _ = ∑ a : ZMod 41,
          ((quadraticChar (ZMod 41) a : ℤ) : ℂ) * ZMod.stdAddChar a := by
      rw [hzero, add_zero]
    _ = ∑ a : ZMod 41,
          deningerQ8FortyOneQuadraticChar a * ZMod.stdAddChar a := by
      apply Fintype.sum_congr
      intro a
      rw [deningerQ8FortyOneQuadraticChar, MulChar.ringHomComp_apply]
      rfl

private theorem deningerQ8FortyOneSquareSum_pairing :
    (∑ x : ZMod 41, ZMod.stdAddChar (x ^ 2)) =
      1 + 2 * ∑ k : Fin 20,
        ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2)) := by
  calc
    (∑ x : ZMod 41, ZMod.stdAddChar (x ^ 2)) =
        ∑ i : Fin 41, ZMod.stdAddChar ((ZMod.finEquiv 41 i) ^ 2) :=
      ((ZMod.finEquiv 41).sum_comp (fun x : ZMod 41 => ZMod.stdAddChar (x ^ 2))).symm
    _ = 1 + 2 * ∑ k : Fin 20,
        ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2)) := by
      have hfin : ∀ i : Fin 41, ZMod.finEquiv 41 i = (i.1 : ZMod 41) := by
        intro i
        apply ZMod.val_injective
        change i.1 = i.1 % 41
        exact (Nat.mod_eq_of_lt i.2).symm
      rw [Fin.sum_univ_add (a := 21) (b := 20)]
      rw [Fin.sum_univ_succ]
      have hzero :
          ZMod.stdAddChar ((ZMod.finEquiv 41 (Fin.castAdd 20 (0 : Fin 21))) ^ 2) = 1 := by
        simp [hfin]
      rw [hzero]
      have hfirst :
          (∑ i : Fin 20,
              ZMod.stdAddChar ((ZMod.finEquiv 41 (Fin.castAdd 20 i.succ)) ^ 2)) =
            ∑ k : Fin 20, ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2)) := by
        apply Fintype.sum_congr
        intro i
        rw [hfin]
        rfl
      rw [hfirst]
      have hsecond :
          (∑ i : Fin 20,
              ZMod.stdAddChar ((ZMod.finEquiv 41 (Fin.natAdd 21 i)) ^ 2)) =
            ∑ k : Fin 20, ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2)) := by
        calc
          (∑ i : Fin 20,
              ZMod.stdAddChar ((ZMod.finEquiv 41 (Fin.natAdd 21 i)) ^ 2)) =
              ∑ i : Fin 20,
                ZMod.stdAddChar
                  ((ZMod.finEquiv 41 (Fin.natAdd 21 (Fin.rev i))) ^ 2) :=
            (Equiv.sum_comp (Fin.revPerm (n := 20)) (fun i : Fin 20 =>
              ZMod.stdAddChar ((ZMod.finEquiv 41 (Fin.natAdd 21 i)) ^ 2))).symm
          _ = ∑ k : Fin 20,
              ZMod.stdAddChar ((((k.1 + 1 : ℕ) : ZMod 41) ^ 2)) := by
            apply Fintype.sum_congr
            intro i
            rw [hfin]
            have hbase :
                (((Fin.natAdd 21 (Fin.rev i)).1 : ℕ) : ZMod 41) =
                  -(((i.1 + 1 : ℕ) : ZMod 41)) := by
              apply eq_neg_of_add_eq_zero_left
              rw [← Nat.cast_add]
              have hv : (Fin.natAdd 21 (Fin.rev i)).1 + (i.1 + 1) = 41 := by
                simp only [Fin.val_natAdd, Fin.val_rev]
                omega
              rw [hv, ZMod.natCast_self]
            rw [hbase]
            ring
      rw [hsecond]
      ring

private theorem deningerQ8FortyOneQuadraticGaussSum_re_eq_positiveCosinePacket :
    (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).re =
      1 + 4 * ∑ j : Fin 10,
        Real.cos (2 * Real.pi * deningerQ8FortyOnePositiveHalfResidue j / 41) := by
  rw [deningerQ8FortyOneQuadraticGaussSum_eq_squareSum,
    deningerQ8FortyOneSquareSum_pairing]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.re_sum]
  simp_rw [deningerQ8FortyOneHalfSquareAddChar_re]
  rw [deningerQ8FortyOne_sum_halfSquareResidue_cos]
  norm_num
  ring

private theorem deningerQ8FortyOnePositiveCosinePacket :
    0 < 1 + 4 * ∑ j : Fin 10,
      Real.cos (2 * Real.pi * deningerQ8FortyOnePositiveHalfResidue j / 41) := by
  have hpi := Real.pi_pos
  have h1mono : Real.cos (Real.pi / 6) < Real.cos (2 * Real.pi / 41) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · linarith
    · nlinarith
  have hsqrt : (3 / 4 : ℝ) < Real.sqrt 3 / 2 := by
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith
  have h1 : (3 / 4 : ℝ) < Real.cos (2 * Real.pi / 41) := by
    rw [Real.cos_pi_div_six] at h1mono
    linarith
  have h20 : (-1 : ℝ) < Real.cos (2 * Real.pi * 20 / 41) := by
    have hmono : Real.cos Real.pi < Real.cos (2 * Real.pi * 20 / 41) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · positivity
      · exact le_rfl
      · nlinarith
    simpa using hmono
  have h2_18 :
      0 < Real.cos (2 * Real.pi * 2 / 41) +
        Real.cos (2 * Real.pi * 18 / 41) := by
    have hmono : Real.cos (Real.pi * 5 / 41) <
        Real.cos (2 * Real.pi * 2 / 41) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith
      · nlinarith
    have hreflect : Real.cos (2 * Real.pi * 18 / 41) =
        -Real.cos (Real.pi * 5 / 41) := by
      rw [show 2 * Real.pi * 18 / 41 = Real.pi - Real.pi * 5 / 41 by ring,
        Real.cos_pi_sub]
    rw [hreflect]
    linarith
  have h4_16 :
      0 < Real.cos (2 * Real.pi * 4 / 41) +
        Real.cos (2 * Real.pi * 16 / 41) := by
    have hmono : Real.cos (Real.pi * 9 / 41) <
        Real.cos (2 * Real.pi * 4 / 41) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith
      · nlinarith
    have hreflect : Real.cos (2 * Real.pi * 16 / 41) =
        -Real.cos (Real.pi * 9 / 41) := by
      rw [show 2 * Real.pi * 16 / 41 = Real.pi - Real.pi * 9 / 41 by ring,
        Real.cos_pi_sub]
    rw [hreflect]
    linarith
  have h5 : 0 < Real.cos (2 * Real.pi * 5 / 41) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith
  have h8 : 0 < Real.cos (2 * Real.pi * 8 / 41) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith
  have h9 : 0 < Real.cos (2 * Real.pi * 9 / 41) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith
  have h10 : 0 < Real.cos (2 * Real.pi * 10 / 41) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith
  simp [Fin.sum_univ_succ, deningerQ8FortyOnePositiveHalfResidue]
  nlinarith

theorem deningerQ8FortyOneQuadraticGaussSum_re_pos :
    0 < (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).re := by
  rw [deningerQ8FortyOneQuadraticGaussSum_re_eq_positiveCosinePacket]
  exact deningerQ8FortyOnePositiveCosinePacket

theorem deningerQ8FortyOneQuadraticGaussSum_eq_sqrt :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar =
      (Real.sqrt 41 : ℂ) := by
  rcases deningerQ8FortyOneQuadraticGaussSum_eq_pos_or_neg_sqrt with h | h
  · exact h
  · have hre := deningerQ8FortyOneQuadraticGaussSum_re_pos
    rw [h] at hre
    have hsqrt : 0 < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
    norm_num at hre
    linarith

noncomputable def deningerQ8FroehlichFortyOneGaussianPhase : ℂ :=
  (Real.sqrt 41 : ℂ)⁻¹ *
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar

theorem deningerQ8FroehlichFortyOneGaussianPhase_eq_one_or_neg_one :
    deningerQ8FroehlichFortyOneGaussianPhase = 1 ∨
      deningerQ8FroehlichFortyOneGaussianPhase = -1 := by
  rcases deningerQ8FortyOneQuadraticGaussSum_eq_pos_or_neg_sqrt with h | h
  · left
    rw [deningerQ8FroehlichFortyOneGaussianPhase, h]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.2 (by norm_num)))
  · right
    rw [deningerQ8FroehlichFortyOneGaussianPhase, h, mul_neg,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_ne_zero'.2 (by norm_num)))]

theorem deningerQ8FroehlichFortyOneGaussianPhase_eq_one_iff_re_pos :
    deningerQ8FroehlichFortyOneGaussianPhase = 1 ↔
      0 < (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).re := by
  constructor
  · intro hphase
    rcases deningerQ8FortyOneQuadraticGaussSum_eq_pos_or_neg_sqrt with h | h
    · rw [h]
      exact Real.sqrt_pos.2 (by norm_num)
    · exfalso
      have hsqrt : (Real.sqrt 41 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.2 (by norm_num))
      rw [deningerQ8FroehlichFortyOneGaussianPhase, h, mul_neg,
        inv_mul_cancel₀ hsqrt] at hphase
      norm_num at hphase
  · intro hre
    rcases deningerQ8FortyOneQuadraticGaussSum_eq_pos_or_neg_sqrt with h | h
    · rw [deningerQ8FroehlichFortyOneGaussianPhase, h]
      exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_ne_zero'.2 (by norm_num)))
    · rw [h] at hre
      have hsqrt : 0 < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
      norm_num at hre
      linarith

theorem deningerQ8FroehlichFortyOneGaussianPhase_eq_one :
    deningerQ8FroehlichFortyOneGaussianPhase = 1 :=
  deningerQ8FroehlichFortyOneGaussianPhase_eq_one_iff_re_pos.2
    deningerQ8FortyOneQuadraticGaussSum_re_pos

end

end RHTower
