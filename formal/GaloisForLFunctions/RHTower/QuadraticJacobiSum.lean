/-
# Closed quadratic Jacobi sums over certified odd prime fields

This is the finite-field complete-sum layer required before the
Bondarenko--Heap quadratic-character correlation estimates can be formalized.
An odd prime is carried with its finite certificate, so all field and
finiteness structure is constructed inside Lean.  No RH, GRH, exceptional
zero, density estimate, or analytic premise is used.
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators Function

noncomputable section

namespace RHTower

/-- A prime together with a proof that it is odd, packaged as finite arithmetic data. -/
abbrev OddPrime := {p : ℕ // p.Prime ∧ p ≠ 2}

/-- The primality certificate equips the associated residue ring with its finite-field structure. -/
instance (p : OddPrime) : Fact p.1.Prime := ⟨p.2.1⟩

/-- The quadratic character of the certified odd prime field, viewed in complex values. -/
def oddPrimeQuadraticCharacter (p : OddPrime) : MulChar (ZMod p.1) ℂ :=
  (quadraticChar (ZMod p.1)).ringHomComp (Int.castRingHom ℂ)

/-- The complex quadratic character retains its three-value quadratic structure. -/
theorem oddPrimeQuadraticCharacter_isQuadratic (p : OddPrime) :
    (oddPrimeQuadraticCharacter p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p.1)).comp _

/-- The complex quadratic character of an odd prime field is nontrivial. -/
theorem oddPrimeQuadraticCharacter_ne_one (p : OddPrime) :
    oddPrimeQuadraticCharacter p ≠ 1 := by
  have hchar : ringChar (ZMod p.1) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact p.2.2
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    (quadraticChar_ne_one hchar)

/-- At a prime level, the nontrivial quadratic character has conductor equal to the level.  The
proof rules out the only proper positive conductor, namely `1`, using the closed nontriviality
theorem above. -/
theorem oddPrimeQuadraticCharacter_isPrimitive (p : OddPrime) :
    DirichletCharacter.IsPrimitive (oddPrimeQuadraticCharacter p) := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor
      (oddPrimeQuadraticCharacter p : DirichletCharacter ℂ p.1) ∣ p.1 :=
    DirichletCharacter.conductor_dvd_level
      (oddPrimeQuadraticCharacter p : DirichletCharacter ℂ p.1)
  rcases (Nat.dvd_prime p.2.1).mp hdiv with h | h
  · exact (oddPrimeQuadraticCharacter_ne_one p
      ((DirichletCharacter.eq_one_iff_conductor_eq_one
        (χ := (oddPrimeQuadraticCharacter p : DirichletCharacter ℂ p.1))).mpr h)).elim
  · exact h

/-- Exact additive Fourier transform of the quadratic character at every certified odd prime.
This is the primitive-conductor Gauss identity with the negative additive phase used by the source
correlation sums. -/
theorem oddPrime_quadratic_additiveFourier
    (p : OddPrime) (b : ZMod p.1) :
    ∑ a : ZMod p.1,
      oddPrimeQuadraticCharacter p a * ZMod.stdAddChar (-(b * a)) =
      (oddPrimeQuadraticCharacter p)⁻¹ (-b) *
        gaussSum (oddPrimeQuadraticCharacter p) (ZMod.stdAddChar (N := p.1)) := by
  calc
    _ = gaussSum (oddPrimeQuadraticCharacter p)
        ((ZMod.stdAddChar (N := p.1)).mulShift (-b)) := by
      rw [gaussSum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [AddChar.mulShift_apply]
      congr 2
      ring
    _ = _ := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := p.1))
      (oddPrimeQuadraticCharacter_isPrimitive p) (-b)

/-- Complete cancellation of the complex quadratic character over every certified odd prime field. -/
theorem oddPrimeQuadraticCharacter_sum_zero (p : OddPrime) :
    ∑ a : ZMod p.1, oddPrimeQuadraticCharacter p a = 0 := by
  have hchar : ringChar (ZMod p.1) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact p.2.2
  change ∑ a : ZMod p.1, Int.castRingHom ℂ (quadraticChar (ZMod p.1) a) = 0
  rw [← map_sum, quadraticChar_sum_zero hchar, map_zero]

/-- The exact quadratic Jacobi complete sum `J(χ, χ) = -χ(-1)` over every certified odd
prime field.  The proof first proves `χ⁻¹ = χ` and then discharges the standard inverse-pair
Jacobi identity. -/
theorem oddPrime_quadratic_jacobiSum (p : OddPrime) :
    jacobiSum (oddPrimeQuadraticCharacter p) (oddPrimeQuadraticCharacter p) =
      -oddPrimeQuadraticCharacter p (-1) := by
  have hinv : (oddPrimeQuadraticCharacter p)⁻¹ = oddPrimeQuadraticCharacter p :=
    (oddPrimeQuadraticCharacter_isQuadratic p).inv
  calc
    jacobiSum (oddPrimeQuadraticCharacter p) (oddPrimeQuadraticCharacter p) =
        jacobiSum (oddPrimeQuadraticCharacter p) (oddPrimeQuadraticCharacter p)⁻¹ := by
          rw [hinv]
    _ = -oddPrimeQuadraticCharacter p (-1) :=
      jacobiSum_nontrivial_inv (oddPrimeQuadraticCharacter_ne_one p)

/-- At every nonzero field element, the quadratic character squares to one. -/
theorem oddPrimeQuadraticCharacter_square_at_nonzero
    (p : OddPrime) {a : ZMod p.1} (ha : a ≠ 0) :
    oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p a = 1 := by
  let u : (ZMod p.1)ˣ := Units.mk0 a ha
  have h := congrArg (fun ψ : MulChar (ZMod p.1) ℂ => ψ (u : ZMod p.1))
    (oddPrimeQuadraticCharacter_isQuadratic p).sq_eq_one
  rw [MulChar.pow_apply_coe] at h
  have hu : (u : ZMod p.1) = a := rfl
  have haunit : IsUnit a := isUnit_iff_ne_zero.mpr ha
  rw [hu, MulChar.one_apply haunit] at h
  simpa only [pow_two] using h

/-- The standard quadratic Gauss sum has exact squared modulus `p` over every certified odd
prime field.  This is the closed complete-sum input for nonzero additive frequencies: no
unproved character-sum estimate is imported. -/
theorem oddPrime_quadratic_gaussNormSq (p : OddPrime) :
    gaussSum (oddPrimeQuadraticCharacter p) (ZMod.stdAddChar (N := p.1)) *
        star (gaussSum (oddPrimeQuadraticCharacter p) (ZMod.stdAddChar (N := p.1))) =
      (p.1 : ℂ) := by
  have h := gaussSum_mul_gaussSum_eq_card (oddPrimeQuadraticCharacter_ne_one p)
    (ZMod.isPrimitive_stdAddChar p.1)
  rw [← star_gaussSum_eq] at h
  simpa using h

/-- Exact squared norm of every additive Fourier coefficient of the quadratic character: it is
zero at frequency zero and exactly `p` at every nonzero frequency. -/
theorem oddPrime_quadratic_additiveFourier_norm
    (p : OddPrime) (b : ZMod p.1) :
    (∑ a : ZMod p.1,
      oddPrimeQuadraticCharacter p a * ZMod.stdAddChar (-(b * a))) *
      star (∑ a : ZMod p.1,
        oddPrimeQuadraticCharacter p a * ZMod.stdAddChar (-(b * a))) =
      if b = 0 then 0 else (p.1 : ℂ) := by
  by_cases hb : b = 0
  · subst b
    simp only [if_pos, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    rw [oddPrimeQuadraticCharacter_sum_zero]
    simp
  · simp only [if_neg hb]
    rw [oddPrime_quadratic_additiveFourier, star_mul]
    have hval : (oddPrimeQuadraticCharacter p)⁻¹ (-b) *
        star ((oddPrimeQuadraticCharacter p)⁻¹ (-b)) = 1 := by
      rw [(oddPrimeQuadraticCharacter_isQuadratic p).inv]
      rw [MulChar.star_apply', (oddPrimeQuadraticCharacter_isQuadratic p).inv]
      exact oddPrimeQuadraticCharacter_square_at_nonzero p (neg_ne_zero.mpr hb)
    calc
      _ = ((oddPrimeQuadraticCharacter p)⁻¹ (-b) *
          star ((oddPrimeQuadraticCharacter p)⁻¹ (-b))) *
          (gaussSum (oddPrimeQuadraticCharacter p) (ZMod.stdAddChar (N := p.1)) *
            star (gaussSum (oddPrimeQuadraticCharacter p) (ZMod.stdAddChar (N := p.1)))) := by
              ring
      _ = _ := by rw [hval, oddPrime_quadratic_gaussNormSq]; ring

/-- The complete additive correlation underlying the nonzero-frequency local factor in
Bondarenko--Heap Lemma 4. -/
def oddPrimeQuadraticAdditiveCorrelation
    (p : OddPrime) (k r b : ZMod p.1) : ℂ :=
  ∑ a : ZMod p.1,
    oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r) *
      ZMod.stdAddChar (-(b * a))

/-- Exact finite-field Parseval for the standard additive character at every certified odd
prime.  It is the frequency-averaged square-root scale identity needed before one can isolate
individual nonzero frequencies. -/
theorem oddPrime_standardAdditive_parseval (p : OddPrime) (f : ZMod p.1 → ℂ) :
    ∑ b : ZMod p.1,
      (∑ a : ZMod p.1, f a * ZMod.stdAddChar (-(b * a))) *
        star (∑ a : ZMod p.1, f a * ZMod.stdAddChar (-(b * a))) =
      (p.1 : ℂ) * ∑ a : ZMod p.1, f a * star (f a) := by
  classical
  have hcharpos : 0 < ringChar (ZMod p.1) := by
    rw [ZMod.ringChar_zmod_n]
    exact p.2.1.pos
  simp_rw [star_sum, Finset.sum_mul_sum]
  simp_rw [star_mul]
  simp_rw [← starRingEnd_apply, AddChar.starComp_apply hcharpos]
  simp_rw [AddChar.inv_apply]
  simp only [neg_neg]
  have hreorder (x y z : ZMod p.1) :
      f y * ZMod.stdAddChar (-(x * y)) *
          (ZMod.stdAddChar (x * z) * (starRingEnd ℂ) (f z)) =
        f y * (starRingEnd ℂ) (f z) * ZMod.stdAddChar (x * (z - y)) := by
    calc
      _ = f y * (starRingEnd ℂ) (f z) *
          (ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (x * z)) := by ring
      _ = f y * (starRingEnd ℂ) (f z) *
          ZMod.stdAddChar (-(x * y) + x * z) := by
            rw [← ZMod.stdAddChar.map_add_eq_mul]
      _ = _ := by
        congr 1
        ring_nf
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum (t : ZMod p.1) :
      ∑ x : ZMod p.1, ZMod.stdAddChar (x * t) =
        if t = 0 then (p.1 : ℂ) else 0 := by
    simpa using AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p.1)) t
      (ZMod.isPrimitive_stdAddChar p.1)
  simp_rw [hsum]
  simp_rw [sub_eq_zero]
  simp only [apply_ite, mul_zero]
  simp
  rw [← Finset.sum_mul]
  ring

/-- Pointwise squared modulus of the prime-field quadratic character. -/
theorem oddPrime_quadratic_valueNorm (p : OddPrime) (a : ZMod p.1) :
    oddPrimeQuadraticCharacter p a * star (oddPrimeQuadraticCharacter p a) =
      if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · subst a
    simp only [MulChar.map_zero, zero_mul, star_zero]
    simp
  · simp only [MulChar.star_apply', (oddPrimeQuadraticCharacter_isQuadratic p).inv]
    rw [oddPrimeQuadraticCharacter_square_at_nonzero p ha, if_neg ha]

/-- Pointwise squared modulus of the quadratic polynomial character in the complete additive
correlation. -/
theorem oddPrime_quadratic_productValueNorm
    (p : OddPrime) (k r a : ZMod p.1) :
    (oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r)) *
        star (oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r)) =
      if a = 0 ∨ k * a + r = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · subst a
    simp only [MulChar.map_zero, zero_mul, star_zero]
    simp
  by_cases hka : k * a + r = 0
  · simp only [hka, MulChar.map_zero, mul_zero, star_zero]
    simp [ha]
  · rw [star_mul]
    calc
      _ = (oddPrimeQuadraticCharacter p a * star (oddPrimeQuadraticCharacter p a)) *
          (oddPrimeQuadraticCharacter p (k * a + r) *
            star (oddPrimeQuadraticCharacter p (k * a + r))) := by ring
      _ = 1 := by
        rw [oddPrime_quadratic_valueNorm p a,
          oddPrime_quadratic_valueNorm p (k * a + r), if_neg ha, if_neg hka]
        norm_num
      _ = _ := by simp [ha, hka]

/-- The complement of zero in a certified odd prime field has exactly `p - 1` elements. -/
private theorem oddPrime_count_notZero (p : OddPrime) :
    (∑ a : ZMod p.1, if a = 0 then (0 : ℂ) else 1) = (p.1 : ℂ) - 1 := by
  classical
  let g : ZMod p.1 → ℂ := fun a => if a = 0 then 0 else 1
  have hsplit := Finset.sum_erase_add Finset.univ g (Finset.mem_univ (0 : ZMod p.1))
  change (∑ a : ZMod p.1, g a) = _
  calc
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod p.1), g a) + g 0 := hsplit.symm
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod p.1), (1 : ℂ)) + 0 := by
      rw [show g 0 = 0 by simp [g]]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      simp only [g]
      exact if_neg (Finset.mem_erase.mp ha).1
    _ = _ := by
      simp [Finset.card_erase_of_mem]
      norm_num [Nat.cast_sub p.2.1.one_le]

/-- Removing two distinct residues from a certified odd prime field leaves exactly `p - 2`
elements. -/
private theorem oddPrime_count_avoidTwo (p : OddPrime) (b : ZMod p.1) (hb : b ≠ 0) :
    (∑ a : ZMod p.1, if a = 0 ∨ a = b then (0 : ℂ) else 1) = (p.1 : ℂ) - 2 := by
  classical
  let g : ZMod p.1 → ℂ := fun a => if a = 0 ∨ a = b then 0 else 1
  have hbmem : b ∈ Finset.univ.erase (0 : ZMod p.1) :=
    Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩
  have hsplit0 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ (0 : ZMod p.1))
  have hsplitb := Finset.sum_erase_add (Finset.univ.erase (0 : ZMod p.1)) g hbmem
  change (∑ a : ZMod p.1, g a) = _
  calc
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod p.1), g a) + g 0 := hsplit0.symm
    _ = ((∑ a ∈ (Finset.univ.erase (0 : ZMod p.1)).erase b, g a) + g b) + 0 := by
      rw [show g 0 = 0 by simp [g]]
      rw [← hsplitb]
    _ = (∑ a ∈ (Finset.univ.erase (0 : ZMod p.1)).erase b, (1 : ℂ)) := by
      rw [show g b = 0 by simp [g]]
      simp only [add_zero]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [g]
      apply if_neg
      rintro (ha0 | hab)
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1 ha0
      · exact (Finset.mem_erase.mp ha).1 hab
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.card_erase_of_mem hbmem, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card]
      have hp1 : 1 ≤ p.1 - 1 :=
        (Nat.le_sub_iff_add_le p.2.1.one_le).mpr p.2.1.two_le
      rw [Nat.cast_sub hp1, Nat.cast_sub p.2.1.one_le]
      ring

/-- Exact count of residues at which the quadratic character factor in the additive correlation
is nonzero, including every degenerate case. -/
theorem oddPrime_quadratic_productRootCount (p : OddPrime) (k r : ZMod p.1) :
    (∑ a : ZMod p.1, if a = 0 ∨ k * a + r = 0 then (0 : ℂ) else 1) =
      if k = 0 then if r = 0 then 0 else (p.1 : ℂ) - 1
      else if r = 0 then (p.1 : ℂ) - 1 else (p.1 : ℂ) - 2 := by
  classical
  by_cases hk : k = 0
  · subst k
    by_cases hr : r = 0
    · simp [hr]
    · simp only [if_neg hr, zero_mul]
      simpa [hr] using oddPrime_count_notZero p
  · by_cases hr : r = 0
    · subst r
      have hmul (a : ZMod p.1) : k * a = 0 ↔ a = 0 := by
        rw [mul_eq_zero]
        simp [hk]
      rw [if_neg hk]
      simp only [if_pos, add_zero]
      simpa only [hmul, or_self] using oddPrime_count_notZero p
    · have hroot (a : ZMod p.1) : k * a + r = 0 ↔ a = -r / k := by
        constructor
        · intro h
          apply (eq_div_iff hk).2
          rw [mul_comm]
          exact eq_neg_of_add_eq_zero_left h
        · intro h
          apply eq_neg_iff_add_eq_zero.mp
          calc
            k * a = a * k := mul_comm _ _
            _ = -r := (eq_div_iff hk).1 h
      have hrootne : -r / k ≠ 0 := div_ne_zero (neg_ne_zero.mpr hr) hk
      simp only [if_neg hk, if_neg hr]
      simp_rw [hroot]
      exact oddPrime_count_avoidTwo p (-r / k) hrootne

/-- Exact total energy of the additive-frequency quadratic correlations.  The right side
records the two possible roots of the quadratic factor without assuming their distinctness. -/
theorem oddPrime_quadratic_additiveCorrelation_parseval
    (p : OddPrime) (k r : ZMod p.1) :
    ∑ b : ZMod p.1,
      oddPrimeQuadraticAdditiveCorrelation p k r b *
        star (oddPrimeQuadraticAdditiveCorrelation p k r b) =
      (p.1 : ℂ) * ∑ a : ZMod p.1,
        if a = 0 ∨ k * a + r = 0 then 0 else 1 := by
  simp only [oddPrimeQuadraticAdditiveCorrelation]
  calc
    _ = (p.1 : ℂ) * ∑ a : ZMod p.1,
        (oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r)) *
          star (oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r)) :=
      oddPrime_standardAdditive_parseval p _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      exact oddPrime_quadratic_productValueNorm p k r a

/-- Fully evaluated all-frequency energy for the local quadratic additive correlation.  This
is a closed finite-field statement for every `k` and `r`, with the degenerate root collisions
accounted for explicitly. -/
theorem oddPrime_quadratic_additiveCorrelation_energy
    (p : OddPrime) (k r : ZMod p.1) :
    ∑ b : ZMod p.1,
      oddPrimeQuadraticAdditiveCorrelation p k r b *
        star (oddPrimeQuadraticAdditiveCorrelation p k r b) =
      (p.1 : ℂ) *
        (if k = 0 then if r = 0 then 0 else (p.1 : ℂ) - 1
        else if r = 0 then (p.1 : ℂ) - 1 else (p.1 : ℂ) - 2) := by
  rw [oddPrime_quadratic_additiveCorrelation_parseval,
    oddPrime_quadratic_productRootCount]

/-- Exact local shifted quadratic correlation over a certified odd prime field.  This is the
prime-field calculation used in the source proof of Bondarenko--Heap Lemma 8: the diagonal has
size `p - 1`, while every unequal shift has complete cancellation to `-1`. -/
theorem oddPrime_quadratic_shiftCorrelation
    (p : OddPrime) (k l : ZMod p.1) :
    ∑ x : ZMod p.1,
      oddPrimeQuadraticCharacter p (x + k) * oddPrimeQuadraticCharacter p (x + l) =
        if k = l then (p.1 : ℂ) - 1 else -1 := by
  classical
  let χ : MulChar (ZMod p.1) ℂ := oddPrimeQuadraticCharacter p
  have hχquad : χ.IsQuadratic := oddPrimeQuadraticCharacter_isQuadratic p
  have hdiag : ∀ k : ZMod p.1, ∑ x : ZMod p.1, χ (x + k) * χ (x + k) = (p.1 : ℂ) - 1 := by
    intro k
    calc
      ∑ x : ZMod p.1, χ (x + k) * χ (x + k) = ∑ x : ZMod p.1, χ x * χ x := by
        simpa only [Equiv.coe_addRight] using
          (Equiv.sum_comp (Equiv.addRight k) (fun x : ZMod p.1 => χ x * χ x))
      _ = ∑ x : ZMod p.1, (χ ^ 2) x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [pow_two, MulChar.mul_apply]
      _ = ∑ x : ZMod p.1, (1 : MulChar (ZMod p.1) ℂ) x := by rw [hχquad.sq_eq_one]
      _ = (Fintype.card (ZMod p.1)ˣ : ℂ) := MulChar.sum_one_eq_card_units
      _ = (p.1 : ℂ) - 1 := by
        rw [ZMod.card_units, Nat.cast_sub p.2.1.one_le]
        norm_num
  by_cases hkl : k = l
  · subst l
    simpa using hdiag k
  · simp only [if_neg hkl]
    let d : ZMod p.1 := k - l
    have hd : d ≠ 0 := by
      intro hd
      apply hkl
      dsimp [d] at hd
      exact sub_eq_zero.mp hd
    have hdsq : χ d * χ d = 1 := oddPrimeQuadraticCharacter_square_at_nonzero p hd
    have hshift :
        (∑ x : ZMod p.1, χ (x + k) * χ (x + l)) =
          ∑ y : ZMod p.1, χ (y + d) * χ y := by
      calc
        (∑ x : ZMod p.1, χ (x + k) * χ (x + l)) =
            ∑ y : ZMod p.1, χ ((y - l) + k) * χ ((y - l) + l) := by
              simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
                (Equiv.sum_comp (Equiv.addRight (-l))
                  (fun x : ZMod p.1 => χ (x + k) * χ (x + l))).symm
        _ = ∑ y : ZMod p.1, χ (y + d) * χ y := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [d]
          congr 2 <;> ring
    have hscale : (∑ y : ZMod p.1, χ (y + d) * χ y) =
        ∑ z : ZMod p.1, χ (z + 1) * χ z := by
      calc
        (∑ y : ZMod p.1, χ (y + d) * χ y) =
            ∑ z : ZMod p.1, χ ((d * z) + d) * χ (d * z) := by
              exact (Equiv.sum_comp (Equiv.mulLeft₀ d hd)
                (fun y : ZMod p.1 => χ (y + d) * χ y)).symm
        _ = ∑ z : ZMod p.1, χ (z + 1) * χ z := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [show d * z + d = d * (z + 1) by ring, map_mul, map_mul]
          calc
            (χ d * χ (z + 1)) * (χ d * χ z) =
                (χ d * χ d) * (χ (z + 1) * χ z) := by ring
            _ = χ (z + 1) * χ z := by rw [hdsq, one_mul]
    have hepssq : χ (-1) * χ (-1) = 1 :=
      oddPrimeQuadraticCharacter_square_at_nonzero p (neg_ne_zero.mpr one_ne_zero)
    have hJfactor : jacobiSum χ χ = χ (-1) * ∑ z : ZMod p.1, χ (z + 1) * χ z := by
      calc
        jacobiSum χ χ = ∑ x : ZMod p.1, χ x * χ (1 - x) := rfl
        _ = ∑ z : ZMod p.1, χ (-z) * χ (1 - (-z)) := by
          simpa only [Equiv.subLeft_apply, zero_sub] using
            (Equiv.sum_comp (Equiv.subLeft (0 : ZMod p.1))
              (fun x : ZMod p.1 => χ x * χ (1 - x))).symm
        _ = χ (-1) * ∑ z : ZMod p.1, χ (z + 1) * χ z := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          rw [show -z = (-1 : ZMod p.1) * z by ring, map_mul]
          rw [show (1 : ZMod p.1) - (-1) * z = z + 1 by ring]
          ac_rfl
    have hJ : jacobiSum χ χ = -χ (-1) := by
      exact oddPrime_quadratic_jacobiSum p
    have hbase : (∑ z : ZMod p.1, χ (z + 1) * χ z) = -1 := by
      calc
        ∑ z : ZMod p.1, χ (z + 1) * χ z =
            (χ (-1) * χ (-1)) * ∑ z : ZMod p.1, χ (z + 1) * χ z := by
              rw [hepssq, one_mul]
        _ = χ (-1) * (χ (-1) * ∑ z : ZMod p.1, χ (z + 1) * χ z) := by ring
        _ = χ (-1) * jacobiSum χ χ := by rw [← hJfactor]
        _ = χ (-1) * (-χ (-1)) := by rw [hJ]
        _ = -1 := by rw [show χ (-1) * (-χ (-1)) = -(χ (-1) * χ (-1)) by ring, hepssq]
    rw [show oddPrimeQuadraticCharacter p = χ by rfl]
    rw [hshift, hscale, hbase]

/-- The complete prime-field quadratic shift operator.  This is the exact finite residue-field
operator that occurs after expanding the square in the local part of Bondarenko--Heap Lemma 8. -/
def oddPrimeQuadraticShiftSum
    (p : OddPrime) (a : ZMod p.1 → ℂ) (x : ZMod p.1) : ℂ :=
  ∑ k : ZMod p.1, a k * oddPrimeQuadraticCharacter p (x + k)

/-- Exact energy identity for the complete prime-field quadratic shift operator.  It is an
unconditional finite calculation: the negative term is the squared modulus of the coefficient
sum, so dropping it later gives the prime-level full-residue `L²` upper bound. -/
theorem oddPrime_quadratic_shiftSum_energy
    (p : OddPrime) (a : ZMod p.1 → ℂ) :
    ∑ x : ZMod p.1, oddPrimeQuadraticShiftSum p a x *
      star (oddPrimeQuadraticShiftSum p a x) =
      (p.1 : ℂ) * ∑ k : ZMod p.1, a k * star (a k) -
        (∑ k : ZMod p.1, a k) * star (∑ k : ZMod p.1, a k) := by
  classical
  have hproduct :
      (∑ k : ZMod p.1, a k) * star (∑ k : ZMod p.1, a k) =
        ∑ k : ZMod p.1, ∑ l : ZMod p.1, a k * star (a l) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  rw [hproduct]
  simp only [oddPrimeQuadraticShiftSum]
  simp_rw [star_sum, Finset.sum_mul_sum, star_mul]
  simp_rw [MulChar.star_apply']
  simp_rw [(oddPrimeQuadraticCharacter_isQuadratic p).inv]
  have hreorder (x k l : ZMod p.1) :
      a k * oddPrimeQuadraticCharacter p (x + k) *
          (oddPrimeQuadraticCharacter p (x + l) * star (a l)) =
        (a k * star (a l)) *
          (oddPrimeQuadraticCharacter p (x + k) *
            oddPrimeQuadraticCharacter p (x + l)) := by
      ring
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, oddPrime_quadratic_shiftCorrelation]
  have hfactor (k l : ZMod p.1) :
      a k * star (a l) * (if k = l then (p.1 : ℂ) - 1 else -1) =
        (a k * star (a l) * (if k = l then (p.1 : ℂ) else 0)) -
          a k * star (a l) := by
    split_ifs <;> ring
  simp_rw [hfactor, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero]
  simp
  have hdouble :
      (∑ k : ZMod p.1, ∑ l : ZMod p.1,
        a k * (starRingEnd ℂ) (a l)) =
        ∑ k : ZMod p.1, a k * ∑ l : ZMod p.1,
          (starRingEnd ℂ) (a l) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  rw [hdouble]
  have hcross :
      (∑ k : ZMod p.1, a k * ∑ l : ZMod p.1,
        (starRingEnd ℂ) (a l)) =
        ∑ k : ZMod p.1, (∑ l : ZMod p.1,
          (starRingEnd ℂ) (a l)) * a k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  rw [hcross]
  have hdiagFactor :
      (∑ x : ZMod p.1, a x * (starRingEnd ℂ) (a x) * (p.1 : ℂ)) =
        (p.1 : ℂ) * ∑ x : ZMod p.1, a x * (starRingEnd ℂ) (a x) := by
    calc
      _ = ∑ x : ZMod p.1, (p.1 : ℂ) *
          (a x * (starRingEnd ℂ) (a x)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ac_rfl
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hdiagFactor]

/-- Closed prime-level full-residue `L²` upper bound for quadratic character shifts.  This is the
positive consequence of the exact energy formula; it has no incomplete character-sum or analytic
input.  It is intentionally not labelled as Bondarenko--Heap Lemma 8, whose interval and
composite-modulus estimate remains a larger theorem. -/
theorem oddPrime_quadratic_shiftSum_normSq_le
    (p : OddPrime) (a : ZMod p.1 → ℂ) :
    ∑ x : ZMod p.1, Complex.normSq (oddPrimeQuadraticShiftSum p a x) ≤
      p.1 * ∑ k : ZMod p.1, Complex.normSq (a k) := by
  have henergy := oddPrime_quadratic_shiftSum_energy p a
  have henergyComplex :
      (∑ x : ZMod p.1, (Complex.normSq (oddPrimeQuadraticShiftSum p a x) : ℂ)) =
        (p.1 : ℂ) * ∑ k : ZMod p.1, (Complex.normSq (a k) : ℂ) -
          (Complex.normSq (∑ k : ZMod p.1, a k) : ℂ) := by
    calc
      _ = ∑ x : ZMod p.1, oddPrimeQuadraticShiftSum p a x *
          star (oddPrimeQuadraticShiftSum p a x) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact (Complex.mul_conj _).symm
      _ = _ := by
        rw [henergy]
        congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact Complex.mul_conj _
        · exact Complex.mul_conj _
  have henergyReal :
      (∑ x : ZMod p.1, Complex.normSq (oddPrimeQuadraticShiftSum p a x)) =
        (p.1 : ℝ) * ∑ k : ZMod p.1, Complex.normSq (a k) -
          Complex.normSq (∑ k : ZMod p.1, a k) := by
    apply Complex.ofReal_injective
    push_cast
    exact henergyComplex
  rw [henergyReal]
  linarith [Complex.normSq_nonneg (∑ k : ZMod p.1, a k)]

/-- Exact zero-frequency linear quadratic complete correlation over a certified odd prime field.
This is the prime-field local factor used in the source proof of Bondarenko--Heap Lemma 4. -/
theorem oddPrime_quadratic_linearCorrelation
    (p : OddPrime) (k r : ZMod p.1) :
    ∑ a : ZMod p.1,
      oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r) =
      if k = 0 then 0 else if r = 0 then
        oddPrimeQuadraticCharacter p k * ((p.1 : ℂ) - 1) else -oddPrimeQuadraticCharacter p k := by
  classical
  let χ : MulChar (ZMod p.1) ℂ := oddPrimeQuadraticCharacter p
  by_cases hk : k = 0
  · subst k
    simp only [zero_mul, if_true]
    rw [← Finset.sum_mul, oddPrimeQuadraticCharacter_sum_zero, zero_mul]
  · simp only [if_neg hk]
    have hksq : χ k * χ k = 1 := oddPrimeQuadraticCharacter_square_at_nonzero p hk
    have hkinv : χ k⁻¹ = χ k := by
      have hmul : χ k⁻¹ * χ k = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hk, map_one]
      calc
        χ k⁻¹ = χ k⁻¹ * 1 := by ring
        _ = χ k⁻¹ * (χ k * χ k) := by rw [hksq]
        _ = (χ k⁻¹ * χ k) * χ k := by ring
        _ = χ k := by rw [hmul, one_mul]
    have htransform :
        (∑ a : ZMod p.1, χ a * χ (k * a + r)) =
          χ k * ∑ x : ZMod p.1, χ x * χ (x + r) := by
      calc
        (∑ a : ZMod p.1, χ a * χ (k * a + r)) =
            ∑ a : ZMod p.1, (χ k⁻¹ * χ (k * a)) * χ (k * a + r) := by
              apply Finset.sum_congr rfl
              intro a ha
              have hfirst : χ k⁻¹ * χ (k * a) = χ a := by
                rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
              rw [hfirst]
        _ = ∑ a : ZMod p.1, χ k * (χ (k * a) * χ (k * a + r)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [hkinv]
              ring
        _ = ∑ x : ZMod p.1, χ k * (χ x * χ (x + r)) := by
              exact Equiv.sum_comp (Equiv.mulLeft₀ k hk)
                (fun x : ZMod p.1 => χ k * (χ x * χ (x + r)))
        _ = χ k * ∑ x : ZMod p.1, χ x * χ (x + r) := by
              rw [Finset.mul_sum]
    by_cases hr : r = 0
    · subst r
      simp only [if_true]
      rw [show oddPrimeQuadraticCharacter p = χ by rfl, htransform]
      have hshift : (∑ x : ZMod p.1, χ x * χ (x + 0)) = (p.1 : ℂ) - 1 := by
        simpa [χ] using
          oddPrime_quadratic_shiftCorrelation p (0 : ZMod p.1) (0 : ZMod p.1)
      rw [hshift]
    · simp only [if_neg hr]
      rw [show oddPrimeQuadraticCharacter p = χ by rfl, htransform]
      have h0r : (0 : ZMod p.1) ≠ r := Ne.symm hr
      have hshift : (∑ x : ZMod p.1, χ x * χ (x + r)) = -1 := by
        simpa [χ, h0r] using oddPrime_quadratic_shiftCorrelation p (0 : ZMod p.1) r
      rw [hshift]
      ring

/-- Product quadratic character on a pair of certified odd prime fields. -/
def oddPrimePairQuadraticCharacter (p q : OddPrime) (x : ZMod p.1 × ZMod q.1) : ℂ :=
  oddPrimeQuadraticCharacter p x.1 * oddPrimeQuadraticCharacter q x.2

/-- Exact shifted quadratic correlation on two prime-field factors.  It is the literal product
of the prime-field local factors and is the finite CRT-product layer used before transferring to
square-free residue rings. -/
theorem oddPrimePair_quadratic_shiftCorrelation
    (p q : OddPrime) (k l : ZMod p.1 × ZMod q.1) :
    ∑ x : ZMod p.1 × ZMod q.1,
      oddPrimePairQuadraticCharacter p q (x + k) *
        oddPrimePairQuadraticCharacter p q (x + l) =
      (if k.1 = l.1 then (p.1 : ℂ) - 1 else -1) *
        (if k.2 = l.2 then (q.1 : ℂ) - 1 else -1) := by
  let fp : ZMod p.1 → ℂ := fun a =>
    oddPrimeQuadraticCharacter p (a + k.1) * oddPrimeQuadraticCharacter p (a + l.1)
  let fq : ZMod q.1 → ℂ := fun b =>
    oddPrimeQuadraticCharacter q (b + k.2) * oddPrimeQuadraticCharacter q (b + l.2)
  calc
    _ = ∑ a : ZMod p.1, ∑ b : ZMod q.1, fp a * fq b := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp [oddPrimePairQuadraticCharacter, fp, fq]
      ring
    _ = (∑ a : ZMod p.1, fp a) * (∑ b : ZMod q.1, fq b) := by
      calc
        _ = ∑ a : ZMod p.1, fp a * ∑ b : ZMod q.1, fq b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = _ := (Finset.sum_mul _ _ _).symm
    _ = _ := by
      rw [show (∑ a : ZMod p.1, fp a) =
        (if k.1 = l.1 then (p.1 : ℂ) - 1 else -1) by
          exact oddPrime_quadratic_shiftCorrelation p k.1 l.1]
      rw [show (∑ b : ZMod q.1, fq b) =
        (if k.2 = l.2 then (q.1 : ℂ) - 1 else -1) by
          exact oddPrime_quadratic_shiftCorrelation q k.2 l.2]

/-- Product quadratic character on a finite family of certified odd prime fields. -/
def oddPrimeFamilyQuadraticCharacter {I : Type*} [Fintype I]
    (p : I → OddPrime) (x : ∀ i, ZMod (p i).1) : ℂ :=
  ∏ i, oddPrimeQuadraticCharacter (p i) (x i)

/-- Exact shifted quadratic correlation over an arbitrary finite product of odd prime fields.
This is the complete finite local-factor product needed for the CRT portion of the source
Lemma 8 argument. -/
theorem oddPrimeFamily_quadratic_shiftCorrelation
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → OddPrime) (k l : ∀ i, ZMod (p i).1) :
    ∑ x : ∀ i, ZMod (p i).1,
      oddPrimeFamilyQuadraticCharacter p (x + k) *
        oddPrimeFamilyQuadraticCharacter p (x + l) =
      ∏ i, if k i = l i then ((p i).1 : ℂ) - 1 else -1 := by
  classical
  let f : ∀ i, ZMod (p i).1 → ℂ := fun i a =>
    oddPrimeQuadraticCharacter (p i) (a + k i) *
      oddPrimeQuadraticCharacter (p i) (a + l i)
  calc
    _ = ∑ x : ∀ i, ZMod (p i).1, ∏ i, f i (x i) := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [oddPrimeFamilyQuadraticCharacter, f]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a : ZMod (p i).1, f i a := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun i => Finset.univ) f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact oddPrime_quadratic_shiftCorrelation (p i) (k i) (l i)

/-- Exact zero-frequency linear quadratic complete correlation over a finite product of odd
prime fields. -/
theorem oddPrimeFamily_quadratic_linearCorrelation
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → OddPrime) (k r : ∀ i, ZMod (p i).1) :
    ∑ a : ∀ i, ZMod (p i).1,
      oddPrimeFamilyQuadraticCharacter p a * oddPrimeFamilyQuadraticCharacter p (k * a + r) =
      ∏ i, if k i = 0 then 0 else if r i = 0 then
        oddPrimeQuadraticCharacter (p i) (k i) * (((p i).1 : ℂ) - 1) else
          -oddPrimeQuadraticCharacter (p i) (k i) := by
  classical
  let f : ∀ i, ZMod (p i).1 → ℂ := fun i a =>
    oddPrimeQuadraticCharacter (p i) a * oddPrimeQuadraticCharacter (p i) (k i * a + r i)
  calc
    _ = ∑ a : ∀ i, ZMod (p i).1, ∏ i, f i (a i) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [oddPrimeFamilyQuadraticCharacter, f]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a : ZMod (p i).1, f i a := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun i => Finset.univ) f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact oddPrime_quadratic_linearCorrelation (p i) (k i) (r i)

/-- A finite family of pairwise distinct certified odd primes.  The certificates are part of the
finite arithmetic datum, so the corresponding product modulus and CRT map are constructed inside
Lean. -/
structure OddPrimeFamily (I : Type*) [Fintype I] where
  prime : I → OddPrime
  pairwise_ne : Pairwise fun i j => (prime i).1 ≠ (prime j).1

namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The primes in a certified distinct family are pairwise coprime. -/
theorem pairwise_coprime (P : OddPrimeFamily I) :
    Pairwise (Nat.Coprime on fun i => (P.prime i).1) := by
  intro i j hij
  exact Nat.coprime_primes (P.prime i).2.1 (P.prime j).2.1 |>.mpr (P.pairwise_ne hij)

/-- Square-free odd modulus associated to a certified prime family. -/
def modulus (P : OddPrimeFamily I) : ℕ := ∏ i, (P.prime i).1

/-- The associated square-free product modulus is positive, hence its residue ring is finite. -/
instance modulus_neZero (P : OddPrimeFamily I) : NeZero P.modulus := ⟨by
  dsimp only [modulus]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (P.prime i).2.1.ne_zero⟩

/-- CRT equivalence from the square-free product modulus to its prime-field factors. -/
def crtEquiv (P : OddPrimeFamily I) :
    ZMod P.modulus ≃+* (∀ i, ZMod (P.prime i).1) :=
  ZMod.prodEquivPi (fun i => (P.prime i).1) P.pairwise_coprime

/-- At integer shifts, equality of two CRT prime coordinates is exactly divisibility of their
difference by that prime. -/
theorem crtEquiv_intCast_eq_iff_dvd_sub (P : OddPrimeFamily I)
    (k l : ℤ) (i : I) :
    P.crtEquiv (k : ZMod P.modulus) i = P.crtEquiv (l : ZMod P.modulus) i ↔
      ((P.prime i).1 : ℤ) ∣ l - k := by
  change ZMod.prodEquivPi (fun j => (P.prime j).1) P.pairwise_coprime
      (k : ZMod (∏ j, (P.prime j).1)) i =
    ZMod.prodEquivPi (fun j => (P.prime j).1) P.pairwise_coprime
      (l : ZMod (∏ j, (P.prime j).1)) i ↔ _
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply]
  simpa using ZMod.intCast_eq_intCast_iff_dvd_sub k l (P.prime i).1

/-- Complex quadratic character on the square-free product modulus, constructed by CRT from
the prime-field characters. -/
def quadraticCharacter (P : OddPrimeFamily I) (x : ZMod P.modulus) : ℂ :=
  oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv x)

/-- Exact shifted quadratic complete correlation at the certified square-free CRT modulus.
The right side is the literal product of the diagonal/off-diagonal prime factors used in the
source proof of Bondarenko--Heap Lemma 8. -/
theorem quadratic_shiftCorrelation [DecidableEq I] (P : OddPrimeFamily I)
    (k l : ZMod P.modulus) :
    ∑ x : ZMod P.modulus, quadraticCharacter P (x + k) * quadraticCharacter P (x + l) =
      ∏ i, if P.crtEquiv k i = P.crtEquiv l i then ((P.prime i).1 : ℂ) - 1 else -1 := by
  calc
    _ = ∑ y : ∀ i, ZMod (P.prime i).1,
        oddPrimeFamilyQuadraticCharacter P.prime (y + P.crtEquiv k) *
          oddPrimeFamilyQuadraticCharacter P.prime (y + P.crtEquiv l) := by
      simp only [quadraticCharacter, map_add]
      change (∑ x : ZMod P.modulus,
          oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv x + P.crtEquiv k) *
            oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv x + P.crtEquiv l)) = _
      exact Equiv.sum_comp P.crtEquiv.toEquiv (fun y : ∀ i, ZMod (P.prime i).1 =>
        oddPrimeFamilyQuadraticCharacter P.prime (y + P.crtEquiv k) *
          oddPrimeFamilyQuadraticCharacter P.prime (y + P.crtEquiv l))
    _ = _ := oddPrimeFamily_quadratic_shiftCorrelation P.prime (P.crtEquiv k) (P.crtEquiv l)

/-- The CRT quadratic character is real-valued: complex conjugation fixes it pointwise. -/
theorem quadraticCharacter_star [DecidableEq I] (P : OddPrimeFamily I)
    (x : ZMod P.modulus) :
    star (quadraticCharacter P x) = quadraticCharacter P x := by
  simp only [quadraticCharacter, oddPrimeFamilyQuadraticCharacter, star_prod]
  simp_rw [MulChar.star_apply']
  simp_rw [(oddPrimeQuadraticCharacter_isQuadratic _).inv]

/-- The complete quadratic shift operator at a certified odd square-free CRT modulus. -/
def quadraticShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (a : ZMod P.modulus → ℂ) (x : ZMod P.modulus) : ℂ :=
  ∑ k : ZMod P.modulus, a k * quadraticCharacter P (x + k)

/-- Exact full-residue energy expansion for the quadratic shift operator at an odd square-free
CRT modulus.  This turns the source Lemma 8 second moment into the already closed local-factor
product; deriving its divisor majorant and interval estimate is a separate remaining step. -/
theorem quadratic_shiftSum_energy [DecidableEq I] (P : OddPrimeFamily I)
    (a : ZMod P.modulus → ℂ) :
    ∑ x : ZMod P.modulus, quadraticShiftSum P a x *
      star (quadraticShiftSum P a x) =
      ∑ k : ZMod P.modulus, ∑ l : ZMod P.modulus, a k * star (a l) *
        ∏ i, if P.crtEquiv k i = P.crtEquiv l i then ((P.prime i).1 : ℂ) - 1 else -1 := by
  classical
  simp only [quadraticShiftSum]
  simp_rw [star_sum, Finset.sum_mul_sum, star_mul, quadraticCharacter_star]
  have hreorder (x k l : ZMod P.modulus) :
      a k * quadraticCharacter P (x + k) *
          (quadraticCharacter P (x + l) * star (a l)) =
        (a k * star (a l)) *
          (quadraticCharacter P (x + k) * quadraticCharacter P (x + l)) := by
      ring
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, quadratic_shiftCorrelation]

/-- Exact CRT coordinate product appearing in the square-free quadratic shifted correlation. -/
def quadraticShiftKernel (P : OddPrimeFamily I)
    (k l : ZMod P.modulus) : ℂ :=
  ∏ i, if P.crtEquiv k i = P.crtEquiv l i then ((P.prime i).1 : ℂ) - 1 else -1

/-- Positive coordinatewise majorant of the exact quadratic shifted-correlation kernel. -/
def quadraticShiftKernelMajorant (P : OddPrimeFamily I)
    (k l : ZMod P.modulus) : ℝ :=
  ∏ i, if P.crtEquiv k i = P.crtEquiv l i then (P.prime i).1 else 1

/-- Integer-shift form of the CRT coordinate majorant: it contains exactly the certified primes
which divide the shift difference. -/
def quadraticShiftDivisorMajorant (P : OddPrimeFamily I) (d : ℤ) : ℝ :=
  ∏ i, if ((P.prime i).1 : ℤ) ∣ d then (P.prime i).1 else 1

/-- Indices of the certified CRT primes which divide an integer shift difference. -/
def shiftPrimeDivisors (P : OddPrimeFamily I) (d : ℤ) : Finset I :=
  Finset.univ.filter fun i => ((P.prime i).1 : ℤ) ∣ d

/-- Natural-number form of the selected-prime divisor majorant. -/
def quadraticShiftDivisorMajorantNat (P : OddPrimeFamily I) (d : ℤ) : ℕ :=
  ∏ i ∈ shiftPrimeDivisors P d, (P.prime i).1

/-- The real divisor majorant is exactly the real cast of its selected-prime natural product. -/
theorem quadraticShiftDivisorMajorant_eq_natCast (P : OddPrimeFamily I) (d : ℤ) :
    quadraticShiftDivisorMajorant P d = quadraticShiftDivisorMajorantNat P d := by
  rw [quadraticShiftDivisorMajorant, quadraticShiftDivisorMajorantNat]
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i => ((P.prime i).1 : ℤ) ∣ d),
        ((P.prime i).1 : ℝ) :=
      (Finset.prod_filter (fun i => ((P.prime i).1 : ℤ) ∣ d)
        (fun i => ((P.prime i).1 : ℝ))).symm
    _ = _ := by norm_cast

/-- The selected-prime product divides the certified square-free CRT modulus. -/
theorem quadraticShiftDivisorMajorantNat_dvd_modulus (P : OddPrimeFamily I) (d : ℤ) :
    quadraticShiftDivisorMajorantNat P d ∣ P.modulus := by
  rw [quadraticShiftDivisorMajorantNat, modulus]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- The selected-prime product divides the natural absolute value of the shift difference.  The
proof combines the internally certified pairwise coprimality with each selected prime divisor. -/
theorem quadraticShiftDivisorMajorantNat_dvd_natAbs (P : OddPrimeFamily I) (d : ℤ) :
    quadraticShiftDivisorMajorantNat P d ∣ d.natAbs := by
  apply Int.natCast_dvd.mp
  rw [quadraticShiftDivisorMajorantNat, Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · rintro i hi j hj hij
    exact (P.pairwise_coprime hij).isCoprime
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- The selected-prime product divides the literal natural gcd of the CRT modulus and the shift
difference. -/
theorem quadraticShiftDivisorMajorantNat_dvd_gcd (P : OddPrimeFamily I) (d : ℤ) :
    quadraticShiftDivisorMajorantNat P d ∣ P.modulus.gcd d.natAbs :=
  Nat.dvd_gcd (quadraticShiftDivisorMajorantNat_dvd_modulus P d)
    (quadraticShiftDivisorMajorantNat_dvd_natAbs P d)

/-- Closed gcd majorant for the selected CRT prime product. -/
theorem quadraticShiftDivisorMajorant_le_gcd (P : OddPrimeFamily I) (d : ℤ) :
    quadraticShiftDivisorMajorant P d ≤ P.modulus.gcd d.natAbs := by
  rw [quadraticShiftDivisorMajorant_eq_natCast]
  exact_mod_cast Nat.le_of_dvd
    (Nat.gcd_pos_of_pos_left _ (P.modulus_neZero.out |> Nat.pos_of_ne_zero))
    (quadraticShiftDivisorMajorantNat_dvd_gcd P d)

/-- Closed absolute-value majorant for the exact CRT local-factor kernel.  The remaining work to
reach the source Lemma 8 bound is to identify this coordinate product with its gcd/divisor
majorant and control the resulting interval coefficient sum. -/
theorem quadraticShiftKernel_norm_le_majorant (P : OddPrimeFamily I)
    (k l : ZMod P.modulus) :
    ‖quadraticShiftKernel P k l‖ ≤ quadraticShiftKernelMajorant P k l := by
  rw [quadraticShiftKernel, quadraticShiftKernelMajorant, norm_prod]
  apply Finset.prod_le_prod
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    by_cases h : P.crtEquiv k i = P.crtEquiv l i
    · simp only [if_pos h]
      let r : ℝ := ((P.prime i).1 : ℝ) - 1
      have hr : ((P.prime i).1 : ℂ) - 1 = (r : ℂ) := by
        dsimp [r]
        norm_cast
      rw [hr, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg]
      · have hpone : (1 : ℝ) ≤ (P.prime i).1 := by
          exact_mod_cast (P.prime i).2.1.one_le
        dsimp [r]
        linarith
      · have hpone : (1 : ℝ) ≤ (P.prime i).1 := by
          exact_mod_cast (P.prime i).2.1.one_le
        dsimp [r]
        linarith
    · simp [h]

/-- The complete square-free CRT quadratic shifted correlation is bounded by its closed positive
coordinatewise majorant. -/
theorem quadratic_shiftCorrelation_norm_le_majorant [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ZMod P.modulus) :
    ‖∑ x : ZMod P.modulus,
      quadraticCharacter P (x + k) * quadraticCharacter P (x + l)‖ ≤
      quadraticShiftKernelMajorant P k l := by
  rw [quadratic_shiftCorrelation, ← quadraticShiftKernel]
  exact quadraticShiftKernel_norm_le_majorant P k l

/-- At integer shifts, the CRT coordinate majorant is exactly the product of the certified primes
dividing the difference.  This is the closed bridge from CRT coincidence to divisor language. -/
theorem quadraticShiftKernelMajorant_intCast (P : OddPrimeFamily I)
    (k l : ℤ) :
    quadraticShiftKernelMajorant P (k : ZMod P.modulus) (l : ZMod P.modulus) =
      quadraticShiftDivisorMajorant P (l - k) := by
  rw [quadraticShiftKernelMajorant, quadraticShiftDivisorMajorant]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [crtEquiv_intCast_eq_iff_dvd_sub]

/-- Complete shifted quadratic correlation at integer shifts, bounded by the literal product of
the certified CRT primes which divide their difference. -/
theorem quadratic_shiftCorrelation_norm_le_divisorMajorant [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod P.modulus,
      quadraticCharacter P (x + (k : ZMod P.modulus)) *
        quadraticCharacter P (x + (l : ZMod P.modulus))‖ ≤
      quadraticShiftDivisorMajorant P (l - k) := by
  calc
    _ ≤ quadraticShiftKernelMajorant P (k : ZMod P.modulus) (l : ZMod P.modulus) :=
      quadratic_shiftCorrelation_norm_le_majorant P _ _
    _ = _ := quadraticShiftKernelMajorant_intCast P k l

/-- Square-free CRT complete-correlation bound in literal gcd form for integer shifts.  This is
the source Lemma 8 local correlation shape before its coefficient-level divisor/Cauchy argument. -/
theorem quadratic_shiftCorrelation_norm_le_gcd [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod P.modulus,
      quadraticCharacter P (x + (k : ZMod P.modulus)) *
        quadraticCharacter P (x + (l : ZMod P.modulus))‖ ≤ P.modulus.gcd (l - k).natAbs :=
  (quadratic_shiftCorrelation_norm_le_divisorMajorant P k l).trans
    (quadraticShiftDivisorMajorant_le_gcd P (l - k))

/-- The coordinatewise CRT majorant is at most the certified square-free product modulus. -/
theorem quadraticShiftKernelMajorant_le_modulus (P : OddPrimeFamily I)
    (k l : ZMod P.modulus) :
    quadraticShiftKernelMajorant P k l ≤ P.modulus := by
  rw [quadraticShiftKernelMajorant]
  calc
    _ ≤ ∏ i, ((P.prime i).1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        by_cases h : P.crtEquiv k i = P.crtEquiv l i
        · simp [h]
        · simp only [if_neg h]
          exact_mod_cast (P.prime i).2.1.one_le
    _ = P.modulus := by
      simp only [modulus, Nat.cast_prod]

/-- Coarse unconditional complete-correlation bound at every certified odd square-free CRT
modulus.  This uniform `q` envelope is weaker than the source gcd/divisor majorant, but is a
closed bound for the actual complete sum. -/
theorem quadratic_shiftCorrelation_norm_le_modulus [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ZMod P.modulus) :
    ‖∑ x : ZMod P.modulus,
      quadraticCharacter P (x + k) * quadraticCharacter P (x + l)‖ ≤ P.modulus :=
  (quadratic_shiftCorrelation_norm_le_majorant P k l).trans
    (quadraticShiftKernelMajorant_le_modulus P k l)

/-- Exact zero-frequency linear quadratic correlation at the certified odd square-free CRT
modulus.  This is the composite-modulus counterpart of the local factor calculation in the
source proof of Bondarenko--Heap Lemma 4. -/
theorem quadratic_linearCorrelation [DecidableEq I] (P : OddPrimeFamily I)
    (k r : ZMod P.modulus) :
    ∑ a : ZMod P.modulus, quadraticCharacter P a * quadraticCharacter P (k * a + r) =
      ∏ i, if P.crtEquiv k i = 0 then 0 else if P.crtEquiv r i = 0 then
        oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv k i) * (((P.prime i).1 : ℂ) - 1) else
          -oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv k i) := by
  calc
    _ = ∑ y : ∀ i, ZMod (P.prime i).1,
        oddPrimeFamilyQuadraticCharacter P.prime y *
          oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv k * y + P.crtEquiv r) := by
      simp only [quadraticCharacter, map_mul, map_add]
      change (∑ a : ZMod P.modulus,
          oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv a) *
            oddPrimeFamilyQuadraticCharacter P.prime
              (P.crtEquiv k * P.crtEquiv a + P.crtEquiv r)) = _
      exact Equiv.sum_comp P.crtEquiv.toEquiv (fun y : ∀ i, ZMod (P.prime i).1 =>
        oddPrimeFamilyQuadraticCharacter P.prime y *
          oddPrimeFamilyQuadraticCharacter P.prime (P.crtEquiv k * y + P.crtEquiv r))
    _ = _ := oddPrimeFamily_quadratic_linearCorrelation P.prime (P.crtEquiv k) (P.crtEquiv r)

end OddPrimeFamily

end RHTower
