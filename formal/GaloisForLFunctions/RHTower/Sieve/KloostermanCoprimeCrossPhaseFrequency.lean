import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalGeometricCancellation
import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# Coprime cross-phase frequencies at the product modulus

For coprime positive moduli, every pair of Kloosterman unit frequencies has one canonical
product-period frequency.  Its CRT coordinates are `-r * x` modulo `q` and `q * y` modulo `r`.
Multiplication by the complementary moduli permutes the two unit groups, so this construction is
an equivalence from the pair of unit groups to the units modulo `q * r`.

The standard additive character of the product frequency is exactly the unequal-modulus phase
ratio used by the terminal geometric estimate.  Consequently the former double reciprocal-chord
sum reindexes without loss or multiplicity as one sum over product-modulus units.  This is the
arithmetic compression needed before a collective harmonic estimate; it assumes no spectral
cancellation theorem.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private def unitsProdMulEquiv (R S : Type*) [Monoid R] [Monoid S] :
    (R × S)ˣ ≃* Rˣ × Sˣ where
  toFun u :=
    (Units.map (MonoidHom.fst R S) u, Units.map (MonoidHom.snd R S) u)
  invFun p :=
    { val := ((p.1 : R), (p.2 : S))
      inv := (((p.1⁻¹ : Rˣ) : R), ((p.2⁻¹ : Sˣ) : S))
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  left_inv u := by
    apply Units.ext
    apply Prod.ext <;> rfl
  right_inv p := by
    apply Prod.ext <;> apply Units.ext <;> rfl
  map_mul' u v := by
    apply Prod.ext <;> apply Units.ext <;> rfl

private def unitsMapRingEquiv
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) : Rˣ ≃* Sˣ where
  toFun u := Units.map e.toMonoidHom u
  invFun u := Units.map e.symm.toMonoidHom u
  left_inv u := by apply Units.ext; simp
  right_inv u := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp

/-- Product-period residue carrying one coprime cross-unit phase.  The complementary factors in
the CRT coordinates are what convert the separate denominators `q` and `r` into denominator
`q * r`. -/
def kloostermanCoprimeCrossPhaseFrequency
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ZMod (q * r) :=
  (ZMod.chineseRemainder hcop).symm
    (((-(ZMod.unitOfCoprime r hcop.symm) * x : (ZMod q)ˣ) : ZMod q),
      (((ZMod.unitOfCoprime q hcop) * y : (ZMod r)ˣ) : ZMod r))

@[simp] theorem kloostermanCoprimeCrossPhaseFrequency_chineseRemainder
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ZMod.chineseRemainder hcop
        (kloostermanCoprimeCrossPhaseFrequency q r hcop x y) =
      (((-(ZMod.unitOfCoprime r hcop.symm) * x : (ZMod q)ˣ) : ZMod q),
        (((ZMod.unitOfCoprime q hcop) * y : (ZMod r)ˣ) : ZMod r)) := by
  simp [kloostermanCoprimeCrossPhaseFrequency]

/-- Coprime cross-unit frequency pairs are exactly the units at the product modulus. -/
def kloostermanCoprimeCrossPhaseFrequencyEquiv
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r) :
    (ZMod q)ˣ × (ZMod r)ˣ ≃ (ZMod (q * r))ˣ :=
  ((Equiv.mulLeft (-(ZMod.unitOfCoprime r hcop.symm))).prodCongr
      (Equiv.mulLeft (ZMod.unitOfCoprime q hcop))).trans
    ((unitsProdMulEquiv (ZMod q) (ZMod r)).symm.toEquiv.trans
      (unitsMapRingEquiv (ZMod.chineseRemainder hcop)).symm.toEquiv)

@[simp] theorem coe_kloostermanCoprimeCrossPhaseFrequencyEquiv_apply
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r)
    (p : (ZMod q)ˣ × (ZMod r)ˣ) :
    ((kloostermanCoprimeCrossPhaseFrequencyEquiv q r hcop p :
        (ZMod (q * r))ˣ) : ZMod (q * r)) =
      kloostermanCoprimeCrossPhaseFrequency q r hcop p.1 p.2 := by
  simp [kloostermanCoprimeCrossPhaseFrequencyEquiv,
    kloostermanCoprimeCrossPhaseFrequency, unitsMapRingEquiv, unitsProdMulEquiv]

/-- The residue-valued coprime cross-frequency map is injective. -/
theorem kloostermanCoprimeCrossPhaseFrequency_injective
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r) :
    Function.Injective (fun p : (ZMod q)ˣ × (ZMod r)ˣ =>
      kloostermanCoprimeCrossPhaseFrequency q r hcop p.1 p.2) := by
  intro p p' hp
  apply (kloostermanCoprimeCrossPhaseFrequencyEquiv q r hcop).injective
  apply Units.ext
  simpa using hp

/-- Complementary-modulus lifting to the product sends the second CRT coordinate to its own
standard additive character. -/
theorem stdAddChar_mul_left_complement_chineseRemainder
    {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)] (hcop : q.Coprime r)
    (a : ℤ) (z : ZMod (q * r)) :
    ZMod.stdAddChar (((a * (q : ℤ) : ℤ) : ZMod (q * r)) * z) =
      ZMod.stdAddChar ((a : ZMod r) * (ZMod.chineseRemainder hcop z).2) := by
  rw [show z = (z.val : ZMod (q * r)) by exact (ZMod.natCast_zmod_val z).symm]
  have hzr :
      (ZMod.chineseRemainder hcop (z.val : ZMod (q * r))).2 = (z.val : ZMod r) := by
    simp [ZMod.chineseRemainder]
  rw [hzr]
  have hlhs :
      ((a * (q : ℤ) : ℤ) : ZMod (q * r)) * (z.val : ZMod (q * r)) =
        ((a * (q : ℤ) * (z.val : ℤ) : ℤ) : ZMod (q * r)) := by
    push_cast
    ring
  have hrhs :
      (a : ZMod r) * (z.val : ZMod r) =
        ((a * (z.val : ℤ) : ℤ) : ZMod r) := by
    push_cast
    ring
  rw [hlhs, hrhs]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  field_simp [hqC, hrC]

/-- Negating a cyclic frequency conjugates its standard additive character. -/
theorem star_stdAddChar_eq_neg
    (q : ℕ) [NeZero q] (z : ZMod q) :
    star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  have hzNorm : ‖ZMod.stdAddChar z‖ = 1 := by simp
  have hzNe : ZMod.stdAddChar z ≠ 0 := norm_ne_zero_iff.mp (by simp [hzNorm])
  apply mul_right_cancel₀ hzNe
  calc
    star (ZMod.stdAddChar z) * ZMod.stdAddChar z =
        (Complex.normSq (ZMod.stdAddChar z) : ℂ) := by
      rw [show star (ZMod.stdAddChar z) =
        conj (ZMod.stdAddChar z) by rfl]
      rw [mul_comm, Complex.mul_conj]
    _ = 1 := by rw [Complex.normSq_eq_norm_sq, hzNorm]; norm_num
    _ = ZMod.stdAddChar (-z) * ZMod.stdAddChar z := by
      rw [← AddChar.map_add_eq_mul]
      simp

/-- The product-level character of the CRT cross-frequency is the original cross-phase ratio. -/
theorem stdAddChar_kloostermanCoprimeCrossPhaseFrequency
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ZMod.stdAddChar (kloostermanCoprimeCrossPhaseFrequency q r hcop x y) =
      kloostermanCrossPhaseRatio q r x y := by
  let e := ZMod.chineseRemainder hcop
  let zx : ZMod (q * r) := e.symm ((x : ZMod q), 0)
  let zy : ZMod (q * r) := e.symm (0, (y : ZMod r))
  have hfreq : kloostermanCoprimeCrossPhaseFrequency q r hcop x y =
      (((-1 : ℤ) * (r : ℤ) : ℤ) : ZMod (q * r)) * zx +
        (((1 : ℤ) * (q : ℤ) : ℤ) : ZMod (q * r)) * zy := by
    apply e.injective
    apply Prod.ext <;>
      simp [kloostermanCoprimeCrossPhaseFrequency, e, zx, zy]
  rw [hfreq, AddChar.map_add_eq_mul]
  rw [RHTower.stdAddChar_mul_complement_chineseRemainder hcop (-1) zx]
  rw [stdAddChar_mul_left_complement_chineseRemainder hcop 1 zy]
  simp only [zx, zy, e, RingEquiv.apply_symm_apply]
  rw [show ((-1 : ℤ) : ZMod q) * (x : ZMod q) = -(x : ZMod q) by simp,
    show ((1 : ℤ) : ZMod r) * (y : ZMod r) = (y : ZMod r) by simp]
  rw [← star_stdAddChar_eq_neg q]
  rfl

/-- The pairwise reciprocal-chord budget is exactly one product-modulus unit sum. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_eq_productUnits
    (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r) :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) =
      ∑ z : (ZMod (q * r))ˣ,
        2 / ‖1 - ZMod.stdAddChar (z : ZMod (q * r))‖ := by
  calc
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) =
        ∑ p : (ZMod q)ˣ × (ZMod r)ˣ,
          2 / ‖1 - kloostermanCrossPhaseRatio q r p.1 p.2‖ := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p : (ZMod q)ˣ × (ZMod r)ˣ,
          2 / ‖1 - ZMod.stdAddChar
            ((kloostermanCoprimeCrossPhaseFrequencyEquiv q r hcop p :
              (ZMod (q * r))ˣ) : ZMod (q * r))‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [coe_kloostermanCoprimeCrossPhaseFrequencyEquiv_apply,
        stdAddChar_kloostermanCoprimeCrossPhaseFrequency]
    _ = ∑ z : (ZMod (q * r))ˣ,
        2 / ‖1 - ZMod.stdAddChar (z : ZMod (q * r))‖ := by
      exact (kloostermanCoprimeCrossPhaseFrequencyEquiv q r hcop).sum_comp
        (fun z : (ZMod (q * r))ˣ =>
          2 / ‖1 - ZMod.stdAddChar (z : ZMod (q * r))‖)

/-- Coprime terminal correlation with the double unit-pair denominator compressed to one
product-modulus unit sum. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productUnitChords
    (M q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hcop : Nat.Coprime q r) (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      ∑ z : (ZMod (q * r))ˣ,
        2 / ‖1 - ZMod.stdAddChar (z : ZMod (q * r))‖ := by
  rw [← sum_kloostermanCrossPhaseRatio_reciprocalChord_eq_productUnits q r hcop]
  exact norm_kloostermanNaturalCrossIntervalTerminalBlock_le_geometric
    M q r hqr n k

end

end RHTower.Sieve
