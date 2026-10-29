import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriBruhatExistence
import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriLatticeChain

/-!
# Uniqueness of the affine Iwahori Bruhat representative

The three lattice-chain contents distinguish every diagonal and
antidiagonal monomial. They recover the integer index and separate the
two families, giving uniqueness in the full infinite dihedral Weyl group.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

/-- Exponents of the three valuation contents for a diagonal monomial. -/
def diagonalLatticeExponents (n : ℤ) : ℤ × ℤ × ℤ :=
  (max (-n) n, max (-n) (n + 1), max (-n) n)

/-- Exponents of the three valuation contents for an antidiagonal monomial. -/
def weylLatticeExponents (n : ℤ) : ℤ × ℤ × ℤ :=
  (max n (-n), max n (1 - n), max (n - 1) (1 - n))

/-- Integer lattice profile of an actual affine Weyl representative. -/
def integerWeylProfile : AffineA1.Weyl → ℤ × ℤ × ℤ
  | .r m => diagonalLatticeExponents (-(show ℤ from m))
  | .sr m => weylLatticeExponents (-(show ℤ from m))

theorem diagonalLatticeExponents_injective : Function.Injective diagonalLatticeExponents := by
  intro n m h
  have h₀ : max (-n) n = max (-m) m := congrArg Prod.fst h
  have h₁ : max (-n) (n + 1) = max (-m) (m + 1) := congrArg (fun p => p.2.1) h
  omega

theorem weylLatticeExponents_injective : Function.Injective weylLatticeExponents := by
  intro n m h
  have h₀ : max n (-n) = max m (-m) := congrArg Prod.fst h
  have h₂ : max (n - 1) (1 - n) = max (m - 1) (1 - m) := congrArg (fun p => p.2.2) h
  omega

/-- Equality of the first and third contents separates diagonal from antidiagonal representatives. -/
theorem diagonalLatticeExponents_ne_weyl (n m : ℤ) :
    diagonalLatticeExponents n ≠ weylLatticeExponents m := by
  intro h
  have h₀ : max (-n) n = max m (-m) := congrArg Prod.fst h
  have h₂ : max (-n) n = max (m - 1) (1 - m) := congrArg (fun p => p.2.2) h
  omega

/-- The lattice profile recovers the full infinite-dihedral Weyl element. -/
theorem integerWeylProfile_injective : Function.Injective integerWeylProfile := by
  intro w v h
  cases w with
  | r m =>
    cases v with
    | r n =>
      have hmn : (m : ℤ) = (n : ℤ) :=
        neg_injective (diagonalLatticeExponents_injective h)
      subst n
      rfl
    | sr n => exact (diagonalLatticeExponents_ne_weyl (-m) (-n) h).elim
  | sr m =>
    cases v with
    | r n => exact (diagonalLatticeExponents_ne_weyl (-n) (-m) h.symm).elim
    | sr n =>
      have hmn : (m : ℤ) = (n : ℤ) :=
        neg_injective (weylLatticeExponents_injective h)
      subst n
      rfl

/-- Embed the integer content exponents into the actual Laurent valuation group. -/
def valuationProfileOfExponents (p : ℤ × ℤ × ℤ) :
    WithZero (Multiplicative ℤ) × WithZero (Multiplicative ℤ) × WithZero (Multiplicative ℤ) :=
  (WithZero.exp p.1, WithZero.exp p.2.1, WithZero.exp p.2.2)

theorem valuationProfileOfExponents_injective : Function.Injective valuationProfileOfExponents := by
  intro p q h
  have h₀ : p.1 = q.1 := WithZero.exp_injective (congrArg Prod.fst h)
  have h₁ : p.2.1 = q.2.1 := WithZero.exp_injective (congrArg (fun r => r.2.1) h)
  have h₂ : p.2.2 = q.2.2 := WithZero.exp_injective (congrArg (fun r => r.2.2) h)
  exact Prod.ext h₀ (Prod.ext h₁ h₂)

private theorem valuation_exp_max (a b : ℤ) :
    max (WithZero.exp a) (WithZero.exp b) = WithZero.exp (max a b) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (WithZero.exp_le_exp.2 hab)]
  · have hba := le_of_lt (lt_of_not_ge hab)
    rw [max_eq_left hba, max_eq_left (WithZero.exp_le_exp.2 hba)]

variable (F : Type*) [Field F]

theorem valuation_laurentXUnit_zpow (n : ℤ) :
    laurentValuation F ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F) =
      WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, coe_laurentXUnit, ← RatFunc.single_zpow]
  exact LaurentSeries.valuation_single_zpow F n

private theorem valuation_laurentXUnit_zpow_inv (n : ℤ) :
    laurentValuation F (((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) =
      WithZero.exp n := by
  rw [← zpow_neg, valuation_laurentXUnit_zpow, neg_neg]

private theorem valuation_laurentXUnit :
    laurentValuation F (laurentXUnit F : LaurentSeries F) = WithZero.exp (-1 : ℤ) := by
  simpa only [zpow_one] using valuation_laurentXUnit_zpow F 1

private theorem valuation_laurentXUnit_inv :
    laurentValuation F (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) =
      WithZero.exp (1 : ℤ) := by
  simpa only [zpow_one] using valuation_laurentXUnit_zpow_inv F 1

private theorem diagonal_monomial_content (n : ℤ) :
    matrixValuationContent (laurentValuation F) (sl2Diagonal (laurentXUnit F ^ n)) =
      WithZero.exp (max (-n) n) := by
  change matrixValuationContent (laurentValuation F)
    !![((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F), 0;
      0, (((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F)] = _
  rw [matrixValuationContent_diagonal, valuation_laurentXUnit_zpow,
    valuation_laurentXUnit_zpow_inv, valuation_exp_max]

private theorem diagonal_monomial_rows_content (n : ℤ) :
    matrixValuationContent (laurentValuation F)
      (latticeRows F (sl2Diagonal (laurentXUnit F ^ n))) =
        WithZero.exp (max (-n) (n + 1)) := by
  rw [latticeRows_entries]
  change matrixValuationContent (laurentValuation F)
    !![((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F), 0;
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * 0,
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        (((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F)] = _
  rw [mul_zero, matrixValuationContent_diagonal, map_mul, valuation_laurentXUnit_zpow,
    valuation_laurentXUnit_inv, valuation_laurentXUnit_zpow_inv,
    ← WithZero.exp_add, add_comm (1 : ℤ) n, valuation_exp_max]

private theorem diagonal_monomial_conjugate_content (n : ℤ) :
    matrixValuationContent (laurentValuation F)
      (latticeConjugate F (sl2Diagonal (laurentXUnit F ^ n))) =
        WithZero.exp (max (-n) n) := by
  rw [latticeConjugate_entries]
  change matrixValuationContent (laurentValuation F)
    !![((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F),
      (laurentXUnit F : LaurentSeries F) * 0;
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * 0,
      (((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F)] = _
  simp only [mul_zero]
  exact diagonal_monomial_content F n

private theorem weyl_monomial_content (n : ℤ) :
    matrixValuationContent (laurentValuation F) (sl2WeylLower (laurentXUnit F ^ n)) =
      WithZero.exp (max n (-n)) := by
  change matrixValuationContent (laurentValuation F)
    !![0, -(((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F);
      ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F), 0] = _
  rw [matrixValuationContent_antidiagonal, Valuation.map_neg, valuation_laurentXUnit_zpow_inv,
    valuation_laurentXUnit_zpow, valuation_exp_max]

private theorem weyl_monomial_rows_content (n : ℤ) :
    matrixValuationContent (laurentValuation F)
      (latticeRows F (sl2WeylLower (laurentXUnit F ^ n))) =
        WithZero.exp (max n (1 - n)) := by
  rw [latticeRows_entries]
  change matrixValuationContent (laurentValuation F)
    !![0, -(((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F);
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F),
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * 0] = _
  rw [mul_zero, matrixValuationContent_antidiagonal, Valuation.map_neg, map_mul,
    valuation_laurentXUnit_zpow_inv, valuation_laurentXUnit_inv, valuation_laurentXUnit_zpow,
    ← WithZero.exp_add, ← sub_eq_add_neg, valuation_exp_max]

private theorem weyl_monomial_conjugate_content (n : ℤ) :
    matrixValuationContent (laurentValuation F)
      (latticeConjugate F (sl2WeylLower (laurentXUnit F ^ n))) =
        WithZero.exp (max (n - 1) (1 - n)) := by
  rw [latticeConjugate_entries]
  change matrixValuationContent (laurentValuation F)
    !![0, (laurentXUnit F : LaurentSeries F) *
      (-(((laurentXUnit F ^ n)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F));
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        ((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F), 0] = _
  rw [matrixValuationContent_antidiagonal, map_mul, map_mul, Valuation.map_neg,
    valuation_laurentXUnit, valuation_laurentXUnit_zpow_inv,
    valuation_laurentXUnit_inv, valuation_laurentXUnit_zpow,
    ← WithZero.exp_add, ← WithZero.exp_add,
    show (-1 : ℤ) + n = n - 1 by omega, ← sub_eq_add_neg, valuation_exp_max]

theorem iwahoriLatticeProfile_diagonal_monomial (n : ℤ) :
    iwahoriLatticeProfile F (sl2Diagonal (laurentXUnit F ^ n)) =
      valuationProfileOfExponents (diagonalLatticeExponents n) :=
  Prod.ext (diagonal_monomial_content F n)
    (Prod.ext (diagonal_monomial_rows_content F n) (diagonal_monomial_conjugate_content F n))

theorem iwahoriLatticeProfile_weyl_monomial (n : ℤ) :
    iwahoriLatticeProfile F (sl2WeylLower (laurentXUnit F ^ n)) =
      valuationProfileOfExponents (weylLatticeExponents n) :=
  Prod.ext (weyl_monomial_content F n)
    (Prod.ext (weyl_monomial_rows_content F n) (weyl_monomial_conjugate_content F n))

/-- The actual group-valued profile is the faithful valuation image of its integer formula. -/
theorem iwahoriLatticeProfile_affineWeylMatrix (w : AffineA1.Weyl) :
    iwahoriLatticeProfile F (affineWeylMatrix F w) = valuationProfileOfExponents (integerWeylProfile w) := by
  cases w with
  | r m => exact iwahoriLatticeProfile_diagonal_monomial F (-(show ℤ from m))
  | sr m => exact iwahoriLatticeProfile_weyl_monomial F (-(show ℤ from m))

/-- Distinct affine Weyl elements give distinct actual Iwahori double cosets. -/
theorem iwahoriEquivalent_affineWeyl_iff (w v : AffineA1.Weyl) :
    iwahoriEquivalent F (affineWeylMatrix F w) (affineWeylMatrix F v) ↔ w = v := by
  constructor
  · rintro ⟨l, hl, r, hr, h⟩
    have hp : iwahoriLatticeProfile F (affineWeylMatrix F w) =
        iwahoriLatticeProfile F (affineWeylMatrix F v) :=
      (iwahoriLatticeProfile_factors F hl hr _).symm.trans
        (congrArg (iwahoriLatticeProfile F) h)
    rw [iwahoriLatticeProfile_affineWeylMatrix, iwahoriLatticeProfile_affineWeylMatrix] at hp
    exact integerWeylProfile_injective (valuationProfileOfExponents_injective hp)
  · rintro rfl
    exact iwahoriEquivalent_refl F _

/-- The full formal Laurent SL₂ group has a unique affine Weyl Iwahori double-coset representative. -/
theorem exists_unique_iwahori_bruhat (g : SL2 (LaurentSeries F)) :
    ∃! w : AffineA1.Weyl, iwahoriEquivalent F g (affineWeylMatrix F w) := by
  obtain ⟨w, hw⟩ := exists_iwahori_bruhat F g
  refine ⟨w, hw, ?_⟩
  intro v hv
  exact (iwahoriEquivalent_affineWeyl_iff F v w).1
    (iwahoriEquivalent_trans F (iwahoriEquivalent_symm F hv) hw)

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
