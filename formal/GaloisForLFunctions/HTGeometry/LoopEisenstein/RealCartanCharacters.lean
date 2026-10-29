import GaloisForLFunctions.HTGeometry.LoopEisenstein.ExtendedCartanConjugation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Weights
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealDegreeRotation

/-!
# Weight characters of the actual real extended Cartan

The logarithm of the absolute value on real units gives complex weight
characters. Unique Cartan coordinates make these characters intrinsic to
the embedded subgroup. Weyl conjugation and degree contraction recover
the affine weight evaluation used in the convergent Weyl sum.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

/-- The image of the three-dimensional split Cartan in the extended loop group. -/
def extendedCartan (F : Type*) [Field F] : Subgroup (ExtendedLoopSL2 F) :=
  (extendedCartanEmbedding F).range

variable (F : Type*) [Field F]

/-- Unique coordinates of an element of the actual embedded extended Cartan. -/
def extendedCartanCoordinates (g : extendedCartan F) : (Fˣ × Fˣ) × Fˣ :=
  Classical.choose g.property

theorem extendedCartanCoordinates_spec (g : extendedCartan F) :
    extendedCartanEmbedding F (extendedCartanCoordinates F g) = (g : ExtendedLoopSL2 F) :=
  Classical.choose_spec g.property

/-- The intrinsic coordinates preserve multiplication. -/
def extendedCartanCoordinateHom : extendedCartan F →* ((Fˣ × Fˣ) × Fˣ) where
  toFun := extendedCartanCoordinates F
  map_one' := by
    apply extendedCartanEmbedding_injective F
    rw [extendedCartanCoordinates_spec, map_one]
    rfl
  map_mul' g h := by
    apply extendedCartanEmbedding_injective F
    rw [extendedCartanCoordinates_spec, map_mul,
      extendedCartanCoordinates_spec, extendedCartanCoordinates_spec]
    rfl

/-- Coordinate change induced by the monomial translation representative. -/
def translatedCartanCoordinates (m : ℤ) (p : (Fˣ × Fˣ) × Fˣ) : (Fˣ × Fˣ) × Fˣ :=
  ((p.1.1 * p.1.2 ^ (-2 * m) * p.2 ^ (-(m * m)), p.1.2 * p.2 ^ m), p.2)

/-- Coordinate change induced by the finite Weyl representative. -/
def reflectedCartanCoordinates (p : (Fˣ × Fˣ) × Fˣ) : (Fˣ × Fˣ) × Fˣ :=
  ((p.1.1, p.1.2⁻¹), p.2)

/-- Conjugation by the actual translation representative, restricted to the Cartan. -/
def translatedCartan (m : ℤ) (g : extendedCartan F) : extendedCartan F :=
  ⟨SemidirectProduct.inl (LoopSL2.translationLift F m) * (g : ExtendedLoopSL2 F) *
      (SemidirectProduct.inl (LoopSL2.translationLift F m))⁻¹, by
    obtain ⟨p, hp⟩ := g.property
    refine ⟨translatedCartanCoordinates F m p, ?_⟩
    rw [← hp]
    exact (translation_conj_extendedCartan F m p.1.1 p.1.2 p.2).symm⟩

/-- Conjugation by the actual finite Weyl representative, restricted to the Cartan. -/
def reflectedCartan (g : extendedCartan F) : extendedCartan F :=
  ⟨SemidirectProduct.inl (LoopSL2.finiteWeylLift F) * (g : ExtendedLoopSL2 F) *
      (SemidirectProduct.inl (LoopSL2.finiteWeylLift F))⁻¹, by
    obtain ⟨p, hp⟩ := g.property
    refine ⟨reflectedCartanCoordinates F p, ?_⟩
    rw [← hp]
    exact (finiteWeyl_conj_extendedCartan F p.1.1 p.1.2 p.2).symm⟩

theorem extendedCartanCoordinates_translated (m : ℤ) (g : extendedCartan F) :
    extendedCartanCoordinates F (translatedCartan F m g) =
      translatedCartanCoordinates F m (extendedCartanCoordinates F g) := by
  apply extendedCartanEmbedding_injective F
  rw [extendedCartanCoordinates_spec]
  change SemidirectProduct.inl (LoopSL2.translationLift F m) * (g : ExtendedLoopSL2 F) *
      (SemidirectProduct.inl (LoopSL2.translationLift F m))⁻¹ = _
  rw [← extendedCartanCoordinates_spec F g]
  exact translation_conj_extendedCartan F m _ _ _

theorem extendedCartanCoordinates_reflected (g : extendedCartan F) :
    extendedCartanCoordinates F (reflectedCartan F g) =
      reflectedCartanCoordinates F (extendedCartanCoordinates F g) := by
  apply extendedCartanEmbedding_injective F
  rw [extendedCartanCoordinates_spec]
  change SemidirectProduct.inl (LoopSL2.finiteWeylLift F) * (g : ExtendedLoopSL2 F) *
      (SemidirectProduct.inl (LoopSL2.finiteWeylLift F))⁻¹ = _
  rw [← extendedCartanCoordinates_spec F g]
  exact finiteWeyl_conj_extendedCartan F _ _ _

/-- Logarithm of the absolute value of a nonzero real unit. -/
def realUnitLog (a : ℝˣ) : ℝ := Real.log (a : ℝ)

theorem realUnitLog_eq_log_abs (a : ℝˣ) : realUnitLog a = Real.log |(a : ℝ)| :=
  (Real.log_abs _).symm

@[simp] theorem realUnitLog_one : realUnitLog 1 = 0 := Real.log_one

theorem realUnitLog_mul (a b : ℝˣ) : realUnitLog (a * b) = realUnitLog a + realUnitLog b :=
  Real.log_mul a.ne_zero b.ne_zero

theorem realUnitLog_zpow (a : ℝˣ) (n : ℤ) : realUnitLog (a ^ n) = n * realUnitLog a := by
  simp only [realUnitLog, Units.val_zpow_eq_zpow_val, Real.log_zpow]

theorem realUnitLog_inv (a : ℝˣ) : realUnitLog a⁻¹ = -realUnitLog a := by
  simp only [realUnitLog, Units.val_inv_eq_inv_val, Real.log_inv]

/-- Pair a complex affine weight with the real logarithmic Cartan coordinates. -/
def cartanLogEvaluation (L : AffineA1.Weight) (p : (ℝˣ × ℝˣ) × ℝˣ) : ℂ :=
  L.level * realUnitLog p.1.1 + L.finite * realUnitLog p.1.2 + L.degree * realUnitLog p.2

@[simp] theorem cartanLogEvaluation_one (L : AffineA1.Weight) :
    cartanLogEvaluation L 1 = 0 := by
  simp only [cartanLogEvaluation, Prod.fst_one, Prod.snd_one, realUnitLog_one,
    Complex.ofReal_zero, mul_zero, add_zero]

theorem cartanLogEvaluation_mul (L : AffineA1.Weight) (p r : (ℝˣ × ℝˣ) × ℝˣ) :
    cartanLogEvaluation L (p * r) = cartanLogEvaluation L p + cartanLogEvaluation L r := by
  simp only [cartanLogEvaluation, Prod.fst_mul, Prod.snd_mul, realUnitLog_mul, Complex.ofReal_add]
  ring

/-- The coordinate weight character, before transport to the embedded subgroup. -/
def cartanCoordinateCharacter (L : AffineA1.Weight) : ((ℝˣ × ℝˣ) × ℝˣ) →* ℂ where
  toFun p := Complex.exp (cartanLogEvaluation L p)
  map_one' := by rw [cartanLogEvaluation_one, Complex.exp_zero]
  map_mul' p r := by rw [cartanLogEvaluation_mul, Complex.exp_add]

/-- A genuine character of the actual real extended Cartan subgroup. -/
def cartanCharacter (L : AffineA1.Weight) : extendedCartan ℝ →* ℂ :=
  (cartanCoordinateCharacter L).comp (extendedCartanCoordinateHom ℝ)

theorem cartanCharacter_ne_zero (L : AffineA1.Weight) (g : extendedCartan ℝ) :
    cartanCharacter L g ≠ 0 := Complex.exp_ne_zero _

/-- Pullback by inverse translation is precisely the affine weight translation. -/
theorem cartanLogEvaluation_translated (m : ℤ) (L : AffineA1.Weight)
    (p : (ℝˣ × ℝˣ) × ℝˣ) :
    cartanLogEvaluation L (translatedCartanCoordinates ℝ (-m) p) =
      cartanLogEvaluation (AffineA1.translateWeight m L) p := by
  simp only [cartanLogEvaluation, translatedCartanCoordinates, realUnitLog_mul,
    realUnitLog_zpow, AffineA1.translateWeight]
  push_cast
  ring

theorem cartanLogEvaluation_reflected (L : AffineA1.Weight) (p : (ℝˣ × ℝˣ) × ℝˣ) :
    cartanLogEvaluation L (reflectedCartanCoordinates ℝ p) =
      cartanLogEvaluation (AffineA1.reflectWeight L) p := by
  simp only [cartanLogEvaluation, reflectedCartanCoordinates, realUnitLog_inv,
    AffineA1.reflectWeight, Complex.ofReal_neg]
  ring

/-- The actual translation conjugation realizes the abstract affine weight action. -/
theorem cartanCharacter_translated (m : ℤ) (L : AffineA1.Weight) (g : extendedCartan ℝ) :
    cartanCharacter L (translatedCartan ℝ (-m) g) =
      cartanCharacter (AffineA1.translateWeight m L) g := by
  change Complex.exp (cartanLogEvaluation L
    (extendedCartanCoordinates ℝ (translatedCartan ℝ (-m) g))) = _
  rw [extendedCartanCoordinates_translated, cartanLogEvaluation_translated]
  rfl

/-- The actual finite Weyl conjugation realizes the finite weight reflection. -/
theorem cartanCharacter_reflected (L : AffineA1.Weight) (g : extendedCartan ℝ) :
    cartanCharacter L (reflectedCartan ℝ g) =
      cartanCharacter (AffineA1.reflectWeight L) g := by
  change Complex.exp (cartanLogEvaluation L
    (extendedCartanCoordinates ℝ (reflectedCartan ℝ g))) = _
  rw [extendedCartanCoordinates_reflected, cartanLogEvaluation_reflected]
  rfl

/-- Positive real torus parameters in additive exponential coordinates. -/
def realCartanUnit (x : ℝ) : ℝˣ := Units.mk0 (Real.exp x) (Real.exp_ne_zero x)

@[simp] theorem realUnitLog_realCartanUnit (x : ℝ) : realUnitLog (realCartanUnit x) = x :=
  Real.log_exp x

@[simp] theorem realUnitLog_realDegreeUnit (r : ℝ) :
    realUnitLog (realDegreeUnit r) = -Real.exp r := Real.log_exp _

/-- The positive Cartan element with the contracting degree factor used by Garland. -/
def positiveRealCartan (t z r : ℝ) : extendedCartan ℝ :=
  ⟨extendedCartanElement ℝ (realCartanUnit z) (realCartanUnit t) (realDegreeUnit r),
    ⟨((realCartanUnit z, realCartanUnit t), realDegreeUnit r), rfl⟩⟩

theorem extendedCartanCoordinates_positive (t z r : ℝ) :
    extendedCartanCoordinates ℝ (positiveRealCartan t z r) =
      ((realCartanUnit z, realCartanUnit t), realDegreeUnit r) :=
  extendedCartanEmbedding_injective ℝ (extendedCartanCoordinates_spec ℝ _)

/-- The abstract degree exponent is evaluation of the constructed Cartan character. -/
theorem cartanCharacter_positive (L : AffineA1.Weight) (t z r : ℝ) :
    cartanCharacter L (positiveRealCartan t z r) =
      Complex.exp (AffineA1.rotatedEvaluation L t z r) := by
  change Complex.exp (cartanLogEvaluation L
    (extendedCartanCoordinates ℝ (positiveRealCartan t z r))) = _
  rw [extendedCartanCoordinates_positive]
  congr 1
  simp only [cartanLogEvaluation, realUnitLog_realCartanUnit, realUnitLog_realDegreeUnit,
    AffineA1.rotatedEvaluation, Complex.ofReal_neg]
  ring

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
