import Mathlib

/-!
# Weyl-algebra source for the negative local-Fourier branch

This module constructs the first Weyl algebra over `ℂ` from its presentation, rather than
postulating exponent transitions.  It supplies four independent pieces of source semantics:

* free noncommutative operator words evaluated by multiplication and differentiation on `ℂ[X]`;
* the two-sided Weyl relation `D X - X D = 1` and its quotient algebra;
* the algebraic Fourier automorphism `X ↦ D`, `D ↦ -X`, including its order-four law;
* polynomial gauge/addition automorphisms `D ↦ D + p(X)`.

The final section proves the exact monomial curve contact chart used by Hiroe's
`F^(∞,∞)` transform.  For an Airy step `β = R + E`, the transformed coordinate has order `E`
and the old leading exponent `β` is divisible by `E`.  This is the genuine leading-edge source
of the negative rank drop.  Preservation of a general lower characteristic tail is intentionally
not asserted here.
-/

namespace GaloisForLFunctions
namespace IrregularStokes
namespace WeylFourier

noncomputable section

/-! ## Presented operators and their polynomial semantics -/

/-- Coordinate and derivative generators of the first Weyl algebra. -/
inductive Generator
  | coordinate
  | derivative
  deriving DecidableEq

/-- Free noncommutative operator words before imposing the Weyl commutator. -/
abbrev PresentedWeyl := FreeAlgebra ℂ Generator

/-- Coordinate generator in the free presentation. -/
def coordinateWord : PresentedWeyl := FreeAlgebra.ι ℂ Generator.coordinate

/-- Derivative generator in the free presentation. -/
def derivativeWord : PresentedWeyl := FreeAlgebra.ι ℂ Generator.derivative

/-- Multiplication by `X` on the polynomial representation. -/
def polynomialCoordinateOperator : Module.End ℂ (Polynomial ℂ) :=
  LinearMap.mulLeft ℂ Polynomial.X

/-- Polynomial differentiation on the polynomial representation. -/
def polynomialDerivativeOperator : Module.End ℂ (Polynomial ℂ) :=
  Polynomial.derivative

/-- Actual action of presented operator words on complex polynomials. -/
def operatorSemantics :
    PresentedWeyl →ₐ[ℂ] Module.End ℂ (Polynomial ℂ) :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => polynomialCoordinateOperator
    | Generator.derivative => polynomialDerivativeOperator)

/-- Multiplication and differentiation satisfy the Weyl commutator on every polynomial. -/
theorem operatorSemantics_commutator :
    operatorSemantics
        (derivativeWord * coordinateWord - coordinateWord * derivativeWord) = 1 := by
  apply LinearMap.ext
  intro p
  simp only [map_sub, map_mul]
  simp only [operatorSemantics, derivativeWord, coordinateWord,
    FreeAlgebra.lift_ι_apply]
  change Polynomial.derivative (Polynomial.X * p) -
    Polynomial.X * Polynomial.derivative p = p
  rw [Polynomial.derivative_mul, Polynomial.derivative_X]
  simp

/-! ## Algebraic Fourier transform on the presentation -/

/-- Forward algebraic Fourier substitution `X ↦ D`, `D ↦ -X`. -/
def fourierWordHom : PresentedWeyl →ₐ[ℂ] PresentedWeyl :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => derivativeWord
    | Generator.derivative => -coordinateWord)

/-- Inverse algebraic Fourier substitution `X ↦ -D`, `D ↦ X`. -/
def inverseFourierWordHom : PresentedWeyl →ₐ[ℂ] PresentedWeyl :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => -derivativeWord
    | Generator.derivative => coordinateWord)

theorem fourierWordHom_inverseFourierWordHom :
    fourierWordHom.comp inverseFourierWordHom = AlgHom.id ℂ PresentedWeyl := by
  apply FreeAlgebra.hom_ext
  funext g
  cases g <;> simp [fourierWordHom, inverseFourierWordHom,
    coordinateWord, derivativeWord]

theorem inverseFourierWordHom_fourierWordHom :
    inverseFourierWordHom.comp fourierWordHom = AlgHom.id ℂ PresentedWeyl := by
  apply FreeAlgebra.hom_ext
  funext g
  cases g <;> simp [fourierWordHom, inverseFourierWordHom,
    coordinateWord, derivativeWord]

/-- Algebraic Fourier transform as an actual automorphism of presented operators. -/
def fourierWord : PresentedWeyl ≃ₐ[ℂ] PresentedWeyl :=
  AlgEquiv.ofAlgHom fourierWordHom inverseFourierWordHom
    fourierWordHom_inverseFourierWordHom inverseFourierWordHom_fourierWordHom

@[simp] theorem fourierWord_coordinate :
    fourierWord coordinateWord = derivativeWord := by
  simp [fourierWord, fourierWordHom, coordinateWord, derivativeWord]

@[simp] theorem fourierWord_derivative :
    fourierWord derivativeWord = -coordinateWord := by
  simp [fourierWord, fourierWordHom, coordinateWord, derivativeWord]

/-- Relation whose vanishing presents the first Weyl algebra. -/
def weylRelation : PresentedWeyl :=
  derivativeWord * coordinateWord - coordinateWord * derivativeWord - 1

/-- Fourier substitution preserves the Weyl relation exactly. -/
theorem fourierWord_weylRelation : fourierWord weylRelation = weylRelation := by
  simp [weylRelation]
  noncomm_ring

/-- Algebraic Fourier transform has order four on every presented operator. -/
theorem fourierWord_fourth (a : PresentedWeyl) :
    fourierWord (fourierWord (fourierWord (fourierWord a))) = a := by
  have h : fourierWord.toAlgHom.comp
      (fourierWord.toAlgHom.comp
        (fourierWord.toAlgHom.comp fourierWord.toAlgHom)) =
      AlgHom.id ℂ PresentedWeyl := by
    apply FreeAlgebra.hom_ext
    funext g
    cases g <;> simp [fourierWord, fourierWordHom,
      coordinateWord, derivativeWord]
  exact DFunLike.congr_fun h a

/-! ## Weyl quotient and descended semantics -/

/-- Two-sided ideal generated by the Weyl relation. -/
def weylIdeal : TwoSidedIdeal PresentedWeyl :=
  TwoSidedIdeal.span {weylRelation}

/-- Congruence presenting the first Weyl algebra. -/
def weylCongruence : RingCon PresentedWeyl := weylIdeal.ringCon

private lemma map_mem_weylIdeal
    (e : PresentedWeyl ≃+* PresentedWeyl) (he : e weylRelation = weylRelation)
    {a : PresentedWeyl} (ha : a ∈ weylIdeal) : e a ∈ weylIdeal := by
  apply TwoSidedIdeal.span_induction (s := {weylRelation})
      (p := fun a _ => e a ∈ weylIdeal) (x := a) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · intro z hz
    have hz' : z = weylRelation := by simpa using hz
    subst z
    rw [he]
    exact TwoSidedIdeal.subset_span (Set.mem_singleton weylRelation)
  · rw [map_zero]
    exact weylIdeal.zero_mem
  · intro u v hu hv ihu ihv
    simpa using weylIdeal.add_mem ihu ihv
  · intro u hu ihu
    simpa using weylIdeal.neg_mem ihu
  · intro u v hv ihv
    simpa using weylIdeal.mul_mem_left (e u) (e v) ihv
  · intro v u hv ihv
    rw [map_mul]
    exact weylIdeal.mul_mem_right (e u) (e v) ihv

theorem fourierWord_mem_weylIdeal_iff (a : PresentedWeyl) :
    fourierWord a ∈ weylIdeal ↔ a ∈ weylIdeal := by
  constructor
  · intro ha
    have hInverseRelation : fourierWord.symm weylRelation = weylRelation := by
      apply fourierWord.injective
      simp [fourierWord_weylRelation]
    simpa using map_mem_weylIdeal fourierWord.symm.toRingEquiv hInverseRelation ha
  · exact map_mem_weylIdeal fourierWord.toRingEquiv fourierWord_weylRelation

theorem weylCongruence_fourier :
    weylCongruence = weylCongruence.comap fourierWord.toRingEquiv := by
  apply RingCon.ext
  intro a b
  change weylIdeal.ringCon a b ↔
    weylIdeal.ringCon (fourierWord a) (fourierWord b)
  rw [TwoSidedIdeal.rel_iff, TwoSidedIdeal.rel_iff]
  rw [← map_sub, fourierWord_mem_weylIdeal_iff]

private lemma operatorSemantics_eq_zero_of_mem_weylIdeal
    {a : PresentedWeyl} (ha : a ∈ weylIdeal) : operatorSemantics a = 0 := by
  apply TwoSidedIdeal.span_induction (s := {weylRelation})
      (p := fun a _ => operatorSemantics a = 0) (x := a) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · intro z hz
    have hz' : z = weylRelation := by simpa using hz
    subst z
    simp [weylRelation, operatorSemantics_commutator]
  · exact map_zero operatorSemantics
  · intro u v hu hv ihu ihv
    simp [ihu, ihv]
  · intro u hu ihu
    simp [ihu]
  · intro u v hv ihv
    simp [map_mul, ihv]
  · intro v u hv ihv
    simp [map_mul, ihv]

theorem weylCongruence_le_operatorSemantics_ker :
    weylCongruence ≤ RingCon.ker operatorSemantics.toRingHom := by
  intro a b hab
  rw [RingCon.ker_apply]
  have hsub : a - b ∈ weylIdeal :=
    (TwoSidedIdeal.rel_iff weylIdeal a b).mp hab
  have hzero := operatorSemantics_eq_zero_of_mem_weylIdeal hsub
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- First Weyl algebra `A₁(ℂ)` as the quotient by `D X - X D - 1`. -/
abbrev WeylAlgebra := weylCongruence.Quotient

/-- Quotient map from presented operator words to the Weyl algebra. -/
def toWeylAlgebra : PresentedWeyl →ₐ[ℂ] WeylAlgebra :=
  weylCongruence.mkₐ ℂ

/-- Coordinate operator in the Weyl algebra. -/
def X : WeylAlgebra := toWeylAlgebra coordinateWord

/-- Derivative operator in the Weyl algebra. -/
def D : WeylAlgebra := toWeylAlgebra derivativeWord

/-- The defining Weyl relation holds in the quotient. -/
theorem D_mul_X_sub_X_mul_D : D * X - X * D = 1 := by
  have hRelation : weylRelation ∈ weylIdeal :=
    TwoSidedIdeal.subset_span (Set.mem_singleton weylRelation)
  have hzero : toWeylAlgebra weylRelation = 0 := Quotient.sound hRelation
  have hzero' : D * X - X * D - 1 = 0 := by
    simpa [weylRelation, toWeylAlgebra, X, D] using hzero
  exact sub_eq_zero.mp hzero'

/-- Algebraic Fourier transform descended to the actual Weyl quotient. -/
def fourier : WeylAlgebra ≃ₐ[ℂ] WeylAlgebra :=
  RingCon.congrₐ ℂ fourierWord weylCongruence_fourier

@[simp] theorem fourier_X : fourier X = D := by
  simp [fourier, X, D, toWeylAlgebra, fourierWord, fourierWordHom,
    coordinateWord, derivativeWord]

@[simp] theorem fourier_D : fourier D = -X := by
  simp [fourier, X, D, toWeylAlgebra, fourierWord, fourierWordHom,
    coordinateWord, derivativeWord]

/-- Polynomial representation of the quotient Weyl algebra. -/
def polynomialRepresentation :
    WeylAlgebra →ₐ[ℂ] Module.End ℂ (Polynomial ℂ) :=
  weylCongruence.liftₐ operatorSemantics
    weylCongruence_le_operatorSemantics_ker

@[simp] theorem polynomialRepresentation_X :
    polynomialRepresentation X = polynomialCoordinateOperator := by
  simp [polynomialRepresentation, X, toWeylAlgebra,
    coordinateWord, operatorSemantics]

@[simp] theorem polynomialRepresentation_D :
    polynomialRepresentation D = polynomialDerivativeOperator := by
  simp [polynomialRepresentation, D, toWeylAlgebra,
    derivativeWord, operatorSemantics]

theorem WeylAlgebra_one_ne_zero : (1 : WeylAlgebra) ≠ 0 := by
  intro h
  have hmap := congrArg polynomialRepresentation h
  have hend : (1 : Module.End ℂ (Polynomial ℂ)) ≠ 0 := by
    intro he
    have happ := LinearMap.congr_fun he (1 : Polynomial ℂ)
    simp at happ
  apply hend
  simp at hmap

instance : Nontrivial WeylAlgebra := ⟨⟨1, 0, WeylAlgebra_one_ne_zero⟩⟩

/-- Generalized Airy cyclic operator `D^R - X^E`. -/
def generalizedAiryOperator (R E : ℕ) : WeylAlgebra := D ^ R - X ^ E

/-- Exact Fourier image of a generalized Airy cyclic operator. -/
theorem fourier_generalizedAiryOperator (R E : ℕ) :
    fourier (generalizedAiryOperator R E) = (-X) ^ R - D ^ E := by
  simp [generalizedAiryOperator]

theorem fourier_sq_X : fourier (fourier X) = -X := by simp

theorem fourier_sq_D : fourier (fourier D) = -D := by simp

/-- The descended Fourier transform has order four on every Weyl operator. -/
theorem fourier_fourth (a : WeylAlgebra) :
    fourier (fourier (fourier (fourier a))) = a := by
  obtain ⟨w, rfl⟩ :=
    RingCon.mkₐ_surjective (α := ℂ) weylCongruence a
  change toWeylAlgebra
      (fourierWord (fourierWord (fourierWord (fourierWord w)))) =
    toWeylAlgebra w
  rw [fourierWord_fourth]

/-! ## Polynomial additions as gauge automorphisms -/

/-- Embed a commutative polynomial as a polynomial in the coordinate word. -/
def coordinatePolynomialWord : Polynomial ℂ →ₐ[ℂ] PresentedWeyl :=
  Polynomial.aeval coordinateWord

@[simp] theorem coordinatePolynomialWord_X :
    coordinatePolynomialWord Polynomial.X = coordinateWord := by
  simp [coordinatePolynomialWord]

/-- Presented gauge substitution `D ↦ D + p(X)`. -/
def gaugeWordHom (p : Polynomial ℂ) : PresentedWeyl →ₐ[ℂ] PresentedWeyl :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => coordinateWord
    | Generator.derivative => derivativeWord + coordinatePolynomialWord p)

/-- Inverse presented gauge substitution `D ↦ D - p(X)`. -/
def inverseGaugeWordHom (p : Polynomial ℂ) : PresentedWeyl →ₐ[ℂ] PresentedWeyl :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => coordinateWord
    | Generator.derivative => derivativeWord - coordinatePolynomialWord p)

@[simp] theorem gaugeWordHom_coordinate (p : Polynomial ℂ) :
    gaugeWordHom p coordinateWord = coordinateWord := by
  simp [gaugeWordHom, coordinateWord]

@[simp] theorem inverseGaugeWordHom_coordinate (p : Polynomial ℂ) :
    inverseGaugeWordHom p coordinateWord = coordinateWord := by
  simp [inverseGaugeWordHom, coordinateWord]

theorem gaugeWordHom_coordinatePolynomialWord (p h : Polynomial ℂ) :
    gaugeWordHom p (coordinatePolynomialWord h) = coordinatePolynomialWord h := by
  have heq : (gaugeWordHom p).comp coordinatePolynomialWord =
      coordinatePolynomialWord := by
    apply Polynomial.algHom_ext
    simp [coordinatePolynomialWord]
  exact AlgHom.congr_fun heq h

theorem inverseGaugeWordHom_coordinatePolynomialWord (p h : Polynomial ℂ) :
    inverseGaugeWordHom p (coordinatePolynomialWord h) =
      coordinatePolynomialWord h := by
  have heq : (inverseGaugeWordHom p).comp coordinatePolynomialWord =
      coordinatePolynomialWord := by
    apply Polynomial.algHom_ext
    simp [coordinatePolynomialWord]
  exact AlgHom.congr_fun heq h

theorem gaugeWordHom_inverseGaugeWordHom (p : Polynomial ℂ) :
    (gaugeWordHom p).comp (inverseGaugeWordHom p) =
      AlgHom.id ℂ PresentedWeyl := by
  apply FreeAlgebra.hom_ext
  funext g
  cases g
  · simp [gaugeWordHom, inverseGaugeWordHom, coordinateWord]
  · simp only [Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
    rw [show inverseGaugeWordHom p (FreeAlgebra.ι ℂ Generator.derivative) =
        derivativeWord - coordinatePolynomialWord p by
      simp [inverseGaugeWordHom, derivativeWord]]
    change gaugeWordHom p
      (derivativeWord - coordinatePolynomialWord p) = derivativeWord
    rw [map_sub, gaugeWordHom_coordinatePolynomialWord]
    simp [gaugeWordHom, derivativeWord]

theorem inverseGaugeWordHom_gaugeWordHom (p : Polynomial ℂ) :
    (inverseGaugeWordHom p).comp (gaugeWordHom p) =
      AlgHom.id ℂ PresentedWeyl := by
  apply FreeAlgebra.hom_ext
  funext g
  cases g
  · simp [gaugeWordHom, inverseGaugeWordHom, coordinateWord]
  · simp only [Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
    rw [show gaugeWordHom p (FreeAlgebra.ι ℂ Generator.derivative) =
        derivativeWord + coordinatePolynomialWord p by
      simp [gaugeWordHom, derivativeWord]]
    change inverseGaugeWordHom p
      (derivativeWord + coordinatePolynomialWord p) = derivativeWord
    rw [map_add, inverseGaugeWordHom_coordinatePolynomialWord]
    simp [inverseGaugeWordHom, derivativeWord]

/-- Polynomial gauge/addition as an actual automorphism of presented operators. -/
def gaugeWord (p : Polynomial ℂ) : PresentedWeyl ≃ₐ[ℂ] PresentedWeyl :=
  AlgEquiv.ofAlgHom (gaugeWordHom p) (inverseGaugeWordHom p)
    (gaugeWordHom_inverseGaugeWordHom p)
    (inverseGaugeWordHom_gaugeWordHom p)

@[simp] theorem gaugeWord_coordinate (p : Polynomial ℂ) :
    gaugeWord p coordinateWord = coordinateWord := by
  simp [gaugeWord, gaugeWordHom, coordinateWord]

@[simp] theorem gaugeWord_derivative (p : Polynomial ℂ) :
    gaugeWord p derivativeWord =
      derivativeWord + coordinatePolynomialWord p := by
  simp [gaugeWord, gaugeWordHom, derivativeWord]

@[simp] theorem gaugeWord_coordinatePolynomialWord (p h : Polynomial ℂ) :
    gaugeWord p (coordinatePolynomialWord h) = coordinatePolynomialWord h :=
  gaugeWordHom_coordinatePolynomialWord p h

/-- Gauge substitution preserves the Weyl relation. -/
theorem gaugeWord_weylRelation (p : Polynomial ℂ) :
    gaugeWord p weylRelation = weylRelation := by
  have hcomm : coordinatePolynomialWord p * coordinateWord =
      coordinateWord * coordinatePolynomialWord p := by
    rw [← coordinatePolynomialWord_X, ← map_mul, ← map_mul, mul_comm]
  simp [weylRelation]
  rw [add_mul, mul_add, hcomm]
  noncomm_ring

theorem gaugeWord_mem_weylIdeal_iff (p : Polynomial ℂ) (a : PresentedWeyl) :
    gaugeWord p a ∈ weylIdeal ↔ a ∈ weylIdeal := by
  constructor
  · intro ha
    have hInverseRelation : (gaugeWord p).symm weylRelation = weylRelation := by
      apply (gaugeWord p).injective
      simp [gaugeWord_weylRelation]
    simpa using map_mem_weylIdeal (gaugeWord p).symm.toRingEquiv hInverseRelation ha
  · intro ha
    exact map_mem_weylIdeal (gaugeWord p).toRingEquiv
      (gaugeWord_weylRelation p) ha

theorem weylCongruence_gauge (p : Polynomial ℂ) :
    weylCongruence = weylCongruence.comap (gaugeWord p).toRingEquiv := by
  apply RingCon.ext
  intro a b
  change weylIdeal.ringCon a b ↔
    weylIdeal.ringCon (gaugeWord p a) (gaugeWord p b)
  rw [TwoSidedIdeal.rel_iff, TwoSidedIdeal.rel_iff]
  rw [← map_sub, gaugeWord_mem_weylIdeal_iff]

/-- Coordinate-polynomial embedding in the quotient Weyl algebra. -/
def coordinatePolynomial : Polynomial ℂ →ₐ[ℂ] WeylAlgebra :=
  toWeylAlgebra.comp coordinatePolynomialWord

/-- Gauge/addition descended to the actual Weyl algebra. -/
def gauge (p : Polynomial ℂ) : WeylAlgebra ≃ₐ[ℂ] WeylAlgebra :=
  RingCon.congrₐ ℂ (gaugeWord p) (weylCongruence_gauge p)

@[simp] theorem gauge_X (p : Polynomial ℂ) : gauge p X = X := by
  simp [gauge, X, toWeylAlgebra, gaugeWord, gaugeWordHom, coordinateWord]

@[simp] theorem gauge_D (p : Polynomial ℂ) :
    gauge p D = D + coordinatePolynomial p := by
  simp [gauge, D, toWeylAlgebra, gaugeWord, gaugeWordHom,
    derivativeWord, coordinatePolynomial]

@[simp] theorem gauge_coordinatePolynomial (p h : Polynomial ℂ) :
    gauge p (coordinatePolynomial h) = coordinatePolynomial h := by
  change toWeylAlgebra (gaugeWord p (coordinatePolynomialWord h)) =
    toWeylAlgebra (coordinatePolynomialWord h)
  rw [gaugeWord_coordinatePolynomialWord]

theorem gauge_preserves_commutator (p : Polynomial ℂ) :
    gauge p (D * X - X * D) = 1 := by
  rw [D_mul_X_sub_X_mul_D, map_one]

/-! ## Hiroe's `F^(∞,∞)` contact chart on actual monomial curve germs -/

/-- Polynomial parametrisation of a plane curve germ. -/
structure ParametrizedPlaneCurve where
  xParam : Polynomial ℂ
  yParam : Polynomial ℂ

/-- Monomial germ `x=t^R`, `y=t^β`. -/
def monomialCurve (R beta : ℕ) : ParametrizedPlaneCurve where
  xParam := Polynomial.X ^ R
  yParam := Polynomial.X ^ beta

/-- Hiroe's infinity-to-infinity contact chart on a monomial germ:
`x₁=y/x=t^(β-R)`, `y₁=y`, represented when `R ≤ β`. -/
def infinityInfinityMonomialTransform (R beta : ℕ) : ParametrizedPlaneCurve :=
  monomialCurve (beta - R) beta

@[simp] theorem monomialCurve_xParam (R beta : ℕ) :
    (monomialCurve R beta).xParam = Polynomial.X ^ R := rfl

@[simp] theorem monomialCurve_yParam (R beta : ℕ) :
    (monomialCurve R beta).yParam = Polynomial.X ^ beta := rfl

@[simp] theorem monomialCurve_xOrder (R beta : ℕ) :
    (monomialCurve R beta).xParam.natDegree = R := by
  simp [monomialCurve]

@[simp] theorem monomialCurve_yOrder (R beta : ℕ) :
    (monomialCurve R beta).yParam.natDegree = beta := by
  simp [monomialCurve]

/-- Exact birational contact relation `x x₁ = y₁`, `y=y₁`. -/
theorem infinityInfinityMonomialTransform_contact
    {R beta : ℕ} (hRbeta : R ≤ beta) :
    (monomialCurve R beta).xParam *
        (infinityInfinityMonomialTransform R beta).xParam =
      (infinityInfinityMonomialTransform R beta).yParam ∧
    (monomialCurve R beta).yParam =
      (infinityInfinityMonomialTransform R beta).yParam := by
  constructor
  · simp only [monomialCurve_xParam, infinityInfinityMonomialTransform,
      monomialCurve_yParam]
    rw [← pow_add, Nat.add_sub_of_le hRbeta]
  · rfl

/-- The transformed coordinate order is the exact exponent subtraction `β-R`. -/
theorem infinityInfinityMonomialTransform_xOrder (R beta : ℕ) :
    (infinityInfinityMonomialTransform R beta).xParam.natDegree = beta - R := by
  simp [infinityInfinityMonomialTransform]

/-- At an Airy step `β=R+E`, Hiroe's contact chart has new coordinate order exactly `E`. -/
theorem airy_infinityInfinity_rankDrop
    {R E beta : ℕ} (hbeta : beta = R + E) :
    (infinityInfinityMonomialTransform R beta).xParam.natDegree = E := by
  rw [infinityInfinityMonomialTransform_xOrder, hbeta]
  omega

/-- If `E ∣ R`, the old Airy leading exponent becomes inessential after the rank drop:
`E ∣ β`, equivalently `gcd(E,β)=E`. -/
theorem airy_infinityInfinity_leadingExponent_gcd
    {R E beta : ℕ} (hER : E ∣ R) (hbeta : beta = R + E) :
    Nat.gcd E beta = E := by
  rw [Nat.gcd_eq_left_iff_dvd]
  rw [hbeta]
  exact dvd_add hER (dvd_refl E)

/-- Operator and curve shadows of an Airy step have the same rank exchange `R ↔ E`. -/
theorem airy_fourier_contact_source
    {R E beta : ℕ} (hbeta : beta = R + E) :
    fourier (generalizedAiryOperator R E) = (-X) ^ R - D ^ E ∧
    (infinityInfinityMonomialTransform R beta).xParam.natDegree = E := by
  exact ⟨fourier_generalizedAiryOperator R E,
    airy_infinityInfinity_rankDrop hbeta⟩

end

end WeylFourier
end IrregularStokes
end GaloisForLFunctions
