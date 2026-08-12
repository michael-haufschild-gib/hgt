import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Literal rational-Witt source: localized polynomials and normalized fractions

For a commutative ring `A`, Deninger's underlying rational-Witt additive group is the kernel of
evaluation at zero on the units of `A[T]` localized at polynomials with constant coefficient one.
The group law is multiplication of rational functions, hence Witt addition.

This module constructs that source literally. It proves denominator regularity, the injective map
from the localization into `A[[T]]`, and the normalized `P/Q` representation of every kernel
element. Witt multiplication is deliberately not fabricated here; its construction and comparison
with the reduced monoid algebra are the next source-level steps.
-/


namespace RHTower

noncomputable section

/-- Multiplicative system of polynomials whose value at zero is one. -/
def deningerRationalWittDenominators (A : Type*) [CommRing A] : Submonoid (Polynomial A) where
  carrier := {P | P.coeff 0 = 1}
  one_mem' := by simp
  mul_mem' {P Q} hP hQ := by
    change P.coeff 0 = 1 at hP
    change Q.coeff 0 = 1 at hQ
    simp [hP, hQ]

/-- Deninger's localization `A[T]_S` for `S = {P | P(0)=1}`. -/
abbrev DeningerRationalWittLocalization (A : Type*) [CommRing A] :=
  Localization (deningerRationalWittDenominators A)

/-- Evaluation at zero descends through the localization because every denominator evaluates to one. -/
noncomputable def deningerRationalWittEvaluationZero (A : Type*) [CommRing A] :
    DeningerRationalWittLocalization A →+* A :=
  IsLocalization.lift (M := deningerRationalWittDenominators A)
    (S := DeningerRationalWittLocalization A) (g := Polynomial.constantCoeff)
    (fun P => by
      change IsUnit ((P : Polynomial A).coeff 0)
      rw [P.2]
      exact isUnit_one)

noncomputable def deningerRationalWittUnitEvaluationZero (A : Type*) [CommRing A] :
    (DeningerRationalWittLocalization A)ˣ →* Aˣ := Units.map (deningerRationalWittEvaluationZero A)

/-- Literal underlying additive group of rational Witt vectors. Its group operation is ordinary
multiplication of normalized rational functions, i.e. Witt addition. -/
abbrev DeningerRationalWittAdditive (A : Type*) [CommRing A] : Type _ :=
  MonoidHom.ker (deningerRationalWittUnitEvaluationZero A)

theorem deningerRationalWittEvaluationZero_algebraMap (A : Type*) [CommRing A] (P : Polynomial A) :
    deningerRationalWittEvaluationZero A (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) P) = P.coeff 0 := by
  exact IsLocalization.lift_eq _ P

theorem deningerRationalWittDenominators_map
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    deningerRationalWittDenominators A ≤
      Submonoid.comap (Polynomial.mapRingHom f)
        (deningerRationalWittDenominators B) := by
  intro P hP
  change (P.map f).coeff 0 = 1
  simp [show P.coeff 0 = 1 from hP]

/-- Functorial map on the literal localized-polynomial carrier. -/
noncomputable def deningerRationalWittLocalizationMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerRationalWittLocalization A →+* DeningerRationalWittLocalization B :=
  IsLocalization.map (DeningerRationalWittLocalization B)
    (Polynomial.mapRingHom f) (deningerRationalWittDenominators_map f)

theorem deningerRationalWittEvaluationZero_natural
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (deningerRationalWittEvaluationZero B).comp
        (deningerRationalWittLocalizationMap f) =
      f.comp (deningerRationalWittEvaluationZero A) := by
  apply IsLocalization.ringHom_ext (deningerRationalWittDenominators A)
  apply Polynomial.ringHom_ext
  · intro a
    simp [deningerRationalWittLocalizationMap,
      deningerRationalWittEvaluationZero, IsLocalization.lift_eq]
  · simp [deningerRationalWittLocalizationMap,
      deningerRationalWittEvaluationZero, IsLocalization.lift_eq]

/-- Functorial map on the literal underlying additive groups of rational Witt vectors. -/
noncomputable def deningerRationalWittAdditiveMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerRationalWittAdditive A →* DeningerRationalWittAdditive B where
  toFun w :=
    ⟨Units.map (deningerRationalWittLocalizationMap f) w.1, by
      apply Units.ext
      have hw := congrArg Units.val w.2
      have hn := RingHom.congr_fun
        (deningerRationalWittEvaluationZero_natural f)
        (w.1 : DeningerRationalWittLocalization A)
      change deningerRationalWittEvaluationZero B
          (deningerRationalWittLocalizationMap f
            (w.1 : DeningerRationalWittLocalization A)) =
        f (deningerRationalWittEvaluationZero A
          (w.1 : DeningerRationalWittLocalization A)) at hn
      change deningerRationalWittEvaluationZero B
          (deningerRationalWittLocalizationMap f
            (w.1 : DeningerRationalWittLocalization A)) = 1
      rw [hn]
      simpa [deningerRationalWittUnitEvaluationZero] using congrArg f hw⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem deningerRationalWittLocalizationMap_id
    (A : Type*) [CommRing A] :
    deningerRationalWittLocalizationMap (RingHom.id A) =
      RingHom.id (DeningerRationalWittLocalization A) := by
  apply IsLocalization.ringHom_ext (deningerRationalWittDenominators A)
  apply Polynomial.ringHom_ext
  · intro a
    simp [deningerRationalWittLocalizationMap]
  · simp [deningerRationalWittLocalizationMap]

theorem deningerRationalWittLocalizationMap_comp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g : B →+* C) (f : A →+* B) :
    deningerRationalWittLocalizationMap (g.comp f) =
      (deningerRationalWittLocalizationMap g).comp
        (deningerRationalWittLocalizationMap f) := by
  apply IsLocalization.ringHom_ext (deningerRationalWittDenominators A)
  apply Polynomial.ringHom_ext
  · intro a
    simp [deningerRationalWittLocalizationMap]
  · simp [deningerRationalWittLocalizationMap]

@[simp] theorem deningerRationalWittAdditiveMap_id
    (A : Type*) [CommRing A] :
    deningerRationalWittAdditiveMap (RingHom.id A) =
      MonoidHom.id (DeningerRationalWittAdditive A) := by
  ext w
  change deningerRationalWittLocalizationMap (RingHom.id A)
      (w.1 : DeningerRationalWittLocalization A) = _
  rw [deningerRationalWittLocalizationMap_id]
  rfl

theorem deningerRationalWittAdditiveMap_comp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g : B →+* C) (f : A →+* B) :
    deningerRationalWittAdditiveMap (g.comp f) =
      (deningerRationalWittAdditiveMap g).comp
        (deningerRationalWittAdditiveMap f) := by
  ext w
  change deningerRationalWittLocalizationMap (g.comp f)
      (w.1 : DeningerRationalWittLocalization A) =
    deningerRationalWittLocalizationMap g
      (deningerRationalWittLocalizationMap f
        (w.1 : DeningerRationalWittLocalization A))
  rw [deningerRationalWittLocalizationMap_comp]
  rfl

/-- Constant-term-one polynomials are non-zero-divisors, detected by their unit power series. -/
theorem deningerRationalWittDenominators_le_nonZeroDivisors
    (A : Type*) [CommRing A] :
    deningerRationalWittDenominators A ≤ nonZeroDivisors (Polynomial A) := by
  intro P hP
  have hunitPS : IsUnit ((P : Polynomial A) : PowerSeries A) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe]
    change P.coeff 0 = 1 at hP
    rw [hP]
    exact isUnit_one
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro Q hPQ
    apply Polynomial.coe_injective A
    apply hunitPS.mul_left_cancel
    simpa using congrArg (fun R : Polynomial A => (R : PowerSeries A)) hPQ
  · intro Q hQP
    apply Polynomial.coe_injective A
    apply hunitPS.mul_right_cancel
    simpa using congrArg (fun R : Polynomial A => (R : PowerSeries A)) hQP

/-- Canonical localization map `A[T]_S → A[[T]]`. -/
noncomputable def deningerRationalWittLocalizationToPowerSeries (A : Type*) [CommRing A] :
    DeningerRationalWittLocalization A →+* PowerSeries A :=
  IsLocalization.lift (M := deningerRationalWittDenominators A)
    (S := DeningerRationalWittLocalization A) (g := Polynomial.coeToPowerSeries.ringHom)
    (fun P => by
      rw [Polynomial.coeToPowerSeries.ringHom_apply,
        PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe]
      have hP : (P : Polynomial A).coeff 0 = 1 := P.2
      rw [hP]
      exact isUnit_one)

/-- The localized-polynomial source embeds in formal power series over every commutative ring. -/
theorem deningerRationalWittLocalizationToPowerSeries_injective (A : Type*) [CommRing A] :
    Function.Injective (deningerRationalWittLocalizationToPowerSeries A) := by
  rw [deningerRationalWittLocalizationToPowerSeries, IsLocalization.lift_injective_iff]
  intro P Q
  constructor
  · intro h
    have hPQ : P = Q :=
      (IsLocalization.injective (DeningerRationalWittLocalization A)
        (deningerRationalWittDenominators_le_nonZeroDivisors A)) h
    exact congrArg Polynomial.toPowerSeries hPQ
  · intro h
    have hPQ : P = Q := (Polynomial.coe_injective A) h
    exact congrArg (algebraMap (Polynomial A) (DeningerRationalWittLocalization A)) hPQ

theorem deningerRationalWittLocalizationToPowerSeries_natural
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (deningerRationalWittLocalizationToPowerSeries B).comp
        (deningerRationalWittLocalizationMap f) =
      (PowerSeries.map f).comp
        (deningerRationalWittLocalizationToPowerSeries A) := by
  apply IsLocalization.ringHom_ext (deningerRationalWittDenominators A)
  apply Polynomial.ringHom_ext
  · intro a
    simp [deningerRationalWittLocalizationMap,
      deningerRationalWittLocalizationToPowerSeries]
  · simp [deningerRationalWittLocalizationMap,
      deningerRationalWittLocalizationToPowerSeries]

/-- The literal rational-Witt localization respects every coefficient-ring monomorphism. -/
theorem deningerRationalWittLocalizationMap_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (deningerRationalWittLocalizationMap f) := by
  intro x y hxy
  apply deningerRationalWittLocalizationToPowerSeries_injective A
  apply PowerSeries.map_injective f hf
  have hn := RingHom.congr_fun
    (deningerRationalWittLocalizationToPowerSeries_natural f) x
  have hn' := RingHom.congr_fun
    (deningerRationalWittLocalizationToPowerSeries_natural f) y
  change deningerRationalWittLocalizationToPowerSeries B
      (deningerRationalWittLocalizationMap f x) =
    PowerSeries.map f (deningerRationalWittLocalizationToPowerSeries A x) at hn
  change deningerRationalWittLocalizationToPowerSeries B
      (deningerRationalWittLocalizationMap f y) =
    PowerSeries.map f (deningerRationalWittLocalizationToPowerSeries A y) at hn'
  rw [← hn, ← hn', hxy]

/-- The literal rational-Witt additive-group functor respects monomorphisms. -/
theorem deningerRationalWittAdditiveMap_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (deningerRationalWittAdditiveMap f) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply deningerRationalWittLocalizationMap_injective f hf
  exact congrArg (fun z : DeningerRationalWittAdditive B =>
    (((z.1 : (DeningerRationalWittLocalization B)ˣ) :
      DeningerRationalWittLocalization B))) hxy

/-- Polynomial representative `1 - aT` of the Teichmüller element `[a]`. -/
def deningerRationalWittTeichmullerPolynomial
    {A : Type*} [CommRing A] (a : A) : Polynomial A :=
  1 - Polynomial.C a * Polynomial.X

@[simp] theorem deningerRationalWittTeichmullerPolynomial_coeff_zero
    {A : Type*} [CommRing A] (a : A) :
    (deningerRationalWittTeichmullerPolynomial a).coeff 0 = 1 := by
  simp [deningerRationalWittTeichmullerPolynomial]

noncomputable def deningerRationalWittTeichmullerUnit
    {A : Type*} [CommRing A] (a : A) :
    (DeningerRationalWittLocalization A)ˣ :=
  (IsLocalization.map_units (M := deningerRationalWittDenominators A)
    (DeningerRationalWittLocalization A)
    ⟨deningerRationalWittTeichmullerPolynomial a,
      deningerRationalWittTeichmullerPolynomial_coeff_zero a⟩).unit

@[simp] theorem deningerRationalWittTeichmullerUnit_val
    {A : Type*} [CommRing A] (a : A) :
    ((deningerRationalWittTeichmullerUnit a :
      (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A) =
      algebraMap (Polynomial A) (DeningerRationalWittLocalization A)
        (deningerRationalWittTeichmullerPolynomial a) := by
  exact (IsLocalization.map_units (M := deningerRationalWittDenominators A)
    (DeningerRationalWittLocalization A)
    ⟨deningerRationalWittTeichmullerPolynomial a,
      deningerRationalWittTeichmullerPolynomial_coeff_zero a⟩).unit_spec

/-- Literal Teichmüller element `[a] = 1-aT` in the localized rational-Witt carrier. -/
noncomputable def deningerRationalWittTeichmuller
    {A : Type*} [CommRing A] (a : A) : DeningerRationalWittAdditive A := by
  refine ⟨deningerRationalWittTeichmullerUnit a, ?_⟩
  apply Units.ext
  change deningerRationalWittEvaluationZero A
      (deningerRationalWittTeichmullerUnit a : DeningerRationalWittLocalization A) = 1
  rw [deningerRationalWittTeichmullerUnit_val,
    deningerRationalWittEvaluationZero_algebraMap,
    deningerRationalWittTeichmullerPolynomial_coeff_zero]

@[simp] theorem deningerRationalWittAdditiveMap_teichmuller
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    deningerRationalWittAdditiveMap f (deningerRationalWittTeichmuller a) =
      deningerRationalWittTeichmuller (f a) := by
  apply Subtype.ext
  apply Units.ext
  change deningerRationalWittLocalizationMap f
      (deningerRationalWittTeichmullerUnit a : DeningerRationalWittLocalization A) =
    (deningerRationalWittTeichmullerUnit (f a) : DeningerRationalWittLocalization B)
  rw [deningerRationalWittTeichmullerUnit_val,
    deningerRationalWittTeichmullerUnit_val]
  rw [deningerRationalWittLocalizationMap, IsLocalization.map_eq]
  congr 1
  ext n
  simp [deningerRationalWittTeichmullerPolynomial]

/-- Evaluation at zero on units of the formal power-series ring. -/
noncomputable def deningerBigWittUnitEvaluationZero
    (A : Type*) [CommRing A] : (PowerSeries A)ˣ →* Aˣ :=
  Units.map PowerSeries.constantCoeff.toMonoidHom

/-- Literal underlying additive group `1 + TA[[T]]` of the big Witt vectors. -/
abbrev DeningerBigWittAdditive (A : Type*) [CommRing A] : Type _ :=
  MonoidHom.ker (deningerBigWittUnitEvaluationZero A)

theorem deningerRationalWitt_constantCoeff_comp_toPowerSeries
    (A : Type*) [CommRing A] :
    PowerSeries.constantCoeff.comp
        (deningerRationalWittLocalizationToPowerSeries A) =
      deningerRationalWittEvaluationZero A := by
  apply IsLocalization.ringHom_ext (deningerRationalWittDenominators A)
  apply Polynomial.ringHom_ext
  · intro a
    simp [deningerRationalWittLocalizationToPowerSeries,
      deningerRationalWittEvaluationZero, IsLocalization.lift_eq]
  · change PowerSeries.constantCoeff
        (deningerRationalWittLocalizationToPowerSeries A
          (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Polynomial.X)) =
      deningerRationalWittEvaluationZero A
        (algebraMap (Polynomial A) (DeningerRationalWittLocalization A) Polynomial.X)
    rw [deningerRationalWittLocalizationToPowerSeries,
      deningerRationalWittEvaluationZero, IsLocalization.lift_eq,
      IsLocalization.lift_eq]
    rfl

/-- Canonical inclusion of literal rational Witt vectors in the big Witt carrier. -/
noncomputable def deningerRationalWittToBigWittAdditive
    (A : Type*) [CommRing A] :
    DeningerRationalWittAdditive A →* DeningerBigWittAdditive A where
  toFun w :=
    ⟨Units.map (deningerRationalWittLocalizationToPowerSeries A) w.1, by
      apply Units.ext
      have hw := congrArg Units.val w.2
      change PowerSeries.constantCoeff
          (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) = 1
      have hc := RingHom.congr_fun
        (deningerRationalWitt_constantCoeff_comp_toPowerSeries A) (w.1 : _)
      change PowerSeries.constantCoeff
          (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) =
        deningerRationalWittEvaluationZero A (w.1 : _) at hc
      rw [hc]
      simpa [deningerRationalWittUnitEvaluationZero] using hw⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- The rational-Witt-to-big-Witt inclusion is injective over every commutative ring. -/
theorem deningerRationalWittToBigWittAdditive_injective
    (A : Type*) [CommRing A] :
    Function.Injective (deningerRationalWittToBigWittAdditive A) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply deningerRationalWittLocalizationToPowerSeries_injective A
  exact congrArg (fun z : DeningerBigWittAdditive A =>
    (((z.1 : (PowerSeries A)ˣ) : PowerSeries A))) hxy

/-- Every literal rational-Witt element has a representative `P/Q` with `P(0)=Q(0)=1`. -/
theorem deningerRationalWittAdditive_exists_normalized_fraction
    (A : Type*) [CommRing A] (w : DeningerRationalWittAdditive A) :
    ∃ (P Q : Polynomial A) (hQ : Q ∈ deningerRationalWittDenominators A),
      P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧
        (w.1 : DeningerRationalWittLocalization A) =
          IsLocalization.mk' (DeningerRationalWittLocalization A) P ⟨Q, hQ⟩ := by
  obtain ⟨⟨P, Q⟩, hPQ⟩ :=
    IsLocalization.mk'_surjective (deningerRationalWittDenominators A)
      ((w.1 : (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A)
  refine ⟨P, Q, Q.2, ?_, Q.2, hPQ.symm⟩
  have hw0 : deningerRationalWittEvaluationZero A
      ((w.1 : (DeningerRationalWittLocalization A)ˣ) : DeningerRationalWittLocalization A) = 1 := by
    have hw := congrArg Units.val w.2
    simpa [deningerRationalWittUnitEvaluationZero] using hw
  rw [← hPQ] at hw0
  rw [deningerRationalWittEvaluationZero, IsLocalization.lift_mk'_spec] at hw0
  have hQ0 : (Q : Polynomial A).coeff 0 = 1 := Q.2
  simpa [hQ0] using hw0

end

end RHTower
