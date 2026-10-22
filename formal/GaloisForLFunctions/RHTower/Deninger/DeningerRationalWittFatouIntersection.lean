import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFieldIntersection

/-!
# Fatou-domain descent for literal rational Witt vectors

Deninger 2025, Corollary 1.10(2) (source label `t1.8`), extends the field-intersection theorem to an extension of
integral domains `A ⊆ B` when `A` is a Fatou domain.  This module formulates the Fatou property
on the literal localized-polynomial and power-series carriers and proves the resulting
rational-Witt descent.

The Fatou predicate below is the source equality

`A[T]_S = Frac(A)(T) ∩ A[[T]]`

inside `Frac(A)[[T]]`, expressed as its nontrivial image-containment direction.  It is not a
rational-Witt descent premise: it applies to every localized polynomial, without a unit or
constant-term-one hypothesis.
-/

namespace RHTower

noncomputable section

/-- Literal Fatou property `A[T]_S = Frac(A)(T) ∩ A[[T]]` at the power-series embedding. -/
def DeningerFatouDomain (A : Type*) [CommRing A] [IsDomain A] : Prop :=
  ∀ (x : DeningerRationalWittLocalization (FractionRing A)) (F : PowerSeries A),
    PowerSeries.map (algebraMap A (FractionRing A)) F =
        deningerRationalWittLocalizationToPowerSeries (FractionRing A) x →
      ∃ y : DeningerRationalWittLocalization A,
        deningerRationalWittLocalizationMap
            (algebraMap A (FractionRing A)) y = x

/-- A localized polynomial with evaluation one is a unit, over an arbitrary commutative ring. -/
theorem deningerRationalWittLocalization_isUnit_of_evaluationZero_eq_one
    (A : Type*) [CommRing A] (x : DeningerRationalWittLocalization A)
    (hx : deningerRationalWittEvaluationZero A x = 1) : IsUnit x := by
  obtain ⟨P, Q, hPQ⟩ :=
    IsLocalization.exists_mk'_eq (deningerRationalWittDenominators A) x
  have hP0 : P.coeff 0 = 1 := by
    rw [← hPQ] at hx
    rw [deningerRationalWittEvaluationZero,
      IsLocalization.lift_mk'_spec] at hx
    have hQ0 : (Q : Polynomial A).coeff 0 = 1 := Q.2
    simpa [hQ0] using hx
  rw [← hPQ, isUnit_iff_exists_inv]
  exact ⟨IsLocalization.mk' (DeningerRationalWittLocalization A) (Q : Polynomial A)
      ⟨P, hP0⟩,
    IsLocalization.mk'_mul_mk'_eq_one' P Q hP0⟩

/-- The literal Fatou property descends a rational Witt vector over the fraction field whenever
its power series has coefficients in the base domain. -/
theorem deningerFatouDomain_rationalWitt_exists_base
    (A : Type*) [CommRing A] [IsDomain A] (hA : DeningerFatouDomain A)
    (w : DeningerRationalWittAdditive (FractionRing A))
    (F : DeningerBigWittAdditive A)
    (hF : deningerBigWittAdditiveMap (algebraMap A (FractionRing A)) F =
      deningerRationalWittToBigWittAdditive (FractionRing A) w) :
    ∃ w0 : DeningerRationalWittAdditive A,
      deningerRationalWittAdditiveMap
          (algebraMap A (FractionRing A)) w0 = w := by
  have hseries : PowerSeries.map (algebraMap A (FractionRing A))
      (((F.1 : (PowerSeries A)ˣ) : PowerSeries A)) =
      deningerRationalWittLocalizationToPowerSeries (FractionRing A) (w.1 : _) :=
    congrArg (fun z : DeningerBigWittAdditive (FractionRing A) =>
      (((z.1 : (PowerSeries (FractionRing A))ˣ) : PowerSeries (FractionRing A)))) hF
  obtain ⟨y, hy⟩ := hA (w.1 : _) (((F.1 : (PowerSeries A)ˣ) : PowerSeries A)) hseries
  have hy0 : deningerRationalWittEvaluationZero A y = 1 := by
    apply FaithfulSMul.algebraMap_injective A (FractionRing A)
    rw [map_one]
    have hn := RingHom.congr_fun
      (deningerRationalWittEvaluationZero_natural
        (algebraMap A (FractionRing A))) y
    change deningerRationalWittEvaluationZero (FractionRing A)
        (deningerRationalWittLocalizationMap
          (algebraMap A (FractionRing A)) y) =
      algebraMap A (FractionRing A) (deningerRationalWittEvaluationZero A y) at hn
    rw [hy] at hn
    have hw0 : deningerRationalWittEvaluationZero (FractionRing A) (w.1 : _) = 1 := by
      have hw := congrArg Units.val w.2
      simpa [deningerRationalWittUnitEvaluationZero] using hw
    exact hn.symm.trans hw0
  let uy : (DeningerRationalWittLocalization A)ˣ :=
    (deningerRationalWittLocalization_isUnit_of_evaluationZero_eq_one A y hy0).unit
  let w0 : DeningerRationalWittAdditive A := ⟨uy, by
    apply Units.ext
    change deningerRationalWittEvaluationZero A y = 1
    simpa [uy, IsUnit.unit_spec] using hy0⟩
  refine ⟨w0, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change deningerRationalWittLocalizationMap
      (algebraMap A (FractionRing A)) y = (w.1 : _)
  exact hy

theorem deningerBigWittAdditiveMap_comp
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g : B →+* C) (f : A →+* B) :
    deningerBigWittAdditiveMap (g.comp f) =
      (deningerBigWittAdditiveMap g).comp (deningerBigWittAdditiveMap f) := by
  apply MonoidHom.ext
  intro F
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map (g.comp f) (((F.1 : (PowerSeries A)ˣ) : PowerSeries A)) =
    PowerSeries.map g
      (PowerSeries.map f (((F.1 : (PowerSeries A)ˣ) : PowerSeries A)))
  exact RingHom.congr_fun (PowerSeries.map_comp f g) _

theorem deningerBigWittAdditiveMap_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (deningerBigWittAdditiveMap f) := by
  intro F G hFG
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.map_injective f hf
  exact congrArg (fun z : DeningerBigWittAdditive B =>
    (((z.1 : (PowerSeries B)ˣ) : PowerSeries B))) hFG

/-- Deninger 2025, Corollary 1.10(2), on literal carriers: for an extension of domains
`A ⊆ B`, if `A` is Fatou, then `W_rat(B) ∩ W(A) = W_rat(A)` inside `W(B)`. -/
theorem deningerRationalWittFatouIntersection_iff
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (hA : DeningerFatouDomain A)
    (w : DeningerRationalWittAdditive B) :
    (∃ w0 : DeningerRationalWittAdditive A,
        deningerRationalWittAdditiveMap (algebraMap A B) w0 = w) ↔
      ∃ F0 : DeningerBigWittAdditive A,
        deningerBigWittAdditiveMap (algebraMap A B) F0 =
          deningerRationalWittToBigWittAdditive B w := by
  constructor
  · rintro ⟨w0, rfl⟩
    refine ⟨deningerRationalWittToBigWittAdditive A w0, ?_⟩
    exact deningerRationalWittToBigWittAdditive_natural (algebraMap A B) w0
  · rintro ⟨F0, hF0⟩
    letI : Algebra (FractionRing A) (FractionRing B) :=
      FractionRing.liftAlgebra A (FractionRing B)
    letI : IsScalarTower A (FractionRing A) (FractionRing B) :=
      FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
    let wL : DeningerRationalWittAdditive (FractionRing B) :=
      deningerRationalWittAdditiveMap (algebraMap B (FractionRing B)) w
    let FK : DeningerBigWittAdditive (FractionRing A) :=
      deningerBigWittAdditiveMap (algebraMap A (FractionRing A)) F0
    have hAL : deningerBigWittAdditiveMap
        (algebraMap A (FractionRing B)) F0 =
      deningerRationalWittToBigWittAdditive (FractionRing B) wL := by
      calc
        deningerBigWittAdditiveMap (algebraMap A (FractionRing B)) F0 =
            deningerBigWittAdditiveMap
              ((algebraMap B (FractionRing B)).comp (algebraMap A B)) F0 := by
                rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
        _ = deningerBigWittAdditiveMap (algebraMap B (FractionRing B))
              (deningerBigWittAdditiveMap (algebraMap A B) F0) := by
                rw [deningerBigWittAdditiveMap_comp]
                rfl
        _ = deningerBigWittAdditiveMap (algebraMap B (FractionRing B))
              (deningerRationalWittToBigWittAdditive B w) :=
                congrArg (deningerBigWittAdditiveMap
                  (algebraMap B (FractionRing B))) hF0
        _ = deningerRationalWittToBigWittAdditive (FractionRing B) wL :=
          deningerRationalWittToBigWittAdditive_natural
            (algebraMap B (FractionRing B)) w
    have hKL : deningerBigWittAdditiveMap
        (algebraMap (FractionRing A) (FractionRing B)) FK =
      deningerRationalWittToBigWittAdditive (FractionRing B) wL := by
      calc
        deningerBigWittAdditiveMap
            (algebraMap (FractionRing A) (FractionRing B)) FK =
          deningerBigWittAdditiveMap
            ((algebraMap (FractionRing A) (FractionRing B)).comp
              (algebraMap A (FractionRing A))) F0 := by
                rw [deningerBigWittAdditiveMap_comp]
                rfl
        _ = deningerBigWittAdditiveMap (algebraMap A (FractionRing B)) F0 := by
              rw [IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)]
        _ = deningerRationalWittToBigWittAdditive (FractionRing B) wL := hAL
    obtain ⟨wK, hwK⟩ :=
      (deningerRationalWittFieldIntersection_iff
        (FractionRing A) (FractionRing B) wL).2 ⟨FK, hKL⟩
    have hAK : deningerBigWittAdditiveMap
        (algebraMap A (FractionRing A)) F0 =
      deningerRationalWittToBigWittAdditive (FractionRing A) wK := by
      apply deningerBigWittAdditiveMap_injective
        (algebraMap (FractionRing A) (FractionRing B))
        (algebraMap (FractionRing A) (FractionRing B)).injective
      calc
        deningerBigWittAdditiveMap
            (algebraMap (FractionRing A) (FractionRing B))
            (deningerBigWittAdditiveMap (algebraMap A (FractionRing A)) F0) =
          deningerBigWittAdditiveMap
            (algebraMap (FractionRing A) (FractionRing B)) FK := rfl
        _ = deningerRationalWittToBigWittAdditive (FractionRing B) wL := hKL
        _ = deningerRationalWittToBigWittAdditive (FractionRing B)
            (deningerRationalWittAdditiveMap
              (algebraMap (FractionRing A) (FractionRing B)) wK) := by rw [hwK]
        _ = deningerBigWittAdditiveMap
            (algebraMap (FractionRing A) (FractionRing B))
            (deningerRationalWittToBigWittAdditive (FractionRing A) wK) :=
              (deningerRationalWittToBigWittAdditive_natural
                (algebraMap (FractionRing A) (FractionRing B)) wK).symm
    obtain ⟨wA, hwA⟩ :=
      deningerFatouDomain_rationalWitt_exists_base A hA wK F0 hAK
    refine ⟨wA, ?_⟩
    apply deningerRationalWittAdditiveMap_injective
      (algebraMap B (FractionRing B))
      (FaithfulSMul.algebraMap_injective B (FractionRing B))
    calc
      deningerRationalWittAdditiveMap (algebraMap B (FractionRing B))
          (deningerRationalWittAdditiveMap (algebraMap A B) wA) =
        deningerRationalWittAdditiveMap
          ((algebraMap B (FractionRing B)).comp (algebraMap A B)) wA := by
            rw [deningerRationalWittAdditiveMap_comp]
            rfl
      _ = deningerRationalWittAdditiveMap
          (algebraMap A (FractionRing B)) wA := by
            rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
      _ = deningerRationalWittAdditiveMap
          ((algebraMap (FractionRing A) (FractionRing B)).comp
            (algebraMap A (FractionRing A))) wA := by
            rw [IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)]
      _ = deningerRationalWittAdditiveMap
          (algebraMap (FractionRing A) (FractionRing B))
          (deningerRationalWittAdditiveMap
            (algebraMap A (FractionRing A)) wA) := by
            rw [deningerRationalWittAdditiveMap_comp]
            rfl
      _ = deningerRationalWittAdditiveMap
          (algebraMap (FractionRing A) (FractionRing B)) wK :=
            congrArg (deningerRationalWittAdditiveMap
              (algebraMap (FractionRing A) (FractionRing B))) hwA
      _ = wL := hwK
      _ = deningerRationalWittAdditiveMap
          (algebraMap B (FractionRing B)) w := rfl

end

end RHTower
