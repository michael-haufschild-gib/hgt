import GaloisForLFunctions.RHTower.DeningerRationalWittFieldIntersection
import GaloisForLFunctions.RHTower.DeningerRationalWittPerfectFieldGaloisDescent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Counterexample to arbitrary-domain rational-Witt Galois descent

Deninger 2025, Theorem 1.2, asserts a perfect-quotient-field equality between `W_rat(A)` and
the Galois-fixed reduced monoid algebra of the absolute normalization for every integral domain.
This module proves that the arbitrary-domain statement is false without a normality hypothesis.

Take the cusp ring

`A = {P ∈ ℚ[X] | coeff_X(P) = 0} = ℚ[X²,X³]`.

In its fraction field, `t = X³/X²` satisfies `t² = X²`, hence is integral over `A`, but `t ∉ A`.
The Teichmüller vector `[t]` therefore comes from both the normalization and the quotient field,
and its lift to the algebraic closure is absolute-Galois fixed.  Nevertheless it cannot come from
`W_rat(A)`: the coefficient of `T` in any base rational Witt vector lies in `A`, whereas that of
`[t]` is `-t`.

The module also proves the sharp general survivor: if every integral quotient-field element has a
Teichmüller preimage from `W_rat(A)`, then every such element already lies in `A`.  Thus the claimed
descent property forces integral closedness; normality is not optional.
-/

namespace RHTower

noncomputable section

theorem deningerRationalWittTeichmullerPreimage_exists_coefficient
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : B)
    (h : ∃ w : DeningerRationalWittAdditive A,
      deningerRationalWittAdditiveMap f w =
        deningerRationalWittTeichmuller x) :
    ∃ a : A, f a = x := by
  obtain ⟨w, hw⟩ := h
  have hs := congrArg
    (fun z : DeningerRationalWittAdditive B =>
      deningerRationalWittLocalizationToPowerSeries B (z.1 : _)) hw
  have hn := RingHom.congr_fun
    (deningerRationalWittLocalizationToPowerSeries_natural f) (w.1 : _)
  change deningerRationalWittLocalizationToPowerSeries B
      (deningerRationalWittLocalizationMap f (w.1 : _)) =
    PowerSeries.map f
      (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) at hn
  change deningerRationalWittLocalizationToPowerSeries B
      (deningerRationalWittLocalizationMap f (w.1 : _)) = _ at hs
  have hs' : PowerSeries.map f
      (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) =
    deningerRationalWittLocalizationToPowerSeries B
      ((deningerRationalWittTeichmuller x).1 : _) := hn.symm.trans hs
  have hc := congrArg (PowerSeries.coeff 1) hs'
  simp [deningerRationalWittTeichmuller,
    deningerRationalWittTeichmullerUnit,
    deningerRationalWittTeichmullerPolynomial,
    deningerRationalWittLocalizationToPowerSeries,
    IsLocalization.lift_eq] at hc
  refine ⟨-PowerSeries.coeff 1
    (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)), ?_⟩
  unfold deningerRationalWittLocalizationToPowerSeries
  rw [map_neg, hc, neg_neg]

theorem deningerRationalWittTeichmullerDescent_implies_integralClosedness
    (A : Type*) [CommRing A] [IsDomain A]
    (h : ∀ x : FractionRing A, IsIntegral A x →
      ∃ w : DeningerRationalWittAdditive A,
        deningerRationalWittAdditiveMap
            (algebraMap A (FractionRing A)) w =
          deningerRationalWittTeichmuller x) :
    ∀ x : FractionRing A, IsIntegral A x →
      ∃ a : A, algebraMap A (FractionRing A) a = x := by
  intro x hx
  exact deningerRationalWittTeichmullerPreimage_exists_coefficient
    (algebraMap A (FractionRing A)) x (h x hx)

def deningerCuspSubring (k : Type*) [Field k] : Subring (Polynomial k) where
  carrier := {P | P.coeff 1 = 0}
  zero_mem' := by change (0 : Polynomial k).coeff 1 = 0; simp
  one_mem' := by change (1 : Polynomial k).coeff 1 = 0; simp [Polynomial.coeff_one]
  add_mem' {P Q} hP hQ := by
    change P.coeff 1 = 0 at hP
    change Q.coeff 1 = 0 at hQ
    change (P + Q).coeff 1 = 0
    simp [hP, hQ]
  neg_mem' {P} hP := by
    change P.coeff 1 = 0 at hP
    change (-P).coeff 1 = 0
    simp [hP]
  mul_mem' {P Q} hP hQ := by
    change P.coeff 1 = 0 at hP
    change Q.coeff 1 = 0 at hQ
    change (P * Q).coeff 1 = 0
    rw [Polynomial.mul_coeff_one, hP, hQ]
    simp

abbrev DeningerCuspRing := deningerCuspSubring ℚ

def deningerCuspX2 : DeningerCuspRing :=
  ⟨Polynomial.X ^ (2 : ℕ), by
    change (Polynomial.X ^ (2 : ℕ) : Polynomial ℚ).coeff 1 = 0
    simp [Polynomial.coeff_X_pow]⟩

def deningerCuspX3 : DeningerCuspRing :=
  ⟨Polynomial.X ^ (3 : ℕ), by
    change (Polynomial.X ^ (3 : ℕ) : Polynomial ℚ).coeff 1 = 0
    simp [Polynomial.coeff_X_pow]⟩

theorem deningerCuspX2_ne_zero : deningerCuspX2 ≠ 0 := by
  intro h
  have hc := congrArg (fun P : DeningerCuspRing => P.1.coeff 2) h
  simp [deningerCuspX2] at hc

noncomputable def deningerCuspT : FractionRing DeningerCuspRing :=
  algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) deningerCuspX3 /
    algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) deningerCuspX2

theorem deningerCuspX3_sq_eq_X2_cubed : deningerCuspX3 ^ (2 : ℕ) = deningerCuspX2 ^ (3 : ℕ) := by
  apply Subtype.ext
  simp [deningerCuspX2, deningerCuspX3]
  ring

theorem deningerCuspT_sq : deningerCuspT ^ (2 : ℕ) =
    algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) deningerCuspX2 := by
  have hx2 : algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) deningerCuspX2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr deningerCuspX2_ne_zero
  rw [deningerCuspT, div_pow]
  field_simp
  simpa using congrArg (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing))
    deningerCuspX3_sq_eq_X2_cubed

theorem deningerCuspT_isIntegral : IsIntegral DeningerCuspRing deningerCuspT := by
  let P : Polynomial DeningerCuspRing :=
    Polynomial.X ^ (2 : ℕ) - Polynomial.C deningerCuspX2
  refine ⟨P, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C deningerCuspX2 two_ne_zero
  · simp [P, deningerCuspT_sq]

theorem deningerCuspT_not_in_base :
    ¬ ∃ a : DeningerCuspRing,
      algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) a = deningerCuspT := by
  rintro ⟨a, ha⟩
  have hx2 : algebraMap DeningerCuspRing (FractionRing DeningerCuspRing) deningerCuspX2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr deningerCuspX2_ne_zero
  have hmul : a * deningerCuspX2 = deningerCuspX3 := by
    apply IsFractionRing.injective DeningerCuspRing (FractionRing DeningerCuspRing)
    rw [map_mul, ha, deningerCuspT]
    exact div_mul_cancel₀ _ hx2
  have hc := congrArg (fun z : DeningerCuspRing => z.1.coeff 3) hmul
  change (a.1 * Polynomial.X ^ (2 : ℕ)).coeff 3 =
    (Polynomial.X ^ (3 : ℕ) : Polynomial ℚ).coeff 3 at hc
  rw [Polynomial.coeff_mul_X_pow] at hc
  simp [Polynomial.coeff_X_pow] at hc
  exact one_ne_zero (hc.symm.trans a.2)

abbrev DeningerCuspNormalization :=
  integralClosure DeningerCuspRing (FractionRing DeningerCuspRing)

noncomputable def deningerCuspIntegralT : DeningerCuspNormalization :=
  ⟨deningerCuspT,
    (mem_integralClosure_iff DeningerCuspRing (FractionRing DeningerCuspRing)).mpr
      deningerCuspT_isIntegral⟩

theorem deningerCuspTeichmuller_exists_normalization_preimage :
    ∃ w : DeningerRationalWittAdditive DeningerCuspNormalization,
      deningerRationalWittAdditiveMap
          (integralClosure DeningerCuspRing (FractionRing DeningerCuspRing)).val.toRingHom w =
        deningerRationalWittTeichmuller deningerCuspT := by
  refine ⟨deningerRationalWittTeichmuller deningerCuspIntegralT, ?_⟩
  rw [deningerRationalWittAdditiveMap_teichmuller]
  rfl

theorem deningerCuspTeichmuller_no_base_preimage :
    ¬ ∃ w : DeningerRationalWittAdditive DeningerCuspRing,
      deningerRationalWittAdditiveMap
          (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing)) w =
        deningerRationalWittTeichmuller deningerCuspT := by
  rintro ⟨w, hw⟩
  have hs := congrArg
    (fun z : DeningerRationalWittAdditive (FractionRing DeningerCuspRing) =>
      deningerRationalWittLocalizationToPowerSeries (FractionRing DeningerCuspRing)
        (z.1 : _)) hw
  have hs' :
      PowerSeries.map (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing))
          (deningerRationalWittLocalizationToPowerSeries DeningerCuspRing (w.1 : _)) =
        deningerRationalWittLocalizationToPowerSeries (FractionRing DeningerCuspRing)
          ((deningerRationalWittTeichmuller deningerCuspT).1 : _) := by
    have hn := RingHom.congr_fun
      (deningerRationalWittLocalizationToPowerSeries_natural
        (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing))) (w.1 : _)
    change deningerRationalWittLocalizationToPowerSeries (FractionRing DeningerCuspRing)
        (deningerRationalWittLocalizationMap
          (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing)) (w.1 : _)) =
      PowerSeries.map (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing))
        (deningerRationalWittLocalizationToPowerSeries DeningerCuspRing (w.1 : _)) at hn
    change deningerRationalWittLocalizationToPowerSeries (FractionRing DeningerCuspRing)
        (deningerRationalWittLocalizationMap
          (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing)) (w.1 : _)) = _ at hs
    exact hn.symm.trans hs
  have hc := congrArg (PowerSeries.coeff 1) hs'
  simp [deningerRationalWittTeichmuller,
    deningerRationalWittTeichmullerUnit,
    deningerRationalWittTeichmullerPolynomial,
    deningerRationalWittLocalizationToPowerSeries,
    IsLocalization.lift_eq] at hc
  apply deningerCuspT_not_in_base
  refine ⟨-PowerSeries.coeff 1
    (deningerRationalWittLocalizationToPowerSeries DeningerCuspRing (w.1 : _)), ?_⟩
  unfold deningerRationalWittLocalizationToPowerSeries
  rw [map_neg, hc, neg_neg]

theorem deningerCuspNormalization_intersection_strict :
    (∃ w : DeningerRationalWittAdditive DeningerCuspNormalization,
        deningerRationalWittAdditiveMap
            (integralClosure DeningerCuspRing (FractionRing DeningerCuspRing)).val.toRingHom w =
          deningerRationalWittTeichmuller deningerCuspT) ∧
      ¬ ∃ w : DeningerRationalWittAdditive DeningerCuspRing,
        deningerRationalWittAdditiveMap
            (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing)) w =
          deningerRationalWittTeichmuller deningerCuspT :=
  ⟨deningerCuspTeichmuller_exists_normalization_preimage,
    deningerCuspTeichmuller_no_base_preimage⟩

abbrev DeningerCuspAlgebraicClosure := AlgebraicClosure (FractionRing DeningerCuspRing)

abbrev DeningerCuspAbsoluteNormalization :=
  integralClosure DeningerCuspRing DeningerCuspAlgebraicClosure

noncomputable def deningerCuspTBar : DeningerCuspAlgebraicClosure :=
  algebraMap (FractionRing DeningerCuspRing) DeningerCuspAlgebraicClosure deningerCuspT

theorem deningerCuspTBar_isIntegral : IsIntegral DeningerCuspRing deningerCuspTBar := by
  exact deningerCuspT_isIntegral.map
    (IsScalarTower.toAlgHom DeningerCuspRing
      (FractionRing DeningerCuspRing) DeningerCuspAlgebraicClosure)

noncomputable def deningerCuspAbsoluteIntegralT : DeningerCuspAbsoluteNormalization :=
  ⟨deningerCuspTBar,
    (mem_integralClosure_iff DeningerCuspRing DeningerCuspAlgebraicClosure).mpr
      deningerCuspTBar_isIntegral⟩

theorem deningerCuspTeichmuller_exists_absoluteNormalization_preimage :
    ∃ w : DeningerRationalWittAdditive DeningerCuspAbsoluteNormalization,
      deningerRationalWittAdditiveMap
          (integralClosure DeningerCuspRing DeningerCuspAlgebraicClosure).val.toRingHom w =
        deningerRationalWittTeichmuller deningerCuspTBar := by
  refine ⟨deningerRationalWittTeichmuller deningerCuspAbsoluteIntegralT, ?_⟩
  rw [deningerRationalWittAdditiveMap_teichmuller]
  rfl

theorem deningerCuspTeichmuller_no_absolute_base_preimage :
    ¬ ∃ w : DeningerRationalWittAdditive DeningerCuspRing,
      deningerRationalWittAdditiveMap
          (algebraMap DeningerCuspRing DeningerCuspAlgebraicClosure) w =
        deningerRationalWittTeichmuller deningerCuspTBar := by
  rintro ⟨w, hw⟩
  apply deningerCuspTeichmuller_no_base_preimage
  refine ⟨w, ?_⟩
  apply deningerRationalWittAdditiveMap_injective
    (algebraMap (FractionRing DeningerCuspRing) DeningerCuspAlgebraicClosure)
    (FaithfulSMul.algebraMap_injective _ _)
  calc
    deningerRationalWittAdditiveMap
        (algebraMap (FractionRing DeningerCuspRing) DeningerCuspAlgebraicClosure)
        (deningerRationalWittAdditiveMap
          (algebraMap DeningerCuspRing (FractionRing DeningerCuspRing)) w) =
      deningerRationalWittAdditiveMap
        (algebraMap DeningerCuspRing DeningerCuspAlgebraicClosure) w := by
          rw [← MonoidHom.comp_apply, ← deningerRationalWittAdditiveMap_comp]
          congr 2
    _ = deningerRationalWittTeichmuller deningerCuspTBar := hw
    _ = deningerRationalWittAdditiveMap
        (algebraMap (FractionRing DeningerCuspRing) DeningerCuspAlgebraicClosure)
        (deningerRationalWittTeichmuller deningerCuspT) := by
          rw [deningerRationalWittAdditiveMap_teichmuller]
          rfl

theorem deningerCuspPerfectGaloisFixed_counterexample :
    (∀ g : DeningerRationalWittAbsoluteGalois (FractionRing DeningerCuspRing),
      deningerRationalWittLiteralGaloisAction (FractionRing DeningerCuspRing) g
          (deningerRationalWittPerfectBaseLift (FractionRing DeningerCuspRing)
            (deningerRationalWittTeichmuller deningerCuspT)) =
        deningerRationalWittPerfectBaseLift (FractionRing DeningerCuspRing)
          (deningerRationalWittTeichmuller deningerCuspT)) ∧
      (∃ w : DeningerRationalWittAdditive DeningerCuspAbsoluteNormalization,
        deningerRationalWittAdditiveMap
            (integralClosure DeningerCuspRing DeningerCuspAlgebraicClosure).val.toRingHom w =
          deningerRationalWittTeichmuller deningerCuspTBar) ∧
      ¬ ∃ w : DeningerRationalWittAdditive DeningerCuspRing,
        deningerRationalWittAdditiveMap
            (algebraMap DeningerCuspRing DeningerCuspAlgebraicClosure) w =
          deningerRationalWittTeichmuller deningerCuspTBar :=
  ⟨fun g => deningerRationalWittPerfectBaseLift_galoisFixed
      (FractionRing DeningerCuspRing) (deningerRationalWittTeichmuller deningerCuspT) g,
    deningerCuspTeichmuller_exists_absoluteNormalization_preimage,
    deningerCuspTeichmuller_no_absolute_base_preimage⟩

end
end RHTower

