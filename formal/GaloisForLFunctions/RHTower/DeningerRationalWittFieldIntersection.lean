import GaloisForLFunctions.RHTower.DeningerRationalWittAICDomainComparison
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Rational Witt vectors and extension-field intersection

This module proves Deninger 2025, Corollary 1.10(1) (source label `t1.8`), on the literal rational-Witt and big-Witt
additive carriers.  For every field extension `L/K`, an element of `W_rat(L)` lies in the image of
`W(K)` if and only if it lies in the image of `W_rat(K)`.

The proof gives a direct descent mechanism.  Split the scalar embedding by a `K`-linear
retraction `L → K`, apply it coefficientwise to a normalized rational presentation `P/Q`, and
use linearity to commute the retraction with multiplication by the base power series.  The
retracted numerator and denominator remain normalized and represent the original series.  This
avoids importing the paper's Hankel-rank characterization and proves the full intersection result
on the actual localized-polynomial carrier.
-/

namespace RHTower

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

noncomputable def deningerFieldExtensionLinearRetraction : L →ₗ[K] K :=
  (Algebra.linearMap K L).leftInverse

@[simp] theorem deningerFieldExtensionLinearRetraction_algebraMap (x : K) :
    deningerFieldExtensionLinearRetraction K L (algebraMap K L x) = x := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L)) x

@[simp] theorem deningerFieldExtensionLinearRetraction_one : deningerFieldExtensionLinearRetraction K L (1 : L) = 1 := by
  rw [← map_one (algebraMap K L), deningerFieldExtensionLinearRetraction_algebraMap]

noncomputable def deningerFieldExtensionPolynomialRetract (P : Polynomial L) : Polynomial K :=
  P.sum fun n a => Polynomial.monomial n (deningerFieldExtensionLinearRetraction K L a)

@[simp] theorem deningerFieldExtensionPolynomialRetract_coeff (P : Polynomial L) (n : ℕ) :
    (deningerFieldExtensionPolynomialRetract K L P).coeff n =
      deningerFieldExtensionLinearRetraction K L (P.coeff n) := by
  classical
  unfold deningerFieldExtensionPolynomialRetract
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · exact fun h => (h hn).elim
  · have hcoeff : P.coeff n = 0 := by
      simpa [Polynomial.mem_support_iff] using hn
    rw [hcoeff, map_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := fun h => hn (h ▸ hb)
    simp [Polynomial.coeff_monomial, hbn]

@[simp] theorem deningerFieldExtensionPolynomialRetract_map (P : Polynomial K) :
    deningerFieldExtensionPolynomialRetract K L (P.map (algebraMap K L)) = P := by
  ext n
  simp

noncomputable def deningerFieldExtensionPowerSeriesRetract (F : PowerSeries L) : PowerSeries K :=
  PowerSeries.mk fun n => deningerFieldExtensionLinearRetraction K L (PowerSeries.coeff n F)

@[simp] theorem deningerFieldExtensionPowerSeriesRetract_coeff (F : PowerSeries L) (n : ℕ) :
    PowerSeries.coeff n (deningerFieldExtensionPowerSeriesRetract K L F) =
      deningerFieldExtensionLinearRetraction K L (PowerSeries.coeff n F) := by
  simp [deningerFieldExtensionPowerSeriesRetract]

@[simp] theorem deningerFieldExtensionPowerSeriesRetract_map (F : PowerSeries K) :
    deningerFieldExtensionPowerSeriesRetract K L (PowerSeries.map (algebraMap K L) F) = F := by
  apply PowerSeries.ext
  intro n
  simp

theorem deningerFieldExtensionPowerSeriesRetract_mul_map
    (F : PowerSeries L) (G : PowerSeries K) :
    deningerFieldExtensionPowerSeriesRetract K L
        (F * PowerSeries.map (algebraMap K L) G) =
      deningerFieldExtensionPowerSeriesRetract K L F * G := by
  apply PowerSeries.ext
  intro n
  simp only [deningerFieldExtensionPowerSeriesRetract_coeff, PowerSeries.coeff_mul,
    PowerSeries.coeff_map]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [mul_comm, ← Algebra.smul_def, map_smul]
  simp [mul_comm]

@[simp] theorem deningerFieldExtensionPowerSeriesRetract_coe_polynomial (P : Polynomial L) :
    deningerFieldExtensionPowerSeriesRetract K L (P : PowerSeries L) =
      (deningerFieldExtensionPolynomialRetract K L P : PowerSeries K) := by
  apply PowerSeries.ext
  intro n
  simp

noncomputable def deningerBigWittAdditiveMap
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    DeningerBigWittAdditive A →* DeningerBigWittAdditive B where
  toFun w :=
    ⟨Units.map (PowerSeries.map f) w.1, by
      apply Units.ext
      have hw := congrArg Units.val w.2
      change PowerSeries.constantCoeff ((w.1 : (PowerSeries A)ˣ) : PowerSeries A) = 1 at hw
      change PowerSeries.constantCoeff
        (PowerSeries.map f (((w.1 : (PowerSeries A)ˣ) : PowerSeries A))) = 1
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hw]
      exact map_one f⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem deningerBigWittAdditiveMap_val
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (w : DeningerBigWittAdditive A) :
    ((((deningerBigWittAdditiveMap f w).1 : (PowerSeries B)ˣ) : PowerSeries B)) =
      PowerSeries.map f (((w.1 : (PowerSeries A)ˣ) : PowerSeries A)) := by
  rfl

theorem deningerRationalWittToBigWittAdditive_natural
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (w : DeningerRationalWittAdditive A) :
    deningerBigWittAdditiveMap f (deningerRationalWittToBigWittAdditive A w) =
      deningerRationalWittToBigWittAdditive B
        (deningerRationalWittAdditiveMap f w) := by
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map f
      (deningerRationalWittLocalizationToPowerSeries A (w.1 : _)) =
    deningerRationalWittLocalizationToPowerSeries B
      (deningerRationalWittLocalizationMap f (w.1 : _))
  exact RingHom.congr_fun
    (deningerRationalWittLocalizationToPowerSeries_natural f).symm (w.1 : _)

theorem deningerRationalWittFieldIntersection_exists_base
    (w : DeningerRationalWittAdditive L) (F : PowerSeries K)
    (hF : PowerSeries.map (algebraMap K L) F =
      deningerRationalWittLocalizationToPowerSeries L (w.1 : _)) :
    ∃ w0 : DeningerRationalWittAdditive K,
      deningerRationalWittAdditiveMap (algebraMap K L) w0 = w := by
  obtain ⟨P, Q, hQmem, hP, hQ, hwval⟩ :=
    deningerRationalWittAdditive_exists_normalized_fraction L w
  let P0 := deningerFieldExtensionPolynomialRetract K L P
  let Q0 := deningerFieldExtensionPolynomialRetract K L Q
  have hP0 : P0.coeff 0 = 1 := by simp [P0, hP]
  have hQ0 : Q0.coeff 0 = 1 := by simp [Q0, hQ]
  have hwPQ := hwval
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at hwPQ
  have hwPQps := congrArg (deningerRationalWittLocalizationToPowerSeries L) hwPQ
  have hwPQps' : (P : PowerSeries L) =
      deningerRationalWittLocalizationToPowerSeries L (w.1 : _) *
        (Q : PowerSeries L) := by
    simpa [deningerRationalWittLocalizationToPowerSeries,
      IsLocalization.lift_eq] using hwPQps
  rw [← hF] at hwPQps'
  have hP0Q0 : (P0 : PowerSeries K) = F * (Q0 : PowerSeries K) := by
    calc
      (P0 : PowerSeries K) = deningerFieldExtensionPowerSeriesRetract K L (P : PowerSeries L) := by
        rw [deningerFieldExtensionPowerSeriesRetract_coe_polynomial]
      _ = deningerFieldExtensionPowerSeriesRetract K L
          (PowerSeries.map (algebraMap K L) F * (Q : PowerSeries L)) :=
        congrArg (deningerFieldExtensionPowerSeriesRetract K L) hwPQps'
      _ = deningerFieldExtensionPowerSeriesRetract K L
          ((Q : PowerSeries L) * PowerSeries.map (algebraMap K L) F) := by rw [mul_comm]
      _ = deningerFieldExtensionPowerSeriesRetract K L (Q : PowerSeries L) * F :=
        deningerFieldExtensionPowerSeriesRetract_mul_map K L _ _
      _ = F * (Q0 : PowerSeries K) := by rw [deningerFieldExtensionPowerSeriesRetract_coe_polynomial, mul_comm]
  let w0 := deningerRationalWittNormalizedFraction P0 Q0 hP0 hQ0
  have hw0PQloc :
      (w0.1 : DeningerRationalWittLocalization K) *
          algebraMap (Polynomial K) (DeningerRationalWittLocalization K) Q0 =
        algebraMap (Polynomial K) (DeningerRationalWittLocalization K) P0 := by
    have hw0val := deningerRationalWittNormalizedFraction_val P0 Q0 hP0 hQ0
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul] at hw0val
    exact hw0val.symm
  have hw0PQps := congrArg (deningerRationalWittLocalizationToPowerSeries K) hw0PQloc
  have hw0PQps' : deningerRationalWittLocalizationToPowerSeries K (w0.1 : _) *
      (Q0 : PowerSeries K) = (P0 : PowerSeries K) := by
    simpa [deningerRationalWittLocalizationToPowerSeries,
      IsLocalization.lift_eq] using hw0PQps
  have hw0series :
      deningerRationalWittLocalizationToPowerSeries K (w0.1 : _) = F := by
    apply (show IsUnit (Q0 : PowerSeries K) by
      rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe]
      simp [hQ0]).mul_right_cancel
    rw [hw0PQps', hP0Q0]
  refine ⟨w0, ?_⟩
  apply deningerRationalWittToBigWittAdditive_injective L
  rw [← deningerRationalWittToBigWittAdditive_natural]
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map (algebraMap K L)
      (deningerRationalWittLocalizationToPowerSeries K (w0.1 : _)) =
    deningerRationalWittLocalizationToPowerSeries L (w.1 : _)
  rw [← hF]
  exact congrArg (PowerSeries.map (algebraMap K L)) hw0series

theorem deningerRationalWittFieldIntersection_iff (w : DeningerRationalWittAdditive L) :
    (∃ w0 : DeningerRationalWittAdditive K,
        deningerRationalWittAdditiveMap (algebraMap K L) w0 = w) ↔
      ∃ F0 : DeningerBigWittAdditive K,
        deningerBigWittAdditiveMap (algebraMap K L) F0 =
          deningerRationalWittToBigWittAdditive L w := by
  constructor
  · rintro ⟨w0, rfl⟩
    refine ⟨deningerRationalWittToBigWittAdditive K w0, ?_⟩
    exact deningerRationalWittToBigWittAdditive_natural (algebraMap K L) w0
  · rintro ⟨F0, hF0⟩
    apply deningerRationalWittFieldIntersection_exists_base K L w
      (((F0.1 : (PowerSeries K)ˣ) : PowerSeries K))
    exact congrArg
      (fun z : DeningerBigWittAdditive L =>
        (((z.1 : (PowerSeries L)ˣ) : PowerSeries L))) hF0

end
end RHTower
