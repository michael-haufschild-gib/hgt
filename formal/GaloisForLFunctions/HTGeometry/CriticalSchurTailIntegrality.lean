import GaloisForLFunctions.HTGeometry.CriticalSchurSourceValuation
import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreIntegrality
import Mathlib.RingTheory.Polynomial.Subring

/-!
# Integrality of the actual critical tails at the Schur divisor

The Schur ramification polynomial is independent of the source scale coordinate.  Consequently
that scale is a unit at the Schur divisor.  This file develops the resulting integral-coordinate
calculus needed to reduce every geometric sheet at a Schur place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum
open MvPolynomial
open Polynomial

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- Every polynomial in the Schur coordinate ring is integral at the Schur divisor. -/
theorem criticalSchurCoordinateValuationSubring_algebraMap_mem
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalSchurSourceRing K m n) :
    algebraMap (criticalSchurSourceRing K m n)
        (FractionRing (criticalSchurSourceRing K m n)) p ∈
      criticalSchurCoordinateValuationSubring K hm hn := by
  let R := criticalSchurSourceRing K m n
  let P := criticalSchurPrimeDivisor K hm hn
  let A := Localization.AtPrime P.1
  let v := IsDiscreteValuationRing.maximalIdeal A
  change v.valuation (FractionRing R) (algebraMap R (FractionRing R) p) ≤ 1
  rw [show algebraMap R (FractionRing R) p =
      algebraMap A (FractionRing R) (algebraMap R A p) from
    IsScalarTower.algebraMap_apply R A (FractionRing R) p,
    v.valuation_of_algebraMap]
  exact v.intValuation_le_one _

/-- The scale variable does not belong to the Schur ramification prime. -/
theorem criticalSchur_scale_not_mem_ramificationIdeal
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X (0 : Fin (m + n - 1 + 1)) : criticalSchurSourceRing K m n) ∉
      criticalSchurRamificationIdeal K m n := by
  rw [criticalSchurRamificationIdeal, Ideal.mem_span_singleton]
  intro hdvd
  let p := criticalSourceSchurRamificationPolynomial K m n
  have hp : Irreducible p := irreducible_criticalSourceSchurRamificationPolynomial K hm hn
  have hX : Irreducible
      (X (0 : Fin (m + n - 1 + 1)) : criticalSchurSourceRing K m n) :=
    (MvPolynomial.X_prime (R := K) (i := (0 : Fin (m + n - 1 + 1)))).irreducible
  have hassoc : Associated p
      (X (0 : Fin (m + n - 1 + 1)) : criticalSchurSourceRing K m n) :=
    hp.associated_of_dvd hX hdvd
  have hdegree := degreeOf_le_of_dvd hassoc.dvd' hp.ne_zero
  have hpdegree : MvPolynomial.degreeOf (0 : Fin (m + n - 1 + 1)) p = 0 := by
    exact degreeOf_zero_rename_succ
      ((rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).det)
  have hXdegree : MvPolynomial.degreeOf (0 : Fin (m + n - 1 + 1))
      (X (0 : Fin (m + n - 1 + 1)) : criticalSchurSourceRing K m n) = 1 := by
    simp
  rw [hXdegree, hpdegree] at hdegree
  omega

/-- The embedded Schur scale and its inverse are both integral in the coordinate field. -/
theorem criticalSchurCoordinateValuationSubring_scale_inv_mem
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (algebraMap (criticalSchurSourceRing K m n)
        (FractionRing (criticalSchurSourceRing K m n))
        (X (0 : Fin (m + n - 1 + 1))))⁻¹ ∈
      criticalSchurCoordinateValuationSubring K hm hn := by
  let R := criticalSchurSourceRing K m n
  let P := criticalSchurPrimeDivisor K hm hn
  let A := Localization.AtPrime P.1
  let v := IsDiscreteValuationRing.maximalIdeal A
  let x : FractionRing R := algebraMap R (FractionRing R)
    (X (0 : Fin (m + n - 1 + 1)))
  have hxoutside : (X (0 : Fin (m + n - 1 + 1)) : R) ∉ P.1 := by
    exact criticalSchur_scale_not_mem_ramificationIdeal K hm hn
  have hxval : v.valuation (FractionRing R) x = 1 := by
    have hmap : x = algebraMap A (FractionRing R)
        (algebraMap R A (X (0 : Fin (m + n - 1 + 1)))) :=
      IsScalarTower.algebraMap_apply R A (FractionRing R) _
    rw [hmap, v.valuation_of_algebraMap]
    apply intValuation_eq_one_iff.mpr
    change algebraMap R A (X (0 : Fin (m + n - 1 + 1))) ∉
      IsLocalRing.maximalIdeal A
    rw [IsLocalRing.mem_maximalIdeal]
    intro hnonunit
    exact hnonunit ((IsLocalization.AtPrime.isUnit_to_map_iff A P.1 _).2 hxoutside)
  change v.valuation (FractionRing R) x⁻¹ ≤ 1
  rw [map_inv₀, hxval, inv_one]

/-! ## Integral triangular coordinate changes -/

/-- Every coefficient of a polynomial belongs to a fixed valuation subring. -/
def PolynomialCoefficientsInValuationSubring
    {E : Type*} [Field E] (O : ValuationSubring E) (P : E[X]) : Prop :=
  ∀ k, P.coeff k ∈ O

theorem polynomialCoefficientsInValuationSubring_one
    {E : Type*} [Field E] (O : ValuationSubring E) :
    PolynomialCoefficientsInValuationSubring O 1 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem PolynomialCoefficientsInValuationSubring.sub
    {E : Type*} [Field E] {O : ValuationSubring E} {P Q : E[X]}
    (hP : PolynomialCoefficientsInValuationSubring O P)
    (hQ : PolynomialCoefficientsInValuationSubring O Q) :
    PolynomialCoefficientsInValuationSubring O (P - Q) := by
  intro k
  rw [Polynomial.coeff_sub]
  exact O.sub_mem (hP k) (hQ k)

theorem PolynomialCoefficientsInValuationSubring.neg
    {E : Type*} [Field E] {O : ValuationSubring E} {P : E[X]}
    (hP : PolynomialCoefficientsInValuationSubring O P) :
    PolynomialCoefficientsInValuationSubring O (-P) := by
  intro k
  rw [Polynomial.coeff_neg]
  exact O.neg_mem _ (hP k)

theorem PolynomialCoefficientsInValuationSubring.mul
    {E : Type*} [Field E] {O : ValuationSubring E} {P Q : E[X]}
    (hP : PolynomialCoefficientsInValuationSubring O P)
    (hQ : PolynomialCoefficientsInValuationSubring O Q) :
    PolynomialCoefficientsInValuationSubring O (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact O.sum_mem fun ij hij => O.mul_mem _ _ (hP ij.1) (hQ ij.2)

theorem PolynomialCoefficientsInValuationSubring.pow
    {E : Type*} [Field E] {O : ValuationSubring E} {P : E[X]}
    (hP : PolynomialCoefficientsInValuationSubring O P) (r : ℕ) :
    PolynomialCoefficientsInValuationSubring O (P ^ r) := by
  induction r with
  | zero => simpa using polynomialCoefficientsInValuationSubring_one O
  | succ r ihr => simpa [pow_succ] using ihr.mul hP

theorem PolynomialCoefficientsInValuationSubring.sum
    {E I : Type*} [Field E] {O : ValuationSubring E}
    {s : Finset I} {P : I → E[X]}
    (hP : ∀ i ∈ s, PolynomialCoefficientsInValuationSubring O (P i)) :
    PolynomialCoefficientsInValuationSubring O (∑ i ∈ s, P i) := by
  intro k
  change (Polynomial.lcoeff E k) (∑ i ∈ s, P i) ∈ O
  rw [map_sum]
  exact O.sum_mem fun i hi => hP i hi k

theorem finiteUnitPolynomial_coefficientsInValuationSubring
    {E : Type*} [Field E] (O : ValuationSubring E)
    {L : ℕ} (u : Fin L → E) (hu : ∀ i, u i ∈ O) :
    PolynomialCoefficientsInValuationSubring O (finiteUnitPolynomial u) := by
  intro k
  rw [finiteUnitPolynomial, Polynomial.coeff_add, Polynomial.coeff_one]
  apply O.add_mem
  · split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · change (Polynomial.lcoeff E k)
      (∑ i : Fin L, Polynomial.monomial ((i : ℕ) + 1) (u i)) ∈ O
    rw [map_sum]
    apply O.sum_mem
    intro i hi
    change (Polynomial.monomial ((i : ℕ) + 1) (u i)).coeff k ∈ O
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact hu i
    · exact O.zero_mem

theorem truncatedReciprocalKernel_coefficientsInValuationSubring
    {E : Type*} [Field E] [CharZero E] (O : ValuationSubring E)
    (N : ℕ) (U : E[X])
    (hU : PolynomialCoefficientsInValuationSubring O U) :
    PolynomialCoefficientsInValuationSubring O (truncatedReciprocalKernel N U) := by
  rw [truncatedReciprocalKernel]
  apply PolynomialCoefficientsInValuationSubring.sum
  intro j hj
  exact (hU.sub (polynomialCoefficientsInValuationSubring_one O)).neg.pow j

/-- If the positive coefficients of a unit series square are integral and `2` is a unit, then the
positive coefficients of the unsquared series are integral. -/
theorem finiteUnitSquarePositive_mem_valuationSubring
    {E : Type*} [Field E] [CharZero E] (O : ValuationSubring E)
    {L : ℕ} (z : Fin L → E)
    (hsq : ∀ i, finiteUnitSquarePositive z i ∈ O)
    (htwoInv : (2 : E)⁻¹ ∈ O) :
    ∀ i, z i ∈ O := by
  intro i
  have hzmem : ∀ k (hk : k < L), z ⟨k, hk⟩ ∈ O := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        rcases k with _ | k
        · have hrel := finiteUnitSquarePositive_zero z hk
          have hsolve : z ⟨0, hk⟩ = (2 : E)⁻¹ *
              finiteUnitSquarePositive z ⟨0, hk⟩ := by
            rw [hrel]
            field_simp
          rw [hsolve]
          exact O.mul_mem _ _ htwoInv (hsq ⟨0, hk⟩)
        · let S : E := ∑ p ∈
            (Finset.HasAntidiagonal.antidiagonal (A := ℕ) k : Finset (ℕ × ℕ)),
            (finiteUnitPolynomial z).coeff (p.1 + 1) *
              (finiteUnitPolynomial z).coeff (p.2 + 1)
          have hS : S ∈ O := by
            apply O.sum_mem
            intro p hp
            apply O.mul_mem
            · rw [show (finiteUnitPolynomial z).coeff (p.1 + 1) =
                  z ⟨p.1, by
                    have hp1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                    omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z
                  ⟨p.1, by
                    have hp1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                    omega⟩]
              exact ih p.1 (by
                have hp1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                omega) (by
                have hp1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                omega)
            · rw [show (finiteUnitPolynomial z).coeff (p.2 + 1) =
                  z ⟨p.2, by
                    have hp2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                    omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z
                  ⟨p.2, by
                    have hp2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                    omega⟩]
              exact ih p.2 (by
                have hp2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                omega) (by
                have hp2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                omega)
          have hrel := finiteUnitSquarePositive_succ z hk
          have hsolve : z ⟨k + 1, hk⟩ = (2 : E)⁻¹ *
              (finiteUnitSquarePositive z ⟨k + 1, hk⟩ - S) := by
            rw [hrel]
            dsimp only [S]
            field_simp
            ring
          rw [hsolve]
          exact O.mul_mem _ _ htwoInv (O.sub_mem (hsq ⟨k + 1, hk⟩) hS)
  exact hzmem i i.isLt

/-- Integrality of a truncated reciprocal unit jet implies integrality of the original unit jet. -/
theorem finiteReciprocalPositive_reflects_mem_valuationSubring
    {E : Type*} [Field E] [CharZero E] (O : ValuationSubring E)
    {L : ℕ} (u : Fin L → E)
    (hv : ∀ i, finiteReciprocalPositive u i ∈ O) :
    ∀ i, u i ∈ O := by
  intro i
  let U := finiteUnitPolynomial u
  let Y := truncatedReciprocalKernel (L + 1) U
  let V := finiteUnitPolynomial (finiteReciprocalPositive u)
  let W := truncatedReciprocalKernel (L + 1) V
  have hU0 : U.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero u
  have hV0 : V.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero _
  have hUY : Polynomial.X ^ (L + 1) ∣ U * Y - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) U hU0
  have hUV : Polynomial.X ^ (L + 1) ∣ U * V - 1 :=
    X_pow_dvd_mul_sub_of_coeff_eq (L + 1) U V Y hUY
      (finiteUnitPolynomial_reciprocal_coeff u)
  have hVW : Polynomial.X ^ (L + 1) ∣ V * W - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) V hV0
  have hVU : Polynomial.X ^ (L + 1) ∣ V * U - 1 := by
    simpa [mul_comm] using hUV
  have hcoeff : W.coeff ((i : ℕ) + 1) = U.coeff ((i : ℕ) + 1) :=
    inverse_mod_coeff_unique (L + 1) V W U hV0 hVW hVU (by omega)
  rw [← finiteUnitPolynomial_coeff_succ u i, ← hcoeff]
  exact truncatedReciprocalKernel_coefficientsInValuationSubring O (L + 1) V
    (finiteUnitPolynomial_coefficientsInValuationSubring O _ hv) ((i : ℕ) + 1)

/-! ## The actual source coordinates are integral -/

theorem criticalSourceSchurFieldEquiv_symm_coordinate
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) :
    (criticalSourceSchurFieldEquiv K hm hn).symm
        (criticalSourceSchurCoordinates K hm hn i) =
      algebraMap (criticalSchurSourceRing K m n)
        (FractionRing (criticalSchurSourceRing K m n)) (X i) := by
  apply (criticalSourceSchurFieldEquiv K hm hn).injective
  rw [(criticalSourceSchurFieldEquiv K hm hn).apply_symm_apply,
    criticalSourceSchurFieldEquiv_algebraMap_apply]
  simp

theorem criticalSourceSchurCoordinates_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) :
    criticalSourceSchurCoordinates K hm hn i ∈
      criticalSchurSourceValuationSubring K hm hn := by
  rw [mem_criticalSchurSourceValuationSubring_iff,
    criticalSourceSchurFieldEquiv_symm_coordinate]
  exact criticalSchurCoordinateValuationSubring_algebraMap_mem K hm hn (X i)

theorem criticalSourceScale_eq_schurCoordinate_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceScale K hm hn =
      criticalSourceSchurCoordinates K hm hn 0 := by
  simp [criticalSourceScale, criticalSourceSchurCoordinates,
    criticalSourceNormalizedRaw, normalizedFiniteJet,
    criticalSourceRawReindexed, criticalSourceRaw]

theorem criticalSourceScale_inv_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSourceScale K hm hn)⁻¹ ∈
      criticalSchurSourceValuationSubring K hm hn := by
  rw [mem_criticalSchurSourceValuationSubring_iff, map_inv₀,
    criticalSourceScale_eq_schurCoordinate_zero,
    criticalSourceSchurFieldEquiv_symm_coordinate]
  exact criticalSchurCoordinateValuationSubring_scale_inv_mem K hm hn

theorem criticalSource_two_inv_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (2 : criticalSourceField K m n)⁻¹ ∈
      criticalSchurSourceValuationSubring K hm hn := by
  let e := criticalSourceSchurFieldEquiv K hm hn
  let R := criticalSchurSourceRing K m n
  let F := FractionRing R
  have heq : e.symm (2 : criticalSourceField K m n)⁻¹ =
      algebraMap R F (MvPolynomial.C ((2 : K)⁻¹)) := by
    apply e.injective
    rw [e.apply_symm_apply, criticalSourceSchurFieldEquiv_algebraMap_apply]
    simp only [MvPolynomial.aeval_C, map_inv₀, map_ofNat]
  rw [mem_criticalSchurSourceValuationSubring_iff, heq]
  exact criticalSchurCoordinateValuationSubring_algebraMap_mem K hm hn
    (MvPolynomial.C ((2 : K)⁻¹))

theorem criticalSourceReciprocalSquarePositive_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1)) :
    criticalSourceReciprocalSquarePositive K hm hn i ∈
      criticalSchurSourceValuationSubring K hm hn := by
  have h := criticalSourceSchurCoordinates_mem_sourceValuationSubring K hm hn i.rev.succ
  simpa [criticalSourceSchurCoordinates,
    criticalSourceReciprocalSquareReversed] using h

theorem criticalSourceNormalizedReciprocalPositive_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∀ i, finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn) i ∈
      criticalSchurSourceValuationSubring K hm hn := by
  let O := criticalSchurSourceValuationSubring K hm hn
  let v := finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn)
  apply finiteUnitSquarePositive_mem_valuationSubring O v
  · intro i
    change finiteUnitSquarePositive
        (finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn)) i ∈
      criticalSchurSourceValuationSubring K hm hn
    simpa only [criticalSourceReciprocalSquarePositive,
      finiteReciprocalSquarePositive] using
      criticalSourceReciprocalSquarePositive_mem_sourceValuationSubring K hm hn i
  · change (2 : criticalSourceField K m n)⁻¹ ∈
      criticalSchurSourceValuationSubring K hm hn
    exact criticalSource_two_inv_mem_sourceValuationSubring K hm hn

theorem criticalSourceNormalizedPositive_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∀ i, criticalSourceNormalizedPositive K hm hn i ∈
      criticalSchurSourceValuationSubring K hm hn :=
  finiteReciprocalPositive_reflects_mem_valuationSubring
    (criticalSchurSourceValuationSubring K hm hn)
    (criticalSourceNormalizedPositive K hm hn)
    (criticalSourceNormalizedReciprocalPositive_mem_sourceValuationSubring K hm hn)

theorem criticalSourceRawReindexed_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) :
    criticalSourceRawReindexed K hm hn i ∈
      criticalSchurSourceValuationSubring K hm hn := by
  let O := criticalSchurSourceValuationSubring K hm hn
  refine Fin.cases ?_ (fun j => ?_) i
  · have hs := criticalSourceSchurCoordinates_mem_sourceValuationSubring K hm hn 0
    rw [← criticalSourceScale_eq_schurCoordinate_zero K hm hn] at hs
    change criticalSourceRawReindexed K hm hn 0 ∈ O
    convert hs using 1
    apply Subtype.ext
    rfl
  · have hu := criticalSourceNormalizedPositive_mem_sourceValuationSubring K hm hn j
    have hs := criticalSourceSchurCoordinates_mem_sourceValuationSubring K hm hn 0
    rw [← criticalSourceScale_eq_schurCoordinate_zero K hm hn] at hs
    have heq : criticalSourceRawReindexed K hm hn j.succ =
        criticalSourceNormalizedPositive K hm hn j * criticalSourceScale K hm hn := by
      change criticalSourceRawReindexed K hm hn j.succ =
        (criticalSourceRawReindexed K hm hn j.succ /
          criticalSourceRawReindexed K hm hn 0) * criticalSourceScale K hm hn
      have hscale : criticalSourceRawReindexed K hm hn 0 =
          criticalSourceScale K hm hn := by
        apply Subtype.ext
        rfl
      rw [← hscale]
      exact (div_mul_cancel₀ _ (criticalSourceRawReindexed_zero_ne K hm hn)).symm
    rw [heq]
    exact O.mul_mem _ _ hu hs

theorem criticalSourceRaw_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n)) :
    criticalSourceRaw K m n i ∈ criticalSchurSourceValuationSubring K hm hn := by
  let i' : Fin (m + n - 1 + 1) := Fin.cast (by omega) i
  have h := criticalSourceRawReindexed_mem_sourceValuationSubring K hm hn i'
  have hcast : Fin.cast (by omega) i' = i := by
    apply Fin.ext
    rfl
  simpa only [criticalSourceRawReindexed, hcast] using h

theorem criticalSourceRecipReindexed_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) :
    criticalSourceRecip K m n (Fin.cast (by omega) i) ∈
      criticalSchurSourceValuationSubring K hm hn := by
  let O := criticalSchurSourceValuationSubring K hm hn
  refine Fin.cases ?_ (fun j => ?_) i
  · have hcoeff := criticalSourceNormalizedReciprocalPolynomial_coeff K hm hn
        (k := 0) (by omega)
    rw [criticalSourceReciprocalPolynomial_coeff K m n 0 (by omega)] at hcoeff
    have hscale := criticalSourceScale_inv_mem_sourceValuationSubring K hm hn
    have heq : criticalSourceRecip K m n (Fin.cast (by omega) (0 :
        Fin (m + n - 1 + 1))) = (criticalSourceScale K hm hn)⁻¹ := by
      have hidx : Fin.cast (by omega) (0 : Fin (m + n - 1 + 1)) =
          (⟨0, by omega⟩ : Fin (m + n)) := by
        apply Fin.ext
        rfl
      rw [hidx]
      apply eq_inv_of_mul_eq_one_right
      simpa [criticalSourceNormalizedReciprocalPolynomial] using hcoeff.symm
    rw [heq]
    exact hscale
  · have hv := criticalSourceNormalizedReciprocalPositive_mem_sourceValuationSubring
      K hm hn j
    have hscale := criticalSourceScale_inv_mem_sourceValuationSubring K hm hn
    have hcoeff := criticalSourceNormalizedReciprocalPolynomial_coeff K hm hn
      (k := (j : ℕ) + 1) (by omega)
    rw [criticalSourceReciprocalPolynomial_coeff K m n ((j : ℕ) + 1) (by omega)] at hcoeff
    have heq : criticalSourceRecip K m n (Fin.cast (by omega) j.succ) =
        (criticalSourceScale K hm hn)⁻¹ *
          finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn) j := by
      have hidx : Fin.cast (by omega) j.succ =
          (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + n)) := by
        apply Fin.ext
        rfl
      rw [hidx]
      rw [show finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn) j =
          criticalSourceScale K hm hn *
            criticalSourceRecip K m n ⟨(j : ℕ) + 1, by omega⟩ by
        simpa [criticalSourceNormalizedReciprocalPolynomial] using hcoeff]
      field_simp [criticalSourceScale_ne_zero K hm hn]
    rw [heq]
    exact O.mul_mem _ _ hscale hv

theorem criticalSourceRecip_mem_sourceValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n)) :
    criticalSourceRecip K m n i ∈ criticalSchurSourceValuationSubring K hm hn := by
  let i' : Fin (m + n - 1 + 1) := Fin.cast (by omega) i
  have h := criticalSourceRecipReindexed_mem_sourceValuationSubring K hm hn i'
  have hcast : Fin.cast (by omega) i' = i := by
    apply Fin.ext
    rfl
  simpa only [hcast] using h

/-! ## Integral models of the actual observation tails -/

theorem criticalObservationRaw_mem_observationValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    criticalObservationRaw K m n i ∈
      criticalSchurObservationValuationSubring K hm hn := by
  rw [mem_criticalSchurObservationValuationSubring_iff]
  have h := criticalSourceRaw_mem_sourceValuationSubring K hm hn
    (⟨m + (i : ℕ), by omega⟩ : Fin (m + n))
  convert h using 1
  apply Subtype.ext
  rfl

theorem criticalObservationRecip_mem_observationValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    criticalObservationRecip K m n j ∈
      criticalSchurObservationValuationSubring K hm hn := by
  rw [mem_criticalSchurObservationValuationSubring_iff]
  have h := criticalSourceRecip_mem_sourceValuationSubring K hm hn
    (⟨n + (j : ℕ), by omega⟩ : Fin (m + n))
  convert h using 1
  apply Subtype.ext
  rfl

theorem criticalObservationRawTail_coefficients_mem_observationValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    PolynomialCoefficientsInValuationSubring
      (criticalSchurObservationValuationSubring K hm hn)
      (criticalObservationRawTail K m n) := by
  intro k
  rw [criticalObservationRawTail, Polynomial.finsetSum_coeff]
  apply (criticalSchurObservationValuationSubring K hm hn).sum_mem
  intro i hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hik : k = m + (i : ℕ)
  · rw [if_pos hik]
    exact (criticalSchurObservationValuationSubring K hm hn).mul_mem _ _
      (criticalObservationRaw_mem_observationValuationSubring K hm hn i)
      (criticalSchurObservationValuationSubring K hm hn).one_mem
  · rw [if_neg hik]
    exact (criticalSchurObservationValuationSubring K hm hn).mul_mem _ _
      (criticalObservationRaw_mem_observationValuationSubring K hm hn i)
      (criticalSchurObservationValuationSubring K hm hn).zero_mem

theorem criticalObservationReciprocalTail_coefficients_mem_observationValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    PolynomialCoefficientsInValuationSubring
      (criticalSchurObservationValuationSubring K hm hn)
      (criticalObservationReciprocalTail K m n) := by
  intro k
  rw [criticalObservationReciprocalTail, Polynomial.finsetSum_coeff]
  apply (criticalSchurObservationValuationSubring K hm hn).sum_mem
  intro j hj
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hjk : k = n + (j : ℕ)
  · rw [if_pos hjk]
    exact (criticalSchurObservationValuationSubring K hm hn).mul_mem _ _
      (criticalObservationRecip_mem_observationValuationSubring K hm hn j)
      (criticalSchurObservationValuationSubring K hm hn).one_mem
  · rw [if_neg hjk]
    exact (criticalSchurObservationValuationSubring K hm hn).mul_mem _ _
      (criticalObservationRecip_mem_observationValuationSubring K hm hn j)
      (criticalSchurObservationValuationSubring K hm hn).zero_mem

/-- Integral raw observation tail at the Schur place. -/
noncomputable def criticalSchurObservationRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurObservationValuationSubring K hm hn)[X] :=
  (criticalObservationRawTail K m n).toSubring
    (criticalSchurObservationValuationSubring K hm hn).toSubring (by
      intro c hc
      obtain ⟨k, hk, hck⟩ := Polynomial.mem_coeffs_iff.mp hc
      rw [hck]
      exact criticalObservationRawTail_coefficients_mem_observationValuationSubring
        K hm hn k)

/-- Integral reciprocal observation tail at the Schur place. -/
noncomputable def criticalSchurObservationReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurObservationValuationSubring K hm hn)[X] :=
  (criticalObservationReciprocalTail K m n).toSubring
    (criticalSchurObservationValuationSubring K hm hn).toSubring (by
      intro c hc
      obtain ⟨k, hk, hck⟩ := Polynomial.mem_coeffs_iff.mp hc
      rw [hck]
      exact criticalObservationReciprocalTail_coefficients_mem_observationValuationSubring
        K hm hn k)

@[simp] theorem map_criticalSchurObservationRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurObservationRawTailIntegral K hm hn).map
        (criticalSchurObservationValuationSubring K hm hn).subtype =
      criticalObservationRawTail K m n := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map]
  exact Polynomial.coeff_toSubring _ _ _

@[simp] theorem map_criticalSchurObservationReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurObservationReciprocalTailIntegral K hm hn).map
        (criticalSchurObservationValuationSubring K hm hn).subtype =
      criticalObservationReciprocalTail K m n := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map]
  exact Polynomial.coeff_toSubring _ _ _

theorem X_pow_dvd_criticalSchurObservationRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalSchurObservationValuationSubring K hm hn)[X]) ^ m ∣
      criticalSchurObservationRawTailIntegral K hm hn := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply Subtype.ext
  have hmap := congrArg (fun P => P.coeff k)
    (map_criticalSchurObservationRawTailIntegral K hm hn)
  rw [Polynomial.coeff_map] at hmap
  have hzero := (Polynomial.X_pow_dvd_iff.mp
    (X_pow_dvd_criticalObservationRawTail K m n)) k hk
  simpa [hzero] using hmap

theorem X_pow_dvd_criticalSchurObservationReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalSchurObservationValuationSubring K hm hn)[X]) ^ n ∣
      criticalSchurObservationReciprocalTailIntegral K hm hn := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply Subtype.ext
  have hmap := congrArg (fun P => P.coeff k)
    (map_criticalSchurObservationReciprocalTailIntegral K hm hn)
  rw [Polynomial.coeff_map] at hmap
  have hzero := (Polynomial.X_pow_dvd_iff.mp
    (X_pow_dvd_criticalObservationReciprocalTail K m n)) k hk
  simpa [hzero] using hmap

end

end GaloisForLFunctions.HTGeometry
