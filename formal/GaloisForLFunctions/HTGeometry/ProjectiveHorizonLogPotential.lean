import GaloisForLFunctions.HTGeometry.ProjectiveHorizonExactLagrangian
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown

open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry

abbrev LogDual (K : Type*) := TrivSqZeroExt K K

noncomputable def dualPolynomialFst {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) : Polynomial K :=
  P.map (TrivSqZeroExt.fstHom K K K).toRingHom

noncomputable def dualPolynomialSnd {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) : Polynomial K :=
  P.sum fun n a => Polynomial.monomial n a.snd

@[simp]
theorem dualPolynomialSnd_coeff {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) (n : ℕ) :
    (dualPolynomialSnd P).coeff n = (P.coeff n).snd := by
  classical
  rw [dualPolynomialSnd, Polynomial.coeff_sum, Polynomial.sum_def]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · intro hnot
      exact (hnot hn).elim
  · have hc : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    rw [hc, TrivSqZeroExt.snd_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by
      intro h
      subst h
      exact hn hb
    simp [Polynomial.coeff_monomial, hbn]

@[simp]
theorem dualPolynomialFst_coeff {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) (n : ℕ) :
    (dualPolynomialFst P).coeff n = (P.coeff n).fst := by
  simp [dualPolynomialFst]

noncomputable def dualPolynomialLift {K : Type*} [CommRing K]
    (P dP : Polynomial K) : Polynomial (LogDual K) :=
  P.map (TrivSqZeroExt.inlHom K K) +
    Polynomial.C (TrivSqZeroExt.inr (R := K) (1 : K)) *
      dP.map (TrivSqZeroExt.inlHom K K)

@[simp]
theorem dualPolynomialLift_coeff_fst {K : Type*} [CommRing K]
    (P dP : Polynomial K) (n : ℕ) :
    ((dualPolynomialLift P dP).coeff n).fst = P.coeff n := by
  simp [dualPolynomialLift]

@[simp]
theorem dualPolynomialLift_coeff_snd {K : Type*} [CommRing K]
    (P dP : Polynomial K) (n : ℕ) :
    ((dualPolynomialLift P dP).coeff n).snd = dP.coeff n := by
  simp [dualPolynomialLift]

@[simp]
theorem dualPolynomialFst_lift {K : Type*} [CommRing K]
    (P dP : Polynomial K) :
    dualPolynomialFst (dualPolynomialLift P dP) = P := by
  ext n
  simp

@[simp]
theorem dualPolynomialSnd_lift {K : Type*} [CommRing K]
    (P dP : Polynomial K) :
    dualPolynomialSnd (dualPolynomialLift P dP) = dP := by
  ext n
  simp

theorem dualPolynomialSnd_add {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialSnd (P + Q) = dualPolynomialSnd P + dualPolynomialSnd Q := by
  ext n
  simp [coeff_add, TrivSqZeroExt.snd_add]

theorem dualPolynomialSnd_neg {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) :
    dualPolynomialSnd (-P) = -dualPolynomialSnd P := by
  ext n
  simp

theorem dualPolynomialSnd_sub {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialSnd (P - Q) = dualPolynomialSnd P - dualPolynomialSnd Q := by
  rw [sub_eq_add_neg, dualPolynomialSnd_add, dualPolynomialSnd_neg]
  rfl

theorem dualPolynomialSnd_mul {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialSnd (P * Q) =
      dualPolynomialFst P * dualPolynomialSnd Q +
        dualPolynomialSnd P * dualPolynomialFst Q := by
  ext n
  simp only [dualPolynomialSnd_coeff, coeff_mul,
    dualPolynomialFst_coeff, coeff_add]
  change (TrivSqZeroExt.sndHom K K)
      (∑ x ∈ Finset.antidiagonal n, P.coeff x.1 * Q.coeff x.2) = _
  rw [map_sum]
  change (∑ x ∈ Finset.antidiagonal n,
      (P.coeff x.1 * Q.coeff x.2).snd) = _
  simp only [TrivSqZeroExt.snd_mul, smul_eq_mul,
    op_smul_eq_smul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact mul_comm _ _

@[simp]
theorem dualPolynomialSnd_zero {K : Type*} [CommRing K] :
    dualPolynomialSnd (0 : Polynomial (LogDual K)) = 0 := by
  ext n
  simp

@[simp]
theorem dualPolynomialSnd_one {K : Type*} [CommRing K] :
    dualPolynomialSnd (1 : Polynomial (LogDual K)) = 0 := by
  ext n
  by_cases hn : n = 0 <;> simp [Polynomial.coeff_one, hn]

@[simp]
theorem dualPolynomialFst_add {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialFst (P + Q) = dualPolynomialFst P + dualPolynomialFst Q := by
  simp [dualPolynomialFst]

@[simp]
theorem dualPolynomialFst_sub {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialFst (P - Q) = dualPolynomialFst P - dualPolynomialFst Q := by
  simp [dualPolynomialFst]

@[simp]
theorem dualPolynomialFst_mul {K : Type*} [CommRing K]
    (P Q : Polynomial (LogDual K)) :
    dualPolynomialFst (P * Q) = dualPolynomialFst P * dualPolynomialFst Q := by
  simp [dualPolynomialFst]

@[simp]
theorem dualPolynomialFst_pow {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) (n : ℕ) :
    dualPolynomialFst (P ^ n) = (dualPolynomialFst P) ^ n := by
  simp [dualPolynomialFst]

@[simp]
theorem dualPolynomialFst_zero {K : Type*} [CommRing K] :
    dualPolynomialFst (0 : Polynomial (LogDual K)) = 0 := by
  simp [dualPolynomialFst]

@[simp]
theorem dualPolynomialFst_one {K : Type*} [CommRing K] :
    dualPolynomialFst (1 : Polynomial (LogDual K)) = 1 := by
  simp [dualPolynomialFst]

noncomputable def dualPolynomialRingHom {K : Type*} [CommRing K] :
    Polynomial (LogDual K) →+* LogDual (Polynomial K) where
  toFun P := (dualPolynomialFst P, dualPolynomialSnd P)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · simp
  map_mul' P Q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [dualPolynomialSnd_mul, TrivSqZeroExt.snd_mul,
        smul_eq_mul, add_comm]
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' P Q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [dualPolynomialSnd_add]

theorem dualPolynomialSnd_pow {K : Type*} [CommRing K]
    (P : Polynomial (LogDual K)) (n : ℕ) :
    dualPolynomialSnd (P ^ n) =
      n • (dualPolynomialFst P) ^ n.pred * dualPolynomialSnd P := by
  have h := congrArg TrivSqZeroExt.snd
    ((dualPolynomialRingHom (K := K)).map_pow P n)
  simpa [dualPolynomialRingHom, nsmul_eq_mul, mul_assoc] using h

noncomputable def logarithmicWeight (K : Type*) [Field K] [CharZero K]
    (k : ℕ) : K :=
  if k = 0 then 0 else (-1 : K) ^ (k + 1) / (k : K)

noncomputable def truncatedLogCoeff {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K) : K :=
  ∑ j ∈ Finset.range N,
    logarithmicWeight K (j + 1) * ((P - 1) ^ (j + 1)).coeff N

noncomputable def dualTruncatedLogCoeff {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial (LogDual K)) : LogDual K :=
  ∑ j ∈ Finset.range N,
    TrivSqZeroExt.inl (logarithmicWeight K (j + 1)) *
      ((P - 1) ^ (j + 1)).coeff N

theorem dualTruncatedLogCoeff_snd {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial (LogDual K)) :
    (dualTruncatedLogCoeff N P).snd =
      ∑ j ∈ Finset.range N,
        logarithmicWeight K (j + 1) *
          (dualPolynomialSnd ((P - 1) ^ (j + 1))).coeff N := by
  rw [dualTruncatedLogCoeff]
  change (TrivSqZeroExt.sndHom K K)
      (∑ j ∈ Finset.range N,
        TrivSqZeroExt.inl (logarithmicWeight K (j + 1)) *
          ((P - 1) ^ (j + 1)).coeff N) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (TrivSqZeroExt.inl (logarithmicWeight K (j + 1)) *
      ((P - 1) ^ (j + 1)).coeff N).snd = _
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, smul_eq_mul, op_smul_eq_smul, mul_zero,
    add_zero, dualPolynomialSnd_coeff]

theorem dualTruncatedLogCoeff_lift_fst {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U V : Polynomial K) :
    (dualTruncatedLogCoeff N (dualPolynomialLift U V)).fst =
      truncatedLogCoeff N U := by
  rw [dualTruncatedLogCoeff, truncatedLogCoeff]
  change (TrivSqZeroExt.fstHom K K K)
      (∑ j ∈ Finset.range N,
        TrivSqZeroExt.inl (logarithmicWeight K (j + 1)) *
          ((dualPolynomialLift U V - 1) ^ (j + 1)).coeff N) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (TrivSqZeroExt.inl (logarithmicWeight K (j + 1)) *
      ((dualPolynomialLift U V - 1) ^ (j + 1)).coeff N).fst = _
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
  rw [← dualPolynomialFst_coeff, dualPolynomialFst_pow, dualPolynomialFst_sub,
    dualPolynomialFst_lift, dualPolynomialFst_one]

theorem logarithmicWeight_succ_mul {K : Type*} [Field K] [CharZero K]
    (j : ℕ) :
    logarithmicWeight K (j + 1) * (j + 1 : K) = (-1 : K) ^ j := by
  rw [logarithmicWeight, if_neg (Nat.succ_ne_zero j)]
  have hj : (j + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  push_cast
  rw [div_mul_cancel₀ _ hj]
  calc
    (-1 : K) ^ (j + 1 + 1) = (-1 : K) ^ j * (-1 : K) ^ 2 := by
      rw [← pow_add]
    _ = (-1 : K) ^ j := by ring

theorem logarithmicWeight_eq_coeff_log
    {K : Type*} [Field K] [CharZero K] (k : ℕ) :
    logarithmicWeight K k = PowerSeries.coeff k (PowerSeries.log K) := by
  rw [logarithmicWeight, PowerSeries.coeff_log]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    norm_cast

noncomputable def truncatedReciprocalKernel {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U : Polynomial K) : Polynomial K :=
  ∑ j ∈ Finset.range N, (-(U - 1)) ^ j

theorem dualTruncatedLogCoeff_lift_snd {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U V : Polynomial K) :
    (dualTruncatedLogCoeff N (dualPolynomialLift U V)).snd =
      (truncatedReciprocalKernel N U * V).coeff N := by
  rw [dualTruncatedLogCoeff_snd]
  simp only [dualPolynomialSnd_pow, dualPolynomialFst_sub,
    dualPolynomialFst_lift, dualPolynomialFst_one, dualPolynomialSnd_sub,
    dualPolynomialSnd_lift, dualPolynomialSnd_one, sub_zero, Nat.pred_succ,
    nsmul_eq_mul]
  rw [truncatedReciprocalKernel, Finset.sum_mul]
  change _ = (Polynomial.lcoeff K N)
    (∑ j ∈ Finset.range N, (-(U - 1)) ^ j * V)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.lcoeff_apply]
  rw [mul_assoc, Polynomial.coeff_natCast_mul]
  push_cast
  rw [← mul_assoc, logarithmicWeight_succ_mul]
  have hneg : (-(U - 1)) ^ j * V =
      Polynomial.C ((-1 : K) ^ j) * ((U - 1) ^ j * V) := by
    rw [neg_pow, show (-1 : K[X]) = Polynomial.C (-1 : K) by simp,
      Polynomial.C_pow]
    ring
  rw [hneg, Polynomial.coeff_C_mul]

theorem mul_truncatedReciprocalKernel {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U : Polynomial K) :
    U * truncatedReciprocalKernel N U = 1 - (-(U - 1)) ^ N := by
  have hgeom := mul_neg_geom_sum (-(U - 1)) N
  simpa [truncatedReciprocalKernel] using hgeom

theorem truncatedReciprocalKernel_isInverseMod {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U : Polynomial K) (hU : U.coeff 0 = 1) :
    X ^ N ∣ U * truncatedReciprocalKernel N U - 1 := by
  have hD : X ∣ -(U - 1) := by
    rw [Polynomial.X_dvd_iff]
    simp [hU]
  have hpow : X ^ N ∣ (-(U - 1)) ^ N := pow_dvd_pow_of_dvd hD N
  rw [mul_truncatedReciprocalKernel]
  have hid : (1 - (-(U - 1)) ^ N : K[X]) - 1 = -((-(U - 1)) ^ N) := by ring
  rw [hid]
  exact dvd_neg.mpr hpow

theorem isCoprime_of_coeff_zero_eq_one {K : Type*} [Field K]
    (U : Polynomial K) (hU : U.coeff 0 = 1) :
    IsCoprime U X := by
  have hD : X ∣ U - 1 := by
    rw [Polynomial.X_dvd_iff]
    simp [hU]
  obtain ⟨H, hH⟩ := hD
  refine ⟨1, -H, ?_⟩
  rw [one_mul]
  calc
    U + -H * X = U - X * H := by ring
    _ = 1 := by rw [← hH]; ring

theorem truncatedReciprocalKernel_mul_coeff_eq_of_inverse
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (U V Y : Polynomial K)
    (hU : U.coeff 0 = 1) (hV : V.coeff 0 = 0)
    (hInv : X ^ (N + 1) ∣ U * Y - 1) :
    (truncatedReciprocalKernel N U * V).coeff N = (Y * V).coeff N := by
  let G := truncatedReciprocalKernel N U
  have hInvN : X ^ N ∣ U * Y - 1 :=
    (pow_dvd_pow X (Nat.le_succ N)).trans hInv
  have hGN : X ^ N ∣ U * G - 1 := by
    exact truncatedReciprocalKernel_isInverseMod N U hU
  have hmul : X ^ N ∣ U * (Y - G) := by
    rw [show U * (Y - G) = (U * Y - 1) - (U * G - 1) by ring]
    exact dvd_sub hInvN hGN
  have hcop : IsCoprime (X ^ N) U :=
    (isCoprime_of_coeff_zero_eq_one U hU).pow_right.symm
  have hdiff : X ^ N ∣ Y - G := hcop.dvd_of_dvd_mul_left hmul
  have hVdvd : X ∣ V := Polynomial.X_dvd_iff.mpr hV
  have hprod : X ^ (N + 1) ∣ (Y - G) * V := by
    simpa [pow_succ] using mul_dvd_mul hdiff hVdvd
  have hz : ((Y - G) * V).coeff N = 0 :=
    (Polynomial.X_pow_dvd_iff.mp hprod) N (by omega)
  have heq : (Y * V).coeff N - (G * V).coeff N = 0 := by
    simpa [sub_mul, Polynomial.coeff_sub] using hz
  exact (sub_eq_zero.mp heq).symm

noncomputable def normalizedPolynomial {K : Type*} [Field K]
    (P : Polynomial K) : Polynomial K :=
  Polynomial.C (P.coeff 0)⁻¹ * P

noncomputable def normalizedPolynomialVariation {K : Type*} [Field K]
    (P dP : Polynomial K) : Polynomial K :=
  Polynomial.C (P.coeff 0)⁻¹ * dP -
    Polynomial.C ((P.coeff 0)⁻¹ * dP.coeff 0 * (P.coeff 0)⁻¹) * P

noncomputable def dualNormalizedPolynomial {K : Type*} [Field K]
    (P dP : Polynomial K) : Polynomial (LogDual K) :=
  Polynomial.C ((dualPolynomialLift P dP).coeff 0)⁻¹ *
    dualPolynomialLift P dP

theorem dualNormalizedPolynomial_eq_lift {K : Type*} [Field K]
    (P dP : Polynomial K) :
    dualNormalizedPolynomial P dP =
      dualPolynomialLift (normalizedPolynomial P)
        (normalizedPolynomialVariation P dP) := by
  ext n
  · simp [dualNormalizedPolynomial, normalizedPolynomial]
  · rw [dualPolynomialLift_coeff_snd]
    rw [dualNormalizedPolynomial, Polynomial.coeff_C_mul]
    have h0 : (dualPolynomialLift P dP).coeff 0 =
        (P.coeff 0, dP.coeff 0) := by
      apply TrivSqZeroExt.ext <;> simp
    have hn : (dualPolynomialLift P dP).coeff n =
        (P.coeff n, dP.coeff n) := by
      apply TrivSqZeroExt.ext <;> simp
    rw [h0, hn]
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inv,
      TrivSqZeroExt.snd_inv, TrivSqZeroExt.fst_mk,
      TrivSqZeroExt.snd_mk, smul_eq_mul, op_smul_eq_smul,
      normalizedPolynomialVariation, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    ring

noncomputable def criticalHorizonLogPotential {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K) : K :=
  truncatedLogCoeff N (normalizedPolynomial P)

noncomputable def criticalHorizonLogDifferential {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P dP : Polynomial K) : K :=
  (dualTruncatedLogCoeff N (dualNormalizedPolynomial P dP)).snd

noncomputable def criticalHorizonLogTangentValue
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P dP : Polynomial K) : LogDual K :=
  dualTruncatedLogCoeff N (dualNormalizedPolynomial P dP)

theorem criticalHorizonLogTangentValue_fst
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P dP : Polynomial K) :
    (criticalHorizonLogTangentValue N P dP).fst =
      criticalHorizonLogPotential N P := by
  rw [criticalHorizonLogTangentValue, criticalHorizonLogPotential,
    dualNormalizedPolynomial_eq_lift, dualTruncatedLogCoeff_lift_fst]

theorem criticalHorizonLogTangentValue_snd
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P dP : Polynomial K) :
    (criticalHorizonLogTangentValue N P dP).snd =
      criticalHorizonLogDifferential N P dP := rfl

theorem criticalHorizonLogDifferential_eq_reciprocal
    {K : Type*} [Field K] [CharZero K]
    {N : ℕ} (hN : 0 < N) (P dP Y : Polynomial K)
    (hP : P.coeff 0 ≠ 0)
    (hInv : X ^ (N + 1) ∣ P * Y - 1) :
    criticalHorizonLogDifferential N P dP = (Y * dP).coeff N := by
  let U := normalizedPolynomial P
  let V := normalizedPolynomialVariation P dP
  let W := Polynomial.C (P.coeff 0) * Y
  have hU : U.coeff 0 = 1 := by
    simp [U, normalizedPolynomial, hP]
  have hV : V.coeff 0 = 0 := by
    simp [V, normalizedPolynomialVariation, hP]
  have hscalar : Polynomial.C (P.coeff 0) * Polynomial.C (P.coeff 0)⁻¹ =
      (1 : K[X]) := by
    rw [← Polynomial.C_mul]
    simp [hP]
  have hUW : U * W = P * Y := by
    dsimp [U, W, normalizedPolynomial]
    calc
      Polynomial.C (P.coeff 0)⁻¹ * P * (Polynomial.C (P.coeff 0) * Y) =
          (Polynomial.C (P.coeff 0) * Polynomial.C (P.coeff 0)⁻¹) *
            (P * Y) := by ring
      _ = P * Y := by rw [hscalar, one_mul]
  have hInvUW : X ^ (N + 1) ∣ U * W - 1 := by
    rwa [hUW]
  rw [criticalHorizonLogDifferential, dualNormalizedPolynomial_eq_lift,
    dualTruncatedLogCoeff_lift_snd]
  rw [truncatedReciprocalKernel_mul_coeff_eq_of_inverse N U V W hU hV hInvUW]
  have hPY : (P * Y).coeff N = 0 := by
    have hzero := (Polynomial.X_pow_dvd_iff.mp hInv) N (by omega)
    simpa [Polynomial.coeff_sub, Polynomial.coeff_one, hN.ne'] using hzero
  have hYP : (Y * P).coeff N = 0 := by
    rw [mul_comm]
    exact hPY
  have hWV : W * V = Y * dP -
      Polynomial.C (dP.coeff 0 * (P.coeff 0)⁻¹) * (Y * P) := by
    dsimp [W, V, normalizedPolynomialVariation]
    have hcorr : Polynomial.C (P.coeff 0) *
        Polynomial.C ((P.coeff 0)⁻¹ * dP.coeff 0 * (P.coeff 0)⁻¹) =
          Polynomial.C (dP.coeff 0 * (P.coeff 0)⁻¹) := by
      rw [← Polynomial.C_mul]
      congr 1
      field_simp [hP]
    calc
      Polynomial.C (P.coeff 0) * Y *
          (Polynomial.C (P.coeff 0)⁻¹ * dP -
            Polynomial.C ((P.coeff 0)⁻¹ * dP.coeff 0 * (P.coeff 0)⁻¹) * P) =
          (Polynomial.C (P.coeff 0) * Polynomial.C (P.coeff 0)⁻¹) *
              (Y * dP) -
            (Polynomial.C (P.coeff 0) *
                Polynomial.C ((P.coeff 0)⁻¹ * dP.coeff 0 * (P.coeff 0)⁻¹)) *
                  (Y * P) := by ring
      _ = Y * dP - Polynomial.C (dP.coeff 0 * (P.coeff 0)⁻¹) * (Y * P) := by
        rw [hscalar, hcorr, one_mul]
  rw [hWV, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hYP, mul_zero, sub_zero]

theorem criticalHorizonLogGradient_eq_reversedReciprocal
    {K : Type*} [Field K] [CharZero K]
    {N : ℕ} (hN : 0 < N) (P Y : Polynomial K)
    (hP : P.coeff 0 ≠ 0)
    (hInv : X ^ (N + 1) ∣ P * Y - 1)
    (i : Fin (N + 1)) :
    criticalHorizonLogDifferential N P (X ^ (i : ℕ)) =
      Y.coeff (N - (i : ℕ)) := by
  rw [criticalHorizonLogDifferential_eq_reciprocal hN P (X ^ (i : ℕ)) Y hP hInv,
    Polynomial.coeff_mul_X_pow', if_pos (by omega)]

theorem one_add_X_mul_derivative_log
    (K : Type*) [Field K] [CharZero K] :
    (1 + PowerSeries.X : PowerSeries K) *
        (PowerSeries.derivative K) (PowerSeries.log K) = 1 := by
  rw [PowerSeries.deriv_log]
  have hmap := congrArg (PowerSeries.rescale (-1 : K))
    (PowerSeries.mk_one_mul_one_sub_eq_one K)
  rw [map_mul, map_one, PowerSeries.rescale_mk,
    map_sub, map_one, PowerSeries.rescale_neg_one_X] at hmap
  simpa [mul_comm] using hmap

theorem derivative_logOf
    {K : Type*} [Field K] [CharZero K]
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1) :
    (PowerSeries.derivative K) (PowerSeries.logOf f) =
      f⁻¹ * (PowerSeries.derivative K) f := by
  have hg : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hprod : f *
      ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1) = 1 := by
    have hmap := congrArg (PowerSeries.substAlgHom hg)
      (one_add_X_mul_derivative_log K)
    simp only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X] at hmap
    rw [show 1 + (f - 1) = f by ring] at hmap
    rw [PowerSeries.coe_substAlgHom hg] at hmap
    exact hmap
  have hf0 : PowerSeries.constantCoeff f ≠ 0 := by simp [hf]
  have hgeom : ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1) = f⁻¹ := by
    calc
      ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1) =
          1 * ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1) := by rw [one_mul]
      _ = (f⁻¹ * f) *
          ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1) := by
            rw [PowerSeries.inv_mul_cancel (h := hf0)]
      _ = f⁻¹ * (f *
          ((PowerSeries.derivative K) (PowerSeries.log K)).subst (f - 1)) := by ring
      _ = f⁻¹ := by rw [hprod, mul_one]
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst K hg, hgeom]
  simp

theorem powerSeries_eq_zero_of_derivative_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {f : PowerSeries K}
    (hder : (PowerSeries.derivative K) f = 0)
    (hconst : PowerSeries.constantCoeff f = 0) :
    f = 0 := by
  ext (_ | n)
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_zero] using hconst
  · have hcoeff := congrArg (PowerSeries.coeff n) hder
    rw [PowerSeries.coeff_derivative] at hcoeff
    change PowerSeries.coeff (n + 1) f * (n + 1 : K) = 0 at hcoeff
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact (mul_eq_zero.mp hcoeff).resolve_right hn

theorem logOf_add_logOf_eq_zero_of_mul_eq_one
    {K : Type*} [Field K] [CharZero K]
    {f g : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1)
    (hfg : f * g = 1) :
    PowerSeries.logOf f + PowerSeries.logOf g = 0 := by
  have hf0 : PowerSeries.constantCoeff f ≠ 0 := by simp [hf]
  have hginv : g = f⁻¹ := by
    calc
      g = 1 * g := by rw [one_mul]
      _ = (f⁻¹ * f) * g := by rw [PowerSeries.inv_mul_cancel (h := hf0)]
      _ = f⁻¹ * (f * g) := by ring
      _ = f⁻¹ := by rw [hfg, mul_one]
  have hfi0 : PowerSeries.constantCoeff f⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv, hf]
    simp
  have hinvinv : f⁻¹⁻¹ = f := by
    calc
      f⁻¹⁻¹ = f⁻¹⁻¹ * 1 := by rw [mul_one]
      _ = f⁻¹⁻¹ * (f⁻¹ * f) := by rw [PowerSeries.inv_mul_cancel (h := hf0)]
      _ = (f⁻¹⁻¹ * f⁻¹) * f := by ring
      _ = f := by rw [PowerSeries.inv_mul_cancel (h := hfi0), one_mul]
  apply powerSeries_eq_zero_of_derivative_eq_zero
  · rw [map_add, derivative_logOf hf, derivative_logOf hg,
      hginv, PowerSeries.derivative_inv']
    rw [hinvinv]
    calc
      f⁻¹ * (PowerSeries.derivative K) f +
          f * (-(f⁻¹) ^ 2 * (PowerSeries.derivative K) f) =
          (1 - f * f⁻¹) * (f⁻¹ * (PowerSeries.derivative K) f) := by ring
      _ = 0 := by rw [PowerSeries.mul_inv_cancel (h := hf0), sub_self, zero_mul]
  · rw [map_add, PowerSeries.constantCoeff_logOf hf,
      PowerSeries.constantCoeff_logOf hg, add_zero]

theorem logOf_mul
    {K : Type*} [Field K] [CharZero K]
    {f g : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.logOf (f * g) =
      PowerSeries.logOf f + PowerSeries.logOf g := by
  have hf0 : PowerSeries.constantCoeff f ≠ 0 := by simp [hf]
  have hg0 : PowerSeries.constantCoeff g ≠ 0 := by simp [hg]
  have hfgc : PowerSeries.constantCoeff (f * g) = 1 := by simp [hf, hg]
  have hfg0 : PowerSeries.constantCoeff (f * g) ≠ 0 := by simp [hfgc]
  have hright : (f * g) * (f⁻¹ * g⁻¹) = 1 := by
    calc
      (f * g) * (f⁻¹ * g⁻¹) = (f * f⁻¹) * (g * g⁻¹) := by ring
      _ = 1 := by
        rw [PowerSeries.mul_inv_cancel (h := hf0),
          PowerSeries.mul_inv_cancel (h := hg0), one_mul]
  have hprodInv : (f * g)⁻¹ = f⁻¹ * g⁻¹ := by
    calc
      (f * g)⁻¹ = (f * g)⁻¹ * 1 := by rw [mul_one]
      _ = (f * g)⁻¹ * ((f * g) * (f⁻¹ * g⁻¹)) := by rw [hright]
      _ = ((f * g)⁻¹ * (f * g)) * (f⁻¹ * g⁻¹) := by ring
      _ = f⁻¹ * g⁻¹ := by rw [PowerSeries.inv_mul_cancel (h := hfg0), one_mul]
  apply sub_eq_zero.mp
  apply powerSeries_eq_zero_of_derivative_eq_zero
  · rw [map_sub, map_add, derivative_logOf hfgc,
      derivative_logOf hf, derivative_logOf hg, hprodInv]
    rw [Derivation.leibniz]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
    have hfc : f⁻¹ * f = 1 := PowerSeries.inv_mul_cancel f hf0
    have hgc : g⁻¹ * g = 1 := PowerSeries.inv_mul_cancel g hg0
    calc
      f⁻¹ * g⁻¹ *
            (f * (PowerSeries.derivative K) g +
              g * (PowerSeries.derivative K) f) -
          (f⁻¹ * (PowerSeries.derivative K) f +
            g⁻¹ * (PowerSeries.derivative K) g) =
          (g⁻¹ * g - 1) * (f⁻¹ * (PowerSeries.derivative K) f) +
            (f⁻¹ * f - 1) * (g⁻¹ * (PowerSeries.derivative K) g) := by ring
      _ = 0 := by simp [hfc, hgc]
  · rw [map_sub, map_add, PowerSeries.constantCoeff_logOf hfgc,
      PowerSeries.constantCoeff_logOf hf, PowerSeries.constantCoeff_logOf hg]
    ring

theorem truncatedLogCoeff_eq_coeff_logOf
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K) (hP : P.coeff 0 = 1) :
    truncatedLogCoeff N P =
      PowerSeries.coeff N (PowerSeries.logOf (P : PowerSeries K)) := by
  have hb : PowerSeries.HasSubst ((P : PowerSeries K) - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      rw [map_sub, map_one]
      change P.coeff 0 - 1 = 0
      rw [hP, sub_self])
  rw [PowerSeries.logOf_eq, PowerSeries.coeff_subst' hb]
  simp only [smul_eq_mul]
  let F : ℕ → K := fun d =>
    PowerSeries.coeff d (PowerSeries.log K) *
      PowerSeries.coeff N (((P : PowerSeries K) - 1) ^ d)
  have hsupport : Function.support F ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro d hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hnot
    have hNd : N < d := by omega
    have hXd : X ^ d ∣ (P - 1) ^ d :=
      pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr (by simp [hP])) d
    have hcoeff : ((P - 1) ^ d).coeff N = 0 :=
      (Polynomial.X_pow_dvd_iff.mp hXd) N hNd
    apply hd
    dsimp [F]
    rw [show ((P : PowerSeries K) - 1) ^ d =
        (((P - 1) ^ d : Polynomial K) : PowerSeries K) by norm_cast]
    rw [Polynomial.coeff_coe, hcoeff, mul_zero]
  change truncatedLogCoeff N P = ∑ᶠ d, F d
  rw [finsum_eq_finsetSum_of_support_subset F hsupport]
  rw [Finset.sum_range_succ']
  have hF0 : F 0 = 0 := by simp [F, PowerSeries.coeff_log]
  rw [hF0, add_zero]
  rw [truncatedLogCoeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [logarithmicWeight_eq_coeff_log]
  congr 1
  rw [show ((P : PowerSeries K) - 1) ^ (j + 1) =
      (((P - 1) ^ (j + 1) : Polynomial K) : PowerSeries K) by norm_cast]
  exact (Polynomial.coeff_coe ((P - 1) ^ (j + 1)) N).symm

theorem normalizedPolynomial_coeff_zero
    {K : Type*} [Field K] (P : Polynomial K) (hP : P.coeff 0 ≠ 0) :
    (normalizedPolynomial P).coeff 0 = 1 := by
  simp [normalizedPolynomial, hP]

theorem criticalHorizonLogPotential_eq_coeff_logOf
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K) (hP : P.coeff 0 ≠ 0) :
    criticalHorizonLogPotential N P =
      PowerSeries.coeff N
        (PowerSeries.logOf (normalizedPolynomial P : PowerSeries K)) := by
  rw [criticalHorizonLogPotential,
    truncatedLogCoeff_eq_coeff_logOf N (normalizedPolynomial P)
      (normalizedPolynomial_coeff_zero P hP)]

theorem truncatedLogCoeff_eq_zero_of_one_mod
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K)
    (hP : X ^ (N + 1) ∣ P - 1) :
    truncatedLogCoeff N P = 0 := by
  rw [truncatedLogCoeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos : 0 < j + 1 := Nat.succ_pos j
  have hpow : X ^ (N + 1) ∣ (P - 1) ^ (j + 1) :=
    hP.trans (dvd_pow_self (P - 1) hjpos.ne')
  have hcoeff : ((P - 1) ^ (j + 1)).coeff N = 0 :=
    (Polynomial.X_pow_dvd_iff.mp hpow) N (by omega)
  rw [hcoeff, mul_zero]

theorem coeff_logOf_eq_zero_of_one_mod
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P : Polynomial K) (hP0 : P.coeff 0 = 1)
    (hP : X ^ (N + 1) ∣ P - 1) :
    PowerSeries.coeff N (PowerSeries.logOf (P : PowerSeries K)) = 0 := by
  rw [← truncatedLogCoeff_eq_coeff_logOf N P hP0,
    truncatedLogCoeff_eq_zero_of_one_mod N P hP]

theorem coeff_zero_mul_eq_one_of_inverse_mod
    {K : Type*} [Field K]
    (N : ℕ) (P Y : Polynomial K)
    (hInv : X ^ (N + 1) ∣ P * Y - 1) :
    P.coeff 0 * Y.coeff 0 = 1 := by
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hInv) 0 (by omega)
  have hcoeff' : (P * Y).coeff 0 - 1 = 0 := by
    simpa [Polynomial.coeff_sub, Polynomial.coeff_one] using hcoeff
  have hmul : (P * Y).coeff 0 = P.coeff 0 * Y.coeff 0 := by simp
  rw [hmul] at hcoeff'
  exact sub_eq_zero.mp hcoeff'

theorem normalizedPolynomial_mul_eq_of_coeff_zero_mul_eq_one
    {K : Type*} [Field K] (P Y : Polynomial K)
    (hPY : P.coeff 0 * Y.coeff 0 = 1) :
    normalizedPolynomial P * normalizedPolynomial Y = P * Y := by
  have hscalar : (P.coeff 0)⁻¹ * (Y.coeff 0)⁻¹ = 1 := by
    rw [← mul_inv, hPY, inv_one]
  dsimp [normalizedPolynomial]
  calc
    (Polynomial.C (P.coeff 0)⁻¹ * P) *
          (Polynomial.C (Y.coeff 0)⁻¹ * Y) =
        Polynomial.C ((P.coeff 0)⁻¹ * (Y.coeff 0)⁻¹) * (P * Y) := by
          rw [Polynomial.C_mul]
          ring
    _ = P * Y := by rw [hscalar]; simp

theorem criticalHorizonLogPotential_add_inverse_eq_zero
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P Y : Polynomial K)
    (hInv : X ^ (N + 1) ∣ P * Y - 1) :
    criticalHorizonLogPotential N P +
        criticalHorizonLogPotential N Y = 0 := by
  have hPY0 := coeff_zero_mul_eq_one_of_inverse_mod N P Y hInv
  have hP0 : P.coeff 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hPY0
    exact zero_ne_one hPY0
  have hY0 : Y.coeff 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hPY0
    exact zero_ne_one hPY0
  let U := normalizedPolynomial P
  let V := normalizedPolynomial Y
  have hU0 : U.coeff 0 = 1 := normalizedPolynomial_coeff_zero P hP0
  have hV0 : V.coeff 0 = 1 := normalizedPolynomial_coeff_zero Y hY0
  have hUV : U * V = P * Y :=
    normalizedPolynomial_mul_eq_of_coeff_zero_mul_eq_one P Y hPY0
  have hInvUV : X ^ (N + 1) ∣ U * V - 1 := by rwa [hUV]
  rw [criticalHorizonLogPotential_eq_coeff_logOf N P hP0,
    criticalHorizonLogPotential_eq_coeff_logOf N Y hY0]
  calc
    PowerSeries.coeff N (PowerSeries.logOf (U : PowerSeries K)) +
          PowerSeries.coeff N (PowerSeries.logOf (V : PowerSeries K)) =
        PowerSeries.coeff N
          (PowerSeries.logOf (U : PowerSeries K) +
            PowerSeries.logOf (V : PowerSeries K)) := by rw [map_add]
    _ = PowerSeries.coeff N
          (PowerSeries.logOf ((U * V : Polynomial K) : PowerSeries K)) := by
            rw [← logOf_mul hU0 hV0]
            norm_cast
    _ = 0 := coeff_logOf_eq_zero_of_one_mod N (U * V)
      (by simp [hU0, hV0]) hInvUV

theorem criticalHorizonLogPotential_inverse_eq_neg
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (P Y : Polynomial K)
    (hInv : X ^ (N + 1) ∣ P * Y - 1) :
    criticalHorizonLogPotential N Y =
      -criticalHorizonLogPotential N P := by
  exact eq_neg_of_add_eq_zero_right
    (criticalHorizonLogPotential_add_inverse_eq_zero N P Y hInv)

/-- The logarithmic vacuum potential after fixing a reciprocal tail `Q`.  The variable low packet
is `A`, while `Xj` is the complete raw jet whose normalized logarithm is used. -/
noncomputable def criticalHorizonVacuumPotential
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj A Q : Polynomial K) : K :=
  criticalHorizonLogPotential N Xj - (A * Q).coeff N

/-- Algebraic directional differential of the vacuum potential. -/
noncomputable def criticalHorizonVacuumDifferential
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj Q dX : Polynomial K) : K :=
  criticalHorizonLogDifferential N Xj dX - (dX * Q).coeff N

/-- Dual-number evaluation certifying the value and differential of the vacuum potential in one
algebraic object. -/
noncomputable def criticalHorizonVacuumTangentValue
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj A Q dX : Polynomial K) : LogDual K :=
  criticalHorizonLogTangentValue N Xj dX -
    TrivSqZeroExt.inl ((A * Q).coeff N) -
    TrivSqZeroExt.inr (R := K) ((dX * Q).coeff N)

@[simp]
theorem criticalHorizonVacuumTangentValue_fst
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj A Q dX : Polynomial K) :
    (criticalHorizonVacuumTangentValue N Xj A Q dX).fst =
      criticalHorizonVacuumPotential N Xj A Q := by
  simp [criticalHorizonVacuumTangentValue, criticalHorizonVacuumPotential,
    criticalHorizonLogTangentValue_fst]

@[simp]
theorem criticalHorizonVacuumTangentValue_snd
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj A Q dX : Polynomial K) :
    (criticalHorizonVacuumTangentValue N Xj A Q dX).snd =
      criticalHorizonVacuumDifferential N Xj Q dX := by
  simp [criticalHorizonVacuumTangentValue, criticalHorizonVacuumDifferential,
    criticalHorizonLogTangentValue_snd]

/-- The vacuum gradient equations are precisely the raw/reciprocal tail-compatibility equations. -/
theorem criticalHorizonVacuumGradient_eq_compatibility
    {K : Type*} [Field K] [CharZero K]
    {N : ℕ} (hN : 0 < N) (Xj Y Q : Polynomial K)
    (hX : Xj.coeff 0 ≠ 0)
    (hInv : X ^ (N + 1) ∣ Xj * Y - 1)
    (i : Fin (N + 1)) :
    criticalHorizonVacuumDifferential N Xj Q (X ^ (i : ℕ)) =
      Y.coeff (N - (i : ℕ)) - Q.coeff (N - (i : ℕ)) := by
  rw [criticalHorizonVacuumDifferential,
    criticalHorizonLogGradient_eq_reversedReciprocal hN Xj Y hX hInv]
  have hi : (i : ℕ) ≤ N := by omega
  have hcoeff : (X ^ (i : ℕ) * Q).coeff N =
      Q.coeff (N - (i : ℕ)) := by
    rw [mul_comm, Polynomial.coeff_mul_X_pow', if_pos hi]
  rw [hcoeff]

/-- Vanishing of one vacuum-gradient coordinate is exactly equality with the prescribed
reciprocal-tail coordinate. -/
theorem criticalHorizonVacuumGradient_eq_zero_iff
    {K : Type*} [Field K] [CharZero K]
    {N : ℕ} (hN : 0 < N) (Xj Y Q : Polynomial K)
    (hX : Xj.coeff 0 ≠ 0)
    (hInv : X ^ (N + 1) ∣ Xj * Y - 1)
    (i : Fin (N + 1)) :
    criticalHorizonVacuumDifferential N Xj Q (X ^ (i : ℕ)) = 0 ↔
      Y.coeff (N - (i : ℕ)) = Q.coeff (N - (i : ℕ)) := by
  rw [criticalHorizonVacuumGradient_eq_compatibility hN Xj Y Q hX hInv i,
    sub_eq_zero]

/-- Simultaneous criticality in the first `m` raw coordinates is exactly equality with the fixed
reciprocal tail `y_n,...,y_N`, written in reversed cotangent order. -/
theorem criticalHorizonPartialVacuumCritical_iff
    {K : Type*} [Field K] [CharZero K]
    {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m + n = N + 1)
    (Xj Y Q : Polynomial K) (hX : Xj.coeff 0 ≠ 0)
    (hInv : X ^ (N + 1) ∣ Xj * Y - 1) :
    (∀ i : Fin m,
      criticalHorizonVacuumDifferential N Xj Q (X ^ (i : ℕ)) = 0) ↔
    (∀ i : Fin m,
      Y.coeff (n + (m - 1 - (i : ℕ))) =
        Q.coeff (n + (m - 1 - (i : ℕ)))) := by
  have hN : 0 < N := by omega
  constructor
  · intro hcrit i
    let iN : Fin (N + 1) := ⟨i, by omega⟩
    have hi := (criticalHorizonVacuumGradient_eq_zero_iff
      hN Xj Y Q hX hInv iN).mp (hcrit i)
    change Y.coeff (N - (i : ℕ)) = Q.coeff (N - (i : ℕ)) at hi
    convert hi using 1 <;> congr 1 <;> omega
  · intro htail i
    let iN : Fin (N + 1) := ⟨i, by omega⟩
    apply (criticalHorizonVacuumGradient_eq_zero_iff
      hN Xj Y Q hX hInv iN).mpr
    change Y.coeff (N - (i : ℕ)) = Q.coeff (N - (i : ℕ))
    convert htail i using 1 <;> congr 1 <;> omega

/-- The Hessian of the logarithmic vacuum potential is the already-defined symmetric Hankel
reciprocal Hessian. -/
noncomputable def criticalHorizonVacuumHessian
    {K : Type*} [CommRing K] (Y : Polynomial K) (L m : ℕ) :
    Matrix (Fin m) (Fin m) K :=
  criticalReciprocalHessian Y L m

theorem criticalHorizonVacuumHessian_reverseRows
    {K : Type*} [CommRing K] (Y : Polynomial K) (n m : ℕ)
    (r j : Fin m) :
    criticalReciprocalJacobian Y n m r j =
      criticalHorizonVacuumHessian Y (m + n) m (Fin.rev r) j :=
  criticalReciprocalJacobian_eq_reverseRows_hessian Y n m r j

/-- The two arbitrary-tail vacuum potentials have opposite values at every compatible state. -/
theorem criticalHorizonVacuumPotential_add_dual_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A B P Q : Polynomial K}
    (hA : A.natDegree < m) (hB : B.natDegree < n)
    (hP : X ^ m ∣ P) (hQ : X ^ n ∣ Q)
    (hInv : X ^ (m + n) ∣ (A + P) * (B + Q) - 1) :
    criticalHorizonVacuumPotential (m + n - 1) (A + P) A Q +
      criticalHorizonVacuumPotential (m + n - 1) (B + Q) B P = 0 := by
  have htop : ((A + P) * (B + Q)).coeff (m + n - 1) = 0 := by
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hInv) (m + n - 1) (by omega)
    simpa [Polynomial.coeff_sub, Polynomial.coeff_one, show m + n - 1 ≠ 0 by omega]
      using hcoeff
  have hpair := criticalHorizonTopPairing_add_dual_eq_zero
    hm hn hA hB hP hQ htop
  have hsucc : m + n - 1 + 1 = m + n := by omega
  have hlog := criticalHorizonLogPotential_add_inverse_eq_zero
    (m + n - 1) (A + P) (B + Q) (by simpa [hsucc] using hInv)
  simp only [criticalHorizonVacuumPotential]
  dsimp [criticalHorizonTopPairing] at hpair
  linear_combination hlog - hpair

/-- The ordinary Legendre-transform value of the logarithmic potential. -/
noncomputable def criticalHorizonLogLegendreTransform
    {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (Xj Y : Polynomial K) : K :=
  criticalHorizonLegendrePairing N Xj Y -
    criticalHorizonLogPotential N Xj

/-- On the reciprocal graph, the Legendre transform is the same logarithmic potential in the
coefficient-reversed dual chart. -/
theorem criticalHorizonLogLegendreTransform_eq_dual
    {K : Type*} [Field K] [CharZero K]
    {N : ℕ} (hN : 0 < N) (Xj Y : Polynomial K)
    (hInv : X ^ (N + 1) ∣ Xj * Y - 1) :
    criticalHorizonLogLegendreTransform N Xj Y =
      criticalHorizonLogPotential N Y := by
  rw [criticalHorizonLogLegendreTransform,
    criticalHorizonLegendrePairing_eq_zero_of_inverse hN (by omega) hInv,
    zero_sub, criticalHorizonLogPotential_inverse_eq_neg N Xj Y hInv]

/-- Truncated inversion is involutive: the same congruence exhibits the dual jet as having raw
inverse `Xj`. -/
theorem criticalHorizonInverseMod_swap
    {K : Type*} [CommRing K] {N : ℕ} {Xj Y : Polynomial K}
    (hInv : X ^ (N + 1) ∣ Xj * Y - 1) :
    X ^ (N + 1) ∣ Y * Xj - 1 := by
  simpa [mul_comm] using hInv

/-- One point of the all-depth exact reciprocal-jet tower. -/
structure CriticalHorizonReciprocalTowerPoint
    (K : Type*) [Field K] [CharZero K] (N : ℕ) where
  raw : Polynomial K
  reciprocal : Polynomial K
  rawUnit : raw.coeff 0 ≠ 0
  inverseMod : X ^ (N + 1) ∣ raw * reciprocal - 1

namespace CriticalHorizonReciprocalTowerPoint

noncomputable def momentum
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (T : CriticalHorizonReciprocalTowerPoint K N) (i : Fin (N + 1)) : K :=
  T.reciprocal.coeff (N - (i : ℕ))

theorem gradient_eq_momentum
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (T : CriticalHorizonReciprocalTowerPoint K N) (hN : 0 < N)
    (i : Fin (N + 1)) :
    criticalHorizonLogDifferential N T.raw (X ^ (i : ℕ)) = T.momentum i :=
  criticalHorizonLogGradient_eq_reversedReciprocal
    hN T.raw T.reciprocal T.rawUnit T.inverseMod i

theorem legendreTransform_eq_dualPotential
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (T : CriticalHorizonReciprocalTowerPoint K N) (hN : 0 < N) :
    criticalHorizonLogLegendreTransform N T.raw T.reciprocal =
      criticalHorizonLogPotential N T.reciprocal :=
  criticalHorizonLogLegendreTransform_eq_dual hN T.raw T.reciprocal T.inverseMod

theorem isotropic
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (T : CriticalHorizonReciprocalTowerPoint K N)
    (dX₁ dX₂ : Polynomial K) :
    criticalHorizonSymplecticPairing (N + 1)
        dX₁ (criticalReciprocalInfinitesimal T.reciprocal dX₁)
        dX₂ (criticalReciprocalInfinitesimal T.reciprocal dX₂) = 0 :=
  criticalReciprocalGraph_isotropic T.reciprocal dX₁ dX₂ (N + 1)

/-- For `m+n=N+1`, the first `m` reversed momenta are exactly the reciprocal tail
`y_n,...,y_N`, in reverse order. -/
theorem partialMomentum_eq_reciprocalTail
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (T : CriticalHorizonReciprocalTowerPoint K N)
    {m n : ℕ} (hmn : m + n = N + 1) (i : Fin m) :
    T.momentum ⟨i, by omega⟩ =
      T.reciprocal.coeff (n + (m - 1 - (i : ℕ))) := by
  simp only [momentum]
  congr 1
  omega

end CriticalHorizonReciprocalTowerPoint

end GaloisForLFunctions.HTGeometry


