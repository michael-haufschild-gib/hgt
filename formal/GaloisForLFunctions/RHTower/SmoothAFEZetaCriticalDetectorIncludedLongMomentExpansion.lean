import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorOmittedLongMomentExpansion

/-!
# Cancellation-preserving long moments of the finite Levinson detector

The finite detector head retains exactly those complementary divisors `q` for which `k ≤ L*q`.
Expanding this retained sum directly preserves the cancellation hidden by the separate
full-minus-omitted energy bound.
-/

open Finset

namespace RHTower

open Complex

noncomputable section

/-- Base divisor sum retained by the finite detector head. -/
def Sieve.barbanVehovIncludedBaseCoeff (L M k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors.filter (fun q => k ≤ L * q),
    Sieve.barbanVehovWeight M q

/-- Log-differentiated divisor sum retained by the finite detector head. -/
def Sieve.barbanVehovIncludedDifferentiatedCoeff (L M k : ℕ) : ℝ :=
  -∑ q ∈ k.divisors.filter (fun q => k ≤ L * q),
    Sieve.barbanVehovWeight M q * Real.log (((k / q : ℕ) : ℝ))

/-- The finite detector convolution is the complementary-divisor sum retained by the head. -/
theorem levinsonCriticalDetectorMollifiedFinCoeff_eq_includedDivisorSum
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    levinsonCriticalDetectorMollifiedFinCoeff lam L M r =
      ∑ q ∈ ((r : ℕ) + 1).divisors.filter
          (fun q => (r : ℕ) + 1 ≤ L * q),
        Sieve.levinsonCriticalDetectorHeadCoeff lam (((r : ℕ) + 1) / q) *
          Sieve.levinsonLinearMollifierCoeff M q := by
  classical
  let K : ℕ := (r : ℕ) + 1
  have hK : 0 < K := by dsimp only [K]; omega
  rw [levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted]
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq_headDivisorSum,
    levinsonCriticalDetectorOmittedHeadCoeff_eq_complementaryDivisorSum]
  have hreindex :
      (∑ d ∈ K.divisors,
          Sieve.levinsonCriticalDetectorHeadCoeff lam d *
            Sieve.levinsonLinearMollifierCoeff M (K / d)) =
        ∑ q ∈ K.divisors,
          Sieve.levinsonCriticalDetectorHeadCoeff lam (K / q) *
            Sieve.levinsonLinearMollifierCoeff M q := by
    exact (Nat.sum_divisorsAntidiagonal
      (fun d q => Sieve.levinsonCriticalDetectorHeadCoeff lam d *
        Sieve.levinsonLinearMollifierCoeff M q)).symm.trans
      (Nat.sum_divisorsAntidiagonal'
        (fun d q => Sieve.levinsonCriticalDetectorHeadCoeff lam d *
          Sieve.levinsonLinearMollifierCoeff M q))
  rw [show ((r : ℕ) + 1) = K by rfl, hreindex]
  rw [← Finset.sum_filter_add_sum_filter_not K.divisors
    (fun q => L * q < K)
    (fun q => Sieve.levinsonCriticalDetectorHeadCoeff lam (K / q) *
      Sieve.levinsonLinearMollifierCoeff M q)]
  simp only [not_lt]
  ring

/-- The finite detector coefficient in normalized included Barban--Vehov form. -/
theorem levinsonCriticalDetectorMollifiedFinCoeff_eq_includedArithmetic
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    levinsonCriticalDetectorMollifiedFinCoeff lam L M r =
      ((((Sieve.barbanVehovIncludedBaseCoeff L M ((r : ℕ) + 1) +
          lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M ((r : ℕ) + 1)) /
        Real.log M) *
          (1 / Real.sqrt ((((r : ℕ) + 1 : ℕ) : ℝ))) : ℝ) : ℂ) := by
  rw [levinsonCriticalDetectorMollifiedFinCoeff_eq_includedDivisorSum]
  rw [Sieve.barbanVehovIncludedBaseCoeff,
    Sieve.barbanVehovIncludedDifferentiatedCoeff]
  simp_rw [Sieve.levinsonCriticalDetectorHeadCoeff,
    Sieve.levinsonLinearMollifierCoeff]
  norm_cast
  have hterm : ∀ q ∈ ((r : ℕ) + 1).divisors.filter
      (fun q => (r : ℕ) + 1 ≤ L * q),
      (1 / Real.sqrt ((((r : ℕ) + 1) / q : ℕ) : ℝ) *
          (1 - lam * Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) *
        (Sieve.barbanVehovWeight M q / Real.log M *
          (1 / Real.sqrt q)) =
        ((Sieve.barbanVehovWeight M q *
            (1 - lam * Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) /
          Real.log M) *
            (1 / Real.sqrt ((((r : ℕ) + 1 : ℕ) : ℝ))) := by
    intro q hq
    have hqdvd : q ∣ (r : ℕ) + 1 :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1
    rw [show
      (1 / Real.sqrt ((((r : ℕ) + 1) / q : ℕ) : ℝ) *
            (1 - lam * Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) *
          (Sieve.barbanVehovWeight M q / Real.log M *
            (1 / Real.sqrt q)) =
        ((Sieve.barbanVehovWeight M q *
            (1 - lam * Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) /
          Real.log M) *
            ((1 / Real.sqrt ((((r : ℕ) + 1) / q : ℕ) : ℝ)) *
              (1 / Real.sqrt q)) by ring]
    rw [Sieve.one_div_sqrt_div_mul_one_div_sqrt_of_dvd (by omega) hqdvd]
  have hsum :
      (∑ q ∈ ((r : ℕ) + 1).divisors.filter
          (fun q => (r : ℕ) + 1 ≤ L * q),
        Sieve.barbanVehovWeight M q *
          (1 - lam * Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) =
      (∑ q ∈ ((r : ℕ) + 1).divisors.filter
          (fun q => (r : ℕ) + 1 ≤ L * q),
        Sieve.barbanVehovWeight M q) -
        lam * ∑ q ∈ ((r : ℕ) + 1).divisors.filter
          (fun q => (r : ℕ) + 1 ≤ L * q),
          Sieve.barbanVehovWeight M q *
            Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)) := by
    calc
      _ = ∑ q ∈ ((r : ℕ) + 1).divisors.filter
          (fun q => (r : ℕ) + 1 ≤ L * q),
          (Sieve.barbanVehovWeight M q -
            lam * (Sieve.barbanVehovWeight M q *
              Real.log (((((r : ℕ) + 1) / q : ℕ) : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_div]
  rw [hsum]
  ring

/-- Exact square norm of one included finite-detector coefficient. -/
theorem norm_levinsonCriticalDetectorMollifiedFinCoeff_sq_included
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) (r : Fin (L * M)) :
    ‖levinsonCriticalDetectorMollifiedFinCoeff lam L M r‖ ^ 2 =
      (Sieve.barbanVehovIncludedBaseCoeff L M ((r : ℕ) + 1) +
          lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M ((r : ℕ) + 1)) ^ 2 /
        (((r : ℕ) + 1 : ℕ) : ℝ) / Real.log M ^ 2 := by
  rw [levinsonCriticalDetectorMollifiedFinCoeff_eq_includedArithmetic,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div]
  have hlog : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast hM)
  have hkR : 0 < ((((r : ℕ) + 1 : ℕ) : ℝ)) := by positivity
  rw [abs_of_pos hlog,
    abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / Real.sqrt ((((r : ℕ) + 1 : ℕ) : ℝ)))]
  have hsqrt : (Real.sqrt ((((r : ℕ) + 1 : ℕ) : ℝ))) ^ 2 =
      (((r : ℕ) + 1 : ℕ) : ℝ) := Real.sq_sqrt hkR.le
  have hinvsqrt :
      ((1 : ℝ) / Real.sqrt ((((r : ℕ) + 1 : ℕ) : ℝ))) ^ 2 =
      1 / ((((r : ℕ) + 1 : ℕ) : ℝ)) := by
    rw [div_pow, one_pow]
    congr 1
  rw [mul_pow, div_pow, sq_abs, hinvsqrt]
  ring

/-- Base harmonic moment retained by the finite detector head on the long range. -/
def levinsonCriticalDetectorIncludedLongBaseMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovIncludedBaseCoeff L M k ^ 2 / (k : ℝ)

/-- Base/differentiated cross moment retained by the finite detector head. -/
def levinsonCriticalDetectorIncludedLongCrossMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovIncludedBaseCoeff L M k *
      Sieve.barbanVehovIncludedDifferentiatedCoeff L M k / (k : ℝ)

/-- Differentiated harmonic moment retained by the finite detector head. -/
def levinsonCriticalDetectorIncludedLongDerivativeMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovIncludedDifferentiatedCoeff L M k ^ 2 / (k : ℝ)

/-- Exact cancellation-preserving quadratic form for the finite detector's long energy. -/
theorem levinsonCriticalDetectorLongEnergy_eq_includedMomentQuadratic
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    levinsonCriticalDetectorLongEnergy lam L M =
      (levinsonCriticalDetectorIncludedLongBaseMoment L M +
          2 * lam * levinsonCriticalDetectorIncludedLongCrossMoment L M +
          lam ^ 2 * levinsonCriticalDetectorIncludedLongDerivativeMoment L M) /
        Real.log M ^ 2 := by
  unfold levinsonCriticalDetectorLongEnergy levinsonCriticalDetectorFiniteEnergyTerm
  rw [show
      (∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
          (fun r : Fin (L * M) => L < (r : ℕ) + 1),
        Complex.normSq (levinsonCriticalDetectorMollifiedFinCoeff lam L M r)) =
      ∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
          (fun r : Fin (L * M) => L < (r : ℕ) + 1),
        ((Sieve.barbanVehovIncludedBaseCoeff L M ((r : ℕ) + 1) +
            lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M ((r : ℕ) + 1)) ^ 2 /
          ((((r : ℕ) + 1 : ℕ) : ℝ)) / Real.log M ^ 2) by
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Complex.sq_norm,
      norm_levinsonCriticalDetectorMollifiedFinCoeff_sq_included lam L hM r]]
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ r ∈ (Finset.univ : Finset (Fin (L * M))).filter
        (fun r : Fin (L * M) => L < (r : ℕ) + 1),
      (Sieve.barbanVehovIncludedBaseCoeff L M ((r : ℕ) + 1) +
          lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M ((r : ℕ) + 1)) ^ 2 /
        ((((r : ℕ) + 1 : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Ioc L (L * M),
        (Sieve.barbanVehovIncludedBaseCoeff L M k +
            lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M k) ^ 2 /
          (k : ℝ) :=
      Sieve.sum_fin_filter_succ_gt_eq_sum_Ioc (L * M) L
        (fun k =>
          (Sieve.barbanVehovIncludedBaseCoeff L M k +
              lam * Sieve.barbanVehovIncludedDifferentiatedCoeff L M k) ^ 2 /
            (k : ℝ))
    _ = _ := by
      rw [levinsonCriticalDetectorIncludedLongBaseMoment,
        levinsonCriticalDetectorIncludedLongCrossMoment,
        levinsonCriticalDetectorIncludedLongDerivativeMoment]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end

end RHTower
