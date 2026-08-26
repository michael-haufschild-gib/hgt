import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongCoefficientDecomposition

/-!
# Arithmetic moment expansion of the omitted detector-head boundary

The head divisors omitted above `L` are reoriented onto their complementary mollifier divisors.
This identifies the exact truncated differentiated Barban--Vehov coefficient and expands its long
energy into base, mixed, and differentiated harmonic moments.
-/

noncomputable section

namespace RHTower

open Complex Finset

/-- Reorient the omitted detector-head sum onto complementary mollifier divisors. -/
theorem levinsonCriticalDetectorOmittedHeadCoeff_eq_complementaryDivisorSum
    (lam : ℝ) (L M k : ℕ) :
    levinsonCriticalDetectorOmittedHeadCoeff lam L M k =
      ∑ q ∈ k.divisors.filter (fun q => L * q < k),
        Sieve.levinsonCriticalDetectorHeadCoeff lam (k / q) *
          Sieve.levinsonLinearMollifierCoeff M q := by
  classical
  rw [levinsonCriticalDetectorOmittedHeadCoeff]
  rw [Finset.sum_filter, Finset.sum_filter]
  let F : ℕ → ℕ → ℂ := fun d q =>
    if L < d then
      Sieve.levinsonCriticalDetectorHeadCoeff lam d *
        Sieve.levinsonLinearMollifierCoeff M q
    else 0
  have hreindex :
      (∑ d ∈ k.divisors, F d (k / d)) =
        ∑ q ∈ k.divisors, F (k / q) q := by
    exact (Nat.sum_divisorsAntidiagonal F).symm.trans
      (Nat.sum_divisorsAntidiagonal' F)
  change (∑ d ∈ k.divisors, F d (k / d)) = _
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
  have hqdvd : q ∣ k := Nat.dvd_of_mem_divisors hq
  have hmul : k / q * q = k := Nat.div_mul_cancel hqdvd
  have hiff : L < k / q ↔ L * q < k := by
    constructor
    · intro h
      rw [← hmul]
      exact (Nat.mul_lt_mul_right hqpos).2 h
    · intro h
      rw [← hmul] at h
      exact (Nat.mul_lt_mul_right hqpos).1 h
  dsimp only [F]
  simp only [hiff]

/-- Truncated base divisor sum supplied by detector-head terms above `L`. -/
def Sieve.barbanVehovOmittedBaseCoeff (L M k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors.filter (fun q => L * q < k),
    Sieve.barbanVehovWeight M q

/-- Log-differentiated truncated divisor sum supplied by detector-head terms above `L`. -/
def Sieve.barbanVehovOmittedDifferentiatedCoeff (L M k : ℕ) : ℝ :=
  -∑ q ∈ k.divisors.filter (fun q => L * q < k),
    Sieve.barbanVehovWeight M q * Real.log (((k / q : ℕ) : ℝ))

/-- The omitted head coefficient is the normalized truncated differentiated Barban--Vehov sum. -/
theorem levinsonCriticalDetectorOmittedHeadCoeff_eq_arithmetic
    (lam : ℝ) (L M : ℕ) {k : ℕ} (hk : 0 < k) :
    levinsonCriticalDetectorOmittedHeadCoeff lam L M k =
      ((((Sieve.barbanVehovOmittedBaseCoeff L M k +
          lam * Sieve.barbanVehovOmittedDifferentiatedCoeff L M k) /
        Real.log M) * (1 / Real.sqrt k) : ℝ) : ℂ) := by
  rw [levinsonCriticalDetectorOmittedHeadCoeff_eq_complementaryDivisorSum]
  rw [Sieve.barbanVehovOmittedBaseCoeff,
    Sieve.barbanVehovOmittedDifferentiatedCoeff]
  simp_rw [Sieve.levinsonCriticalDetectorHeadCoeff,
    Sieve.levinsonLinearMollifierCoeff]
  norm_cast
  calc
    ∑ q ∈ k.divisors.filter (fun q => L * q < k),
        (1 / Real.sqrt (((k / q : ℕ) : ℝ)) *
            (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) *
          (Sieve.barbanVehovWeight M q / Real.log M *
            (1 / Real.sqrt q)) =
      ∑ q ∈ k.divisors.filter (fun q => L * q < k),
        ((Sieve.barbanVehovWeight M q *
            (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) / Real.log M) *
          (1 / Real.sqrt k) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqdvd : q ∣ k :=
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1
      rw [show
        (1 / Real.sqrt (((k / q : ℕ) : ℝ)) *
              (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) *
            (Sieve.barbanVehovWeight M q / Real.log M *
              (1 / Real.sqrt q)) =
          ((Sieve.barbanVehovWeight M q *
              (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) / Real.log M) *
            ((1 / Real.sqrt (((k / q : ℕ) : ℝ))) *
              (1 / Real.sqrt q)) by ring]
      rw [Sieve.one_div_sqrt_div_mul_one_div_sqrt_of_dvd hk hqdvd]
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have hsum :
          (∑ q ∈ k.divisors.filter (fun q => L * q < k),
              Sieve.barbanVehovWeight M q *
                (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) =
            (∑ q ∈ k.divisors.filter (fun q => L * q < k),
                Sieve.barbanVehovWeight M q) -
              lam *
                ∑ q ∈ k.divisors.filter (fun q => L * q < k),
                  Sieve.barbanVehovWeight M q *
                    Real.log (((k / q : ℕ) : ℝ)) := by
        calc
          _ = ∑ q ∈ k.divisors.filter (fun q => L * q < k),
                (Sieve.barbanVehovWeight M q -
                  lam * (Sieve.barbanVehovWeight M q *
                    Real.log (((k / q : ℕ) : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
          _ = _ := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum]
      ring

/-- Exact square norm of one omitted detector-head coefficient. -/
theorem norm_levinsonCriticalDetectorOmittedHeadCoeff_sq
    (lam : ℝ) (L : ℕ) {M k : ℕ} (hM : 1 < M) (hk : 0 < k) :
    ‖levinsonCriticalDetectorOmittedHeadCoeff lam L M k‖ ^ 2 =
      (Sieve.barbanVehovOmittedBaseCoeff L M k +
          lam * Sieve.barbanVehovOmittedDifferentiatedCoeff L M k) ^ 2 /
        (k : ℝ) / Real.log M ^ 2 := by
  rw [levinsonCriticalDetectorOmittedHeadCoeff_eq_arithmetic lam L M hk,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div]
  have hlog : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast hM)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [abs_of_pos hlog,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt k)]
  have hsqrt : (Real.sqrt (k : ℝ)) ^ 2 = k := Real.sq_sqrt hkR.le
  have hinvsqrt : ((1 : ℝ) / Real.sqrt k) ^ 2 = 1 / (k : ℝ) := by
    field_simp
    nlinarith
  rw [mul_pow, div_pow, sq_abs, hinvsqrt]
  ring

/-- Base harmonic energy of the omitted detector-head boundary. -/
def levinsonCriticalDetectorOmittedLongBaseMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovOmittedBaseCoeff L M k ^ 2 / (k : ℝ)

/-- Base/derivative cross moment of the omitted detector-head boundary. -/
def levinsonCriticalDetectorOmittedLongCrossMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovOmittedBaseCoeff L M k *
      Sieve.barbanVehovOmittedDifferentiatedCoeff L M k / (k : ℝ)

/-- Differentiated harmonic energy of the omitted detector-head boundary. -/
def levinsonCriticalDetectorOmittedLongDerivativeMoment (L M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc L (L * M),
    Sieve.barbanVehovOmittedDifferentiatedCoeff L M k ^ 2 / (k : ℝ)

/-- The omitted-head energy is exactly a quadratic form in three truncated harmonic moments. -/
theorem levinsonCriticalDetectorOmittedLongEnergy_eq_momentQuadratic
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    levinsonCriticalDetectorOmittedLongEnergy lam L M =
      (levinsonCriticalDetectorOmittedLongBaseMoment L M +
          2 * lam * levinsonCriticalDetectorOmittedLongCrossMoment L M +
          lam ^ 2 * levinsonCriticalDetectorOmittedLongDerivativeMoment L M) /
        Real.log M ^ 2 := by
  rw [levinsonCriticalDetectorOmittedLongEnergy_eq_sum_Ioc]
  rw [levinsonCriticalDetectorOmittedLongBaseMoment,
    levinsonCriticalDetectorOmittedLongCrossMoment,
    levinsonCriticalDetectorOmittedLongDerivativeMoment]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_levinsonCriticalDetectorOmittedHeadCoeff_sq lam L hM
    (by have := (Finset.mem_Ioc.mp hk).1; omega)]
  ring

end RHTower
