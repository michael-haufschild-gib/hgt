import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner

/-!
# Gamma-sewn Möbius valuation contraction

The inverse dressing from the summable Möbius--Schur depth frame to the undamped
Gamma--valuation frame is unbounded along the primes.  The doubled-frequency archimedean
characteristic has exactly the complementary amplitude decay.  Sewing the two source factors
before completing over primes gives the multiplier

`(1 / 2) * sqrt(phi_infty(2 x log p)) * (1 + q) / sqrt(q)`,

where `q = exp(-x log p)` is the true aperture node.  Its fourth power is

`(1 + q)^4 / (8 * (1 + q^4))`.

Consequently it is a strict contraction for every positive aperture, becomes lossless only at
the zero-aperture boundary, and never kills a prime coordinate.  At unit aperture its second
factor is literally the previously constructed Möbius valuation recovery.  This is the
source-derived infinite multiplier exposed by combining the two earlier no-go/survivor pairs; it
does not prove the remaining convergence to the continued prime--archimedean response.
-/

namespace RHTower

noncomputable section

/-- The analytic-aperture continuation of the inverse Möbius--Schur dressing. -/
def xiMobiusPrimeSchurApertureValuationRecovery
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode x p
  (1 + q) / Real.sqrt q

/-- Gamma sewing of the inverse Möbius dressing, normalized to have boundary norm one. -/
def gammaSewnMobiusValuationContractionMultiplier
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  (1 / 2 : ℝ) *
    Real.sqrt
      (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ))) *
    xiMobiusPrimeSchurApertureValuationRecovery x p

/-- The aperture continuation agrees with the actual unit-aperture recovery. -/
theorem xiMobiusPrimeSchurApertureValuationRecovery_one
    (p : Nat.Primes) :
    xiMobiusPrimeSchurApertureValuationRecovery 1 p =
      xiMobiusPrimeSchurValuationRecovery p := by
  simp only [xiMobiusPrimeSchurApertureValuationRecovery,
    xiMobiusPrimeSchurValuationRecovery]

/-- The doubled-frequency Gamma characteristic written in the true aperture disk coordinate. -/
theorem semilocalArchimedeanCharacteristic_two_aperture_log_sq
    (x : ℝ) (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)) ^ 2 =
      let q := xiTransversePrimeApertureDiskNode x p
      2 * q ^ 2 / (1 + q ^ 4) := by
  let u := x * Real.log (p : ℝ)
  let q := xiTransversePrimeApertureDiskNode x p
  have hqpos : 0 < q := xiTransversePrimeApertureDiskNode_pos x p
  have hqne : q ≠ 0 := hqpos.ne'
  have hqexp : q = Real.exp (-u) := by
    simp only [q, u, xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hexp_mul : Real.exp u * q = 1 := by
    rw [hqexp, ← Real.exp_add]
    simp
  rw [show 2 * x * Real.log (p : ℝ) = 2 * u by simp [u, mul_assoc],
    semilocalArchimedeanCharacteristic_sq, Real.cosh_eq]
  change ((Real.exp (2 * u) + Real.exp (-(2 * u))) / 2)⁻¹ =
    2 * q ^ 2 / (1 + q ^ 4)
  rw [Real.exp_two_mul, show -(2 * u) = 2 * (-u) by ring,
    Real.exp_two_mul, ← hqexp]
  field_simp [hqne]
  nlinarith

/-- Exact fourth-power law of the sewn source multiplier. -/
theorem gammaSewnMobiusValuationContractionMultiplier_pow_four
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p ^ 4 =
      let q := xiTransversePrimeApertureDiskNode x p
      (1 + q) ^ 4 / (8 * (1 + q ^ 4)) := by
  let q := xiTransversePrimeApertureDiskNode x p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos x p).le
  have hqne : q ≠ 0 := (xiTransversePrimeApertureDiskNode_pos x p).ne'
  have hchar0 :
      0 ≤ semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)) := by
    exact (semilocalArchimedeanCharacteristic_pos _).le
  rw [gammaSewnMobiusValuationContractionMultiplier,
    xiMobiusPrimeSchurApertureValuationRecovery]
  change ((1 / 2 : ℝ) *
      Real.sqrt (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ))) *
      ((1 + q) / Real.sqrt q)) ^ 4 = _
  rw [show ((1 / 2 : ℝ) *
      Real.sqrt (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ))) *
      ((1 + q) / Real.sqrt q)) ^ 4 =
      (1 / 16 : ℝ) *
        semilocalArchimedeanCharacteristic
          (2 * x * Real.log (p : ℝ)) ^ 2 *
        (1 + q) ^ 4 / q ^ 2 by
      rw [mul_pow, mul_pow, div_pow,
        show (Real.sqrt
          (semilocalArchimedeanCharacteristic
            (2 * x * Real.log (p : ℝ)))) ^ 4 =
          semilocalArchimedeanCharacteristic
            (2 * x * Real.log (p : ℝ)) ^ 2 by
          rw [show (Real.sqrt
            (semilocalArchimedeanCharacteristic
              (2 * x * Real.log (p : ℝ)))) ^ 4 =
            (Real.sqrt
              (semilocalArchimedeanCharacteristic
                (2 * x * Real.log (p : ℝ))) ^ 2) ^ 2 by ring,
            Real.sq_sqrt hchar0],
        Real.sq_sqrt hq0]
      ring]
  rw [semilocalArchimedeanCharacteristic_two_aperture_log_sq]
  change (1 / 16 : ℝ) * (2 * q ^ 2 / (1 + q ^ 4)) *
      (1 + q) ^ 4 / q ^ 2 =
    (1 + q) ^ 4 / (8 * (1 + q ^ 4))
  field_simp [hqne]

/-- Algebraic factorization behind strict contractivity away from the boundary node `q=1`. -/
theorem gammaSewnMobiusValuationContraction_gap_factorization (q : ℝ) :
    8 * (1 + q ^ 4) - (1 + q) ^ 4 =
      (1 - q) ^ 2 * (7 * q ^ 2 + 10 * q + 7) := by
  ring

/-- The sewn multiplier is positive at every real aperture. -/
theorem gammaSewnMobiusValuationContractionMultiplier_pos
    (x : ℝ) (p : Nat.Primes) :
    0 < gammaSewnMobiusValuationContractionMultiplier x p := by
  unfold gammaSewnMobiusValuationContractionMultiplier
    xiMobiusPrimeSchurApertureValuationRecovery
  have hq := xiTransversePrimeApertureDiskNode_pos x p
  exact mul_pos
    (mul_pos (by norm_num)
      (Real.sqrt_pos.2 (semilocalArchimedeanCharacteristic_pos _)))
    (div_pos (by linarith) (Real.sqrt_pos.2 hq))

/-- On every positive aperture the source-sewn multiplier is a strict contraction. -/
theorem gammaSewnMobiusValuationContractionMultiplier_lt_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p < 1 := by
  let q := xiTransversePrimeApertureDiskNode x p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos x p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one hx p
  have hden : 0 < 8 * (1 + q ^ 4) := by positivity
  have hbracket : 0 < 7 * q ^ 2 + 10 * q + 7 := by positivity
  have hgap : (1 + q) ^ 4 < 8 * (1 + q ^ 4) := by
    nlinarith [gammaSewnMobiusValuationContraction_gap_factorization q,
      sq_pos_of_ne_zero (sub_ne_zero.mpr hq1.ne)]
  have hpow :
      gammaSewnMobiusValuationContractionMultiplier x p ^ 4 < 1 := by
    rw [gammaSewnMobiusValuationContractionMultiplier_pow_four]
    change (1 + q) ^ 4 / (8 * (1 + q ^ 4)) < 1
    exact (div_lt_one hden).2 hgap
  have hpos := gammaSewnMobiusValuationContractionMultiplier_pos x p
  nlinarith [sq_nonneg
    (gammaSewnMobiusValuationContractionMultiplier x p ^ 2 - 1)]

/-- At zero aperture the sewn multiplier reaches the lossless boundary value. -/
theorem gammaSewnMobiusValuationContractionMultiplier_zero
    (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier 0 p = 1 := by
  rw [gammaSewnMobiusValuationContractionMultiplier]
  simp [xiMobiusPrimeSchurApertureValuationRecovery,
    xiTransversePrimeApertureDiskNode]

/-- Pointwise action of the source-sewn contraction on the full prime--valuation stream. -/
def gammaSewnMobiusValuationContraction
    (x : ℝ) :
    ((Nat.Primes × ℕ) → ℂ) →ₗ[ℂ] ((Nat.Primes × ℕ) → ℂ) where
  toFun f pe :=
    (gammaSewnMobiusValuationContractionMultiplier x pe.1 : ℂ) * f pe
  map_add' f g := by
    funext pe
    simp [mul_add]
  map_smul' c f := by
    funext pe
    simp
    ring

@[simp] theorem gammaSewnMobiusValuationContraction_apply
    (x : ℝ) (f : (Nat.Primes × ℕ) → ℂ) (pe : Nat.Primes × ℕ) :
    gammaSewnMobiusValuationContraction x f pe =
      (gammaSewnMobiusValuationContractionMultiplier x pe.1 : ℂ) * f pe :=
  rfl

/-- The infinite sewn contraction loses no prime or valuation coordinate. -/
theorem gammaSewnMobiusValuationContraction_injective (x : ℝ) :
    Function.Injective (gammaSewnMobiusValuationContraction x) := by
  intro f g hfg
  funext pe
  have hpe := congrFun hfg pe
  simp only [gammaSewnMobiusValuationContraction_apply] at hpe
  exact mul_left_cancel₀
    (Complex.ofReal_ne_zero.mpr
      (gammaSewnMobiusValuationContractionMultiplier_pos x pe.1).ne') hpe

end

end RHTower
