import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.HTGeometry.PositiveSummabilityComparison

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
the zero-aperture boundary, and never kills a prime coordinate.  Its defect has exact quadratic
tangency to the physical aperture node, so its correction of the linear Möbius valuation ray is
exactly cubic.  At unit aperture its second factor is literally the previously constructed Möbius
valuation recovery.

Applying the multiplier to the actual fixed-critical continuous-aperture Möbius frame produces an
all-prime, complete-valuation Hilbert metric.  Its diagonal is summable at every positive aperture,
and every finite injective prime packet retains full weighted-Vandermonde rank.  The uniform lower
bound also proves a sharp no-go: sewing preserves summability and cannot act as a hidden compact
cutoff.  These are source-side crossing data; they do not prove the remaining convergence to the
continued prime--archimedean response.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Filter Matrix Set

/-- The analytic-aperture continuation of the inverse Möbius--Schur dressing. -/
def xiMobiusPrimeSchurApertureValuationRecovery
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
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
  unfold xiMobiusPrimeSchurApertureValuationRecovery
    xiMobiusPrimeSchurValuationRecovery
  unfold xiMobiusContinuousApertureDiskNode
    xiTransversePrimeApertureDiskNode
  norm_num

/-- The doubled-frequency Gamma characteristic written in the true aperture disk coordinate. -/
theorem semilocalArchimedeanCharacteristic_two_aperture_log_sq
    (x : ℝ) (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)) ^ 2 =
      let q := xiMobiusContinuousApertureDiskNode x p
      2 * q ^ 2 / (1 + q ^ 4) := by
  let u := x * Real.log (p : ℝ)
  let q := xiMobiusContinuousApertureDiskNode x p
  have hqpos : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hqne : q ≠ 0 := hqpos.ne'
  have hqexp : q = Real.exp (-u) := by
    simp only [q, u, xiMobiusContinuousApertureDiskNode]
    congr 1
    ring
  have hexp_mul : Real.exp u * q = 1 := by
    rw [hqexp, ← Real.exp_add]
    simp
  rw [show 2 * x * Real.log (p : ℝ) = 2 * u by simp [u, mul_assoc],
    semilocalArchimedeanCharacteristic_sq, Real.cosh_eq]
  change ((Real.exp (2 * u) + Real.exp (-(2 * u))) / 2)⁻¹ =
    2 * q ^ 2 / (1 + q ^ 4)
  rw [show -(2 * u) = (-u) + (-u) by ring,
    show 2 * u = u + u by ring, Real.exp_add, Real.exp_add, ← hqexp]
  field_simp [hqne]
  nlinarith [hexp_mul]

/-- Exact fourth-power law of the sewn source multiplier. -/
theorem gammaSewnMobiusValuationContractionMultiplier_pow_four
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p ^ 4 =
      let q := xiMobiusContinuousApertureDiskNode x p
      (1 + q) ^ 4 / (8 * (1 + q ^ 4)) := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 ≤ q := (xiMobiusContinuousApertureDiskNode_pos x p).le
  have hqne : q ≠ 0 := (xiMobiusContinuousApertureDiskNode_pos x p).ne'
  have hchar0 :
      0 ≤ semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)) := by
    exact (Real.rpow_pos_of_pos (Real.cosh_pos _) (-(1 : ℝ) / 2)).le
  rw [gammaSewnMobiusValuationContractionMultiplier,
    xiMobiusPrimeSchurApertureValuationRecovery]
  change ((1 / 2 : ℝ) *
      Real.sqrt (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ))) *
      ((1 + q) / Real.sqrt q)) ^ 4 =
        (1 + q) ^ 4 / (8 * (1 + q ^ 4))
  have hchar4 : (Real.sqrt
      (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)))) ^ 4 =
      (semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ))) ^ 2 := by
    calc
      (Real.sqrt
          (semilocalArchimedeanCharacteristic
            (2 * x * Real.log (p : ℝ)))) ^ 4 =
          (Real.sqrt
            (semilocalArchimedeanCharacteristic
              (2 * x * Real.log (p : ℝ))) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hchar0]
  have hq4 : (Real.sqrt q) ^ 4 = q ^ 2 := by
    calc
      (Real.sqrt q) ^ 4 = (Real.sqrt q ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hq0]
  calc
    ((1 / 2 : ℝ) *
        Real.sqrt (semilocalArchimedeanCharacteristic
          (2 * x * Real.log (p : ℝ))) *
        ((1 + q) / Real.sqrt q)) ^ 4 =
      (1 / 16 : ℝ) *
        semilocalArchimedeanCharacteristic
          (2 * x * Real.log (p : ℝ)) ^ 2 *
        (1 + q) ^ 4 / q ^ 2 := by
          rw [mul_pow, mul_pow, hchar4]
          simp only [div_pow]
          rw [hq4]
          ring
    _ = (1 + q) ^ 4 / (8 * (1 + q ^ 4)) := by
      have hcharFormula :
          semilocalArchimedeanCharacteristic
              (2 * x * Real.log (p : ℝ)) ^ 2 =
            2 * q ^ 2 / (1 + q ^ 4) := by
        simpa only [q] using
          semilocalArchimedeanCharacteristic_two_aperture_log_sq x p
      rw [hcharFormula]
      field_simp [hqne]
      norm_num

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
  have hq := xiMobiusContinuousApertureDiskNode_pos x p
  have hchar : 0 < semilocalArchimedeanCharacteristic
      (2 * x * Real.log (p : ℝ)) :=
    Real.rpow_pos_of_pos (Real.cosh_pos _) (-(1 : ℝ) / 2)
  exact mul_pos
    (mul_pos (by norm_num)
      (Real.sqrt_pos.2 hchar))
    (div_pos (by linarith) (Real.sqrt_pos.2 hq))

/-- On every positive aperture the source-sewn multiplier is a strict contraction. -/
theorem gammaSewnMobiusValuationContractionMultiplier_lt_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p < 1 := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
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

/-- The sewn multiplier is uniformly bounded away from zero.  This is the precise reason that it
preserves prime information, but also why it cannot by itself Hilbertize a divergent source. -/
theorem one_half_lt_gammaSewnMobiusValuationContractionMultiplier
    (x : ℝ) (p : Nat.Primes) :
    (1 / 2 : ℝ) < gammaSewnMobiusValuationContractionMultiplier x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  have hq : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hden : 0 < 8 * (1 + q ^ 4) := by positivity
  have hpoly : 0 < 4 * q + 6 * q ^ 2 + 4 * q ^ 3 := by positivity
  have hnum : 1 + q ^ 4 < (1 + q) ^ 4 := by
    nlinarith [show (1 + q) ^ 4 - (1 + q ^ 4) =
      4 * q + 6 * q ^ 2 + 4 * q ^ 3 by ring]
  have hc4 : (1 / 8 : ℝ) < c ^ 4 := by
    rw [show c ^ 4 = (1 + q) ^ 4 / (8 * (1 + q ^ 4)) by
      simpa only [c, q] using
        gammaSewnMobiusValuationContractionMultiplier_pow_four x p]
    rw [lt_div_iff₀ hden]
    nlinarith
  have hc0 : 0 < c :=
    gammaSewnMobiusValuationContractionMultiplier_pos x p
  by_contra hnot
  have hc : c ≤ 1 / 2 := le_of_not_gt hnot
  have hc2 : c ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hc) (by linarith : 0 ≤ c + 1 / 2)]
  have hc4upper : c ^ 4 ≤ 1 / 16 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hc2) (by positivity : 0 ≤ c ^ 2 + 1 / 4)]
  nlinarith

/-- **No free Hilbertization.**  On a positive aperture, Gamma sewing preserves summability of
every nonnegative prime energy exactly.  It is a boundedly invertible localization, not a hidden
compact cutoff. -/
theorem summable_gammaSewnMobiusMultiplier_sq_mul_iff
    {x : ℝ} (hx : 0 < x) (a : Nat.Primes → ℝ) (ha : ∀ p, 0 ≤ a p) :
    Summable (fun p =>
      gammaSewnMobiusValuationContractionMultiplier x p ^ 2 * a p) ↔
      Summable a := by
  apply HTGeometry.summable_mul_iff_of_nonneg_of_uniform_pos_le_of_le
    (c := 1 / 4) (C := 1) a
    (fun p => gammaSewnMobiusValuationContractionMultiplier x p ^ 2)
    ha (by norm_num : (0 : ℝ) < 1 / 4)
  · intro p
    have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
    have hc := one_half_lt_gammaSewnMobiusValuationContractionMultiplier x p
    nlinarith [mul_pos
      (sub_pos.mpr hc)
      (by linarith : 0 <
        gammaSewnMobiusValuationContractionMultiplier x p + 1 / 2)]
  · intro p
    have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
    have hc1 := gammaSewnMobiusValuationContractionMultiplier_lt_one hx p
    nlinarith [mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hc1.le) (by linarith : 0 ≤
        gammaSewnMobiusValuationContractionMultiplier x p + 1)]

/-- At zero aperture the sewn multiplier reaches the lossless boundary value. -/
theorem gammaSewnMobiusValuationContractionMultiplier_zero
    (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier 0 p = 1 := by
  rw [gammaSewnMobiusValuationContractionMultiplier]
  simp [xiMobiusPrimeSchurApertureValuationRecovery,
    xiMobiusContinuousApertureDiskNode,
    semilocalArchimedeanCharacteristic]
  norm_num

/-- The regular gain after extracting the exact quadratic true-aperture defect of Gamma sewing. -/
def gammaSewnMobiusValuationQuadraticDefectGain
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  (7 * q ^ 2 + 10 * q + 7) /
    (8 * (1 + q ^ 4) * (1 + c) * (1 + c ^ 2))

/-- **Exact quadratic tangency.**  The contraction first departs from the identity by two copies
of the physical aperture increment `1-p^{-x}`. -/
theorem one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain
    (x : ℝ) (p : Nat.Primes) :
    1 - gammaSewnMobiusValuationContractionMultiplier x p =
      (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2 *
        gammaSewnMobiusValuationQuadraticDefectGain x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hqden : 8 * (1 + q ^ 4) ≠ 0 := by positivity
  have hcplus : 1 + c ≠ 0 := by positivity
  have hcsqplus : 1 + c ^ 2 ≠ 0 := by positivity
  have hpow : c ^ 4 = (1 + q) ^ 4 / (8 * (1 + q ^ 4)) := by
    simpa only [c, q] using
      gammaSewnMobiusValuationContractionMultiplier_pow_four x p
  have honefour :
      1 - c ^ 4 =
        (1 - q) ^ 2 * (7 * q ^ 2 + 10 * q + 7) /
          (8 * (1 + q ^ 4)) := by
    rw [hpow]
    field_simp [hqden]
    nlinarith [gammaSewnMobiusValuationContraction_gap_factorization q]
  change 1 - c = (1 - q) ^ 2 *
    ((7 * q ^ 2 + 10 * q + 7) /
      (8 * (1 + q ^ 4) * (1 + c) * (1 + c ^ 2)))
  rw [show (1 - q) ^ 2 *
      ((7 * q ^ 2 + 10 * q + 7) /
        (8 * (1 + q ^ 4) * (1 + c) * (1 + c ^ 2))) =
      (1 - c ^ 4) / ((1 + c) * (1 + c ^ 2)) by
    rw [honefour]
    field_simp [hqden, hcplus, hcsqplus]]
  field_simp [hcplus, hcsqplus]
  ring

/-- The extracted quadratic gain reaches the exact boundary coefficient `3/8`. -/
@[simp] theorem gammaSewnMobiusValuationQuadraticDefectGain_zero
    (p : Nat.Primes) :
    gammaSewnMobiusValuationQuadraticDefectGain 0 p = 3 / 8 := by
  simp [gammaSewnMobiusValuationQuadraticDefectGain,
    gammaSewnMobiusValuationContractionMultiplier_zero,
    xiMobiusContinuousApertureDiskNode]
  norm_num

/-- The Gamma-sewn feature of the actual fixed-critical Möbius continuous-aperture source.
The critical prime damping remains in the source; only its valuation ray moves with `x`. -/
def gammaSewnMobiusContinuousApertureFeature
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusValuationContractionMultiplier x p *
    xiMobiusPrimeSchurContinuousForwardDifference x p e

/-- **Cubic sewing law.**  The difference between the sewn and unsewn source features contains
exactly three copies of the true aperture increment.  The cubic order is forced by quadratic
Gamma tangency plus the linear Möbius valuation increment. -/
theorem gammaSewnMobiusContinuousApertureFeature_sub_source_eq_cubic
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusContinuousApertureFeature x p e -
        xiMobiusPrimeSchurContinuousForwardDifference x p e =
      -gammaSewnMobiusValuationQuadraticDefectGain x p *
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ 3 *
        xiMobiusContinuousApertureDiskNode x p ^ e := by
  calc
    gammaSewnMobiusContinuousApertureFeature x p e -
        xiMobiusPrimeSchurContinuousForwardDifference x p e =
      -(1 - gammaSewnMobiusValuationContractionMultiplier x p) *
        xiMobiusPrimeSchurContinuousForwardDifference x p e := by
          rw [gammaSewnMobiusContinuousApertureFeature]
          ring
    _ = _ := by
      rw [one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
      ring

/-- At unit aperture the sewn feature is literally the doubled-frequency Gamma amplitude times
the previously proved recovered Gamma--valuation coordinate. -/
theorem gammaSewnMobiusContinuousApertureFeature_one_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusContinuousApertureFeature 1 p e =
      (1 / 2 : ℝ) *
        Real.sqrt
          (semilocalArchimedeanCharacteristic (2 * Real.log (p : ℝ))) *
        xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  have hnode : xiMobiusContinuousApertureDiskNode 1 p =
      xiTransversePrimeApertureDiskNode 1 p := by
    unfold xiMobiusContinuousApertureDiskNode
      xiTransversePrimeApertureDiskNode
    norm_num
  have hforward : xiMobiusPrimeSchurContinuousForwardDifference 1 p e =
      xiMobiusPrimeSchurForwardDifference p e := by
    rw [xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
      xiMobiusPrimeSchurForwardDifference_eq_geometric, hnode]
    ring
  rw [gammaSewnMobiusContinuousApertureFeature, hforward,
    gammaSewnMobiusValuationContractionMultiplier,
    xiMobiusPrimeSchurApertureValuationRecovery_one]
  rw [show 2 * 1 * Real.log (p : ℝ) = 2 * Real.log (p : ℝ) by ring]
  calc
    (1 / 2 : ℝ) *
          Real.sqrt (semilocalArchimedeanCharacteristic (2 * Real.log (p : ℝ))) *
        xiMobiusPrimeSchurValuationRecovery p *
      xiMobiusPrimeSchurForwardDifference p e =
        (1 / 2 : ℝ) *
          Real.sqrt (semilocalArchimedeanCharacteristic (2 * Real.log (p : ℝ))) *
            (xiMobiusPrimeSchurValuationRecovery p *
              xiMobiusPrimeSchurForwardDifference p e) := by ring
    _ = _ := by rw [xiMobiusPrimeSchurValuationRecovery_mul_forwardDifference]

/-! ## All-order Rees principal symbols -/

/-- Iterated forward difference of the sewn source in valuation depth.  The iteration index is the
Rees grade minus one. -/
def gammaSewnMobiusContinuousApertureDepthDifference :
    ℕ → ℝ → Nat.Primes → ℕ → ℝ
  | 0, x, p, e => gammaSewnMobiusContinuousApertureFeature x p e
  | k + 1, x, p, e =>
      gammaSewnMobiusContinuousApertureDepthDifference k x p (e + 1) -
        gammaSewnMobiusContinuousApertureDepthDifference k x p e

/-- Every iterated valuation difference is still one geometric ray, with one new copy of the
physical aperture increment at each Rees grade. -/
theorem gammaSewnMobiusContinuousApertureDepthDifference_eq_geometric
    (k : ℕ) (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusContinuousApertureDepthDifference k x p e =
      (-1 : ℝ) ^ k * gammaSewnMobiusValuationContractionMultiplier x p *
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ (k + 1) *
        xiMobiusContinuousApertureDiskNode x p ^ e := by
  induction k generalizing e with
  | zero =>
      rw [gammaSewnMobiusContinuousApertureDepthDifference,
        gammaSewnMobiusContinuousApertureFeature,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
      ring
  | succ k ih =>
      rw [gammaSewnMobiusContinuousApertureDepthDifference, ih (e + 1), ih e,
        pow_succ (xiMobiusContinuousApertureDiskNode x p) e]
      rw [pow_succ (-1 : ℝ) k,
        show k + 1 + 1 = (k + 1) + 1 by omega,
        pow_succ (1 - xiMobiusContinuousApertureDiskNode x p) (k + 1)]
      ring

/-- The sewing multiplier is continuous at the lossless aperture boundary. -/
theorem continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero
    (p : Nat.Primes) :
    ContinuousAt (fun x : ℝ =>
      gammaSewnMobiusValuationContractionMultiplier x p) 0 := by
  unfold gammaSewnMobiusValuationContractionMultiplier
    xiMobiusPrimeSchurApertureValuationRecovery
    semilocalArchimedeanCharacteristic
    xiMobiusContinuousApertureDiskNode
  have hq : Real.exp (-(0 : ℝ) * Real.log (p : ℝ)) ≠ 0 := by positivity
  have hchar : 0 <
      Real.cosh (2 * (0 : ℝ) * Real.log (p : ℝ)) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (Real.cosh_pos _) _
  fun_prop (disch := aesop)

/-- The all-order principal Rees symbol retained by Gamma sewing.  Grade `k` carries the
prime-log power `k+1` with the original critical Möbius damping. -/
def gammaSewnMobiusReesPrincipalSymbol (k : ℕ) (p : Nat.Primes) : ℝ :=
  (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) *
    Real.log (p : ℝ) ^ (k + 1)

/-- **All-order Rees symbol law.**  After the canonical sign and aperture normalization, every
iterated valuation difference converges to the corresponding prime-log symbol.  The limit is
independent of the starting valuation depth. -/
theorem tendsto_gammaSewnMobiusContinuousApertureDepthDifference_div_pow
    (k : ℕ) (p : Nat.Primes) (e : ℕ) :
    Tendsto
      (fun x : ℝ =>
        (-1 : ℝ) ^ k *
          gammaSewnMobiusContinuousApertureDepthDifference k x p e /
            x ^ (k + 1))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (gammaSewnMobiusReesPrincipalSymbol k p)) := by
  let q : ℝ := xiTransversePrimeApertureDiskNode 1 p
  let L : ℝ := Real.log (p : ℝ)
  let r : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let c : ℝ → ℝ := fun x =>
    gammaSewnMobiusValuationContractionMultiplier x p
  have hc : Tendsto c (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    have h : ContinuousWithinAt c (Ioi 0) 0 :=
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).continuousWithinAt
    simpa only [c, gammaSewnMobiusValuationContractionMultiplier_zero] using h.tendsto
  have hgap : Tendsto (fun x : ℝ => (1 - r x) / x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L) := by
    convert
      tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
        1 p using 1 <;> simp only [r, L, mul_one, one_mul]
  have hr : Tendsto (fun x : ℝ => r x ^ e)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    have hcont : ContinuousAt (fun x : ℝ => r x ^ e) 0 := by
      dsimp only [r]
      unfold xiMobiusContinuousApertureDiskNode
      fun_prop
    have hwithin : ContinuousWithinAt (fun x : ℝ => r x ^ e) (Ioi 0) 0 :=
      hcont.continuousWithinAt
    simpa only [r, xiMobiusContinuousApertureDiskNode, neg_zero, zero_mul,
      Real.exp_zero, one_pow] using hwithin.tendsto
  have hlimit : Tendsto
      (fun x : ℝ =>
        (-1 : ℝ) ^ k * (-1 : ℝ) ^ k * c x *
          (q / (1 + q)) * ((1 - r x) / x) ^ (k + 1) * r x ^ e)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * 1 *
        (q / (1 + q)) * L ^ (k + 1) * 1)) := by
    exact (((((tendsto_const_nhds.mul tendsto_const_nhds).mul hc).mul
      tendsto_const_nhds).mul (hgap.pow (k + 1))).mul hr)
  convert hlimit using 1
  · funext x
    rw [gammaSewnMobiusContinuousApertureDepthDifference_eq_geometric]
    change (-1 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * c x * (q / (1 + q)) *
          (1 - r x) ^ (k + 1) * r x ^ e) / x ^ (k + 1) = _
    rw [div_pow]
    ring
  · simp only [gammaSewnMobiusReesPrincipalSymbol, q, L]
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      simp
    rw [hsign]
    ring

/-- The first `N` Rees symbols on `N` primes.  Rows are increasing aperture grades and columns are
prime labels. -/
def gammaSewnMobiusReesPrincipalSymbolMatrix
    {N : ℕ} (p : Fin N → Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun k j => gammaSewnMobiusReesPrincipalSymbol k.val (p j)

/-- The Rees symbol matrix is a diagonally weighted Vandermonde on the prime logarithms. -/
theorem gammaSewnMobiusReesPrincipalSymbolMatrix_factorization
    {N : ℕ} (p : Fin N → Nat.Primes) :
    gammaSewnMobiusReesPrincipalSymbolMatrix p =
      (Matrix.vandermonde (fun j => Real.log ((p j : Nat.Primes) : ℝ)))ᵀ *
        Matrix.diagonal (fun j =>
          (xiTransversePrimeApertureDiskNode 1 (p j) /
            (1 + xiTransversePrimeApertureDiskNode 1 (p j))) *
          Real.log (p j : ℝ)) := by
  classical
  ext k j
  rw [Matrix.mul_diagonal]
  simp only [gammaSewnMobiusReesPrincipalSymbolMatrix,
    gammaSewnMobiusReesPrincipalSymbol, Matrix.transpose_apply,
    Matrix.vandermonde_apply]
  rw [pow_succ]
  ring

/-- **Unbounded exact Rees rank.**  Every injective `N`-prime packet is separated by its first
`N` Gamma-sewn principal symbols. -/
theorem gammaSewnMobiusReesPrincipalSymbolMatrix_det_ne_zero
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    (gammaSewnMobiusReesPrincipalSymbolMatrix p).det ≠ 0 := by
  let L : Fin N → ℝ := fun j => Real.log (p j : ℝ)
  let d : Fin N → ℝ := fun j =>
    (xiTransversePrimeApertureDiskNode 1 (p j) /
      (1 + xiTransversePrimeApertureDiskNode 1 (p j))) * L j
  have hL : Function.Injective L := by
    intro i j hij
    have hi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (p i).2.pos
    have hj : (0 : ℝ) < (p j : ℝ) := by exact_mod_cast (p j).2.pos
    have hreal : (p i : ℝ) = (p j : ℝ) := by
      rw [← Real.exp_log hi, ← Real.exp_log hj]
      exact congrArg Real.exp hij
    apply hp
    apply Subtype.ext
    exact_mod_cast hreal
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    have hq : 0 < xiTransversePrimeApertureDiskNode 1 (p j) :=
      xiTransversePrimeApertureDiskNode_pos 1 (p j)
    have hp1 : (1 : ℝ) < (p j : ℝ) := by
      exact_mod_cast (p j).2.one_lt
    dsimp only [d, L]
    exact mul_ne_zero
      (div_ne_zero hq.ne' (by positivity))
      (Real.log_pos hp1).ne'
  rw [gammaSewnMobiusReesPrincipalSymbolMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hL
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- Closed all-prime, complete-valuation Gram kernel of the Gamma-sewn source rays. -/
def gammaSewnMobiusContinuousAperturePrimeKernel
    (x : ℝ) (p r : Nat.Primes) : ℝ :=
  let qp := xiTransversePrimeApertureDiskNode 1 p
  let qr := xiTransversePrimeApertureDiskNode 1 r
  let u := xiMobiusContinuousApertureDiskNode x p
  let v := xiMobiusContinuousApertureDiskNode x r
  gammaSewnMobiusValuationContractionMultiplier x p *
    gammaSewnMobiusValuationContractionMultiplier x r *
    (qp / (1 + qp)) * (qr / (1 + qr)) *
    (1 - u) * (1 - v) / (1 - u * v)

/-- The closed sewn kernel is exactly the completed Gram over the full valuation tower. -/
theorem tsum_gammaSewnMobiusContinuousApertureFeature_mul_eq_kernel
    {x : ℝ} (hx : 0 < x) (p r : Nat.Primes) :
    (∑' e : ℕ, gammaSewnMobiusContinuousApertureFeature x p e *
      gammaSewnMobiusContinuousApertureFeature x r e) =
        gammaSewnMobiusContinuousAperturePrimeKernel x p r := by
  let qp := xiTransversePrimeApertureDiskNode 1 p
  let qr := xiTransversePrimeApertureDiskNode 1 r
  let u := xiMobiusContinuousApertureDiskNode x p
  let v := xiMobiusContinuousApertureDiskNode x r
  let cp := gammaSewnMobiusValuationContractionMultiplier x p
  let cr := gammaSewnMobiusValuationContractionMultiplier x r
  have hu0 : 0 ≤ u := (xiMobiusContinuousApertureDiskNode_pos x p).le
  have hv0 : 0 ≤ v := (xiMobiusContinuousApertureDiskNode_pos x r).le
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hv1 : v < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx r
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hu0 hu1 hv1.le
  calc
    (∑' e : ℕ, gammaSewnMobiusContinuousApertureFeature x p e *
        gammaSewnMobiusContinuousApertureFeature x r e) =
      ∑' e : ℕ,
        (cp * cr * (qp / (1 + qp)) * (qr / (1 + qr)) *
          (1 - u) * (1 - v)) * (u * v) ^ e := by
        apply tsum_congr
        intro e
        rw [gammaSewnMobiusContinuousApertureFeature,
          gammaSewnMobiusContinuousApertureFeature,
          xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
          xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
        change (cp * (qp / (1 + qp) * (1 - u) * u ^ e)) *
            (cr * (qr / (1 + qr) * (1 - v) * v ^ e)) = _
        rw [mul_pow]
        ring
    _ = (cp * cr * (qp / (1 + qp)) * (qr / (1 + qr)) *
          (1 - u) * (1 - v)) * ∑' e : ℕ, (u * v) ^ e := by
        rw [tsum_mul_left]
    _ = (cp * cr * (qp / (1 + qp)) * (qr / (1 + qr)) *
          (1 - u) * (1 - v)) * (1 - u * v)⁻¹ := by
        rw [tsum_geometric_of_lt_one huv0 huv1]
    _ = gammaSewnMobiusContinuousAperturePrimeKernel x p r := by
        simp only [gammaSewnMobiusContinuousAperturePrimeKernel,
          qp, qr, u, v, cp, cr, div_eq_mul_inv]

/-- Positive aperture makes the true prime nodes injective in the prime label. -/
theorem xiMobiusContinuousApertureDiskNode_injective_prime
    {x : ℝ} (hx : 0 < x) :
    Function.Injective (fun p : Nat.Primes =>
      xiMobiusContinuousApertureDiskNode x p) := by
  intro p r hpr
  have hexp :
      -x * Real.log (p : ℝ) = -x * Real.log (r : ℝ) := by
    exact Real.exp_injective hpr
  have hlog : Real.log (p : ℝ) = Real.log (r : ℝ) := by
    nlinarith
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hr : 0 < (r : ℝ) := by exact_mod_cast r.2.pos
  have hreal : (p : ℝ) = (r : ℝ) := by
    rw [← Real.exp_log hp, ← Real.exp_log hr, hlog]
  apply Subtype.ext
  exact_mod_cast hreal

/-- Rows are valuation depths and columns are sewn prime rays at one true aperture. -/
def gammaSewnMobiusContinuousApertureSamplingMatrix
    {N : ℕ} (x : ℝ) (p : Fin N → Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun e j => gammaSewnMobiusContinuousApertureFeature x (p j) e

/-- The sewn source matrix is a diagonally weighted true-aperture Vandermonde. -/
theorem gammaSewnMobiusContinuousApertureSamplingMatrix_factorization
    {N : ℕ} (x : ℝ) (p : Fin N → Nat.Primes) :
    gammaSewnMobiusContinuousApertureSamplingMatrix x p =
      (Matrix.vandermonde
        (fun j => xiMobiusContinuousApertureDiskNode x (p j)))ᵀ *
      Matrix.diagonal (fun j =>
        gammaSewnMobiusValuationContractionMultiplier x (p j) *
          (xiTransversePrimeApertureDiskNode 1 (p j) /
            (1 + xiTransversePrimeApertureDiskNode 1 (p j))) *
          (1 - xiMobiusContinuousApertureDiskNode x (p j))) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  rw [gammaSewnMobiusContinuousApertureSamplingMatrix,
    gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  simp [Matrix.vandermonde]
  ring

/-- Every finite injective prime packet survives Gamma sewing with exact full rank. -/
theorem gammaSewnMobiusContinuousApertureSamplingMatrix_det_ne_zero
    {N : ℕ} {x : ℝ} (hx : 0 < x) {p : Fin N → Nat.Primes}
    (hp : Function.Injective p) :
    (gammaSewnMobiusContinuousApertureSamplingMatrix x p).det ≠ 0 := by
  let q : Fin N → ℝ := fun j => xiMobiusContinuousApertureDiskNode x (p j)
  let d : Fin N → ℝ := fun j =>
    gammaSewnMobiusValuationContractionMultiplier x (p j) *
      (xiTransversePrimeApertureDiskNode 1 (p j) /
        (1 + xiTransversePrimeApertureDiskNode 1 (p j))) * (1 - q j)
  have hq : Function.Injective q :=
    (xiMobiusContinuousApertureDiskNode_injective_prime hx).comp hp
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    have hnode0 : 0 < xiTransversePrimeApertureDiskNode 1 (p j) :=
      xiTransversePrimeApertureDiskNode_pos 1 (p j)
    have hq1 : q j < 1 :=
      xiMobiusContinuousApertureDiskNode_lt_one hx (p j)
    have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x (p j)
    dsimp only [d]
    exact mul_ne_zero
      (mul_ne_zero hc0.ne'
        (div_ne_zero hnode0.ne' (by positivity)))
      (sub_ne_zero.mpr hq1.ne')
  rw [gammaSewnMobiusContinuousApertureSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hq
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- On the diagonal, Gamma sewing is a strict source contraction of the pre-existing true-aperture
metric rather than a new Hilbert carrier inserted by hand. -/
theorem gammaSewnMobiusContinuousAperturePrimeKernel_self
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusContinuousAperturePrimeKernel x p p =
      gammaSewnMobiusValuationContractionMultiplier x p ^ 2 *
        xiMobiusPrimeContinuousApertureSzegoMetric x x p := by
  simp only [gammaSewnMobiusContinuousAperturePrimeKernel,
    xiMobiusPrimeContinuousApertureSzegoMetric]
  ring

/-- The sewn complete-valuation metric remains all-prime Hilbertian on every open aperture. -/
theorem summable_gammaSewnMobiusContinuousAperturePrimeKernel_self
    {x : ℝ} (hx : 0 < x) :
    Summable (fun p : Nat.Primes =>
      gammaSewnMobiusContinuousAperturePrimeKernel x p p) := by
  have hbase := summable_xiMobiusPrimeContinuousApertureSzegoMetric_self hx
  apply Summable.of_nonneg_of_le
    (fun p => by
      rw [gammaSewnMobiusContinuousAperturePrimeKernel_self]
      exact mul_nonneg (sq_nonneg _)
        (xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg hx p))
    (fun p => by
      rw [gammaSewnMobiusContinuousAperturePrimeKernel_self]
      have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
      have hc1 := gammaSewnMobiusValuationContractionMultiplier_lt_one hx p
      have hmetric := xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg hx p
      have hc2 : gammaSewnMobiusValuationContractionMultiplier x p ^ 2 ≤ 1 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr hc1.le) (by linarith : 0 ≤
            gammaSewnMobiusValuationContractionMultiplier x p + 1)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 hmetric)
    hbase

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

namespace RHTower

open Filter Topology Set

noncomputable section

theorem continuousAt_gammaSewnMobiusValuationQuadraticDefectGain_zero
    (p : Nat.Primes) :
    ContinuousAt (fun x : ℝ =>
      gammaSewnMobiusValuationQuadraticDefectGain x p) 0 := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let c : ℝ → ℝ := fun x =>
    gammaSewnMobiusValuationContractionMultiplier x p
  change ContinuousAt (fun x : ℝ =>
    (7 * q x ^ 2 + 10 * q x + 7) /
      (8 * (1 + q x ^ 4) * (1 + c x) * (1 + c x ^ 2))) 0
  have hq : ContinuousAt q 0 := by
    dsimp only [q, xiMobiusContinuousApertureDiskNode]
    fun_prop
  have hc : ContinuousAt c 0 := by
    simpa only [c] using
      continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp [q, c, gammaSewnMobiusValuationContractionMultiplier_zero]

end

end RHTower
