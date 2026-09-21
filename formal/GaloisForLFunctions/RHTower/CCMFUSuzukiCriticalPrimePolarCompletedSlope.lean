import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalPrimeOnlyPolarWallTransport
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail

/-!
# Completed cell of the derivative-scale CCM--FU slope

The reciprocal-wall derivative of the literal critical prime--polar action has a
prime--polar--Gamma completion at the exact cell level.  No estimate is asserted here.
-/

namespace RHTower

noncomputable section

open Filter Topology Set
open scoped BigOperators
open GaloisForLFunctions.RHTower

/-- One literal full prime--polar slope cell is a negative completed Suzuki-curvature cell plus
its exact Gamma--harmonic finite-part increment. -/
theorem ccmFUCriticalPrimePolarSlopeCell_eq_completedCurvature
    (j : ℕ) :
    (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
        (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2) =
      -(32 / Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
          suzukiCheckpointSignedCurvatureCell (j + 2) +
        (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
          (suzukiCheckpointCriticalArchCorrection j +
            suzukiCheckpointCriticalHarmonicCell j) := by
  have h := suzukiCheckpointCriticalOrderedTerm_eq j
  unfold suzukiCheckpointCriticalOrderedTerm
    suzukiCheckpointCurvaturePowerDamping at h
  let x : ℝ := ((j + 3 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by
    dsimp only [x]
    exact_mod_cast (by omega : 1 < j + 3)))
  have hdamp : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  rw [show ((j + 2 + 1 : ℕ) : ℝ) = x by dsimp [x]] at h
  rw [hdamp] at h
  have hcurv : suzukiCheckpointSignedCurvatureCell (j + 2) =
      Real.sqrt x * (suzukiCheckpointCriticalArchCorrection j + 1 / x -
        ArithmeticFunction.vonMangoldt (j + 3) / x) := by
    calc
      suzukiCheckpointSignedCurvatureCell (j + 2) =
          Real.sqrt x * ((Real.sqrt x)⁻¹ *
            suzukiCheckpointSignedCurvatureCell (j + 2)) := by field_simp
      _ = _ := by rw [h]
  rw [show ((j + 3 : ℕ) : ℝ) = x by rfl,
    show ((j + 2 : ℕ) : ℝ) = x - 1 by
      dsimp only [x]
      push_cast
      ring,
    hcurv]
  unfold suzukiCheckpointCriticalHarmonicCell
  field_simp [hsqrt, hlog]
  rw [show ((j + 3 : ℕ) : ℝ) = x by rfl,
    show ((j + 2 : ℕ) : ℝ) = x - 1 by
      dsimp only [x]
      push_cast
      ring]
  ring

/-- The Γ--harmonic cell left after completing the literal derivative-scale
prime--polar source. -/
def ccmFUCriticalPrimePolarSourceFreeSlopeCell (j : ℕ) : ℝ :=
  (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
    Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
      (suzukiCheckpointCriticalArchCorrection j +
        suzukiCheckpointCriticalHarmonicCell j)

private theorem ccmFUCriticalPrimePolar_rpow_neg_three_halves_mul_sqrt
    (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) * Real.sqrt x = x⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  convert Real.rpow_neg_one x using 1 <;> ring

private theorem ccmFUCriticalPrimePolar_abs_archCorrection_staticSlope_le
    (j : ℕ) :
    |suzukiCheckpointCriticalArchCorrection j *
        (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2)| ≤
      (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 2 j := by
  let x : ℝ := ((j + 3 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp only [x]; positivity
  have harch := abs_suzukiCheckpointCriticalArchCorrection_le j
  have hlog : 0 < Real.log x := Real.log_pos (by
    dsimp only [x]
    exact_mod_cast (by omega : 1 < j + 3))
  rw [abs_mul]
  have hweight0 : 0 ≤ 32 * Real.sqrt x / Real.log x ^ 2 := by positivity
  calc
    |suzukiCheckpointCriticalArchCorrection j| *
        |32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2| ≤
      ((5 / 3 : ℝ) * x ^ (-(3 / 2 : ℝ))) *
        (32 * Real.sqrt x / Real.log x ^ 2) := by
          apply mul_le_mul harch
          · rw [abs_of_nonneg (by simpa [x] using hweight0)]
          · exact abs_nonneg _
          · positivity
    _ = (160 / 3 : ℝ) *
          (x ^ (-(3 / 2 : ℝ)) * Real.sqrt x / Real.log x ^ 2) := by ring
    _ = (160 / 3 : ℝ) * (x⁻¹ / Real.log x ^ 2) := by
      rw [ccmFUCriticalPrimePolar_rpow_neg_three_halves_mul_sqrt x hx]
    _ = (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 2 j := by
      have hweight : HTGeometry.shiftedReciprocalLogWeight 2 j =
          x⁻¹ / Real.log x ^ 2 := by
        unfold HTGeometry.shiftedReciprocalLogWeight
        change 1 / (((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2) = _
        dsimp only [x]
        push_cast
        field_simp
      rw [hweight]

private theorem ccmFUCriticalPrimePolar_inv_mul_sqrt_eq_rpow_neg_three_halves
    (x : ℝ) (hx : 0 < x) :
    1 / (x * Real.sqrt x) = x ^ (-(3 / 2 : ℝ)) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hr := ccmFUCriticalPrimePolar_rpow_neg_three_halves_mul_sqrt x hx
  apply (div_eq_iff (mul_ne_zero hx.ne' hs)).2
  calc
    1 = x * x⁻¹ := by field_simp
    _ = x * (x ^ (-(3 / 2 : ℝ)) * Real.sqrt x) := by rw [hr]
    _ = x ^ (-(3 / 2 : ℝ)) * (x * Real.sqrt x) := by ring

private theorem ccmFUCriticalPrimePolar_abs_harmonicCell_staticSlope_le
    (j : ℕ) :
    |suzukiCheckpointCriticalHarmonicCell j *
        (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2)| ≤
      64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let a : ℝ := ((j + 2 : ℕ) : ℝ)
  let x : ℝ := ((j + 3 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hx : 0 < x := by dsimp only [x]; positivity
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hxa : x ≤ 2 * a := by
    dsimp only [x, a]
    exact_mod_cast (by omega : j + 3 ≤ 2 * (j + 2))
  have hlog1 : 1 ≤ Real.log x := by
    dsimp only [x]
    convert HTGeometry.one_le_log_natCast_add_three j using 1 <;> push_cast <;> ring
  have hweight : 32 * Real.sqrt x / Real.log x ^ 2 ≤ 32 * Real.sqrt x := by
    have hpow : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hlog1
    have hinv : 1 / Real.log x ^ 2 ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpow
    rw [show 32 * Real.sqrt x / Real.log x ^ 2 =
      (32 * Real.sqrt x) * (1 / Real.log x ^ 2) by ring]
    calc
      (32 * Real.sqrt x) * (1 / Real.log x ^ 2) ≤
          (32 * Real.sqrt x) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 32 * Real.sqrt x := by ring
  have hcell := abs_suzukiCheckpointCriticalHarmonicCell_le j
  have hraw : |suzukiCheckpointCriticalHarmonicCell j| *
      |32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2| ≤
      (1 / (a * x)) * (32 * Real.sqrt x) := by
    apply mul_le_mul hcell
    · have hweight0 : 0 ≤ 32 * Real.sqrt x / Real.log x ^ 2 := by positivity
      rw [abs_of_nonneg (by simpa [x] using hweight0)]
      simpa [x] using hweight
    · exact abs_nonneg _
    · positivity
  have hcore : Real.sqrt x / (a * x) ≤ 2 / (x * Real.sqrt x) := by
    rw [div_le_div_iff₀ (mul_pos ha hx) (mul_pos hx hs)]
    nlinarith [Real.sq_sqrt hx.le]
  rw [abs_mul]
  calc
    |suzukiCheckpointCriticalHarmonicCell j| *
        |32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2| ≤
      (1 / (a * x)) * (32 * Real.sqrt x) := hraw
    _ = 32 * (Real.sqrt x / (a * x)) := by ring
    _ ≤ 32 * (2 / (x * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = 64 * x ^ (-(3 / 2 : ℝ)) := by
      rw [show 32 * (2 / (x * Real.sqrt x)) =
        64 * (1 / (x * Real.sqrt x)) by ring,
        ccmFUCriticalPrimePolar_inv_mul_sqrt_eq_rpow_neg_three_halves x hx]
    _ = 64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by rfl

/-- Absolute derivative-scale Γ--harmonic control.  One logarithm is lost relative to
the moving triangular action, but the finite part remains summable. -/
theorem ccmFUCriticalPrimePolar_abs_sourceFreeSlopeCell_le (j : ℕ) :
    |ccmFUCriticalPrimePolarSourceFreeSlopeCell j| ≤
      (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 2 j +
        64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  unfold ccmFUCriticalPrimePolarSourceFreeSlopeCell
  rw [mul_add]
  calc
    |(32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
        suzukiCheckpointCriticalArchCorrection j +
      (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
        suzukiCheckpointCriticalHarmonicCell j| ≤
      |(32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
        suzukiCheckpointCriticalArchCorrection j| +
      |(32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
        suzukiCheckpointCriticalHarmonicCell j| := abs_add_le _ _
    _ ≤
        |suzukiCheckpointCriticalArchCorrection j *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ 2)| +
          |suzukiCheckpointCriticalHarmonicCell j *
            (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
              Real.log ((j + 3 : ℕ) : ℝ) ^ 2)| := by
          ring_nf
          exact le_rfl
    _ ≤ _ := add_le_add
      (ccmFUCriticalPrimePolar_abs_archCorrection_staticSlope_le j)
      (ccmFUCriticalPrimePolar_abs_harmonicCell_staticSlope_le j)

/-- The derivative-scale Γ--harmonic completion has one unconditional finite budget. -/
theorem ccmFUCriticalPrimePolar_summable_sourceFreeSlopeCell :
    Summable ccmFUCriticalPrimePolarSourceFreeSlopeCell := by
  have hlog : Summable (fun j : ℕ =>
      (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 2 j) :=
    Summable.mul_left _ HTGeometry.summable_shiftedReciprocalLogWeight_two
  have hbase : Summable (fun j : ℕ => (j : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun j : ℕ =>
      ((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (summable_nat_add_iff 3).2 hbase
  have hpow : Summable (fun j : ℕ =>
      64 * ((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Summable.mul_left _ hshift
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    ccmFUCriticalPrimePolar_abs_sourceFreeSlopeCell_le (hlog.add hpow)

/-- Derivative-scale absolute majorant for literal proper-prime-power slope cells. -/
def ccmFUCriticalPrimePolarProperPowerSlopeWeight (n : ℕ) : ℝ :=
  if IsProperPrimePow n then
    1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))
  else 0

private def ccmFUCriticalPrimePolarProperPowerSlopeMajor
    (pk : Nat.Primes × ℕ) : ℝ :=
  (1 / ((pk.1 : ℝ) * Real.log (pk.1 : ℝ))) * (3 / 4 : ℝ) ^ pk.2

private theorem ccmFUCriticalPrimePolar_sqrt_pow_lower_geometric
    (p j : ℕ) (hp : 2 ≤ p) :
    (p : ℝ) * (4 / 3 : ℝ) ^ j ≤
      Real.sqrt (((p ^ (j + 2) : ℕ) : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbase : (16 / 9 : ℝ) ≤ (p : ℝ) := by linarith
  have hpow : (16 / 9 : ℝ) ^ j ≤ (p : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) hbase j
  calc
    ((p : ℝ) * (4 / 3 : ℝ) ^ j) ^ 2 =
        (p : ℝ) ^ 2 * (16 / 9 : ℝ) ^ j := by
      rw [mul_pow]
      congr 1
      calc
        ((4 / 3 : ℝ) ^ j) ^ 2 = ((4 / 3 : ℝ) ^ 2) ^ j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
        _ = (16 / 9 : ℝ) ^ j := by norm_num
    _ ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = (p : ℝ) ^ (j + 2) := by
      rw [← pow_add]
      congr 1
      omega
    _ = (((p ^ (j + 2) : ℕ) : ℝ)) := by norm_cast

private theorem ccmFUCriticalPrimePolar_properPowerSlopeWeight_comp_le_major
    (pk : Nat.Primes × ℕ) :
    ccmFUCriticalPrimePolarProperPowerSlopeWeight (properPowMap pk) ≤
      ccmFUCriticalPrimePolarProperPowerSlopeMajor pk := by
  rcases pk with ⟨p, j⟩
  have hproper : IsProperPrimePow ((p : ℕ) ^ (j + 2)) :=
    isProperPrimePow_iff.mpr ⟨p, p.2, j, rfl⟩
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hpow0 : (0 : ℝ) < (((p : ℕ) ^ (j + 2) : ℕ) : ℝ) := by positivity
  have hlogpow : Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) =
      ((j : ℝ) + 2) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  have hloglower : Real.log (p : ℝ) ≤
      Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) := by
    rw [hlogpow]
    nlinarith
  have hsqrt := ccmFUCriticalPrimePolar_sqrt_pow_lower_geometric (p : ℕ) j hp2
  have hden : (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ≤
      Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) := by
    calc
      (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ≤
          Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) * Real.log (p : ℝ) := by
            gcongr
      _ ≤ Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
          Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) := by
            gcongr
  have hden0 : 0 < (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) := by
    positivity
  unfold ccmFUCriticalPrimePolarProperPowerSlopeWeight
    ccmFUCriticalPrimePolarProperPowerSlopeMajor properPowMap
  rw [if_pos hproper]
  have hrecip :
      1 / (Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ))) ≤
        1 / ((p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ)) :=
    one_div_le_one_div_of_le hden0 hden
  calc
    1 / (Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ))) ≤
        1 / ((p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ)) := hrecip
    _ = (1 / ((p : ℝ) * Real.log (p : ℝ))) * (3 / 4 : ℝ) ^ j := by
      have hpow : (4 / 3 : ℝ) ^ j * (3 / 4 : ℝ) ^ j = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      rw [hpow]

private theorem ccmFUCriticalPrimePolar_properPowerSlopeWeight_nonneg (n : ℕ) :
    0 ≤ ccmFUCriticalPrimePolarProperPowerSlopeWeight n := by
  unfold ccmFUCriticalPrimePolarProperPowerSlopeWeight
  split_ifs <;> positivity

private theorem ccmFUCriticalPrimePolar_summable_properPowerSlopeMajor :
    Summable ccmFUCriticalPrimePolarProperPowerSlopeMajor := by
  let f : Nat.Primes → ℝ := fun p => 1 / ((p : ℝ) * Real.log (p : ℝ))
  let g : ℕ → ℝ := fun j => (3 / 4 : ℝ) ^ j
  have hf : Summable f := by
    simpa only [f, Real.rpow_one] using
      Sieve.summable_primes_one_div_mul_log_rpow (show (0 : ℝ) < 1 by norm_num)
  have hg : Summable g := summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs]
    norm_num)
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp only [f]
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    positivity
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    dsimp only [g]
    positivity
  change Summable (fun pk : Nat.Primes × ℕ => f pk.1 * g pk.2)
  exact hf.mul_of_nonneg hg hf0 hg0

private theorem ccmFUCriticalPrimePolar_properPowerSlopeWeight_eq_zero_of_notMem_range
    {n : ℕ} (hn : n ∉ Set.range properPowMap) :
    ccmFUCriticalPrimePolarProperPowerSlopeWeight n = 0 := by
  unfold ccmFUCriticalPrimePolarProperPowerSlopeWeight
  rw [if_neg]
  intro hproper
  obtain ⟨p, hp, j, rfl⟩ := isProperPrimePow_iff.mp hproper
  exact hn ⟨(⟨p, hp⟩, j), rfl⟩

/-- Proper prime powers remain absolutely summable after the reciprocal-wall derivative. -/
theorem ccmFUCriticalPrimePolar_summable_properPowerSlopeWeight :
    Summable ccmFUCriticalPrimePolarProperPowerSlopeWeight := by
  rw [← properPow_injective.summable_iff
    (fun n hn => ccmFUCriticalPrimePolar_properPowerSlopeWeight_eq_zero_of_notMem_range hn)]
  exact Summable.of_nonneg_of_le
    (fun pk => ccmFUCriticalPrimePolar_properPowerSlopeWeight_nonneg (properPowMap pk))
    ccmFUCriticalPrimePolar_properPowerSlopeWeight_comp_le_major
    ccmFUCriticalPrimePolar_summable_properPowerSlopeMajor

/-- Literal proper-prime-power contribution to one derivative-scale source cell. -/
def ccmFUCriticalPrimePolarProperPowerSlopeCell (j : ℕ) : ℝ :=
  (if IsProperPrimePow (j + 3) then
      ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
    else 0) *
      (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2)

theorem ccmFUCriticalPrimePolar_abs_properPowerSlopeCell_le (j : ℕ) :
    |ccmFUCriticalPrimePolarProperPowerSlopeCell j| ≤
      32 * ccmFUCriticalPrimePolarProperPowerSlopeWeight (j + 3) := by
  unfold ccmFUCriticalPrimePolarProperPowerSlopeCell
  by_cases hproper : IsProperPrimePow (j + 3)
  · rw [if_pos hproper]
    have hn : 0 < ((j + 3 : ℕ) : ℝ) := by positivity
    have hlog : 0 < Real.log ((j + 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < j + 3))
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (j + 3) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : ArithmeticFunction.vonMangoldt (j + 3) ≤
        Real.log ((j + 3 : ℕ) : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    unfold ccmFUCriticalPrimePolarProperPowerSlopeWeight
    rw [if_pos hproper, abs_mul,
      abs_of_nonneg (div_nonneg hΛ0 hn.le),
      abs_of_nonneg (by positivity : 0 ≤
        32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2)]
    have hmain : ArithmeticFunction.vonMangoldt (j + 3) /
        ((j + 3 : ℕ) : ℝ) *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ 2) ≤
        32 * (1 / (Real.sqrt ((j + 3 : ℕ) : ℝ) *
          Real.log ((j + 3 : ℕ) : ℝ))) := by
      rw [show ArithmeticFunction.vonMangoldt (j + 3) /
          ((j + 3 : ℕ) : ℝ) *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ 2) =
          32 * (ArithmeticFunction.vonMangoldt (j + 3) /
            (Real.sqrt ((j + 3 : ℕ) : ℝ) *
              Real.log ((j + 3 : ℕ) : ℝ) ^ 2)) by
              have hsqrt : Real.sqrt ((j + 3 : ℕ) : ℝ) ≠ 0 :=
                (Real.sqrt_pos.mpr hn).ne'
              field_simp
              rw [Real.sq_sqrt hn.le]
              ]
      have hden : 0 < Real.sqrt ((j + 3 : ℕ) : ℝ) *
          Real.log ((j + 3 : ℕ) : ℝ) ^ 2 :=
        mul_pos (Real.sqrt_pos.mpr hn) (sq_pos_of_pos hlog)
      calc
        32 * (ArithmeticFunction.vonMangoldt (j + 3) /
            (Real.sqrt ((j + 3 : ℕ) : ℝ) *
              Real.log ((j + 3 : ℕ) : ℝ) ^ 2)) ≤
            32 * (Real.log ((j + 3 : ℕ) : ℝ) /
              (Real.sqrt ((j + 3 : ℕ) : ℝ) *
                Real.log ((j + 3 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hΛ hden.le) (by norm_num)
        _ = 32 * (1 / (Real.sqrt ((j + 3 : ℕ) : ℝ) *
            Real.log ((j + 3 : ℕ) : ℝ))) := by
          have hsqrt : Real.sqrt ((j + 3 : ℕ) : ℝ) ≠ 0 :=
            (Real.sqrt_pos.mpr hn).ne'
          field_simp
    exact hmain
  · rw [if_neg hproper]
    unfold ccmFUCriticalPrimePolarProperPowerSlopeWeight
    simp [hproper]

/-- The literal proper-prime-power derivative tail has a single absolute budget. -/
theorem ccmFUCriticalPrimePolar_summable_properPowerSlopeCell :
    Summable ccmFUCriticalPrimePolarProperPowerSlopeCell := by
  have hinj : Function.Injective (fun j : ℕ => j + 3) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hmajor : Summable (fun j : ℕ =>
      32 * ccmFUCriticalPrimePolarProperPowerSlopeWeight (j + 3)) :=
    (ccmFUCriticalPrimePolar_summable_properPowerSlopeWeight.comp_injective hinj).mul_left 32
  apply Summable.of_norm_bounded_eventually_nat hmajor
  filter_upwards [Filter.eventually_ge_atTop 0] with j _
  rw [Real.norm_eq_abs]
  exact ccmFUCriticalPrimePolar_abs_properPowerSlopeCell_le j

/-- Finite accumulated completed curvature at the literal reciprocal-wall scale. -/
def ccmFUCriticalPrimePolarCompletedCurvatureSlope (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N - 2),
    -(32 / Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
      suzukiCheckpointSignedCurvatureCell (j + 2)

/-- Finite Γ--harmonic defect accumulated at the literal reciprocal-wall scale. -/
def ccmFUCriticalPrimePolarSourceFreeSlopeDefect (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N - 2), ccmFUCriticalPrimePolarSourceFreeSlopeCell j

/-- Finite literal proper-prime-power defect accumulated at the reciprocal-wall scale. -/
def ccmFUCriticalPrimePolarProperPowerSlopeDefect (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N - 2), ccmFUCriticalPrimePolarProperPowerSlopeCell j

/-- Exact source-faithful landing of every finite valuation-one FU slope head on completed
Suzuki curvature.  Both discarded ports remain visible and separately summable. -/
theorem ccmFUCriticalPrimeOnlyPolarSlope_eq_completedCurvature_add_sourceFree_sub_proper
    (N : ℕ) :
    ccmFUCriticalPrimeOnlyPolarSlopeAction N =
      ccmFUCriticalPrimePolarCompletedCurvatureSlope N +
        ccmFUCriticalPrimePolarSourceFreeSlopeDefect N -
          ccmFUCriticalPrimePolarProperPowerSlopeDefect N := by
  unfold ccmFUCriticalPrimeOnlyPolarSlopeAction
    ccmFUCriticalPrimePolarCompletedCurvatureSlope
    ccmFUCriticalPrimePolarSourceFreeSlopeDefect
    ccmFUCriticalPrimePolarProperPowerSlopeDefect
  calc
    ∑ j ∈ Finset.range (N - 2),
        suzukiCheckpointCriticalPrimeOnlyPolarCell (j + 3) *
          (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
            Real.log ((j + 3 : ℕ) : ℝ) ^ 2) =
        ∑ j ∈ Finset.range (N - 2),
          (-(32 / Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
              suzukiCheckpointSignedCurvatureCell (j + 2) +
            ccmFUCriticalPrimePolarSourceFreeSlopeCell j -
              ccmFUCriticalPrimePolarProperPowerSlopeCell j) := by
          apply Finset.sum_congr rfl
          intro j _
          have hfull := ccmFUCriticalPrimePolarSlopeCell_eq_completedCurvature j
          have hsplit :=
            suzukiCheckpointCriticalPrimePolarIncrement_eq_primeOnly_add_properPrimePower (j + 3)
          rw [show (j + 3 - 1 : ℕ) = j + 2 by omega] at hsplit
          unfold suzukiCheckpointCriticalPrimeOnlyPolarCell
            ccmFUCriticalPrimePolarSourceFreeSlopeCell
            ccmFUCriticalPrimePolarProperPowerSlopeCell
          rw [show (j + 3 - 1 : ℕ) = j + 2 by omega]
          rw [hsplit] at hfull
          ring_nf at hfull ⊢
          linarith
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem ccmFUCriticalPrimePolar_criticalMultiplier_eq_slope_mul_inverseWall
    {H : ℝ} (hH : H ≠ 0) (j : ℕ) :
    suzukiCheckpointCriticalTriangularMultiplier H j =
      (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) /
        Real.log ((j + 3 : ℕ) : ℝ) ^ 2) *
        (1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H) := by
  have hlog : Real.log ((j + 3 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < j + 3)))
  unfold suzukiCheckpointCriticalTriangularMultiplier
    ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  field_simp [hH, hlog]

/-- The negative signed Suzuki curvature carried by the literal finite FU aperture. -/
def ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    -suzukiCheckpointSignedCurvatureCell (j + 2) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (Real.log ((j + 3 : ℕ) : ℝ))

/-- The literal Γ--harmonic finite part retained at the moving triangular wall. -/
def ccmFUCriticalPrimePolarSourceFreeAction (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    ccmFUCriticalPrimePolarSourceFreeSlopeCell j *
      (1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H)

private theorem ccmFUCriticalPrimePolar_fullCell_eq_negativeCurvature_add_sourceFree
    {H : ℝ} (hH : H ≠ 0) (j : ℕ) :
    (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
        suzukiCheckpointCriticalTriangularMultiplier H j =
      -suzukiCheckpointSignedCurvatureCell (j + 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H
          (Real.log ((j + 3 : ℕ) : ℝ)) +
      ccmFUCriticalPrimePolarSourceFreeSlopeCell j *
        (1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H) := by
  have hmult := ccmFUCriticalPrimePolar_criticalMultiplier_eq_slope_mul_inverseWall hH j
  have hcell := ccmFUCriticalPrimePolarSlopeCell_eq_completedCurvature j
  rw [hmult]
  rw [← mul_assoc, hcell]
  unfold ccmFUCriticalPrimePolarSourceFreeSlopeCell
    ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  have hlog : Real.log ((j + 3 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < j + 3)))
  field_simp [hH, hlog]

/-- Exact source-faithful prime--polar--Γ decomposition of the literal full FU reporter. -/
theorem ccmFUCriticalPrimePolarAction_eq_negativeCompletedCurvature_add_sourceFree
    {H : ℝ} (hH : H ≠ 0) :
    suzukiCheckpointCriticalPrimePolarAction H =
      ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction H +
        ccmFUCriticalPrimePolarSourceFreeAction H := by
  unfold suzukiCheckpointCriticalPrimePolarAction
    ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction
    ccmFUCriticalPrimePolarSourceFreeAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact ccmFUCriticalPrimePolar_fullCell_eq_negativeCurvature_add_sourceFree hH j

/-- Exact source-faithful decomposition of the RH-bearing valuation-one reporter. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_eq_negativeCompletedCurvature_add_sourceFree_sub_proper
    {H : ℝ} (hH : H ≠ 0) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction H =
      ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction H +
        ccmFUCriticalPrimePolarSourceFreeAction H -
          suzukiCheckpointCriticalProperPrimePowerAtomicAction H := by
  have hsplit := suzukiCheckpointCriticalPrimePolarAction_eq_primeOnlyPolar_add_properPrimePower H
  rw [ccmFUCriticalPrimePolarAction_eq_negativeCompletedCurvature_add_sourceFree hH] at hsplit
  linarith

/-- The Γ--harmonic port of the actual triangular reporter has one uniform unconditional budget. -/
theorem ccmFUCriticalPrimePolar_exists_uniform_sourceFreeAction_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
      |ccmFUCriticalPrimePolarSourceFreeAction H| ≤ C := by
  let q : ℕ → ℝ := fun j => 2 * |ccmFUCriticalPrimePolarSourceFreeSlopeCell j|
  have hqsum : Summable q := by
    dsimp only [q]
    exact ccmFUCriticalPrimePolar_summable_sourceFreeSlopeCell.abs.mul_left 2
  have hq0 : ∀ j : ℕ, 0 ≤ q j := by
    intro j
    dsimp only [q]
    positivity
  refine ⟨∑' j : ℕ, q j, tsum_nonneg hq0, ?_⟩
  intro H hH
  have hHpos : 0 < H := by linarith
  have hHinv : 1 / H ≤ 1 := by
    rw [div_le_iff₀ hHpos]
    linarith
  unfold ccmFUCriticalPrimePolarSourceFreeAction
  calc
    |∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        ccmFUCriticalPrimePolarSourceFreeSlopeCell j *
          (1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H)| ≤
      ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        |ccmFUCriticalPrimePolarSourceFreeSlopeCell j *
          (1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), q j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hlog1 : 1 ≤ Real.log ((j + 3 : ℕ) : ℝ) := by
        convert HTGeometry.one_le_log_natCast_add_three j using 1 <;>
          push_cast <;> ring
      have hloginv : 1 / Real.log ((j + 3 : ℕ) : ℝ) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num) hlog1
      have hlogpos : 0 < Real.log ((j + 3 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < j + 3))
      have hloginv0 : 0 ≤ 1 / Real.log ((j + 3 : ℕ) : ℝ) :=
        one_div_nonneg.mpr hlogpos.le
      have hHinv0 : 0 ≤ 1 / H := one_div_nonneg.mpr hHpos.le
      have hfactor : |1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H| ≤ 2 := by
        calc
          |1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H| ≤
              |1 / Real.log ((j + 3 : ℕ) : ℝ)| + |1 / H| := abs_sub _ _
          _ = 1 / Real.log ((j + 3 : ℕ) : ℝ) + 1 / H := by
            rw [abs_of_nonneg hloginv0, abs_of_nonneg hHinv0]
          _ ≤ 1 + 1 := add_le_add hloginv hHinv
          _ = 2 := by norm_num
      dsimp only [q]
      calc
        |ccmFUCriticalPrimePolarSourceFreeSlopeCell j| *
            |1 / Real.log ((j + 3 : ℕ) : ℝ) - 1 / H| ≤
            |ccmFUCriticalPrimePolarSourceFreeSlopeCell j| * 2 :=
          mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
        _ = 2 * |ccmFUCriticalPrimePolarSourceFreeSlopeCell j| := by ring
    _ ≤ ∑' j : ℕ, q j := hqsum.sum_le_tsum _ (fun j _ => hq0 j)

/-- The finite negative curvature head is exactly the existing signed Suzuki reporter. -/
theorem ccmFUCriticalPrimePolar_negativeCompletedCurvatureAction_eq_neg_transform
    {H : ℝ} (hH : 2 ≤ H) :
    ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction H =
      -suzukiCheckpointTriangularCurvatureTransform H := by
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hM2, _⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell
    (hlog2one.trans (one_le_two.trans hH))
  let M := suzukiCheckpointEventIndex H
  let m := M - 2
  have hmM : m + 2 = M := Nat.sub_add_cancel hM2
  let term : ℕ → ℝ := fun j =>
    suzukiCheckpointSignedCurvatureCell j *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (Real.log ((j + 1 : ℕ) : ℝ))
  have hshift := Finset.sum_Ico_add term 0 m 2
  have hzero : Finset.Ico 0 m = Finset.range m := by
    ext i
    simp
  rw [hzero, hmM] at hshift
  have hcurv : suzukiCheckpointTriangularCurvatureTransform H =
      ∑ n ∈ Finset.range m, term (n + 2) := by
    unfold suzukiCheckpointTriangularCurvatureTransform
    change (∑ j ∈ Finset.Ico 2 M, term j) = _
    rw [← hshift]
    apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.add_comm] using rfl
  have hnegative : ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction H =
      -(∑ n ∈ Finset.range m, term (n + 2)) := by
    unfold ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction
    change (∑ j ∈ Finset.range m,
      -suzukiCheckpointSignedCurvatureCell (j + 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H
          (Real.log ((j + 3 : ℕ) : ℝ))) = _
    calc
      _ = ∑ j ∈ Finset.range m, -term (j + 2) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [term]
        rw [show j + 2 + 1 = j + 3 by omega]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  calc
    ccmFUCriticalPrimePolarNegativeCompletedCurvatureAction H =
        -(∑ n ∈ Finset.range m, term (n + 2)) := hnegative
    _ = -suzukiCheckpointTriangularCurvatureTransform H := by rw [hcurv]

/-- Literal valuation-one prime--polar action is the actual signed Suzuki reporter plus two
uniformly controlled source ports; no positive/negative source region is separated. -/
theorem ccmFUCriticalPrimeOnlyPolarAction_eq_neg_transform_add_sourceFree_sub_proper
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointCriticalPrimeOnlyPolarAction H =
      -suzukiCheckpointTriangularCurvatureTransform H +
        ccmFUCriticalPrimePolarSourceFreeAction H -
          suzukiCheckpointCriticalProperPrimePowerAtomicAction H := by
  rw [ccmFUCriticalPrimeOnlyPolarAction_eq_negativeCompletedCurvature_add_sourceFree_sub_proper
    (ne_of_gt (by linarith : 0 < H)),
    ccmFUCriticalPrimePolar_negativeCompletedCurvatureAction_eq_neg_transform hH]

end

end RHTower
