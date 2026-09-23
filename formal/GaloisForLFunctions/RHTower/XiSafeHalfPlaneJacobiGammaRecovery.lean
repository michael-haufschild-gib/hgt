import GaloisForLFunctions.RHTower.CriticalHalfApertureJacobiGammaRecovery
import GaloisForLFunctions.RHTower.PrimeClockScaleFactor
import GaloisForLFunctions.RHTower.XiTransverseShiftDefectDifferentialRank

/-!
# Safe-half-plane Jacobi--Gamma recovery

The critical Jacobi--Gamma recovery has a forced asymmetric deformation throughout the safe
half-plane.  If

`r_x(p) = p⁻ˣ`, `q(p) = p⁻¹ᐟ²`, and `d_x(p) = p^(1/2-x)`,

then `d_x q = r_x`.  The interior Jacobi coefficient is consequently forced to be

`b_x(p) = d_x(p)^(2 : ℕ) = p * r_x(p)^(2 : ℕ)`.

With these coefficients, the Pascal-normalized Gamma-sewn ray at aperture `x`, together with the
same Gamma vacuum used at the critical aperture, recovers the complete shifted von Mangoldt
prime-power stream

`(log p) * p^(-x(e+1))`.

For `x > 1/2`, both source multipliers lie strictly between zero and one and the recovered stream
is a genuine square-summable all-prime/all-valuation vector.  At `x = 1/2` the multipliers become
one, the asymmetric operator becomes the critical symmetric Jacobi operator, and the recovered
stream leaves `ell^(2 : ℕ)`.  Thus the critical line is the exact lossless boundary of this source
recovery, not an exponent inserted after the fact.

This is a fixed source map, not an existence interface and not an RH criterion.  It supplies the
safe-side infinite carrier which must still be composed with the literal signed polar/window
incidence before any RH-bearing norm estimate.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Boundary transport from the critical Gamma vacuum to aperture `x`. -/
def xiSafeHalfPlaneJacobiBoundaryWeight (x : ℝ) (p : Nat.Primes) : ℝ :=
  xiMobiusContinuousApertureDiskNode (x - 1 / 2) p

/-- The unique interior coefficient compatible with the same recovered geometric ray. -/
def xiSafeHalfPlaneJacobiInteriorWeight (x : ℝ) (p : Nat.Primes) : ℝ :=
  xiSafeHalfPlaneJacobiBoundaryWeight x p ^ 2

theorem xiSafeHalfPlaneJacobiBoundaryWeight_pos
    (x : ℝ) (p : Nat.Primes) :
    0 < xiSafeHalfPlaneJacobiBoundaryWeight x p :=
  xiMobiusContinuousApertureDiskNode_pos _ p

theorem xiSafeHalfPlaneJacobiBoundaryWeight_le_one
    {x : ℝ} (hx : 1 / 2 ≤ x) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiBoundaryWeight x p ≤ 1 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    simp [xiSafeHalfPlaneJacobiBoundaryWeight]
  · exact (xiMobiusContinuousApertureDiskNode_lt_one (sub_pos.mpr h) p).le

theorem xiSafeHalfPlaneJacobiBoundaryWeight_lt_one
    {x : ℝ} (hx : 1 / 2 < x) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiBoundaryWeight x p < 1 :=
  xiMobiusContinuousApertureDiskNode_lt_one (sub_pos.mpr hx) p

@[simp] theorem xiSafeHalfPlaneJacobiBoundaryWeight_half
    (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiBoundaryWeight (1 / 2) p = 1 := by
  simp [xiSafeHalfPlaneJacobiBoundaryWeight]

theorem xiSafeHalfPlaneJacobiInteriorWeight_pos
    (x : ℝ) (p : Nat.Primes) :
    0 < xiSafeHalfPlaneJacobiInteriorWeight x p := by
  exact sq_pos_of_pos (xiSafeHalfPlaneJacobiBoundaryWeight_pos x p)

theorem xiSafeHalfPlaneJacobiInteriorWeight_le_one
    {x : ℝ} (hx : 1 / 2 ≤ x) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiInteriorWeight x p ≤ 1 := by
  have h0 := xiSafeHalfPlaneJacobiBoundaryWeight_pos x p
  have h1 := xiSafeHalfPlaneJacobiBoundaryWeight_le_one hx p
  unfold xiSafeHalfPlaneJacobiInteriorWeight
  nlinarith

theorem xiSafeHalfPlaneJacobiInteriorWeight_lt_one
    {x : ℝ} (hx : 1 / 2 < x) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiInteriorWeight x p < 1 := by
  have h0 := xiSafeHalfPlaneJacobiBoundaryWeight_pos x p
  have h1 := xiSafeHalfPlaneJacobiBoundaryWeight_lt_one hx p
  unfold xiSafeHalfPlaneJacobiInteriorWeight
  nlinarith

@[simp] theorem xiSafeHalfPlaneJacobiInteriorWeight_half
    (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiInteriorWeight (1 / 2) p = 1 := by
  rw [xiSafeHalfPlaneJacobiInteriorWeight,
    xiSafeHalfPlaneJacobiBoundaryWeight_half]
  norm_num

/-- The boundary multiplier transports the critical node exactly to the safe aperture node. -/
theorem xiSafeHalfPlaneJacobiBoundaryWeight_mul_halfNode
    (x : ℝ) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiBoundaryWeight x p *
        xiMobiusContinuousApertureDiskNode (1 / 2) p =
      xiMobiusContinuousApertureDiskNode x p := by
  rw [xiSafeHalfPlaneJacobiBoundaryWeight,
    ← xiMobiusContinuousApertureDiskNode_add]
  congr 1
  ring

/-- The interior multiplier forced by boundary transport is `p` times the square of the safe
aperture node. -/
theorem xiSafeHalfPlaneJacobiInteriorWeight_eq_prime_mul_node_sq
    (x : ℝ) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiInteriorWeight x p =
      (p : ℝ) * xiMobiusContinuousApertureDiskNode x p ^ 2 := by
  let P : ℝ := p
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  unfold xiSafeHalfPlaneJacobiInteriorWeight
    xiSafeHalfPlaneJacobiBoundaryWeight
    xiMobiusContinuousApertureDiskNode
  change Real.exp (-(x - 1 / 2) * Real.log P) ^ 2 =
    P * Real.exp (-x * Real.log P) ^ 2
  rw [pow_two, ← Real.exp_add, pow_two, ← Real.exp_add]
  calc
    Real.exp (-(x - 1 / 2) * Real.log P +
        -(x - 1 / 2) * Real.log P) =
        Real.exp (Real.log P + (-x * Real.log P + -x * Real.log P)) := by
          congr 1
          ring
    _ = Real.exp (Real.log P) *
        Real.exp (-x * Real.log P + -x * Real.log P) := by
          rw [Real.exp_add]
    _ = P * Real.exp (-x * Real.log P + -x * Real.log P) := by
          rw [Real.exp_log hP]

/-- The safe-half-plane asymmetric Jacobi recovery with the actual Gamma boundary coordinate. -/
def xiSafeHalfPlaneJacobiGammaRecovery
    (x : ℝ) (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ)
    (p : Nat.Primes) : ℕ → ℝ
  | 0 => f p 1 + xiSafeHalfPlaneJacobiBoundaryWeight x p *
      criticalHalfApertureGammaBoundaryGauge p * g p
  | e + 1 => xiSafeHalfPlaneJacobiInteriorWeight x p * f p e + f p (e + 2)

/-- At the critical boundary the asymmetric recovery is literally the previously constructed
symmetric Jacobi--Gamma recovery. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_half
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ) :
    xiSafeHalfPlaneJacobiGammaRecovery (1 / 2) f g =
      criticalHalfApertureJacobiGammaRecovery f g := by
  funext p e
  cases e with
  | zero =>
      rw [xiSafeHalfPlaneJacobiGammaRecovery,
        criticalHalfApertureJacobiGammaRecovery,
        xiSafeHalfPlaneJacobiBoundaryWeight_half]
      ring
  | succ e =>
      rw [xiSafeHalfPlaneJacobiGammaRecovery,
        criticalHalfApertureJacobiGammaRecovery,
        xiSafeHalfPlaneJacobiInteriorWeight_half]
      ring

/-- Uniform boundary energy bound throughout the closed safe half-plane. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_zero_sq_le
    {x : ℝ} (hx : 1 / 2 ≤ x)
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiGammaRecovery x f g p 0 ^ 2 ≤
      2 * (f p 1) ^ 2 + 32 / 9 * (g p) ^ 2 := by
  let d := xiSafeHalfPlaneJacobiBoundaryWeight x p
  let G := criticalHalfApertureGammaBoundaryGauge p
  have hd2 : d ^ 2 ≤ 1 := by
    have hd0 := xiSafeHalfPlaneJacobiBoundaryWeight_pos x p
    have hd1 := xiSafeHalfPlaneJacobiBoundaryWeight_le_one hx p
    dsimp only [d]
    nlinarith
  have hG2 : G ^ 2 ≤ 16 / 9 := by
    exact criticalHalfApertureGammaBoundaryGauge_sq_le_sixteen_ninths p
  have hdG2 : d ^ 2 * G ^ 2 ≤ 16 / 9 := by
    calc
      d ^ 2 * G ^ 2 ≤ 1 * G ^ 2 :=
        mul_le_mul_of_nonneg_right hd2 (sq_nonneg G)
      _ ≤ 16 / 9 := by simpa using hG2
  have hterm : (d * G * g p) ^ 2 ≤ 16 / 9 * (g p) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right hdG2 (sq_nonneg (g p))
  rw [xiSafeHalfPlaneJacobiGammaRecovery]
  change (f p 1 + d * G * g p) ^ 2 ≤
    2 * (f p 1) ^ 2 + 32 / 9 * (g p) ^ 2
  nlinarith [sq_nonneg (f p 1 - d * G * g p)]

/-- Uniform interior energy bound throughout the closed safe half-plane. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_succ_sq_le
    {x : ℝ} (hx : 1 / 2 ≤ x)
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ)
    (p : Nat.Primes) (e : ℕ) :
    xiSafeHalfPlaneJacobiGammaRecovery x f g p (e + 1) ^ 2 ≤
      2 * (f p e) ^ 2 + 2 * (f p (e + 2)) ^ 2 := by
  let b := xiSafeHalfPlaneJacobiInteriorWeight x p
  have hb2 : b ^ 2 ≤ 1 := by
    have hb0 := xiSafeHalfPlaneJacobiInteriorWeight_pos x p
    have hb1 := xiSafeHalfPlaneJacobiInteriorWeight_le_one hx p
    dsimp only [b]
    nlinarith
  have hterm : (b * f p e) ^ 2 ≤ (f p e) ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg (f p e)]
  rw [xiSafeHalfPlaneJacobiGammaRecovery]
  change (b * f p e + f p (e + 2)) ^ 2 ≤
    2 * (f p e) ^ 2 + 2 * (f p (e + 2)) ^ 2
  nlinarith [sq_nonneg (b * f p e - f p (e + 2))]

/-- Safe-half-plane von Mangoldt prime-power coefficient produced by the source map. -/
def xiSafeHalfPlanePrimePowerCoefficient
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.log (p : ℝ) * xiMobiusContinuousApertureDiskNode x p ^ (e + 1)

theorem xiSafeHalfPlanePrimePowerCoefficient_ne_zero
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiSafeHalfPlanePrimePowerCoefficient x p e ≠ 0 := by
  have hP : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  exact mul_ne_zero (Real.log_pos hP).ne'
    (pow_ne_zero _ (xiMobiusContinuousApertureDiskNode_pos x p).ne')

/-- **HT source exposure on the prime layer.**  An integral aperture increment of the recovered
safe Jacobi stream is exactly a diagonally damped copy of the actual transverse Xi-shift source.
The latter is the source whose upper-end carrier has cofinite-deletion robust differential rank
over the genuine coordinate field. -/
theorem xiSafeHalfPlanePrimeCoefficient_sub_natShift_eq_transverseSource
    (x : ℝ) (a : ℕ) (p : Nat.Primes) :
    ((xiSafeHalfPlanePrimePowerCoefficient x p 0 -
        xiSafeHalfPlanePrimePowerCoefficient (x + a) p 0 : ℝ) : ℂ) =
      (xiMobiusContinuousApertureDiskNode x p : ℂ) *
        xiTransverseShiftArithmetic a p := by
  have haNode :
      xiMobiusContinuousApertureDiskNode (a : ℝ) p =
        xiTransversePrimeApertureDiskNode a p := by
    rfl
  rw [xiSafeHalfPlanePrimePowerCoefficient,
    xiSafeHalfPlanePrimePowerCoefficient]
  simp only [zero_add, pow_one]
  rw [xiMobiusContinuousApertureDiskNode_add,
    xiTransverseShiftArithmetic_apply_prime,
    primeShiftFactor_nat_eq_xiTransversePrimeApertureDiskNode,
    ← haNode]
  push_cast
  ring

/-- Exact recovery at the unilateral boundary. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_zero
    {x : ℝ} (hx : 1 / 2 ≤ x) (p : Nat.Primes) :
    xiSafeHalfPlaneJacobiGammaRecovery x
        (gammaSewnMobiusPascalNormalizedRay x)
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p 0 =
      xiSafeHalfPlanePrimePowerCoefficient x p 0 := by
  let P : ℝ := p
  let r := xiMobiusContinuousApertureDiskNode x p
  let d := xiSafeHalfPlaneJacobiBoundaryWeight x p
  let q := xiMobiusContinuousApertureDiskNode (1 / 2) p
  have hx0 : 0 < x := by linarith
  have hP : (1 : ℝ) < P := by
    dsimp only [P]
    exact_mod_cast p.2.one_lt
  have hboundary := criticalHalfApertureGammaBoundaryGauge_mul_vacuum_eq p
  have hdq := xiSafeHalfPlaneJacobiBoundaryWeight_mul_halfNode x p
  rw [xiSafeHalfPlaneJacobiGammaRecovery,
    gammaSewnMobiusPascalNormalizedRay_eq_geometric hx0,
    xiSafeHalfPlanePrimePowerCoefficient]
  change Real.log P / (P + 1) * r ^ 1 +
      d * criticalHalfApertureGammaBoundaryGauge p *
        (Real.log P * xiTransversePrimeHalfShiftedFirstValuationCoordinate p) =
    Real.log P * r ^ (0 + 1)
  rw [show d * criticalHalfApertureGammaBoundaryGauge p *
      (Real.log P * xiTransversePrimeHalfShiftedFirstValuationCoordinate p) =
        Real.log P * d *
          (criticalHalfApertureGammaBoundaryGauge p *
            xiTransversePrimeHalfShiftedFirstValuationCoordinate p) by ring,
    hboundary]
  change Real.log P / (P + 1) * r ^ 1 +
      Real.log P * d * (q * P / (P + 1)) =
    Real.log P * r ^ (0 + 1)
  rw [show Real.log P * d * (q * P / (P + 1)) =
      Real.log P * (d * q) * P / (P + 1) by ring,
    hdq]
  simp only [pow_one, zero_add]
  have hplus : P + 1 ≠ 0 := by nlinarith
  field_simp [hplus]
  ring

/-- Exact recovery at every positive valuation depth. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_succ
    {x : ℝ} (hx : 1 / 2 ≤ x) (p : Nat.Primes) (e : ℕ) :
    xiSafeHalfPlaneJacobiGammaRecovery x
        (gammaSewnMobiusPascalNormalizedRay x)
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p (e + 1) =
      xiSafeHalfPlanePrimePowerCoefficient x p (e + 1) := by
  let P : ℝ := p
  let r := xiMobiusContinuousApertureDiskNode x p
  let b := xiSafeHalfPlaneJacobiInteriorWeight x p
  have hx0 : 0 < x := by linarith
  have hP : (1 : ℝ) < P := by
    dsimp only [P]
    exact_mod_cast p.2.one_lt
  have hb := xiSafeHalfPlaneJacobiInteriorWeight_eq_prime_mul_node_sq x p
  rw [xiSafeHalfPlaneJacobiGammaRecovery,
    gammaSewnMobiusPascalNormalizedRay_eq_geometric hx0,
    gammaSewnMobiusPascalNormalizedRay_eq_geometric hx0,
    xiSafeHalfPlanePrimePowerCoefficient]
  change b * (Real.log P / (P + 1) * r ^ e) +
      Real.log P / (P + 1) * r ^ (e + 2) =
    Real.log P * r ^ (e + 1 + 1)
  change xiSafeHalfPlaneJacobiInteriorWeight x p *
      (Real.log P / (P + 1) * r ^ e) +
      Real.log P / (P + 1) * r ^ (e + 2) =
    Real.log P * r ^ (e + 1 + 1)
  rw [hb, show e + 1 + 1 = e + 2 by omega, pow_add r e 2]
  have hplus : P + 1 ≠ 0 := by nlinarith
  field_simp [hplus]
  ring

/-- **Safe Jacobi--Gamma source recovery.**  The forced asymmetric operator recovers the complete
shifted von Mangoldt stream at every aperture in the closed safe half-plane. -/
theorem xiSafeHalfPlaneJacobiGammaRecovery_eq_coefficient
    {x : ℝ} (hx : 1 / 2 ≤ x) (p : Nat.Primes) (e : ℕ) :
    xiSafeHalfPlaneJacobiGammaRecovery x
        (gammaSewnMobiusPascalNormalizedRay x)
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p e =
      xiSafeHalfPlanePrimePowerCoefficient x p e := by
  cases e with
  | zero => exact xiSafeHalfPlaneJacobiGammaRecovery_zero hx p
  | succ e => exact xiSafeHalfPlaneJacobiGammaRecovery_succ hx p e

/-- Squared safe coefficient factors into its depth-zero prime-clock energy and a geometric
valuation tail. -/
theorem xiSafeHalfPlanePrimePowerCoefficient_sq_eq
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiSafeHalfPlanePrimePowerCoefficient x p e ^ 2 =
      primeClockScaleMetric x p *
        (xiMobiusContinuousApertureDiskNode x p ^ 2) ^ e := by
  let r := xiMobiusContinuousApertureDiskNode x p
  have hP : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hrpow : r ^ 2 = (p : ℝ) ^ (-2 * x) := by
    dsimp only [r]
    rw [xiMobiusContinuousApertureDiskNode, Real.rpow_def_of_pos hP,
      pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpow : (r ^ (e + 1)) ^ 2 = (r ^ 2) ^ (e + 1) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [xiSafeHalfPlanePrimePowerCoefficient, mul_pow, hpow,
    primeClockScaleMetric, ← hrpow, pow_succ]
  ring

/-- The depth-zero energy is exactly the existing prime-clock scale metric. -/
theorem xiSafeHalfPlanePrimePowerCoefficient_zero_sq_eq_primeClockScaleMetric
    (x : ℝ) (p : Nat.Primes) :
    xiSafeHalfPlanePrimePowerCoefficient x p 0 ^ 2 =
      primeClockScaleMetric x p := by
  simpa using xiSafeHalfPlanePrimePowerCoefficient_sq_eq x p 0

/-- Right of the critical line, the recovered all-prime/all-valuation stream is a genuine
square-summable Hilbert vector. -/
theorem summable_xiSafeHalfPlanePrimePowerCoefficient_sq_of_half_lt
    {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiSafeHalfPlanePrimePowerCoefficient x pe.1 pe.2 ^ 2) := by
  have hinner (p : Nat.Primes) : Summable (fun e : ℕ =>
      xiSafeHalfPlanePrimePowerCoefficient x p e ^ 2) := by
    let a := xiMobiusContinuousApertureDiskNode x p ^ 2
    have ha0 : 0 ≤ a := sq_nonneg _
    have hrlt : xiMobiusContinuousApertureDiskNode x p < 1 :=
      xiMobiusContinuousApertureDiskNode_lt_one (by linarith) p
    have ha1 : a < 1 := by
      have hr0 := xiMobiusContinuousApertureDiskNode_pos x p
      dsimp only [a]
      nlinarith
    exact ((summable_geometric_of_lt_one ha0 ha1).mul_left
      (primeClockScaleMetric x p)).congr (fun e => by
        rw [xiSafeHalfPlanePrimePowerCoefficient_sq_eq])
  rw [summable_prod_of_nonneg (fun pe => sq_nonneg _)]
  constructor
  · exact hinner
  · have hmajor : Summable (fun p : Nat.Primes =>
        2 * primeClockScaleMetric x p) :=
      (summable_primeClockScaleMetric_of_half_lt hx).mul_left 2
    refine Summable.of_nonneg_of_le
      (fun p => tsum_nonneg fun e => sq_nonneg _)
      (fun p => ?_) hmajor
    ·
      let a := xiMobiusContinuousApertureDiskNode x p ^ 2
      have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
      have hP1 : (1 : ℝ) ≤ (p : ℝ) := one_le_two.trans hP
      have hP0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_two hP
      have ha0 : 0 ≤ a := sq_nonneg _
      have hrlt : xiMobiusContinuousApertureDiskNode x p < 1 :=
        xiMobiusContinuousApertureDiskNode_lt_one (by linarith) p
      have ha1 : a < 1 := by
        have hr0 := xiMobiusContinuousApertureDiskNode_pos x p
        dsimp only [a]
        nlinarith
      have harpow : a = (p : ℝ) ^ (-2 * x) := by
        dsimp only [a]
        rw [xiMobiusContinuousApertureDiskNode, Real.rpow_def_of_pos hP0,
          pow_two, ← Real.exp_add]
        congr 1
        ring
      have hahalf : a ≤ 1 / 2 := by
        calc
          a = (p : ℝ) ^ (-2 * x) := harpow
          _ ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
          _ = (p : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
          _ ≤ 1 / 2 := by
            simpa [one_div] using
              (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hP)
      have hden : 0 < 1 - a := sub_pos.mpr ha1
      have hinv : (1 - a)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hden zero_lt_two]
        linarith
      have hmetric : 0 ≤ primeClockScaleMetric x p := by
        unfold primeClockScaleMetric
        positivity
      rw [tsum_congr (fun e => xiSafeHalfPlanePrimePowerCoefficient_sq_eq x p e),
        tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
      calc
        primeClockScaleMetric x p * (1 - a)⁻¹ ≤
            primeClockScaleMetric x p * 2 :=
          mul_le_mul_of_nonneg_left hinv hmetric
        _ = 2 * primeClockScaleMetric x p := by ring

set_option maxHeartbeats 400000 in
/-- At or left of the critical line, even the depth-zero slice prevents square summability. -/
theorem not_summable_xiSafeHalfPlanePrimePowerCoefficient_sq_of_le_half
    {x : ℝ} (hx : x ≤ 1 / 2) :
    ¬ Summable (fun pe : Nat.Primes × ℕ =>
      xiSafeHalfPlanePrimePowerCoefficient x pe.1 pe.2 ^ 2) := by
  intro hsum
  let i : Nat.Primes → Nat.Primes × ℕ := fun p => (p, 0)
  have hi : Function.Injective i := by
    intro p q hpq
    exact congrArg Prod.fst hpq
  have hslice := hsum.comp_injective hi
  change Summable (fun p : Nat.Primes =>
    xiSafeHalfPlanePrimePowerCoefficient x p 0 ^ 2) at hslice
  have hclock : Summable (primeClockScaleMetric x) := by
    exact hslice.congr
      (xiSafeHalfPlanePrimePowerCoefficient_zero_sq_eq_primeClockScaleMetric x)
  have hhalf := (summable_primeClockScaleMetric_iff x).1 hclock
  linarith

/-- **Sharp Hilbert boundary.**  The recovered source stream belongs to `ell^(2 : ℕ)` exactly in the
open safe half-plane. -/
theorem summable_xiSafeHalfPlanePrimePowerCoefficient_sq_iff
    (x : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiSafeHalfPlanePrimePowerCoefficient x pe.1 pe.2 ^ 2) ↔
      1 / 2 < x := by
  constructor
  · intro h
    exact lt_of_not_ge fun hx =>
      not_summable_xiSafeHalfPlanePrimePowerCoefficient_sq_of_le_half hx h
  · exact summable_xiSafeHalfPlanePrimePowerCoefficient_sq_of_half_lt

end RHTower
