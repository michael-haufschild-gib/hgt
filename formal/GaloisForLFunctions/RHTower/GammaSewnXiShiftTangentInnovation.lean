import GaloisForLFunctions.RHTower.GammaSewnSynchronizedEulerFisherBarycenter
import GaloisForLFunctions.RHTower.XiShiftAllValuationLayerBarrier

/-!
# Gamma-sewn Xi-shift tangent innovation

The doubled-aperture synchronized valuation law and the two-state Gamma sewing law are joined
before the lossless boundary is taken.  The resulting positive probability law has a centered
clock whose variance is exactly the full Gamma aperture Fisher curvature.  Its probability
generating function is rooted at the constant mode.

At physical aperture one, the depth marginal is source-derived: its cumulative distribution is
the prime-power coefficient exposed by the completed `+2` Xi shift, divided by the prime
logarithm.  Equivalently, the normalized depth mass is the valuation forward difference of the
actual hypertranscendental Xi-shift source.  This is the source-side tangent operation; no target
response identification, zero-location statement, or RH-equivalent positivity enters here.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- The positive depth marginal of the joined packet, at doubled aperture. -/
def gammaSewnXiShiftJointDepthProbability
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnSynchronizedEulerDepthProbability (2 * x) p e

/-- The Bernoulli parameter forced by the Gamma sewing multiplier. -/
def gammaSewnXiShiftSewingMean (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  q ^ 4 / (1 + q ^ 4)

/-- The two-state Gamma sewing marginal. -/
def gammaSewnXiShiftSewingProbability
    (x : ℝ) (p : Nat.Primes) (b : Bool) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  if b then q ^ 4 / (1 + q ^ 4) else 1 / (1 + q ^ 4)

/-- The bit value of the Gamma sewing state. -/
def gammaSewnXiShiftSewingBit (b : Bool) : ℝ :=
  if b then 1 else 0

/-- The independent positive joint depth--sewing law. -/
def gammaSewnXiShiftJointProbability
    (x : ℝ) (p : Nat.Primes) (e : ℕ) (b : Bool) : ℝ :=
  gammaSewnXiShiftJointDepthProbability x p e *
    gammaSewnXiShiftSewingProbability x p b

theorem gammaSewnXiShiftSewingProbability_sum_one
    (x : ℝ) (p : Nat.Primes) :
    ∑ b : Bool, gammaSewnXiShiftSewingProbability x p b = 1 := by
  have hden : 1 + xiMobiusContinuousApertureDiskNode x p ^ 4 ≠ 0 := by
    positivity
  simp [gammaSewnXiShiftSewingProbability]
  field_simp [hden]
  ring

/-- The joined depth--sewing law is normalized before the boundary limit. -/
theorem tsum_gammaSewnXiShiftJointProbability_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    ∑' e : ℕ, ∑ b : Bool, gammaSewnXiShiftJointProbability x p e b = 1 := by
  have hprob := hasSum_gammaSewnSynchronizedEulerDepthProbability_one
    (x := 2 * x) (by positivity) p
  calc
    _ = ∑' e : ℕ, gammaSewnXiShiftJointDepthProbability x p e := by
      apply tsum_congr
      intro e
      simp only [gammaSewnXiShiftJointProbability]
      rw [← Finset.mul_sum]
      rw [gammaSewnXiShiftSewingProbability_sum_one]
      ring
    _ = 1 := hprob.tsum_eq

/-- Raw joined clock: twice the prime logarithm times depth plus sewing state. -/
def gammaSewnXiShiftJointClock
    (p : Nat.Primes) (e : ℕ) (b : Bool) : ℝ :=
  2 * Real.log (p : ℝ) * ((e : ℝ) + gammaSewnXiShiftSewingBit b)

/-- Mean of the joined clock at positive aperture. -/
def gammaSewnXiShiftJointClockMean (x : ℝ) (p : Nat.Primes) : ℝ :=
  let r := xiMobiusContinuousApertureDiskNode x p ^ 2
  2 * Real.log (p : ℝ) *
    (r / (1 - r) + gammaSewnXiShiftSewingMean x p)

/-- Centering the joined clock splits it into the centered physical Euler height and centered
Gamma sewing bit.  This is an identity of one positive joint law, not a decomposition into signed
boundary channels. -/
theorem gammaSewnXiShiftJointClock_sub_mean_eq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) (b : Bool) :
    gammaSewnXiShiftJointClock p e b - gammaSewnXiShiftJointClockMean x p =
      4 * (xiGammaEulerBoundaryHalfHeight p e -
        gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p) +
      2 * Real.log (p : ℝ) *
        (gammaSewnXiShiftSewingBit b - gammaSewnXiShiftSewingMean x p) := by
  have hnode : xiMobiusContinuousApertureDiskNode (2 * x) p =
      xiMobiusContinuousApertureDiskNode x p ^ 2 := by
    rw [show 2 * x = x + x by ring,
      xiMobiusContinuousApertureDiskNode_add, pow_two]
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hden : 1 - xiMobiusContinuousApertureDiskNode x p ^ 2 ≠ 0 := by
    nlinarith [sq_lt_sq₀
      (xiMobiusContinuousApertureDiskNode_pos x p).le
      (by norm_num : (0 : ℝ) ≤ 1) |>.2 hq1]
  unfold gammaSewnXiShiftJointClock gammaSewnXiShiftJointClockMean
    gammaSewnSynchronizedEulerHalfHeightBarycenter xiGammaEulerBoundaryHalfHeight
  rw [hnode]
  field_simp [hden]
  ring

private theorem gammaSewnXiShiftSewing_centeredSquare
    (x : ℝ) (p : Nat.Primes) (A C : ℝ) :
    ∑ b : Bool, gammaSewnXiShiftSewingProbability x p b *
        (A + C * (gammaSewnXiShiftSewingBit b -
          gammaSewnXiShiftSewingMean x p)) ^ 2 =
      A ^ 2 + C ^ 2 * gammaSewnXiShiftSewingMean x p *
        (1 - gammaSewnXiShiftSewingMean x p) := by
  have hden : 1 + xiMobiusContinuousApertureDiskNode x p ^ 4 ≠ 0 := by
    positivity
  rw [Fintype.sum_bool]
  simp [gammaSewnXiShiftSewingProbability, gammaSewnXiShiftSewingBit,
    gammaSewnXiShiftSewingMean]
  field_simp [hden]
  ring

private theorem hasSum_gammaSewnXiShiftDepthCenteredHeight_sq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftJointDepthProbability x p e *
        (xiGammaEulerBoundaryHalfHeight p e -
          gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p) ^ 2)
      (gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p) := by
  let M := gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p
  have hsecond :=
    hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight_sq
      (x := 2 * x) (by positivity) p
  have hmean : HasSum
      (fun e : ℕ => gammaSewnSynchronizedEulerDepthProbability (2 * x) p e *
        xiGammaEulerBoundaryHalfHeight p e) M :=
    hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight
      (x := 2 * x) (by positivity) p
  have hprob := hasSum_gammaSewnSynchronizedEulerDepthProbability_one
    (x := 2 * x) (by positivity) p
  have hcombined :=
    (hsecond.sub (hmean.mul_left (2 * M))).add (hprob.mul_left (M ^ 2))
  have hcentered : Summable
      (fun e : ℕ => gammaSewnXiShiftJointDepthProbability x p e *
        (xiGammaEulerBoundaryHalfHeight p e - M) ^ 2) := by
    apply hcombined.summable.congr
    intro e
    simp only [gammaSewnXiShiftJointDepthProbability]
    ring
  simpa only [gammaSewnSynchronizedEulerHalfHeightVariance] using
    hcentered.hasSum

/-- Genuine second moment of the centered joined depth--sewing clock. -/
def gammaSewnXiShiftJointClockVariance
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ, ∑ b : Bool,
    gammaSewnXiShiftJointProbability x p e b *
      (gammaSewnXiShiftJointClock p e b -
        gammaSewnXiShiftJointClockMean x p) ^ 2

/-- The joined positive clock has exactly the full Gamma aperture Fisher curvature as variance. -/
theorem gammaSewnXiShiftJointClockVariance_eq_fisherCurvature
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnXiShiftJointClockVariance x p =
      gammaSewnMobiusApertureFisherCurvature x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let L := Real.log (p : ℝ)
  let B := gammaSewnXiShiftSewingMean x p
  have hden : 1 + q ^ 4 ≠ 0 := by positivity
  have hdepth := hasSum_gammaSewnXiShiftDepthCenteredHeight_sq hx p
  have hprob := hasSum_gammaSewnSynchronizedEulerDepthProbability_one
    (x := 2 * x) (by positivity) p
  have hsum := (hdepth.mul_left 16).add
    (hprob.mul_left (4 * L ^ 2 * B * (1 - B)))
  unfold gammaSewnXiShiftJointClockVariance
  calc
    _ = ∑' e : ℕ,
        (16 * (gammaSewnXiShiftJointDepthProbability x p e *
          (xiGammaEulerBoundaryHalfHeight p e -
            gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p) ^ 2) +
         (4 * L ^ 2 * B * (1 - B)) *
          gammaSewnXiShiftJointDepthProbability x p e) := by
      apply tsum_congr
      intro e
      calc
        ∑ b : Bool, gammaSewnXiShiftJointProbability x p e b *
            (gammaSewnXiShiftJointClock p e b -
              gammaSewnXiShiftJointClockMean x p) ^ 2 =
            gammaSewnXiShiftJointDepthProbability x p e *
              ∑ b : Bool, gammaSewnXiShiftSewingProbability x p b *
                (4 * (xiGammaEulerBoundaryHalfHeight p e -
                    gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p) +
                  2 * L * (gammaSewnXiShiftSewingBit b - B)) ^ 2 := by
              simp_rw [gammaSewnXiShiftJointClock_sub_mean_eq hx]
              simp only [gammaSewnXiShiftJointProbability]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _hb
              dsimp only [L, B]
              ring
        _ = gammaSewnXiShiftJointDepthProbability x p e *
              ((4 * (xiGammaEulerBoundaryHalfHeight p e -
                  gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p)) ^ 2 +
                (2 * L) ^ 2 * B * (1 - B)) := by
              rw [gammaSewnXiShiftSewing_centeredSquare]
        _ = 16 * (gammaSewnXiShiftJointDepthProbability x p e *
              (xiGammaEulerBoundaryHalfHeight p e -
                gammaSewnSynchronizedEulerHalfHeightBarycenter (2 * x) p) ^ 2) +
            (4 * L ^ 2 * B * (1 - B)) *
              gammaSewnXiShiftJointDepthProbability x p e := by ring
    _ = 16 * gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p +
        4 * L ^ 2 * B * (1 - B) := by
      convert hsum.tsum_eq using 1
      all_goals ring
    _ = 16 * gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p +
        gammaSewnSewingBernoulliFisherCurvature x p := by
      congr 1
      dsimp only [q, L, B, gammaSewnXiShiftSewingMean]
      unfold gammaSewnSewingBernoulliFisherCurvature
      field_simp [hden]
      ring
    _ = gammaSewnMobiusApertureFisherCurvature x p :=
      (gammaSewnMobiusApertureFisherCurvature_eq_sixteen_heightVariance_add_sewing
        hx p).symm

/-- Closed probability generating function of depth plus sewing bit. -/
def gammaSewnXiShiftJointPGF
    (x : ℝ) (p : Nat.Primes) (z : ℂ) : ℂ :=
  let r := xiMobiusContinuousApertureDiskNode x p ^ 2
  ((1 - r : ℝ) : ℂ) * (1 + ((r ^ 2 : ℝ) : ℂ) * z) /
    (((1 + r ^ 2 : ℝ) : ℂ) * (1 - (r : ℂ) * z))

/-- Rooting the joined source removes the constant mode before any norm or boundary limit. -/
theorem gammaSewnXiShiftJointPGF_sub_one_eq_tangent
    (x : ℝ) (p : Nat.Primes) (z : ℂ)
    (hz : 1 - ((xiMobiusContinuousApertureDiskNode x p ^ 2 : ℝ) : ℂ) * z ≠ 0) :
    gammaSewnXiShiftJointPGF x p z - 1 =
      (((xiMobiusContinuousApertureDiskNode x p ^ 2 *
          (1 + xiMobiusContinuousApertureDiskNode x p ^ 2) : ℝ) : ℂ) *
        (z - 1)) /
      (((1 + xiMobiusContinuousApertureDiskNode x p ^ 4 : ℝ) : ℂ) *
        (1 - ((xiMobiusContinuousApertureDiskNode x p ^ 2 : ℝ) : ℂ) * z)) := by
  have hplus : ((1 + xiMobiusContinuousApertureDiskNode x p ^ 4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show
      1 + xiMobiusContinuousApertureDiskNode x p ^ 4 ≠ 0 by positivity)
  have hz' :
      1 - z * ((xiMobiusContinuousApertureDiskNode x p ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa [mul_comm] using hz
  unfold gammaSewnXiShiftJointPGF
  field_simp [hz, hz', hplus]
  push_cast
  ring

theorem gammaSewnXiShiftJointPGF_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnXiShiftJointPGF x p 1 = 1 := by
  let r := xiMobiusContinuousApertureDiskNode x p ^ 2
  have hq0 := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hr1 : r < 1 := by
    dsimp only [r]
    nlinarith [sq_lt_sq₀ hq0.le (by norm_num : (0 : ℝ) ≤ 1) |>.2 hq1]
  have hminusR : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
  have hplusR : 1 + r ^ 2 ≠ 0 := by positivity
  have hminus : ((1 - r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hminusR
  have hplus : ((1 + r ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hplusR
  change (((1 - r : ℝ) : ℂ) * (1 + ((r ^ 2 : ℝ) : ℂ) * 1) /
    (((1 + r ^ 2 : ℝ) : ℂ) * (1 - (r : ℂ) * 1))) = 1
  push_cast at hminus hplus ⊢
  field_simp [hminus, hplus]

/-- Finite CDF of the source-derived depth marginal. -/
def gammaSewnXiShiftDepthCDF (p : Nat.Primes) (e : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (e + 1), gammaSewnXiShiftJointDepthProbability 1 p j

theorem gammaSewnXiShiftDepthCDF_eq_one_sub_pow
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnXiShiftDepthCDF p e =
      1 - xiMobiusContinuousApertureDiskNode 2 p ^ (e + 1) := by
  induction e with
  | zero =>
      simp [gammaSewnXiShiftDepthCDF, gammaSewnXiShiftJointDepthProbability,
        gammaSewnSynchronizedEulerDepthProbability]
  | succ e ih =>
      rw [gammaSewnXiShiftDepthCDF, Finset.sum_range_succ]
      change gammaSewnXiShiftDepthCDF p e +
          gammaSewnXiShiftJointDepthProbability 1 p (e + 1) = _
      rw [ih]
      simp only [gammaSewnXiShiftJointDepthProbability,
        gammaSewnSynchronizedEulerDepthProbability]
      ring

private theorem xiMobiusContinuousApertureDiskNode_two_pow_succ_eq_rpow
    (p : Nat.Primes) (e : ℕ) :
    xiMobiusContinuousApertureDiskNode 2 p ^ (e + 1) =
      (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hpowNat : 0 < (p : ℕ) ^ (e + 1) := pow_pos p.2.pos _
  have hpow : (0 : ℝ) < (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  rw [xiMobiusContinuousApertureDiskNode_pow, Real.rpow_def_of_pos hpow]
  congr 1
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- The prime-power coefficient of the actual completed `+2` Xi-shift source is the depth CDF,
scaled by the prime logarithm. -/
theorem filteredVonMangoldtCoeff_primePower_eq_gammaSewnXiShiftDepthCDF
    (p : Nat.Primes) (e : ℕ) :
    filteredVonMangoldtCoeff ((p : ℕ) ^ (e + 1)) =
      ((Real.log (p : ℝ) * gammaSewnXiShiftDepthCDF p e : ℝ) : ℂ) := by
  have hcpow : ((((p : ℕ) ^ (e + 1) : ℕ) : ℂ)) ^ (-(2 : ℂ)) =
      ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ) ^ (-(2 : ℝ)) : ℝ) := by
    simpa using
      (Complex.ofReal_cpow
        (Nat.cast_nonneg ((p : ℕ) ^ (e + 1))) (-(2 : ℝ))).symm
  rw [filteredVonMangoldtCoeff,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.2, hcpow,
    gammaSewnXiShiftDepthCDF_eq_one_sub_pow,
    xiMobiusContinuousApertureDiskNode_two_pow_succ_eq_rpow]
  norm_cast

theorem gammaSewnXiShiftDepthCDF_zero
    (p : Nat.Primes) :
    gammaSewnXiShiftDepthCDF p 0 =
      gammaSewnXiShiftJointDepthProbability 1 p 0 := by
  simp [gammaSewnXiShiftDepthCDF]

theorem gammaSewnXiShiftDepthCDF_forwardDifference
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnXiShiftDepthCDF p (e + 1) - gammaSewnXiShiftDepthCDF p e =
      gammaSewnXiShiftJointDepthProbability 1 p (e + 1) := by
  unfold gammaSewnXiShiftDepthCDF
  rw [show e + 1 + 1 = (e + 1) + 1 by omega,
    Finset.sum_range_succ]
  ring

/-- The zero-depth Xi-shift coefficient is the first normalized source innovation. -/
theorem filteredVonMangoldtCoeff_prime_eq_gammaSewnXiShiftDepthInnovation
    (p : Nat.Primes) :
    filteredVonMangoldtCoeff p =
      ((Real.log (p : ℝ) *
        gammaSewnXiShiftJointDepthProbability 1 p 0 : ℝ) : ℂ) := by
  simpa [gammaSewnXiShiftDepthCDF] using
    (filteredVonMangoldtCoeff_primePower_eq_gammaSewnXiShiftDepthCDF p 0)

/-- Adjacent prime-power coefficients of the actual Xi-shift source differ by exactly one
normalized valuation-depth atom. -/
theorem filteredVonMangoldtCoeff_primePower_forwardDifference_eq_depthInnovation
    (p : Nat.Primes) (e : ℕ) :
    filteredVonMangoldtCoeff ((p : ℕ) ^ ((e + 1) + 1)) -
        filteredVonMangoldtCoeff ((p : ℕ) ^ (e + 1)) =
      ((Real.log (p : ℝ) *
        gammaSewnXiShiftJointDepthProbability 1 p (e + 1) : ℝ) : ℂ) := by
  rw [filteredVonMangoldtCoeff_primePower_eq_gammaSewnXiShiftDepthCDF,
    filteredVonMangoldtCoeff_primePower_eq_gammaSewnXiShiftDepthCDF]
  norm_cast
  rw [← mul_sub, gammaSewnXiShiftDepthCDF_forwardDifference]

/-! ## Height-localized endpoint synthesis

The apparent `p⁻²`-to-`p⁻¹` resolution deficit is entirely a father-mode phenomenon.  The
following all-depth physical-height lift has endpoint mean `p⁻¹`, while its centered `L²` mass is
exactly `p⁻⁴`.  Thus tangent renormalization removes the only square-root scale gap; the remaining
height-localized channel is already at the Xi-shift innovation scale.
-/

/-- The source-forced all-depth height lift of one prime endpoint. -/
def gammaSewnXiShiftEndpointHeightLift (p : Nat.Primes) (e : ℕ) : ℝ :=
  (1 - xiMobiusContinuousApertureDiskNode 2 p) / (p : ℝ) * ((e : ℝ) + 1)

/-- The endpoint lift is a fixed normalization of the literal physical Euler half-height. -/
theorem gammaSewnXiShiftEndpointHeightLift_eq_eulerHeight
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnXiShiftEndpointHeightLift p e =
      (2 * (1 - xiMobiusContinuousApertureDiskNode 2 p) /
        ((p : ℝ) * Real.log (p : ℝ))) *
          xiGammaEulerBoundaryHalfHeight p e := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hL : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  unfold gammaSewnXiShiftEndpointHeightLift xiGammaEulerBoundaryHalfHeight
  field_simp [hp.ne', hL]

/-- Infinite physical-height synthesis reconstructs the ordinary-prime endpoint amplitude. -/
theorem hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift
    (p : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftJointDepthProbability 1 p e *
        gammaSewnXiShiftEndpointHeightLift p e)
      ((p : ℝ)⁻¹) := by
  let r := xiMobiusContinuousApertureDiskNode 2 p
  let P : ℝ := p
  let L := Real.log P
  have hL' : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hL : L ≠ 0 := by
    dsimp only [L, P]
    exact hL'
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one
    (by norm_num : (0 : ℝ) < 2) p
  have hheight :=
    hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight
      (x := 2) (by norm_num) p
  have hscaled := hheight.mul_left (2 * (1 - r) / (P * L))
  convert hscaled using 1
  · funext e
    rw [gammaSewnXiShiftEndpointHeightLift_eq_eulerHeight]
    dsimp only [r, P, L, gammaSewnXiShiftJointDepthProbability]
    ring
  · unfold gammaSewnSynchronizedEulerHalfHeightBarycenter
    dsimp only [r, P, L]
    field_simp [hP.ne', hL', sub_ne_zero.mpr hr1.ne']

private theorem gammaSewnXiShiftEndpointHeightLift_sub_mean_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnXiShiftEndpointHeightLift p e - (p : ℝ)⁻¹ =
      (2 * (1 - xiMobiusContinuousApertureDiskNode 2 p) /
        ((p : ℝ) * Real.log (p : ℝ))) *
        (xiGammaEulerBoundaryHalfHeight p e -
          gammaSewnSynchronizedEulerHalfHeightBarycenter 2 p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hL : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one
    (by norm_num : (0 : ℝ) < 2) p
  unfold gammaSewnXiShiftEndpointHeightLift xiGammaEulerBoundaryHalfHeight
    gammaSewnSynchronizedEulerHalfHeightBarycenter
  field_simp [hp.ne', hL, sub_ne_zero.mpr hr1.ne']

/-- The centered endpoint lift has exact `p⁻²` norm scale: its squared norm is `p⁻⁴`. -/
theorem hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift_centered_sq
    (p : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftJointDepthProbability 1 p e *
        (gammaSewnXiShiftEndpointHeightLift p e - (p : ℝ)⁻¹) ^ 2)
      (xiMobiusContinuousApertureDiskNode 2 p / (p : ℝ) ^ 2) := by
  let r := xiMobiusContinuousApertureDiskNode 2 p
  let P : ℝ := p
  let L := Real.log P
  have hL' : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hL : L ≠ 0 := by
    dsimp only [L, P]
    exact hL'
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one
    (by norm_num : (0 : ℝ) < 2) p
  have hcentered :=
    hasSum_gammaSewnXiShiftDepthCenteredHeight_sq (x := 1) (by norm_num) p
  have hscaled := hcentered.mul_left ((2 * (1 - r) / (P * L)) ^ 2)
  convert hscaled using 1
  · funext e
    rw [gammaSewnXiShiftEndpointHeightLift_sub_mean_eq]
    dsimp only [r, P, L]
    ring
  · rw [show (2 : ℝ) * 1 = 2 by norm_num,
      gammaSewnSynchronizedEulerHalfHeightVariance_eq
      (x := 2) (by norm_num)]
    dsimp only [r, P, L]
    field_simp [hP.ne', hL', sub_ne_zero.mpr hr1.ne']
    norm_num

theorem xiMobiusContinuousApertureDiskNode_two_eq_inv_sq
    (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode 2 p = ((p : ℝ)⁻¹) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  unfold xiMobiusContinuousApertureDiskNode
  rw [show -(2 : ℝ) * Real.log (p : ℝ) =
      -Real.log (p : ℝ) + -Real.log (p : ℝ) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring

/-- Exact tangent-scale form of the centered height lift. -/
theorem hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift_centered_sq_eq_inv_four
    (p : Nat.Primes) :
    HasSum
      (fun e : ℕ => gammaSewnXiShiftJointDepthProbability 1 p e *
        (gammaSewnXiShiftEndpointHeightLift p e - (p : ℝ)⁻¹) ^ 2)
      (((p : ℝ)⁻¹) ^ 4) := by
  convert
    hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift_centered_sq p using 1
  rw [xiMobiusContinuousApertureDiskNode_two_eq_inv_sq]
  field_simp

/-- The all-depth height synthesis is a strict local `L²` contraction. -/
theorem gammaSewnXiShiftEndpointHeightLift_centered_sq_sum_lt_one
    (p : Nat.Primes) :
    (∑' e : ℕ, gammaSewnXiShiftJointDepthProbability 1 p e *
      (gammaSewnXiShiftEndpointHeightLift p e - (p : ℝ)⁻¹) ^ 2) < 1 := by
  rw [(hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift_centered_sq_eq_inv_four
    p).tsum_eq]
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  exact pow_lt_one₀ hinv0 hinv (by norm_num)

/-- The actual Xi-shift innovation stream, with the depth-zero term rooted at zero. -/
def filteredVonMangoldtPrimePowerInnovation
    (p : Nat.Primes) : ℕ → ℂ
  | 0 => filteredVonMangoldtCoeff p
  | e + 1 =>
      filteredVonMangoldtCoeff ((p : ℕ) ^ ((e + 1) + 1)) -
        filteredVonMangoldtCoeff ((p : ℕ) ^ (e + 1))

/-- Every actual Xi-shift innovation is the prime logarithm times one normalized depth atom. -/
theorem filteredVonMangoldtPrimePowerInnovation_eq_depthProbability
    (p : Nat.Primes) (e : ℕ) :
    filteredVonMangoldtPrimePowerInnovation p e =
      ((Real.log (p : ℝ) *
        gammaSewnXiShiftJointDepthProbability 1 p e : ℝ) : ℂ) := by
  rcases e with _ | e
  · exact filteredVonMangoldtCoeff_prime_eq_gammaSewnXiShiftDepthInnovation p
  · exact
      filteredVonMangoldtCoeff_primePower_forwardDifference_eq_depthInnovation p e

/-- The physical ordinary-prime endpoint coefficient is reconstructed by a strict, all-depth,
height-localized synthesis of the actual completed Xi-shift innovations. -/
theorem hasSum_filteredVonMangoldtPrimePowerInnovation_mul_endpointHeightLift
    (p : Nat.Primes) :
    HasSum
      (fun e : ℕ => filteredVonMangoldtPrimePowerInnovation p e *
        (gammaSewnXiShiftEndpointHeightLift p e : ℂ))
      ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) := by
  have hreal :=
    (hasSum_gammaSewnXiShiftDepthProbability_mul_endpointHeightLift p).mul_left
      (Real.log (p : ℝ))
  have hcomplex := hreal.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  convert hcomplex using 1
  · funext e
    rw [filteredVonMangoldtPrimePowerInnovation_eq_depthProbability]
    simp only [Function.comp_apply]
    change ((Real.log (p : ℝ) *
          gammaSewnXiShiftJointDepthProbability 1 p e : ℝ) : ℂ) *
        (gammaSewnXiShiftEndpointHeightLift p e : ℂ) =
      ((Real.log (p : ℝ) *
        (gammaSewnXiShiftJointDepthProbability 1 p e *
          gammaSewnXiShiftEndpointHeightLift p e) : ℝ) : ℂ)
    push_cast
    ring

end

end RHTower
