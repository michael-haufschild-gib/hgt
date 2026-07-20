import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction
import GaloisForLFunctions.RHTower.SoninSemilocalFluxSource

/-!
# Critical half-aperture Jacobi--Gamma recovery

The Gamma-sewn continuous-aperture source contains the central von Mangoldt prime-power
coefficient by a source operation which is invisible to scalar one-edge recovery.  First apply
the infinitesimal Pascal death rate and undo the uniformly invertible Gamma sewing.  At the
critical half-aperture, the resulting geometric ray is then acted on by unilateral valuation
adjacency.  Every positive depth is recovered from its two neighbours.  At depth zero the unique
missing predecessor is supplied exactly by the Gamma-coupled vacuum coordinate, with rational
gauge `p^2 / (p^2 - 1)` lying in `[1, 4/3]`.

The half-aperture is rigid: self-reproduction under the same Jacobi adjacency at just the first
two depths forces the aperture to equal `1/2`.  Thus the central exponent is selected by the
Möbius denominator `p+1` and valuation adjacency, rather than inserted as a target coefficient.

The coefficient `(log p) * p^(-(e+1)/2)` itself is classical (it is the prime-power term in the
central explicit formula).  The new source statement is its exact bounded-gauge production from
the Gamma-sewn Möbius ray and Gamma vacuum.  This is a pre-Gram coefficient bridge; it does not
assert the remaining polar/window cancellation or prove RH.
-/

namespace RHTower

noncomputable section

/-- Infinitesimal rate of the source-selected Pascal thinning connection. -/
def gammaSewnMobiusPascalDeathRate (x : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / (1 - xiMobiusContinuousApertureDiskNode x p)

/-- Apply the Pascal generator and the inverse Gamma sewing before forming a Gram. -/
def gammaSewnMobiusPascalNormalizedRay
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusPascalDeathRate x p *
    (gammaSewnMobiusValuationContractionMultiplier x p)⁻¹ *
      gammaSewnMobiusContinuousApertureFeature x p e

/-- The generator cancels the aperture increment, while inverse sewing cancels only a uniformly
invertible multiplier.  The fixed critical Möbius damping `1 / (p+1)` remains. -/
theorem gammaSewnMobiusPascalNormalizedRay_eq_geometric
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusPascalNormalizedRay x p e =
      Real.log (p : ℝ) / ((p : ℝ) + 1) *
        xiMobiusContinuousApertureDiskNode x p ^ e := by
  let P : ℝ := p
  let r := xiMobiusContinuousApertureDiskNode x p
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hgap : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  have hc : c ≠ 0 :=
    (gammaSewnMobiusValuationContractionMultiplier_pos x p).ne'
  have hu : xiTransversePrimeApertureDiskNode 1 p = P⁻¹ :=
    xiTransversePrimeApertureDiskNode_one_eq_inv p
  rw [gammaSewnMobiusPascalNormalizedRay,
    gammaSewnMobiusPascalDeathRate,
    gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  change Real.log P / (1 - r) * c⁻¹ *
      (c * ((xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p)) *
          (1 - r) * r ^ e)) = Real.log P / (P + 1) * r ^ e
  rw [hu]
  field_simp [hgap, hc, hP.ne']

/-- Squaring the half-aperture node gives the unit-aperture reciprocal-prime node. -/
theorem xiMobiusContinuousApertureDiskNode_half_sq
    (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (1 / 2) p ^ 2 =
      xiTransversePrimeApertureDiskNode 1 p := by
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv,
    xiMobiusContinuousApertureDiskNode_pow]
  have hP : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  norm_num
  rw [Real.exp_neg, Real.exp_log hP]

/-- The half-aperture node is the central reciprocal square-root prime weight. -/
theorem xiMobiusContinuousApertureDiskNode_half_eq_inv_sqrt
    (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (1 / 2) p =
      (Real.sqrt (p : ℝ))⁻¹ := by
  have hP : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [xiMobiusContinuousApertureDiskNode, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hP, ← Real.exp_neg]
  congr 1
  ring

/-- The Pascal-normalized sewn ray at the unique critical aperture. -/
def criticalHalfApertureGammaSewnPascalRay
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusPascalNormalizedRay (1 / 2) p e

theorem criticalHalfApertureGammaSewnPascalRay_eq
    (p : Nat.Primes) (e : ℕ) :
    criticalHalfApertureGammaSewnPascalRay p e =
      Real.log (p : ℝ) / ((p : ℝ) + 1) *
        xiMobiusContinuousApertureDiskNode (1 / 2) p ^ e := by
  exact gammaSewnMobiusPascalNormalizedRay_eq_geometric
    (by norm_num) p e

/-- Rational Gamma boundary gauge.  Unlike the forbidden scalar resolution by `p+1`, this gauge
is uniformly bounded over every prime. -/
def criticalHalfApertureGammaBoundaryGauge (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)

theorem criticalHalfApertureGammaBoundaryGauge_pos (p : Nat.Primes) :
    0 < criticalHalfApertureGammaBoundaryGauge p := by
  have hP : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  unfold criticalHalfApertureGammaBoundaryGauge
  exact div_pos (sq_pos_of_pos (zero_lt_one.trans hP)) (by nlinarith)

/-- The Gamma boundary repair is bounded by `4/3`, sharply at the smallest prime. -/
theorem criticalHalfApertureGammaBoundaryGauge_le_four_thirds
    (p : Nat.Primes) :
    criticalHalfApertureGammaBoundaryGauge p ≤ 4 / 3 := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  rw [criticalHalfApertureGammaBoundaryGauge, div_le_iff₀ hden]
  nlinarith

theorem one_le_criticalHalfApertureGammaBoundaryGauge
    (p : Nat.Primes) :
    1 ≤ criticalHalfApertureGammaBoundaryGauge p := by
  have hP : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  rw [criticalHalfApertureGammaBoundaryGauge, le_div_iff₀ hden]
  linarith

theorem criticalHalfApertureGammaBoundaryGauge_sq_le_sixteen_ninths
    (p : Nat.Primes) :
    criticalHalfApertureGammaBoundaryGauge p ^ 2 ≤ 16 / 9 := by
  have h0 := criticalHalfApertureGammaBoundaryGauge_pos p
  have h4 := criticalHalfApertureGammaBoundaryGauge_le_four_thirds p
  nlinarith

/-- Unilateral Jacobi adjacency with a separate Gamma boundary input. -/
def criticalHalfApertureJacobiGammaRecovery
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ)
    (p : Nat.Primes) : ℕ → ℝ
  | 0 => f p 1 + criticalHalfApertureGammaBoundaryGauge p * g p
  | e + 1 => f p e + f p (e + 2)

/-- Pointwise energy control at the Gamma boundary.  The constant is uniform over all primes. -/
theorem criticalHalfApertureJacobiGammaRecovery_zero_sq_le
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ) (p : Nat.Primes) :
    criticalHalfApertureJacobiGammaRecovery f g p 0 ^ 2 ≤
      2 * (f p 1) ^ 2 + 32 / 9 * (g p) ^ 2 := by
  let G := criticalHalfApertureGammaBoundaryGauge p
  have hG := criticalHalfApertureGammaBoundaryGauge_sq_le_sixteen_ninths p
  have hgsq : (G * g p) ^ 2 ≤ 16 / 9 * (g p) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hG (sq_nonneg (g p))
  rw [criticalHalfApertureJacobiGammaRecovery]
  change (f p 1 + G * g p) ^ 2 ≤
    2 * (f p 1) ^ 2 + 32 / 9 * (g p) ^ 2
  nlinarith [sq_nonneg (f p 1 - G * g p)]

/-- Pointwise energy control on every interior valuation layer. -/
theorem criticalHalfApertureJacobiGammaRecovery_succ_sq_le
    (f : Nat.Primes → ℕ → ℝ) (g : Nat.Primes → ℝ)
    (p : Nat.Primes) (e : ℕ) :
    criticalHalfApertureJacobiGammaRecovery f g p (e + 1) ^ 2 ≤
      2 * (f p e) ^ 2 + 2 * (f p (e + 2)) ^ 2 := by
  rw [criticalHalfApertureJacobiGammaRecovery]
  nlinarith [sq_nonneg (f p e - f p (e + 2))]

/-- Central prime-power coefficient, expressed in the intrinsic half-aperture node. -/
def criticalCentralPrimePowerCoefficient (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.log (p : ℝ) *
    xiMobiusContinuousApertureDiskNode (1 / 2) p ^ (e + 1)

theorem criticalCentralPrimePowerCoefficient_eq_inv_sqrt
    (p : Nat.Primes) (e : ℕ) :
    criticalCentralPrimePowerCoefficient p e =
      Real.log (p : ℝ) * ((Real.sqrt (p : ℝ))⁻¹ ^ (e + 1)) := by
  rw [criticalCentralPrimePowerCoefficient,
    xiMobiusContinuousApertureDiskNode_half_eq_inv_sqrt]

/-- The Gamma vacuum is exactly the missing negative-depth predecessor, after the bounded rational
gauge is applied. -/
theorem criticalHalfApertureGammaBoundaryGauge_mul_vacuum_eq
    (p : Nat.Primes) :
    criticalHalfApertureGammaBoundaryGauge p *
        xiTransversePrimeHalfShiftedFirstValuationCoordinate p =
      xiMobiusContinuousApertureDiskNode (1 / 2) p *
        (p : ℝ) / ((p : ℝ) + 1) := by
  let P : ℝ := p
  let q := xiMobiusContinuousApertureDiskNode (1 / 2) p
  let u := xiTransversePrimeApertureDiskNode 1 p
  have hP : (1 : ℝ) < P := by
    dsimp only [P]
    exact_mod_cast p.2.one_lt
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos _ p
  have hq2 : q ^ 2 = u := xiMobiusContinuousApertureDiskNode_half_sq p
  have hsqrt : Real.sqrt u = q := by
    rw [← hq2, Real.sqrt_sq_eq_abs, abs_of_pos hq0]
  have hu : u = P⁻¹ := xiTransversePrimeApertureDiskNode_one_eq_inv p
  rw [xiTransversePrimeHalfShiftedFirstValuationCoordinate_eq]
  change criticalHalfApertureGammaBoundaryGauge p *
      (Real.sqrt u * (1 - u)) = q * P / (P + 1)
  rw [hsqrt, hu]
  unfold criticalHalfApertureGammaBoundaryGauge
  change P ^ 2 / (P ^ 2 - 1) * (q * (1 - P⁻¹)) = q * P / (P + 1)
  have hP0 : P ≠ 0 := ne_of_gt (zero_lt_one.trans hP)
  have hden : P ^ 2 - 1 ≠ 0 := by nlinarith
  have hplus : P + 1 ≠ 0 := by nlinarith
  field_simp [hP0, hden, hplus]
  ring

/-- Every positive valuation depth is recovered by the two adjacent normalized source depths. -/
theorem criticalHalfApertureJacobiGammaRecovery_succ
    (p : Nat.Primes) (e : ℕ) :
    criticalHalfApertureJacobiGammaRecovery
        criticalHalfApertureGammaSewnPascalRay
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p (e + 1) =
      criticalCentralPrimePowerCoefficient p (e + 1) := by
  let P : ℝ := p
  let q := xiMobiusContinuousApertureDiskNode (1 / 2) p
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.2.pos
  have hq2 : q ^ 2 = P⁻¹ := by
    rw [xiMobiusContinuousApertureDiskNode_half_sq,
      xiTransversePrimeApertureDiskNode_one_eq_inv]
  rw [criticalHalfApertureJacobiGammaRecovery,
    criticalHalfApertureGammaSewnPascalRay_eq,
    criticalHalfApertureGammaSewnPascalRay_eq,
    criticalCentralPrimePowerCoefficient]
  change Real.log P / (P + 1) * q ^ e +
      Real.log P / (P + 1) * q ^ (e + 2) =
    Real.log P * q ^ (e + 1 + 1)
  rw [show e + 1 + 1 = e + 2 by omega, pow_add q e 2, hq2]
  field_simp [hP.ne']

/-- The depth-zero defect of unilateral adjacency is repaired by the actual Gamma vacuum. -/
theorem criticalHalfApertureJacobiGammaRecovery_zero
    (p : Nat.Primes) :
    criticalHalfApertureJacobiGammaRecovery
        criticalHalfApertureGammaSewnPascalRay
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p 0 =
      criticalCentralPrimePowerCoefficient p 0 := by
  let P : ℝ := p
  let q := xiMobiusContinuousApertureDiskNode (1 / 2) p
  have hP : (1 : ℝ) < P := by
    dsimp only [P]
    exact_mod_cast p.2.one_lt
  have hboundary :=
    criticalHalfApertureGammaBoundaryGauge_mul_vacuum_eq p
  rw [criticalHalfApertureJacobiGammaRecovery,
    criticalHalfApertureGammaSewnPascalRay_eq,
    criticalCentralPrimePowerCoefficient]
  change Real.log P / (P + 1) * q ^ 1 +
      criticalHalfApertureGammaBoundaryGauge p *
        (Real.log P * xiTransversePrimeHalfShiftedFirstValuationCoordinate p) =
    Real.log P * q ^ (0 + 1)
  rw [show criticalHalfApertureGammaBoundaryGauge p *
      (Real.log P * xiTransversePrimeHalfShiftedFirstValuationCoordinate p) =
      Real.log P *
        (criticalHalfApertureGammaBoundaryGauge p *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p) by ring,
    hboundary]
  simp only [pow_one, zero_add]
  change Real.log P / (P + 1) * q +
      Real.log P * (q * P / (P + 1)) = Real.log P * q
  have hplus : P + 1 ≠ 0 := by nlinarith
  field_simp [hplus]
  ring

/-- **Jacobi--Gamma source recovery.**  The complete central von Mangoldt prime-power stream is the
image of the Gamma-sewn half-aperture ray plus its Gamma boundary coordinate. -/
theorem criticalHalfApertureJacobiGammaRecovery_eq_centralCoefficient
    (p : Nat.Primes) (e : ℕ) :
    criticalHalfApertureJacobiGammaRecovery
        criticalHalfApertureGammaSewnPascalRay
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p e =
      criticalCentralPrimePowerCoefficient p e := by
  cases e with
  | zero => exact criticalHalfApertureJacobiGammaRecovery_zero p
  | succ e => exact criticalHalfApertureJacobiGammaRecovery_succ p e

/-- The recovered real stream is literally the existing semilocal Sonin prime-flux source. -/
theorem criticalHalfApertureJacobiGammaRecovery_eq_soninPrimeFlux
    (p : Nat.Primes) (e : ℕ) :
    (criticalHalfApertureJacobiGammaRecovery
        criticalHalfApertureGammaSewnPascalRay
        (fun p => Real.log (p : ℝ) *
          xiTransversePrimeHalfShiftedFirstValuationCoordinate p)
        p e : ℂ) =
      soninSemilocalPrimeFluxCoefficient (p, e) := by
  rw [criticalHalfApertureJacobiGammaRecovery_eq_centralCoefficient,
    criticalCentralPrimePowerCoefficient_eq_inv_sqrt,
    soninSemilocalPrimeFluxCoefficient_eq_vonMangoldt,
    vonMangoldt_prime_pow_succ_eq_log]
  norm_cast

/-- Doubling aperture squares its disk node. -/
private theorem xiMobiusContinuousApertureDiskNode_two_mul
    (x : ℝ) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (2 * x) p =
      xiMobiusContinuousApertureDiskNode x p ^ 2 := by
  rw [xiMobiusContinuousApertureDiskNode,
    xiMobiusContinuousApertureDiskNode, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- **Critical-aperture rigidity.**  Among positive apertures, reproduction of the generator ray
by symmetric valuation adjacency is possible exactly at `x=1/2`.  Equality at depths `0` and `2`
already forces the critical aperture. -/
theorem gammaSewnMobiusPascalJacobi_selfReproduction_iff
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusPascalNormalizedRay x p 0 +
        gammaSewnMobiusPascalNormalizedRay x p 2 =
          Real.log (p : ℝ) *
            xiMobiusContinuousApertureDiskNode x p ^ 2 ↔
      x = 1 / 2 := by
  let P : ℝ := p
  let r := xiMobiusContinuousApertureDiskNode x p
  have hP : (1 : ℝ) < P := by
    dsimp only [P]
    exact_mod_cast p.2.one_lt
  have hL : 0 < Real.log P := Real.log_pos hP
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos x p
  constructor
  · intro h
    rw [gammaSewnMobiusPascalNormalizedRay_eq_geometric hx,
      gammaSewnMobiusPascalNormalizedRay_eq_geometric hx, pow_zero] at h
    change Real.log P / (P + 1) * 1 +
        Real.log P / (P + 1) * r ^ 2 = Real.log P * r ^ 2 at h
    have hden : P + 1 ≠ 0 := by nlinarith
    field_simp [hden] at h
    have hr2 : r ^ 2 = P⁻¹ := by
      have hfactor : Real.log P * (1 - P * r ^ 2) = 0 := by
        nlinarith
      have : 1 - P * r ^ 2 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hL.ne'
      field_simp [ne_of_gt hP]
      nlinarith
    have hnodes : xiMobiusContinuousApertureDiskNode (2 * x) p =
        xiMobiusContinuousApertureDiskNode 1 p := by
      rw [xiMobiusContinuousApertureDiskNode_two_mul]
      change r ^ 2 = xiMobiusContinuousApertureDiskNode 1 p
      rw [hr2, show xiMobiusContinuousApertureDiskNode 1 p = P⁻¹ by
        unfold xiMobiusContinuousApertureDiskNode
        rw [neg_mul, one_mul, Real.exp_neg, Real.exp_log (by linarith)]]
    have harg := xiMobiusContinuousApertureDiskNode_injective p hnodes
    nlinarith
  · rintro rfl
    have h := criticalHalfApertureJacobiGammaRecovery_succ p 0
    simpa [criticalHalfApertureJacobiGammaRecovery,
      criticalHalfApertureGammaSewnPascalRay,
      criticalCentralPrimePowerCoefficient] using h

end

end RHTower
