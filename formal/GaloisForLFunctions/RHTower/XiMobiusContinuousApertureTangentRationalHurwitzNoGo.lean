import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureRationalHurwitzNoGo

/-!
# The first continuous Möbius source germ still sees the critical strip

The zero-aperture derivative of the continuous Möbius source diagonal inserts one logarithmic
prime moment.  After applying the normalized rational-Hurwitz reflection energy, it is uniformly
equivalent to the `m=1`, `theta=1` prime-seam energy and hence has the same exact open-strip
summability aperture as every fixed positive source metric.

The module also proves the actual all-prime right-germ limit by dominated convergence.  Thus both
finiteness of the first reflected source tangent and existence of its normalized total limit hold
on every Xi fibre unconditionally; neither is an RH selector.
-/

namespace RHTower

noncomputable section

open Filter

/-- The residual local source factor after extracting the first logarithmic moment of the
unit-damped prime reflection seam. -/
def xiMobiusContinuousApertureTangentLorentzFactor (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  1 / (1 + q) ^ 2 / 8

/-- Uniform positive lower bound for the reflected source-tangent factor. -/
theorem one_div_thirty_two_le_xiMobiusContinuousApertureTangentLorentzFactor
    (p : Nat.Primes) :
    (1 : ℝ) / 32 ≤ xiMobiusContinuousApertureTangentLorentzFactor p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hrecip : (1 : ℝ) / 4 ≤ 1 / (1 + q) ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg (1 - q)]
  rw [xiMobiusContinuousApertureTangentLorentzFactor]
  change (1 : ℝ) / 32 ≤ 1 / (1 + q) ^ 2 / 8
  nlinarith

/-- Uniform upper bound for the reflected source-tangent factor. -/
theorem xiMobiusContinuousApertureTangentLorentzFactor_le_one
    (p : Nat.Primes) :
    xiMobiusContinuousApertureTangentLorentzFactor p ≤ 1 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hrecip : 1 / (1 + q) ^ 2 ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg q]
  rw [xiMobiusContinuousApertureTangentLorentzFactor]
  change 1 / (1 + q) ^ 2 / 8 ≤ (1 : ℝ)
  linarith

/-- The zero-aperture source diagonal derivative applied to the normalized finite-value reflection
energy. -/
def xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy
    (rho : ℂ) (p : Nat.Primes) : ℝ :=
  (xiMobiusPrimeContinuousApertureSlopeTerm p / 2) *
    normalizedScaleSeamEnergy (p : ℕ) rho

/-- On the open strip, the source tangent is literally applied to the rational-Hurwitz
value-reflection energy. -/
theorem xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_rationalHurwitz
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p =
      (xiMobiusPrimeContinuousApertureSlopeTerm p / 2) *
        normalizedRationalHurwitzReflectionEnergy (p : ℕ) rho := by
  rw [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip]

/-- Exact source-tangent/value splice: aperture differentiation inserts precisely the first
logarithmic moment and retains unit power damping. -/
theorem xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_factor
    (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p =
      xiMobiusContinuousApertureTangentLorentzFactor p *
        weightedPrimeClockReflectionLogMomentEnergy 1 1 rho.re p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let L := Real.log (p : ℝ)
  let P : ℝ := p
  have hp0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : q = P⁻¹ := xiTransversePrimeApertureDiskNode_one_eq_inv p
  have hcore : q ^ 2 * P = P⁻¹ := by
    rw [hq]
    field_simp
  rw [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy,
    xiMobiusPrimeContinuousApertureSlopeTerm,
    normalizedScaleSeamEnergy_prime_eq_primeClockReflectionEnergy,
    xiMobiusContinuousApertureTangentLorentzFactor,
    weightedPrimeClockReflectionLogMomentEnergy]
  change (((q / (1 + q)) ^ 2 * L) / 2) *
      (P / 4 * primeClockReflectionEnergy rho.re p) =
    (1 / (1 + q) ^ 2 / 8) *
      (|L| ^ 1 * (P ^ (-1 : ℝ) * primeClockReflectionEnergy rho.re p))
  rw [abs_of_pos hL, pow_one, Real.rpow_neg_one, div_pow]
  calc
    (q ^ 2 / (1 + q) ^ 2 * L / 2) *
        (P / 4 * primeClockReflectionEnergy rho.re p) =
      (1 / (1 + q) ^ 2 / 8) *
        (L * ((q ^ 2 * P) * primeClockReflectionEnergy rho.re p)) := by ring
    _ = _ := by rw [hcore]

theorem xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_nonneg
    (rho : ℂ) (p : Nat.Primes) :
    0 ≤ xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p := by
  rw [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_factor]
  have hfactor : 0 ≤ xiMobiusContinuousApertureTangentLorentzFactor p := by
    linarith [one_div_thirty_two_le_xiMobiusContinuousApertureTangentLorentzFactor p]
  exact mul_nonneg hfactor
    (mul_nonneg (pow_nonneg (abs_nonneg _) 1)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))

/-- Uniform lower comparison with the first logarithmic moment of the unit-damped seam. -/
theorem one_div_thirty_two_mul_weightedLogMomentEnergy_le_tangent
    (rho : ℂ) (p : Nat.Primes) :
    (1 : ℝ) / 32 * weightedPrimeClockReflectionLogMomentEnergy 1 1 rho.re p ≤
      xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p := by
  rw [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_factor]
  exact mul_le_mul_of_nonneg_right
    (one_div_thirty_two_le_xiMobiusContinuousApertureTangentLorentzFactor p)
    (mul_nonneg (pow_nonneg (abs_nonneg _) 1)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))

/-- Uniform upper comparison with the first logarithmic moment of the unit-damped seam. -/
theorem xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_le_weighted
    (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p ≤
      weightedPrimeClockReflectionLogMomentEnergy 1 1 rho.re p := by
  rw [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_factor]
  exact mul_le_of_le_one_left
    (mul_nonneg (pow_nonneg (abs_nonneg _) 1)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))
    (xiMobiusContinuousApertureTangentLorentzFactor_le_one p)

/-- **First source-germ no-go.** The reflected aperture tangent has exactly the open-critical-strip
summability classification. -/
theorem summable_xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_iff
    (rho : ℂ) :
    Summable (xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1 := by
  rw [show xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho = fun p =>
      xiMobiusContinuousApertureTangentLorentzFactor p *
        weightedPrimeClockReflectionLogMomentEnergy 1 1 rho.re p by
    funext p
    exact xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_eq_factor rho p]
  exact summable_mul_weightedPrimeClockReflectionLogMomentEnergy_iff
    1 1 rho.re xiMobiusContinuousApertureTangentLorentzFactor
    (c := (1 : ℝ) / 32) (C := 1)
    (by norm_num)
    one_div_thirty_two_le_xiMobiusContinuousApertureTangentLorentzFactor
    xiMobiusContinuousApertureTangentLorentzFactor_le_one

/-- The total continuous source-diagonal energy after inserting the normalized value reflection. -/
def xiMobiusContinuousApertureTotalNormalizedReflectionEnergy
    (a : ℝ) (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureDiagonal a p *
    normalizedScaleSeamEnergy (p : ℕ) rho

/-- This total is the actual continuous Möbius--Szegő reflection energy at every positive
aperture. -/
theorem xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_eq_tsum_metric
    {a : ℝ} (ha : 0 < a) (rho : ℂ) :
    xiMobiusContinuousApertureTotalNormalizedReflectionEnergy a rho =
      ∑' p : Nat.Primes,
        xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p := by
  apply tsum_congr
  intro p
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy,
    xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_diagonal ha p]

@[simp] theorem xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_zero
    (rho : ℂ) :
    xiMobiusContinuousApertureTotalNormalizedReflectionEnergy 0 rho = 0 := by
  simp [xiMobiusContinuousApertureTotalNormalizedReflectionEnergy]

/-- Total reflected energy of the first source aperture tangent. -/
def xiMobiusContinuousApertureTangentTotalNormalizedReflectionEnergy
    (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p

/-- Pointwise right derivative of the source/value energy at zero aperture. -/
theorem tendsto_xiMobiusPrimeContinuousApertureDiagonalNormalizedReflectionEnergy_div
    (rho : ℂ) (p : Nat.Primes) :
    Tendsto
      (fun a : ℝ =>
        (xiMobiusPrimeContinuousApertureDiagonal a p *
          normalizedScaleSeamEnergy (p : ℕ) rho) / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho p)) := by
  have hslope : Tendsto
      (fun a : ℝ => xiMobiusPrimeContinuousApertureDiagonal a p / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureSlopeTerm p / 2)) := by
    have h :=
      (hasDerivAt_xiMobiusPrimeContinuousApertureDiagonal_zero p).tendsto_slope_zero_right
    simpa [div_eq_inv_mul, mul_comm] using h
  have hscaled := hslope.const_mul (normalizedScaleSeamEnergy (p : ℕ) rho)
  simpa [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- The source slope times the normalized reflection energy dominates every positive-aperture
difference quotient. -/
theorem norm_xiMobiusPrimeContinuousApertureDiagonalNormalizedReflectionEnergy_div_le
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p : Nat.Primes) :
    ‖(xiMobiusPrimeContinuousApertureDiagonal a p *
        normalizedScaleSeamEnergy (p : ℕ) rho) / a‖ ≤
      xiMobiusPrimeContinuousApertureSlopeTerm p *
        normalizedScaleSeamEnergy (p : ℕ) rho := by
  have henergy := normalizedScaleSeamEnergy_nonneg rho (p : ℕ)
  rw [show (xiMobiusPrimeContinuousApertureDiagonal a p *
      normalizedScaleSeamEnergy (p : ℕ) rho) / a =
      (xiMobiusPrimeContinuousApertureDiagonal a p / a) *
        normalizedScaleSeamEnergy (p : ℕ) rho by ring,
    norm_mul]
  simp only [Real.norm_eq_abs, abs_of_nonneg henergy]
  exact mul_le_mul_of_nonneg_right
    (norm_xiMobiusPrimeContinuousApertureDiagonal_div_le_slopeTerm ha p) henergy

/-- **All-prime reflected germ law.** On the open strip, the normalized total continuous source
energy converges to its finite first tangent energy. -/
theorem tendsto_xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_div_nhdsGT_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto
      (fun a : ℝ =>
        xiMobiusContinuousApertureTotalNormalizedReflectionEnergy a rho / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureTangentTotalNormalizedReflectionEnergy rho)) := by
  have htangent : Summable
      (xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho) := by
    apply
      (summable_xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_iff rho).mpr
    exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hsum : Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureSlopeTerm p *
        normalizedScaleSeamEnergy (p : ℕ) rho) := by
    have htwo := htangent.mul_left 2
    exact htwo.congr (fun p => by
      simp only [xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy]
      ring)
  have hpoint (p : Nat.Primes) :=
    tendsto_xiMobiusPrimeContinuousApertureDiagonalNormalizedReflectionEnergy_div rho p
  have hbound : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ p : Nat.Primes,
        ‖(xiMobiusPrimeContinuousApertureDiagonal a p *
            normalizedScaleSeamEnergy (p : ℕ) rho) / a‖ ≤
          xiMobiusPrimeContinuousApertureSlopeTerm p *
            normalizedScaleSeamEnergy (p : ℕ) rho := by
    filter_upwards [self_mem_nhdsWithin] with a ha p
    exact
      norm_xiMobiusPrimeContinuousApertureDiagonalNormalizedReflectionEnergy_div_le ha rho p
  have hlimit := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa [xiMobiusContinuousApertureTotalNormalizedReflectionEnergy,
    xiMobiusContinuousApertureTangentTotalNormalizedReflectionEnergy,
    tsum_div_const] using hlimit

/-- Every Xi fibre has a summable first reflected source tangent unconditionally. -/
theorem summable_xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_of_xi_zero
    {rho : ℂ} (hzero : xi rho = 0) :
    Summable (xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho) := by
  have hstrip := xi_zero_re_mem_open_unit hzero
  apply
    (summable_xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_iff rho).mpr
  exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- The reflected all-prime source-germ limit holds on every Xi fibre unconditionally. -/
theorem tendsto_xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_of_xi_zero
    {rho : ℂ} (hzero : xi rho = 0) :
    Tendsto
      (fun a : ℝ =>
        xiMobiusContinuousApertureTotalNormalizedReflectionEnergy a rho / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureTangentTotalNormalizedReflectionEnergy rho)) :=
  tendsto_xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_div_nhdsGT_zero
    (xi_zero_re_mem_open_unit hzero)

/-- Global Prop interface for summability of the first reflected source tangent on all Xi fibres. -/
def XiMobiusContinuousApertureTangentReflectionEnergySummable : Prop :=
  ∀ rho : ℂ, xi rho = 0 →
    Summable (xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy rho)

theorem xiMobiusContinuousApertureTangentReflectionEnergySummable :
    XiMobiusContinuousApertureTangentReflectionEnergySummable :=
  fun _ hzero =>
    summable_xiMobiusPrimeContinuousApertureTangentNormalizedReflectionEnergy_of_xi_zero hzero

/-- Global Prop interface for the normalized reflected aperture-germ limit on all Xi fibres. -/
def XiMobiusContinuousApertureReflectedTangentLimit : Prop :=
  ∀ rho : ℂ, xi rho = 0 →
    Tendsto
      (fun a : ℝ =>
        xiMobiusContinuousApertureTotalNormalizedReflectionEnergy a rho / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureTangentTotalNormalizedReflectionEnergy rho))

theorem xiMobiusContinuousApertureReflectedTangentLimit :
    XiMobiusContinuousApertureReflectedTangentLimit :=
  fun _ hzero =>
    tendsto_xiMobiusContinuousApertureTotalNormalizedReflectionEnergy_of_xi_zero hzero

end

end RHTower
