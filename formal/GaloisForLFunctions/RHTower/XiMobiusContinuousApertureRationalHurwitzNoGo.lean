import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.XiMobiusSchurRationalHurwitzLorentzAperture

/-!
# Fixed continuous Möbius apertures all see the critical strip

This module inserts the normalized rational-Hurwitz reflection energy into every fixed positive
member of the continuous Möbius--Szegő source family.  For each `a>0`, the resulting prime energy
is summable exactly when

`rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1`.

Thus changing a fixed positive source aperture does not improve the unit-aperture classification:
every Xi zero belongs to every such Hilbert sector unconditionally.  The comparison constant
degenerates only as `a → 0+`, isolating the non-uniform tangent/contractivity interface which a
genuine RH argument would have to control.
-/

namespace RHTower

noncomputable section

/-- At nonnegative aperture, the continuous source disk node is antitone in its prime. -/
theorem xiMobiusContinuousApertureDiskNode_antitone_prime
    {a : ℝ} (ha : 0 ≤ a) {p r : Nat.Primes}
    (hpr : (p : ℕ) ≤ (r : ℕ)) :
    xiMobiusContinuousApertureDiskNode a r ≤
      xiMobiusContinuousApertureDiskNode a p := by
  rw [xiMobiusContinuousApertureDiskNode,
    xiMobiusContinuousApertureDiskNode]
  apply Real.exp_le_exp.mpr
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hprR : (p : ℝ) ≤ (r : ℝ) := by exact_mod_cast hpr
  have hlog : Real.log (p : ℝ) ≤ Real.log (r : ℝ) :=
    Real.log_le_log hp0 hprR
  nlinarith

/-- The prime-two node is a uniform upper bound for every prime node. -/
theorem xiMobiusContinuousApertureDiskNode_le_primeTwo
    {a : ℝ} (ha : 0 ≤ a) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode a p ≤
      Real.exp (-a * Real.log 2) := by
  rw [xiMobiusContinuousApertureDiskNode]
  apply Real.exp_le_exp.mpr
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp2
  nlinarith

/-- The residual local factor after extracting the unit-damped reflected prime amplitude from the
continuous Möbius source metric. -/
def xiMobiusContinuousApertureLorentzFactor (a : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) / 4

/-- A prime-independent positive lower comparison constant at fixed aperture `a>0`. -/
def xiMobiusContinuousApertureLorentzLower (a : ℝ) : ℝ :=
  (1 - Real.exp (-a * Real.log 2)) / 32

theorem xiMobiusContinuousApertureLorentzLower_pos
    {a : ℝ} (ha : 0 < a) :
    0 < xiMobiusContinuousApertureLorentzLower a := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-a * Real.log 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  rw [xiMobiusContinuousApertureLorentzLower]
  positivity

/-- Aperture one in the continuous family is exactly the canonical Möbius Schur diagonal. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_one_eq_schurDifferenceKernel
    (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric 1 1 p =
      xiMobiusPrimeSchurDifferenceKernel p p := by
  rw [xiMobiusPrimeContinuousApertureSzegoMetric_self (by norm_num),
    xiMobiusPrimeSchurDifferenceKernel_self]
  have hnode : xiMobiusContinuousApertureDiskNode 1 p =
      xiTransversePrimeApertureDiskNode 1 p := by
    simp [xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
  rw [hnode]
  have hden : 1 + xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
    have hq0 := xiTransversePrimeApertureDiskNode_pos 1 p
    linarith
  field_simp [hden]

/-- For each fixed positive aperture, the local factor has a uniform positive lower bound over all
primes.  The bound is intentionally non-uniform as `a → 0+`. -/
theorem xiMobiusContinuousApertureLorentzLower_le_factor
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusContinuousApertureLorentzLower a ≤
      xiMobiusContinuousApertureLorentzFactor a p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let R := Real.exp (-a * Real.log 2)
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hrR : r ≤ R := xiMobiusContinuousApertureDiskNode_le_primeTwo ha.le p
  have hR1 : R < 1 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [show R = Real.exp (-a * Real.log 2) by rfl, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hrecip : (1 : ℝ) / 4 ≤ 1 / (1 + q) ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg (1 - q)]
  have hratio : (1 - R) / 2 ≤ (1 - r) / (1 + r) := by
    have hnum : (1 - R) / 2 ≤ (1 - r) / 2 := by linarith
    have hden : (1 - r) / 2 ≤ (1 - r) / (1 + r) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (by linarith : 0 < 1 + r)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact hnum.trans hden
  have hprod : (1 / 4 : ℝ) * ((1 - R) / 2) ≤
      (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) := by
    exact mul_le_mul hrecip hratio (by positivity) (by positivity)
  rw [xiMobiusContinuousApertureLorentzLower,
    xiMobiusContinuousApertureLorentzFactor]
  change (1 - R) / 32 ≤
    (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) / 4
  calc
    (1 - R) / 32 = ((1 / 4 : ℝ) * ((1 - R) / 2)) / 4 := by ring
    _ ≤ ((1 / (1 + q) ^ 2) * ((1 - r) / (1 + r))) / 4 := by
      nlinarith

/-- The continuous residual factor is at most one. -/
theorem xiMobiusContinuousApertureLorentzFactor_le_one
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusContinuousApertureLorentzFactor a p ≤ 1 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hrecip : 1 / (1 + q) ^ 2 ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg q]
  have hratio : (1 - r) / (1 + r) ≤ (1 : ℝ) := by
    rw [div_le_one (by linarith : 0 < 1 + r)]
    linarith
  have hprod : (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) ≤ 1 := by
    calc
      (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) ≤ 1 * 1 := by
        exact mul_le_mul hrecip hratio (by positivity) (by norm_num)
      _ = 1 := by ring
  rw [xiMobiusContinuousApertureLorentzFactor]
  change (1 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) / 4 ≤ 1
  linarith

/-- The continuous Möbius source metric applied to the normalized reflected finite-value
transfer. -/
def xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy
    (a : ℝ) (rho : ℂ) (p : Nat.Primes) : ℝ :=
  xiMobiusPrimeContinuousApertureSzegoMetric a a p *
    normalizedScaleSeamEnergy (p : ℕ) rho

/-- At aperture one, the continuous reflection energy is the canonical Möbius Schur reflection
energy already classified by the unit-aperture theorem. -/
theorem xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_one_eq_schur
    (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy 1 rho p =
      xiMobiusPrimeSchurNormalizedReflectionEnergy rho p := by
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy,
    xiMobiusPrimeSchurNormalizedReflectionEnergy,
    xiMobiusPrimeContinuousApertureSzegoMetric_one_eq_schurDifferenceKernel]

/-- On the open strip, this is literally the continuous source metric applied to the finite
rational-Hurwitz value-reflection energy. -/
theorem xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_rationalHurwitz
    {a : ℝ} {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p =
      xiMobiusPrimeContinuousApertureSzegoMetric a a p *
        normalizedRationalHurwitzReflectionEnergy (p : ℕ) rho := by
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip]

/-- Exact continuous source/value splice. -/
theorem xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_apertureFactor
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p =
      xiMobiusContinuousApertureLorentzFactor a p *
        weightedPrimeClockReflectionEnergy 1 rho.re p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let P : ℝ := p
  have hp0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hq : q = P⁻¹ := xiTransversePrimeApertureDiskNode_one_eq_inv p
  have hcore : q ^ 2 * P = P⁻¹ := by
    rw [hq]
    field_simp
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy,
    xiMobiusPrimeContinuousApertureSzegoMetric_self ha p,
    normalizedScaleSeamEnergy_prime_eq_primeClockReflectionEnergy,
    xiMobiusContinuousApertureLorentzFactor,
    weightedPrimeClockReflectionEnergy]
  change (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)) *
      (P / 4 * primeClockReflectionEnergy rho.re p) =
    (1 / (1 + q) ^ 2 * ((1 - r) / (1 + r)) / 4) *
      (P ^ (-1 : ℝ) * primeClockReflectionEnergy rho.re p)
  rw [Real.rpow_neg_one, div_pow]
  calc
    (q ^ 2 / (1 + q) ^ 2) * ((1 - r) / (1 + r)) *
        (P / 4 * primeClockReflectionEnergy rho.re p) =
      (1 / (1 + q) ^ 2 * ((1 - r) / (1 + r)) / 4) *
        ((q ^ 2 * P) * primeClockReflectionEnergy rho.re p) := by ring
    _ = _ := by rw [hcore]

theorem xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_nonneg
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p : Nat.Primes) :
    0 ≤ xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p := by
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_apertureFactor ha]
  have hfactor : 0 < xiMobiusContinuousApertureLorentzFactor a p :=
    lt_of_lt_of_le (xiMobiusContinuousApertureLorentzLower_pos ha)
      (xiMobiusContinuousApertureLorentzLower_le_factor ha p)
  exact mul_nonneg hfactor.le
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

/-- Uniform lower comparison, at fixed aperture, with the unit-damped reflected prime amplitude. -/
theorem continuousApertureLower_mul_weightedPrimeClockReflectionEnergy_le
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p : Nat.Primes) :
    xiMobiusContinuousApertureLorentzLower a *
        weightedPrimeClockReflectionEnergy 1 rho.re p ≤
      xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p := by
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_apertureFactor ha]
  exact mul_le_mul_of_nonneg_right
    (xiMobiusContinuousApertureLorentzLower_le_factor ha p)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

/-- Uniform upper comparison with the unit-damped reflected prime amplitude. -/
theorem xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_le_weighted
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho p ≤
      weightedPrimeClockReflectionEnergy 1 rho.re p := by
  rw [xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_apertureFactor ha]
  exact mul_le_of_le_one_left
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
    (xiMobiusContinuousApertureLorentzFactor_le_one ha p)

/-- **Fixed-aperture family no-go.** Every positive continuous Möbius aperture has exactly the
same open-critical-strip summability classification. -/
theorem summable_xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_iff
    {a : ℝ} (ha : 0 < a) (rho : ℂ) :
    Summable (xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1 := by
  rw [show xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho = fun p =>
      xiMobiusContinuousApertureLorentzFactor a p *
        weightedPrimeClockReflectionEnergy 1 rho.re p by
    funext p
    exact xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_eq_apertureFactor ha rho p]
  exact summable_mul_weightedPrimeClockReflectionEnergy_iff
    1 rho.re (xiMobiusContinuousApertureLorentzFactor a)
    (c := xiMobiusContinuousApertureLorentzLower a) (C := 1)
    (xiMobiusContinuousApertureLorentzLower_pos ha)
    (xiMobiusContinuousApertureLorentzLower_le_factor ha)
    (xiMobiusContinuousApertureLorentzFactor_le_one ha)

/-- Every Xi zero belongs to every fixed positive continuous-aperture sector unconditionally. -/
theorem summable_xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_of_xi_zero
    {a : ℝ} (ha : 0 < a) {rho : ℂ} (hzero : xi rho = 0) :
    Summable (xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho) := by
  have hstrip := xi_zero_re_mem_open_unit hzero
  apply (summable_xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_iff ha rho).mpr
  exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- Quantified Prop interface for membership in every fixed positive continuous source metric. -/
def XiMobiusAllPositiveContinuousApertureReflectionEnergySummable : Prop :=
  ∀ a : ℝ, 0 < a → ∀ rho : ℂ, xi rho = 0 →
    Summable (xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy a rho)

/-- The all-positive-aperture membership Prop discharges outright, without RH. -/
theorem xiMobiusAllPositiveContinuousApertureReflectionEnergySummable :
    XiMobiusAllPositiveContinuousApertureReflectionEnergySummable :=
  fun _ ha _ hzero =>
    summable_xiMobiusPrimeContinuousApertureNormalizedReflectionEnergy_of_xi_zero ha hzero

end

end RHTower
