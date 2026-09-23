import GaloisForLFunctions.RHTower.XiTransversePrimeSourceProjectiveTangent

/-!
# The Xi aperture--Poisson valuation-clock shuttle

At prime `p` and valuation depth `e`, the actual transverse Xi source is the Brownian--Laplace
primitive sampled at rate `(e+1) log p`.  Its aperture derivative is the exponential at that rate.
Multiplying by the aperture gives exactly the normalized half-line spectral density of the Poisson
response.  Thus a Poisson scale shuttle is the difference of two Euler-aperture derivatives of the
actual source primitive, not an analogy imposed after the fact.

The two densities have one exact spectral switch.  Above it the source shuttle is strictly
negative, so every sufficiently deep valuation layer and every sufficiently large prime lies in
the same response orientation.  More strongly, summing the entire valuation tower at a fixed
prime produces a Bose aperture factor that is strictly decreasing: infinite valuation fusion
restores a uniform negative orientation at every prime.  Completion across primes and the Gamma
factor into the full Xi quadratic response remains open.
-/

namespace RHTower

noncomputable section

/-- The actual valuation-`e` logarithmic clock at prime `p`. -/
def xiPrimeValuationLaplaceRate (e : ℕ) (p : Nat.Primes) : ℝ :=
  ((e + 1 : ℕ) : ℝ) * Real.log (p : ℝ)

theorem xiPrimeValuationLaplaceRate_pos (e : ℕ) (p : Nat.Primes) :
    0 < xiPrimeValuationLaplaceRate e p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  exact mul_pos (by positivity) (Real.log_pos hp)

/-- Canonical real-aperture continuation of the normalized prime-power Xi source primitive. -/
def xiTransversePrimePowerContinuousLaplacePrimitive
    (a : ℝ) (e : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - Real.exp (-a * xiPrimeValuationLaplaceRate e p)) /
    xiPrimeValuationLaplaceRate e p

/-- At every integral aperture, the real continuation is exactly the existing Brownian--Laplace
sample of the normalized actual Xi transverse prime-power source. -/
theorem xiTransversePrimePowerContinuousLaplacePrimitive_natCast
    (a e : ℕ) (p : Nat.Primes) :
    (xiTransversePrimePowerContinuousLaplacePrimitive (a : ℝ) e p : ℂ) =
      xiTransversePrimePowerBrownianLaplaceSample a e p := by
  have hr := xiPrimeValuationLaplaceRate_pos e p
  rw [xiTransversePrimePowerBrownianLaplaceSample]
  change (xiTransversePrimePowerContinuousLaplacePrimitive (a : ℝ) e p : ℂ) =
    ∫ t : ℝ in 0..(a : ℝ),
      Complex.exp (-((xiPrimeValuationLaplaceRate e p : ℝ) : ℂ) * t)
  rw [intervalIntegral_cexp_neg_rate hr]
  unfold xiTransversePrimePowerContinuousLaplacePrimitive
  push_cast
  congr 2
  ring_nf

/-- Differentiating the actual source primitive exposes its valuation-clock exponential. -/
theorem hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive
    (a : ℝ) (e : ℕ) (p : Nat.Primes) :
    HasDerivAt
      (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p)
      (Real.exp (-a * xiPrimeValuationLaplaceRate e p)) a := by
  let r := xiPrimeValuationLaplaceRate e p
  have hr : 0 < r := xiPrimeValuationLaplaceRate_pos e p
  have harg : HasDerivAt (fun u : ℝ => -u * r) (-r) a := by
    simpa using (hasDerivAt_id a).neg.mul_const r
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u * r))
      (-r * Real.exp (-a * r)) a := by
    simpa [mul_comm] using! (Real.hasDerivAt_exp (-a * r)).comp a harg
  have hnum : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u * r))
      (r * Real.exp (-a * r)) a := by
    simpa using! ((hasDerivAt_const a (1 : ℝ)).sub hexp).congr_deriv (by ring)
  have hquot := hnum.div_const r
  simpa [xiTransversePrimePowerContinuousLaplacePrimitive, r, hr.ne'] using hquot

/-- The normalized half-line spectral density of the Poisson response. -/
def poissonSpectralHalfDensity (a t : ℝ) : ℝ :=
  a * Real.exp (-a * t)

/-- The signed spectral weight transported between two Poisson resolutions. -/
def poissonSpectralScaleShuttle (a b t : ℝ) : ℝ :=
  poissonSpectralHalfDensity b t - poissonSpectralHalfDensity a t

/-- At every actual valuation clock, the Poisson density is the aperture Euler derivative of the
normalized Xi transverse source primitive. -/
theorem poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_sourceEulerDerivative
    (a : ℝ) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralHalfDensity a (xiPrimeValuationLaplaceRate e p) =
      a * deriv
        (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) a := by
  rw [(hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive a e p).deriv]
  rfl

/-- The signed Poisson shuttle is exactly the difference of two source Euler derivatives. -/
theorem poissonSpectralScaleShuttle_xiPrimeValuationLaplaceRate_eq_sourceEulerDerivative
    (a b : ℝ) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p) =
      b * deriv
          (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) b -
        a * deriv
          (fun u : ℝ => xiTransversePrimePowerContinuousLaplacePrimitive u e p) a := by
  rw [(hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive b e p).deriv,
    (hasDerivAt_xiTransversePrimePowerContinuousLaplacePrimitive a e p).deriv]
  rfl

/-- The unique frequency at which two Poisson spectral densities agree. -/
def poissonSpectralScaleSwitch (a b : ℝ) : ℝ :=
  Real.log (b / a) / (b - a)

theorem poissonSpectralScaleSwitch_pos
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < poissonSpectralScaleSwitch a b := by
  have hratio : 1 < b / a := by
    rw [lt_div_iff₀ ha]
    simpa using hab
  exact div_pos (Real.log_pos hratio) (sub_pos.mpr hab)

private theorem poissonSpectralHalfDensity_eq_exp
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    poissonSpectralHalfDensity a t = Real.exp (Real.log a - a * t) := by
  unfold poissonSpectralHalfDensity
  calc
    a * Real.exp (-a * t) = Real.exp (Real.log a) * Real.exp (-a * t) := by
      rw [Real.exp_log ha]
    _ = Real.exp (Real.log a + -a * t) := (Real.exp_add _ _).symm
    _ = Real.exp (Real.log a - a * t) := by
      congr 1
      ring_nf

/-- The scale shuttle is positive precisely below its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_pos_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < poissonSpectralScaleShuttle a b t ↔
      t < poissonSpectralScaleSwitch a b := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_pos,
    poissonSpectralHalfDensity_eq_exp ha,
    poissonSpectralHalfDensity_eq_exp hb,
    Real.exp_lt_exp, poissonSpectralScaleSwitch,
    lt_div_iff₀ (sub_pos.mpr hab), Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- The scale shuttle vanishes precisely at its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_eq_zero_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    poissonSpectralScaleShuttle a b t = 0 ↔
      t = poissonSpectralScaleSwitch a b := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_eq_zero,
    poissonSpectralHalfDensity_eq_exp hb,
    poissonSpectralHalfDensity_eq_exp ha,
    Real.exp_injective.eq_iff, poissonSpectralScaleSwitch,
    eq_div_iff (sub_pos.mpr hab).ne', Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- The scale shuttle is negative precisely above its unique spectral switch. -/
theorem poissonSpectralScaleShuttle_neg_iff
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) :
    poissonSpectralScaleShuttle a b t < 0 ↔
      poissonSpectralScaleSwitch a b < t := by
  have hb : 0 < b := ha.trans hab
  rw [poissonSpectralScaleShuttle, sub_neg,
    poissonSpectralHalfDensity_eq_exp hb,
    poissonSpectralHalfDensity_eq_exp ha,
    Real.exp_lt_exp, poissonSpectralScaleSwitch,
    div_lt_iff₀ (sub_pos.mpr hab), Real.log_div hb.ne' ha.ne']
  constructor <;> intro h <;> nlinarith

/-- At an actual prime-valuation clock, lying above the switch is exactly strict negative source
shuttle orientation. -/
theorem poissonSpectralScaleShuttle_xiPrimeValuationLaplaceRate_neg_iff
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p) < 0 ↔
      poissonSpectralScaleSwitch a b < xiPrimeValuationLaplaceRate e p :=
  poissonSpectralScaleShuttle_neg_iff ha hab

/-! ## Infinite valuation fusion -/

/-- The geometric node associated with one prime at aperture `a`. -/
def xiPrimeValuationGeometricNode (a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-a * Real.log (p : ℝ))

theorem xiPrimeValuationGeometricNode_pos (a : ℝ) (p : Nat.Primes) :
    0 < xiPrimeValuationGeometricNode a p := by
  exact Real.exp_pos _

theorem xiPrimeValuationGeometricNode_lt_one
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiPrimeValuationGeometricNode a p < 1 := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  rw [xiPrimeValuationGeometricNode, Real.exp_lt_one_iff]
  have hmul : 0 < a * Real.log (p : ℝ) := mul_pos ha (Real.log_pos hp)
  nlinarith

/-- Each valuation-clock Poisson density is a shifted geometric term. -/
theorem poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_geometric
    (a : ℝ) (e : ℕ) (p : Nat.Primes) :
    poissonSpectralHalfDensity a (xiPrimeValuationLaplaceRate e p) =
      a * xiPrimeValuationGeometricNode a p ^ (e + 1) := by
  unfold poissonSpectralHalfDensity xiPrimeValuationLaplaceRate
    xiPrimeValuationGeometricNode
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    Summable (fun e : ℕ =>
      poissonSpectralHalfDensity a (xiPrimeValuationLaplaceRate e p)) := by
  let q := xiPrimeValuationGeometricNode a p
  have hq0 : 0 < q := xiPrimeValuationGeometricNode_pos a p
  have hq1 : q < 1 := xiPrimeValuationGeometricNode_lt_one ha p
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hgeom : Summable (fun e : ℕ => q ^ e) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hshift : Summable (fun e : ℕ => q ^ (e + 1)) := by
    refine (Summable.mul_left q hgeom).congr ?_
    intro e
    rw [pow_succ']
  refine (Summable.mul_left a hshift).congr ?_
  intro e
  rw [poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_geometric]

/-- The complete valuation-depth fusion of the Poisson half-density at one actual prime. -/
def poissonPrimeValuationFusedHalfDensity (a : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ, poissonSpectralHalfDensity a (xiPrimeValuationLaplaceRate e p)

theorem poissonPrimeValuationFusedHalfDensity_eq_geometric
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity a p =
      a * xiPrimeValuationGeometricNode a p *
        (1 - xiPrimeValuationGeometricNode a p)⁻¹ := by
  let q := xiPrimeValuationGeometricNode a p
  have hq0 : 0 < q := xiPrimeValuationGeometricNode_pos a p
  have hq1 : q < 1 := xiPrimeValuationGeometricNode_lt_one ha p
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  rw [poissonPrimeValuationFusedHalfDensity]
  simp_rw [poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate_eq_geometric]
  rw [tsum_mul_left, ← geom_series_mul_shift q hqnorm,
    tsum_geometric_of_norm_lt_one hqnorm]
  simp [q, mul_assoc]

/-- The dimensionless Bose aperture factor exposed by complete valuation fusion. -/
def boseApertureFactor (x : ℝ) : ℝ :=
  x / (Real.exp x - 1)

private theorem boseApertureFactor_hasDerivAt
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseApertureFactor
      ((Real.exp x - 1 - x * Real.exp x) / (Real.exp x - 1) ^ (2 : ℕ)) x := by
  have hden : Real.exp x - 1 ≠ 0 := by
    exact (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  simpa [boseApertureFactor] using!
    (hasDerivAt_id x).div ((Real.hasDerivAt_exp x).sub_const 1) hden

private theorem boseApertureFactor_deriv_neg
    {x : ℝ} (hx : 0 < x) : deriv boseApertureFactor x < 0 := by
  rw [(boseApertureFactor_hasDerivAt hx).deriv]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hlinear : Real.exp x * (1 - x) < 1 := by
    calc
      Real.exp x * (1 - x) < Real.exp x * Real.exp (-x) :=
        mul_lt_mul_of_pos_left (Real.one_sub_lt_exp_neg hx.ne') (Real.exp_pos x)
      _ = 1 := hprod
  have hnum : Real.exp x - 1 - x * Real.exp x < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hnum
    (sq_pos_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)))

/-- The Bose aperture factor is strictly decreasing throughout the physical positive chamber. -/
theorem boseApertureFactor_strictAntiOn_pos :
    StrictAntiOn boseApertureFactor (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (𝕜 := ℝ) 0) ?_ ?_
  · refine ContinuousOn.div continuousOn_id
      (Real.continuous_exp.continuousOn.sub continuousOn_const) ?_
    intro x hx
    exact (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  · intro x hx
    rw [interior_Ioi] at hx
    exact boseApertureFactor_deriv_neg hx

/-- Closed Bose form of the fully fused valuation tower. -/
theorem poissonPrimeValuationFusedHalfDensity_eq_boseApertureFactor
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity a p =
      (Real.log (p : ℝ))⁻¹ *
        boseApertureFactor (a * Real.log (p : ℝ)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hx : 0 < a * Real.log (p : ℝ) := mul_pos ha hlog
  rw [poissonPrimeValuationFusedHalfDensity_eq_geometric ha]
  unfold xiPrimeValuationGeometricNode boseApertureFactor
  rw [show -a * Real.log (p : ℝ) = -(a * Real.log (p : ℝ)) by ring,
    Real.exp_neg]
  field_simp [hlog.ne', (Real.exp_pos (a * Real.log (p : ℝ))).ne',
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne']

/-- Complete valuation fusion of a signed scale shuttle at one prime. -/
def poissonPrimeValuationFusedScaleShuttle
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  poissonPrimeValuationFusedHalfDensity b p -
    poissonPrimeValuationFusedHalfDensity a p

/-- Infinite valuation fusion removes the finite-depth sign mixture: the fully fused refinement is
strictly negative at every actual prime. -/
theorem poissonPrimeValuationFusedScaleShuttle_neg
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : Nat.Primes) :
    poissonPrimeValuationFusedScaleShuttle a b p < 0 := by
  have hb : 0 < b := ha.trans hab
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hxy : a * Real.log (p : ℝ) < b * Real.log (p : ℝ) :=
    mul_lt_mul_of_pos_right hab hlog
  have hanti := boseApertureFactor_strictAntiOn_pos
    (mul_pos ha hlog) (mul_pos hb hlog) hxy
  rw [poissonPrimeValuationFusedScaleShuttle,
    poissonPrimeValuationFusedHalfDensity_eq_boseApertureFactor hb,
    poissonPrimeValuationFusedHalfDensity_eq_boseApertureFactor ha,
    sub_neg]
  exact mul_lt_mul_of_pos_left hanti (inv_pos.mpr hlog)

/-- The sum of the actual prime-valuation shuttles is strictly negative. -/
theorem tsum_poissonSpectralScaleShuttle_xiPrimeValuationLaplaceRate_neg
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : Nat.Primes) :
    (∑' e : ℕ,
      poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p)) < 0 := by
  have hb : 0 < b := ha.trans hab
  rw [show (∑' e : ℕ,
      poissonSpectralScaleShuttle a b (xiPrimeValuationLaplaceRate e p)) =
      poissonPrimeValuationFusedScaleShuttle a b p by
    rw [poissonPrimeValuationFusedScaleShuttle,
      poissonPrimeValuationFusedHalfDensity,
      poissonPrimeValuationFusedHalfDensity]
    simpa [poissonSpectralScaleShuttle] using
      (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate hb p).tsum_sub
        (summable_poissonSpectralHalfDensity_xiPrimeValuationLaplaceRate ha p)]
  exact poissonPrimeValuationFusedScaleShuttle_neg ha hab p

end

end RHTower
