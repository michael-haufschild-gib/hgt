import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestXiTraceTransport
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedReflectionRigidity
import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementThreshold

/-!
# Singular Hodge graph fracture of the literal Euler prime current

The positive von--Mangoldt current at every finite pole scale already carries
the source-side precursor of the Gamma/Hardy graph norm.  Its pole-scaled
clock is the compact-head variable, while multiplication by `exp(clock)-1`
is exactly the square of the source-forced Hodge scale.  Applying this
singular multiplier to the reflection-odd endpoint character produces a
summable positive prime-power current exactly at zero displacement.

The nonzero case fails on the prime slice: after factorization it dominates
a positive constant times Euler's divergent prime-harmonic series.  Thus
safe scalar endpoint continuation cannot provide Hodge graph landing; the
singular source transport crosses the exponent-one prime-flux abscissa
before the cofinal clock limit.
-/

open Complex Filter MeasureTheory Set ArithmeticFunction

namespace RHTower

noncomputable section

/-- Square of the discrete source Hodge multiplier at finite pole scale. -/
def eulerPrimeCurrentDiscreteHodgeScaleSq (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.exp (eulerPrimeCurrentClock sigma n) - 1

/-- Unsquared reflection-odd endpoint character on the retained prime-power label. -/
def eulerPrimeCurrentReflectedEndpointDifference
    (sigma a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (a * eulerPrimeCurrentClock sigma n) -
    Real.exp (-a * eulerPrimeCurrentClock sigma n)

/-- Positive graph-energy coordinate of the singularly Hodge-weighted Euler current. -/
def eulerPrimeCurrentSingularHodgeGraphEnergy
    (sigma a : ℝ) (n : ℕ) : ℝ :=
  eulerPrimeCurrentProbability sigma n *
    eulerPrimeCurrentDiscreteHodgeScaleSq sigma n *
      eulerPrimeCurrentReflectedEndpointDifference sigma a n ^ 2

theorem eulerPrimeCurrentClock_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ eulerPrimeCurrentClock sigma n := by
  rw [eulerPrimeCurrentClock]
  exact mul_nonneg (sub_nonneg.mpr hsigma.le) (real_log_nat_nonneg n)

/-- The discrete multiplier is literally the square of the continuous Hodge scale
at the source clock. -/
theorem eulerPrimeCurrentDiscreteHodgeScaleSq_eq_hodgeScale_sq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    eulerPrimeCurrentDiscreteHodgeScaleSq sigma n =
      eulerPrimitiveBoundaryHodgeScale
          (eulerPrimeCurrentClock sigma n) ^ 2 := by
  rw [eulerPrimeCurrentDiscreteHodgeScaleSq,
    eulerPrimitiveBoundaryHodgeScale, Real.sq_sqrt]
  exact sub_nonneg.mpr
    (Real.one_le_exp (eulerPrimeCurrentClock_nonneg hsigma n))

/-- The real reflected source coordinate is exactly the difference of the two
literal complex endpoint characters. -/
theorem eulerPrimitiveBoundaryEndpointFeature_reflection_sub
    (sigma a : ℝ) (n : ℕ) :
    eulerPrimitiveBoundaryEndpointFeature sigma ((-a : ℝ) : ℂ) n -
        eulerPrimitiveBoundaryEndpointFeature sigma (a : ℂ) n =
      (eulerPrimeCurrentReflectedEndpointDifference sigma a n : ℝ) := by
  simp only [eulerPrimitiveBoundaryEndpointFeature,
    eulerPrimitiveHorizonMultiplier,
    eulerPrimeCurrentReflectedEndpointDifference,
    eulerPrimeCurrentClock]
  rw [show
      -(((sigma : ℂ) - 1) * ((-a : ℝ) : ℂ)) * (Real.log n : ℂ) =
        ((a * ((sigma - 1) * Real.log n) : ℝ) : ℂ) by
      push_cast
      ring_nf,
    show
      -(((sigma : ℂ) - 1) * (a : ℂ)) * (Real.log n : ℂ) =
        ((-a * ((sigma - 1) * Real.log n) : ℝ) : ℂ) by
      push_cast
      ring_nf,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  rfl

theorem eulerPrimeCurrentSingularHodgeGraphEnergy_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℝ) (n : ℕ) :
    0 ≤ eulerPrimeCurrentSingularHodgeGraphEnergy sigma a n := by
  rw [eulerPrimeCurrentSingularHodgeGraphEnergy]
  exact mul_nonneg
    (mul_nonneg
      (eulerPrimeCurrentProbability_nonneg hsigma n)
      (sub_nonneg.mpr
        (Real.one_le_exp (eulerPrimeCurrentClock_nonneg hsigma n))))
    (sq_nonneg _)

theorem eulerPrimeCurrentReflectedEndpointDifference_neg
    (sigma a : ℝ) (n : ℕ) :
    eulerPrimeCurrentReflectedEndpointDifference sigma (-a) n =
      -eulerPrimeCurrentReflectedEndpointDifference sigma a n := by
  unfold eulerPrimeCurrentReflectedEndpointDifference
  ring_nf

theorem eulerPrimeCurrentSingularHodgeGraphEnergy_neg
    (sigma a : ℝ) (n : ℕ) :
    eulerPrimeCurrentSingularHodgeGraphEnergy sigma (-a) n =
      eulerPrimeCurrentSingularHodgeGraphEnergy sigma a n := by
  unfold eulerPrimeCurrentSingularHodgeGraphEnergy
  rw [eulerPrimeCurrentReflectedEndpointDifference_neg]
  ring_nf

private theorem exp_primeHodge_core
    {sigma a L P : ℝ} (hlog : Real.exp L = P) :
    Real.exp (-sigma * L) * Real.exp ((sigma - 1) * L) *
        Real.exp (a * ((sigma - 1) * L)) ^ 2 =
      P⁻¹ * Real.exp (2 * a * ((sigma - 1) * L)) := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  rw [show
      -sigma * L + (sigma - 1) * L +
          (a * ((sigma - 1) * L) + a * ((sigma - 1) * L)) =
        -L + 2 * a * ((sigma - 1) * L) by ring]
  rw [Real.exp_add, Real.exp_neg, hlog]

/-- Prime-slice factorization.  Hodge size bias cancels the safe `p⁻(sigma-1)`
damping and exposes a Bianchi mass at negative displacement. -/
theorem eulerPrimeCurrentSingularHodgeGraphEnergy_prime_eq
    {sigma a : ℝ} (hsigma : 1 < sigma)
    (p : Nat.Primes) :
    eulerPrimeCurrentSingularHodgeGraphEnergy sigma a p =
      (eulerPrimeCurrentTotal sigma)⁻¹ *
        suzukiRootedBianchiPrimeMassAt (-2 * a * (sigma - 1)) p *
          (1 - Real.exp (-eulerPrimeCurrentClock sigma p)) *
            (1 - Real.exp
              (-2 * a * eulerPrimeCurrentClock sigma p)) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have htotal : eulerPrimeCurrentTotal sigma ≠ 0 :=
    (eulerPrimeCurrentTotal_pos hsigma).ne'
  rw [eulerPrimeCurrentSingularHodgeGraphEnergy,
    eulerPrimeCurrentProbability, eulerPrimeCurrentMass,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop,
    eulerPrimeCurrentDiscreteHodgeScaleSq,
    eulerPrimeCurrentReflectedEndpointDifference,
    suzukiRootedBianchiPrimeMassAt,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop,
    Real.rpow_def_of_pos hp]
  rw [show Real.exp (eulerPrimeCurrentClock sigma p) - 1 =
      Real.exp (eulerPrimeCurrentClock sigma p) *
        (1 - Real.exp (-eulerPrimeCurrentClock sigma p)) by
      rw [mul_sub, mul_one, ← Real.exp_add]
      have hzero :
          eulerPrimeCurrentClock sigma p +
              -eulerPrimeCurrentClock sigma p = 0 := by ring
      rw [hzero, Real.exp_zero],
    show
      Real.exp (a * eulerPrimeCurrentClock sigma p) -
          Real.exp (-a * eulerPrimeCurrentClock sigma p) =
        Real.exp (a * eulerPrimeCurrentClock sigma p) *
          (1 - Real.exp
            (-2 * a * eulerPrimeCurrentClock sigma p)) by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 1
      ring_nf]
  rw [eulerPrimeCurrentClock]
  have hcore := exp_primeHodge_core (sigma := sigma) (a := a)
    (L := Real.log (p : ℝ)) (P := (p : ℝ)) (Real.exp_log hp)
  rw [mul_pow]
  rw [show a * ((sigma - 1) * Real.log (p : ℝ)) =
      a * (Real.log (p : ℝ) * (sigma - 1)) by ring]
  rw [show
      -(-2 * a * (sigma - 1)) * Real.log (p : ℝ) =
        2 * a * ((sigma - 1) * Real.log (p : ℝ)) by ring]
  field_simp [htotal, hp.ne']
  have hcore' :
      Real.exp (-(Real.log (p : ℝ) * sigma)) *
          Real.exp (Real.log (p : ℝ) * (sigma - 1)) *
            Real.exp (Real.log (p : ℝ) * (sigma - 1) * a) ^ 2 *
              (p : ℝ) =
        Real.exp (Real.log (p : ℝ) * (sigma - 1) * a * 2) := by
    rw [show -(Real.log (p : ℝ) * sigma) =
        -sigma * Real.log (p : ℝ) by ring,
      show Real.log (p : ℝ) * (sigma - 1) =
        (sigma - 1) * Real.log (p : ℝ) by ring,
      show (sigma - 1) * Real.log (p : ℝ) * a =
        a * ((sigma - 1) * Real.log (p : ℝ)) by ring,
      hcore]
    field_simp [hp.ne']
  calc
    _ = Real.log (p : ℝ) *
          (1 - Real.exp (-(Real.log (p : ℝ) * (sigma - 1)))) *
          (1 - Real.exp (-(Real.log (p : ℝ) * (sigma - 1) * a * 2))) ^ 2 *
          (Real.exp (-(Real.log (p : ℝ) * sigma)) *
            Real.exp (Real.log (p : ℝ) * (sigma - 1)) *
            Real.exp (Real.log (p : ℝ) * (sigma - 1) * a) ^ 2 *
            (p : ℝ)) := by ring
    _ = _ := by rw [hcore']

private theorem one_sub_exp_neg_clock_two_le
    {sigma : ℝ} (hsigma : 1 < sigma) (p : Nat.Primes) :
    1 - Real.exp (-(sigma - 1) * Real.log 2) ≤
      1 - Real.exp (-eulerPrimeCurrentClock sigma p) := by
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · change 0 < (p : ℝ)
      exact_mod_cast p.prop.pos
    · exact_mod_cast p.prop.two_le
  have heps : 0 ≤ sigma - 1 := sub_nonneg.mpr hsigma.le
  have hmul : (sigma - 1) * Real.log 2 ≤
      eulerPrimeCurrentClock sigma p := by
    rw [eulerPrimeCurrentClock]
    exact mul_le_mul_of_nonneg_left hlog heps
  have hexp : Real.exp (-eulerPrimeCurrentClock sigma p) ≤
      Real.exp (-(sigma - 1) * Real.log 2) := by
    rw [Real.exp_le_exp]
    linarith
  linarith

private theorem one_sub_exp_neg_two_mul_clock_two_le
    {sigma a : ℝ} (hsigma : 1 < sigma) (ha : 0 < a)
    (p : Nat.Primes) :
    1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2)) ≤
      1 - Real.exp (-2 * a * eulerPrimeCurrentClock sigma p) := by
  have hclock : (sigma - 1) * Real.log 2 ≤
      eulerPrimeCurrentClock sigma p := by
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · norm_num
      · change 0 < (p : ℝ)
        exact_mod_cast p.prop.pos
      · exact_mod_cast p.prop.two_le
    rw [eulerPrimeCurrentClock]
    exact mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hsigma.le)
  have hmul : -2 * a * eulerPrimeCurrentClock sigma p ≤
      -2 * a * ((sigma - 1) * Real.log 2) := by
    nlinarith
  exact sub_le_sub_left (Real.exp_le_exp.mpr hmul) 1

private theorem sourceHodgePrimeLowerConstant_pos
    {sigma a : ℝ} (hsigma : 1 < sigma) (ha : 0 < a) :
    0 < (1 - Real.exp (-(sigma - 1) * Real.log 2)) *
        (1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2))) ^ 2 := by
  have heps : 0 < sigma - 1 := sub_pos.mpr hsigma
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfirst : 0 < 1 - Real.exp (-(sigma - 1) * Real.log 2) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hsecond :
      0 < 1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have hprod : 0 < 2 * a * ((sigma - 1) * Real.log 2) := by positivity
    linarith
  positivity

/-- The positive variable Hodge factors are uniformly bounded below on the
whole prime slice by their prime-two values. -/
private theorem sourceHodgePrimeLowerConstant_mul_bianchi_le
    {sigma a : ℝ} (hsigma : 1 < sigma) (ha : 0 < a)
    (p : Nat.Primes) :
    ((1 - Real.exp (-(sigma - 1) * Real.log 2)) *
        (1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2))) ^ 2) *
        suzukiRootedBianchiPrimeMassAt (-2 * a * (sigma - 1)) p ≤
      eulerPrimeCurrentTotal sigma *
        eulerPrimeCurrentSingularHodgeGraphEnergy sigma a p := by
  have hfactor1 := one_sub_exp_neg_clock_two_le hsigma p
  have hfactor2 := one_sub_exp_neg_two_mul_clock_two_le hsigma ha p
  have hfactor1nonneg :
      0 ≤ 1 - Real.exp (-(sigma - 1) * Real.log 2) := by
    apply le_of_lt
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.log_pos one_lt_two]
  have hfactor2nonneg :
      0 ≤ 1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2)) := by
    exact le_of_lt (by
      rw [sub_pos, Real.exp_lt_one_iff]
      have hprod : 0 < 2 * a * ((sigma - 1) * Real.log 2) := by
        positivity
      linarith)
  have hfactor2target :
      0 ≤ 1 - Real.exp (-2 * a * eulerPrimeCurrentClock sigma p) :=
    le_trans hfactor2nonneg hfactor2
  have hfactor1target :
      0 ≤ 1 - Real.exp (-eulerPrimeCurrentClock sigma p) :=
    le_trans hfactor1nonneg hfactor1
  have hsq :
      (1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2))) ^ 2 ≤
        (1 - Real.exp (-2 * a * eulerPrimeCurrentClock sigma p)) ^ 2 :=
    (sq_le_sq₀ hfactor2nonneg hfactor2target).2 hfactor2
  have hmass :
      0 ≤ suzukiRootedBianchiPrimeMassAt (-2 * a * (sigma - 1)) p := by
    rw [suzukiRootedBianchiPrimeMassAt]
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le
  have hproducts :
      (1 - Real.exp (-(sigma - 1) * Real.log 2)) *
          (1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2))) ^ 2 ≤
        (1 - Real.exp (-eulerPrimeCurrentClock sigma p)) *
          (1 - Real.exp (-2 * a * eulerPrimeCurrentClock sigma p)) ^ 2 :=
    mul_le_mul hfactor1 hsq (sq_nonneg _) hfactor1target
  have := mul_le_mul_of_nonneg_right hproducts hmass
  rw [eulerPrimeCurrentSingularHodgeGraphEnergy_prime_eq hsigma]
  calc
    _ ≤ ((1 - Real.exp (-eulerPrimeCurrentClock sigma p)) *
          (1 - Real.exp (-2 * a * eulerPrimeCurrentClock sigma p)) ^ 2) *
          suzukiRootedBianchiPrimeMassAt (-2 * a * (sigma - 1)) p := this
    _ = eulerPrimeCurrentTotal sigma *
          ((eulerPrimeCurrentTotal sigma)⁻¹ *
            suzukiRootedBianchiPrimeMassAt (-2 * a * (sigma - 1)) p *
              (1 - Real.exp (-eulerPrimeCurrentClock sigma p)) *
                (1 - Real.exp
                  (-2 * a * eulerPrimeCurrentClock sigma p)) ^ 2) := by
      field_simp [(eulerPrimeCurrentTotal_pos hsigma).ne']

private theorem not_summable_eulerPrimeCurrentSingularHodgeGraphEnergy_of_pos
    {sigma a : ℝ} (hsigma : 1 < sigma) (ha : 0 < a) :
    ¬ Summable (eulerPrimeCurrentSingularHodgeGraphEnergy sigma a) := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      eulerPrimeCurrentSingularHodgeGraphEnergy sigma a p) :=
    hsum.comp_injective (fun p q hpq => Subtype.ext hpq)
  let c : ℝ :=
    (1 - Real.exp (-(sigma - 1) * Real.log 2)) *
      (1 - Real.exp (-2 * a * ((sigma - 1) * Real.log 2))) ^ 2
  have hc : c ≠ 0 :=
    (sourceHodgePrimeLowerConstant_pos hsigma ha).ne'
  have hscaledEnergy : Summable (fun p : Nat.Primes =>
      eulerPrimeCurrentTotal sigma *
        eulerPrimeCurrentSingularHodgeGraphEnergy sigma a p) :=
    hslice.mul_left _
  have hscaledBianchi : Summable (fun p : Nat.Primes =>
      c * vonMangoldtGammaRenormalizedBoundaryCoordinate
        (-2 * a * (sigma - 1)) p ^ 2) := by
    refine Summable.of_nonneg_of_le
      (f := fun p : Nat.Primes =>
        eulerPrimeCurrentTotal sigma *
          eulerPrimeCurrentSingularHodgeGraphEnergy sigma a p)
      (g := fun p : Nat.Primes =>
        c * vonMangoldtGammaRenormalizedBoundaryCoordinate
          (-2 * a * (sigma - 1)) p ^ 2) ?_ ?_ hscaledEnergy
    · intro p
      exact mul_nonneg
        (le_of_lt (sourceHodgePrimeLowerConstant_pos hsigma ha))
        (sq_nonneg _)
    · intro p
      have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
      have hmass : 0 ≤
          ArithmeticFunction.vonMangoldt p / (p : ℝ) *
            Real.exp
              (-(-2 * a * (sigma - 1)) * Real.log (p : ℝ)) := by
        exact mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
          (Real.exp_pos _).le
      rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hp2,
        Real.sq_sqrt hmass]
      exact sourceHodgePrimeLowerConstant_mul_bianchi_le hsigma ha p
  have hBianchi : Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate
        (-2 * a * (sigma - 1)) p ^ 2) :=
    (summable_mul_left_iff hc).mp hscaledBianchi
  have hpos :=
    (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff
      (-2 * a * (sigma - 1))).1 hBianchi
  nlinarith

/-- **Finite-scale singular Hodge graph fracture.**  At every safe Euler pole
scale, the actual positive prime-power current admits the reflected endpoint
character in the singular Hodge graph domain exactly at zero displacement. -/
theorem summable_eulerPrimeCurrentSingularHodgeGraphEnergy_iff
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℝ) :
    Summable (eulerPrimeCurrentSingularHodgeGraphEnergy sigma a) ↔
      a = 0 := by
  constructor
  · intro hsum
    by_contra ha0
    rcases lt_or_gt_of_ne ha0 with ha | ha
    · have hneg : 0 < -a := neg_pos.mpr ha
      apply not_summable_eulerPrimeCurrentSingularHodgeGraphEnergy_of_pos
        hsigma hneg
      apply hsum.congr
      intro n
      exact (eulerPrimeCurrentSingularHodgeGraphEnergy_neg sigma a n).symm
    · exact
        not_summable_eulerPrimeCurrentSingularHodgeGraphEnergy_of_pos
          hsigma ha hsum
  · rintro rfl
    have hzero :
        eulerPrimeCurrentSingularHodgeGraphEnergy sigma 0 = 0 := by
      funext n
      simp [eulerPrimeCurrentSingularHodgeGraphEnergy,
        eulerPrimeCurrentReflectedEndpointDifference]
    rw [hzero]
    exact summable_zero

/-- Xi-fracture specialization of the literal source graph-domain theorem. -/
theorem summable_eulerPrimeCurrentSingularHodgeGraphEnergy_boundaryFracture_iff
    {sigma : ℝ} (hsigma : 1 < sigma) (rho : ℂ) :
    Summable
        (eulerPrimeCurrentSingularHodgeGraphEnergy sigma
          (xiNearbyPoleDualityAdjunctionFracture rho).re) ↔
      rho.re = 1 / 2 := by
  rw [summable_eulerPrimeCurrentSingularHodgeGraphEnergy_iff hsigma]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

end

end RHTower
