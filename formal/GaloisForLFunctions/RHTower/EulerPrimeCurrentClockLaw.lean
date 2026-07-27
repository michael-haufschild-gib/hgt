import GaloisForLFunctions.RHTower.CCMEulerEssentialBoundaryLayerCorrespondence
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence

/-!
# The positive Euler prime-power current as a critical clock law

The von Mangoldt weight `Λ(n)n^{-σ}`, normalized by the positive current
`A(σ) = -ζ′(σ)/ζ(σ)`, is a probability law on the prime powers.  Its rescaled logarithmic clock
`(σ-1)·log n` has characteristic function `A(σ - it(σ-1))/A(σ)`, which is the corpus response
`ccmEulerPrimeCurrentClockResponse`.  Lévy's continuity theorem therefore upgrades the proved
pointwise response limit to weak convergence of the Euler clock to the unit exponential law.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

/-! ### The prime-power mass and its partition function -/

/-- Positive prime-power mass of the von Mangoldt current at inverse temperature `σ`. -/
def eulerPrimeCurrentMass (sigma : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-sigma)

theorem eulerPrimeCurrentMass_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ eulerPrimeCurrentMass sigma n := by
  rw [eulerPrimeCurrentMass]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem summable_eulerPrimeCurrentMass {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerPrimeCurrentMass sigma) :=
  summable_vonMangoldt_rpow hsigma

/-- Partition function of the positive Euler prime-power current. -/
def eulerPrimeCurrentTotal (sigma : ℝ) : ℝ := ∑' n : ℕ, eulerPrimeCurrentMass sigma n

theorem ofReal_eulerPrimeCurrentMass_eq (sigma : ℝ) (n : ℕ) :
    ((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) =
      LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (sigma : ℂ) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerPrimeCurrentMass, LSeries.term]
  · have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    rw [LSeries.term_of_ne_zero hn0, eulerPrimeCurrentMass]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rw [show ((-sigma : ℝ) : ℂ) = -((sigma : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.cpow_neg]
    field_simp
    norm_num

theorem ofReal_eulerPrimeCurrentTotal_eq {sigma : ℝ} (hsigma : 1 < sigma) :
    ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) = infinitePrimeFlux (sigma : ℂ) := by
  have hre : ((sigma : ℂ)).re = sigma := Complex.ofReal_re sigma
  have hmap := Complex.ofRealCLM.map_tsum (summable_eulerPrimeCurrentMass hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  calc ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)
      = ∑' n : ℕ, ((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) := by
        rw [eulerPrimeCurrentTotal]
        exact hmap
    _ = ∑' n : ℕ, LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (sigma : ℂ) n := tsum_congr (ofReal_eulerPrimeCurrentMass_eq sigma)
    _ = infinitePrimeFlux (sigma : ℂ) := by
        rw [infinitePrimeFlux_eq_vonMangoldtLSeries (by rw [hre]; exact hsigma), LSeries]

theorem eulerPrimeCurrentTotal_pos {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < eulerPrimeCurrentTotal sigma := by
  have hterm : 0 < eulerPrimeCurrentMass sigma 2 := by
    rw [eulerPrimeCurrentMass, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : (0 : ℝ) < (2 : ℕ) ^ (-sigma) := by
      have : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
      exact Real.rpow_pos_of_pos this _
    exact mul_pos hlog hpow
  have hle : eulerPrimeCurrentMass sigma 2 ≤ eulerPrimeCurrentTotal sigma :=
    (summable_eulerPrimeCurrentMass hsigma).le_tsum 2
      (fun n _ => eulerPrimeCurrentMass_nonneg sigma n)
  linarith

/-! ### The normalized prime-power law -/

/-- Normalized prime-power probability of the positive Euler current. -/
def eulerPrimeCurrentProbability (sigma : ℝ) (n : ℕ) : ℝ :=
  eulerPrimeCurrentMass sigma n / eulerPrimeCurrentTotal sigma

theorem eulerPrimeCurrentProbability_nonneg {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ eulerPrimeCurrentProbability sigma n :=
  div_nonneg (eulerPrimeCurrentMass_nonneg sigma n)
    (le_of_lt (eulerPrimeCurrentTotal_pos hsigma))

theorem summable_eulerPrimeCurrentProbability {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerPrimeCurrentProbability sigma) :=
  (summable_eulerPrimeCurrentMass hsigma).div_const _

theorem tsum_eulerPrimeCurrentProbability {sigma : ℝ} (hsigma : 1 < sigma) :
    ∑' n : ℕ, eulerPrimeCurrentProbability sigma n = 1 := by
  change (∑' n : ℕ, eulerPrimeCurrentMass sigma n / eulerPrimeCurrentTotal sigma) = 1
  rw [tsum_div_const, ← eulerPrimeCurrentTotal]
  exact div_self (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))

private def eulerPrimeCurrentPMFOf (sigma : ℝ) (hsigma : 1 < sigma) : PMF ℕ := by
  refine ⟨fun n => ENNReal.ofReal (eulerPrimeCurrentProbability sigma n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← ENNReal.toNNReal_one]
  have hsum : HasSum (eulerPrimeCurrentProbability sigma) 1 := by
    rw [← tsum_eulerPrimeCurrentProbability hsigma]
    exact (summable_eulerPrimeCurrentProbability hsigma).hasSum
  simpa using hsum.toNNReal (eulerPrimeCurrentProbability_nonneg hsigma)

/-- The Euler prime-power law, extended harmlessly away from its natural half-plane. -/
def eulerPrimeCurrentPMF (sigma : ℝ) : PMF ℕ :=
  if hsigma : 1 < sigma then eulerPrimeCurrentPMFOf sigma hsigma else PMF.pure 1

theorem eulerPrimeCurrentPMF_toReal {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    (eulerPrimeCurrentPMF sigma n).toReal = eulerPrimeCurrentProbability sigma n := by
  rw [eulerPrimeCurrentPMF, dif_pos hsigma]
  change (ENNReal.ofReal (eulerPrimeCurrentProbability sigma n)).toReal = _
  rw [ENNReal.toReal_ofReal (eulerPrimeCurrentProbability_nonneg hsigma n)]

/-- The Euler prime-power law as a probability measure on its discrete index. -/
def eulerPrimeCurrentIndexProbabilityMeasure (sigma : ℝ) : ProbabilityMeasure ℕ :=
  ⟨(eulerPrimeCurrentPMF sigma).toMeasure, inferInstance⟩

/-- The rescaled logarithmic Euler prime-power clock. -/
def eulerPrimeCurrentClock (sigma : ℝ) (n : ℕ) : ℝ := (sigma - 1) * Real.log n

/-- The Euler prime-power clock as a Borel probability measure. -/
def eulerPrimeCurrentClockProbabilityMeasure (sigma : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (eulerPrimeCurrentIndexProbabilityMeasure sigma)
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (eulerPrimeCurrentClock sigma) (eulerPrimeCurrentPMF sigma).toMeasure)

/-! ### The characteristic function -/

theorem integrable_eulerPrimeCurrentClock_char (sigma t : ℝ) :
    Integrable
      (fun n : ℕ =>
        Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I))
      (eulerPrimeCurrentPMF sigma).toMeasure := by
  refine (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable ?_
  filter_upwards with n
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem charFun_eulerPrimeCurrentClockProbabilityMeasure_eq_tsum
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    charFun (eulerPrimeCurrentClockProbabilityMeasure sigma : Measure ℝ) t =
      ∑' n : ℕ,
        (eulerPrimeCurrentProbability sigma n : ℂ) *
          Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I) := by
  rw [charFun_apply_real]
  unfold eulerPrimeCurrentClockProbabilityMeasure eulerPrimeCurrentIndexProbabilityMeasure
    ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hint : Integrable
      (fun n : ℕ =>
        Complex.exp ((t : ℂ) * (eulerPrimeCurrentClock sigma n : ℂ) * Complex.I))
      (eulerPrimeCurrentPMF sigma).toMeasure := by
    convert integrable_eulerPrimeCurrentClock_char sigma t using 1
    funext n
    push_cast
    rfl
  rw [PMF.integral_eq_tsum _ _ hint]
  apply tsum_congr
  intro n
  rw [eulerPrimeCurrentPMF_toReal hsigma]
  change (eulerPrimeCurrentProbability sigma n : ℂ) * _ = _
  congr 2
  push_cast
  rfl

/-- Every phase term of the clock series is the corresponding von Mangoldt Dirichlet term at the
critical parameter. -/
theorem ofReal_eulerPrimeCurrentMass_mul_phase_eq {sigma : ℝ} (t : ℝ) (n : ℕ) :
    ((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) *
        Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I) =
      LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (ccmEulerPrimeCurrentCriticalParameter sigma t) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerPrimeCurrentMass, LSeries.term]
  · have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn0, ofReal_eulerPrimeCurrentMass_eq sigma n,
      LSeries.term_of_ne_zero hn0]
    have hsplit : ((n : ℕ) : ℂ) ^ (ccmEulerPrimeCurrentCriticalParameter sigma t)
        = ((n : ℕ) : ℂ) ^ ((sigma : ℝ) : ℂ) *
          ((n : ℕ) : ℂ) ^ (-(((t * (sigma - 1) : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.cpow_add _ _ hnC, ccmEulerPrimeCurrentCriticalParameter]
      ring_nf
    have hphase : Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I)
        = (((n : ℕ) : ℂ) ^ (-(((t * (sigma - 1) : ℝ) : ℂ) * Complex.I)))⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg]
      congr 1
      rw [eulerPrimeCurrentClock]
      have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring]
        rw [← Complex.ofReal_log (le_of_lt hnpos)]
      rw [hlog]
      push_cast
      ring
    rw [hsplit, hphase]
    field_simp

/-- **The Euler clock characteristic function is the proved prime-current response.** -/
theorem charFun_eulerPrimeCurrentClockProbabilityMeasure_eq_response
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    charFun (eulerPrimeCurrentClockProbabilityMeasure sigma : Measure ℝ) t =
      ccmEulerPrimeCurrentClockResponse sigma t := by
  have htotal : ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))
  rw [charFun_eulerPrimeCurrentClockProbabilityMeasure_eq_tsum hsigma t]
  have hterm : ∀ n : ℕ,
      (eulerPrimeCurrentProbability sigma n : ℂ) *
          Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I) =
        LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
            (ccmEulerPrimeCurrentCriticalParameter sigma t) n /
          ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) := by
    intro n
    calc
      (eulerPrimeCurrentProbability sigma n : ℂ) *
            Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I) =
          (((eulerPrimeCurrentMass sigma n : ℝ) : ℂ) *
              Complex.exp (((t * eulerPrimeCurrentClock sigma n : ℝ) : ℂ) * Complex.I)) /
            ((eulerPrimeCurrentTotal sigma : ℝ) : ℂ) := by
        rw [eulerPrimeCurrentProbability]
        push_cast
        ring
      _ = _ := by rw [ofReal_eulerPrimeCurrentMass_mul_phase_eq t n]
  rw [tsum_congr hterm, tsum_div_const]
  rw [ccmEulerPrimeCurrentClockResponse_eq_vonMangoldtLSeriesRatio hsigma t,
    ofReal_eulerPrimeCurrentTotal_eq hsigma,
    infinitePrimeFlux_eq_vonMangoldtLSeries (by rw [Complex.ofReal_re]; exact hsigma)]
  simp only [LSeries]

/-- **The positive Euler prime-power current has the unit exponential critical clock law.** -/
theorem tendsto_eulerPrimeCurrentClockProbabilityMeasure :
    Tendsto eulerPrimeCurrentClockProbabilityMeasure (nhdsWithin 1 (Ioi 1))
      (nhds mobiusCriticalExponentialProbabilityMeasure) := by
  rw [tendsto_iff_seq_tendsto]
  intro sigma hsigma
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hresponse := (tendsto_ccmEulerPrimeCurrentClockResponse_eq_exponentialCharFun t).comp hsigma
  refine hresponse.congr' ?_
  have hev : ∀ᶠ k in atTop, 1 < sigma k := by
    have := hsigma self_mem_nhdsWithin
    simpa using this
  filter_upwards [hev] with k hk
  exact (charFun_eulerPrimeCurrentClockProbabilityMeasure_eq_response hk t).symm

end RHTower
