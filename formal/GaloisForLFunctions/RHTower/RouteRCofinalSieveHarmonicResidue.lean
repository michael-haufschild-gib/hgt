import GaloisForLFunctions.RHTower.RouteRCriticalWallOrientedHarmonicQuantization
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope

/-!
# Cofinal sieve recovery of the Route R harmonic residue

Restarting the Euler sieve after every finite prime prefix gives a probability
measure on the remaining primes.  Its expectation of `p * a p` recovers the
coefficient of `1 / p` modulo every summable prime field.  Applied to the
moving first-wall Gamma Bockstein, the recovered coefficient is exactly
`-1`, `0`, or `1` according to orientation.

No divisor criticality or source-flatness premise occurs.  The last theorem
identifies the remaining source obligation with convergence of one explicit
pre-divisor sieve reporter to zero.
-/

open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Restarted cofinal sieve -/

/-- Density remaining after sieving by the first `n` primes of the tail
starting at position `N`. -/
def routeRCofinalSieveDensity
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n,
    (1 - (((e (N + k) : ℕ) : ℝ))⁻¹)

/-- Loss of restarted sieve density at the `n`th tail prime. -/
def routeRCofinalSieveWeight
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) : ℝ :=
  routeRCofinalSieveDensity e N n /
    ((e (N + n) : ℕ) : ℝ)

@[simp]
theorem routeRCofinalSieveDensity_zero
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    routeRCofinalSieveDensity e N 0 = 1 := by
  simp [routeRCofinalSieveDensity]

theorem routeRCofinalSieveDensity_pos
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    0 < routeRCofinalSieveDensity e N n := by
  rw [routeRCofinalSieveDensity]
  refine Finset.prod_pos fun k _ => ?_
  rw [sub_pos, inv_lt_one_iff₀]
  exact Or.inr (one_lt_prime_cast (e (N + k)))

theorem routeRCofinalSieveDensity_le_one
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    routeRCofinalSieveDensity e N n ≤ 1 := by
  rw [routeRCofinalSieveDensity]
  refine Finset.prod_le_one (fun k _ => ?_) fun k _ => ?_
  · exact sub_nonneg.mpr
      (le_of_lt ((inv_lt_one_iff₀).mpr
        (Or.inr (one_lt_prime_cast (e (N + k))))))
  · have hprimePos : 0 < ((e (N + k) : ℕ) : ℝ) := by
      exact_mod_cast (e (N + k)).2.pos
    have hinvPos : 0 < (((e (N + k) : ℕ) : ℝ))⁻¹ := inv_pos.mpr hprimePos
    linarith

theorem routeRCofinalSieveDensity_succ
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    routeRCofinalSieveDensity e N (n + 1) =
      routeRCofinalSieveDensity e N n *
        (1 - (((e (N + n) : ℕ) : ℝ))⁻¹) := by
  rw [routeRCofinalSieveDensity, Finset.prod_range_succ,
    routeRCofinalSieveDensity]

/-- Exact restarted-sieve loss identity. -/
theorem routeRCofinalSieveDensity_sub_succ
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    routeRCofinalSieveDensity e N n -
        routeRCofinalSieveDensity e N (n + 1) =
      routeRCofinalSieveWeight e N n := by
  rw [routeRCofinalSieveDensity_succ, routeRCofinalSieveWeight]
  field_simp
  ring

/-- Finite restarted losses telescope exactly. -/
theorem sum_routeRCofinalSieveWeight
    (e : ℕ ≃ Nat.Primes) (N M : ℕ) :
    ∑ n ∈ Finset.range M, routeRCofinalSieveWeight e N n =
      1 - routeRCofinalSieveDensity e N M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        ← routeRCofinalSieveDensity_sub_succ e N M]
      ring

theorem not_summable_routeRCofinalPrimeReciprocal
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    ¬ Summable (fun n : ℕ =>
      (((e (N + n) : ℕ) : ℝ))⁻¹) := by
  intro htail
  have htail' : Summable (fun n : ℕ =>
      (((e (n + N) : ℕ) : ℝ))⁻¹) := by
    simpa [Nat.add_comm] using htail
  have hfull : Summable (fun n : ℕ =>
      (((e n : ℕ) : ℝ))⁻¹) :=
    (summable_nat_add_iff N).mp htail'
  refine Nat.Primes.not_summable_one_div ?_
  have hprime : Summable (fun p : Nat.Primes =>
      (((p : ℕ) : ℝ))⁻¹) := by
    simpa [Function.comp_def] using
      (e.summable_iff (f := fun p : Nat.Primes =>
        (((p : ℕ) : ℝ))⁻¹)).mp hfull
  simpa [one_div] using hprime

/-- Restarted sieve density vanishes along every cofinal prime tail. -/
theorem tendsto_routeRCofinalSieveDensity_zero
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Tendsto (routeRCofinalSieveDensity e N) atTop (𝓝 0) := by
  have hnonneg : ∀ n : ℕ,
      (0 : ℝ) ≤ (((e (N + n) : ℕ) : ℝ))⁻¹ := fun n => by positivity
  have hdiv : Tendsto
      (fun M => ∑ n ∈ Finset.range M,
        (((e (N + n) : ℕ) : ℝ))⁻¹) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
      (not_summable_routeRCofinalPrimeReciprocal e N)
  have hexp : Tendsto
      (fun M => Real.exp
        (-∑ n ∈ Finset.range M,
          (((e (N + n) : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  refine squeeze_zero
    (fun M => (routeRCofinalSieveDensity_pos e N M).le)
    (fun M => ?_) hexp
  rw [routeRCofinalSieveDensity, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun n _ => ?_) (fun n _ => ?_)
  · have hinvLt : (((e (N + n) : ℕ) : ℝ))⁻¹ < 1 :=
      (inv_lt_one_iff₀).mpr (Or.inr (one_lt_prime_cast (e (N + n))))
    linarith
  · linarith [Real.add_one_le_exp
      (-(((e (N + n) : ℕ) : ℝ))⁻¹)]

theorem routeRCofinalSieveWeight_pos
    (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    0 < routeRCofinalSieveWeight e N n := by
  rw [routeRCofinalSieveWeight]
  have hprimePos : 0 < ((e (N + n) : ℕ) : ℝ) := by
    exact_mod_cast (e (N + n)).2.pos
  exact div_pos (routeRCofinalSieveDensity_pos e N n) hprimePos

/-- Every restarted tail loss measure has total mass one. -/
theorem hasSum_routeRCofinalSieveWeight
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    HasSum (routeRCofinalSieveWeight e N) 1 := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ routeRCofinalSieveWeight e N n :=
    fun n => (routeRCofinalSieveWeight_pos e N n).le
  have hbound : ∀ M : ℕ,
      ∑ n ∈ Finset.range M, routeRCofinalSieveWeight e N n ≤ 1 := by
    intro M
    rw [sum_routeRCofinalSieveWeight]
    linarith [routeRCofinalSieveDensity_pos e N M]
  have hsummable : Summable (routeRCofinalSieveWeight e N) :=
    summable_of_sum_range_le hnonneg hbound
  refine (hsummable.hasSum_iff_tendsto_nat).mpr ?_
  refine Tendsto.congr
    (fun M => (sum_routeRCofinalSieveWeight e N M).symm) ?_
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_routeRCofinalSieveDensity_zero e N)

theorem tsum_routeRCofinalSieveWeight
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    ∑' n : ℕ, routeRCofinalSieveWeight e N n = 1 :=
  (hasSum_routeRCofinalSieveWeight e N).tsum_eq

/-! ## Coefficient-faithful harmonic reporter -/

/-- Universal complex prime-harmonic field. -/
def routeRPrimeHarmonicField (p : Nat.Primes) : ℂ :=
  ((((p : ℕ) : ℝ))⁻¹ : ℂ)

/-- Restarted sieve expectation of a prime field.  Since the probability
weight is `D / p`, this is the expectation of `p * a p`. -/
def routeRCofinalSieveHarmonicReporter
    (e : ℕ ≃ Nat.Primes) (N : ℕ)
    (a : Nat.Primes → ℂ) : ℂ :=
  ∑' n : ℕ,
    (routeRCofinalSieveDensity e N n : ℂ) * a (e (N + n))

private theorem summable_primeField_along_cofinalTail
    {a : Nat.Primes → ℂ} (ha : Summable a)
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Summable (fun n : ℕ => a (e (N + n))) := by
  have hfull : Summable (fun n : ℕ => a (e n)) := by
    simpa [Function.comp_def] using
      (e.summable_iff (f := a)).mpr ha
  have htail : Summable (fun n : ℕ => a (e (n + N))) :=
    (summable_nat_add_iff N).mpr hfull
  simpa [Nat.add_comm] using htail

private theorem norm_routeRCofinalSieveReporterTerm_le
    (e : ℕ ≃ Nat.Primes) (N n : ℕ)
    (a : Nat.Primes → ℂ) :
    ‖(routeRCofinalSieveDensity e N n : ℂ) * a (e (N + n))‖ ≤
      ‖a (e (N + n))‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (routeRCofinalSieveDensity_pos e N n)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (routeRCofinalSieveDensity_le_one e N n)

theorem summable_routeRCofinalSieveHarmonicReporter_of_summable
    {a : Nat.Primes → ℂ} (ha : Summable a)
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Summable (fun n : ℕ =>
      (routeRCofinalSieveDensity e N n : ℂ) * a (e (N + n))) := by
  have htail := summable_primeField_along_cofinalTail ha e N
  exact Summable.of_norm (Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n => norm_routeRCofinalSieveReporterTerm_le e N n a)
    htail.norm)

/-- Every restarted reporter evaluates the universal harmonic field to one. -/
theorem hasSum_routeRCofinalSieveHarmonicField
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    HasSum (fun n : ℕ =>
      (routeRCofinalSieveDensity e N n : ℂ) *
        routeRPrimeHarmonicField (e (N + n))) 1 := by
  have h := Complex.ofRealCLM.hasSum
    (hasSum_routeRCofinalSieveWeight e N)
  convert h using 1
  · ext n
    simp [routeRPrimeHarmonicField, routeRCofinalSieveWeight,
      div_eq_mul_inv]
  · simp

theorem routeRCofinalSieveHarmonicReporter_harmonic
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    routeRCofinalSieveHarmonicReporter e N routeRPrimeHarmonicField = 1 :=
  (hasSum_routeRCofinalSieveHarmonicField e N).tsum_eq

/-- Summable prime fields vanish under cofinal restarted reporting. -/
theorem norm_routeRCofinalSieveHarmonicReporter_le_tail
    {a : Nat.Primes → ℂ} (ha : Summable a)
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    ‖routeRCofinalSieveHarmonicReporter e N a‖ ≤
      ∑' n : ℕ, ‖a (e (N + n))‖ := by
  have hreport :=
    summable_routeRCofinalSieveHarmonicReporter_of_summable ha e N
  have htail := summable_primeField_along_cofinalTail ha e N
  rw [routeRCofinalSieveHarmonicReporter]
  exact (norm_tsum_le_tsum_norm hreport.norm).trans
    (Summable.tsum_le_tsum
      (fun n => norm_routeRCofinalSieveReporterTerm_le e N n a)
      hreport.norm htail.norm)

theorem tendsto_routeRCofinalSieveHarmonicReporter_zero_of_summable
    {a : Nat.Primes → ℂ} (ha : Summable a)
    (e : ℕ ≃ Nat.Primes) :
    Tendsto (fun N => routeRCofinalSieveHarmonicReporter e N a)
      atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  refine squeeze_zero (fun N => norm_nonneg _)
    (fun N => norm_routeRCofinalSieveHarmonicReporter_le_tail ha e N) ?_
  have hfull : Summable (fun n : ℕ => ‖a (e n)‖) := by
    have hseq : Summable (fun n : ℕ => a (e n)) := by
      simpa [Function.comp_def] using
        (e.summable_iff (f := a)).mpr ha
    exact hseq.norm
  simpa [Nat.add_comm] using
    (tendsto_sum_nat_add (fun n : ℕ => ‖a (e n)‖))

/-- A prime field has harmonic coefficient `c` when subtracting `c / p`
leaves an `ell^1` field. -/
def RouteRPrimeHarmonicAsymptotic
    (a : Nat.Primes → ℂ) (c : ℂ) : Prop :=
  Summable (fun p => a p - c * routeRPrimeHarmonicField p)

theorem routeRCofinalSieveHarmonicReporter_eq_coeff_add_remainder
    {a : Nat.Primes → ℂ} {c : ℂ}
    (h : RouteRPrimeHarmonicAsymptotic a c)
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    routeRCofinalSieveHarmonicReporter e N a =
      c + routeRCofinalSieveHarmonicReporter e N
        (fun p => a p - c * routeRPrimeHarmonicField p) := by
  let b : Nat.Primes → ℂ :=
    fun p => a p - c * routeRPrimeHarmonicField p
  have hb : Summable b := h
  have hh := (hasSum_routeRCofinalSieveHarmonicField e N).mul_left c
  have hbReporter : HasSum
      (fun n : ℕ =>
        (routeRCofinalSieveDensity e N n : ℂ) * b (e (N + n)))
      (routeRCofinalSieveHarmonicReporter e N b) :=
    (summable_routeRCofinalSieveHarmonicReporter_of_summable hb e N).hasSum
  have hadd := hh.add hbReporter
  have hadd' : HasSum
      (fun n : ℕ =>
        c * ((routeRCofinalSieveDensity e N n : ℂ) *
          routeRPrimeHarmonicField (e (N + n))) +
        (routeRCofinalSieveDensity e N n : ℂ) * b (e (N + n)))
      (c + routeRCofinalSieveHarmonicReporter e N b) := by
    simpa using hadd
  have hsum : HasSum
      (fun n : ℕ =>
        (routeRCofinalSieveDensity e N n : ℂ) * a (e (N + n)))
      (c + routeRCofinalSieveHarmonicReporter e N b) := by
    exact hadd'.congr (fun n => by
      dsimp [b]
      ring)
  exact hsum.tsum_eq

/-- **Cofinal sieve coefficient recovery.**  Restarted sieve expectations
recover the unique harmonic coefficient modulo all summable prime fields. -/
theorem tendsto_routeRCofinalSieveHarmonicReporter
    {a : Nat.Primes → ℂ} {c : ℂ}
    (h : RouteRPrimeHarmonicAsymptotic a c)
    (e : ℕ ≃ Nat.Primes) :
    Tendsto (fun N => routeRCofinalSieveHarmonicReporter e N a)
      atTop (𝓝 c) := by
  let b : Nat.Primes → ℂ :=
    fun p => a p - c * routeRPrimeHarmonicField p
  have hb : Summable b := h
  have hzero :=
    tendsto_routeRCofinalSieveHarmonicReporter_zero_of_summable hb e
  have hsum : Tendsto
      (fun N => c + routeRCofinalSieveHarmonicReporter e N b)
      atTop (𝓝 c) := by
    simpa using hzero.const_add c
  exact hsum.congr' (Filter.Eventually.of_forall fun N =>
    (routeRCofinalSieveHarmonicReporter_eq_coeff_add_remainder h e N).symm)

/-- Harmonic coefficient is unique. -/
theorem routeRPrimeHarmonicAsymptotic_unique
    {a : Nat.Primes → ℂ} {c d : ℂ}
    (hc : RouteRPrimeHarmonicAsymptotic a c)
    (hd : RouteRPrimeHarmonicAsymptotic a d) :
    c = d := by
  exact tendsto_nhds_unique
    (tendsto_routeRCofinalSieveHarmonicReporter hc nthPrimeEquiv)
    (tendsto_routeRCofinalSieveHarmonicReporter hd nthPrimeEquiv)

/-! ## Route R critical-wall residue -/

/-- Complex prime field of the Gamma Bockstein at its moving first trace wall. -/
def routeRPrimeGammaCriticalWallField
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  (primeGammaCofinalBocksteinCriticalWallCoefficient t p : ℂ)

theorem routeRPrimeGammaCriticalWallAsymptotic_neg_one_of_pos
    {t : ℝ} (ht : 0 < t) :
    RouteRPrimeHarmonicAsymptotic
      (routeRPrimeGammaCriticalWallField t) (-1) := by
  have hreal :=
    summable_criticalWallCoefficient_add_primeHarmonic_of_pos ht
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  refine hcomplex.congr fun p => ?_
  rw [routeRPrimeGammaCriticalWallField, routeRPrimeHarmonicField]
  change
    ((primeGammaCofinalBocksteinCriticalWallCoefficient t p +
      (((p : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = _
  push_cast
  ring

theorem routeRPrimeGammaCriticalWallAsymptotic_one_of_neg
    {t : ℝ} (ht : t < 0) :
    RouteRPrimeHarmonicAsymptotic
      (routeRPrimeGammaCriticalWallField t) 1 := by
  have hreal :=
    summable_criticalWallCoefficient_sub_primeHarmonic_of_neg ht
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  refine hcomplex.congr fun p => ?_
  rw [routeRPrimeGammaCriticalWallField, routeRPrimeHarmonicField]
  change
    ((primeGammaCofinalBocksteinCriticalWallCoefficient t p -
      (((p : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = _
  push_cast
  ring

theorem routeRPrimeGammaCriticalWallAsymptotic_zero :
    RouteRPrimeHarmonicAsymptotic
      (routeRPrimeGammaCriticalWallField 0) 0 := by
  simp [RouteRPrimeHarmonicAsymptotic,
    routeRPrimeGammaCriticalWallField,
    primeGammaCofinalBocksteinCriticalWallCoefficient]

/-- Positive grades have cofinal sieve harmonic residue `-1`. -/
theorem tendsto_routeRPrimeGammaCriticalWallReporter_neg_one_of_pos
    (e : ℕ ≃ Nat.Primes) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun N => routeRCofinalSieveHarmonicReporter e N
        (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 (-1)) :=
  tendsto_routeRCofinalSieveHarmonicReporter
    (routeRPrimeGammaCriticalWallAsymptotic_neg_one_of_pos ht) e

/-- Negative grades have cofinal sieve harmonic residue `+1`. -/
theorem tendsto_routeRPrimeGammaCriticalWallReporter_one_of_neg
    (e : ℕ ≃ Nat.Primes) {t : ℝ} (ht : t < 0) :
    Tendsto
      (fun N => routeRCofinalSieveHarmonicReporter e N
        (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 1) :=
  tendsto_routeRCofinalSieveHarmonicReporter
    (routeRPrimeGammaCriticalWallAsymptotic_one_of_neg ht) e

/-- Neutral grade has zero cofinal sieve harmonic residue. -/
theorem tendsto_routeRPrimeGammaCriticalWallReporter_zero
    (e : ℕ ≃ Nat.Primes) :
    Tendsto
      (fun N => routeRCofinalSieveHarmonicReporter e N
        (routeRPrimeGammaCriticalWallField 0))
      atTop (𝓝 0) :=
  tendsto_routeRCofinalSieveHarmonicReporter
    routeRPrimeGammaCriticalWallAsymptotic_zero e

/-- The explicit source reporter tends to zero exactly at neutral grade. -/
theorem routeRPrimeGammaCriticalWallReporter_zeroLimit_iff
    (e : ℕ ≃ Nat.Primes) (t : ℝ) :
    Tendsto
      (fun N => routeRCofinalSieveHarmonicReporter e N
        (routeRPrimeGammaCriticalWallField t))
      atTop (𝓝 0) ↔ t = 0 := by
  constructor
  · intro hzero
    by_contra ht
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hone :=
        tendsto_routeRPrimeGammaCriticalWallReporter_one_of_neg e htneg
      have : (1 : ℂ) = 0 := tendsto_nhds_unique hone hzero
      norm_num at this
    · have hnegone :=
        tendsto_routeRPrimeGammaCriticalWallReporter_neg_one_of_pos e htpos
      have : (-1 : ℂ) = 0 := tendsto_nhds_unique hnegone hzero
      norm_num at this
  · rintro rfl
    exact tendsto_routeRPrimeGammaCriticalWallReporter_zero e

/-- Xi-specialized first-wall field. -/
def routeRPrimeGammaXiCriticalWallField
    (rho : XiDivisorSupport) : Nat.Primes → ℂ :=
  routeRPrimeGammaCriticalWallField (primeDepthBVWoldXiCenteredRate rho)

/-- **Concrete remaining source gate.**  Zero of the restarted-sieve source
reporter at an actual Xi support point is exactly critical-line placement.
This is a reduction theorem, not an assertion of the zero limit. -/
theorem routeRPrimeGammaXiCriticalWallReporter_zeroLimit_iff_re_eq_half
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) :
    Tendsto
      (fun N => routeRCofinalSieveHarmonicReporter e N
        (routeRPrimeGammaXiCriticalWallField rho))
      atTop (𝓝 0) ↔ (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiCriticalWallField,
    routeRPrimeGammaCriticalWallReporter_zeroLimit_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

end

end RHTower
