import GaloisForLFunctions.RHTower.RouteRFirstWallScaleQuantification

/-!
# Neutral-grade and prime-tail limits do not commute

At every fixed restarted Euler tail, the critically damped Gamma wall field tends to zero when
its transverse grade tends to zero.  The convergence follows from one common sieve-probability
majorant.  In the other order, every positive grade has cofinal residue `-1` and every negative
grade has cofinal residue `+1`.

Thus the moving first wall is an oriented blow-up of the neutral grade: its two punctured sides
remain separated at cofinal prime depth even though every fixed-depth readout converges to zero.
This is an exact escape-of-mass/non-uniform-integrability law, not an RH equivalence.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Read the moving Gamma first wall with the restarted cofinal Euler sieve. -/
def routeRFirstWallTailReadout
    (e : ℕ ≃ Nat.Primes) (t : ℝ) (N : ℕ) : ℂ :=
  routeRCofinalSieveHarmonicReporter e N
    (routeRPrimeGammaCriticalWallField t)

private theorem norm_routeRFirstWallTailReadoutTerm_le
    (e : ℕ ≃ Nat.Primes) (t : ℝ) (N n : ℕ) :
    ‖(routeRCofinalSieveDensity e N n : ℂ) *
        routeRPrimeGammaCriticalWallField t (e (N + n))‖ ≤
      routeRCofinalSieveWeight e N n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (routeRCofinalSieveDensity_pos e N n),
    routeRPrimeGammaCriticalWallField, Complex.norm_real, Real.norm_eq_abs,
    abs_criticalWallCoefficient_eq, routeRCofinalSieveWeight]
  have h := routeRFirstWallMass_le_harmonic t (e (N + n))
  rw [primeHarmonicWeight] at h
  exact mul_le_mul_of_nonneg_left h
    (routeRCofinalSieveDensity_pos e N n).le

/-- Every fixed-prime moving-wall coefficient vanishes along every grade path tending to zero. -/
theorem tendsto_primeGammaCofinalBocksteinCriticalWallCoefficient_of_tendsto_zero
    {α : Type*} {l : Filter α} (p : Nat.Primes) {grade : α → ℝ}
    (hgrade : Tendsto grade l (nhds 0)) :
    Tendsto (fun a =>
      primeGammaCofinalBocksteinCriticalWallCoefficient (grade a) p)
      l (nhds 0) := by
  have hexponent : Tendsto (fun a => -2 * |grade a|) l (nhds 0) := by
    simpa using hgrade.abs.const_mul (-2)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hrpow : Tendsto (fun a => (p : ℝ) ^ (-2 * |grade a|))
      l (nhds 1) := by
    have h := (Real.continuousAt_const_rpow hp0).tendsto.comp hexponent
    change Tendsto (fun a => (p : ℝ) ^ (-2 * |grade a|))
      l (nhds ((p : ℝ) ^ (0 : ℝ))) at h
    simpa using h
  have hdefect : Tendsto (fun a => 1 - (p : ℝ) ^ (-2 * |grade a|))
      l (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hrpow)
  have hmass : Tendsto (fun a => routeRFirstWallMass (grade a) p)
      l (nhds 0) := by
    simpa [routeRFirstWallMass] using
      hdefect.const_mul (primeActivationOccupancyFisherDensity p)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.norm_eq_abs,
    abs_criticalWallCoefficient_eq] using hmass

/-- **Fixed-tail neutral continuity.**  For any grade path tending to zero, every fixed restarted
Euler tail readout tends to zero.  One summable sieve weight dominates all grades. -/
theorem tendsto_routeRFirstWallTailReadout_of_grade_tendsto_zero
    {α : Type*} {l : Filter α} (e : ℕ ≃ Nat.Primes) (N : ℕ)
    {grade : α → ℝ} (hgrade : Tendsto grade l (nhds 0)) :
    Tendsto (fun a => routeRFirstWallTailReadout e (grade a) N)
      l (nhds 0) := by
  have hpoint : ∀ n : ℕ, Tendsto
      (fun a =>
        (routeRCofinalSieveDensity e N n : ℂ) *
          routeRPrimeGammaCriticalWallField (grade a) (e (N + n)))
      l (nhds 0) := by
    intro n
    have hcoeff := Complex.ofRealCLM.continuous.tendsto 0 |>.comp
      (tendsto_primeGammaCofinalBocksteinCriticalWallCoefficient_of_tendsto_zero
        (e (N + n)) hgrade)
    simpa [Function.comp_apply, routeRPrimeGammaCriticalWallField] using
      hcoeff.const_mul (routeRCofinalSieveDensity e N n : ℂ)
  have hdom := tendsto_tsum_of_dominated_convergence
    (hasSum_routeRCofinalSieveWeight e N).summable hpoint
    (Filter.Eventually.of_forall fun a n =>
      norm_routeRFirstWallTailReadoutTerm_le e (grade a) N n)
  simpa [routeRFirstWallTailReadout,
    routeRCofinalSieveHarmonicReporter] using hdom

/-- Positive grades tending to the neutral wall. -/
def routeRFirstWallNeutralApproachGrade (m : ℕ) : ℝ :=
  (((m + 1 : ℕ) : ℝ))⁻¹

theorem routeRFirstWallNeutralApproachGrade_pos (m : ℕ) :
    0 < routeRFirstWallNeutralApproachGrade m := by
  rw [routeRFirstWallNeutralApproachGrade]
  positivity

theorem tendsto_routeRFirstWallNeutralApproachGrade_zero :
    Tendsto routeRFirstWallNeutralApproachGrade atTop (nhds 0) := by
  have htop : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact tendsto_inv_atTop_zero.comp htop

/-- At fixed tail start, both oriented approaches to the neutral wall give zero. -/
theorem routeRFirstWallTailReadout_fixedTail_oriented_neutral_limits
    (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Tendsto (fun m => routeRFirstWallTailReadout e
      (routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 0) ∧
    Tendsto (fun m => routeRFirstWallTailReadout e
      (-routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 0) := by
  exact ⟨
    tendsto_routeRFirstWallTailReadout_of_grade_tendsto_zero e N
      tendsto_routeRFirstWallNeutralApproachGrade_zero,
    tendsto_routeRFirstWallTailReadout_of_grade_tendsto_zero e N (by
      simpa using tendsto_routeRFirstWallNeutralApproachGrade_zero.neg)⟩

/-- At fixed positive grade, cofinal prime depth retains the negative unit residue. -/
theorem tendsto_routeRFirstWallTailReadout_positive_cofinal_neg_one
    (e : ℕ ≃ Nat.Primes) (m : ℕ) :
    Tendsto (fun N => routeRFirstWallTailReadout e
      (routeRFirstWallNeutralApproachGrade m) N) atTop (nhds (-1)) := by
  exact tendsto_routeRPrimeGammaCriticalWallReporter_neg_one_of_pos e
    (routeRFirstWallNeutralApproachGrade_pos m)

/-- At fixed negative grade, cofinal prime depth retains the positive unit residue. -/
theorem tendsto_routeRFirstWallTailReadout_negative_cofinal_one
    (e : ℕ ≃ Nat.Primes) (m : ℕ) :
    Tendsto (fun N => routeRFirstWallTailReadout e
      (-routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 1) := by
  exact tendsto_routeRPrimeGammaCriticalWallReporter_one_of_neg e
    (neg_lt_zero.mpr (routeRFirstWallNeutralApproachGrade_pos m))

/-- **Oriented neutral-grade/tail-depth noncommutation.**  Grade-to-zero first gives the neutral
value `0` at every fixed tail.  Prime-depth first gives the two quantized boundary values `-1`
and `+1`.  Hence the moving first wall is an oriented blow-up, and convergence to the neutral
grade is necessarily non-uniform in prime-tail depth. -/
theorem routeRFirstWall_oriented_neutral_tail_limits_do_not_commute
    (e : ℕ ≃ Nat.Primes) :
    (∀ N : ℕ, Tendsto (fun m => routeRFirstWallTailReadout e
      (routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 0)) ∧
    (∀ N : ℕ, Tendsto (fun m => routeRFirstWallTailReadout e
      (-routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 0)) ∧
    (∀ m : ℕ, Tendsto (fun N => routeRFirstWallTailReadout e
      (routeRFirstWallNeutralApproachGrade m) N) atTop (nhds (-1))) ∧
    (∀ m : ℕ, Tendsto (fun N => routeRFirstWallTailReadout e
      (-routeRFirstWallNeutralApproachGrade m) N) atTop (nhds 1)) ∧
    (0 : ℂ) ≠ -1 ∧ (0 : ℂ) ≠ 1 := by
  exact ⟨fun N => (routeRFirstWallTailReadout_fixedTail_oriented_neutral_limits e N).1,
    fun N => (routeRFirstWallTailReadout_fixedTail_oriented_neutral_limits e N).2,
    tendsto_routeRFirstWallTailReadout_positive_cofinal_neg_one e,
    tendsto_routeRFirstWallTailReadout_negative_cofinal_one e, by norm_num, by norm_num⟩

end

end RHTower
