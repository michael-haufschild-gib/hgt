import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkChangesSignOnce
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.HorizonAveragesAndSparseHorizons
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheInversionDefectIsPositive

/-!
# Readings of the sign criterion

The sign of the signed damping work is the cheapest hypothesis the continuation layer has, and it
can be read on each face the corpus owns.

* **The Markov face.**  The same derivative is boundary flux minus jump energy minus density
  forcing, so the sign criterion says exactly that the flux of the arithmetic chain dominates its
  dissipation plus its forcing (`riemannHypothesis_of_flux_ge_jump_add_forcing`).  Dissipation is
  the enemy of backward continuation, and this states the balance it must lose.
* **Sparse horizons.**  The criterion is pointwise in the horizon, and horizon monotonicity fills
  the gaps: checking the sign at dyadic horizons only is enough
  (`riemannHypothesis_of_nonneg_signedWork_dyadic`).
* **Not vacuous.**  The critical energy is strictly positive at every positive damping and every
  horizon, because the first cell is `1 − 1/ζ(1+ε) > 0`
  (`dampedMobiusEnergy_pos`).  So the `√E_T` allowances of the sublinear criteria are genuine, and
  the sign criterion is not asking for a sign of something that vanishes.
-/

open Set Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The Markov face -/

/-- **The sign criterion on the Markov face.**  If the boundary flux of the arithmetic chain
dominates its jump energy plus its density forcing at every horizon and every damping below one
half, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_flux_ge_jump_add_forcing
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T +
          2 * dampedReadout ε *
            (∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean ε n) ≤
        arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_nonneg_signedWork fun T ε hε hε2 => ?_
  have hmarkov := two_mul_signedDampingWork_eq_markov hε T
  have hbal := h T ε hε hε2
  linarith

/-! ## §2. Sparse horizons -/

/-- **The sign only has to be checked at dyadic horizons.**  The energy is monotone in the horizon,
so dyadic admission is admission. -/
theorem riemannHypothesis_of_nonneg_signedWork_dyadic
    (h : ∀ (k : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → 0 ≤ signedDampingWork ε (2 ^ k)) :
    RiemannHypothesis := by
  have hadm : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Admits dampedMobiusEnergy ε := by
    intro ε hε hε2
    obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le (le_refl (1 / 2 : ℝ))
    refine Admits.of_dyadic_horizons (C := max B 0) (dampedMobiusEnergy_mono ε) fun k => ?_
    have hmono := monotoneOn_dampedMobiusEnergy_of_signedWork_nonneg (a := ε) (b := 1 / 2) hε
      (2 ^ k) fun x hx => h k x (lt_of_lt_of_le hε hx.1) hx.2
    have hle := hmono (left_mem_Icc.mpr hε2) (right_mem_Icc.mpr hε2) hε2
    exact hle.trans ((hB (2 ^ k)).trans (le_max_left B 0))
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  have hmin : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  refine ⟨min δ (1 / 2) / 2, by positivity, by linarith [min_le_left δ (1 / 2 : ℝ)], ?_⟩
  exact hadm _ (by positivity) (by linarith [min_le_right δ (1 / 2 : ℝ)])

/-! ## §3. The criterion is not vacuous -/

/-- The first cell of the source is `1 − 1/ζ(1+ε)`, which is strictly positive. -/
theorem pmPowerDampedCenteredDivisorPrefix_one_pos {ε : ℝ} (hε : 0 < ε) :
    0 < pmPowerDampedCenteredDivisorPrefix ε 1 := by
  have hZ : 1 < realZetaSeries (1 + ε) := by
    have hsum := summable_realZetaTerm (s := 1 + ε) (by linarith)
    have htwo : (∑ i ∈ range 2, ((i : ℝ) + 1) ^ (-(1 + ε))) ≤ realZetaSeries (1 + ε) := by
      rw [realZetaSeries]
      exact hsum.sum_le_tsum _ (fun i _ => by positivity)
    have hval : (∑ i ∈ range 2, ((i : ℝ) + 1) ^ (-(1 + ε))) =
        1 + (2 : ℝ) ^ (-(1 + ε)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 + ε)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hval] at htwo
    linarith
  have hdensity : (pmPowerDampedDivisorDensity ε).re = 1 / realZetaSeries (1 + ε) :=
    pmPowerDampedDivisorDensity_re_eq hε
  have hlt : (pmPowerDampedDivisorDensity ε).re < 1 := by
    rw [hdensity]
    rw [div_lt_one (by linarith)]
    linarith
  have hcoeff : pmPowerDampedDivisorCoeff ε 1 = 1 := by
    rw [pmPowerDampedDivisorCoeff]
    simp
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  have hIcc : (Finset.Icc 1 1 : Finset ℕ) = {1} := by
    ext n
    rw [Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hIcc, Finset.sum_singleton, hcoeff]
  push_cast
  linarith

/-- **The critical energy is strictly positive.**  So the sublinear allowances `κ √E_T` of the
criteria are genuine and the sign criterion is not a sign of nothing. -/
theorem dampedMobiusEnergy_pos {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    0 < dampedMobiusEnergy ε T := by
  have hone : (1 : ℕ) ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨le_rfl, hT⟩
  have hcell : 0 < pmPowerDampedCenteredDivisorPrefix ε 1 ^ 2 /
      ((1 : ℝ) * ((1 : ℝ) + 1)) := by
    have h := pmPowerDampedCenteredDivisorPrefix_one_pos hε
    positivity
  have hnonneg : ∀ n ∈ Finset.Icc 1 T, 0 ≤ pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) := fun n _ => by positivity
  unfold dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnonneg hone)
  simpa using hcell

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
