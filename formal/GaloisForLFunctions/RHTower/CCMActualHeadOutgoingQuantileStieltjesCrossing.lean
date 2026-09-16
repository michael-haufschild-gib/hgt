import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileCharacteristicTransport
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileBarycentricDebt
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.CCMSharpRectangularSewing

/-!
# Completed-error crossing law for literal outgoing quantile heads

The outgoing mass clock and the logarithmic time clock select different finite prime sets.  This
file keeps that mismatch instead of discarding it: its two pieces (time-cutoff intrusion and
mass-cutoff overshoot) form an explicit nonnegative crossing credit.  The literal finite outgoing
quadratic moment is therefore exactly completed signed-error action, minus a fixed archimedean
leakage, plus that crossing credit.

This is a source-faithful finite identity.  It neither replaces the completed source by an
absolute bound nor imports a sign from the distinct matched Gamma--Slepian clock.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

private theorem sum_sub_sum_eq_sdiff_cross
    (s t : Finset ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ t, g n) - ∑ n ∈ s, g n =
      (∑ n ∈ t \ s, g n) - ∑ n ∈ s \ t, g n := by
  have ht := Finset.sum_sdiff_eq_sub (f := g)
    (Finset.inter_subset_right : s ∩ t ⊆ t)
  have hs := Finset.sum_sdiff_eq_sub (f := g)
    (Finset.inter_subset_left : s ∩ t ⊆ s)
  rw [Finset.sdiff_inter_self_right] at ht
  rw [Finset.sdiff_inter_self_left] at hs
  linarith

private theorem criticalMellinStieltjesPairing_quadraticTimeCutoff
    {H : ℝ} (hH : 0 ≤ H) :
    criticalMellinStieltjesPairing (H / 2)
        (fun h : ℝ => ((H ^ 2 - h ^ 2 : ℝ) : ℂ)) =
      -(∫ h in Ioc (0 : ℝ) H,
        (criticalMellinCompletedError h : ℂ) * ((-2 * h : ℝ) : ℂ)) := by
  have ha : 0 ≤ H / 2 := by linarith
  have hderiv : ∀ x ∈ Icc (0 : ℝ) (2 * (H / 2)),
      HasDerivAt (fun h : ℝ => ((H ^ 2 - h ^ 2 : ℝ) : ℂ))
        ((-2 * x : ℝ) : ℂ) x := by
    intro x hx
    have hr : HasDerivAt (fun h : ℝ => H ^ 2 - h ^ 2) (-2 * x) x := by
      have hpow : HasDerivAt (fun h : ℝ => h ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      simpa using hpow.const_sub (H ^ 2)
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
    simpa only [Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using! hc
  have hint : IntervalIntegrable (fun h : ℝ => ((-2 * h : ℝ) : ℂ)) volume 0
      (2 * (H / 2)) :=
    (by fun_prop : Continuous fun h : ℝ => ((-2 * h : ℝ) : ℂ)).intervalIntegrable _ _
  have hend : ((H ^ 2 - (2 * (H / 2)) ^ 2 : ℝ) : ℂ) = 0 := by
    norm_cast
    ring
  simpa only [show 2 * (H / 2) = H by ring] using
    (criticalMellinStieltjesPairing_integrationByParts ha hderiv hint hend)

/-- Quadratic atom profile relative to a logarithmic cutoff `H`. -/
def ccmOutgoingQuantileQuadraticAtomProfile (H : ℝ) (n : ℕ) : ℝ :=
  criticalMellinAtomWeight n * (H ^ 2 - (Real.log n) ^ 2)

/-- Exact correction induced by crossing from mass cutoff `N` to time cutoff
`⌊exp b_N⌋`.  The first sum is time-cutoff intrusion; the second is mass-cutoff overshoot. -/
def ccmOutgoingQuantileQuadraticCrossingCorrection (N : ℕ) : ℝ :=
  let H := ccmOutgoingPrimeQuantileBoundary N
  let K := Nat.floor (Real.exp H)
  (∑ n ∈ Finset.Icc 2 K \ Finset.range N,
    ccmOutgoingQuantileQuadraticAtomProfile H n) -
    ∑ n ∈ Finset.range N \ Finset.Icc 2 K,
      ccmOutgoingQuantileQuadraticAtomProfile H n

/-- The residual inward archimedean mass after splitting `2 cosh(h/2)` into its two
exponential halves. -/
def ccmOutgoingQuantileQuadraticArchimedeanLeakage (H : ℝ) : ℝ :=
  ∫ h in (0 : ℝ)..H, Real.exp (-h / 2) * (H ^ 2 - h ^ 2)

/-- The inward archimedean contribution has an exact threshold-action form.  In particular,
it is not an independent error term: it is precisely the deterministic baseline
`2 * (1 - exp (-h / 2))` against the quadratic Stieltjes derivative. -/
theorem ccmOutgoingQuantileQuadraticArchimedeanLeakage_eq_thresholdAction (H : ℝ) :
    ccmOutgoingQuantileQuadraticArchimedeanLeakage H =
      2 * (∫ h in (0 : ℝ)..H, h * (2 * (1 - Real.exp (-h / 2)))) := by
  let F : ℝ → ℝ := fun h => H ^ 2 - h ^ 2
  let G : ℝ → ℝ := fun h => 2 * (1 - Real.exp (-h / 2))
  have hFderiv : ∀ x ∈ uIcc (0 : ℝ) H, HasDerivAt F (-2 * x) x := by
    intro x hx
    dsimp only [F]
    have hpow : HasDerivAt (fun h : ℝ => h ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    simpa using hpow.const_sub (H ^ 2)
  have hGderiv : ∀ x ∈ uIcc (0 : ℝ) H, HasDerivAt G (Real.exp (-x / 2)) x := by
    intro x hx
    dsimp only [G]
    have hinner : HasDerivAt (fun h : ℝ => -h / 2) (-(1 / 2 : ℝ)) x := by
      simpa [neg_div] using ((hasDerivAt_id x).neg.div_const (2 : ℝ))
    have hexp : HasDerivAt (fun h : ℝ => Real.exp (-h / 2))
        (-(1 / 2 : ℝ) * Real.exp (-x / 2)) x := by
      change HasDerivAt (Real.exp ∘ fun h : ℝ => -h / 2)
        (-(1 / 2 : ℝ) * Real.exp (-x / 2)) x
      simpa [mul_comm] using (Real.hasDerivAt_exp (-x / 2)).comp x hinner
    simpa [mul_assoc] using (hexp.const_sub 1).const_mul 2
  have hFint : IntervalIntegrable (fun h : ℝ => -2 * h) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ => -2 * h).intervalIntegrable _ _
  have hGint : IntervalIntegrable (fun h : ℝ => Real.exp (-h / 2)) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (-h / 2)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hFderiv hGderiv hFint hGint
  have hFH : F H = 0 := by
    dsimp only [F]
    ring
  have hG0 : G 0 = 0 := by
    dsimp only [G]
    norm_num
  rw [hFH, hG0, zero_mul, mul_zero, sub_zero] at hibp
  have hswap :
      (∫ h in (0 : ℝ)..H, Real.exp (-h / 2) * F h) =
        ∫ h in (0 : ℝ)..H, F h * Real.exp (-h / 2) := by
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  have hscale :
      (∫ h in (0 : ℝ)..H, (-2 * h) * G h) =
        -(2 * ∫ h in (0 : ℝ)..H, h * G h) := by
    calc
      (∫ h in (0 : ℝ)..H, (-2 * h) * G h) =
          ∫ h in (0 : ℝ)..H, (-2) * (h * G h) := by
            apply intervalIntegral.integral_congr
            intro h hh
            ring
      _ = (-2) * ∫ h in (0 : ℝ)..H, h * G h := by
        rw [intervalIntegral.integral_const_mul]
      _ = -(2 * ∫ h in (0 : ℝ)..H, h * G h) := by ring
  unfold ccmOutgoingQuantileQuadraticArchimedeanLeakage
  change (∫ h in (0 : ℝ)..H, Real.exp (-h / 2) * F h) =
    2 * ∫ h in (0 : ℝ)..H, h * G h
  linarith

/-- Signed completed prime--polar action against the literal quadratic time cutoff. -/
def ccmOutgoingQuantileCompletedErrorAction (N : ℕ) : ℝ :=
  let H := ccmOutgoingPrimeQuantileBoundary N
  (-(∫ h in Ioc (0 : ℝ) H,
    (criticalMellinCompletedError h : ℂ) * ((-2 * h : ℝ) : ℂ))).re

/-- Literal completed prime--polar action after exact removal of its deterministic
archimedean threshold.  The prime staircase remains inside this signed integral. -/
def ccmOutgoingQuantileThresholdCenteredCompletedErrorAction (N : ℕ) : ℝ :=
  let H := ccmOutgoingPrimeQuantileBoundary N
  2 * (∫ h in (0 : ℝ)..H,
    h * (criticalMellinCompletedError h - 2 * (1 - Real.exp (-h / 2))))

private theorem criticalMellinCompletedError_intervalIntegrable_zero_to
    {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable criticalMellinCompletedError volume 0 H := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hH]
  rw [show criticalMellinCompletedError = fun s : ℝ =>
      4 * Real.sinh (s / 2) - criticalMellinPrimeMass s by
    funext s
    exact criticalMellinCompletedError_eq_polar_sub_primeMass s]
  apply IntegrableOn.sub
  · exact (continuous_const.mul
      (Real.continuous_sinh.comp
        (continuous_id.div_const 2))).continuousOn.integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
  · exact integrableOn_criticalMellinPrimeMass_Ioc

/-- The complex Stieltjes action is exactly the real signed completed-error moment; no
regularity is imputed to the prime staircase beyond its established local integrability. -/
theorem ccmOutgoingQuantileCompletedErrorAction_eq_realIntervalAction (N : ℕ) :
    ccmOutgoingQuantileCompletedErrorAction N =
      2 * (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        h * criticalMellinCompletedError h) := by
  let H := ccmOutgoingPrimeQuantileBoundary N
  have hH : 0 ≤ H := ccmOutgoingPrimeQuantileBoundary_nonneg N
  have hE : IntervalIntegrable criticalMellinCompletedError volume 0 H :=
    criticalMellinCompletedError_intervalIntegrable_zero_to hH
  have hlinear : ContinuousOn (fun h : ℝ => -2 * h) (uIcc (0 : ℝ) H) :=
    (by fun_prop : Continuous fun h : ℝ => -2 * h).continuousOn
  have hproduct : IntervalIntegrable
      (fun h : ℝ => criticalMellinCompletedError h * (-2 * h)) volume 0 H := by
    simpa only [mul_comm] using hE.continuousOn_mul hlinear
  have hcast := Complex.ofRealCLM.intervalIntegral_comp_comm hproduct
  have hre :
      (∫ h in (0 : ℝ)..H,
        (criticalMellinCompletedError h : ℂ) * ((-2 * h : ℝ) : ℂ)).re =
        ∫ h in (0 : ℝ)..H, criticalMellinCompletedError h * (-2 * h) := by
    simpa [Complex.ofRealCLM_apply, Complex.ofReal_mul] using congrArg Complex.re hcast
  unfold ccmOutgoingQuantileCompletedErrorAction
  change (-(∫ h in Ioc (0 : ℝ) H,
    (criticalMellinCompletedError h : ℂ) * ((-2 * h : ℝ) : ℂ))).re =
      2 * ∫ h in (0 : ℝ)..H, h * criticalMellinCompletedError h
  rw [Complex.neg_re, ← intervalIntegral.integral_of_le hH, hre]
  have hinter :
      (∫ h in (0 : ℝ)..H, criticalMellinCompletedError h * (-2 * h)) =
        ∫ h in (0 : ℝ)..H, (-2) * (h * criticalMellinCompletedError h) := by
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  rw [hinter, intervalIntegral.integral_const_mul]
  ring

/-- Exact threshold-centering of the literal completed action.  This is the finite producer
left after prime--polar cancellation; it is not an estimate on either source separately. -/
theorem ccmOutgoingQuantileCompletedErrorAction_sub_archimedeanLeakage_eq_thresholdCenteredAction
    (N : ℕ) :
    ccmOutgoingQuantileCompletedErrorAction N -
        ccmOutgoingQuantileQuadraticArchimedeanLeakage
          (ccmOutgoingPrimeQuantileBoundary N) =
      ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N := by
  let H := ccmOutgoingPrimeQuantileBoundary N
  have hH : 0 ≤ H := ccmOutgoingPrimeQuantileBoundary_nonneg N
  have hE : IntervalIntegrable criticalMellinCompletedError volume 0 H :=
    criticalMellinCompletedError_intervalIntegrable_zero_to hH
  have hId : ContinuousOn (fun h : ℝ => h) (uIcc (0 : ℝ) H) :=
    continuous_id.continuousOn
  have hsource : IntervalIntegrable
      (fun h : ℝ => h * criticalMellinCompletedError h) volume 0 H := by
    simpa only [mul_comm] using hE.continuousOn_mul hId
  have hbaseline : IntervalIntegrable
      (fun h : ℝ => h * (2 * (1 - Real.exp (-h / 2)))) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ =>
      h * (2 * (1 - Real.exp (-h / 2)))).intervalIntegrable _ _
  rw [ccmOutgoingQuantileCompletedErrorAction_eq_realIntervalAction,
    ccmOutgoingQuantileQuadraticArchimedeanLeakage_eq_thresholdAction]
  unfold ccmOutgoingQuantileThresholdCenteredCompletedErrorAction
  change 2 * (∫ h in (0 : ℝ)..H, h * criticalMellinCompletedError h) -
      2 * ∫ h in (0 : ℝ)..H, h * (2 * (1 - Real.exp (-h / 2))) =
    2 * ∫ h in (0 : ℝ)..H,
      h * (criticalMellinCompletedError h - 2 * (1 - Real.exp (-h / 2)))
  calc
    2 * (∫ h in (0 : ℝ)..H, h * criticalMellinCompletedError h) -
        2 * ∫ h in (0 : ℝ)..H, h * (2 * (1 - Real.exp (-h / 2))) =
        2 * ((∫ h in (0 : ℝ)..H, h * criticalMellinCompletedError h) -
          ∫ h in (0 : ℝ)..H, h * (2 * (1 - Real.exp (-h / 2)))) := by ring
    _ = 2 * ∫ h in (0 : ℝ)..H,
        h * criticalMellinCompletedError h - h * (2 * (1 - Real.exp (-h / 2))) := by
      rw [intervalIntegral.integral_sub hsource hbaseline]
    _ = 2 * ∫ h in (0 : ℝ)..H,
        h * (criticalMellinCompletedError h - 2 * (1 - Real.exp (-h / 2))) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro h hh
      ring

/-- The literal time-clock/mass-clock discrepancy at height `T`: polar mass accumulated to `T`
minus the actual prime mass selected by its integer log-time head. -/
def ccmOutgoingQuantileTerminalMassDiscrepancy (T : ℝ) : ℝ :=
  2 * Real.exp (T / 2) -
    (2 + ccmOutgoingPrimeCumulative (Nat.floor (Real.exp T) + 1))

/-- The threshold-centered source action expressed in the native terminal mass discrepancy. -/
def ccmOutgoingQuantileTerminalMassAction (N : ℕ) : ℝ :=
  let H := ccmOutgoingPrimeQuantileBoundary N
  2 * (∫ h in (0 : ℝ)..H,
    h * ccmOutgoingQuantileTerminalMassDiscrepancy h)

/-- The terminal mass discrepancy is exactly the threshold-centered completed prime--polar
error. -/
theorem ccmOutgoingQuantileTerminalMassDiscrepancy_eq_thresholdCenteredError (T : ℝ) :
    ccmOutgoingQuantileTerminalMassDiscrepancy T =
      criticalMellinCompletedError T - 2 * (1 - Real.exp (-(T / 2))) := by
  exact quantileTerminalMass_eq_completedError_sub_threshold T

/-- Pointwise, the native discrepancy is the oriented polar mass from the actual quantile
boundary of the log-time head to its time endpoint.  Its sign is therefore retained rather than
replaced by an absolute terminal mismatch. -/
theorem ccmOutgoingQuantileTerminalMassDiscrepancy_eq_orientedQuantileTail (T : ℝ) :
    ccmOutgoingQuantileTerminalMassDiscrepancy T =
      ∫ h in ccmOutgoingPrimeQuantileBoundary
        (Nat.floor (Real.exp T) + 1)..T, Real.exp (h / 2) := by
  exact (integral_exp_half_quantileBoundary_to_eq_massMismatch T
    (Nat.floor (Real.exp T) + 1)).symm

/-- **Native mass-clock form of the remaining Route-O action.** The source term is the signed
average of oriented quantile tails across the literal time head. -/
theorem ccmOutgoingQuantileThresholdCenteredCompletedErrorAction_eq_terminalMassAction
    (N : ℕ) :
    ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N =
      ccmOutgoingQuantileTerminalMassAction N := by
  unfold ccmOutgoingQuantileThresholdCenteredCompletedErrorAction
  unfold ccmOutgoingQuantileTerminalMassAction
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro h hh
  change h * (criticalMellinCompletedError h - 2 * (1 - Real.exp (-h / 2))) =
    h * ccmOutgoingQuantileTerminalMassDiscrepancy h
  rw [show -h / 2 = -(h / 2) by ring]
  rw [← ccmOutgoingQuantileTerminalMassDiscrepancy_eq_thresholdCenteredError]

private theorem ccmOutgoingQuantileQuadraticAtomProfile_nonneg_of_le_floor_exp
    {H : ℝ} (hH : 0 ≤ H) {n : ℕ} (hn : n ∈ Finset.Icc 2 (Nat.floor (Real.exp H))) :
    0 ≤ ccmOutgoingQuantileQuadraticAtomProfile H n := by
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnle : (n : ℝ) ≤ Real.exp H :=
    (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hn).2
  have hlog : Real.log n ≤ H := (Real.log_le_iff_le_exp hnpos).mpr hnle
  have hn1 : 1 ≤ n := by omega
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  unfold ccmOutgoingQuantileQuadraticAtomProfile
  exact mul_nonneg (criticalMellinAtomWeight_nonneg n) (by nlinarith)

private theorem ccmOutgoingQuantileQuadraticAtomProfile_nonpos_of_floor_exp_lt
    {H : ℝ} (hH : 0 ≤ H) {n : ℕ} (hn2 : 2 ≤ n)
    (hn : Nat.floor (Real.exp H) < n) :
    ccmOutgoingQuantileQuadraticAtomProfile H n ≤ 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : Real.exp H < n :=
    (Nat.floor_lt (Real.exp_nonneg H)).mp hn
  have hlog : H < Real.log n := by
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_log hnpos]
    exact hexp
  have hn1 : 1 ≤ n := by omega
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  unfold ccmOutgoingQuantileQuadraticAtomProfile
  exact mul_nonpos_of_nonneg_of_nonpos (criticalMellinAtomWeight_nonneg n) (by nlinarith)

/-- Crossing from the literal mass clock to the literal time clock can only improve the
quadratic moment balance: intruding time atoms are nonnegative and overshooting mass atoms are
nonpositive before subtraction. -/
theorem ccmOutgoingQuantileQuadraticCrossingCorrection_nonneg (N : ℕ) :
    0 ≤ ccmOutgoingQuantileQuadraticCrossingCorrection N := by
  let H := ccmOutgoingPrimeQuantileBoundary N
  let K := Nat.floor (Real.exp H)
  let T := Finset.Icc 2 K
  let S := Finset.range N
  let g := ccmOutgoingQuantileQuadraticAtomProfile H
  have hH : 0 ≤ H := ccmOutgoingPrimeQuantileBoundary_nonneg N
  have hT : ∀ n ∈ T \ S, 0 ≤ g n := by
    intro n hn
    exact ccmOutgoingQuantileQuadraticAtomProfile_nonneg_of_le_floor_exp hH
      (Finset.mem_sdiff.mp hn).1
  have hS : ∀ n ∈ S \ T, g n ≤ 0 := by
    intro n hn
    by_cases hsmall : n < 2
    · interval_cases n <;>
        simp [g, ccmOutgoingQuantileQuadraticAtomProfile, criticalMellinAtomWeight]
    · have hn2 : 2 ≤ n := Nat.le_of_not_gt hsmall
      have hnK : K < n := by
        have hnot : ¬ n ≤ K := by
          intro hle
          exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_Icc.mpr ⟨hn2, hle⟩)
        omega
      exact ccmOutgoingQuantileQuadraticAtomProfile_nonpos_of_floor_exp_lt hH hn2 hnK
  have hpos : 0 ≤ ∑ n ∈ T \ S, g n := Finset.sum_nonneg hT
  have hneg : ∑ n ∈ S \ T, g n ≤ 0 := Finset.sum_nonpos hS
  change 0 ≤ (∑ n ∈ T \ S, g n) - ∑ n ∈ S \ T, g n
  linarith

private theorem ccmOutgoingQuantileQuadraticCrossingCorrection_eq_timeAtom_sub_massAtom
    (N : ℕ) :
    ccmOutgoingQuantileQuadraticCrossingCorrection N =
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (ccmOutgoingPrimeQuantileBoundary N))),
        ccmOutgoingQuantileQuadraticAtomProfile (ccmOutgoingPrimeQuantileBoundary N) n) -
      ∑ n ∈ Finset.range N,
        ccmOutgoingQuantileQuadraticAtomProfile (ccmOutgoingPrimeQuantileBoundary N) n := by
  unfold ccmOutgoingQuantileQuadraticCrossingCorrection
  exact (sum_sub_sum_eq_sdiff_cross (Finset.range N)
    (Finset.Icc 2 (Nat.floor (Real.exp (ccmOutgoingPrimeQuantileBoundary N))))
    (ccmOutgoingQuantileQuadraticAtomProfile
      (ccmOutgoingPrimeQuantileBoundary N))).symm

private theorem integral_exp_half_quadraticProfile_eq_polar_sub_leakage
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * (H ^ 2 - h ^ 2)) =
      (∫ h in Ioc (0 : ℝ) H,
        (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))).re -
        ccmOutgoingQuantileQuadraticArchimedeanLeakage H := by
  have hpcont : Continuous (fun h : ℝ =>
      (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))) := by
    fun_prop
  have hpint : Integrable (fun h : ℝ =>
      (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)))
      (volume.restrict (Ioc (0 : ℝ) H)) :=
    hpcont.continuousOn.integrableOn_Icc.mono_set fun h hh => ⟨hh.1.le, hh.2⟩
  have hpRe :
      (∫ h in Ioc (0 : ℝ) H,
        (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))).re =
        ∫ h in (0 : ℝ)..H, 2 * Real.cosh (h / 2) * (H ^ 2 - h ^ 2) := by
    calc
      (∫ h in Ioc (0 : ℝ) H,
          (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))).re =
          ∫ h in Ioc (0 : ℝ) H,
            (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)).re :=
        (integral_re hpint).symm
      _ = ∫ h in (0 : ℝ)..H, 2 * Real.cosh (h / 2) * (H ^ 2 - h ^ 2) := by
        rw [← intervalIntegral.integral_of_le hH]
        apply intervalIntegral.integral_congr
        intro h hh
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        norm_num
        ring
  have hplus : IntervalIntegrable (fun h : ℝ =>
      Real.exp (h / 2) * (H ^ 2 - h ^ 2)) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ =>
      Real.exp (h / 2) * (H ^ 2 - h ^ 2)).intervalIntegrable _ _
  have hminus : IntervalIntegrable (fun h : ℝ =>
      Real.exp (-h / 2) * (H ^ 2 - h ^ 2)) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ =>
      Real.exp (-h / 2) * (H ^ 2 - h ^ 2)).intervalIntegrable _ _
  have hsplit :
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * (H ^ 2 - h ^ 2)) +
        ∫ h in (0 : ℝ)..H, Real.exp (-h / 2) * (H ^ 2 - h ^ 2) =
        ∫ h in (0 : ℝ)..H, 2 * Real.cosh (h / 2) * (H ^ 2 - h ^ 2) := by
    rw [← intervalIntegral.integral_add hplus hminus]
    apply intervalIntegral.integral_congr
    intro h hh
    change Real.exp (h / 2) * (H ^ 2 - h ^ 2) +
      Real.exp (-h / 2) * (H ^ 2 - h ^ 2) =
      2 * Real.cosh (h / 2) * (H ^ 2 - h ^ 2)
    have hneg : -h / 2 = -(h / 2) := by ring
    rw [hneg, Real.cosh_eq]
    ring
  rw [← hpRe] at hsplit
  unfold ccmOutgoingQuantileQuadraticArchimedeanLeakage
  linarith

private theorem outgoingQuantileMoment_eq_integralProfile_sub_atomProfile (N : ℕ) :
    (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        Real.exp (h / 2) * h ^ 2) =
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        Real.exp (h / 2) *
          (ccmOutgoingPrimeQuantileBoundary N ^ 2 - h ^ 2)) -
      ∑ n ∈ Finset.range N,
        ccmOutgoingQuantileQuadraticAtomProfile (ccmOutgoingPrimeQuantileBoundary N) n := by
  let H := ccmOutgoingPrimeQuantileBoundary N
  let P := ccmOutgoingPrimeCumulative N
  have hmass : (∫ h in (0 : ℝ)..H, Real.exp (h / 2)) = P := by
    dsimp only [H, P]
    exact integral_exp_half_zero_to_quantileBoundary N
  have hA : IntervalIntegrable (fun h : ℝ => H ^ 2 * Real.exp (h / 2)) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ => H ^ 2 * Real.exp (h / 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2) * h ^ 2) volume 0 H :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2) * h ^ 2).intervalIntegrable _ _
  have hcont :
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * (H ^ 2 - h ^ 2)) =
        H ^ 2 * P - ∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2 := by
    calc
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * (H ^ 2 - h ^ 2)) =
        ∫ h in (0 : ℝ)..H, H ^ 2 * Real.exp (h / 2) - Real.exp (h / 2) * h ^ 2 := by
          apply intervalIntegral.integral_congr
          intro h hh
          ring
      _ = (∫ h in (0 : ℝ)..H, H ^ 2 * Real.exp (h / 2)) -
          ∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2 :=
        intervalIntegral.integral_sub hA hB
      _ = H ^ 2 * P - ∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2 := by
        rw [intervalIntegral.integral_const_mul, hmass]
  have hatom :
      (∑ n ∈ Finset.range N, ccmOutgoingQuantileQuadraticAtomProfile H n) =
        H ^ 2 * P - ∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n * (Real.log n) ^ 2 := by
    unfold ccmOutgoingQuantileQuadraticAtomProfile
    calc
      (∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n * (H ^ 2 - (Real.log n) ^ 2)) =
          ∑ n ∈ Finset.range N,
            (H ^ 2 * criticalMellinAtomWeight n -
              criticalMellinAtomWeight n * (Real.log n) ^ 2) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = (∑ n ∈ Finset.range N, H ^ 2 * criticalMellinAtomWeight n) -
          ∑ n ∈ Finset.range N,
            criticalMellinAtomWeight n * (Real.log n) ^ 2 := by
          rw [Finset.sum_sub_distrib]
      _ = H ^ 2 * P - ∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n * (Real.log n) ^ 2 := by
          rw [← Finset.mul_sum]
          rfl
  change (∑ n ∈ Finset.range N,
    criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2) =
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * (H ^ 2 - h ^ 2)) -
      ∑ n ∈ Finset.range N, ccmOutgoingQuantileQuadraticAtomProfile H n
  linarith

/-- **Source-faithful crossing law.**  The literal finite outgoing second moment is completed
prime--polar action minus the exact inward archimedean leakage plus a nonnegative clock-crossing
credit. -/
theorem ccmActualHeadOutgoingQuantileMoment_eq_completedErrorCrossingLaw (N : ℕ) :
    let H := ccmOutgoingPrimeQuantileBoundary N
    (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2) =
      ccmOutgoingQuantileCompletedErrorAction N -
        ccmOutgoingQuantileQuadraticArchimedeanLeakage H +
          ccmOutgoingQuantileQuadraticCrossingCorrection N := by
  let H := ccmOutgoingPrimeQuantileBoundary N
  have hH : 0 ≤ H := ccmOutgoingPrimeQuantileBoundary_nonneg N
  have hprofile := outgoingQuantileMoment_eq_integralProfile_sub_atomProfile N
  have hpolar := integral_exp_half_quadraticProfile_eq_polar_sub_leakage hH
  have hcross := ccmOutgoingQuantileQuadraticCrossingCorrection_eq_timeAtom_sub_massAtom N
  have hpairRe :
      (criticalMellinStieltjesPairing (H / 2)
        (fun h : ℝ => ((H ^ 2 - h ^ 2 : ℝ) : ℂ))).re =
        (∫ h in Ioc (0 : ℝ) H,
          (((H ^ 2 - h ^ 2 : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ))).re -
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp H)),
          ccmOutgoingQuantileQuadraticAtomProfile H n := by
    unfold criticalMellinStieltjesPairing
    simp only [show 2 * (H / 2) = H by ring, Complex.sub_re, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    unfold ccmOutgoingQuantileQuadraticAtomProfile
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsource := criticalMellinStieltjesPairing_quadraticTimeCutoff hH
  change (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2) =
      ccmOutgoingQuantileCompletedErrorAction N -
        ccmOutgoingQuantileQuadraticArchimedeanLeakage H +
          ccmOutgoingQuantileQuadraticCrossingCorrection N
  change (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2) = _ at hprofile
  unfold ccmOutgoingQuantileCompletedErrorAction
  rw [hsource] at hpairRe
  linarith

/-- **Threshold-centered crossing law.**  The literal finite outgoing moment is the signed
completed prime--polar residual after its deterministic threshold is removed, plus the favorable
mass-clock/time-clock crossing credit.  Thus neither clock conversion nor archimedean splitting
leaves an unaccounted error. -/
theorem ccmActualHeadOutgoingQuantileMoment_eq_thresholdCenteredCrossingLaw (N : ℕ) :
    let H := ccmOutgoingPrimeQuantileBoundary N
    (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
      (∫ h in (0 : ℝ)..H, Real.exp (h / 2) * h ^ 2) =
      ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N +
        ccmOutgoingQuantileQuadraticCrossingCorrection N := by
  dsimp only
  rw [ccmActualHeadOutgoingQuantileMoment_eq_completedErrorCrossingLaw,
    ccmOutgoingQuantileCompletedErrorAction_sub_archimedeanLeakage_eq_thresholdCenteredAction]

/-- The native terminal-mass action plus its exact clock-crossing credit is identically the
signed barycentric credit minus the unavoidable squared-displacement debt of the same literal
quantile cells.  This is a lawful bridge because both sides use the actual outgoing mass clock. -/
theorem ccmOutgoingQuantileTerminalMassAction_add_crossing_eq_barycentricDebt
    (N : ℕ) :
    ccmOutgoingQuantileTerminalMassAction N +
        ccmOutgoingQuantileQuadraticCrossingCorrection N =
      ccmOutgoingQuantileFiniteBarycentricCredit N -
        ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N := by
  rw [← ccmOutgoingQuantileThresholdCenteredCompletedErrorAction_eq_terminalMassAction,
    ← ccmActualHeadOutgoingQuantileMoment_eq_thresholdCenteredCrossingLaw,
    ccmActualHeadOutgoingQuantileFiniteMomentError_eq_barycentricDebt]

/-- The exact Route-O finite coercivity condition has two equivalent literal forms: the
threshold-centered terminal-mass action with crossing credit is nonnegative exactly when signed
barycentric credit pays the full squared-displacement debt. -/
theorem ccmOutgoingQuantileTerminalMassActionCrossing_nonneg_iff_barycentricDebtPaid
    (N : ℕ) :
    0 ≤ ccmOutgoingQuantileTerminalMassAction N +
        ccmOutgoingQuantileQuadraticCrossingCorrection N ↔
      ccmOutgoingQuantileFiniteQuadraticDisplacementDebt N ≤
        ccmOutgoingQuantileFiniteBarycentricCredit N := by
  rw [ccmOutgoingQuantileTerminalMassAction_add_crossing_eq_barycentricDebt]
  constructor <;> intro h <;> linarith

/-- The threshold-centered completed source alone is a literal lower bound for the finite
outgoing moment.  The comparison preserves prime--polar cancellation; crossing is retained only
through its proved favorable sign. -/
theorem ccmActualHeadOutgoingQuantileMoment_lowerBound_thresholdCenteredCompletedErrorAction
    (N : ℕ) :
    ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N ≤
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) := by
  rw [ccmActualHeadOutgoingQuantileMoment_eq_thresholdCenteredCrossingLaw]
  linarith [ccmOutgoingQuantileQuadraticCrossingCorrection_nonneg N]

/-- Exact finite obstruction in its cancellation-preserving form.  Cofinal control must land on
this threshold-centered signed action (or a stronger source-faithful quantity); generic bounds on
the separate prime and polar terms do not establish this inequality. -/
theorem ccmActualHeadOutgoingQuantileMoment_nonneg_iff_thresholdCenteredActionCrossing_nonneg
    (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) ↔
      0 ≤ ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N +
        ccmOutgoingQuantileQuadraticCrossingCorrection N := by
  rw [ccmActualHeadOutgoingQuantileMoment_eq_thresholdCenteredCrossingLaw]

/-- The completed signed action alone gives a literal lower bound because clock crossing is
favorable rather than an error to be estimated away. -/
theorem ccmActualHeadOutgoingQuantileMoment_lowerBound_completedErrorMinusLeakage (N : ℕ) :
    ccmOutgoingQuantileCompletedErrorAction N -
        ccmOutgoingQuantileQuadraticArchimedeanLeakage
          (ccmOutgoingPrimeQuantileBoundary N) ≤
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) := by
  rw [ccmActualHeadOutgoingQuantileMoment_eq_completedErrorCrossingLaw]
  linarith [ccmOutgoingQuantileQuadraticCrossingCorrection_nonneg N]

/-- Exact finite obstruction: nonnegative literal outgoing curvature is equivalent to the
completed signed source plus crossing credit paying the whole inward archimedean leakage. -/
theorem ccmActualHeadOutgoingQuantileMoment_nonneg_iff_completedErrorCrossingPaysLeakage
    (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.range N,
      criticalMellinAtomWeight n * (Real.log n) ^ 2) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * h ^ 2) ↔
      ccmOutgoingQuantileQuadraticArchimedeanLeakage
          (ccmOutgoingPrimeQuantileBoundary N) ≤
          ccmOutgoingQuantileCompletedErrorAction N +
          ccmOutgoingQuantileQuadraticCrossingCorrection N := by
  rw [ccmActualHeadOutgoingQuantileMoment_eq_completedErrorCrossingLaw]
  constructor <;> intro h <;> linarith

/-- The actual outgoing Fourier curvature is the same completed-error crossing balance, with no
replacement of its mass clock by a time-clock model. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero_eq_completedErrorCrossingLaw
    (N : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N)) 0 =
      4 * Real.pi ^ 2 *
        (ccmOutgoingQuantileCompletedErrorAction N -
          ccmOutgoingQuantileQuadraticArchimedeanLeakage
            (ccmOutgoingPrimeQuantileBoundary N) +
          ccmOutgoingQuantileQuadraticCrossingCorrection N) := by
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero,
    ccmActualHeadOutgoingQuantileMoment_eq_completedErrorCrossingLaw]

/-- The actual outgoing Fourier curvature is the threshold-centered prime--polar action plus
the exact nonnegative crossing credit. -/
theorem ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero_eq_thresholdCenteredCrossingLaw
    (N : ℕ) :
    deriv (deriv (ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol N)) 0 =
      4 * Real.pi ^ 2 *
        (ccmOutgoingQuantileThresholdCenteredCompletedErrorAction N +
          ccmOutgoingQuantileQuadraticCrossingCorrection N) := by
  rw [ccmActualHeadOutgoingQuantileCosinePhaseFiniteSymbol_secondDeriv_zero,
    ccmActualHeadOutgoingQuantileMoment_eq_thresholdCenteredCrossingLaw]

end RHTower
