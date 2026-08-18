import GaloisForLFunctions.RHTower.CCMActualHeadGammaWallOutgoingProducer

/-!
# Monotone outgoing-polar transport on actual Gamma heads

Local symmetric mass-matched cells preserve prime normalization but need not cover the outgoing
polar ray without overlaps or gaps.  This module removes that global assembly obstruction by using
the canonical mass coordinate

`X(h) = 2 exp(h/2)`.

If `P_N = sum_(n<N) Lambda(n)/sqrt(n)`, define

`b_N = 2 log(1 + P_N/2)`.

Then `[b_n,b_(n+1)]` are consecutive, monotone cells and

`integral_[b_n,b_(n+1)] exp(h/2) dh = Lambda(n)/sqrt(n)`

exactly.  Thus every finite prime block minus its polar mass is a sum of literal same-head
translation transports, with no prime-gap estimate and no separate absolute prime/polar bound.

The completed endpoint coefficient has a stronger exact interpretation.  For terminal height `T`,
it contributes

`2 E_f(T) + integral_[b_N,T] exp(h/2) (E_f(T)-E_f(h)) dh`.

Consequently the full outgoing prime--polar--Gamma producer is higher Gamma energy, scalar Gamma
reserve, the nonnegative `2 E_f(2a)` endpoint reserve, and only the consecutive oriented transport
cells.  This identity is unconditional on the literal actual head.  It does not sign those
transport cells; it isolates them as the sole remaining RH-bearing current after global coverage
has been solved exactly.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Critical prime mass strictly below index `N`. -/
def ccmOutgoingPrimeCumulative (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, criticalMellinAtomWeight n

/-- Monotone outgoing-polar quantile boundary carrying the prime mass below `N` from height zero. -/
def ccmOutgoingPrimeQuantileBoundary (N : ℕ) : ℝ :=
  2 * Real.log (1 + ccmOutgoingPrimeCumulative N / 2)

theorem ccmOutgoingPrimeCumulative_nonneg (N : ℕ) :
    0 ≤ ccmOutgoingPrimeCumulative N := by
  unfold ccmOutgoingPrimeCumulative
  exact Finset.sum_nonneg fun n hn => criticalMellinAtomWeight_nonneg n

theorem ccmOutgoingPrimeCumulative_succ (N : ℕ) :
    ccmOutgoingPrimeCumulative (N + 1) =
      ccmOutgoingPrimeCumulative N + criticalMellinAtomWeight N := by
  simp [ccmOutgoingPrimeCumulative, Finset.sum_range_succ]

theorem ccmOutgoingPrimeQuantileBoundary_zero :
    ccmOutgoingPrimeQuantileBoundary 0 = 0 := by
  simp [ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative]

theorem exp_half_ccmOutgoingPrimeQuantileBoundary (N : ℕ) :
    Real.exp (ccmOutgoingPrimeQuantileBoundary N / 2) =
      1 + ccmOutgoingPrimeCumulative N / 2 := by
  have hP := ccmOutgoingPrimeCumulative_nonneg N
  have hpos : 0 < 1 + ccmOutgoingPrimeCumulative N / 2 := by linarith
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [show 2 * Real.log (1 + ccmOutgoingPrimeCumulative N / 2) / 2 =
      Real.log (1 + ccmOutgoingPrimeCumulative N / 2) by ring,
    Real.exp_log hpos]

theorem ccmOutgoingPrimeQuantileBoundary_mono_step (N : ℕ) :
    ccmOutgoingPrimeQuantileBoundary N ≤
      ccmOutgoingPrimeQuantileBoundary (N + 1) := by
  have hP := ccmOutgoingPrimeCumulative_nonneg N
  have hw := criticalMellinAtomWeight_nonneg N
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [ccmOutgoingPrimeCumulative_succ]
  gcongr
  linarith

lemma intervalIntegral_exp_half_eq (x y : ℝ) :
    (∫ h in x..y, Real.exp (h / 2)) =
      2 * Real.exp (y / 2) - 2 * Real.exp (x / 2) := by
  let P : ℝ → ℝ := fun h => 2 * Real.exp (h / 2)
  have hderiv : ∀ h ∈ uIcc x y, HasDerivAt P (Real.exp (h / 2)) h := by
    intro h hh
    dsimp only [P]
    apply (((Real.hasDerivAt_exp (h / 2)).comp h
      ((hasDerivAt_id h).div_const 2)).const_mul 2).congr_deriv
    ring
  have hint : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2)) volume x y :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Every consecutive quantile cell has exactly its literal critical von-Mangoldt mass. -/
theorem integral_exp_half_quantileCell_eq_atomWeight (n : ℕ) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1), Real.exp (h / 2)) =
      criticalMellinAtomWeight n := by
  rw [intervalIntegral_exp_half_eq,
    exp_half_ccmOutgoingPrimeQuantileBoundary,
    exp_half_ccmOutgoingPrimeQuantileBoundary,
    ccmOutgoingPrimeCumulative_succ]
  ring

theorem integral_exp_half_zero_to_quantileBoundary (N : ℕ) :
    (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        Real.exp (h / 2)) = ccmOutgoingPrimeCumulative N := by
  rw [intervalIntegral_exp_half_eq,
    exp_half_ccmOutgoingPrimeQuantileBoundary]
  simp only [zero_div, Real.exp_zero]
  ring

/-- Exact partition of outgoing polar defect energy by consecutive prime quantile cells. -/
theorem integral_exp_half_translationDefect_zero_to_quantileBoundary
    (N : ℕ) (f : SoninL2) :
    (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
        Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      ∑ n ∈ Finset.range N,
        ∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f := by
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f
  have hF : Continuous F := by
    dsimp only [F]
    exact (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      ((((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2)
  induction N with
  | zero => simp [ccmOutgoingPrimeQuantileBoundary_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      change (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary (N + 1), F h) = _
      rw [← ih]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable (μ := volume) 0
          (ccmOutgoingPrimeQuantileBoundary N))
        (hF.intervalIntegrable (μ := volume)
          (ccmOutgoingPrimeQuantileBoundary N)
          (ccmOutgoingPrimeQuantileBoundary (N + 1)))).symm

/-- One prime atom minus its monotone polar cell is its literal signed translation transport. -/
theorem primeAtom_sub_quantileCell_eq_translationTransport
    (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect (Real.log n) f -
            ccmActualHeadTranslationDefect h f) := by
  let b := ccmOutgoingPrimeQuantileBoundary
  let E : ℝ → ℝ := fun h => ccmActualHeadTranslationDefect h f
  have hweight : Continuous fun h : ℝ => Real.exp (h / 2) := by fun_prop
  have hE : Continuous E := by
    dsimp only [E]
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E (Real.log n)) volume (b n) (b (n + 1)) :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E h) volume (b n) (b (n + 1)) :=
    (hweight.mul hE).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  have hfirst : (∫ h in b n..b (n + 1),
      Real.exp (h / 2) * E (Real.log n)) =
      criticalMellinAtomWeight n * E (Real.log n) := by
    calc
      _ = E (Real.log n) * ∫ h in b n..b (n + 1), Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  change criticalMellinAtomWeight n * E (Real.log n) -
      (∫ h in b n..b (n + 1), Real.exp (h / 2) * E h) = _
  calc
    _ = (∫ h in b n..b (n + 1), Real.exp (h / 2) * E (Real.log n)) -
        ∫ h in b n..b (n + 1), Real.exp (h / 2) * E h := by rw [hfirst]
    _ = ∫ h in b n..b (n + 1),
        (Real.exp (h / 2) * E (Real.log n) - Real.exp (h / 2) * E h) :=
      (intervalIntegral.integral_sub hconst hvar).symm
    _ = ∫ h in b n..b (n + 1),
        Real.exp (h / 2) * (E (Real.log n) - E h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring

/-- Finite prime block minus its exactly partitioned outgoing polar mass. -/
theorem primeBlock_sub_quantilePolar_eq_sum_translationTransport
    (N : ℕ) (f : SoninL2) :
    (∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f) -
        (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      ∑ n ∈ Finset.range N,
        ∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) *
            (ccmActualHeadTranslationDefect (Real.log n) f -
              ccmActualHeadTranslationDefect h f) := by
  rw [integral_exp_half_translationDefect_zero_to_quantileBoundary]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact primeAtom_sub_quantileCell_eq_translationTransport n f

/-- The terminal polar mass mismatch is exactly the completed endpoint transport coefficient. -/
theorem integral_exp_half_quantileBoundary_to_eq_massMismatch (T : ℝ) (N : ℕ) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2)) =
      2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N) := by
  rw [intervalIntegral_exp_half_eq,
    exp_half_ccmOutgoingPrimeQuantileBoundary]
  ring

theorem endpointMass_sub_polarTail_eq_translationTransport
    (T : ℝ) (N : ℕ) (f : SoninL2) :
    (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) *
          ccmActualHeadTranslationDefect T f -
        (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2) *
          (ccmActualHeadTranslationDefect T f -
            ccmActualHeadTranslationDefect h f) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let E : ℝ → ℝ := fun h => ccmActualHeadTranslationDefect h f
  have hweight : Continuous fun h : ℝ => Real.exp (h / 2) := by fun_prop
  have hE : Continuous E := by
    dsimp only [E]
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E T) volume b T :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E h) volume b T :=
    (hweight.mul hE).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileBoundary_to_eq_massMismatch T N
  have hfirst : (∫ h in b..T, Real.exp (h / 2) * E T) =
      (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * E T := by
    calc
      _ = E T * ∫ h in b..T, Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  change (2 * Real.exp (T / 2) - (2 + ccmOutgoingPrimeCumulative N)) * E T -
      (∫ h in b..T, Real.exp (h / 2) * E h) = _
  calc
    _ = (∫ h in b..T, Real.exp (h / 2) * E T) -
        ∫ h in b..T, Real.exp (h / 2) * E h := by rw [hfirst]
    _ = ∫ h in b..T,
        (Real.exp (h / 2) * E T - Real.exp (h / 2) * E h) :=
      (intervalIntegral.integral_sub hconst hvar).symm
    _ = ∫ h in b..T, Real.exp (h / 2) * (E T - E h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring

/-- **Global monotone-transport producer.** The completed endpoint coefficient supplies a positive
`2 E(T)` reserve, while every remaining prime--polar term is an oriented transport difference on
one exact quantile cell. No overlap, gap, or separate absolute prime/polar estimate remains. -/
theorem completedPrimePolarBlock_eq_twoEndpoint_add_quantileTransports
    (T : ℝ) (N : ℕ) (f : SoninL2) :
    (2 * Real.exp (T / 2) - ccmOutgoingPrimeCumulative N) *
          ccmActualHeadTranslationDefect T f +
        (∑ n ∈ Finset.range N,
          criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f) -
        (∫ h in (0 : ℝ)..T,
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      2 * ccmActualHeadTranslationDefect T f +
        (∑ n ∈ Finset.range N,
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) *
              (ccmActualHeadTranslationDefect (Real.log n) f -
                ccmActualHeadTranslationDefect h f)) +
        (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
          Real.exp (h / 2) *
            (ccmActualHeadTranslationDefect T f -
              ccmActualHeadTranslationDefect h f)) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f
  have hF : Continuous F := by
    dsimp only [F]
    exact (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      ((((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2)
  have hsplit : (∫ h in (0 : ℝ)..T, F h) =
      (∫ h in (0 : ℝ)..b, F h) + ∫ h in b..T, F h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 b)
      (hF.intervalIntegrable (μ := volume) b T)).symm
  have hcells := primeBlock_sub_quantilePolar_eq_sum_translationTransport N f
  have hend := endpointMass_sub_polarTail_eq_translationTransport T N f
  change _ = _
  change (∫ h in (0 : ℝ)..T, F h) = _ at hsplit
  change _ - (∫ h in (0 : ℝ)..b, F h) = _ at hcells
  change _ - (∫ h in b..T, F h) = _ at hend
  linear_combination hcells + hend - hsplit

private theorem sum_range_succ_eq_sum_Icc_two
    (N : ℕ) (F : ℕ → ℝ) (h0 : F 0 = 0) (h1 : F 1 = 0) :
    (∑ n ∈ Finset.range (N + 1), F n) =
      ∑ n ∈ Finset.Icc 2 N, F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hnrange hnnot
    simp only [Finset.mem_range] at hnrange
    have hnlt : n < 2 := by
      by_contra h
      have hn2 : 2 ≤ n := Nat.le_of_not_gt h
      exact hnnot (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    interval_cases n
    · exact h0
    · exact h1

theorem ccmOutgoingPrimeCumulative_floor_exp_succ_eq_primeMass (T : ℝ) :
    ccmOutgoingPrimeCumulative (Nat.floor (Real.exp T) + 1) =
      criticalMellinPrimeMass T := by
  rw [criticalMellinPrimeMass_eq_atomSum]
  unfold ccmOutgoingPrimeCumulative
  exact sum_range_succ_eq_sum_Icc_two
    (Nat.floor (Real.exp T)) criticalMellinAtomWeight
    (by simp [criticalMellinAtomWeight])
    (by simp [criticalMellinAtomWeight])

theorem ccmPrimeTranslationDefectEnergy_eq_quantileRange
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimeTranslationDefectEnergy a f =
      ∑ n ∈ Finset.range (Nat.floor (Real.exp (2 * a.1)) + 1),
        criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 := by
  unfold ccmPrimeTranslationDefectEnergy
  exact (sum_range_succ_eq_sum_Icc_two
    (Nat.floor (Real.exp (2 * a.1)))
    (fun n => criticalMellinAtomWeight n *
      ccmActualHeadTranslationDefect (Real.log n) f.1)
    (by simp [criticalMellinAtomWeight])
    (by simp [criticalMellinAtomWeight])).symm

/-- Literal Γ-wall outgoing producer in monotone quantile-transport normal form. This is an exact
prime--polar--Gamma identity on the actual physical head, not a scalar-mass surrogate. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_quantileTransport
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        2 * ccmActualHeadTranslationDefect (2 * a.1) f.1 +
        (∑ n ∈ Finset.range N,
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) *
              (ccmActualHeadTranslationDefect (Real.log n) f.1 -
                ccmActualHeadTranslationDefect h f.1)) +
        (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
          Real.exp (h / 2) *
            (ccmActualHeadTranslationDefect (2 * a.1) f.1 -
              ccmActualHeadTranslationDefect h f.1)) := by
  dsimp only
  rw [ccmRestrictedWeilActualHeadGammaWallOutgoingProducer,
    ccmActualHeadPrimeWallChordEnergy_formDomain,
    ccmPrimeTranslationDefectEnergy_eq_quantileRange]
  unfold ccmActualHeadOutgoingPolarEnergy
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [a.property])]
  rw [← ccmOutgoingPrimeCumulative_floor_exp_succ_eq_primeMass]
  have htransport := completedPrimePolarBlock_eq_twoEndpoint_add_quantileTransports
    (2 * a.1) (Nat.floor (Real.exp (2 * a.1)) + 1)
    (ccmArchimedeanFormToAperture a u).1
  have hexp : Real.exp (2 * a.1 / 2) = Real.exp a.1 := by
    congr 1
    ring
  rw [hexp] at htransport
  linear_combination htransport

end RHTower
