import GaloisForLFunctions.BiScaleUncertainty.SignedCoherentMomentReceiver
import GaloisForLFunctions.BiScaleUncertainty.OddMultiplierLeakageFamily
import GaloisForLFunctions.BiScaleUncertainty.FiniteTranslationTrains

/-!
# Unbounded realized cancellation at fixed original-source energy

The existing smooth odd six-packet family has a negative second-lag correlation.
Moving its packets outward increases the source mean and makes the signed
coherent budget improvement arbitrarily large, while preserving the first-lag
zero and the same positive original energy. The full plastic receiver inherits
this realized gain for every collar cutoff.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported ContDiff

namespace GaloisForLFunctions.BiScaleUncertainty.RealizedCoherentCancellation
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower.EvenSector.SmoothBlindInterpolation
open CenteredHyperbolicGram ProjectedHyperbolicGram SourceLattice SignedCoherentMoment
open OddMultiplierLeakage HyperbolicRay
noncomputable section

/-- The extra outward displacement separates reflection pairs from the second lag. -/
def outwardSource (T : ℝ) : C_c(ℝ, ℝ) := source (|T| + lag)

theorem outwardSource_smooth (T : ℝ) : ContDiff ℝ ∞ (outwardSource T : ℝ → ℝ) :=
  sourceFn_smooth _

theorem outwardSource_odd (T u : ℝ) : outwardSource T (-u) = -outwardSource T u := source_odd _ _

theorem outwardSource_energy (T : ℝ) : autocorr (outwardSource T) 0 = 6 * packetMass :=
  source_autocorr_zero _

theorem outwardSource_first_zero (T : ℝ) : autocorr (outwardSource T) (Real.log 2) = 0 :=
  source_autocorr_lag _

private def secondAdjacent (i j : Fin 6) : Prop := (i = 0 ∧ j = 2) ∨ (i = 5 ∧ j = 3)

private theorem sum_six (g : Fin 6 → ℝ) :
    ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change g 0 + (g 1 + (g 2 + (g 3 + (g 4 + g 5)))) = _
  ring

private theorem second_gap (T : ℝ) (hT : lag ≤ |T|) (i j : Fin 6)
    (h : ¬secondAdjacent i j) : lag ≤ |2 * lag + node T i - node T j| := by
  have hd := lag_pos
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [secondAdjacent, Fin.ext_iff] at h
  all_goals norm_num [node]
  all_goals try linarith [le_abs_self lag]
  all_goals
    by_contra hn
    have hh := abs_lt.mp (lt_of_not_ge hn)
    rcases hh with ⟨ha, hb⟩
    linarith

/-- Exactly two coefficient products survive at twice the first logarithmic lag. -/
theorem outwardSource_second_correlation (T : ℝ) :
    autocorr (outwardSource T) (2 * Real.log 2) = -2 * packetMass := by
  classical
  have hT : lag ≤ abs (|T| + lag) := by
    rw [abs_of_pos (by linarith only [abs_nonneg T, lag_pos] : 0 < |T| + lag)]
    linarith only [abs_nonneg T]
  have hw : _root_.RHTower.AutocorrelationKrein.pulseWidth < lag := by
    unfold _root_.RHTower.AutocorrelationKrein.pulseWidth lag
    linarith only [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have he (i j : Fin 6) : autocorr packet
      (2 * lag + node (|T| + lag) i - node (|T| + lag) j) =
        if secondAdjacent i j then packetMass else 0 := by
    by_cases h : secondAdjacent i j
    · rw [if_pos h]
      have hz : 2 * lag + node (|T| + lag) i - node (|T| + lag) j = 0 := by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [node] <;> ring
      rw [hz]
      rfl
    · rw [if_neg h]
      exact packet_autocorr_zero (hw.le.trans (second_gap _ hT i j h))
  change autocorr (finiteTranslateSource packet Finset.univ coefficient (node (|T| + lag)))
    (2 * lag) = _
  rw [autocorr_finiteTranslateSource packet_smooth.continuous packet_compact]
  simp_rw [he]
  simp only [sum_six]
  dsimp [coefficient]
  norm_num [secondAdjacent, Fin.ext_iff]
  ring

/-- Positive slope already present in the exact multiplier-leakage law. -/
def leakageSlope : ℝ := 2 * Real.sinh (lag / 2) * packetCoshMass

theorem leakageSlope_pos : 0 < leakageSlope := by
  exact mul_pos (mul_pos (by norm_num)
    (Real.sinh_pos_iff.mpr (by linarith only [lag_pos]))) packetCoshMass_pos

private theorem coshMass_eq_source_and_sine (f : C_c(ℝ, ℝ)) (α : ℝ) :
    coshMass f α = autocorr f 0 + 2 * autocorr (sinhCompact α f) 0 := by
  have hF := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hS := integrable_sq (g := (sinhCompact α f : ℝ → ℝ))
    (sinhCompact α f).continuous (sinhCompact α f).hasCompactSupport
  have he : (fun u => Real.cosh (2 * α * u) * f u ^ 2) =
      fun u => f u ^ 2 + 2 * (sinhCompact α f u) ^ 2 := by
    funext u
    have hc : Real.cosh (2 * (α * u)) = 1 + 2 * Real.sinh (α * u) ^ 2 := by
      rw [Real.cosh_two_mul]
      nlinarith only [Real.cosh_sq_sub_sinh_sq (α * u)]
    rw [show 2 * α * u = 2 * (α * u) by ring, hc]
    change _ = f u ^ 2 + 2 * (Real.sinh (α * u) * f u) ^ 2
    ring
  unfold coshMass
  rw [he, integral_add hF (hS.const_mul 2), integral_const_mul,
    integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero]

/-- Moving the same fixed-energy packets outward forces their source mean to grow. -/
theorem outwardSource_mean_growth (T : ℝ) :
    2 * leakageSlope * |T| ≤ 6 * packetMass * sourceMean (outwardSource T) (1 / 2) := by
  let F := outwardSource T
  have hR : 0 < autocorr F 0 := source_energy_pos _
  have hmu : autocorr F 0 * sourceMean F (1 / 2) =
      autocorr F 0 + 2 * autocorr (sinhCompact (1 / 2) F) 0 := by
    unfold sourceMean
    rw [coshMass_eq_source_and_sine]
    field_simp [hR.ne']
  have hbound := (le_abs_self (autocorr (sinhCompact (1 / 2) F) lag)).trans
    (abs_autocorr_le_zero (sinhCompact (1 / 2) F).hasCompactSupport
      (sinhCompact (1 / 2) F).continuous lag)
  have hval : autocorr (sinhCompact (1 / 2) F) lag =
      leakageSlope * Real.sinh (|T| + 3 * lag) := by
    change autocorr (sinhCompact (1 / 2) (source (|T| + lag))) lag = _
    rw [source_sinh_autocorr_lag,
      abs_of_pos (by linarith only [abs_nonneg T, lag_pos] : 0 < |T| + lag),
      show |T| + lag + 2 * lag = |T| + 3 * lag by ring]
    unfold leakageSlope
    ring
  rw [hval] at hbound
  have hs : |T| ≤ Real.sinh (|T| + 3 * lag) := by
    have h := Real.self_le_sinh_iff.mpr
      (show 0 ≤ |T| + 3 * lag by linarith only [abs_nonneg T, lag_pos])
    linarith only [h, lag_pos]
  have hlow := (mul_le_mul_of_nonneg_left hs leakageSlope_pos.le).trans hbound
  have he : autocorr F 0 = 6 * packetMass := outwardSource_energy T
  change _ ≤ 6 * packetMass * sourceMean F (1 / 2)
  rw [he] at hmu hR
  linarith only [hlow, hmu, hR]

/-- Exact negative-sample mechanism behind the realized cancellation. -/
theorem outwardSource_correction_balance (T : ℝ) :
    Real.cosh lag * correctionSample (outwardSource T) 2 =
      packetMass * (Real.cosh lag ^ 2 - sourceMean (outwardSource T) (1 / 2)) := by
  rw [correctionSample, if_neg (by norm_num : (2 : ℤ) ≠ 0)]
  norm_num only [sourceSample]
  rw [show (2 * Real.log 2) / 2 = lag by unfold lag; ring,
    outwardSource_second_correlation]
  field_simp [(Real.cosh_pos lag).ne']
  ring

private theorem gap_ge_sample (f : C_c(ℝ, ℝ)) (k : ℤ) :
    -2 * correctionSample f k ≤ latticeFrame f - coherentBudget f := by
  have hs : Summable (fun z : ℤ => max (-correctionSample f z) 0) := by
    apply summable_of_hasFiniteSupport
    apply (correctionSample_finite f).subset
    intro z hz
    change max (-correctionSample f z) 0 ≠ 0 at hz
    change correctionSample f z ≠ 0
    intro he
    exact hz (by simp [he])
  have ht := hs.le_tsum k (fun _ _ => le_max_right _ _)
  change max (-correctionSample f k) 0 ≤ negativeCorrectionMass f at ht
  rw [latticeFrame_sub_coherentBudget]
  have hm := le_max_left (-correctionSample f k) 0
  linarith only [ht, hm]

/-- Explicit positive growth rate for the improvement, using just one lattice sample. -/
def gainSlope : ℝ := 2 * leakageSlope / (3 * Real.cosh lag)

theorem gainSlope_pos : 0 < gainSlope :=
  div_pos (mul_pos (by norm_num) leakageSlope_pos) (mul_pos (by norm_num) (Real.cosh_pos _))

/-- The correction saving grows without bound while original source energy stays fixed. -/
theorem outwardSource_gap_lower (T : ℝ) :
    gainSlope * |T| - 2 * packetMass * Real.cosh lag ≤
      latticeFrame (outwardSource T) - coherentBudget (outwardSource T) := by
  have hm := outwardSource_mean_growth T
  have he := outwardSource_correction_balance T
  have hg := mul_le_mul_of_nonneg_right (gap_ge_sample (outwardSource T) 2) (Real.cosh_pos lag).le
  have hb : gainSlope * (3 * Real.cosh lag) = 2 * leakageSlope := by
    unfold gainSlope
    field_simp [(Real.cosh_pos lag).ne']
  have hbt := congrArg (fun x : ℝ => x * |T|) hb
  apply le_of_mul_le_mul_right ?_ (Real.cosh_pos lag)
  nlinarith only [hm, he, hg, hbt]

theorem oddCompactSource_outwardSource (T : ℝ) :
    oddCompactSource (outwardSource T) = outwardSource T := by
  ext u
  change (outwardSource T u - outwardSource T (-u)) / 2 = outwardSource T u
  rw [outwardSource_odd]
  ring

/-- Unconditional realization of arbitrarily large signed-budget savings. -/
theorem exists_fixedEnergy_logZero_large_gain (A : ℝ) :
    ∃ T : ℝ, A < latticeFrame (outwardSource T) - coherentBudget (outwardSource T) := by
  let T := (|A + 2 * packetMass * Real.cosh lag| + 1) / gainSlope
  have hT : 0 < T := div_pos (by positivity) gainSlope_pos
  have ht : gainSlope * T = |A + 2 * packetMass * Real.cosh lag| + 1 := by
    unfold T
    field_simp [gainSlope_pos.ne']
  refine ⟨T, ?_⟩
  have h := outwardSource_gap_lower T
  rw [abs_of_pos hT, ht] at h
  have ha := le_abs_self (A + 2 * packetMass * Real.cosh lag)
  linarith only [h, ha]

/-- The same smooth odd source improves every full plastic certificate by the prescribed amount. -/
theorem exists_smooth_odd_fixedEnergy_plastic_gain (A : ℝ) :
    ∃ f : C_c(ℝ, ℝ), ContDiff ℝ ∞ (f : ℝ → ℝ) ∧ (∀ u, f (-u) = -f u) ∧
      autocorr f 0 = 6 * packetMass ∧ autocorr f (Real.log 2) = 0 ∧
        A < latticeFrame f - coherentBudget f ∧
          ∀ N : ℕ, (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar f N (-y)) +
            plasticRemainderEnergy f - 2 * Real.log 2 * latticeFrame f +
              2 * Real.log 2 * A < plasticCrossover f := by
  obtain ⟨T, hT⟩ := exists_fixedEnergy_logZero_large_gain A
  refine ⟨outwardSource T, outwardSource_smooth T, outwardSource_odd T,
    outwardSource_energy T, outwardSource_first_zero T, hT, ?_⟩
  intro N
  have hp := odd_plasticCrossover_ge_coherentBudget (outwardSource T) N
  rw [oddCompactSource_outwardSource] at hp
  have hd : 0 < 2 * Real.log 2 := mul_pos (by norm_num) lag_pos
  have hg := mul_pos hd (sub_pos.mpr hT)
  nlinarith only [hp, hg]

end
end GaloisForLFunctions.BiScaleUncertainty.RealizedCoherentCancellation
