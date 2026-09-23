import GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeJetPairing
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParity
import GaloisForLFunctions.RHTower.CCMActualHeadGammaWallOutgoingProducer

/-!
# Reflection fiber of the actual wall-Gram light-cone jet

The completed restricted-Weil producer is reflection-even, whereas the differentiated wall
orientation current is reflection-odd.  Thus direct scalar producer transport cannot retain the
orientation channel: it lives in the off-diagonal parity fiber.
-/

open Complex MeasureTheory

noncomputable section
namespace RHTower

/-- The actual wall-chord derivative multiplier is odd in spectral frequency. -/
theorem deriv_normSq_ccmActualHeadMellinWallChord_primePower_neg
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    deriv (fun x : ℝ =>
        normSq (ccmActualHeadMellinWallChord x
          (xiGammaEulerValuationNat (p, e)))) (-xi) =
      -deriv (fun x : ℝ =>
        normSq (ccmActualHeadMellinWallChord x
          (xiGammaEulerValuationNat (p, e)))) xi := by
  rw [congrFun (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) (-xi),
    congrFun (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi,
    ccmActualHeadMatchedWallLightImbalance_eq,
    ccmActualHeadMatchedWallLightImbalance_eq]
  rw [show 2 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) * -xi =
      -(2 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) * xi) by ring,
    Real.sin_neg]
  ring

/-- Reflection reverses the actual-head wall-chord jet current. -/
theorem ccmActualHeadWallChordJetCurrent_l2Reflection
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallChordJetCurrent p e (l2Reflection f) =
      -ccmActualHeadWallChordJetCurrent p e f := by
  unfold ccmActualHeadWallChordJetCurrent
  rw [fourierUnitary_l2Reflection]
  let m : ℝ → ℝ := fun xi =>
    deriv (fun x : ℝ =>
      normSq (ccmActualHeadMellinWallChord x
        (xiGammaEulerValuationNat (p, e)))) xi
  let g : SoninL2 := fourierUnitary f
  have hreflect := l2Reflection_ae g
  calc
    (∫ xi : ℝ, m xi * ‖(l2Reflection g : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
        ∫ xi : ℝ, m xi * ‖(g : ℝ → ℂ) (-xi)‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [hreflect] with xi hxi
      rw [hxi]
    _ = ∫ xi : ℝ, -(m (-xi) * ‖(g : ℝ → ℂ) (-xi)‖ ^ (2 : ℕ)) := by
      apply integral_congr_ae
      filter_upwards with xi
      dsimp only [m]
      rw [deriv_normSq_ccmActualHeadMellinWallChord_primePower_neg]
      ring
    _ = -(∫ xi : ℝ, m (-xi) * ‖(g : ℝ → ℂ) (-xi)‖ ^ (2 : ℕ)) := by
      rw [integral_neg]
    _ = -(∫ xi : ℝ, m xi * ‖(g : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
      congr 1
      simpa only using MeasureTheory.integral_neg_eq_self
        (fun xi : ℝ => m xi * ‖(g : ℝ → ℂ) xi‖ ^ (2 : ℕ)) volume

/-- The jet current is quadratic, hence invariant under global sign. -/
@[simp] theorem ccmActualHeadWallChordJetCurrent_neg
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallChordJetCurrent p e (-f) =
      ccmActualHeadWallChordJetCurrent p e f := by
  unfold ccmActualHeadWallChordJetCurrent
  rw [map_neg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg (fourierUnitary f)] with xi hxi
  rw [hxi]
  simp only [Pi.neg_apply, norm_neg]

/-- Every reflection-even head is invisible to the wall-chord jet current. -/
theorem ccmActualHeadWallChordJetCurrent_eq_zero_of_reflection_even
    (p : Nat.Primes) (e : ℕ) (f : SoninL2)
    (hf : l2Reflection f = f) :
    ccmActualHeadWallChordJetCurrent p e f = 0 := by
  have h := ccmActualHeadWallChordJetCurrent_l2Reflection p e f
  rw [hf] at h
  linarith

/-- Every reflection-odd head is also invisible to the quadratic jet current. -/
theorem ccmActualHeadWallChordJetCurrent_eq_zero_of_reflection_odd
    (p : Nat.Primes) (e : ℕ) (f : SoninL2)
    (hf : l2Reflection f = -f) :
    ccmActualHeadWallChordJetCurrent p e f = 0 := by
  have h := ccmActualHeadWallChordJetCurrent_l2Reflection p e f
  rw [hf, ccmActualHeadWallChordJetCurrent_neg] at h
  linarith

/-- Reflection swaps the two exact positive light slacks. -/
theorem ccmActualHeadWallPositiveLightRateEnergy_l2Reflection
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallPositiveLightRateEnergy p e (l2Reflection f) =
      ccmActualHeadWallNegativeLightRateEnergy p e f := by
  have hpos := wallPositiveLightRateEnergy_sub_chordJetCurrent_eq_centerReserve
    p e (l2Reflection f)
  have hneg := wallNegativeLightRateEnergy_add_chordJetCurrent_eq_centerReserve p e f
  have hnorm : ‖l2Reflection f‖ = ‖f‖ := l2ReflectionIsometry.norm_map f
  rw [ccmActualHeadWallChordJetCurrent_l2Reflection, hnorm] at hpos
  linarith

theorem ccmActualHeadWallNegativeLightRateEnergy_l2Reflection
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallNegativeLightRateEnergy p e (l2Reflection f) =
      ccmActualHeadWallPositiveLightRateEnergy p e f := by
  have hneg := wallNegativeLightRateEnergy_add_chordJetCurrent_eq_centerReserve
    p e (l2Reflection f)
  have hpos := wallPositiveLightRateEnergy_sub_chordJetCurrent_eq_centerReserve p e f
  have hnorm : ‖l2Reflection f‖ = ‖f‖ := l2ReflectionIsometry.norm_map f
  rw [ccmActualHeadWallChordJetCurrent_l2Reflection, hnorm] at hneg
  linarith

/-- Completed actual Γ-wall producer is reflection-even on the literal complete form domain. -/
theorem ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_reflection
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a
        (ccmArchimedeanFormReflection a u) =
      ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a u := by
  rw [ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic,
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic,
    ccmRestrictedWeilSourceQuadratic_reflection]

/-- On the same complete form-domain reflection fiber, actual wall jet reverses sign. -/
theorem ccmActualHeadWallChordJetCurrent_formReflection
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallChordJetCurrent p e
        (ccmArchimedeanWeightedToL2
          (ccmArchimedeanFormReflection a u).1) =
      -ccmActualHeadWallChordJetCurrent p e
        (ccmArchimedeanWeightedToL2 u.1) := by
  change ccmActualHeadWallChordJetCurrent p e
      (ccmArchimedeanWeightedToL2 (ccmArchimedeanFourierReflection u.1)) = _
  rw [ccmArchimedeanWeightedToL2_reflection,
    ccmActualHeadWallChordJetCurrent_l2Reflection]

/-- A scalar selector factoring only through the completed producer can recover the jet on a
reflection fiber only when that jet vanishes. -/
theorem wallChordJet_zero_of_factors_through_completedProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (p : Nat.Primes) (e : ℕ) (selector : ℝ → ℝ)
    (hselector : ∀ v : CCMArchimedeanFormDomain a,
      ccmActualHeadWallChordJetCurrent p e (ccmArchimedeanWeightedToL2 v.1) =
        selector (ccmRestrictedWeilActualHeadGammaWallOutgoingProducer a v)) :
    ccmActualHeadWallChordJetCurrent p e (ccmArchimedeanWeightedToL2 u.1) = 0 := by
  have hu := hselector u
  have hur := hselector (ccmArchimedeanFormReflection a u)
  rw [ccmActualHeadWallChordJetCurrent_formReflection,
    ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_reflection] at hur
  linarith

end RHTower
