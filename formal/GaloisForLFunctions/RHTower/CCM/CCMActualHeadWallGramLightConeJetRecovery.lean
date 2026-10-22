import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeCircleCompletion

/-!
# Differential recovery of Suzuki light orientation from the actual CCM wall Gram

Although one scalar chord value sees only the cosine sheet of a wall phase, its spectral derivative
recovers the literal sine/light orientation exactly. The second center jet is a positive dressing
of the CCM/Suzuki prime-entry third-jet scale, and the matched polar contact is a further positive
moment dressing of that actual wall curvature.
-/

open Complex

noncomputable section
namespace RHTower

/-- Positive second center jet of one actual prime-power wall-chord energy. -/
def ccmActualHeadWallChordQuadraticJet
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  2 * criticalMellinAtomWeight n *
    (2 * Real.pi * Real.log n) ^ (2 : ℕ)

/-- Spectral differentiation of actual scalar chord energy recovers literal wall-light orientation. -/
theorem hasDerivAt_normSq_ccmActualHeadMellinWallChord_primePower
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    HasDerivAt
      (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x
        (xiGammaEulerValuationNat (p, e))))
      (4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
        ccmActualHeadMatchedWallLightImbalance p e xi) xi := by
  let n := xiGammaEulerValuationNat (p, e)
  let w := criticalMellinAtomWeight n
  let a := 2 * Real.pi * Real.log n
  have hfun :
      (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x n)) =
        fun x : ℝ => w * (2 - 2 * Real.cos (a * x)) := by
    funext x
    rw [normSq_ccmActualHeadMellinWallChord]
    dsimp only [w, a]
    congr 3
    ring_nf
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => a * x) a xi := by
    simpa using (hasDerivAt_id xi).const_mul a
  have hinner := (hasDerivAt_const (x := xi) (c := (2 : ℝ))).sub
    (hlin.cos.const_mul 2)
  have h := hinner.const_mul w
  apply h.congr_deriv
  rw [ccmActualHeadMatchedWallLightImbalance_eq]
  dsimp only [w, a, n]
  ring

/-- Function-level division-free orientation recovery from the actual scalar wall Gram. -/
theorem deriv_normSq_ccmActualHeadMellinWallChord_primePower
    (p : Nat.Primes) (e : ℕ) :
    deriv
        (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x
          (xiGammaEulerValuationNat (p, e)))) =
      fun x : ℝ =>
        4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
          ccmActualHeadMatchedWallLightImbalance p e x := by
  funext xi
  exact
    (hasDerivAt_normSq_ccmActualHeadMellinWallChord_primePower xi p e).deriv

/-- Negative light occurs division-free as scalar center reserve minus half the chord derivative. -/
theorem actualWallChord_deriv_add_negativeLight_eq_centerReserve
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    8 * Real.pi * Real.log n *
          normSq (suzukiCriticalWallNegativeLightAmplitude
            (2 * Real.pi * xi) p e) +
        deriv (fun x : ℝ =>
          normSq (ccmActualHeadMellinWallChord x n)) xi =
      4 * Real.pi * Real.log n * criticalMellinAtomWeight n := by
  let n := xiGammaEulerValuationNat (p, e)
  have hnegative :=
    normSq_suzukiCriticalWallNegativeLightAmplitude_eq_centerReserve_sub_imbalance
      p e xi
  have hderiv := congrFun
    (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi
  dsimp only [n] at hnegative hderiv ⊢
  rw [hnegative, hderiv]
  ring

/-- The actual wall chord has the declared positive second jet at spectral center. -/
theorem normSq_ccmActualHeadMellinWallChord_secondDeriv_zero
    (p : Nat.Primes) (e : ℕ) :
    deriv (deriv (fun x : ℝ =>
      normSq (ccmActualHeadMellinWallChord x
        (xiGammaEulerValuationNat (p, e))))) 0 =
      ccmActualHeadWallChordQuadraticJet p e := by
  let n := xiGammaEulerValuationNat (p, e)
  let k := 4 * Real.pi * Real.log n
  rw [deriv_normSq_ccmActualHeadMellinWallChord_primePower]
  have h := (hasDerivAt_ccmActualHeadMatchedWallLightImbalance p e 0).const_mul k
  rw [h.deriv]
  rw [ccmActualHeadMatchedWallLightImbalanceFirstJet_zero]
  unfold ccmActualHeadWallChordQuadraticJet
  dsimp only [n, k]
  ring

theorem ccmActualHeadWallChordQuadraticJet_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadWallChordQuadraticJet p e := by
  let n := xiGammaEulerValuationNat (p, e)
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  unfold ccmActualHeadWallChordQuadraticJet
  dsimp only [n]
  positivity

/-- Forced positive dressing from the CCM prime-entry third jet to actual chord curvature. -/
def ccmActualHeadWallChordThirdJetDressing (n : ℕ) : ℝ :=
  Real.pi ^ (2 : ℕ) / 4 * Real.log n ^ (5 : ℕ)

theorem ccmActualHeadWallChordThirdJetDressing_primePower_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadWallChordThirdJetDressing
      (xiGammaEulerValuationNat (p, e)) := by
  unfold ccmActualHeadWallChordThirdJetDressing
  have hlog : 0 < Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  positivity

/-- Actual wall-chord curvature is exactly a positive dressing of the literal CCM third-jet scale. -/
theorem ccmActualHeadWallChordQuadraticJet_eq_dressing_mul_thirdJetScale
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallChordQuadraticJet p e =
      ccmActualHeadWallChordThirdJetDressing
          (xiGammaEulerValuationNat (p, e)) *
        ccmGuinandWeilPrimeEntryThirdJetScale
          (xiGammaEulerValuationNat (p, e)) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [ccmActualHeadWallChordQuadraticJet,
    ccmActualHeadWallChordThirdJetDressing,
    ccmGuinandWeilPrimeEntryThirdJetScale]
  field_simp [hlog]
  ring

/-- Matched polar quadratic contact is the first-moment dressing of actual wall curvature. -/
theorem log_mul_wallLightQuadraticJet_eq_orientedMoment_mul_wallChordQuadraticJet
    (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    (2 * Real.pi * Real.log n) *
        ccmActualHeadMatchedWallLightOrientedQuadraticJet p e =
      ccmActualHeadMatchedOrientedFirstMoment n *
        ccmActualHeadWallChordQuadraticJet p e := by
  unfold ccmActualHeadMatchedWallLightOrientedQuadraticJet
    ccmActualHeadWallChordQuadraticJet
  ring

end RHTower
