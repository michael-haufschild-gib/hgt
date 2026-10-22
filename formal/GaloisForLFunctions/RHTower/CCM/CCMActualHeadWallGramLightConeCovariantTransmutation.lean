import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeReflectionFiber

/-!
# Covariant transmutation of the wall-Gram jet into the actual matched producer

The reflection-odd wall-chord derivative becomes reflection-even after pairing with the corpus's
literal odd matched-polar sine connection.  The resulting covariant current is exactly a positive
diagonal coefficient times the existing summable Suzuki current and occurs with its forced sign
inside the actual prime-minus-polar cell.
-/

open Complex MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Positive prime-power coefficient converting the matched Suzuki current into the covariant
wall-chord jet. -/
def ccmActualHeadWallPolarJetRate
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  (2 * Real.pi * Real.log n) * criticalMellinAtomWeight n

/-- Wall-chord derivative paired with the literal odd matched-polar connection. -/
def ccmActualHeadWallChordPolarJetCurrent
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  ∫ xi : ℝ,
    deriv (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x n)) xi *
      ccmActualHeadMatchedSinePhaseProfile n xi *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

theorem ccmActualHeadWallPolarJetRate_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadWallPolarJetRate p e := by
  have hlog : 0 < Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  unfold ccmActualHeadWallPolarJetRate
  positivity

theorem integrable_ccmActualHeadWallChordPolarJetCurrent_integrand
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    let n := xiGammaEulerValuationNat (p, e)
    Integrable (fun xi : ℝ =>
      deriv (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x n)) xi *
        ccmActualHeadMatchedSinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  let n := xiGammaEulerValuationNat (p, e)
  have h :=
    (integrable_ccmActualHeadMatchedSinePhaseProfile_mul_density n f).const_mul
      (4 * Real.pi * Real.log n * criticalMellinAtomWeight n)
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change
    (4 * Real.pi * Real.log n * criticalMellinAtomWeight n) *
          (Real.sin (2 * Real.pi * Real.log n * xi) *
            ccmActualHeadMatchedSinePhaseProfile n xi *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
      deriv (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x n)) xi *
        ccmActualHeadMatchedSinePhaseProfile n xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  rw [congrFun (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi,
    ccmActualHeadMatchedWallLightImbalance_eq]
  dsimp only [n]
  ring

/-- **Covariant transmutation.**  Odd wall differentiation followed by the odd polar connection is
exactly the actual matched Suzuki current with its forced positive source coefficient. -/
theorem ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallChordPolarJetCurrent p e f =
      ccmActualHeadWallPolarJetRate p e *
        ccmActualHeadMatchedSuzukiCurrent
          (xiGammaEulerValuationNat (p, e)) f := by
  let n := xiGammaEulerValuationNat (p, e)
  rw [ccmActualHeadWallChordPolarJetCurrent,
    ccmActualHeadMatchedSuzukiCurrent_eq_sinePhaseProfile]
  have hrewrite :
      (∫ xi : ℝ,
        deriv (fun x : ℝ => normSq (ccmActualHeadMellinWallChord x n)) xi *
          ccmActualHeadMatchedSinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
        (4 * Real.pi * Real.log n * criticalMellinAtomWeight n) *
          ∫ xi : ℝ,
            Real.sin (2 * Real.pi * Real.log n * xi) *
              ccmActualHeadMatchedSinePhaseProfile n xi *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with xi
    rw [congrFun (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi,
      ccmActualHeadMatchedWallLightImbalance_eq]
    dsimp only [n]
    ring
  rw [hrewrite]
  unfold ccmActualHeadWallPolarJetRate
  dsimp only [n]
  ring

/-- The existing matched Suzuki current is reflection-even: its arithmetic and polar orientation
factors are both odd. -/
theorem ccmActualHeadMatchedSuzukiCurrent_l2Reflection
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadMatchedSuzukiCurrent n (l2Reflection f) =
      ccmActualHeadMatchedSuzukiCurrent n f := by
  rw [ccmActualHeadMatchedSuzukiCurrent_eq_sinePhaseProfile,
    ccmActualHeadMatchedSuzukiCurrent_eq_sinePhaseProfile,
    fourierUnitary_l2Reflection]
  let K : ℝ → ℝ := fun xi =>
    Real.sin (2 * Real.pi * Real.log n * xi) *
      ccmActualHeadMatchedSinePhaseProfile n xi
  let g : SoninL2 := fourierUnitary f
  have hreflect := l2Reflection_ae g
  congr 1
  calc
    (∫ xi : ℝ, K xi * ‖(l2Reflection g : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
        ∫ xi : ℝ, K xi * ‖(g : ℝ → ℂ) (-xi)‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards [hreflect] with xi hxi
      rw [hxi]
    _ = ∫ xi : ℝ, K (-xi) * ‖(g : ℝ → ℂ) (-xi)‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards with xi
      dsimp only [K]
      rw [show 2 * Real.pi * Real.log n * -xi =
          -(2 * Real.pi * Real.log n * xi) by ring,
        Real.sin_neg, ccmActualHeadMatchedSinePhaseProfile_neg]
      ring
    _ = ∫ xi : ℝ, K xi * ‖(g : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
      simpa only using MeasureTheory.integral_neg_eq_self
        (fun xi : ℝ => K xi * ‖(g : ℝ → ℂ) xi‖ ^ (2 : ℕ)) volume

/-- Covariantizing the odd wall jet bypasses the scalar reflection no-go: the resulting current is
reflection-even. -/
theorem ccmActualHeadWallChordPolarJetCurrent_l2Reflection
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallChordPolarJetCurrent p e (l2Reflection f) =
      ccmActualHeadWallChordPolarJetCurrent p e f := by
  rw [ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent,
    ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent,
    ccmActualHeadMatchedSuzukiCurrent_l2Reflection]

/-- **Division-free actual-cell occurrence.**  After the forced positive diagonal scaling, the
actual prime-minus-polar cell contains the covariant wall jet with coefficient exactly `-1`. -/
theorem wallPolarJetRate_mul_actualCell_eq_scaledSymmetric_sub_polarJet
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    let n := xiGammaEulerValuationNat (p, e)
    ccmActualHeadWallPolarJetRate p e *
        (criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f) =
      ccmActualHeadWallPolarJetRate p e *
          ccmActualHeadMatchedSymmetricCellResidual n f -
        ccmActualHeadWallChordPolarJetCurrent p e f := by
  let n := xiGammaEulerValuationNat (p, e)
  have hcell := ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki
    n f
  have hjet :=
    ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent p e f
  dsimp only [n] at hcell hjet ⊢
  rw [hcell, hjet]
  ring

/-- The covariant wall jet inherits the existing quadratic-aperture summable bound. -/
theorem abs_ccmActualHeadWallChordPolarJetCurrent_le
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    |ccmActualHeadWallChordPolarJetCurrent p e f| ≤
      ccmActualHeadWallPolarJetRate p e *
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) ^ (2 : ℕ) /
          (4 * Real.exp
            (Real.log (xiGammaEulerValuationNat (p, e)) / 2)) * ‖f‖ ^ (2 : ℕ)) := by
  rw [ccmActualHeadWallChordPolarJetCurrent_eq_rate_mul_matchedSuzukiCurrent,
    abs_mul, abs_of_pos (ccmActualHeadWallPolarJetRate_pos p e)]
  exact mul_le_mul_of_nonneg_left
    (abs_ccmActualHeadMatchedSuzukiCurrent_le_quadratic
      (xiGammaEulerValuationNat (p, e)) f)
    (ccmActualHeadWallPolarJetRate_pos p e).le

/-- Finite labeled packet of scaled actual prime-minus-polar cells. -/
def ccmActualHeadWallPolarJetFiniteActualBlock
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) : ℝ :=
  ∑ pe ∈ F,
    let n := xiGammaEulerValuationNat pe
    ccmActualHeadWallPolarJetRate pe.1 pe.2 *
      (criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f)

def ccmActualHeadWallPolarJetFiniteSymmetricBlock
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) : ℝ :=
  ∑ pe ∈ F,
    ccmActualHeadWallPolarJetRate pe.1 pe.2 *
      ccmActualHeadMatchedSymmetricCellResidual (xiGammaEulerValuationNat pe) f

def ccmActualHeadWallChordPolarJetFiniteCurrent
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) : ℝ :=
  ∑ pe ∈ F, ccmActualHeadWallChordPolarJetCurrent pe.1 pe.2 f

/-- Finite packet assembly preserves labels and the forced coefficient-minus-one occurrence. -/
theorem ccmActualHeadWallPolarJetFiniteActualBlock_eq_symmetric_sub_current
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) :
    ccmActualHeadWallPolarJetFiniteActualBlock F f =
      ccmActualHeadWallPolarJetFiniteSymmetricBlock F f -
        ccmActualHeadWallChordPolarJetFiniteCurrent F f := by
  unfold ccmActualHeadWallPolarJetFiniteActualBlock
    ccmActualHeadWallPolarJetFiniteSymmetricBlock
    ccmActualHeadWallChordPolarJetFiniteCurrent
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pe hpe
  simpa only [Prod.eta] using
    wallPolarJetRate_mul_actualCell_eq_scaledSymmetric_sub_polarJet pe.1 pe.2 f

end RHTower
