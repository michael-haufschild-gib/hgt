import GaloisForLFunctions.RHTower.PaperCirclePredictionLaw

/-! # Exact optimal prediction for actual native circle observations

The source's attained variational energy is the mean squared posterior character
mean. Completing the square gives the excess loss of every predictor and proves
that the bounded optimizer is unique at every observation.
-/

open scoped BigOperators NNReal Classical ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleCaptureEnergy (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) (u : Grid (l+r+10)) : ℝ :=
  Thermal.energyZ (paperCircleObservationCell l i) (paperCircleHistoryLikelihood a (l+r+10) k s)
    (paperCircleHistoryCellScene a l r k i s).norm (paperCircleLocalizedForm a (l+r+10) k t) u

def paperCircleCharacterScore (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) : ℝ :=
  ((paperCircleHistoryCellPosterior a l r k i s).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
      (fun v => Capture.utility true (c v.2) (chi u v.1))

/-- The paper's variational completeness theorem applied to an actual native observation. -/
theorem paperCircleCharacterScore_source_complete (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    (∀ c : Grid (l+r+10) → ℂ, (∀ z, ‖c z‖ ≤ 1) →
      paperCircleCharacterScore a l r k i s t u c ≤ paperCircleCaptureEnergy a l r k i s t u) ∧
    ∃ c : Grid (l+r+10) → ℂ, (∀ z, ‖c z‖ ≤ 1) ∧
      paperCircleCharacterScore a l r k i s t u c = paperCircleCaptureEnergy a l r k i s t u := by
  let base := paperCircleHistoryCellScene a l r k i s
  let obs : Scene (l+r+10) :=
    { base with fund := { base.fund with mood := paperCircleLocalizedForm a (l+r+10) k t } }
  have hn : 0 ≤ obs.norm := by
    change 0 ≤ base.norm
    rw [paperCircleHistoryCellScene_norm]
    exact (paperCircleHistoryCellScene_mass_pos a l r k i s).le
  have hs (c : Grid (l+r+10) → ℂ) : Capture.sales true obs c u =
      paperCircleCharacterScore a l r k i s t u c := by
    change rung base (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))
      (fun x z => Capture.utility true (c z) (chi u x)) = _
    unfold paperCircleCharacterScore
    rw [Law.Ex_withNext]
    simp only [Law.Ex, rung, addMass,
      base, paperCircleHistoryCellScene_ante, Finset.mul_sum, mul_assoc]
  have h := Capture.test_complete true obs
    (fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le) hn u
  simpa only [hs, show Capture.magnitude true obs u = paperCircleCaptureEnergy a l r k i s t u
    from rfl] using h

/-- Fourier capture energy is exactly the squared norm of the conditional character mean. -/
theorem paperCircleCaptureEnergy_mean_square (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleCaptureEnergy a l r k i s t u =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => ‖paperCircleNextCharacterMean a l r k i s t u z‖^2) := by
  unfold paperCircleCaptureEnergy Thermal.energyZ Law.Ex
  apply Finset.sum_congr rfl
  intro z _
  rw [paperCircleNextCharacterMean_source]
  change ‖(paperCircleNextObservationLaw a l r k i s t z : ℂ) *
      paperCircleNextCharacterMean a l r k i s t u z‖^2 /
        hist (paperCircleHistoryCellScene a l r k i s)
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z = _
  rw [paperCircleNextObservationLaw_hist, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (paperCircleNextObservationLaw_pos a l r k i s t z)]
  field_simp [(paperCircleNextObservationLaw_pos a l r k i s t z).ne']

theorem paperCircleCharacterScore_posterior (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterScore a l r k i s t u c =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => 2 * (c z * paperCircleNextCharacterMean a l r k i s t u z).re - ‖c z‖^2) := by
  unfold paperCircleCharacterScore
  rw [paperCircleNextPosterior_disintegration a l r k i s t
    (fun z x => Capture.utility true (c z) (chi u x))]
  congr 1
  funext z
  change (paperCircleNextPosterior a l r k i s t z).Ex
    (fun x => 2 * (c z * chi u x).re - ‖c z‖^2) = _
  rw [Law.Ex_sub, Law.Ex_lmul, Law.Ex_const, ← Law.re_Cx, Law.Cx_lmul]
  rfl

private lemma complex_completion (m c : ℂ) :
    ‖m‖^2 - (2*(c*m).re - ‖c‖^2) = ‖c - conj m‖^2 := by
  simp [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj]
  ring

/-- Exact excess score; the tester need not satisfy any boundedness premise. -/
theorem paperCircleCharacterScore_gap (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCaptureEnergy a l r k i s t u - paperCircleCharacterScore a l r k i s t u c =
      (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => ‖c z - conj (paperCircleNextCharacterMean a l r k i s t u z)‖^2) := by
  rw [paperCircleCaptureEnergy_mean_square, paperCircleCharacterScore_posterior, ← Law.Ex_sub]
  congr 1
  funext z
  exact complex_completion _ _

theorem paperCircleCharacterScore_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterScore a l r k i s t u c ≤ paperCircleCaptureEnergy a l r k i s t u := by
  have h := paperCircleCharacterScore_gap a l r k i s t u c
  have hn := (paperCircleNextObservationLaw a l r k i s t).Ex_nonneg
    (fun z => sq_nonneg ‖c z - conj (paperCircleNextCharacterMean a l r k i s t u z)‖)
  linarith

/-- Strictly positive output masses give pointwise uniqueness of the optimal tester. -/
theorem paperCircleCharacterScore_eq_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterScore a l r k i s t u c = paperCircleCaptureEnergy a l r k i s t u ↔
      ∀ z, c z = conj (paperCircleNextCharacterMean a l r k i s t u z) := by
  constructor
  · intro he z
    have hz : (paperCircleNextObservationLaw a l r k i s t).Ex
        (fun z => ‖c z - conj (paperCircleNextCharacterMean a l r k i s t u z)‖^2) = 0 := by
      rw [← paperCircleCharacterScore_gap, he, sub_self]
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ =>
      mul_nonneg ((paperCircleNextObservationLaw a l r k i s t).nonneg z)
        (sq_nonneg ‖c z - conj (paperCircleNextCharacterMean a l r k i s t u z)‖))).mp hz
    have hsq := (mul_eq_zero.mp (ht z (Finset.mem_univ z))).resolve_left
      (paperCircleNextObservationLaw_pos a l r k i s t z).ne'
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · intro hc
    have h := paperCircleCharacterScore_gap a l r k i s t u c
    simp only [hc, sub_self, norm_zero, pow_two, zero_mul, Law.Ex_const] at h
    linarith

theorem paperCircleCharacterScore_optimizer (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    (∀ z, ‖conj (paperCircleNextCharacterMean a l r k i s t u z)‖ ≤ 1) ∧
      paperCircleCharacterScore a l r k i s t u
        (fun z => conj (paperCircleNextCharacterMean a l r k i s t u z)) =
          paperCircleCaptureEnergy a l r k i s t u := by
  constructor
  · intro z
    rw [Complex.norm_conj]
    exact paperCircleNextCharacterMean_norm a l r k i s t u z
  · exact (paperCircleCharacterScore_eq_iff a l r k i s t u _).mpr (fun _ => rfl)

def paperCircleCharacterRisk (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) : ℝ :=
  ((paperCircleHistoryCellPosterior a l r k i s).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
      (fun v => ‖chi u v.1 - conj (c v.2)‖^2)

theorem paperCircleCharacterRisk_score (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterRisk a l r k i s t u c = 1 - paperCircleCharacterScore a l r k i s t u c := by
  have h (x z : Grid (l+r+10)) : ‖chi u x - conj (c z)‖^2 =
      1 - Capture.utility true (c z) (chi u x) := by
    have he := complex_completion (c z) (chi u x)
    rw [norm_chi] at he
    simp only [Capture.utility, ↓reduceIte]
    rw [← he]
    rw [mul_comm (chi u x) (c z)]
    ring
  simp only [paperCircleCharacterRisk, h, Law.Ex_sub, Law.Ex_const, paperCircleCharacterScore]

/-- The irreducible error is one minus Fourier capture energy. -/
theorem paperCircleCharacterRisk_decomposition (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterRisk a l r k i s t u c =
      1 - paperCircleCaptureEnergy a l r k i s t u +
        (paperCircleNextObservationLaw a l r k i s t).Ex
          (fun z => ‖c z - conj (paperCircleNextCharacterMean a l r k i s t u z)‖^2) := by
  rw [← paperCircleCharacterScore_gap, paperCircleCharacterRisk_score]
  ring

theorem paperCircleCaptureEnergy_range (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    0 ≤ paperCircleCaptureEnergy a l r k i s t u ∧ paperCircleCaptureEnergy a l r k i s t u ≤ 1 := by
  rw [paperCircleCaptureEnergy_mean_square]
  constructor
  · exact Law.Ex_nonneg _ (fun z => sq_nonneg _)
  · apply le_trans (Law.Ex_mono _ (g := fun _ => 1) (fun z => ?_)) (Law.Ex_const _ 1).le
    have h := paperCircleNextCharacterMean_norm a l r k i s t u z
    nlinarith [norm_nonneg (paperCircleNextCharacterMean a l r k i s t u z)]

end
end RHTower
