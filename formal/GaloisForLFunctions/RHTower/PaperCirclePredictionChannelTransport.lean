import GaloisForLFunctions.RHTower.PaperCircleSplitCharacterPosterior
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Assembly.Phase

/-! # Transporting native character predictors across channel frequencies

The source's channel phase comparison gives a common conditional distortion
budget for every base frequency. Disintegration pays that budget exactly, so a
frequency chosen after observing the output incurs no frequency-count factor.
-/

open scoped BigOperators NNReal Classical ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Paths
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure.Capture

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private lemma conjugate_difference (a b : ℂ) :
    ‖conj a - conj b‖^2 = ‖b-a‖^2 := by
  rw [← map_sub, Complex.norm_conj, norm_sub_rev]

private lemma law_phase_risk {α : Type} [Fintype α] (P : Law α)
    (m n : α → ℂ) (e r d : ℝ)
    (hr : r = 1-e+P.Ex (fun z => ‖conj (m z)-conj (n z)‖^2))
    (h : P.Ex (fun z => ‖n z-m z‖^2) ≤ d) : r ≤ 1-e+d := by
  rw [hr]
  simp only [conjugate_difference]
  exact add_le_add le_rfl h

private lemma law_sqrt_transport {α : Type} [Fintype α] (P : Law α)
    (n m : α → ℂ) (d : ℝ) (hd : 0 ≤ d)
    (h : P.Ex (fun z => ‖n z-m z‖^2) ≤ d^2) :
    Real.sqrt (P.Ex (fun z => ‖n z‖^2)) ≤
      Real.sqrt (P.Ex (fun z => ‖m z‖^2)) + d := by
  have hz (z : α) : ‖n z‖ ≤ ‖m z‖ + ‖n z-m z‖ := by
    have h := norm_add_le (m z) (n z-m z)
    rwa [show m z+(n z-m z)=n z by ring] at h
  have hg := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hd] at hg
  exact (Real.sqrt_le_sqrt (P.Ex_mono (fun z =>
    pow_le_pow_left₀ (norm_nonneg _) (hz z) 2))).trans
      ((P.quadratic_minkowski (fun z => ‖m z‖) (fun z => ‖n z-m z‖)).trans
        (add_le_add le_rfl hg))

/-- Conditional squared phase distortion of the actual observation channel. -/
def paperCircleChannelPhaseCost (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (w z : Grid (l+r+10)) : ℝ :=
  (paperCircleNextPosterior a l r k i s t z).Ex (fun x => ‖chi w x - chi w z‖^2)

theorem paperCircleChannelPhaseCost_nonneg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (w z : Grid (l+r+10)) :
    0 ≤ paperCircleChannelPhaseCost a l r k i s t w z :=
  Law.Ex_nonneg _ (fun _ => sq_nonneg _)

/-- The average distortion is exactly the paper's channel pseudometric squared. -/
theorem paperCircleChannelPhaseCost_mean (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (w : Grid (l+r+10)) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (paperCircleChannelPhaseCost a l r k i s t w) =
        Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 := by
  unfold paperCircleChannelPhaseCost
  rw [← paperCircleNextPosterior_disintegration, Law.Ex_withNext]
  have h (x : Grid (l+r+10)) :
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t) x).Ex
        (fun z => ‖chi w x - chi w z‖^2) =
          Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 := by
    rw [Thermal.ch_ex]
    have he (z) : chi w x - chi w (x+z) = chi w x * (1-chi w z) := by
      rw [chi_add]; ring
    simp only [he, norm_mul, norm_chi, one_mul, Thermal.delta,
      Real.sq_sqrt (Law.Ex_nonneg _ (fun _ => sq_nonneg _))]
  simp only [h, Law.Ex_const]

/-- One conditional budget controls all base frequencies at each observed output. -/
theorem paperCircleNextCharacterMean_phase_pointwise (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u w z : Grid (l+r+10)) :
    ‖paperCircleNextCharacterMean a l r k i s t (u+w) z -
        chi w z * paperCircleNextCharacterMean a l r k i s t u z‖^2 ≤
      paperCircleChannelPhaseCost a l r k i s t w z := by
  let P := paperCircleNextPosterior a l r k i s t z
  have he : P.Cx (fun x => (chi w x - chi w z) * chi u x) =
      paperCircleNextCharacterMean a l r k i s t (u+w) z -
        chi w z * paperCircleNextCharacterMean a l r k i s t u z := by
    unfold paperCircleNextCharacterMean Law.Cx
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [chi_add']
    ring
  have h := P.sq_Cx_norm (fun x => (chi w x - chi w z) * chi u x)
  simpa only [he, norm_mul, norm_chi, mul_one, P, paperCircleChannelPhaseCost] using h

/-- The base frequency may depend on the entire observed output. -/
theorem paperCircleNextCharacterMean_adaptive_phase_transport (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (pick : Grid (l+r+10) → Grid (l+r+10)) (w : Grid (l+r+10)) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => ‖paperCircleNextCharacterMean a l r k i s t (pick z+w) z -
        chi w z * paperCircleNextCharacterMean a l r k i s t (pick z) z‖^2) ≤
          Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 := by
  exact (Law.Ex_mono _ (fun z =>
    paperCircleNextCharacterMean_phase_pointwise a l r k i s t (pick z) w z)).trans_eq
      (paperCircleChannelPhaseCost_mean a l r k i s t w)

theorem paperCircleNextCharacterMean_phase_transport (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u w : Grid (l+r+10)) :
    (paperCircleNextObservationLaw a l r k i s t).Ex
      (fun z => ‖paperCircleNextCharacterMean a l r k i s t (u+w) z -
        chi w z * paperCircleNextCharacterMean a l r k i s t u z‖^2) ≤
          Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 :=
  paperCircleNextCharacterMean_adaptive_phase_transport a l r k i s t (fun _ => u) w

/-- Simultaneous control of every frequency, without paying the size of the grid. -/
theorem paperCircleNextCharacterMean_any_frequency_phase_tail (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (w : Grid (l+r+10)) (b : ℝ) :
    b * (paperCircleNextObservationLaw a l r k i s t).prob
      (fun z => ∃ u, b ≤ ‖paperCircleNextCharacterMean a l r k i s t (u+w) z -
        chi w z * paperCircleNextCharacterMean a l r k i s t u z‖^2) ≤
          Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 := by
  apply le_trans (Law.upperTail _ _ (paperCircleChannelPhaseCost a l r k i s t w)
    (paperCircleChannelPhaseCost_nonneg a l r k i s t w) b ?_)
    (paperCircleChannelPhaseCost_mean a l r k i s t w).le
  intro z hz
  obtain ⟨u, hu⟩ := hz
  exact hu.trans (paperCircleNextCharacterMean_phase_pointwise a l r k i s t u w z)

/-- A phase-rotated optimizer at one frequency predicts the shifted frequency. -/
theorem paperCircleCharacterRisk_phase_transport (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u w : Grid (l+r+10)) :
    paperCircleCharacterRisk a l r k i s t (u+w)
      (fun z => conj (chi w z * paperCircleNextCharacterMean a l r k i s t u z)) ≤
        1 - paperCircleCaptureEnergy a l r k i s t (u+w) +
          Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w ^ 2 := by
  exact law_phase_risk (paperCircleNextObservationLaw a l r k i s t)
    (fun z => chi w z * paperCircleNextCharacterMean a l r k i s t u z)
    (paperCircleNextCharacterMean a l r k i s t (u+w)) _ _ _
    (paperCircleCharacterRisk_decomposition a l r k i s t (u+w) _)
    (paperCircleNextCharacterMean_phase_transport a l r k i s t u w)

/-- The paper's exact Fourier decoding identity for actual posterior predictions. -/
theorem paperCircleNextCharacterMean_channel_decode (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u w : Grid (l+r+10)) :
    (paperCircleNextObservationLaw a l r k i s t).Cx
      (fun z => chi w z * paperCircleNextCharacterMean a l r k i s t u z) =
        (Thermal.cred (paperCircleLocalizedForm a (l+r+10) k t) w : ℂ) *
          (paperCircleHistoryCellPosterior a l r k i s).Cx (chi (u+w)) := by
  let scene := paperCircleObservationScene a l r k i s t
  have hs : scalar scene (u+w) =
      (paperCircleHistoryCellPosterior a l r k i s).Cx (chi (u+w)) := by
    change (∑ x, (ante (paperCircleHistoryCellScene a l r k i s) x : ℂ) * chi (u+w) x) = _
    simp only [paperCircleHistoryCellScene_ante, Law.Cx]
  calc
    _ = ∑ z, chi w z * letter scene u z := by
      unfold Law.Cx
      apply Finset.sum_congr rfl
      intro z _
      change _ = chi w z * Thermal.fz (paperCircleObservationCell l i)
        (paperCircleHistoryLikelihood a (l+r+10) k s)
        (paperCircleHistoryCellScene a l r k i s).norm
        (paperCircleLocalizedForm a (l+r+10) k t) u z
      rw [paperCircleNextCharacterMean_source]
      ring
    _ = _ := by rw [Troupe.duet_decode, hs]; rfl

/-- The square root of prediction energy is Lipschitz in the channel pseudometric. -/
theorem paperCircleCaptureEnergy_sqrt_shift (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u w : Grid (l+r+10)) :
    Real.sqrt (paperCircleCaptureEnergy a l r k i s t (u+w)) ≤
      Real.sqrt (paperCircleCaptureEnergy a l r k i s t u) +
        Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w := by
  have h := law_sqrt_transport (paperCircleNextObservationLaw a l r k i s t)
    (paperCircleNextCharacterMean a l r k i s t (u+w))
    (fun z => chi w z * paperCircleNextCharacterMean a l r k i s t u z)
    (Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w)
    (Real.sqrt_nonneg _) (paperCircleNextCharacterMean_phase_transport a l r k i s t u w)
  simp only [norm_mul, norm_chi, one_mul] at h
  exact (congrArg Real.sqrt (paperCircleCaptureEnergy_mean_square a l r k i s t (u+w))).le.trans
    (h.trans_eq (congrArg (fun q => Real.sqrt q +
      Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) w)
        (paperCircleCaptureEnergy_mean_square a l r k i s t u).symm))

theorem paperCircleCaptureEnergy_sqrt_channel_bound (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u v : Grid (l+r+10)) :
    |Real.sqrt (paperCircleCaptureEnergy a l r k i s t u) -
      Real.sqrt (paperCircleCaptureEnergy a l r k i s t v)| ≤
        Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) (u-v) := by
  have h1 := paperCircleCaptureEnergy_sqrt_shift a l r k i s t v (u-v)
  have h2 := paperCircleCaptureEnergy_sqrt_shift a l r k i s t u (v-u)
  rw [show v+(u-v)=u by ring] at h1
  rw [show u+(v-u)=v by ring] at h2
  rw [show v-u = -(u-v) by ring, Thermal.delta_even] at h2
  rw [abs_le]
  constructor <;> linarith

theorem paperCircleCaptureEnergy_channel_bound (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u v : Grid (l+r+10)) :
    |paperCircleCaptureEnergy a l r k i s t u - paperCircleCaptureEnergy a l r k i s t v| ≤
      2 * Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) (u-v) := by
  let A := paperCircleCaptureEnergy a l r k i s t u
  let B := paperCircleCaptureEnergy a l r k i s t v
  let d := Thermal.delta (paperCircleLocalizedForm a (l+r+10) k t) (u-v)
  have hA := paperCircleCaptureEnergy_range a l r k i s t u
  have hB := paperCircleCaptureEnergy_range a l r k i s t v
  have ha : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.1
  have hb : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.1
  have had : Real.sqrt A ≤ 1 := by nlinarith [Real.sqrt_nonneg A]
  have hbd : Real.sqrt B ≤ 1 := by nlinarith [Real.sqrt_nonneg B]
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have h := (abs_le.mp (paperCircleCaptureEnergy_sqrt_channel_bound a l r k i s t u v))
  have h1 := mul_le_mul_of_nonneg_right h.2 (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))
  have h2 := mul_le_mul_of_nonneg_right h.1 (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))
  change |A-B| ≤ 2*d
  rw [abs_le]
  constructor <;> nlinarith

end
end RHTower
