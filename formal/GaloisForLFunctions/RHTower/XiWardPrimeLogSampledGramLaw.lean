import GaloisForLFunctions.RHTower.XiWardMergedSlackPrimeLogSampling

/-!
# Prime-log sampled positivity of the four-unit Ward matrices

The augmented boundary Gram `W_P = [[G_P, r_P], [r_P^*, 4]]` is positive
semidefinite for every right-half-plane packet exactly when RH holds.  The
detection-window law reduces this to sampled packets: a strict-right pair makes
the one-node Schur diagonal strictly negative at every sample inside its margin
window, and every off-line pair has an upper representative, so covering the
positive heights alone suffices.  Consequently `W_P`-positivity restricted to
finite packets drawn from any detection cover of the positive heights — in
particular from the locally finite prime-log family — is already exactly RH.
-/

open Complex Filter Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- A strict-right pair makes the one-node four-unit Schur diagonal strictly
negative at every sample inside its margin window. -/
theorem continuedXiWardFourUnitSchurDefect_marginWindow_diag_re_neg
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    (continuedXiWardFourUnitSchurDefect
      (fun _ : Fin 1 => (1 / 2 : ℂ) + I * (t : ℂ)) 0 0).re < 0 := by
  set node : ℂ := (1 / 2 : ℂ) + I * (t : ℂ) with hnodedef
  set r : ℂ := continuedXiAntiCausalWardResponse node with hrdef
  have hnorm : 4 < Complex.normSq r := by
    rw [hrdef, hnodedef]
    exact normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four q ht
  change (4 * (1 / (node + star node)) - r * star r).re < 0
  have hden : node + star node = (1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, RCLike.star_def, Complex.conj_re,
        Complex.one_re]
      rw [hnodedef]
      norm_num [Complex.add_re, Complex.mul_re]
    · simp only [Complex.add_im, RCLike.star_def, Complex.conj_im,
        Complex.one_im]
      ring
  rw [hden, div_one]
  rw [show r * star r = (Complex.normSq r : ℂ) from Complex.mul_conj r]
  norm_num
  linarith

/-- A margin-window sample refutes positive semidefiniteness of the one-node
augmented boundary Gram. -/
theorem continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ (2 : ℕ) ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 => (1 / 2 : ℂ) + I * (t : ℂ))).PosSemidef := by
  rw [continuedXiWardFourUnitBoundaryGram_posSemidef_iff_schur]
  intro h
  have hd := h.diag_nonneg (i := 0)
  rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hd
  linarith [hd.1,
    continuedXiWardFourUnitSchurDefect_marginWindow_diag_re_neg q ht]

/-! ## The sampled Ward-matrix law -/

/-- Four-unit augmented Gram positivity for all finite packets drawn from `S`
on the Euler edge. -/
def ContinuedXiWardSampledBoundaryGramLaw (S : Set ℝ) : Prop :=
  ∀ {n : ℕ} (height : Fin n → ℝ), (∀ i, height i ∈ S) →
    (continuedXiWardFourUnitBoundaryGram
      (fun i => (1 / 2 : ℂ) + I * (height i : ℂ))).PosSemidef

/-- Detection cover of the positive heights only.  Every strict-right pair has
an upper representative, so this one-sided covering already carries the full
refutation power. -/
def XiWardUpperDetectionCover (S : Set ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → ∃ t ∈ S, (t + y) ^ (2 : ℕ) ≤ xiWardZeroFreeMargin y / 2

theorem XiWardDetectionCover.upper {S : Set ℝ}
    (h : XiWardDetectionCover S) : XiWardUpperDetectionCover S :=
  fun y _ => h y

theorem continuedXiWardSampledBoundaryGramLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardSampledBoundaryGramLaw S := by
  intro n height _
  apply riemannHypothesis_iff_continuedXiWardFourUnitBoundaryGramLaw.mp hRH
  intro i
  norm_num [Complex.add_re, Complex.mul_re]

theorem riemannHypothesis_of_continuedXiWardSampledBoundaryGramLaw
    {S : Set ℝ} (hcov : XiWardUpperDetectionCover S)
    (hlaw : ContinuedXiWardSampledBoundaryGramLaw S) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im q.2
  exact continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef q htwin
    (hlaw (fun _ : Fin 1 => t) (fun _ => htS))

/-- **Sampled Ward-matrix completeness law.**  On every detection cover of the
positive heights, positivity of the sampled four-unit Ward matrices is exactly
RH. -/
theorem riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw
    {S : Set ℝ} (hcov : XiWardUpperDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardSampledBoundaryGramLaw S :=
  ⟨fun hRH =>
    continuedXiWardSampledBoundaryGramLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardSampledBoundaryGramLaw hcov⟩

/-- **Prime-log sampled Ward-matrix completeness.**  Past an explicit cutoff,
positivity of the four-unit Ward matrices on finite packets drawn from the
signed prime logarithms and one finite grid is exactly RH: the requested `W_P`
positivity need only be proved on the arithmetic sample family. -/
theorem exists_cutoff_riemannHypothesis_iff_primeLogSampledBoundaryGramLaw :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      (RiemannHypothesis ↔
        ContinuedXiWardSampledBoundaryGramLaw (xiWardPrimeLogSampleSet Y)) := by
  obtain ⟨y₁, hy₁3, hcov⟩ := exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  exact ⟨y₁, hy₁3, fun Y hY =>
    riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw
      (hcov Y hY).upper⟩

end

end RHTower
