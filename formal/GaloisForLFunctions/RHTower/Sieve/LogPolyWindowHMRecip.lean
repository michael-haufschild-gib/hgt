import GaloisForLFunctions.RHTower.Sieve.PlainKernelMassRecip
import GaloisForLFunctions.RHTower.Sieve.LogPolySetScaling

/-!
# Halász–Montgomery for a Gallagher polynomial, with the reciprocal kernel mass

The same repackaging as `Sieve/LogPolySetScaling` and `Sieve/LogPolyWindowHM`, but over
`Sieve/PlainKernelMassRecip.setIntegral_normSq_dirPoly_le_recip`: the diagonal term is now
`N·log T` and the set's measure is multiplied by `√T·log T` rather than by `N`.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The Halász–Montgomery mass at height `T` for a polynomial of length `N` over a set of measure
`volE`. -/
def hmMassRecip (N : ℕ) (T volE : ℝ) : ℝ :=
  2 * (N : ℝ) + plainKernelFarConst N T * volE
    + 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T)

/-- **Lemma 2.6 for a Gallagher polynomial, in the Dirichlet variable.** -/
theorem setIntegral_normSq_logPoly_le_recip (a : ℕ → ℂ) {D : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc 1 N) {S : Set ℝ} (hS : MeasurableSet S) {T : ℝ} (hT : 1 ≤ T)
    (hSs : S ⊆ Set.Icc (-T) T) {Ω : ℝ} (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹ * (hmMassRecip N T (volume.real S) * (Ω ^ 2 * (D.card : ℝ))) := by
  classical
  rw [setIntegral_normSq_logPoly_eq a hD hS]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (setIntegral_normSq_dirPoly_le_recip hN (finCoeff D a N) hT hS hSs).trans ?_
  have hmass0 : (0 : ℝ) ≤ hmMassRecip N T (volume.real S) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ volume.real S := ENNReal.toReal_nonneg
    have h3 : (0 : ℝ) ≤ plainKernelFarConst N T := plainKernelFarConst_nonneg N hT
    have h4 : (0 : ℝ) ≤ Real.log (2 + 2 * T) := Real.log_nonneg (by linarith)
    have p1 : (0 : ℝ) ≤ plainKernelFarConst N T * volume.real S := mul_nonneg h3 h2
    have p2 : (0 : ℝ) ≤ 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T) :=
      mul_nonneg (by positivity) h4
    rw [hmMassRecip]
    linarith
  exact mul_le_mul_of_nonneg_left (sum_normSq_finCoeff_le hΩ ha) hmass0

/-- **Lemma 2.6 over a measurable set of Gallagher frequencies.** -/
theorem setIntegral_normSq_logPoly_le_HM_window_recip (a : ℕ → ℂ) {D : Finset ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hD : D ⊆ Finset.Icc 1 N) {E : Set ℝ} (hE : MeasurableSet E) {W : ℝ}
    (hW : 1 ≤ W) (hEs : E ⊆ Set.Icc (-W) W) {Ω : ℝ} (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in E, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
            * (Ω ^ 2 * (D.card : ℝ))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  have hT : (1 : ℝ) ≤ 2 * Real.pi * W := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hW, h3]
  set S : Set ℝ := (fun v : ℝ => (2 * Real.pi)⁻¹ * v) ⁻¹' E with hSdef
  have hSm : MeasurableSet S := (measurable_const_mul _) hE
  have hpre : (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S = E := by
    ext w
    simp only [hSdef, Set.mem_preimage]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hSs : S ⊆ Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W) := by
    intro v hv
    have hmem : (2 * Real.pi)⁻¹ * v ∈ Set.Icc (-W) W := hEs hv
    rw [Set.mem_Icc] at hmem ⊢
    obtain ⟨h1, h2⟩ := hmem
    constructor
    · have := mul_le_mul_of_nonneg_left h1 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h2 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
  have hvol : volume.real S = 2 * Real.pi * volume.real E := by
    rw [hSdef, volume_real_preimage_mul_left hinv, inv_inv]
  have hbase := setIntegral_normSq_logPoly_le_recip a hN hD hSm hT hSs hΩ ha
  rw [hpre, hvol] at hbase
  exact hbase

end

end RHTower.Sieve
