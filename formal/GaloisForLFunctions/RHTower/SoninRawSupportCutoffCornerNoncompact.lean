import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact

/-!
# The raw support-cutoff corner of the explicit prime factor is noncompact

In the multiplicative model `L²(ℝ_+^*, d*u)` the explicit place-addition map is
`T_p = 1 - p^{-1/2} D_p` with `(D_p f)(u) = f(u/p)`, and `P_λ` is multiplication by the indicator of
`(0, λ]`.  Under the logarithmic unitary `u = e^x` the space becomes `L²(ℝ)`, `D_p` becomes
translation by `-log p`, and `P_λ` becomes `logHalflineCutoff (log λ)`.  This file works in that
coordinate.

The corner `(1 - P) D P` carries the normalized indicators of the pairwise disjoint shell cells of
`(b - h, b]` to an orthonormal family: each cell is fixed by `P`, and its translate is annihilated
by `P` by the exact cutoff covariance `logHalflineCutoff_mul_logTranslationCLM`.  An orthonormal
sequence is weakly null while its images all have norm one, so the corner is **not compact** — and
neither is `(1 - P) T_p P`, which is a nonzero multiple of it.  In particular the corner is not
Hilbert–Schmidt, not trace class, and not of finite rank.
-/

namespace RHTower

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

/-- The source cells: pairwise disjoint subintervals of the window `(b - h, b]` swept by the
translation. -/
def rawCutoffCell (b h : ℝ) (n : ℕ) : Set ℝ := shellCell (b - h) b n

theorem measurableSet_rawCutoffCell (b h : ℝ) (n : ℕ) :
    MeasurableSet (rawCutoffCell b h n) := measurableSet_Ioc

theorem rawCutoffCell_measure_ne_top (b h : ℝ) (n : ℕ) :
    volume (rawCutoffCell b h n) ≠ ∞ := by
  rw [rawCutoffCell, shellCell, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem rawCutoffCell_measureReal_pos (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    0 < volume.real (rawCutoffCell b h n) := by
  have hlt : b - h < b := by linarith
  have hcell := shellLeft_lt_shellRight hlt n
  rw [rawCutoffCell, shellCell, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]
  linarith

/-- The normalized shell vectors of the swept window. -/
def rawCutoffVector (b h : ℝ) (n : ℕ) : SoninL2 :=
  normalizedIndicator (rawCutoffCell b h n) (measurableSet_rawCutoffCell b h n)
    (rawCutoffCell_measure_ne_top b h n)

theorem rawCutoffVector_orthonormal (b : ℝ) {h : ℝ} (hh : 0 < h) :
    Orthonormal ℂ (rawCutoffVector b h) := by
  have hlt : b - h < b := by linarith
  exact orthonormal_normalizedIndicator (measurableSet_rawCutoffCell b h)
    (rawCutoffCell_measure_ne_top b h) (fun n => rawCutoffCell_measureReal_pos b hh n)
    (shellCell_pairwiseDisjoint hlt)

/-- Each cell lies inside the cutoff window, so the cutoff fixes its vector. -/
theorem logHalflineCutoff_rawCutoffVector (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    logHalflineCutoff b (rawCutoffVector b h n) = rawCutoffVector b h n := by
  have hlt : b - h < b := by linarith
  refine indicatorCutoff_normalizedIndicator_of_subset _ _ measurableSet_Iic _ _ ?_
  intro x hx
  exact le_of_lt (lt_of_le_of_lt hx.2 (shellRight_lt hlt n))

/-- Each cell lies strictly above the shifted cutoff, so the shifted cutoff annihilates it. -/
theorem logHalflineCutoff_sub_rawCutoffVector (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    logHalflineCutoff (b - h) (rawCutoffVector b h n) = 0 := by
  have hlt : b - h < b := by linarith
  refine indicatorCutoff_normalizedIndicator_of_disjoint _ _ measurableSet_Iic _ _ ?_
  intro x hx hmem
  exact absurd (lt_of_lt_of_le (lt_shellLeft hlt n) hmem.1.le) (not_lt_of_ge hx)

theorem norm_logTranslationCLM (h : ℝ) (f : SoninL2) :
    ‖logTranslationCLM h f‖ = ‖f‖ := by
  simp [logTranslationCLM]

/-- **The raw support-cutoff corner of the prime dilation.** -/
def logRawCutoffCorner (b h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  (1 - logHalflineCutoff b) ∘L (logTranslationCLM (-h) ∘L logHalflineCutoff b)

theorem logRawCutoffCorner_apply (b h : ℝ) (f : SoninL2) :
    logRawCutoffCorner b h f
      = logTranslationCLM (-h) (logHalflineCutoff b f)
        - logHalflineCutoff b (logTranslationCLM (-h) (logHalflineCutoff b f)) := by
  simp [logRawCutoffCorner]

/-- On the shell vectors the corner is exactly the translation: nothing is lost. -/
theorem logRawCutoffCorner_rawCutoffVector (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    logRawCutoffCorner b h (rawCutoffVector b h n)
      = logTranslationCLM (-h) (rawCutoffVector b h n) := by
  have hfix := logHalflineCutoff_rawCutoffVector b hh n
  have hcov : logHalflineCutoff b ∘L logTranslationCLM (-h)
      = logTranslationCLM (-h) ∘L logHalflineCutoff (b + -h) :=
    logHalflineCutoff_mul_logTranslationCLM b (-h)
  have hcut : logHalflineCutoff b (logTranslationCLM (-h) (rawCutoffVector b h n)) = 0 := by
    have happ := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T (rawCutoffVector b h n)) hcov
    simp only [ContinuousLinearMap.comp_apply] at happ
    rw [happ, show b + -h = b - h by ring, logHalflineCutoff_sub_rawCutoffVector b hh n, map_zero]
  rw [logRawCutoffCorner_apply, hfix, hcut, sub_zero]

theorem norm_logRawCutoffCorner_rawCutoffVector (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ‖logRawCutoffCorner b h (rawCutoffVector b h n)‖ = 1 := by
  rw [logRawCutoffCorner_rawCutoffVector b hh n, norm_logTranslationCLM]
  exact (rawCutoffVector_orthonormal b hh).1 n

/-- **Card `B`: the raw support-cutoff corner is noncompact for every window and every positive
translation.**  Hence it is not Hilbert–Schmidt, not trace class, and not of finite rank. -/
theorem logRawCutoffCorner_not_isCompactOperator (b : ℝ) {h : ℝ} (hh : 0 < h) :
    ¬ IsCompactOperator (logRawCutoffCorner b h) := by
  have horth := rawCutoffVector_orthonormal b hh
  refine not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
    (logRawCutoffCorner b h) (rawCutoffVector b h) 1 1 (fun n => le_of_eq (horth.1 n))
    (Orthonormal.weakly_tendsto_zero horth) zero_lt_one
    (fun n => le_of_eq (norm_logRawCutoffCorner_rawCutoffVector b hh n).symm)

/-- The card's own operator `(1 - P) T_p P` with `T_p = 1 - c D_p`: the cutoff idempotence kills
the constant term, leaving `-c` times the raw corner. -/
theorem logPlaceAdditionCorner_apply (b h : ℝ) (c : ℂ) (f : SoninL2) :
    ((1 - logHalflineCutoff b) ∘L ((1 - c • logTranslationCLM (-h)) ∘L logHalflineCutoff b)) f
      = (logHalflineCutoff b f - c • logTranslationCLM (-h) (logHalflineCutoff b f))
        - logHalflineCutoff b (logHalflineCutoff b f
            - c • logTranslationCLM (-h) (logHalflineCutoff b f)) := by
  simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, smul_apply,
    map_sub, map_smul]
  module

/-- The card's own operator `(1 - P) T_p P` with `T_p = 1 - c D_p`: the cutoff idempotence kills
the constant term, leaving `-c` times the raw corner. -/
theorem logPlaceAdditionCorner_eq_smul (b h : ℝ) (c : ℂ) :
    (1 - logHalflineCutoff b) ∘L
        ((1 - c • logTranslationCLM (-h)) ∘L logHalflineCutoff b)
      = (-c) • logRawCutoffCorner b h := by
  apply ContinuousLinearMap.ext
  intro f
  have hfix : logHalflineCutoff b (logHalflineCutoff b f) = logHalflineCutoff b f :=
    congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
      (indicatorCutoff_idempotent (Iic b) measurableSet_Iic)
  have hsm : ((-c) • logRawCutoffCorner b h) f = (-c) • (logRawCutoffCorner b h f) := rfl
  rw [logPlaceAdditionCorner_apply, map_sub, map_smul, hfix, hsm, logRawCutoffCorner_apply]
  module

/-- Consequently the card's place-addition corner is noncompact whenever the dilation coefficient
is nonzero. -/
theorem logPlaceAdditionCorner_not_isCompactOperator (b : ℝ) {h : ℝ} (hh : 0 < h) {c : ℂ}
    (hc : c ≠ 0) :
    ¬ IsCompactOperator
      ((1 - logHalflineCutoff b) ∘L
        ((1 - c • logTranslationCLM (-h)) ∘L logHalflineCutoff b)) := by
  rw [logPlaceAdditionCorner_eq_smul]
  intro hcpt
  refine logRawCutoffCorner_not_isCompactOperator b hh ?_
  have hscale : logRawCutoffCorner b h = (-c)⁻¹ • ((-c) • logRawCutoffCorner b h) := by
    rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hc), one_smul]
  rw [hscale]
  exact hcpt.smul ((-c)⁻¹)

end

end RHTower
