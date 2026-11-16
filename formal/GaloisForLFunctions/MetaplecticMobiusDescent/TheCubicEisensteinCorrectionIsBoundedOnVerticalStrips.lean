import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicIncomingResidue
import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
# Uniform vertical bounds for the cubic Eisenstein correction

On a fixed compact height interval above one, the cusp forcing grows at most linearly
in the spectral parameter. Self-adjointness divides this by
`|Im(s(2-s))| = 2 |Re s-1| |Im s|`. Thus the actual `L²` correction is bounded
on every bounded real strip separated from `Re s=1`, for `|Im s| ≥ 1`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

/-- On a compact height interval above one, vertical oscillation has unit norm. -/
theorem compactHeightExp_norm_le (a b : ℝ) (ha : 1 < a)
    (B : ℝ) (hB : 0 ≤ B) (s : ℂ) (hs : s.re ≤ B) :
    ‖NormedSpace.exp (s • compactLogProfile a b (by linarith))‖ ≤
      Real.exp (B * Real.log b) := by
  apply (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr
  intro v
  have hv : 0 < (v : ℝ) := lt_of_lt_of_le (by linarith : 0 < a) v.2.1
  have hv1 : 1 ≤ (v : ℝ) := le_trans ha.le v.2.1
  have hexp := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a b (by linarith))
  change (NormedSpace.exp (s • compactLogProfile a b (by linarith))) v =
    NormedSpace.exp ((s • compactLogProfile a b (by linarith)) v) at hexp
  rw [hexp, ← Complex.exp_eq_exp_ℂ]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, compactLogProfile,
    ContinuousMap.coe_mk, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (mul_le_mul hs (Real.log_le_log hv v.2.2)
    (Real.log_nonneg hv1) hB)

/-- The actual compact-height forcing has at most linear vertical growth. -/
theorem kernelL2Defect_norm_le_linear (a b : ℝ) (ha : 1 < a) (hab : a < b)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ B →
      ‖kernelL2Defect a b (by linarith) hab s‖ ≤ C * (1 + ‖s‖) := by
  set E : ℝ := Real.exp (B * Real.log b)
  set D : ℝ := ‖compactDefectSecond a b‖ + 2 * ‖compactDefectFirst a b‖
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨‖compactProfileL2 a b hab.le‖ * E * D, by positivity, ?_⟩
  intro s hs
  have hlin : ‖(2 : ℂ) * s - 1‖ ≤ 2 * ‖s‖ + 1 := by
    calc ‖(2 : ℂ) * s - 1‖ ≤ ‖(2 : ℂ) * s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have hrest : ‖compactDefectSecond a b + (2 * s - 1) • compactDefectFirst a b‖ ≤
      D * (1 + ‖s‖) := by
    calc
      _ ≤ ‖compactDefectSecond a b‖ + ‖(2 * s - 1) • compactDefectFirst a b‖ := norm_add_le _ _
      _ = ‖compactDefectSecond a b‖ + ‖(2 : ℂ) * s - 1‖ * ‖compactDefectFirst a b‖ := by rw [norm_smul]
      _ ≤ ‖compactDefectSecond a b‖ + (2 * ‖s‖ + 1) * ‖compactDefectFirst a b‖ := by
        gcongr
      _ ≤ D * (1 + ‖s‖) := by
        dsimp only [D]
        nlinarith only [norm_nonneg (compactDefectFirst a b),
          mul_nonneg (norm_nonneg (compactDefectSecond a b)) (norm_nonneg s)]
  have hprofile : ‖compactDefectProfile a b (by linarith) s‖ ≤ E * D * (1 + ‖s‖) := by
    rw [compactDefectProfile]
    calc
      _ ≤ ‖NormedSpace.exp (s • compactLogProfile a b (by linarith))‖ *
          ‖compactDefectSecond a b + (2 * s - 1) • compactDefectFirst a b‖ := norm_mul_le _ _
      _ ≤ E * (D * (1 + ‖s‖)) :=
        mul_le_mul (compactHeightExp_norm_le a b ha B hB s hs) hrest (norm_nonneg _) hE
      _ = _ := by ring
  rw [← compactProfileL2_actual_defect a b (by linarith) hab s]
  calc
    _ ≤ ‖compactProfileL2 a b hab.le‖ * ‖compactDefectProfile a b (by linarith) s‖ :=
      (compactProfileL2 a b hab.le).le_opNorm _
    _ ≤ ‖compactProfileL2 a b hab.le‖ * (E * D * (1 + ‖s‖)) :=
      mul_le_mul_of_nonneg_left hprofile (norm_nonneg (compactProfileL2 a b hab.le))
    _ = _ := by ring

/-- The imaginary spectral parameter controls the actual Eisenstein correction. -/
theorem kernelEisensteinL2Correction_im_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (s : ℂ) (hs : s.re ≠ 1) (hi : s.im ≠ 0) :
    |(kernelEisensteinSpectralParameter s).im| *
      ‖kernelEisensteinL2Correction a b ha hab s‖ ≤ ‖kernelL2Defect a b ha hab s‖ := by
  obtain ⟨u, hu, hLu⟩ := kernelEnergyLaplacian.mem_graph_iff.mp
    (kernelEisensteinL2Correction_graph_nonreal a b ha hab s hs hi)
  have h := HTGeometry.norm_sub_smul_lower_bound kernelEnergyLaplacian_selfAdjoint
    (kernelEisensteinSpectralParameter s) u
  rw [hu, hLu, add_sub_cancel_right] at h
  exact h

/-- Uniform `L²` control on every bounded real strip separated from `Re s=1`,
at all imaginary heights of absolute value at least one. -/
theorem kernelEisensteinL2Correction_vertical_bound (a b : ℝ) (ha : 1 < a) (hab : a < b)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ B → δ ≤ |s.re - 1| → 1 ≤ |s.im| →
      ‖kernelEisensteinL2Correction a b (by linarith) hab s‖ ≤ C := by
  obtain ⟨D, hD, hdef⟩ := kernelL2Defect_norm_le_linear a b ha hab B hB
  refine ⟨D * (B + 2) / (2 * δ), by positivity, ?_⟩
  intro s hσ hd ht
  have hσ1 : s.re ≠ 1 := by
    intro he
    rw [he, sub_self, abs_zero] at hd
    linarith
  have hi : s.im ≠ 0 := by intro he; rw [he, abs_zero] at ht; linarith
  have him : (kernelEisensteinSpectralParameter s).im = -2 * (s.re - 1) * s.im := by
    simp only [kernelEisensteinSpectralParameter, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have habs : |(kernelEisensteinSpectralParameter s).im| = 2 * |s.re - 1| * |s.im| := by
    rw [him, abs_mul, abs_mul]
    norm_num
  have hnorm : 1 + ‖s‖ ≤ (B + 2) * |s.im| := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    nlinarith only [hn, hσ, ht, mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ B + 1)]
  have hc := kernelEisensteinL2Correction_im_bound a b (by linarith) hab s hσ1 hi
  rw [habs] at hc
  have hforces := (hdef s ((le_abs_self _).trans hσ)).trans
    (mul_le_mul_of_nonneg_left hnorm hD)
  have hleft : 2 * δ * ‖kernelEisensteinL2Correction a b (by linarith) hab s‖ * |s.im| ≤
      D * (B + 2) * |s.im| := by
    calc
      _ ≤ 2 * |s.re - 1| * |s.im| *
          ‖kernelEisensteinL2Correction a b (by linarith) hab s‖ := by
        nlinarith only [mul_le_mul_of_nonneg_right hd
          (mul_nonneg (norm_nonneg (kernelEisensteinL2Correction a b (by linarith) hab s)) (abs_nonneg s.im))]
      _ ≤ _ := by simpa only [mul_assoc] using hc.trans hforces
  have hcancel := (mul_le_mul_iff_left₀ (lt_of_lt_of_le zero_lt_one ht)).mp hleft
  exact (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr (by nlinarith only [hcancel])

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
