import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeFourierMassAdmission

/-! The actual infinite Fourier--Bessel sum commutes with its original Mellin integral. -/
open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
open D4BMGlobalAngularResponse
noncomputable section

/-- One original complex diagonal Fourier mode with its actual Mellin weight. -/
def nativeFourierMellinTerm (q : XiZeroCopy) (s : ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  (y:ℂ)^(s-2)*amplitude (center q) y N^(2 : ℕ)

/-- Every original weighted mode is continuous throughout the positive height domain. -/
theorem nativeFourierMellinTerm_continuousOn (q : XiZeroCopy) (s : ℂ) (N : ℕ) :
    ContinuousOn (nativeFourierMellinTerm q s N) (Ioi (0:ℝ)) := by
  have hc : ContinuousOn (fun y : ℝ => (y:ℂ)^(s-2)) (Ioi (0:ℝ)) := by
    intro y hy
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hy))).continuousWithinAt
  exact hc.mul ((amplitude_continuousOn (center q) N).pow 2)

/-- Norms preserve the literal Mellin weight and the full coefficient norm square. -/
theorem nativeFourierMellinTerm_norm (q : XiZeroCopy) (s : ℂ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖nativeFourierMellinTerm q s N y‖ = y^(s.re-2)*‖amplitude (center q) y N‖^(2 : ℕ) := by
  rw [nativeFourierMellinTerm,norm_mul,norm_pow,Complex.norm_cpow_eq_rpow_re_of_pos hy]
  norm_num

/-- The original mode norms are summable at every positive height. -/
theorem nativeFourierMellinTerm_norm_summable (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (fun N => ‖nativeFourierMellinTerm q s N y‖) := by
  simp_rw [nativeFourierMellinTerm_norm q s _ hy]
  exact (amplitudeMass_summable (center q) hy).mul_left _

/-- Their full sum of norms is exactly the admitted weighted coefficient mass. -/
theorem nativeFourierMellinTerm_norm_tsum (q : XiZeroCopy) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∑' N, ‖nativeFourierMellinTerm q s N y‖) = y^(s.re-2)*amplitudeMass (center q) y := by
  simp_rw [nativeFourierMellinTerm_norm q s _ hy]
  exact tsum_mul_left

/-- The complete sum of mode norms is integrable in the actual Mellin chamber. -/
theorem nativeFourierMellin_norm_sum_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun y : ℝ => ∑' N, ‖nativeFourierMellinTerm q s N y‖) (Ioi (0:ℝ)) := by
  apply (nativeAmplitudeMass_mellin_integrable q s.re hs).congr_fun _ measurableSet_Ioi
  intro y hy
  exact (nativeFourierMellinTerm_norm_tsum q s hy).symm

/-- Each original complex mode has an absolutely admitted Mellin integral. -/
theorem nativeFourierMellinTerm_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) (N : ℕ) :
    IntegrableOn (nativeFourierMellinTerm q s N) (Ioi (0:ℝ)) := by
  apply (nativeFourierMellin_norm_sum_integrable q s hs).mono'
    ((nativeFourierMellinTerm_continuousOn q s N).aestronglyMeasurable measurableSet_Ioi)
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro y hy
  exact (nativeFourierMellinTerm_norm_summable q s hy).le_tsum N (fun _ _ => norm_nonneg _)

/-- Summability of integral norms is derived from the native full-source energy bounds. -/
theorem nativeFourierMellin_integral_norm_summable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun N => ∫ y in Ioi (0:ℝ), ‖nativeFourierMellinTerm q s N y‖) := by
  have hm (N : ℕ) : AEStronglyMeasurable (fun y => ‖nativeFourierMellinTerm q s N y‖)
      (volume.restrict (Ioi (0:ℝ))) := (nativeFourierMellinTerm_integrable q s hs N).norm.aestronglyMeasurable
  have hb : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), Summable (fun N => ‖nativeFourierMellinTerm q s N y‖) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => nativeFourierMellinTerm_norm_summable q s hy)
  exact (hasSum_integral_of_dominated_convergence
    (fun N y => ‖nativeFourierMellinTerm q s N y‖) hm
    (fun _ => ae_of_all _ (fun _ => by rw [norm_norm])) hb
    (nativeFourierMellin_norm_sum_integrable q s hs) (hb.mono fun _ h => h.hasSum)).summable

/-- The full complex diagonal sum itself is absolutely admitted without discarding phase. -/
theorem nativeFourierMellin_integrable (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun y : ℝ => (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) (Ioi (0:ℝ)) := by
  have he : (fun y : ℝ => (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
      fun y => ∑' N, nativeFourierMellinTerm q s N y := by
    funext y
    exact (tsum_mul_left).symm
  rw [he]
  apply (nativeFourierMellin_norm_sum_integrable q s hs).mono'
    (AEMeasurable.tsum (fun N => (nativeFourierMellinTerm_integrable q s hs N).aemeasurable)).aestronglyMeasurable
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun y hy => norm_tsum_le_tsum_norm (nativeFourierMellinTerm_norm_summable q s hy))

/-- The entire original Fourier--Bessel source commutes with its Mellin integral. -/
theorem nativeFourierMellin_integral_eq_tsum (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ))) =
      ∑' N, ∫ y in Ioi (0:ℝ), (y:ℂ)^(s-2)*amplitude (center q) y N^(2 : ℕ) := by
  have h := integral_tsum_of_summable_integral_norm (nativeFourierMellinTerm_integrable q s hs)
    (nativeFourierMellin_integral_norm_summable q s hs)
  have he (y : ℝ) : (∑' N, nativeFourierMellinTerm q s N y) =
      (y:ℂ)^(s-2)*(∑' N, amplitude (center q) y N^(2 : ℕ)) := tsum_mul_left
  simp_rw [he] at h
  exact h.symm

end
end RHTower.D4BMCuspProjection
