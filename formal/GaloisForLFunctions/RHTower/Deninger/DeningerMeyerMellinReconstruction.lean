import GaloisForLFunctions.HTGeometry.MellinRegularStripLinear
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFullXiJetAdmissionBoundary
import Mathlib.Analysis.Fourier.Inversion

/-!+# Reconstruction in the original all-weight Meyer source

An entire Mellin datum rapidly decreasing on every closed vertical strip
has an inverse in the original all-weight logarithmic source. Contour
translation controls every weighted derivative. No spectral admission or
source regularity assumption is imposed on the inverse.
-/

open Complex MeasureTheory Filter Set Topology Asymptotics
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Rapid vertical decay on all strips, with no uniformity required as the
strip widens. -/
def DeningerEntireMellinRegular (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, MellinRegularStrip F a b

namespace DeningerEntireMellinRegular

variable {F : ℂ → ℂ}

theorem differentiable (hF : DeningerEntireMellinRegular F) :
    Differentiable ℂ F := fun z =>
  (hF (z.re - 1) (z.re + 1)).diff z (by linarith) (by linarith)

theorem neg_mul_id (hF : DeningerEntireMellinRegular F) :
    DeningerEntireMellinRegular (fun s => -s * F s) := by
  intro a b
  convert ((hF a b).mul_id).const_mul (-1) using 1
  ext s
  ring

theorem signedPow (hF : DeningerEntireMellinRegular F) (n : ℕ) :
    DeningerEntireMellinRegular (fun s => (-s)^n * F s) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
      convert ih.neg_mul_id using 1
      ext s
      ring

theorem inverse_line_eq (hF : DeningerEntireMellinRegular F)
    (a b t : ℝ) :
    mellinInv a F (Real.exp t) = mellinInv b F (Real.exp t) :=
  (hF (min a b - 1) (max a b + 1)).mellinInv_eq
    (by have := min_le_left a b; linarith)
    (by have := le_max_left a b; linarith)
    (by have := min_le_right a b; linarith)
    (by have := le_max_right a b; linarith) (Real.exp_pos t)

end DeningerEntireMellinRegular

/-- Inverse Mellin transform in logarithmic radius. The abscissa one is
arbitrary, by contour translation. -/
def deningerMeyerInverseMellinProfile (F : ℂ → ℂ) (t : ℝ) : ℂ :=
  mellinInv 1 F (Real.exp t)

theorem deningerMeyerInverseMellinProfile_hasDerivAt
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (t : ℝ) :
    HasDerivAt (deningerMeyerInverseMellinProfile F)
      (deningerMeyerInverseMellinProfile (fun s => -s * F s) t) t := by
  have h := ((hF 0 2).hasDerivAt_mellinInv
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    one_ne_zero (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
  have he : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  simpa [deningerMeyerInverseMellinProfile, Function.comp_def,
    Complex.real_smul, he] using! h

theorem iteratedDeriv_deningerMeyerInverseMellinProfile
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (n : ℕ) :
    iteratedDeriv n (deningerMeyerInverseMellinProfile F) =
      deningerMeyerInverseMellinProfile (fun s => (-s)^n * F s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [(deningerMeyerInverseMellinProfile_hasDerivAt (hF.signedPow n) t).deriv]
      congr 1
      funext s
      ring

theorem deningerMeyerInverseMellinProfile_strongLogDecay
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) :
    DeningerMeyerStrongLogDecay (deningerMeyerInverseMellinProfile F) where
  smooth := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [iteratedDeriv_deningerMeyerInverseMellinProfile hF n]
    exact fun t => (deningerMeyerInverseMellinProfile_hasDerivAt (hF.signedPow n) t).differentiableAt
  decayTop := by
    intro n a
    rw [iteratedDeriv_deningerMeyerInverseMellinProfile hF n]
    let C := (1 / (2 * Real.pi)) *
      ∫ y : ℝ, ‖(-((a : ℂ) + y * I))^n * F ((a : ℂ) + y * I)‖
    apply IsBigO.of_bound C
    filter_upwards with t
    rw [deningerMeyerInverseMellinProfile,
      (hF.signedPow n).inverse_line_eq 1 a t]
    have h := GaloisForLFunctions.HTGeometry.norm_mellinInv_le
      (Ψ := fun s => (-s)^n * F s) a (Real.exp_pos t)
    simpa [C, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (-a)),
      mul_assoc, mul_left_comm, mul_comm] using h
  decayBot := by
    intro n b
    rw [iteratedDeriv_deningerMeyerInverseMellinProfile hF n]
    let C := (1 / (2 * Real.pi)) *
      ∫ y : ℝ, ‖(-(((-b : ℝ) : ℂ) + y * I))^n * F (((-b : ℝ) : ℂ) + y * I)‖
    apply IsBigO.of_bound C
    filter_upwards with t
    rw [deningerMeyerInverseMellinProfile,
      (hF.signedPow n).inverse_line_eq 1 (-b) t]
    have h := GaloisForLFunctions.HTGeometry.norm_mellinInv_le
      (Ψ := fun s => (-s)^n * F s) (-b) (Real.exp_pos t)
    simpa [C, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) b),
      mul_assoc, mul_left_comm, mul_comm] using h

/-- The reconstructed profile belongs to the actual Meyer source. -/
def deningerMeyerInverseMellinSource (F : ℂ → ℂ)
    (hF : DeningerEntireMellinRegular F) : DeningerMeyerStrongLogTarget :=
  ⟨deningerMeyerInverseMellinProfile F,
    deningerMeyerInverseMellinProfile_strongLogDecay hF⟩

theorem deningerMeyerInverseMellinSource_weighted_fourier
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (σ : ℝ) :
    deningerMeyerWeightedLogProfile σ (deningerMeyerInverseMellinSource F hF) =
      𝓕 (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * I)) := by
  funext t
  change (Real.exp (σ * t) : ℂ) * mellinInv 1 F (Real.exp t) = _
  rw [Complex.ofReal_exp, hF.inverse_line_eq 1 σ t, mellinInv_eq_fourierInv σ F (Real.exp_pos t),
    Real.log_exp, Real.fourierInv_eq_fourier_neg, neg_neg, smul_eq_mul]
  have he : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  rw [Complex.cpow_def_of_ne_zero he, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp,
    ← mul_assoc, ← Complex.exp_add]
  simp [Complex.ofReal_mul, mul_comm]

/-- Inversion recovers the prescribed entire datum, on every vertical line. -/
theorem deningerMeyerInverseMellinSource_mellin
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerInverseMellinSource F hF) s = F s := by
  let φ : ℝ → ℂ := fun y => F ((s.re : ℂ) + 2 * Real.pi * y * I)
  have hc : Continuous φ := hF.differentiable.continuous.comp (by fun_prop)
  have hi : Integrable φ := by
    have hline := (hF (s.re - 1) (s.re + 1)).integrable_line
      (c := s.re) (by linarith) (by linarith)
    convert hline.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0) using 1
    funext y
    push_cast
    ring
  have hFi : Integrable (𝓕 φ) := by
    rw [← deningerMeyerInverseMellinSource_weighted_fourier hF s.re]
    exact integrable_deningerMeyerWeightedLogProfile
      (deningerMeyerInverseMellinSource F hF).property s.re
  have hinv := congrFun (hc.fourierInv_fourier_eq hi hFi) (s.im / (2 * Real.pi))
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  calc deningerMeyerStrongLogMellin (deningerMeyerInverseMellinSource F hF) s
      = 𝓕 (deningerMeyerWeightedLogProfile s.re
          (deningerMeyerInverseMellinSource F hF)) (-s.im / (2 * Real.pi)) := by
        conv_lhs => rw [hs]
        exact deningerMeyerStrongLogMellin_eq_fourier_weighted _ _ _
    _ = F s := by
      rw [deningerMeyerInverseMellinSource_weighted_fourier hF]
      change 𝓕 (𝓕 φ) (-s.im / (2 * Real.pi)) = F s
      rw [← neg_div] at hinv
      rw [hinv]
      change F ((s.re : ℂ) + 2 * Real.pi * (s.im / (2 * Real.pi) : ℝ) * I) = F s
      congr 1
      push_cast
      conv_rhs => rw [hs]
      field_simp

end
end RHTower
