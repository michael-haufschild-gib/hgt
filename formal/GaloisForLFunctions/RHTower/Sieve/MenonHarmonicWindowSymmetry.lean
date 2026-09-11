import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicWindowThresholdSplit
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeBlockSymmetry

/-!
# Reflection symmetry of the window and its exceptional set

The harmonic Ramare bilinear form has real arithmetic coefficients, so complex conjugation reverses
frequency and its norm is even.  Consequently the exceptional set of a threshold is symmetric, and
its measure is at most twice that of its nonnegative half.

This is what lets a large-values count stated for **positive** ordinates — which is how the
Heath--Brown/Montgomery receivers of `Sieve/MenonHeathBrown*` are stated — bound the whole window.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- Conjugation reverses frequency in the harmonic Ramare cofactor polynomial. -/
theorem conj_logPoly_harmonicRamareCofactorCoeff (P D : Finset ℕ) (w : ℝ) :
    (starRingEnd ℂ) (logPoly (harmonicRamareCofactorCoeff P) D w)
      = logPoly (harmonicRamareCofactorCoeff P) D (-w) := by
  classical
  rw [logPoly, logPoly, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul]
  congr 1
  · rw [harmonicRamareCofactorCoeff, harmonicMoebiusC]
    push_cast
    rw [map_div₀, map_div₀, map_add, map_one, map_intCast, map_natCast, map_natCast]
  · rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

/-- The norm of the harmonic Ramare bilinear form is even in frequency. -/
theorem norm_harmonicRamareBilinear_neg (P s : Finset ℕ) (w : ℝ) :
    ‖harmonicRamareBilinear P s (-w)‖ = ‖harmonicRamareBilinear P s w‖ := by
  classical
  have hconj : (starRingEnd ℂ) (harmonicRamareBilinear P s w)
      = harmonicRamareBilinear P s (-w) := by
    rw [harmonicRamareBilinear, harmonicRamareBilinear, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, conj_harmonicMoebiusPhase]
    congr 1
    exact conj_logPoly_harmonicRamareCofactorCoeff P _ w
  rw [← hconj, Complex.norm_conj]

/-- The exceptional set of an even-norm function is symmetric. -/
theorem neg_mem_windowSuperLevel {F : ℝ → ℂ} (hF : ∀ w : ℝ, ‖F (-w)‖ = ‖F w‖)
    {W V w : ℝ} (hw : w ∈ windowSuperLevel F W V) :
    -w ∈ windowSuperLevel F W V := by
  obtain ⟨hmem, hlt⟩ := hw
  rw [Set.mem_Icc] at hmem
  exact ⟨Set.mem_Icc.2 ⟨by linarith [hmem.2], by linarith [hmem.1]⟩, by
    simpa only [Set.mem_setOf_eq, hF w] using hlt⟩

/-- **Half the window suffices.**  The exceptional set of an even-norm function has at most twice
the measure of its nonnegative half. -/
theorem volume_windowSuperLevel_le_two_mul_nonneg
    {F : ℝ → ℂ} (hFc : Continuous F) (hF : ∀ w : ℝ, ‖F (-w)‖ = ‖F w‖) (W V : ℝ) :
    volume.real (windowSuperLevel F W V)
      ≤ 2 * volume.real (windowSuperLevel F W V ∩ Set.Ici 0) := by
  classical
  set S : Set ℝ := windowSuperLevel F W V with hSdef
  have hSm : MeasurableSet S := measurableSet_windowSuperLevel hFc W V
  have hSs : S ⊆ Set.Icc (-W) W := windowSuperLevel_subset F W V
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hSs)
    simp [Real.volume_Icc]
  have hPm : MeasurableSet (S ∩ Set.Ici 0) := hSm.inter measurableSet_Ici
  have hNm : MeasurableSet (S ∩ Set.Iio 0) := hSm.inter measurableSet_Iio
  have hcover : S = (S ∩ Set.Ici 0) ∪ (S ∩ Set.Iio 0) := by
    ext w
    constructor
    · intro hw
      rcases le_or_gt 0 w with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
    · rintro (hw | hw) <;> exact hw.1
  have hpre : S ∩ Set.Iio 0 ⊆ (fun v : ℝ => -1 * v) ⁻¹' (S ∩ Set.Ici 0) := by
    intro w hw
    refine ⟨?_, ?_⟩
    · simpa using neg_mem_windowSuperLevel hF hw.1
    · have hlt := hw.2
      simp only [Set.mem_Iio] at hlt
      simp only [Set.mem_Ici]
      linarith
  have hpresub : (fun v : ℝ => -1 * v) ⁻¹' (S ∩ Set.Ici 0) ⊆ Set.Icc (-W) W := by
    intro w hw
    have hmem : -w ∈ S := by simpa using hw.1
    have h2 := hSs hmem
    rw [Set.mem_Icc] at h2 ⊢
    constructor <;> linarith [h2.1, h2.2]
  have hprefin : volume ((fun v : ℝ => -1 * v) ⁻¹' (S ∩ Set.Ici 0)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hpresub)
    simp [Real.volume_Icc]
  have hle : volume.real (S ∩ Set.Iio 0) ≤ volume.real (S ∩ Set.Ici 0) := by
    have h1 := measureReal_mono hpre hprefin
    have h2 := volume_real_preimage_neg_mul_left (S := S ∩ Set.Ici 0) (c := 1) one_pos
    simp only [inv_one, one_mul] at h2
    exact h1.trans_eq h2
  have hunion : volume.real S ≤ volume.real (S ∩ Set.Ici 0) + volume.real (S ∩ Set.Iio 0) := by
    conv_lhs => rw [hcover]
    exact measureReal_union_le _ _
  linarith

end

end RHTower.Sieve
