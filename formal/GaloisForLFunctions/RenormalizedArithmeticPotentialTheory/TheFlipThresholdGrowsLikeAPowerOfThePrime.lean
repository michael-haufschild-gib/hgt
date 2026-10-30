import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.NoFixedOverlapSeesEveryFlip
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The flip threshold grows like a power of the prime

Write `M = ‖φ‖²`, `T(y) = ∫_y^∞ |φ̂(2πt)|² dt` and `E_m(c)` for the completed conductor energies.

* **Plancherel** (`setIntegral_Ioi_shellSpectrum_le`): `T(0) ≤ M/2`.
* **Conductor bounds** (`completedConductorEnergy_le_one`, `completedShellEnergy_le_log`,
  `completedShellEnergy_le_pow`): `E_m(c) ≤ (m/φ(m)) E_1(c/m)`, and if `T(y) ≤ B y⁻⁷` then
  `E_1(y) ≤ 1 + log⁺(1/y) + 4B/M` and, for `y ≥ 1`, `E_1(y) ≤ (4B/M) y⁻⁷`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis CompletedShell

section Generic

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
include hφ hsupp

/-- **Plancherel for the shell spectrum**: `∫ |φ̂(2πt)|² dt = ‖φ‖²`. -/
theorem integral_shellSpectrum_eq : ∫ t, shellSpectrum φ t = ∫ u, φ u ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hfc : HasCompactSupport (fun u => (φ u : ℂ)) := hφc.comp_left Complex.ofReal_zero
  have hf : ContDiff ℝ 2 (fun u => (φ u : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have h := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf hfc
  have hscale := Measure.integral_comp_mul_left
    (fun r : ℝ => ‖Zeta23.paperFT (fun u => (φ u : ℂ)) (r : ℂ)‖ ^ 2) (2 * π)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have hpi : |(2 * π)⁻¹| = 1 / (2 * π) := by
    rw [abs_of_pos (inv_pos.mpr Real.two_pi_pos), one_div]
  unfold shellSpectrum
  rw [hscale, hpi, smul_eq_mul, h]

/-- **The tail of the shell spectrum is at most half the mass.** -/
theorem setIntegral_Ioi_shellSpectrum_le {y : ℝ} (hy : 0 ≤ y) :
    ∫ t in Ioi y, shellSpectrum φ t ≤ (∫ u, φ u ^ 2) / 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hint : Integrable (shellSpectrum φ) := by
    have h0 := CriticalArithmeticCorrelationTheory.integrableOn_shellSpectrum_Ioi hφ hφc 0
    have h1 : IntegrableOn (shellSpectrum φ) (Iic 0) := by
      have hneg : IntegrableOn (fun t => shellSpectrum φ (-t)) (Ioi 0) := by
        simpa only [shellSpectrum_neg] using h0
      have := (integrableOn_Iic_iff_integrableOn_Iio).mpr
        ((hneg.comp_neg (μ := volume)).mono_set fun t (ht : t ∈ Iio 0) => by
          simp only [mem_preimage, mem_Ioi, Left.neg_pos_iff]; exact ht)
      simpa only [neg_neg] using this
    have := h1.union h0
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  have hsym : ∫ t in Ioi 0, shellSpectrum φ t = ∫ t in Iic 0, shellSpectrum φ t := by
    have := integral_comp_neg_Ioi 0 (shellSpectrum φ)
    simp only [shellSpectrum_neg, neg_zero] at this
    exact this
  have hsplit : ∫ t, shellSpectrum φ t =
      (∫ t in Iic 0, shellSpectrum φ t) + ∫ t in Ioi 0, shellSpectrum φ t := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have hmono : ∫ t in Ioi y, shellSpectrum φ t ≤ ∫ t in Ioi 0, shellSpectrum φ t :=
    setIntegral_mono_set hint.integrableOn (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Ioi_subset_Ioi hy))
  rw [integral_shellSpectrum_eq hφ hsupp] at hsplit
  linarith

omit hφ hsupp in
/-- A polynomial decay of the shell spectrum gives a polynomial tail. -/
theorem setIntegral_Ioi_shellSpectrum_le_pow {A : ℝ}
    (hA : ∀ t : ℝ, 0 < t → shellSpectrum φ t ≤ A * t ^ (-8 : ℝ)) {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi y, shellSpectrum φ t ≤ A / 7 * y ^ (-7 : ℝ) := by
  have hmaj : IntegrableOn (fun t : ℝ => A * t ^ (-8 : ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hy).const_mul A
  have hval : ∫ t in Ioi y, A * t ^ (-8 : ℝ) = A / 7 * y ^ (-7 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy]
    norm_num
    ring
  have hA0 : 0 ≤ A := by
    have h1 := hA 1 one_pos
    rw [Real.one_rpow, mul_one] at h1
    exact (shellSpectrum_nonneg 1).trans h1
  by_cases hint : IntegrableOn (shellSpectrum φ) (Ioi y)
  · rw [← hval]
    exact setIntegral_mono_on hint hmaj measurableSet_Ioi fun t ht => hA t (hy.trans ht)
  · rw [integral_undef hint]
    exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos hy _).le

end Generic

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
