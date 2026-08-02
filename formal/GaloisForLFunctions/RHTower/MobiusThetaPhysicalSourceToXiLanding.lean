import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity

/-!
# Physical Möbius--theta source landing in Xi

This module realizes the high-exponent reciprocal-zeta multiplier before spectral evaluation.
The source is an absolutely convergent `L²` sum of logarithmic translates of the canonical theta
source, with coefficients supplied by the power-supported Möbius arithmetic function.  Plancherel
then proves that its real Fourier boundary is `ζ(m(1/2+it))⁻¹ XiC(t)`.

Unlike the earlier value-level complete-resolution vector, `mobiusThetaRung m` contains no `XiC`,
spectral parameter, or zero.  Thus the theorem is an unconditional physical source-to-Xi landing,
not scalar multiplication by a preselected target value.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries
open scoped BigOperators LSeries.notation Moebius FourierTransform SchwartzMap

noncomputable section
namespace RHTower

/-- Ambient Hilbert space of the physical logarithmic source. -/
abbrev MobiusThetaSourceL2 := Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)

/-- One half-density, power-supported Möbius coefficient acting on the corresponding logarithmic
translate of the canonical theta source. -/
def mobiusThetaRungTerm (m n : ℕ) : MobiusThetaSourceL2 :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
    MellinL2.additiveTranslationUnitary
      (-Real.log n * MellinL2.spectralNormalization) xiThetaSourceL2

theorem norm_mobiusThetaRungTerm (m n : ℕ) :
    ‖mobiusThetaRungTerm m n‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n‖ *
        ‖xiThetaSourceL2‖ := by
  rw [mobiusThetaRungTerm, norm_smul, LinearIsometryEquiv.norm_map]

theorem summable_mobiusThetaRungTerm {m : ℕ} (hm : m ≠ 0)
    (hmhalf : 1 / (m : ℝ) < (1 / 2 : ℂ).re) :
    Summable (mobiusThetaRungTerm m) := by
  have hcoeff := LSeriesSummable_mPart_moebius hm hmhalf
  unfold LSeriesSummable at hcoeff
  apply Summable.of_norm
  simpa only [norm_mobiusThetaRungTerm] using hcoeff.norm.mul_right ‖xiThetaSourceL2‖

theorem summable_mobiusThetaRungTerm_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    Summable (mobiusThetaRungTerm m) := by
  apply summable_mobiusThetaRungTerm (by omega)
  norm_num [Complex.div_re]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by positivity
  rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- Target-free physical Möbius--theta rung.  For `m ≥ 3` this is an absolutely convergent
Hilbert-space series. -/
def mobiusThetaRung (m : ℕ) : MobiusThetaSourceL2 :=
  ∑' n : ℕ, mobiusThetaRungTerm m n

/-- Fourier-side term obtained from the physical translate by Plancherel. -/
def mobiusThetaFourierTerm (m n : ℕ) : MobiusThetaSourceL2 :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
    MellinL2.fourierPhaseMulUnitary
      (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2

theorem norm_mobiusThetaFourierTerm (m n : ℕ) :
    ‖mobiusThetaFourierTerm m n‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n‖ *
        ‖xiThetaFourierSourceL2‖ := by
  rw [mobiusThetaFourierTerm, norm_smul, LinearIsometryEquiv.norm_map]

theorem summable_norm_mobiusThetaFourierTerm {m : ℕ} (hm : 3 ≤ m) :
    Summable (fun n : ℕ => ‖mobiusThetaFourierTerm m n‖) := by
  have hcoeff := LSeriesSummable_mPart_moebius
    (s := (1 / 2 : ℂ)) (by omega : m ≠ 0) (by
      norm_num [Complex.div_re]
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have hmPos : (0 : ℝ) < m := by positivity
      rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith)
  unfold LSeriesSummable at hcoeff
  simpa only [norm_mobiusThetaFourierTerm] using
    hcoeff.norm.mul_right ‖xiThetaFourierSourceL2‖

theorem summable_mobiusThetaFourierTerm {m : ℕ} (hm : 3 ≤ m) :
    Summable (mobiusThetaFourierTerm m) :=
  Summable.of_norm (summable_norm_mobiusThetaFourierTerm hm)

/-- Plancherel commutes with the physical Möbius source sum term by term. -/
theorem fourier_mobiusThetaRung {m : ℕ} (hm : 3 ≤ m) :
    𝓕 (mobiusThetaRung m) =
      ∑' n : ℕ, mobiusThetaFourierTerm m n := by
  rw [mobiusThetaRung]
  change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (∑' n : ℕ, mobiusThetaRungTerm m n) = _
  calc
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (∑' n : ℕ, mobiusThetaRungTerm m n) =
        ∑' n : ℕ, (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
          (mobiusThetaRungTerm m n) := by
      exact ContinuousLinearMap.map_tsum
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
        (summable_mobiusThetaRungTerm_of_three_le hm)
    _ = _ := by
      apply tsum_congr
      intro n
      rw [mobiusThetaRungTerm, mobiusThetaFourierTerm, map_smul]
      congr 1
      change 𝓕 (MellinL2.additiveTranslationUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaSourceL2) = _
      rw [MellinL2.fourier_additiveTranslation, fourier_xiThetaSourceL2]

theorem fourierPhase_neg_log_normalized (n : ℕ) (t : ℝ) :
    MellinL2.fourierPhase
        (-Real.log n * MellinL2.spectralNormalization) t =
      MellinL2.mellinCharacter n (-t) := by
  rw [show -Real.log n * MellinL2.spectralNormalization =
      Real.log n * MellinL2.spectralNormalization * (-1) by ring]
  unfold MellinL2.fourierPhase MellinL2.spectralNormalization
    MellinL2.mellinCharacter
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Half-density Dirichlet coefficient times the physical translation character is the centered
Dirichlet coefficient. -/
theorem LSeries_term_half_mul_mellinCharacter_neg
    (f : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term f (1 / 2 : ℂ) n * MellinL2.mellinCharacter n (-t) =
      LSeries.term f ((1 / 2 : ℂ) + (t : ℂ) * I) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    MellinL2.mellinCharacter_eq_cpow n hnpos (-t)]
  rw [show I * ((-t : ℝ) : ℂ) = -((t : ℂ) * I) by push_cast; ring,
    Complex.cpow_neg]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  norm_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem summable_mobiusThetaFourierValueTerm {m : ℕ} (hm : 3 ≤ m) (t : ℝ) :
    Summable (fun n : ℕ =>
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
        MellinL2.mellinCharacter n (-t) * XiC (t : ℂ)) := by
  have hc : Summable (LSeries.term
      (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ)) := by
    exact LSeriesSummable_mPart_moebius
      (s := (1 / 2 : ℂ)) (by omega : m ≠ 0) (by
        norm_num [Complex.div_re]
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
        have hmPos : (0 : ℝ) < m := by positivity
        rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith)
  apply Summable.of_norm
  simpa only [norm_mul, MellinL2.norm_mellinCharacter, one_mul, mul_assoc] using
    hc.norm.mul_right ‖XiC (t : ℂ)‖

theorem tsum_enorm_mobiusThetaFourierTerm_ne_top {m : ℕ} (hm : 3 ≤ m) :
    ∑' n : ℕ, ‖mobiusThetaFourierTerm m n‖ₑ ≠ ⊤ := by
  simp only [enorm_eq_nnnorm]
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simpa only [coe_nnnorm] using summable_norm_mobiusThetaFourierTerm hm

theorem mobiusThetaFourierTerm_ae (m n : ℕ) :
    mobiusThetaFourierTerm m n =ᵐ[volume]
      fun t : ℝ =>
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
          MellinL2.mellinCharacter n (-t) * XiC (t : ℂ) := by
  change
    (LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
      MellinL2.fourierPhaseMulUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2) =ᵐ[volume] _
  have hphase :
      MellinL2.fourierPhaseMulUnitary
          (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2 =ᵐ[volume]
        fun t : ℝ =>
          MellinL2.fourierPhase
              (-Real.log n * MellinL2.spectralNormalization) t *
            xiThetaFourierSourceL2 t := by
    change MellinL2.fourierPhaseMulAux
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2 =ᵐ[volume] _
    exact MellinL2.fourierPhaseMulAux_ae _ _
  filter_upwards [Lp.coeFn_smul
      (LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n)
      (MellinL2.fourierPhaseMulUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2),
    hphase, xiThetaFourierSourceL2_ae] with t hsmul hphase_t hxi
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hphase_t, hxi, fourierPhase_neg_log_normalized]
  ring

/-- **Unconditional physical source-to-Xi landing on the Plancherel boundary.**  For every
high-exponent rung, the Fourier transform of the target-free translated theta source is the full
centered Xi function times the corresponding reciprocal-zeta multiplier, almost everywhere on
the real spectral line. -/
theorem fourier_mobiusThetaRung_ae {m : ℕ} (hm : 3 ≤ m) :
    ((𝓕 (mobiusThetaRung m) : MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ =>
        (riemannZeta ((m : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹ * XiC (t : ℂ) := by
  have hfourier := fourier_mobiusThetaRung hm
  rw [hfourier]
  have hcoe :
      (((∑' n : ℕ, mobiusThetaFourierTerm m n) : MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
        fun t : ℝ => ∑' n : ℕ, mobiusThetaFourierTerm m n t :=
    Lp.coeFn_tsum (tsum_enorm_mobiusThetaFourierTerm_ne_top hm)
  have hterm : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      mobiusThetaFourierTerm m n t =
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
          MellinL2.mellinCharacter n (-t) * XiC (t : ℂ) :=
    ae_all_iff.mpr fun n => mobiusThetaFourierTerm_ae m n
  filter_upwards [hcoe, hterm] with t hcoe_t hterm_t
  rw [hcoe_t]
  calc
    (∑' n : ℕ, mobiusThetaFourierTerm m n t) =
        ∑' n : ℕ,
          LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
              ((1 / 2 : ℂ) + (t : ℂ) * I) n * XiC (t : ℂ) := by
      apply tsum_congr
      intro n
      rw [hterm_t n, LSeries_term_half_mul_mellinCharacter_neg]
    _ = LSeries (↗(mPart m (μ : ArithmeticFunction ℤ)))
          ((1 / 2 : ℂ) + (t : ℂ) * I) * XiC (t : ℂ) := tsum_mul_right
    _ = (riemannZeta ((m : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹ *
          XiC (t : ℂ) := by
      rw [LSeries_mPart_moebius (by omega : m ≠ 0)]
      norm_num [Complex.div_re]
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have hmPos : (0 : ℝ) < m := by positivity
      rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

end RHTower
