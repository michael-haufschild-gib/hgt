import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionMasks
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialMellinBound
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleSign

/-!
# Bounded even deletion from full Weil positivity

The two signed polynomial tests give opposite bounds for the even deviation
series. Pole normalization makes their shared coefficient converge to a
positive number, so both bounds remain uniform near one.
-/

open Complex MeasureTheory Filter Topology Set
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSingularArithmetic GaussZeroSum

def sourceEvenDeviation (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  LSeries (evenPart (WeilHerglotz.lamC lam -
    fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s

private theorem GammaReal_im (σ : ℝ) : (Gammaℝ (σ : ℂ)).im = 0 := by
  rw [Gammaℝ_def]
  have he : -(σ : ℂ)/2 = ((-(σ/2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_cpow Real.pi_pos.le]
  have he' : (σ : ℂ)/2 = ((σ/2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he', Complex.Gamma_ofReal]
  simp

private theorem sourceSquare_eq_deviation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1<s.re) :
    sourceZetaSquare hW s =
      LSeries (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s *
        riemannZeta s ^ 2 := by
  have hd := LSeriesSummable.sub (WeilHerglotz.summable_term_lamC hW hs)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  rw [← LSeries_sourceSquareCoeff hW hs, sourceSquareCoeff,
    LSeries_convolution' (hd.convolution h1) h1, LSeries_convolution' hd h1,
    LSeries_one_eq_riemannZeta hs]
  ring

private def normalizedSource (lam : ℕ → ℝ) (σ : ℝ) : ℝ :=
  (σ-1)^2 * (mellin (sourceGaussianProfile lam) ((σ : ℂ)/2)).re

private def deletionWeight (σ : ℝ) : ℝ :=
  (((σ : ℂ)-1)^2 * Gammaℝ (σ : ℂ) * riemannZeta (σ : ℂ)^2).re

private def deletionDiagonal (c σ : ℝ) : ℝ :=
  1+c^2/2-c*(4 : ℝ)^(-(σ/2)) - (c/2)*(1/4 : ℝ)^(-(σ/2))*
    (-1+4*(2 : ℝ)^(-σ)-2*((2 : ℝ)^(-σ))^2)

private def deletionCoefficient (σ : ℝ) : ℝ :=
  (1/4 : ℝ)^(-(σ/2))*(1-(2 : ℝ)^(-σ))^2*deletionWeight σ

private theorem normalized_polynomial_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (c : ℝ) {σ : ℝ} (hσ : 1<σ) :
    (σ-1)^2*(mellin (sourceTwoPointGaussianProfile lam c) ((σ : ℂ)/2)).re =
      deletionDiagonal c σ * normalizedSource lam σ -
        c * deletionCoefficient σ * (sourceEvenDeviation lam (σ : ℂ)).re := by
  have hx : (2 : ℂ)^(-(σ : ℂ)) = (((2 : ℝ)^(-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg]
    exact (Complex.ofReal_cpow (by norm_num : (0 : ℝ)≤2) _).symm
  have hz := riemannZeta_im_eq_zero_of_one_lt hσ
  have hg := GammaReal_im σ
  have hsq := sourceSquare_eq_deviation hW (s := (σ : ℂ)) hσ
  have hm := mellin_sourceGaussianProfile hW (s := (σ : ℂ)) hσ
  rw [re_mellin_sourceTwoPointGaussianProfile_eq hW c hσ,
    LSeries_sourceAlternating_deletion hW hσ, hx]
  unfold deletionDiagonal normalizedSource deletionCoefficient deletionWeight sourceEvenDeviation
  rw [hm, hsq]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im, hz, hg]
  ring

private theorem continuousAt_GammaReal_one' : ContinuousAt Gammaℝ 1 := by
  have h : ContinuousAt (fun s : ℂ => (Gammaℝ s)⁻¹) 1 :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hi := h.inv₀ (by simp : (Gammaℝ 1)⁻¹ ≠ 0)
  change ContinuousAt (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) 1 at hi
  simpa only [inv_inv] using hi

private theorem tendsto_deletionWeight :
    Tendsto deletionWeight (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hr := tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds
  have hg := continuousAt_GammaReal_one'.tendsto.comp hr
  have hp := (differentiable_zetaResidueFactor 1).continuousAt.tendsto.comp hr
  have ht := Complex.continuous_re.tendsto _ |>.comp (hg.mul (hp.pow 2))
  simp only [Gammaℝ_one, zetaResidueFactor_one, one_pow, one_mul, Complex.one_re] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  change 1<σ at hσ
  have hne : (σ : ℂ) ≠ 1 := by intro he; have := congrArg Complex.re he; simp at this; linarith [hσ]
  simp only [Function.comp_apply, zetaResidueFactor_of_ne hne]
  unfold deletionWeight
  congr 1
  ring

private theorem continuous_deletionDiagonal (c : ℝ) : Continuous (deletionDiagonal c) := by
  unfold deletionDiagonal
  fun_prop (disch := norm_num)

private theorem tendsto_deletionCoefficient :
    Tendsto deletionCoefficient (𝓝[>] (1 : ℝ))
      (𝓝 ((1/4 : ℝ)^(-(1/2 : ℝ))/4)) := by
  have h : Continuous (fun σ : ℝ => (1/4 : ℝ)^(-(σ/2))*(1-(2 : ℝ)^(-σ))^2) := by fun_prop (disch := norm_num)
  have ht := (h.tendsto 1).mono_left nhdsWithin_le_nhds |>.mul tendsto_deletionWeight
  norm_num [Real.rpow_neg_one] at ht
  change Tendsto deletionCoefficient (𝓝[>] (1 : ℝ)) (𝓝 (1/2)) at ht
  convert ht using 1
  norm_num

private theorem bounded_even_deviation_of_upper_bounds {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hB : ∀ c : ℝ, ∃ B : ℝ, ∀ σ : ℝ, 1<σ → σ<3/2 →
      (mellin (sourceTwoPointGaussianProfile lam c) ((σ : ℂ)/2)).re ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(sourceEvenDeviation lam (σ : ℂ)).re| ≤ K := by
  obtain ⟨Bp,hBp⟩ := hB 1
  obtain ⟨Bm,hBm⟩ := hB (-1)
  let kp : ℝ := (1/4 : ℝ)^(-(1/2 : ℝ))/4
  have hkp : 0<kp := by dsimp [kp]; positivity
  have hk := tendsto_deletionCoefficient.eventually_const_lt (show kp/2<kp by linarith)
  have hq := tendsto_sq_mul_re_mellin_sourceGaussianProfile hW
  have hlim (c B : ℝ) : ∃ A : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(σ-1)^2*B-deletionDiagonal c σ*normalizedSource lam σ| ≤ A := by
    have hz : Tendsto (fun σ : ℝ => (σ-1)^2*B) (𝓝[>] 1) (𝓝 0) := by
      have h : ContinuousAt (fun σ : ℝ => (σ-1)^2*B) 1 := by fun_prop (disch := norm_num)
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    exact (hz.sub (((continuous_deletionDiagonal c).tendsto 1).mono_left
      nhdsWithin_le_nhds |>.mul hq)).abs.isBoundedUnder_le
  obtain ⟨Ap,hAp⟩ := hlim 1 Bp
  obtain ⟨Am,hAm⟩ := hlim (-1) Bm
  let A : ℝ := |Ap|+|Am|
  refine ⟨A/(kp/2), by dsimp [A]; positivity, ?_⟩
  have hu : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ<3/2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ)<3/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hu,hk,hAp,hAm] with σ hσ hu hk hp hm
  have hplus := mul_le_mul_of_nonneg_left (hBp σ hσ hu) (sq_nonneg (σ-1))
  have hminus := mul_le_mul_of_nonneg_left (hBm σ hσ hu) (sq_nonneg (σ-1))
  rw [normalized_polynomial_eq hW 1 hσ] at hplus
  rw [normalized_polynomial_eq hW (-1) hσ] at hminus
  have hp' : - deletionCoefficient σ*(sourceEvenDeviation lam (σ : ℂ)).re ≤ A := by
    have h := (le_abs_self _).trans hp
    have hb : Ap≤A := by dsimp [A]; linarith [le_abs_self Ap,abs_nonneg Am]
    nlinarith
  have hm' : deletionCoefficient σ*(sourceEvenDeviation lam (σ : ℂ)).re ≤ A := by
    have h := (le_abs_self _).trans hm
    have hb : Am≤A := by dsimp [A]; linarith [le_abs_self Am,abs_nonneg Ap]
    nlinarith
  have hprod : deletionCoefficient σ*|(sourceEvenDeviation lam (σ : ℂ)).re| ≤ A := by
    by_cases he : 0 ≤ (sourceEvenDeviation lam (σ : ℂ)).re
    · rwa [abs_of_nonneg he]
    · rw [abs_of_neg (lt_of_not_ge he), mul_neg]
      simpa only [neg_mul] using hp'
  apply (le_div_iff₀ (by positivity : 0<kp/2)).mpr
  nlinarith [abs_nonneg ((sourceEvenDeviation lam (σ : ℂ)).re)]

/-- Full positivity bounds the real even deviation series near one, without
postulating continuation or a residue for the deleted source. -/
theorem exists_abs_re_sourceEvenDeviation_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(sourceEvenDeviation lam (σ : ℂ)).re| ≤ K :=
  bounded_even_deviation_of_upper_bounds hW
    (exists_re_mellin_sourceTwoPointGaussianProfile_le hW)

end RHTower.WeilWorkSettledPhase
