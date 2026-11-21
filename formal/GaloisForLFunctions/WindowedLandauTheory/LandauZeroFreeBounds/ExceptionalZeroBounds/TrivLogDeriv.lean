import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLowBox
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! The principal logarithmic derivative is bounded by the pole term and a logarithmic error. -/

open Complex

namespace WindowedLandauTheory.ZeroFreeDirichlet

private theorem zeta_log_deriv_high {σ t : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 4 ≤ |t|) :
    -(logDeriv riemannZeta ((σ : ℂ) + t * I)).re ≤ Real.log |t| / 2 + 1 / 2 := by
  have h := RHTower.neg_re_logDeriv_riemannZeta_le_half hσ hσ₂ ht
  rcases le_or_gt 0 t with hpos | hneg
  · simpa only [abs_of_nonneg hpos] using h
  · have hconj : (starRingEnd ℂ) ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I) = (σ : ℂ) + t * I := by
      apply Complex.ext <;> simp [abs_of_neg hneg]
    rw [← hconj, RHTower.logDeriv_riemannZeta_conj]
    simpa only [Complex.conj_re] using h

private theorem zeta_log_deriv_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    (-logDeriv riemannZeta ((σ : ℂ) + t * I)).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + K * Real.log (|t| + 2) := by
  obtain ⟨δ, hδ, M, hM, hbox⟩ := RHTower.Sieve.exists_bound_zetaLogDerivReg_line_low 2 (by norm_num)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / 2 + (M + 1) / Real.log 2, by positivity, fun σ t hσ hσ₂ => ?_⟩
  let s : ℂ := (σ : ℂ) + t * I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hsub : s - 1 = (σ : ℂ) - 1 + t * I := by dsimp [s]; ring
  have htwo : (2 : ℝ) ≤ |t| + 2 := le_add_of_nonneg_left (abs_nonneg t)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hK : M + 1 ≤ (M + 1) / Real.log 2 * Real.log (|t| + 2) := by
    calc M + 1 = (M + 1) / Real.log 2 * Real.log 2 := (div_mul_cancel₀ _ hlog₂.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [← hsub, ← show s = (σ : ℂ) + t * I from rfl]
  rcases le_or_gt |t| 9 with ht | ht
  · have hs₁ : s ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hs
      exact (lt_irrefl _ hs)
    have hb := hbox σ (by linarith only [hσ, hδ]) hσ₂ t ht
    rw [RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs₁ (riemannZeta_ne_zero_of_one_lt_re hs),
      Complex.add_re, one_div, add_mul]
    have hreg : (RHTower.Sieve.zetaLogDerivReg s).re ≤ M := (Complex.re_le_norm _).trans hb
    linarith only [hK, hreg, hlog, hlog₂]
  · have ht₄ : 4 ≤ |t| := by linarith only [ht]
    have hh := zeta_log_deriv_high hσ hσ₂ ht₄
    have hlog' : Real.log |t| ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by linarith only [ht]) (by linarith)
    have hp : 0 ≤ (1 / (s - 1)).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re, Complex.one_re]
      exact div_nonneg (sub_nonneg.mpr hs.le) (Complex.normSq_nonneg _)
    have hh' : (-logDeriv riemannZeta s).re ≤ Real.log |t| / 2 + 1 / 2 := by
      simpa only [Complex.neg_re] using hh
    rw [add_mul]
    linarith only [hh', hlog', hK, hM, hp]

theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK, hzeta⟩ := zeta_log_deriv_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ₂ => ?_⟩
  let s : ℂ := (σ : ℂ) + t * I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hprincipal : (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-logDeriv riemannZeta s).re + Real.log q := by
    simpa only [negLD, logDeriv_apply, neg_div] using
      RHTower.neg_re_logDeriv_trivChar_le (q := q) hs
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq := Real.log_nonneg hq
  have hlogt : 0 ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by linarith only [abs_nonneg t])
  rw [Real.log_mul (by positivity : (q : ℝ) ≠ 0) (by positivity : |t| + 2 ≠ 0)]
  have hz := hzeta σ t hσ hσ₂
  change (negLD (1 : DirichletCharacter ℂ q) s).re ≤ _
  nlinarith only [hprincipal, hz, hlogt, mul_nonneg hK hlogq]

end WindowedLandauTheory.ZeroFreeDirichlet
