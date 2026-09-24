import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule

/-!
# A sharp upper bound for `−Re ζ'/ζ` just right of the abscissa

On `1 < σ ≤ 2` and height `t ≥ 4` the completed logarithmic derivative has positive real part, so
the four-factor identity `ξ'/ξ = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ + ζ'/ζ` bounds `−Re ζ'/ζ` by the three
elementary pieces alone:

```text
−Re (ζ'/ζ)(σ + it) ≤ Re(1/s) + Re(1/(s−1)) + ‖Γ_ℝ'/Γ_ℝ(s)‖ ≤ 1/5 + log t + C,
```

with `C = digammaVerticalLogConstant`.  The coefficient of `log t` is one: the archimedean factor is
the only source of growth, and the zeros only help.
-/

open Complex GaloisForLFunctions

namespace RHTower

noncomputable section

/-- **The sharp Landau-type bound.**  For `1 < σ ≤ 2` and `t ≥ 4`. -/
theorem neg_re_logDeriv_riemannZeta_le {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ 1 / 5 + Real.log t + digammaVerticalLogConstant := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have h1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hfour := logDeriv_xi_fourFactor h1
  have hG : logDeriv Complex.Gammaℝ s
      = Complex.digamma (s / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    logDeriv_Gammaℝ_digamma (by rw [hsre]; linarith)
  -- the completed logarithmic derivative has positive real part
  have hxi : 0 < (logDeriv xi s).re := re_logDeriv_xi_pos_of_one_le_re h1.le
  -- rewrite `ζ'/ζ`
  have hzeta : logDeriv riemannZeta s
      = logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hG]
    rw [hfour]
    ring
  rw [hzeta]
  have hre : (logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s).re
      = (logDeriv xi s).re - (1 / s).re - (1 / (s - 1)).re
        - (logDeriv Complex.Gammaℝ s).re := by
    simp only [Complex.sub_re]
  rw [hre]
  -- the two elementary real parts
  have hnormSq : Complex.normSq s = σ ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hnormSq1 : Complex.normSq (s - 1) = (σ - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hA : (1 / s).re ≤ 2 / 17 := by
    rw [one_div, Complex.inv_re, hsre, hnormSq]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hB : (1 / (s - 1)).re ≤ 1 / 16 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, hnormSq1]
    simp only [Complex.one_re]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hC : (logDeriv Complex.Gammaℝ s).re
      ≤ Real.log t + digammaVerticalLogConstant := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [hsdef]
    exact norm_logDeriv_Gammaℝ_le (by linarith) (by linarith) ht
  linarith [hxi, hA, hB, hC]

end

end RHTower
