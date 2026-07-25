import GaloisForLFunctions.RHTower.SmoothAFEZetaReflection
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Exact dual coefficient and Gamma-ratio factorization

On the critical line `s = 1/2+iτ`, `χ(s)` is nonzero.  Each reflected Dirichlet term therefore
factors exactly as

`χ(s) (n+1)^(s-1) · [χ(s+w)/χ(s)] (n+1)^w x^w G(w)/w`.

This separates the dual Dirichlet coefficient from the shifted Gamma ratio whose uniform Stirling
approximation supplies the classical smooth AFE error.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaChiShiftRatio (s w : ℂ) : ℂ :=
  zetaChi (s + w) / zetaChi s

def smoothAFEDualRatioTerm
    (s : ℂ) (x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio s w *
    (n + 1 : ℂ) ^ w * (x : ℂ) ^ w * smoothAFEGaussianKernel w

def smoothAFEDualRatioIntegrand
    (s : ℂ) (y : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio s w * smoothAFEMellinIntegrand y w

theorem smoothAFEDualRatioTerm_eq_integrand
    {x : ℝ} (hx : 0 < x) (s : ℂ) (n : ℕ) (w : ℂ) :
    smoothAFEDualRatioTerm s x n w =
      smoothAFEDualRatioIntegrand s
        (1 / ((n + 1 : ℝ) * x)) w := by
  have hnpos : (0 : ℝ) < n + 1 := by
    exact_mod_cast Nat.succ_pos n
  have hscale : 0 < (n + 1 : ℝ) * x := mul_pos hnpos hx
  have hrecip :
      (((1 / ((n + 1 : ℝ) * x) : ℝ) : ℂ) ^ (-w)) =
        (((n + 1 : ℝ) * x : ℝ) : ℂ) ^ w := by
    simpa using cpow_div_pos_neg (a := 1) (b := (n + 1 : ℝ) * x)
      zero_lt_one hscale w
  have hmul :
      ((((n + 1 : ℝ) * x : ℝ) : ℂ) ^ w) =
        (n + 1 : ℂ) ^ w * (x : ℂ) ^ w := by
    convert Complex.mul_cpow_ofReal_nonneg hnpos.le hx.le w using 1 <;>
      norm_num
  rw [smoothAFEDualRatioTerm, smoothAFEDualRatioIntegrand,
    smoothAFEMellinIntegrand, hrecip, hmul]
  ring

theorem smoothAFEZetaReflectedTerm_eq_dualRatioTerm
    {s w : ℂ} {x : ℝ} (n : ℕ) (hχ : zetaChi s ≠ 0) :
    smoothAFEZetaReflectedTerm s x n w =
      zetaChi s * (n + 1 : ℂ) ^ (s - 1) *
        smoothAFEDualRatioTerm s x n w := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hpow := Complex.cpow_add (x := (n + 1 : ℂ)) (s - 1) w hn
  have hexponent : (s - 1) + w = s + w - 1 := by ring
  rw [hexponent] at hpow
  rw [smoothAFEZetaReflectedTerm_eq_cpow,
    smoothAFEDualRatioTerm, smoothAFEZetaChiShiftRatio, hpow]
  field_simp [hχ]

theorem smoothAFEZetaReflectedTerm_eq_dualRatioTerm_line
    (τ : ℝ) {w : ℂ} {x : ℝ} (n : ℕ) :
    smoothAFEZetaReflectedTerm (linePt τ) x n w =
      zetaChi (linePt τ) * (n + 1 : ℂ) ^ (linePt τ - 1) *
        smoothAFEDualRatioTerm (linePt τ) x n w :=
  smoothAFEZetaReflectedTerm_eq_dualRatioTerm n
    (zetaChi_line_ne_zero τ)

theorem smoothAFEZetaMellinIntegrand_eq_dualRatio_tsum_left_one
    (τ : ℝ) {x t : ℝ} :
    smoothAFEZetaMellinIntegrand (linePt τ) x
        ((-1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ,
        zetaChi (linePt τ) * (n + 1 : ℂ) ^ (linePt τ - 1) *
          smoothAFEDualRatioTerm (linePt τ) x n
            ((-1 : ℂ) + (t : ℂ) * I) := by
  rw [smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one
    (s := linePt τ) (x := x) (t := t) (linePt_re τ)]
  apply tsum_congr
  intro n
  exact smoothAFEZetaReflectedTerm_eq_dualRatioTerm_line τ n

end RHTower
