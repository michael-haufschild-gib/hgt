import Mathlib.Analysis.Calculus.SmoothSeries
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectTsumDerivative

/-!
# Real-displacement derivative of the direct Gaussian AFE edge

Varying `d` in `s(d)=1/2-d+i*tau` differentiates the direct Dirichlet
coefficient with the positive logarithmic factor.  Gaussian cutoff decay
provides a uniform summable derivative majorant on `0 < d < 1/4`.
-/

noncomputable section

open Complex Filter Set

namespace RHTower

def smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  ((n + 1 : ℂ) ^ (-displacedLinePt d tau) *
      Complex.log (n + 1 : ℂ)) *
    smoothAFECutoff ((n + 1 : ℝ) / x)

theorem smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm_eq_I_mul_height
    (d x tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n =
      I * smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n := by
  unfold smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
    smoothAFEZetaDisplacedDirectHeightDerivativeTerm
  ring_nf
  simp

theorem hasDerivAt_smoothAFEZetaDisplacedDirectTerm_displacement
    (d x tau : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedDirectTerm u x tau n)
      (smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) d := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hs : HasDerivAt (fun u : ℝ => displacedLinePt u tau) (-1 : ℂ) d := by
    have hreal :=
      ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)).ofReal_comp
    simpa [displacedLinePt] using hreal.add_const ((tau : ℂ) * I)
  have hpC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ)) (y := -displacedLinePt d tau)
      (Or.inl hn)).hasDerivAt
  have hp := hpC.comp d hs.neg
  have h := hp.mul_const (smoothAFECutoff ((n + 1 : ℝ) / x))
  simpa [Function.comp_apply, Pi.neg_apply,
    smoothAFEZetaDisplacedDirectTerm,
    smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm] using h

theorem norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
    (d x tau : ℝ) (n : ℕ) :
    ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 - d)) *
        Real.log (n + 1 : ℝ) *
        ‖smoothAFECutoff ((n + 1 : ℝ) / x)‖ := by
  rw [smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm_eq_I_mul_height,
    norm_mul, norm_I, one_mul,
    norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm]

theorem summable_norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) (tau : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n‖) := by
  simpa only [norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm,
    norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm] using
    summable_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm
      hdhalf hx tau

def smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField
    (d x tau : ℝ) : ℂ :=
  ∑' n : ℕ,
    smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n

/-- The complete direct edge differentiates term by term in displacement. -/
theorem hasDerivAt_smoothAFEZetaDisplacedDirectSourceField_displacement
    {d x : ℝ} (hd : 0 < d) (hdq : d < 1 / 4) (hx : 0 < x)
    (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedDirectSourceField u x tau)
      (smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau) d := by
  let major : ℕ → ℝ := fun n =>
    ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
      (1 / 4) x tau n‖
  have hmajor : Summable major := by
    dsimp only [major]
    exact summable_norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm
      (by norm_num) hx tau
  have hterm : ∀ n : ℕ, ∀ u ∈ Ioo (0 : ℝ) (1 / 4),
      HasDerivAt
        (fun y : ℝ => smoothAFEZetaDisplacedDirectTerm y x tau n)
        (smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm u x tau n) u := by
    exact fun n u _ =>
      hasDerivAt_smoothAFEZetaDisplacedDirectTerm_displacement u x tau n
  have hbound : ∀ n : ℕ, ∀ u ∈ Ioo (0 : ℝ) (1 / 4),
      ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm u x tau n‖ ≤
        major n := by
    intro n u hu
    dsimp only [major]
    rw [norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm,
      norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm]
    have hr : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow :
        (n + 1 : ℝ) ^ (-(1 / 2 - u)) ≤
          (n + 1 : ℝ) ^ (-(1 / 2 - (1 / 4 : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith [hu.2])
    gcongr
    exact Real.log_nonneg hr
  have hdmem : d ∈ Ioo (0 : ℝ) (1 / 4) := ⟨hd, hdq⟩
  have hvalue : Summable (fun n : ℕ =>
      smoothAFEZetaDisplacedDirectTerm d x tau n) := by
    apply Summable.of_norm
    exact summable_norm_smoothAFEZetaDisplacedDirectTerm
      (hdq.trans (by norm_num)) hx tau
  have hsum := hasDerivAt_tsum_of_isPreconnected hmajor isOpen_Ioo
    (convex_Ioo (0 : ℝ) (1 / 4)).isPreconnected hterm hbound hdmem
    hvalue hdmem
  unfold smoothAFEZetaDisplacedDirectSourceField
    smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField
  exact hsum

end RHTower
