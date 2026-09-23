import GaloisForLFunctions.RHTower.XiPoissonMomentTrace
import GaloisForLFunctions.RHTower.XiPoissonMomentTail

/-!
# The bottom shell's polynomial, and the asymptotic identity

Weighting the `n`-th moment trace by `exp (g_1 t)` holds the bottom shell at constant modulus -- each
of its copies has height exactly `g_1`, so only the phase `exp (-i t J)` survives -- while the
above-bottom part is suppressed by the spectral gap.  What is left is a **finite** sum,

`xiPoissonShellPoly n t = sum_{q in bottom} alpha^_q ^ n * exp (-i t (Im alpha^_q))`,

a trigonometric polynomial in `t` whose coefficients are the `n`-th powers of the shell's Poisson
points.  Its moduli `‖alpha^‖^n = (g_1^(2 : ℕ) + J^(2 : ℕ))^(n/2)` are what `GeometricAmplitudeDominance`
separates.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The above-bottom part of the `n`-th moment trace. -/
def xiPoissonAboveMomentSum (n : ℕ) (τ : ℂ) : ℂ :=
  ∑' q : xiPoissonAboveBottom,
    xiPoissonPoint (q : XiZeroCopy) ^ n * xiPoissonTerm τ (q : XiZeroCopy)

/-- The bottom shell's trigonometric polynomial. -/
def xiPoissonShellPoly (n : ℕ) (t : ℝ) : ℂ :=
  ∑ q ∈ xiPoissonBottomShell,
    xiPoissonPoint q ^ n * Complex.exp (-(t : ℂ) * I * ((xiPoissonPoint q).im : ℂ))

theorem xiPoissonMomentTraceC_split {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    xiPoissonMomentTraceC n τ =
      (∑ q ∈ xiPoissonBottomShell, xiPoissonPoint q ^ n * xiPoissonTerm τ q) +
        xiPoissonAboveMomentSum n τ :=
  ((summable_xiPoissonMomentTerm hτ n).sum_add_tsum_compl).symm

/-- On the bottom shell the height factors out exactly, leaving only a phase. -/
theorem exp_bottomHeight_mul_shell_term (n : ℕ) (t : ℝ) {q : XiZeroCopy}
    (hq : q ∈ xiPoissonBottomShell) :
    ((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
        (xiPoissonPoint q ^ n * xiPoissonTerm ((t : ℝ) : ℂ) q)
      = xiPoissonPoint q ^ n *
          Complex.exp (-(t : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) := by
  have hsplit : xiPoissonPoint q =
      ((xiPoissonBottomHeight : ℝ) : ℂ) + ((xiPoissonPoint q).im : ℂ) * I := by
    rw [← mem_xiPoissonBottomShell.mp hq]
    exact (Complex.re_add_im _).symm
  have hexp : ((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
      Complex.exp (-(t : ℂ) * xiPoissonPoint q) =
      Complex.exp (-(t : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [hsplit]
    push_cast
    ring
  rw [xiPoissonTerm, ← mul_assoc, mul_comm _ (xiPoissonPoint q ^ n), mul_assoc, hexp]

/-- **The asymptotic identity.**  The weighted moment trace is the shell polynomial plus a weighted
tail. -/
theorem exp_bottomHeight_mul_momentTraceC_eq {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) * xiPoissonMomentTraceC n ((t : ℝ) : ℂ)
      = xiPoissonShellPoly n t +
        ((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
          xiPoissonAboveMomentSum n ((t : ℝ) : ℂ) := by
  have hre : (0 : ℝ) < (((t : ℝ) : ℂ)).re := by simpa using ht
  rw [xiPoissonMomentTraceC_split hre n, mul_add]
  congr 1
  rw [Finset.mul_sum, xiPoissonShellPoly]
  exact Finset.sum_congr rfl fun q hq => exp_bottomHeight_mul_shell_term n t hq

/-- The weighted tail is bounded by the moment-weighted above-bottom mass. -/
theorem norm_exp_bottomHeight_mul_aboveMomentSum_le {σ : ℝ} (hσ : 0 < σ) (n : ℕ) {v : ℝ}
    (hv : 0 ≤ v) :
    ‖((Real.exp (xiPoissonBottomHeight * (σ + v)) : ℝ) : ℂ) *
        xiPoissonAboveMomentSum n (((σ + v : ℝ)) : ℂ)‖ ≤
      Real.exp (xiPoissonBottomHeight * (σ + v)) *
        ∑' q : xiPoissonAboveBottom,
          ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
            xiPoissonWeight (σ + v) (q : XiZeroCopy) := by
  have hre : (0 : ℝ) < ((((σ + v : ℝ)) : ℂ)).re := by
    simpa using (by linarith : (0 : ℝ) < σ + v)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine le_trans (norm_tsum_le_tsum_norm
    ((summable_norm_xiPoissonMomentTerm hre n).subtype _)) ?_
  refine Summable.tsum_le_tsum (fun q => ?_)
    ((summable_norm_xiPoissonMomentTerm hre n).subtype _)
    ((summable_pow_mul_xiPoissonWeight (by linarith : (0:ℝ) < σ + v) n).subtype _)
  rw [norm_mul, norm_pow, xiPoissonWeight]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) n)
  rw [norm_xiPoissonTerm]
  refine Real.exp_le_exp.mpr ?_
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  exact le_refl _

end

end RHTower
