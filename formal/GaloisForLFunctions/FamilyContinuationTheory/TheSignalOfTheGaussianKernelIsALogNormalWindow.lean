import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfAHeckeKernelIsASumOverSquarefreeIdeals
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsTheZeroAbscissa

/-!
# The signal of the Gaussian kernel is a log-normal window

The signal of `exp((s − c)²)` is `(2√π)⁻¹ y^c exp(−(log y)²/4)`: the line `Re s = 2` moves to
`Re s = c`, where the integrand is a Gaussian in the height (`signal_gaussKernel`).

Hence the signal of the kernel `exp((s − c)²)/L(s, ψ)` of a ray class character is the Möbius sum
over the squarefree ideals with the log-normal weight of `Z/N𝔞`
(`signal_heckeKernel_eq_tsum_logNormal`), and a bound `O(Z^b)`, `b < 1`, for

`Σ_S (−1)^{|S|} ψ(∏ S) · (Z/N_S)^c exp(−log²(Z/N_S)/4)`

excludes the zeros of `L(s, ψ)` in `Re s > b` (`heckeLFunction_ne_zero_of_logNormalSum_le`).
-/

noncomputable section

open Complex MeasureTheory NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

/-- The log-normal window `(2π)⁻¹ √π · y^c exp(−(log y)²/4)`, written through `log y`. -/
def logNormalWindow (c y : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ((Real.pi : ℂ) ^ (1 / 2 : ℂ) * cexp ((Real.log y : ℂ) * c - (Real.log y : ℂ) ^ 2 / 4))

theorem differentiable_gaussKernel (c : ℝ) : Differentiable ℂ (gaussKernel c) := by
  unfold gaussKernel
  fun_prop

/-- The Gaussian kernel decays on every strip between the lines `Re s = c` and `Re s = 2`. -/
theorem norm_gaussKernel_le {c : ℝ} {s : ℂ} (h : (s.re - c) ^ 2 ≤ (2 - c) ^ 2) :
    ‖gaussKernel c s‖ ≤ Real.exp ((2 - c) ^ 2) / (1 + s.im ^ 2) := by
  unfold gaussKernel
  rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add, div_eq_mul_inv]
  refine mul_le_mul (Real.exp_le_exp.mpr h) ?_ (Real.exp_pos _).le (Real.exp_pos _).le
  rw [Real.exp_neg]
  refine inv_anti₀ (by positivity) ?_
  linarith [Real.add_one_le_exp (s.im ^ 2)]

/-- The line of the Gaussian signal moves to the centre. -/
theorem signal_gaussKernel_two_eq (c : ℝ) {y : ℝ} (hy : 0 < y) :
    signal (gaussKernel c) 2 y = signal (gaussKernel c) c y := by
  rcases le_total c 2 with h | h
  · exact signal_eq_of_decay h (fun s _ _ => differentiable_gaussKernel c s)
      (fun s h1 h2 => norm_gaussKernel_le
        (pow_le_pow_left₀ (by linarith) (by linarith) 2)) hy
  · refine (signal_eq_of_decay h (fun s _ _ => differentiable_gaussKernel c s)
      (fun s h1 h2 => norm_gaussKernel_le ?_) hy).symm
    nlinarith

/-- **The signal of the Gaussian kernel.** -/
theorem signal_gaussKernel (c : ℝ) {y : ℝ} (hy : 0 < y) :
    signal (gaussKernel c) 2 y = logNormalWindow c y := by
  rw [signal_gaussKernel_two_eq c hy]
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hfun : (fun t : ℝ => (y : ℂ) ^ (-(((-c : ℝ) : ℂ) + (t : ℂ) * I)) •
      gaussKernel c (-(((-c : ℝ) : ℂ) + (t : ℂ) * I))) =
      fun t : ℝ => cexp ((-1 : ℂ) * (t : ℂ) ^ 2 + (-(Real.log y : ℂ) * I) * t +
        (Real.log y : ℂ) * c) := by
    funext t
    have hw : -(((-c : ℝ) : ℂ) + (t : ℂ) * I) = (c : ℂ) - t * I := by
      push_cast
      ring
    have hg : ((c : ℂ) - t * I - c) ^ 2 = -((t : ℂ) ^ 2) := by
      have h1 : (c : ℂ) - t * I - c = -(t * I) := by ring
      rw [h1, neg_sq, mul_pow, I_sq]
      ring
    unfold gaussKernel
    rw [hw, hg, smul_eq_mul, cpow_def_of_ne_zero hy0, ← Complex.ofReal_log hy.le,
      ← Complex.exp_add]
    congr 1
    ring
  have hint := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)
    (-(Real.log y : ℂ) * I) ((Real.log y : ℂ) * c)
  have e1 : (Real.pi : ℂ) / -(-1 : ℂ) = Real.pi := by ring
  have e2 : (Real.log y : ℂ) * c - (-(Real.log y : ℂ) * I) ^ 2 / (4 * (-1 : ℂ)) =
      (Real.log y : ℂ) * c - (Real.log y : ℂ) ^ 2 / 4 := by
    have h1 : (-(Real.log y : ℂ) * I) ^ 2 = -((Real.log y : ℂ) ^ 2) := by
      rw [mul_pow, I_sq]
      ring
    rw [h1]
    ring
  rw [e1, e2] at hint
  unfold signal logNormalWindow
  rw [mellinInv, hfun, hint]

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- **The signal of a Hecke kernel with its explicit weight.** -/
theorem signal_heckeKernel_eq_tsum_logNormal (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (heckeKernel 𝔪 ψ c) 2 Z =
      ∑' S : Finset (HeightOneSpectrum (𝓞 K)),
        squarefreeCoeff 𝔪 ψ S * logNormalWindow c (Z / squarefreeNorm S) := by
  rw [signal_heckeKernel_eq_tsum 𝔪 ψ c hZ]
  refine tsum_congr fun S => ?_
  rw [signal_gaussKernel c (div_pos hZ (Nat.cast_pos.mpr (squarefreeNorm_pos S)))]

/-- **The explicit criterion.** For a nontrivial ray class character `ψ`, a bound `O(Z^b)`,
`b < 1`, for the Möbius sum over the squarefree ideals with the log-normal weight excludes the
zeros of `L(s, ψ)` in `Re s > b`. -/
theorem heckeLFunction_ne_zero_of_logNormalSum_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {c b C Z₀ : ℝ} (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hC : ∀ Z : ℝ, Z₀ ≤ Z → ‖∑' S : Finset (HeightOneSpectrum (𝓞 K)),
      squarefreeCoeff 𝔪 ψ S * logNormalWindow c (Z / squarefreeNorm S)‖ ≤ C * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) : heckeLFunction 𝔪 ψ ρ ≠ 0 :=
  heckeLFunction_ne_zero_of_signal_le hψ hb hZ₀
    (fun Z hZ => by
      rw [signal_heckeKernel_eq_tsum_logNormal 𝔪 ψ c (lt_of_lt_of_le hZ₀ hZ)]
      exact hC Z hZ) ρ hρ

end GaloisForLFunctions.FamilyContinuationTheory
