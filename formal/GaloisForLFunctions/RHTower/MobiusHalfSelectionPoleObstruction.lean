import GaloisForLFunctions.RHTower.MobiusHalfSelectionEulerCorrection
import GaloisForLFunctions.RHTower.DivisorSourceDirichlet
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import Mathlib.Analysis.Analytic.IsolatedZeros
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The actual half-selection divisor source cannot extend across the zeta pole

Form the literal arithmetic convolution `g=a*b`, where `a(n)=μ(n)/2^ω(n)`
and `b(n)=log n-τ(n)+2γ` off zero. Its summatory function and weighted Abel
mean agree exactly with the existing Bernoulli mean. Its absolutely convergent
L-series is the product of the two verified source factors.

There is no holomorphic function on `Re s > 1/2` agreeing with this L-series
on `Re s > 2`. Squaring and using the entire zeta pole unit would force
`F(s)^(2 : ℕ) Z(s)=(s-1)B(s)^(2 : ℕ) R(s)`. At one, the left side has zero value and
zero derivative, whereas the right derivative is nonzero.

This closes the analytic obstruction for the exact source. Transferring a
hypothetical linear bound on its weighted mean to such a continuation remains
separate; this file does not assert that transfer or decide RH.
-/

noncomputable section
open Complex Finset Filter Topology Set
namespace RHTower

/-- Complex arithmetic-function lift of the already defined divisor increment. -/
def halfSelectionDivisorSourceAF : ArithmeticFunction ℂ :=
  ⟨fun n => (primeFreeDivisorIncrementAF n : ℂ), by simp⟩

/-- Exact off-zero coefficient of the literal divisor source. -/
theorem halfSelectionDivisorSourceAF_apply {n : ℕ} (hn : n ≠ 0) :
    halfSelectionDivisorSourceAF n = (primeFreeDivisorIncrement n : ℂ) := by
  change (primeFreeDivisorIncrementAF n : ℂ) = _
  rw [primeFreeDivisorIncrementAF_apply hn]

/-- The actual half-selected Möbius coefficient convolved with the divisor source. -/
def halfSelectionDivisorConvolution : ArithmeticFunction ℂ :=
  halfSelectionMoebiusAF * halfSelectionDivisorSourceAF

private theorem summable_halfSelectionDivisorSource {s : ℂ} (hs : 3/2 < s.re) :
    LSeriesSummable halfSelectionDivisorSourceAF s := by
  apply (LSeriesSummable_congr s (fun {n} hn => halfSelectionDivisorSourceAF_apply hn)).mpr
  exact LSeriesSummable_primeFreeDivisorIncrement hs

/-- Absolute convergence of the actual convolution on a safe half-plane. -/
theorem LSeriesSummable_halfSelectionDivisorConvolution {s : ℂ} (hs : 3/2 < s.re) :
    LSeriesSummable halfSelectionDivisorConvolution s :=
  ArithmeticFunction.LSeriesSummable_mul
    (LSeriesSummable_halfSelectionMoebiusAF (by linarith)) (summable_halfSelectionDivisorSource hs)

/-- Exact L-series product of the actual arithmetic factors. -/
theorem LSeries_halfSelectionDivisorConvolution {s : ℂ} (hs : 3/2 < s.re) :
    LSeries halfSelectionDivisorConvolution s =
      LSeries halfSelectionMoebiusAF s * divisorSourceDirichlet s := by
  rw [halfSelectionDivisorConvolution,ArithmeticFunction.LSeries_mul'
    (LSeriesSummable_halfSelectionMoebiusAF (by linarith)) (summable_halfSelectionDivisorSource hs)]
  rw [divisorSourceDirichlet_eq_LSeries hs]
  congr 1
  exact LSeries_congr (fun {n} hn => halfSelectionDivisorSourceAF_apply hn) s

private theorem sum_halfSelectionDivisorSource (N : ℕ) :
    (∑ n ∈ Icc 1 N, halfSelectionDivisorSourceAF n) = (primeFreeDivisorDefect N : ℂ) := by
  rw [← sum_primeFreeDivisorIncrement N,Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  exact halfSelectionDivisorSourceAF_apply (by have := (mem_Icc.mp hn).1; omega)

/-- Exact summatory identification with the floor-dilated divisor defect. -/
theorem sum_halfSelectionDivisorConvolution (N : ℕ) :
    (∑ n ∈ Icc 1 N, halfSelectionDivisorConvolution n) =
      ((∑ d ∈ Icc 1 N, halfSelectionMoebiusWeight d * primeFreeDivisorDefect (N/d) : ℝ) : ℂ) := by
  rw [halfSelectionDivisorConvolution,sum_Icc_mul_apply,Complex.ofReal_sum]
  simp_rw [sum_halfSelectionDivisorSource]
  apply sum_congr rfl
  intro d hd
  rw [halfSelectionMoebiusAF_apply,Complex.ofReal_mul]

/-- The existing Bernoulli mean is the square-root Abel mean of this exact convolution. -/
theorem mobiusDivisorHalfSelectionHead_eq_convolution_abel (M : ℕ) :
    (mobiusDivisorHalfSelectionHead M : ℂ) =
      ∑ k ∈ Icc 1 (M-1), ((Real.sqrt (k+1:ℕ)-Real.sqrt k : ℝ) : ℂ) *
        ∑ n ∈ Icc 1 k, halfSelectionDivisorConvolution n := by
  rw [mobiusDivisorHalfSelectionHead_eq_divisor_abel,Complex.ofReal_sum]
  apply sum_congr rfl
  intro k hk
  rw [sum_halfSelectionDivisorConvolution,Complex.ofReal_mul]

/-- Unconditional obstruction: the actual source L-series has no holomorphic strict-half-plane extension. -/
theorem not_exists_analytic_halfSelectionDivisor_extension :
    ¬ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s : ℂ | (1/2:ℝ)<s.re} ∧
      ∀ s : ℂ, 2<s.re → F s = LSeries halfSelectionDivisorConvolution s := by
  rintro ⟨F,hF,hFar⟩
  let U : Set ℂ := {s : ℂ | (1/2:ℝ)<s.re}
  let H : ℂ → ℂ := fun s => F s^(2 : ℕ)*zetaPoleUnit s -
    (s-1)*divisorSourceDirichlet s^(2 : ℕ)*halfSelectionEulerCorrection s
  have hH : AnalyticOnNhd ℂ H U := by
    intro s hs
    exact (((hF s hs).pow 2).mul (differentiable_zetaPoleUnit.analyticAt s)).sub
      (((show AnalyticAt ℂ (fun s : ℂ => s-1) s by fun_prop).mul
        ((analyticOnNhd_divisorSourceDirichlet s hs).pow 2)).mul
        (analyticOnNhd_halfSelectionEulerCorrection s hs))
  have hHzero : ∀ s : ℂ, 2<s.re → H s=0 := by
    intro s hs
    have hs1 : 1<s.re := by linarith
    have hsne : s≠1 := by intro h; rw [h] at hs; norm_num at hs
    dsimp [H]
    rw [hFar s hs,LSeries_halfSelectionDivisorConvolution (by linarith),zetaPoleUnit_of_ne hsne,
      halfSelectionEulerCorrection_eq_LSeries_sq_mul_zeta hs1]
    ring
  have hfreq : ∃ᶠ s in 𝓝[≠] (3:ℂ), H s=0 := by
    have hnear : ∀ᶠ s in 𝓝 (3:ℂ), 2<s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hz := hnear.mono (fun s hs => hHzero s hs)
    exact (Eventually.filter_mono nhdsWithin_le_nhds hz).frequently
  have hzero := hH.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt (1/2:ℝ)).isPreconnected
    (show (3:ℂ)∈U by norm_num [U]) hfreq
  have hone : (1:ℂ)∈U := by norm_num [U]
  have hf1 : F 1=0 := by
    have h := hzero hone
    dsimp [H] at h
    have hsq : F 1^(2 : ℕ)=0 := by simpa [zetaPoleUnit_one] using h
    exact (sq_eq_zero_iff).mp hsq
  have heq : (fun s : ℂ => F s^(2 : ℕ)*zetaPoleUnit s) =ᶠ[𝓝 (1:ℂ)]
      (fun s : ℂ => (s-1)*divisorSourceDirichlet s^(2 : ℕ)*halfSelectionEulerCorrection s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1/2:ℝ)<(1:ℂ).re by norm_num)] with s hs
    exact sub_eq_zero.mp (hzero hs)
  have hFd := (hF 1 hone).differentiableAt.hasDerivAt
  have hBd := (analyticOnNhd_divisorSourceDirichlet 1 hone).differentiableAt.hasDerivAt
  have hRd := (analyticOnNhd_halfSelectionEulerCorrection 1 hone).differentiableAt.hasDerivAt
  have hleft := (hFd.pow 2).mul (differentiable_zetaPoleUnit 1).hasDerivAt
  have hright := (((hasDerivAt_id (1:ℂ)).sub_const 1).mul (hBd.pow 2)).mul hRd
  have hbad := hright.unique (hleft.congr_of_eventuallyEq heq.symm)
  have hbad' : divisorSourceDirichlet 1^(2 : ℕ)*halfSelectionEulerCorrection 1 = 0 := by
    simpa [Pi.pow_apply,Pi.mul_apply,hf1] using hbad
  exact (mul_ne_zero (pow_ne_zero 2 divisorSourceDirichlet_one_ne_zero)
    halfSelectionEulerCorrection_one_ne_zero) hbad'

end RHTower
