import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeNormalFrame
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The essential inverse-flow symbol and the fixed-width Weil sample

In the compact reciprocal coordinate `μ = -1/z` of the source-derived inverse the fixed-width
tomography symbol is

`Φ_{a,L}(μ) = 2μ (sin(a/μ) - sin((a-L)/μ))`,

with an essential singularity at the compact spectral boundary `μ = 0`.  On a root block it
reproduces the fixed-width Xi--Weil sample

`F_{a,L}(w) = e^{aw} A_L(w) + e^{-aw} A_L(-w)`,  `A_L(w) = (1 - e^{-Lw})/w`,

at the corresponding spectral parameter `w = i z`.
-/

open Filter Topology

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

/-- The fixed-width tomography symbol in the compact reciprocal coordinate. -/
def essentialFlowSymbol (a L : ℝ) (μ : ℂ) : ℂ :=
  2 * μ * (Complex.sin (((a : ℝ) : ℂ) / μ) - Complex.sin ((((a - L : ℝ)) : ℂ) / μ))

/-- The inverse-flow symbol is even on the entire complex plane, including its arbitrary value at
the puncture. -/
theorem essentialFlowSymbol_neg (a L : ℝ) (μ : ℂ) :
    essentialFlowSymbol a L (-μ) = essentialFlowSymbol a L μ := by
  simp only [essentialFlowSymbol, div_neg, Complex.sin_neg]
  ring

/-- Real punctured sequence on which the width difference is exactly periodic and the symbol
vanishes. -/
def essentialFlowZeroSequence (L : ℝ) (n : ℕ) : ℂ :=
  (((L / (2 * Real.pi)) * (1 / ((n : ℝ) + 1) : ℝ) : ℝ) : ℂ)

/-- Imaginary punctured sequence on which the two hyperbolic-sine values are strictly distinct. -/
def essentialFlowNonzeroSequence (n : ℕ) : ℂ :=
  -Complex.I * (((1 / ((n : ℝ) + 1) : ℝ) : ℝ) : ℂ)

theorem essentialFlowZeroSequence_ne_zero {L : ℝ} (hL : 0 < L) (n : ℕ) :
    essentialFlowZeroSequence L n ≠ 0 := by
  rw [essentialFlowZeroSequence]
  norm_cast
  positivity

theorem essentialFlowNonzeroSequence_ne_zero (n : ℕ) :
    essentialFlowNonzeroSequence n ≠ 0 := by
  rw [essentialFlowNonzeroSequence]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_cast; positivity)

theorem essentialFlowZeroSequence_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (essentialFlowZeroSequence L) atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hreal : Tendsto
        (fun n : ℕ => (L / (2 * Real.pi)) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (0 : ℝ)) := by
      have hconst : Tendsto (fun _n : ℕ => L / (2 * Real.pi)) atTop
          (𝓝 (L / (2 * Real.pi))) := tendsto_const_nhds
      simpa using hconst.mul tendsto_one_div_add_atTop_nhds_zero_nat
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  · exact Eventually.of_forall fun n => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact essentialFlowZeroSequence_ne_zero hL n

theorem essentialFlowNonzeroSequence_tendsto :
    Tendsto essentialFlowNonzeroSequence atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto
      (fun n : ℕ => -Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝 (0 : ℂ))
    have hreal : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomplex : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _n : ℕ => -Complex.I) atTop (𝓝 (-Complex.I))).mul
        hcomplex)
  · exact Eventually.of_forall fun n => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact essentialFlowNonzeroSequence_ne_zero n

/-- The periodic real sequence consists of exact zeros of the inverse-flow symbol. -/
theorem essentialFlowSymbol_zeroSequence
    {L : ℝ} (hL : 0 < L) (a : ℝ) (n : ℕ) :
    essentialFlowSymbol a L (essentialFlowZeroSequence L n) = 0 := by
  have hmu := essentialFlowZeroSequence_ne_zero hL n
  have harg :
      ((a : ℂ) / essentialFlowZeroSequence L n) =
        (((a - L : ℝ) : ℂ) / essentialFlowZeroSequence L n) +
          (n + 1 : ℕ) * (2 * (Real.pi : ℂ)) := by
    rw [essentialFlowZeroSequence]
    push_cast
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp [hL0]
    ring
  rw [essentialFlowSymbol, harg, Complex.sin_add_nat_mul_two_pi]
  ring

/-- The imaginary punctured sequence consists of exact nonzeros of the inverse-flow symbol. -/
theorem essentialFlowSymbol_nonzeroSequence
    {L : ℝ} (hL : 0 < L) (a : ℝ) (n : ℕ) :
    essentialFlowSymbol a L (essentialFlowNonzeroSequence n) ≠ 0 := by
  let t : ℝ := (n : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hmu := essentialFlowNonzeroSequence_ne_zero n
  have hseq : essentialFlowNonzeroSequence n = -Complex.I * (t : ℂ)⁻¹ := by
    simp [essentialFlowNonzeroSequence, t]
  have hinv : (essentialFlowNonzeroSequence n)⁻¹ = (t : ℂ) * Complex.I := by
    rw [hseq, mul_inv, inv_inv, inv_neg, Complex.inv_I]
    ring
  have harg1 :
      (a : ℂ) / essentialFlowNonzeroSequence n = ((a * t : ℝ) : ℂ) * Complex.I := by
    rw [div_eq_mul_inv, hinv]
    push_cast
    ring
  have harg2 :
      ((a - L : ℝ) : ℂ) / essentialFlowNonzeroSequence n =
        (((a - L) * t : ℝ) : ℂ) * Complex.I := by
    rw [div_eq_mul_inv, hinv]
    push_cast
    ring
  have hlt : (a - L) * t < a * t := by nlinarith
  have hsinh : Real.sinh ((a - L) * t) ≠ Real.sinh (a * t) :=
    (Real.sinh_strictMono hlt).ne
  rw [essentialFlowSymbol, harg1, harg2, Complex.sin_mul_I, Complex.sin_mul_I]
  refine mul_ne_zero (mul_ne_zero (by norm_num) hmu) ?_
  rw [← sub_mul]
  refine mul_ne_zero (sub_ne_zero.mpr ?_) Complex.I_ne_zero
  exact_mod_cast hsinh.symm

/-- For every positive width the puncture is essential: the symbol is not meromorphic at zero.
It is holomorphic at every nonzero point, so this excludes both removable and finite-pole-order
continuations. -/
theorem essentialFlowSymbol_not_meromorphicAt_zero
    {L : ℝ} (hL : 0 < L) (a : ℝ) :
    ¬ MeromorphicAt (essentialFlowSymbol a L) 0 := by
  intro hmero
  rcases hmero.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · have hev : ∀ᶠ n : ℕ in atTop,
        essentialFlowSymbol a L (essentialFlowNonzeroSequence n) = 0 :=
      essentialFlowNonzeroSequence_tendsto.eventually hzero
    obtain ⟨n, hn⟩ := hev.exists
    exact essentialFlowSymbol_nonzeroSequence hL a n hn
  · have hev : ∀ᶠ n : ℕ in atTop,
        essentialFlowSymbol a L (essentialFlowZeroSequence L n) ≠ 0 :=
      (essentialFlowZeroSequence_tendsto hL).eventually hnonzero
    obtain ⟨n, hn⟩ := hev.exists
    exact hn (essentialFlowSymbol_zeroSequence hL a n)

/-- The essential symbol is holomorphic throughout the punctured plane. -/
theorem essentialFlowSymbol_differentiableAt
    (a L : ℝ) {mu : ℂ} (hmu : mu ≠ 0) :
    DifferentiableAt ℂ (essentialFlowSymbol a L) mu := by
  unfold essentialFlowSymbol
  fun_prop

/-- The fixed-width amplitude `A_L(w) = (1 - e^{-Lw})/w`. -/
def weilWidthAmplitude (L : ℝ) (w : ℂ) : ℂ := (1 - Complex.exp (-((L : ℝ) : ℂ) * w)) / w

/-- The fixed-width Weil sample `F_{a,L}(w) = e^{aw} A_L(w) + e^{-aw} A_L(-w)`. -/
def weilFixedWidthSample (a L : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (((a : ℝ) : ℂ) * w) * weilWidthAmplitude L w
    + Complex.exp (-(((a : ℝ) : ℂ) * w)) * weilWidthAmplitude L (-w)

/-- The common closed form of both sides on a root block. -/
def rootBlockForm (a L : ℝ) (z : ℂ) : ℂ :=
  Complex.I * z⁻¹ * (Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z)))
      - Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z))
      - Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z)))
      + Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)))

theorem essentialFlowSymbol_eq_rootBlockForm (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    essentialFlowSymbol a L (-z⁻¹) = rootBlockForm a L z := by
  have harg1 : ((a : ℝ) : ℂ) / (-z⁻¹) = -(((a : ℝ) : ℂ) * z) := by field_simp
  have harg2 : (((a - L : ℝ)) : ℂ) / (-z⁻¹) = -((((a - L : ℝ)) : ℂ) * z) := by field_simp
  have hs1 : Complex.exp ((-(((a : ℝ) : ℂ) * z)) * Complex.I)
      = Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z))) := by
    congr 1
    ring
  have hs2 : Complex.exp ((((a : ℝ) : ℂ) * z) * Complex.I)
      = Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z)) := by
    congr 1
    ring
  have hs3 : Complex.exp ((-((((a - L : ℝ)) : ℂ) * z)) * Complex.I)
      = Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z))) := by
    congr 1
    ring
  have hs4 : Complex.exp (((((a - L : ℝ)) : ℂ) * z) * Complex.I)
      = Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)) := by
    congr 1
    ring
  rw [essentialFlowSymbol, harg1, harg2, Complex.sin_neg, Complex.sin_neg,
    Complex.sin, Complex.sin, hs1, hs2, hs3, hs4, rootBlockForm]
  field_simp
  ring

theorem weilFixedWidthSample_eq_rootBlockForm (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    weilFixedWidthSample a L (Complex.I * z) = rootBlockForm a L z := by
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero hIne hz
  have hinv : (Complex.I * z)⁻¹ = -Complex.I * z⁻¹ := by
    rw [mul_inv, Complex.inv_I]
  have hinv' : (-(Complex.I * z))⁻¹ = Complex.I * z⁻¹ := by
    rw [inv_neg, hinv]
    ring
  have hUX : Complex.exp (((a : ℝ) : ℂ) * (Complex.I * z))
        * Complex.exp (-((L : ℝ) : ℂ) * (Complex.I * z))
      = Complex.exp ((((a - L : ℝ)) : ℂ) * (Complex.I * z)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hVY : Complex.exp (-(((a : ℝ) : ℂ) * (Complex.I * z)))
        * Complex.exp (-((L : ℝ) : ℂ) * -(Complex.I * z))
      = Complex.exp (-((((a - L : ℝ)) : ℂ) * (Complex.I * z))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [weilFixedWidthSample, weilWidthAmplitude, weilWidthAmplitude, rootBlockForm,
    ← hUX, ← hVY, div_eq_mul_inv, div_eq_mul_inv, hinv, hinv']
  ring

/-- **The tomography symbol reproduces the fixed-width Weil sample on every root block.** -/
theorem essentialFlowSymbol_root (a L : ℝ) {z : ℂ} (hz : z ≠ 0) :
    essentialFlowSymbol a L (-z⁻¹) = weilFixedWidthSample a L (Complex.I * z) := by
  rw [essentialFlowSymbol_eq_rootBlockForm a L hz, weilFixedWidthSample_eq_rootBlockForm a L hz]


/-! ### The spectral coordinates of the root block -/

/-- **The spectral parameter of a root block.**  With `w = i z` the compact eigenvalue
`mu = -1/z` is also `-i/w`. -/
theorem compactEigenvalue_eq_of_spectralParameter {z : ℂ} (hz : z ≠ 0) :
    -z⁻¹ = -Complex.I / (Complex.I * z) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp

/-- **The two zero conditions agree.**  `Xi_C(z) = 0` is `Xi(1/2 + w) = 0` at `w = i z`. -/
theorem xiC_eq_xi_shift (z : ℂ) : XiC z = xi (1 / 2 + Complex.I * z) := by
  rw [XiC]
  congr 1
  ring

theorem xiC_eq_zero_iff_xi_shift (z : ℂ) :
    XiC z = 0 ↔ xi (1 / 2 + Complex.I * z) = 0 := by
  rw [xiC_eq_xi_shift]


end HedenmalmThetaSource

end

end RHTower
