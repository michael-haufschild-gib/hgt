import GaloisForLFunctions.RHTower.ConnesFracConvSwap
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential

/-!
# §VII (41), step 3: the symbol of `C_{α,v}` grows like `|x|^α`

§VII (39)-(41) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes writes *"the Fourier transform on `k_v` of the distribution `C_{α,v}` behaves like
`|x_v|^α`"* and uses it without proof.  This module proves it at the archimedean place, in the
quantitative form that (41) needs: the symbol

  `m_α(x) = ∫ ψ(|ε|)(e^{2πiεx} − 1) dε/|ε|^{1+α}`

is *real*, negative, and

  `‖m_α(x)‖ ≥ 2 C_α (2π|x|)^α − 2·(2δ^{-α}/α)`.

The mechanism: the imaginary part integrates to zero because the weight is even, the real part is
`−2 ∫_0^∞ ψ(s)(1 − cos(2π|x|s))s^{-1-α}ds`, and that is the truncated Lévy integral whose growth
was established in `ConnesFractionalSymbolGrowth`.
-/

open MeasureTheory Real Set
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The Fourier symbol of Connes' operator (39). -/
def connesFracSymbol (α : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) *
    (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1)

theorem connes_norm_expChar_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  have hnorm : ‖((θ : ℂ) * Complex.I)‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |θ| 1 with h | h
  · have hz : ‖((θ : ℂ) * Complex.I)‖ ≤ 1 := by rw [hnorm]; exact h
    have hb := Complex.norm_exp_sub_one_le hz
    rwa [hnorm] at hb
  · have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    calc ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖
        ≤ ‖Complex.exp ((θ : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
      _ ≤ 2 * |θ| := by nlinarith

/-- The symbol's integrand is absolutely integrable. -/
theorem connes_fracSymbol_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0) (x : ℝ) :
    Integrable (fun ε : ℝ => ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1)) volume := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hmaj : Integrable (fun ε : ℝ => (4 * π * |x|) *
      Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε) volume :=
    (connes_fracEps_integrable hα1).const_mul _
  have hwmeas : Measurable (connesFracWeight α ψ) :=
    connesFracWeight_measurable (by linarith) hψc
  refine MeasureTheory.Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun ε => ?_)
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact Complex.measurable_ofReal.comp hwmeas
    · have hc : Continuous fun ε : ℝ =>
          Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1 := by fun_prop
      exact hc.measurable
  · by_cases hmem : ε ∈ Icc (-1 : ℝ) 1
    · have hεle : |ε| ≤ 1 := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hind : Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε = |ε| ^ (-α) :=
        Set.indicator_of_mem hmem (fun ε : ℝ => |ε| ^ (-α))
      rw [hind, norm_mul]
      have hwabs : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ ≤ |ε| ^ (-1 - α) := by
        rw [Complex.norm_real, Real.norm_eq_abs, connesFracWeight,
          abs_of_nonneg (mul_nonneg (hψ0 _) (Real.rpow_nonneg (abs_nonneg ε) _))]
        calc ψ |ε| * |ε| ^ (-1 - α) ≤ 1 * |ε| ^ (-1 - α) :=
              mul_le_mul_of_nonneg_right (hψ1 _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = |ε| ^ (-1 - α) := one_mul _
      have hexp := connes_norm_expChar_sub_one_le (2 * π * (ε * x))
      have habs : |2 * π * (ε * x)| = 2 * π * (|ε| * |x|) := by
        have h1 : (0 : ℝ) ≤ 2 * π := by positivity
        rw [abs_mul, abs_of_nonneg h1, abs_mul]
      rw [habs] at hexp
      rcases eq_or_ne ε 0 with hε0 | hε0
      · subst hε0
        have hz : Complex.exp (((2 * π * ((0:ℝ) * x) : ℝ) : ℂ) * Complex.I) - 1 = 0 := by
          norm_num
        rw [hz, norm_zero, mul_zero]
        positivity
      · have hεpos : (0 : ℝ) < |ε| := abs_pos.mpr hε0
        have hcomb : |ε| ^ (-1 - α) * |ε| = |ε| ^ (-α) := by
          rw [show (-1 - α : ℝ) = -α + -1 by ring, Real.rpow_add hεpos,
            Real.rpow_neg_one, inv_mul_cancel_right₀ (ne_of_gt hεpos)]
        calc ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ *
              ‖Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1‖
            ≤ (|ε| ^ (-1 - α)) * (2 * (2 * π * (|ε| * |x|))) :=
              mul_le_mul hwabs hexp (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = (4 * π * |x|) * (|ε| ^ (-1 - α) * |ε|) := by ring
          _ = (4 * π * |x|) * |ε| ^ (-α) := by rw [hcomb]
    · have hgt : 1 < |ε| := by
        by_contra hcon
        exact hmem (Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hcon)))
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      rw [hw0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      have : (0 : ℝ) ≤ Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε :=
        connes_fracEps_nonneg ε
      positivity

theorem connesTruncatedLevy_nonneg {α : ℝ} {ψ : ℝ → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (t : ℝ) :
    0 ≤ connesTruncatedLevy α ψ t := by
  refine setIntegral_nonneg measurableSet_Ioi fun ε hε => ?_
  exact mul_nonneg (hψ0 ε) (connesLevyKernelAt_nonneg α t (le_of_lt hε))

/-- **The symbol is real and negative**, with modulus the truncated Lévy integral. -/
theorem connes_fracSymbol_re {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0) (x : ℝ) :
    (connesFracSymbol α ψ x).re = -(2 * connesTruncatedLevy α ψ (2 * π * |x|)) := by
  have hint := connes_fracSymbol_integrable hα0 hα1 hψc hψ0 hψ1 hψsupp x
  have hre : (connesFracSymbol α ψ x).re
      = ∫ ε : ℝ, (((connesFracWeight α ψ ε : ℝ) : ℂ) *
          (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1)).re := by
    rw [connesFracSymbol]
    exact (integral_re hint).symm
  have hpt : ∀ ε : ℝ, (((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I) - 1)).re
      = -((fun s : ℝ => ψ s * ((1 - Real.cos (2 * π * |x| * s)) * s ^ (-1 - α))) |ε|) := by
    intro ε
    have hcosre : (Complex.exp (((2 * π * (ε * x) : ℝ) : ℂ) * Complex.I)).re
        = Real.cos (2 * π * (ε * x)) := Complex.exp_ofReal_mul_I_re _
    have hcoseq : Real.cos (2 * π * (ε * x)) = Real.cos (2 * π * |x| * |ε|) := by
      have habs : |2 * π * (ε * x)| = 2 * π * |x| * |ε| := by
        have h1 : (0 : ℝ) ≤ 2 * π := by positivity
        rw [abs_mul, abs_of_nonneg h1, abs_mul]
        ring
      calc Real.cos (2 * π * (ε * x)) = Real.cos |2 * π * (ε * x)| :=
            (Real.cos_abs _).symm
        _ = Real.cos (2 * π * |x| * |ε|) := by rw [habs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, hcosre, zero_mul, sub_zero]
    rw [hcoseq, connesFracWeight]
    ring
  rw [hre, integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_neg]
  have habs2 : (∫ a : ℝ,
      (fun s : ℝ => ψ s * ((1 - Real.cos (2 * π * |x| * s)) * s ^ (-1 - α))) |a|)
      = 2 * ∫ s in Ioi (0 : ℝ),
          ψ s * ((1 - Real.cos (2 * π * |x| * s)) * s ^ (-1 - α)) :=
    integral_comp_abs (f := fun s : ℝ => ψ s * ((1 - Real.cos (2 * π * |x| * s)) * s ^ (-1 - α)))
  rw [habs2]
  rfl

/-- **§VII (41), the symbol lower bound.**  The symbol of `C_{α,v}` grows like `|x|^α`. -/
theorem connes_fracSymbol_norm_lower {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hα2 : α < 2)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0)
    {δ : ℝ} (hδ : 0 < δ) (hψδ : ∀ s ∈ Ioc (0 : ℝ) δ, ψ s = 1)
    {x : ℝ} (hx : x ≠ 0) :
    2 * (connesLevyConstant α * (2 * π * |x|) ^ α) - 2 * (2 * δ ^ (-α) / α)
      ≤ ‖connesFracSymbol α ψ x‖ := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have ht : (0 : ℝ) < 2 * π * |x| := by
    have : (0 : ℝ) < |x| := abs_pos.mpr hx
    positivity
  have hre := connes_fracSymbol_re hα0 hα1 hψc hψ0 hψ1 hψsupp x
  have hlow := connes_truncatedLevy_lower_bound hα0 hα2 hψc hψ0 hψ1 hδ hψδ ht
  have habs : |(connesFracSymbol α ψ x).re| ≤ ‖connesFracSymbol α ψ x‖ :=
    Complex.abs_re_le_norm _
  have hTnn : 0 ≤ connesTruncatedLevy α ψ (2 * π * |x|) := connesTruncatedLevy_nonneg hψ0 _
  have heq : |(connesFracSymbol α ψ x).re| = 2 * connesTruncatedLevy α ψ (2 * π * |x|) := by
    rw [hre, abs_neg, abs_of_nonneg (by linarith)]
  rw [heq] at habs
  linarith

end

end GaloisForLFunctions.RHTower
