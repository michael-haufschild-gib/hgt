import GaloisForLFunctions.RHTower.SelbergScatteringEntireTransform
import Mathlib.Topology.Piecewise

/-!
# Continuous reciprocal symbol for the entire native Casimir transform

The modular energy is `A = 1 − Δ_H`. In its bounded inverse coordinate `x`,
the entire transform of `A − 1` is represented by the reciprocal symbol
`g(x) = 1 / (F(x⁻¹ − 1).re + 2)` for `x > 0`, extended by zero elsewhere.
The symbol is continuous, takes values in `[0,1]`, and is strictly positive
on the positive half-line. Continuity at zero follows from hyperbolic-cosine
growth, not a numerical approximation.
-/

open Filter Topology
namespace RHTower.SelbergScatteringEntireTransform
noncomputable section

/-- Reciprocal coordinate for the entire transform of `A - 1`, extended by zero. -/
def entireCovarianceSymbol (x : ℝ) : ℝ :=
  if 0 < x then ((casimirTransform (x⁻¹ - 1 : ℝ)).re + 2)⁻¹ else 0

theorem entireCovarianceSymbol_pos {x : ℝ} (hx : 0 < x) :
    0 < entireCovarianceSymbol x := by
  rw [entireCovarianceSymbol, if_pos hx]
  apply inv_pos.mpr
  have h := (casimirTransform_real_range (x⁻¹ - 1)).2
  linarith

theorem entireCovarianceSymbol_nonneg (x : ℝ) : 0 ≤ entireCovarianceSymbol x := by
  by_cases hx : 0 < x
  · exact (entireCovarianceSymbol_pos hx).le
  · simp [entireCovarianceSymbol, hx]

theorem entireCovarianceSymbol_le_one (x : ℝ) : entireCovarianceSymbol x ≤ 1 := by
  by_cases hx : 0 < x
  · rw [entireCovarianceSymbol, if_pos hx]
    have h := (casimirTransform_real_range (x⁻¹ - 1)).2
    apply inv_le_one_of_one_le₀
    linarith
  · simp [entireCovarianceSymbol, hx]

theorem entireCovarianceSymbol_zero_iff (x : ℝ) :
    entireCovarianceSymbol x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    have := entireCovarianceSymbol_pos (lt_of_not_ge hx)
    linarith
  · intro hx
    simp [entireCovarianceSymbol, not_lt.mpr hx]

/-- The entire native transform grows without bound along the real positive ray. -/
theorem casimirTransform_real_tendsto_atTop :
    Tendsto (fun x : ℝ => (casimirTransform x).re) atTop atTop := by
  have hcosh : Tendsto Real.cosh atTop atTop := by
    apply tendsto_atTop_mono (fun x => ?_)
      (Tendsto.atTop_mul_const (show 0 < (1 / 2 : ℝ) by norm_num) Real.tendsto_exp_atTop)
    rw [Real.cosh_eq]
    have := Real.exp_pos (-x)
    linarith
  have hs : Tendsto (fun x : ℝ => x - 1 / 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-(1 / 4 : ℝ)) tendsto_id
  have ht := hcosh.comp (Tendsto.const_mul_atTop
    (show 0 < 8 * Real.pi by positivity) (Real.tendsto_sqrt_atTop.comp hs))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 / 4 : ℝ)] with x hx
  rw [casimirTransform_of_ge_quarter x hx, Complex.ofReal_re]
  rfl

private theorem reciprocalEntire_tendsto_zero :
    Tendsto (fun x : ℝ => ((casimirTransform (x⁻¹ - 1 : ℝ)).re + 2)⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹ - 1) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ (-1 : ℝ) tendsto_inv_nhdsGT_zero
  have hf := casimirTransform_real_tendsto_atTop.comp hi
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 hf)

/-- Continuity includes the accumulation point zero of the original modular covariance. -/
theorem continuous_entireCovarianceSymbol : Continuous entireCovarianceSymbol := by
  unfold entireCovarianceSymbol
  apply continuous_if'
  · intro x hx
    have hx0 : x = 0 := by simpa only [show {x : ℝ | 0 < x} = Set.Ioi 0 from rfl,
      frontier_Ioi, Set.mem_singleton_iff] using hx
    subst x
    rw [if_neg (lt_irrefl (0 : ℝ))]
    change Tendsto (fun x : ℝ => ((casimirTransform (x⁻¹ - 1 : ℝ)).re + 2)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
    exact reciprocalEntire_tendsto_zero
  · intro x hx
    have hx0 : x = 0 := by simpa only [show {x : ℝ | 0 < x} = Set.Ioi 0 from rfl,
      frontier_Ioi, Set.mem_singleton_iff] using hx
    subst x
    simpa only [lt_self_iff_false, if_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝[{x : ℝ | ¬0 < x}] 0) (𝓝 0))
  · intro x hx
    have harg : ContinuousWithinAt (fun y : ℝ => y⁻¹ - 1) {y | 0 < y} x :=
      (continuousWithinAt_id.inv₀ (ne_of_gt hx)).sub continuousWithinAt_const
    have hf := Complex.continuous_re.comp
      (differentiable_casimirTransform.continuous.comp Complex.continuous_ofReal)
    apply ((hf.continuousAt.comp_continuousWithinAt harg).add continuousWithinAt_const).inv₀
    change (casimirTransform (x⁻¹ - 1 : ℝ)).re + 2 ≠ 0
    have h := (casimirTransform_real_range (x⁻¹ - 1)).2
    linarith
  · exact continuousOn_const

/-- The reciprocal coordinate retains the exact scalar identity, with the native energy shift. -/
theorem entireCovarianceSymbol_inverse (x : ℝ) (hx : 0 < x) :
    (entireCovarianceSymbol x)⁻¹ - 2 = (casimirTransform (x⁻¹ - 1 : ℝ)).re := by
  simp [entireCovarianceSymbol, hx]

end
end RHTower.SelbergScatteringEntireTransform
