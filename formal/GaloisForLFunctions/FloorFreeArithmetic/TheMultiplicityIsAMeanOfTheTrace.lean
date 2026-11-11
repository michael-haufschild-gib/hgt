import GaloisForLFunctions.FloorFreeArithmetic.TheTopTraceDeterminesTheTopLayer
import GaloisForLFunctions.HTGeometry.BohrOrbitHaarLaw
import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSeeEveryConfiguration

/-!
# The multiplicity is a mean of the trace

The spline coefficient of a point `b + iλ` of the top line is the Cesàro mean of the normalized
trace against the character `e^{−iλu}`: the lower layers die out and the top trace is almost
periodic. For `ζ` the coefficient of a zero `ρ = ½ + z` is `2 m_ρ B̂(−iz)²`, with `m_ρ` the
multiplicity and `B̂` the transform of the spline. So the mean is quantized: it is zero or at
least the quantum `2|B̂(−iz)|²` in modulus.

This is the integrality of the tangent datum, and it gives a unit gap at every candidate zero:
a mean below the quantum on arbitrarily late windows excludes the zero, at every depth.

* `tendsto_windowAverage_normTrace_bohrChar`: the mean of the trace recovers the coefficient.
* `evenCoeff_zeta_eq`, `quantum_le_norm_evenCoeff_zeta`: quantization for `ζ`.
* `not_mem_zetaZeroConfig_of_mean_lt_quantum`: the unit gap.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality

variable {Z : ZeroConfig} {b : ℝ}

/-- The normalized trace is continuous. -/
theorem continuous_normTrace (hZ : TemperedConfig Z) (b : ℝ) : Continuous (normTrace Z b) := by
  unfold normTrace
  exact (continuous_two_re_lagStructure hZ).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)

/-- **The mean of the trace recovers the top coefficient.** At a depth bounding the
configuration, the average over `[0, T]` of the normalized trace against `e^{−iλu}` tends to the
spline coefficient of the point `b + iλ`. -/
theorem tendsto_windowAverage_normTrace_bohrChar (hZ : TemperedConfig Z) (htop : TopDepth Z b)
    (lam : ℝ) :
    Tendsto (windowAverage fun u => ((normTrace Z b u : ℝ) : ℂ) * bohrChar lam u) atTop
      (𝓝 (evenCoeff Z (boxSpline 1 3) ⟨b, lam⟩)) := by
  have hL : Tendsto (windowAverage fun u => topTraceC Z b u * bohrChar lam u) atTop
      (𝓝 (evenCoeff Z (boxSpline 1 3) ⟨b, lam⟩)) := by
    have h := tendsto_windowAverage_bohrCoefficient (continuous_topTraceC (b := b) hZ)
      (isBohrAlmostPeriodic_topTraceC hZ) lam
    rwa [bohrCoefficient_topTraceC hZ lam] at h
  have hf : Continuous fun u : ℝ => ((normTrace Z b u : ℝ) : ℂ) * bohrChar lam u :=
    (Complex.continuous_ofReal.comp (continuous_normTrace hZ b)).mul (continuous_bohrChar lam)
  have hg : Continuous fun u : ℝ => topTraceC Z b u * bohrChar lam u :=
    (continuous_topTraceC hZ).mul (continuous_bohrChar lam)
  refine HTGeometry.tendsto_windowAverage_of_tendsto_sub_zero hf hg ?_ hL
  -- the difference is the remainder of the lower layers times a unimodular character
  show Tendsto (fun u : ℝ => ((normTrace Z b u : ℝ) : ℂ) * bohrChar lam u -
    topTraceC Z b u * bohrChar lam u) atTop (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrem := (tendsto_normTrace_sub_topTrace hZ htop).abs
  rw [abs_zero] at hrem
  refine hrem.congr fun u => ?_
  rw [← sub_mul, norm_mul, norm_bohrChar, mul_one, ← ofReal_topTrace, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-! ### Quantization for the zeta function -/

/-- **The tangent datum of `ζ` is integral.** The spline coefficient of a zero `½ + z` is
`2 m B̂(−iz)²`, `m` its multiplicity. -/
theorem evenCoeff_zeta_eq {z : ℂ} (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) :
    evenCoeff zetaZeroConfig (boxSpline 1 3) z =
      (2 * (zetaZeroConfig.mult (1 / 2 + z) : ℂ)) * paperFT (boxSpline 1 3) (-(I * z)) ^ 2 := by
  have e : conj ((1 / 2 : ℂ) + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
  have hc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier := by
    have h := _root_.RHTower.conj_mem_zetaZeroConfig hz
    rwa [e] at h
  have hm : zetaZeroConfig.mult (1 / 2 + conj z) = zetaZeroConfig.mult (1 / 2 + z) := by
    have h := _root_.RHTower.mult_conj_zetaZeroConfig hz
    rwa [e] at h
  rw [evenCoeff_eq_of_conj_symm zetaZeroConfig (contDiff_boxSpline one_pos 2).continuous
    (hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3))
    (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hz]
  simp only [Set.indicator_of_mem hc, hm]
  ring

/-- The quantum: the modulus of the coefficient of a zero is at least `2|B̂(−iz)|²`. -/
theorem quantum_le_norm_evenCoeff_zeta {z : ℂ} (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) :
    2 * ‖paperFT (boxSpline 1 3) (-(I * z))‖ ^ 2 ≤
      ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖ := by
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hz
  have hcast : (2 * (zetaZeroConfig.mult (1 / 2 + z) : ℂ)) =
      ((2 * zetaZeroConfig.mult (1 / 2 + z) : ℕ) : ℂ) := by push_cast; ring
  rw [evenCoeff_zeta_eq hz, norm_mul, norm_pow, hcast, Complex.norm_natCast]
  have hsq : 0 ≤ ‖paperFT (boxSpline 1 3) (-(I * z))‖ ^ 2 := by positivity
  have h2 : (2 : ℝ) ≤ ((2 * zetaZeroConfig.mult (1 / 2 + z) : ℕ) : ℝ) := by
    push_cast
    linarith only [hm]
  exact mul_le_mul_of_nonneg_right h2 hsq

/-- **The unit gap of a multiplicity.** At a depth `b` bounding all zeros of `ζ`: if on
arbitrarily late windows the mean of the normalized trace against `e^{−iλu}` stays below the
quantum `2|B̂(−i(b + iλ))|²`, then `½ + b + iλ` is not a zero. -/
theorem not_mem_zetaZeroConfig_of_mean_lt_quantum {lam c : ℝ}
    (htop : TopDepth zetaZeroConfig b)
    (hc : c < 2 * ‖paperFT (boxSpline 1 3) (-(I * (⟨b, lam⟩ : ℂ)))‖ ^ 2)
    (hmean : ∃ᶠ T in atTop,
      ‖windowAverage (fun u => ((normTrace zetaZeroConfig b u : ℝ) : ℂ) * bohrChar lam u) T‖ ≤
        c) :
    ((1 / 2 : ℂ) + ⟨b, lam⟩) ∉ zetaZeroConfig.carrier := by
  intro hmem
  have hlim := (tendsto_windowAverage_normTrace_bohrChar temperedConfig_zetaZeroConfig htop
    lam).norm
  have hle : ‖evenCoeff zetaZeroConfig (boxSpline 1 3) ⟨b, lam⟩‖ ≤ c :=
    le_of_tendsto_of_frequently hlim hmean
  have hge := quantum_le_norm_evenCoeff_zeta hmem
  linarith only [hle, hge, hc]

end GaloisForLFunctions.FloorFreeArithmetic
