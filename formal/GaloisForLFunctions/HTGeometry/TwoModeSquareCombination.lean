import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# A vanishing admixture does not move a limit of squared masses

If the squared mass of `f` converges and the squared mass of `g` vanishes, then the squared mass of
`f + g` converges to the same limit: the cross term is controlled by Cauchy--Schwarz,
`|∫ f g| ≤ √(∫f² · ∫g²)`, and one factor tends to zero.

This is the shape a two-mode source takes when one of its two modes is asymptotically negligible:
the surviving mode keeps its limit, the vanishing mode contributes nothing, and the cross term
disappears with it.  Scaling the surviving mode by a convergent coefficient multiplies the limit by
the square of that coefficient, and scaling the negligible mode by a coefficient tending to zero
keeps it negligible even when its own squared mass does not vanish.

The measurability and integrability hypotheses are only required eventually along the filter, which
is what an asymptotic family of solutions of a differential equation supplies.
-/

open MeasureTheory Filter

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} {l : Filter ι} {μ : Measure ℝ}

/-- The cross term is bounded by the geometric mean of the two masses. -/
theorem abs_integral_mul_le_sqrt {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    |∫ y, f y * g y ∂μ| ≤ Real.sqrt ((∫ y, f y ^ 2 ∂μ) * ∫ y, g y ^ 2 ∂μ) := by
  have hsq := sq_integral_mul_le hfm hgm hf2 hg2
  have habs : |∫ y, f y * g y ∂μ| = Real.sqrt ((∫ y, f y * g y ∂μ) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  exact Real.sqrt_le_sqrt hsq

/-- Expanding the square of a sum under the integral. -/
theorem integral_sq_add {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, (f x + g x) ^ 2 ∂μ
      = (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ 2 ∂μ := by
  have hfg : Integrable (fun x => f x * g x) μ :=
    integrable_mul_of_sq_integrable hfm hgm hf2 hg2
  have hfg2 : Integrable (fun x => 2 * (f x * g x)) μ := hfg.const_mul 2
  calc ∫ x, (f x + g x) ^ 2 ∂μ
      = ∫ x, (f x ^ 2 + 2 * (f x * g x)) + g x ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
    _ = (∫ x, (f x ^ 2 + 2 * (f x * g x)) ∂μ) + ∫ x, g x ^ 2 ∂μ :=
        integral_add (hf2.add hfg2) hg2
    _ = ((∫ x, f x ^ 2 ∂μ) + ∫ x, 2 * (f x * g x) ∂μ) + ∫ x, g x ^ 2 ∂μ := by
        rw [integral_add hf2 hfg2]
    _ = (∫ x, f x ^ 2 ∂μ) + 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ 2 ∂μ := by
        rw [integral_const_mul]

/-- Rescaling a family by a fixed factor rescales its squared mass by the square of that
factor. -/
theorem integral_sq_const_mul (c : ℝ) (f : ℝ → ℝ) :
    ∫ x, (c * f x) ^ 2 ∂μ = c ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  rw [show (fun x => (c * f x) ^ 2) = fun x => c ^ 2 * f x ^ 2 from by funext x; ring,
    integral_const_mul]

/-- **A vanishing admixture does not move the limit.** -/
theorem tendsto_integral_sq_add_of_tendsto_zero {f g : ι → ℝ → ℝ} {A : ℝ}
    (hfm : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hgm : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ)
    (hf2 : ∀ᶠ i in l, Integrable (fun x => f i x ^ 2) μ)
    (hg2 : ∀ᶠ i in l, Integrable (fun x => g i x ^ 2) μ)
    (hfA : Tendsto (fun i => ∫ x, f i x ^ 2 ∂μ) l (𝓝 A))
    (hg0 : Tendsto (fun i => ∫ x, g i x ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, (f i x + g i x) ^ 2 ∂μ) l (𝓝 A) := by
  have hmaj : Tendsto
      (fun i => 2 * Real.sqrt ((∫ x, f i x ^ 2 ∂μ) * ∫ x, g i x ^ 2 ∂μ)
        + ∫ x, g i x ^ 2 ∂μ) l (𝓝 0) := by
    have hprod : Tendsto (fun i => (∫ x, f i x ^ 2 ∂μ) * ∫ x, g i x ^ 2 ∂μ) l (𝓝 0) := by
      have := hfA.mul hg0
      rwa [mul_zero] at this
    have hsqrt : Tendsto
        (fun i => Real.sqrt ((∫ x, f i x ^ 2 ∂μ) * ∫ x, g i x ^ 2 ∂μ)) l (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hprod
      rw [Real.sqrt_zero] at h
      exact h
    have := (hsqrt.const_mul 2).add hg0
    simpa using this
  have hdiff : Tendsto
      (fun i => (∫ x, (f i x + g i x) ^ 2 ∂μ) - ∫ x, f i x ^ 2 ∂μ) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i =>
      2 * Real.sqrt ((∫ x, f i x ^ 2 ∂μ) * ∫ x, g i x ^ 2 ∂μ) + ∫ x, g i x ^ 2 ∂μ) ?_ hmaj
    filter_upwards [hfm, hgm, hf2, hg2] with i hfmi hgmi hf2i hg2i
    rw [integral_sq_add hfmi hgmi hf2i hg2i]
    have hnn : (0 : ℝ) ≤ ∫ x, g i x ^ 2 ∂μ :=
      integral_nonneg fun x => sq_nonneg _
    have hcs := abs_integral_mul_le_sqrt hfmi hgmi hf2i hg2i
    rw [Real.norm_eq_abs,
      show (∫ x, f i x ^ 2 ∂μ) + 2 * (∫ x, f i x * g i x ∂μ) + (∫ x, g i x ^ 2 ∂μ)
          - ∫ x, f i x ^ 2 ∂μ
        = 2 * (∫ x, f i x * g i x ∂μ) + ∫ x, g i x ^ 2 ∂μ from by ring]
    calc |2 * (∫ x, f i x * g i x ∂μ) + ∫ x, g i x ^ 2 ∂μ|
        ≤ |2 * (∫ x, f i x * g i x ∂μ)| + |∫ x, g i x ^ 2 ∂μ| := abs_add_le _ _
      _ = 2 * |∫ x, f i x * g i x ∂μ| + ∫ x, g i x ^ 2 ∂μ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hnn]
      _ ≤ 2 * Real.sqrt ((∫ x, f i x ^ 2 ∂μ) * ∫ x, g i x ^ 2 ∂μ) + ∫ x, g i x ^ 2 ∂μ := by
          have := mul_le_mul_of_nonneg_left hcs (by norm_num : (0:ℝ) ≤ 2)
          linarith
  have h := hdiff.add hfA
  simpa using h

/-- **Two-mode combination with variable coefficients.**  The negligible mode is only required to
have a bounded squared mass; its coefficient tending to zero is what removes it, together with the
cross term.  The surviving mode's limit is multiplied by the square of the limiting coefficient. -/
theorem tendsto_integral_sq_two_mode {f g : ι → ℝ → ℝ} {b c : ι → ℝ} {A B b₀ : ℝ}
    (hfm : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hgm : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ)
    (hf2 : ∀ᶠ i in l, Integrable (fun x => f i x ^ 2) μ)
    (hg2 : ∀ᶠ i in l, Integrable (fun x => g i x ^ 2) μ)
    (hfA : Tendsto (fun i => ∫ x, f i x ^ 2 ∂μ) l (𝓝 A))
    (hgB : Tendsto (fun i => ∫ x, g i x ^ 2 ∂μ) l (𝓝 B))
    (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 0)) :
    Tendsto (fun i => ∫ x, (b i * f i x + c i * g i x) ^ 2 ∂μ) l (𝓝 (b₀ ^ 2 * A)) := by
  have hbf : Tendsto (fun i => ∫ x, (b i * f i x) ^ 2 ∂μ) l (𝓝 (b₀ ^ 2 * A)) := by
    refine ((hb.pow 2).mul hfA).congr fun i => ?_
    exact (integral_sq_const_mul (b i) (f i)).symm
  have hcg : Tendsto (fun i => ∫ x, (c i * g i x) ^ 2 ∂μ) l (𝓝 0) := by
    have h := (hc.pow 2).mul hgB
    rw [show (0 : ℝ) ^ 2 * B = 0 from by ring] at h
    exact h.congr fun i => (integral_sq_const_mul (c i) (g i)).symm
  refine tendsto_integral_sq_add_of_tendsto_zero
    (f := fun i x => b i * f i x) (g := fun i x => c i * g i x)
    (hfm.mono fun i h => h.const_mul (b i)) (hgm.mono fun i h => h.const_mul (c i))
    ?_ ?_ hbf hcg
  · filter_upwards [hf2] with i h
    refine (h.const_mul (b i ^ 2)).congr ?_
    filter_upwards with x
    ring
  · filter_upwards [hg2] with i h
    refine (h.const_mul (c i ^ 2)).congr ?_
    filter_upwards with x
    ring

end GaloisForLFunctions.HTGeometry
