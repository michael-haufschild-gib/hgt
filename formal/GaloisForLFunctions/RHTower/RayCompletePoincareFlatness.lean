import GaloisForLFunctions.RHTower.RayCompleteTranslationAnalytic

/-!
# The zero Poincare shadow of positive-frequency Dirichlet carriers

An inverse-power Poincare shadow is zero precisely when every polynomial rescaling still tends to
zero on the positive real ray.  Absolute convergence with a strictly positive lowest frequency
gives this flatness directly from the uniform exponential bound.  Consequently every finite
translation of a ray-complete carrier has the same zero formal shadow.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A function has zero complete inverse-power Poincare expansion on the positive real ray. -/
def HasZeroInversePowerPoincareShadow (f : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, Tendsto (fun x : ℝ => (x : ℂ) ^ N * f x) atTop (nhds 0)

/-- Every absolutely convergent generalized Dirichlet series with a positive lowest frequency is
flat beyond all inverse powers. -/
theorem generalizedDirichletSeries_hasZeroInversePowerPoincareShadow
    {mu : ℕ → ℝ} (hmu : Monotone mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma)) :
    HasZeroInversePowerPoincareShadow
      (fun x : ℝ => generalizedDirichletSeries mu a x) := by
  intro N
  let S : ℝ := ∑' n, ‖a n‖ * Real.exp (-mu n * sigma)
  let C : ℝ := S * Real.exp (mu 0 * sigma)
  have hS : 0 ≤ S :=
    tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hC : 0 ≤ C := mul_nonneg hS (Real.exp_pos _).le
  have hmajorant : Tendsto
      (fun x : ℝ => C * (x ^ N * Real.exp (-mu 0 * x))) atTop (nhds 0) := by
    have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) (mu 0) hmu0
    have hpow :
        (fun x : ℝ => x ^ (N : ℝ) * Real.exp (-mu 0 * x)) =ᶠ[atTop]
          (fun x : ℝ => x ^ N * Real.exp (-mu 0 * x)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_natCast]
    simpa using (hbase.congr' hpow).const_mul C
  apply squeeze_zero_norm' ?_ hmajorant
  filter_upwards [eventually_ge_atTop (max sigma 0)] with x hx
  have hxsigma : sigma ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hx
  have hdecay := norm_generalizedDirichletSeries_real_le hmu hmu0 ha hxsigma
  have hsplit : Real.exp (-mu 0 * (x - sigma)) =
      Real.exp (mu 0 * sigma) * Real.exp (-mu 0 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  calc
    x ^ N * ‖generalizedDirichletSeries mu a ↑x‖ ≤
        x ^ N * (S * Real.exp (-mu 0 * (x - sigma))) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg hx0 _)
    _ = C * (x ^ N * Real.exp (-mu 0 * x)) := by rw [hsplit]; simp only [C]; ring

/-- Every finite translation of an absolutely convergent positive-frequency carrier has zero
inverse-power Poincare shadow. -/
theorem finiteTranslationAction_hasZeroInversePowerPoincareShadow
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (P : AddMonoidAlgebra ℂ ℂ) :
    HasZeroInversePowerPoincareShadow
      (fun x : ℝ => finiteTranslationAction P (generalizedDirichletSeries mu a) x) := by
  let tau := finiteTranslationThreshold P sigma
  let b := translatedGeneralizedCoefficient P mu a
  have hb : Summable (fun n => ‖b n‖ * Real.exp (-mu n * tau)) := by
    simpa [b, tau] using summable_translatedGeneralizedCoefficient hmu hmu0 ha P
  have hflat := generalizedDirichletSeries_hasZeroInversePowerPoincareShadow
    hmu.monotone hmu0 hb
  intro N
  apply Tendsto.congr' ?_ (hflat N)
  filter_upwards [eventually_ge_atTop tau] with x hx
  rw [finiteTranslationAction_generalizedDirichletSeries hmu hmu0 ha P hx]

/-- The formal translation-constraint ideal of the zero Poincare shadow is the whole translation
algebra: every operator sends the zero shadow to the rational zero shadow. -/
def zeroShadowFormalConstraintIdeal : Ideal (AddMonoidAlgebra ℂ ℂ) := ⊤

theorem zeroShadowFormalConstraintIdeal_eq_top :
    zeroShadowFormalConstraintIdeal = ⊤ := rfl

theorem mem_zeroShadowFormalConstraintIdeal (P : AddMonoidAlgebra ℂ ℂ) :
    P ∈ zeroShadowFormalConstraintIdeal := by simp [zeroShadowFormalConstraintIdeal]

end GaloisForLFunctions.RHTower
