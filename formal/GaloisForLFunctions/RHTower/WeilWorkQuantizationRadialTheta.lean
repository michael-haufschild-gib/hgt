import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialMellin

/-!
# Arithmetic transforms of the canonical radial trace

The actual Weil-positive source determines a measurable quotient trace and its reflected
completion. This module proves their common polynomial bound, the reflected theta identity,
and both Hamburger/Laplace identities. No continuous critical-edge extension or functional
equation is supplied. These identities are prerequisites for the finite-remainder rigidity
argument; they do not assert that the reflection defect vanishes.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  WeilWorkSettledPhase GaloisForLFunctions.HTGeometry HamburgerStability AbelianTwist

/-- Global linear growth of the actual boundary quotient. -/
theorem exists_norm_quantizationTraceF_linear_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖quantizationTraceF hW y‖ ≤ C * (1 + |y|) := by
  obtain ⟨CF, hCF, hF⟩ := exists_norm_quantizationProdF_le hW
  obtain ⟨CB, hCB, hB⟩ := exists_bound_quantizationTraceF hW (-2) 2
  refine ⟨CF + CB, by positivity, fun y => ?_⟩
  rcases le_or_gt 2 |y| with hy | hy
  · have hb : ‖quantizationTraceF hW y‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ) := by
      apply le_of_tendsto (tendsto_quantizationTraceF hW y).norm
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
      exact hF (1 / 2 + η) y (by linarith [hη.1]) (by linarith [hη.2]) hy
    have hp : (1 + |y|) ^ (1 / 2 : ℝ) ≤ 1 + |y| := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by linarith [abs_nonneg y] : 1 ≤ 1 + |y|) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    calc ‖quantizationTraceF hW y‖ ≤ CF * (1 + |y|) := hb.trans (mul_le_mul_of_nonneg_left hp hCF)
      _ ≤ (CF + CB) * (1 + |y|) := by gcongr; linarith
  · have hmem : y ∈ uIcc (-2 : ℝ) 2 := by
      rw [uIcc_of_le (by norm_num)]
      exact ⟨(abs_lt.mp hy).1.le, (abs_lt.mp hy).2.le⟩
    calc ‖quantizationTraceF hW y‖ ≤ CB := hB y hmem
      _ ≤ (CF + CB) * (1 + |y|) := by nlinarith [abs_nonneg y]

theorem quantizationCompletedTrace_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    quantizationCompletedTrace hW (-y) = conj (quantizationCompletedTrace hW y) := by
  simp only [quantizationCompletedTrace, quantizationBoundaryTrace_neg, map_mul, bigG_two_conj]

/-- The reflected completion divided by the original critical-line Gamma factor. -/
def quantizationReflectedTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  quantizationCompletedTrace hW (-y) /
    ((((1 / 2 : ℝ) : ℂ) + y * I) * ((((1 / 2 : ℝ) : ℂ) + y * I) - 1) *
      Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * I))

theorem norm_quantizationReflectedTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    ‖quantizationReflectedTraceF hW y‖ = ‖quantizationTraceF hW y‖ := by
  simp only [quantizationReflectedTraceF, quantizationTraceF, norm_div,
    quantizationCompletedTrace_neg, Complex.norm_conj]

theorem measurable_quantizationReflectedTraceF {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (quantizationReflectedTraceF hW) := by
  have hc : Continuous (fun y : ℝ =>
      (((1 / 2 : ℝ) : ℂ) + y * I) * ((((1 / 2 : ℝ) : ℂ) + y * I) - 1) *
        Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * I)) := by
    apply Continuous.mul (by fun_prop)
    rw [continuous_iff_continuousAt]
    intro y
    exact (TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos
      (s := (((1 / 2 : ℝ) : ℂ) + y * I)) (by norm_num)).continuousAt.comp
      (f := fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I)) (by fun_prop)
  exact ((measurable_quantizationCompletedTrace hW).comp measurable_neg).div hc.measurable

theorem quantizationReflectedTraceF_gamma {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    Gammaℝ (lineS t) * quantizationReflectedTraceF hW (2 * t) =
      Gammaℝ (lineS (-t)) * quantizationTraceF hW (2 * (-t)) := by
  have hp : ∀ u : ℝ, lineS u = ((1 / 2 : ℝ) : ℂ) + (2 * u : ℝ) * I := by
    intro u; unfold lineS; push_cast; ring
  have hd : lineS (-t) * (lineS (-t) - 1) = lineS t * (lineS t - 1) := by
    simp only [hp]; push_cast; ring
  have hΓ := Gammaℝ_lineS_ne_zero t
  have hΓ' := Gammaℝ_lineS_ne_zero (-t)
  have hn : (2 : ℝ) * -t = -(2 * t) := by ring
  simp only [quantizationReflectedTraceF, quantizationTraceF, ← hp]
  rw [hn]
  field_simp
  rw [hd]

theorem exists_quantization_trace_pair_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖quantizationTraceF hW (2 * t)‖ ≤ C * (1 + |t|) ^ (1 : ℕ) ∧
      ‖quantizationReflectedTraceF hW (2 * t)‖ ≤ C * (1 + |t|) ^ (1 : ℕ) := by
  obtain ⟨C, hC, hB⟩ := exists_norm_quantizationTraceF_linear_le hW
  refine ⟨2 * C, by positivity, fun t => ?_⟩
  have h : ‖quantizationTraceF hW (2 * t)‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    have hb := hB (2 * t)
    rw [abs_mul, abs_two] at hb
    simp only [pow_one]
    nlinarith
  exact ⟨h, by rw [norm_quantizationReflectedTraceF]; exact h⟩

theorem quantization_reflected_defectKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) * defectKernel (fun t => quantizationTraceF hW (2 * t)) x⁻¹ =
      defectKernel (fun t => quantizationReflectedTraceF hW (2 * t)) x := by
  unfold defectKernel
  rw [mul_left_comm, ← integral_const_mul, ← integral_neg_eq_self]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + (-t : ℝ) * I)) *
        (Gammaℝ (lineS (-t)) * quantizationTraceF hW (2 * (-t)))) =
    (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Gammaℝ (lineS t) * quantizationReflectedTraceF hW (2 * t))
  rw [ofReal_inv_cpow_eq hx, ← mul_assoc, ofReal_cpow_mul_ofReal_cpow hx]
  have he : -(1 / 2 : ℂ) + -(-(((1 / 4 : ℝ) : ℂ) + (-t : ℝ) * I)) =
      -(((1 / 4 : ℝ) : ℂ) + t * I) := by push_cast; ring
  rw [he, quantizationReflectedTraceF_gamma]

theorem quantization_even_theta_relation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    coeffTheta (dirichletExp (lamLog lam)) x - (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      coeffTheta (dirichletExp (lamLog lam)) x⁻¹ =
      betaG (quantizationCompletion hW) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) - 1) +
        defectKernel (fun t => quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t)) x := by
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have hm : Measurable (fun t : ℝ => quantizationTraceF hW (2 * t)) :=
    (measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)
  have hm' : Measurable (fun t : ℝ => quantizationReflectedTraceF hW (2 * t)) :=
    (measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)
  have hw : AEStronglyMeasurable
      (fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).aestronglyMeasurable
  have hwb : ∀ᵐ t : ℝ, ‖(x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))‖ ≤ x ^ (-(1 / 4 : ℝ)) := by
    refine Eventually.of_forall fun t => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hi := (integrable_Gammaℝ_mul hm.aestronglyMeasurable (fun t => (hB t).1)).bdd_mul hw hwb
  have hi' := (integrable_Gammaℝ_mul hm'.aestronglyMeasurable (fun t => (hB t).2)).bdd_mul hw hwb
  have hK : defectKernel (fun t => quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t)) x =
      defectKernel (fun t => quantizationTraceF hW (2 * t)) x -
        defectKernel (fun t => quantizationReflectedTraceF hW (2 * t)) x := by
    unfold defectKernel
    simp_rw [mul_sub]
    rw [integral_sub hi hi', mul_sub]
  have hhalf : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [ofReal_inv_cpow_eq hx, ofReal_cpow_mul_ofReal_cpow hx]
    norm_num
  have hInv : (x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta (dirichletExp (lamLog lam)) x⁻¹ =
      betaG (quantizationCompletion hW) + defectKernel (fun t => quantizationReflectedTraceF hW (2 * t)) x := by
    rw [quantization_coeffTheta_eq_defectKernel hW (inv_pos.mpr hx), mul_add,
      mul_left_comm ((x : ℂ) ^ (-(1 / 2 : ℂ))) (betaG (quantizationCompletion hW)), hhalf, mul_one,
      quantization_reflected_defectKernel hW hx]
  rw [quantization_coeffTheta_eq_defectKernel hW hx, hInv, hK]
  ring

/-- First arithmetic transform: the actual boundary quotient recovers the Hamburger series. -/
theorem quantization_hamburgerSeries_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    hamburgerSeries (dirichletExp (lamLog lam)) τ = betaG (quantizationCompletion hW) +
      defectLaplace (fun t => quantizationTraceF hW (2 * t)) τ := by
  have ha := fun σ hσ => quantization_coeff_summable hW (σ := σ) hσ
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have hm : Measurable (fun t : ℝ => quantizationTraceF hW (2 * t)) :=
    (measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta (dirichletExp (lamLog lam)) x =
      0 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta (dirichletExp (lamLog lam)) x⁻¹) + 0 +
        betaG (quantizationCompletion hW) * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
          defectKernel (fun t => quantizationTraceF hW (2 * t)) x := by
    intro x hx
    simpa using quantization_coeffTheta_eq_defectKernel hW hx
  have h := hamburgerSeries_eq_of_coeffTheta_relation_defect _ _ ha ha htheta
    (fun τ hτ => (defectKernel_laplace hm (fun t => (hB t).1) hτ).1)
    (differentiableOn_defectLaplace hm.aestronglyMeasurable (fun t => (hB t).1))
    (fun τ hτ => (defectKernel_laplace hm (fun t => (hB t).1) hτ).2) hτ
  simpa using h

/-- The reflection defect has the arithmetic theta/Laplace representation from the source. -/
theorem quantization_hamburgerSeries_reflection {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    hamburgerSeries (dirichletExp (lamLog lam)) τ =
      (∑' n : ℕ, dirichletExp (lamLog lam) (n + 1) *
        cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))) -
      betaG (quantizationCompletion hW) / (Real.pi * τ) + betaG (quantizationCompletion hW) +
      defectLaplace (fun t => quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t)) τ := by
  have ha := fun σ hσ => quantization_coeff_summable hW (σ := σ) hσ
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  let g : ℝ → ℂ := fun t => quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t)
  have hm : Measurable g :=
    ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).sub
      ((measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id))
  have hb : ∀ t : ℝ, ‖g t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    intro t
    calc ‖g t‖ ≤ ‖quantizationTraceF hW (2 * t)‖ + ‖quantizationReflectedTraceF hW (2 * t)‖ := norm_sub_le _ _
      _ ≤ C * (1 + |t|) ^ (1 : ℕ) + C * (1 + |t|) ^ (1 : ℕ) := add_le_add (hB t).1 (hB t).2
      _ = _ := by ring
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta (dirichletExp (lamLog lam)) x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta (dirichletExp (lamLog lam)) x⁻¹) +
        -betaG (quantizationCompletion hW) + betaG (quantizationCompletion hW) * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
          defectKernel g x := by
    intro x hx
    have h := quantization_even_theta_relation hW hx
    dsimp only [g]
    linear_combination h
  have h := hamburgerSeries_eq_of_coeffTheta_relation_defect _ _ ha ha htheta
    (fun τ hτ => (defectKernel_laplace hm hb hτ).1)
    (differentiableOn_defectLaplace hm.aestronglyMeasurable hb)
    (fun τ hτ => (defectKernel_laplace hm hb hτ).2) hτ
  simpa only [g, one_mul, neg_div, sub_eq_add_neg] using h

end RHTower.WeilSpectral
