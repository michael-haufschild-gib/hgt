import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFriedrichsOperator

/-!
# The restricted Weil form is compactly negative at every aperture

At a fixed aperture the corpus writes the restricted Weil form of `ζ` as the archimedean
form-domain energy plus a bounded remainder read through the physical embedding,

`W(u, u) = ‖u‖² + ⟪R (J u), J u⟫`,

where `R` collects the two polar evaluations and the prime translations with `n ≤ e^{2a}`
(`RHTower.ccmRestrictedWeilBoundedRemainder`) and `J` is the **compact** embedding of the form
domain into the aperture (`RHTower.isCompactOperator_ccmArchimedeanFormToAperture`).  So the whole
negative part of the critical form is seen through a compact operator: this is the compact
negativity of `AdverseProfilesCannotVanish`, for the actual form.

* **Compact maps upgrade weak convergence** (`tendsto_of_weakConvC`): a bounded weakly convergent
  sequence is mapped by a compact operator to a norm-convergent one.
* **Weak lower semicontinuity** (`compactPerturbation_le_of_weakConvC`) and **adverse profiles
  cannot vanish** (`compactPerturbation_adverse_weakLimit`) for every form
  `‖u‖² + re ⟪R (J u), J u⟫` with `J` compact.
* **The critical form** (`ccmRestrictedWeilForm_adverse_weakLimit`): at every positive aperture, a
  unit-bounded sequence of the restricted Weil form with energies tending to `μ < 0` and a weak
  limit `u` in the archimedean form domain has `u ≠ 0` and `W(u, u) ≤ μ ‖u‖²`.

Escape of adverse mass at a fixed aperture is therefore impossible; what a positivity proof must
control is the dependence of these compactness statements on the aperture.
-/

open Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Weak convergence: every continuous linear functional converges. -/
def WeakConvC (u : ℕ → E) (u₀ : E) : Prop :=
  ∀ φ : E →L[ℂ] ℂ, Tendsto (fun n => φ (u n)) atTop (𝓝 (φ u₀))

/-- **Compact operators upgrade bounded weak convergence to norm convergence.** -/
theorem tendsto_of_weakConvC {J : E →L[ℂ] F} (hJ : IsCompactOperator J) {u : ℕ → E} {u₀ : E}
    (h : WeakConvC u u₀) {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B) :
    Tendsto (fun n => J (u n)) atTop (𝓝 (J u₀)) := by
  have hB1 : (0 : ℝ) < |B| + 1 := by positivity
  obtain ⟨K, hK, hJK⟩ := (isCompactOperator_iff_image_closedBall_subset_compact
    J.toLinearMap hB1).1 hJ
  have hmem : ∀ n, J (u n) ∈ K := fun n => hJK ⟨u n, by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hB n, le_abs_self B], rfl⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨w, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq fun n => hmem (ns n)
  refine ⟨ψ, ?_⟩
  -- the subsequential limit is `J u₀`: test it against every vector
  have hw : w = J u₀ := by
    apply ext_inner_left ℂ
    intro y
    have h1 : Tendsto (fun n => inner ℂ y (J (u (ns (ψ n))))) atTop (𝓝 (inner ℂ y w)) :=
      (continuous_inner.comp (continuous_const.prodMk continuous_id)).tendsto w |>.comp hlim
    have h2 : Tendsto (fun n => inner ℂ y (J (u (ns (ψ n))))) atTop (𝓝 (inner ℂ y (J u₀))) := by
      have := (h ((innerSL ℂ y).comp J)).comp (hns.comp hψ.tendsto_atTop)
      simpa [Function.comp_def] using this
    exact tendsto_nhds_unique h1 h2
  rw [← hw]
  simpa [Function.comp_def] using hlim

/-- The compactly perturbed energy `‖u‖² + re ⟪R (J u), J u⟫`. -/
def compactPerturbedEnergy (J : E →L[ℂ] F) (R : F →L[ℂ] F) (u : E) : ℝ :=
  ‖u‖ ^ 2 + (inner ℂ (R (J u)) (J u)).re

/-- Testing a weakly convergent sequence against its limit. -/
theorem tendsto_re_inner_of_weakConvC {u : ℕ → E} {u₀ : E} (h : WeakConvC u u₀) :
    Tendsto (fun n => (inner ℂ u₀ (u n)).re) atTop (𝓝 (‖u₀‖ ^ 2)) := by
  have h0 := (Complex.continuous_re.tendsto _).comp (h (innerSL ℂ u₀))
  have e : (innerSL ℂ u₀ u₀).re = ‖u₀‖ ^ 2 := by
    rw [innerSL_apply_apply]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) u₀
  rw [e] at h0
  simpa [Function.comp_def, innerSL_apply_apply] using h0

/-- `2 re ⟪u₀, v⟫ − ‖u₀‖² ≤ ‖v‖²`. -/
theorem two_re_inner_sub_le (u₀ v : E) : 2 * (inner ℂ u₀ v).re - ‖u₀‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h1 := @norm_sub_sq ℂ E _ _ _ v u₀
  have h2 : RCLike.re (inner ℂ v u₀) = (inner ℂ u₀ v).re := by
    rw [← inner_conj_symm v u₀, RCLike.conj_re]
    rfl
  rw [h2] at h1
  nlinarith [sq_nonneg ‖v - u₀‖]

/-- **Weak lower semicontinuity** of a compactly perturbed energy along bounded sequences. -/
theorem compactPerturbation_le_of_weakConvC {J : E →L[ℂ] F} (hJ : IsCompactOperator J)
    (R : F →L[ℂ] F) {u : ℕ → E} {u₀ : E} (h : WeakConvC u u₀) {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    {μ : ℝ} (hμ : Tendsto (fun n => compactPerturbedEnergy J R (u n)) atTop (𝓝 μ)) :
    compactPerturbedEnergy J R u₀ ≤ μ := by
  have hrc : Continuous fun x : F => (inner ℂ (R x) x).re :=
    Complex.continuous_re.comp (continuous_inner.comp (R.continuous.prodMk continuous_id))
  have hrJ : Tendsto (fun n => (inner ℂ (R (J (u n))) (J (u n))).re) atTop
      (𝓝 ((inner ℂ (R (J u₀)) (J u₀)).re)) :=
    (hrc.tendsto _).comp (tendsto_of_weakConvC hJ h hB)
  -- `‖u_n‖² = Q(u_n) − r(J u_n) → μ − r(J u₀)`
  have hnorm : Tendsto (fun n => ‖u n‖ ^ 2) atTop
      (𝓝 (μ - (inner ℂ (R (J u₀)) (J u₀)).re)) := by
    refine (hμ.sub hrJ).congr fun n => ?_
    simp only [compactPerturbedEnergy]
    ring
  have hle : 2 * ‖u₀‖ ^ 2 - ‖u₀‖ ^ 2 ≤ μ - (inner ℂ (R (J u₀)) (J u₀)).re :=
    le_of_tendsto_of_tendsto' (((tendsto_re_inner_of_weakConvC h).const_mul 2).sub_const _)
      hnorm fun n => two_re_inner_sub_le u₀ (u n)
  simp only [compactPerturbedEnergy]
  linarith

/-- **Adverse profiles of a compactly perturbed energy cannot vanish.** -/
theorem compactPerturbation_adverse_weakLimit {J : E →L[ℂ] F} (hJ : IsCompactOperator J)
    (R : F →L[ℂ] F) {u : ℕ → E} {u₀ : E} (h : WeakConvC u u₀) (hu : ∀ n, ‖u n‖ ≤ 1) {μ : ℝ}
    (hμ0 : μ < 0) (hμ : Tendsto (fun n => compactPerturbedEnergy J R (u n)) atTop (𝓝 μ)) :
    u₀ ≠ 0 ∧ ‖u₀‖ ≤ 1 ∧ compactPerturbedEnergy J R u₀ ≤ μ * ‖u₀‖ ^ 2 := by
  have hQ := compactPerturbation_le_of_weakConvC hJ R h hu hμ
  -- the weak limit stays in the unit ball
  have hnorm1 : ‖u₀‖ ≤ 1 := by
    have hinner := tendsto_re_inner_of_weakConvC h
    have hb : ∀ n, (inner ℂ u₀ (u n)).re ≤ ‖u₀‖ := fun n => by
      calc (inner ℂ u₀ (u n)).re ≤ ‖inner ℂ u₀ (u n)‖ := Complex.re_le_norm _
        _ ≤ ‖u₀‖ * ‖u n‖ := norm_inner_le_norm _ _
        _ ≤ ‖u₀‖ * 1 := mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _)
        _ = ‖u₀‖ := mul_one _
    have := le_of_tendsto' hinner hb
    nlinarith [norm_nonneg u₀]
  have hne : u₀ ≠ 0 := by
    rintro rfl
    simp [compactPerturbedEnergy] at hQ
    linarith
  refine ⟨hne, hnorm1, ?_⟩
  have h1 : ‖u₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u₀]
  nlinarith

/-- The real part of the restricted Weil form is the compactly perturbed archimedean energy. -/
theorem re_ccmRestrictedWeilForm_eq (a : RHTower.SuzukiPositiveAperture)
    (u : RHTower.CCMArchimedeanFormDomain a) :
    (RHTower.ccmRestrictedWeilForm a u u).re =
      compactPerturbedEnergy (RHTower.ccmArchimedeanFormToAperture a)
        (RHTower.ccmRestrictedWeilBoundedRemainder a) u := by
  unfold RHTower.ccmRestrictedWeilForm compactPerturbedEnergy
  rw [Complex.add_re, show (inner ℂ u u).re = ‖u‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) u]

/-- **Adverse profiles of the critical form cannot vanish at a fixed aperture.** -/
theorem ccmRestrictedWeilForm_adverse_weakLimit (a : RHTower.SuzukiPositiveAperture)
    {u : ℕ → RHTower.CCMArchimedeanFormDomain a} {u₀ : RHTower.CCMArchimedeanFormDomain a}
    (h : WeakConvC u u₀) (hu : ∀ n, ‖u n‖ ≤ 1) {μ : ℝ} (hμ0 : μ < 0)
    (hμ : Tendsto (fun n => (RHTower.ccmRestrictedWeilForm a (u n) (u n)).re) atTop (𝓝 μ)) :
    u₀ ≠ 0 ∧ ‖u₀‖ ≤ 1 ∧ (RHTower.ccmRestrictedWeilForm a u₀ u₀).re ≤ μ * ‖u₀‖ ^ 2 := by
  simp only [re_ccmRestrictedWeilForm_eq] at hμ ⊢
  exact compactPerturbation_adverse_weakLimit
    (RHTower.isCompactOperator_ccmArchimedeanFormToAperture a) _ h hu hμ0 hμ

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
