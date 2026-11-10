import GaloisForLFunctions.InfiniteRankWeilTheory.ThePairedXiModelDoesNotLand
import GaloisForLFunctions.RHTower.ArchimedeanBalancedPerron

/-!
# The Riemann Gamma factor and zero count do not force landing

Decomplete the paired Xi model with the entire factor `2/(s Γℝ(s))`.
The resulting function is holomorphic off `1`, has residue one there,
and satisfies the Riemann completed functional equation. Its completed
zeros are all simple and off-line, approach the line, and differ in count
from the actual Xi divisor by at most one. No Euler product or Dirichlet
series representation is asserted for this analytic calibration.
-/

noncomputable section
open Complex Set Filter Topology
open scoped ComplexConjugate
open _root_.RHTower Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

namespace GaloisForLFunctions.InfiniteRankWeilTheory

theorem pairedXiModel_one_ne_zero : pairedXiModel 1 ≠ 0 := by
  intro h
  have := (pairedXiModel_zero_strip h).2
  norm_num at this

/-- The uncompleted calibration, with the pole at zero removed by entire decompletion. -/
def pairedRiemannModel (s : ℂ) : ℂ :=
  pairedXiModel s * boundaryDecompletion s / (2 * pairedXiModel 1 * (s - 1))

/-- Its completion has the usual pair of Riemann poles. -/
def pairedRiemannCompletion (s : ℂ) : ℂ :=
  pairedXiModel s / (pairedXiModel 1 * s * (s - 1))

theorem meromorphicOn_pairedRiemannModel : MeromorphicOn pairedRiemannModel univ := by
  intro s _
  have hn := (differentiable_pairedXiModel.mul boundaryDecompletion_differentiable).analyticAt s
  have hd : AnalyticAt ℂ (fun z : ℂ => 2 * pairedXiModel 1 * (z - 1)) s := by fun_prop
  exact hn.meromorphicAt.div hd.meromorphicAt

theorem differentiableOn_pairedRiemannModel :
    DifferentiableOn ℂ pairedRiemannModel ({1}ᶜ : Set ℂ) := by
  intro s hs
  change s ≠ 1 at hs
  have hd : DifferentiableAt ℂ (fun z : ℂ => 2 * pairedXiModel 1 * (z - 1)) s := by fun_prop
  exact ((differentiable_pairedXiModel.mul boundaryDecompletion_differentiable s).div hd
    (mul_ne_zero (mul_ne_zero two_ne_zero pairedXiModel_one_ne_zero)
      (sub_ne_zero.mpr hs))).differentiableWithinAt

/-- The unique pole has the same residue as zeta. -/
theorem pairedRiemannModel_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * pairedRiemannModel s) (𝓝[≠] 1) (𝓝 1) := by
  have hD : boundaryDecompletion 1 = 2 := by
    rw [boundaryDecompletion_eq (by norm_num)]
    simp only [Complex.Gammaℝ_one, inv_one, mul_one, div_one]
  have hc : Continuous (fun s : ℂ =>
      pairedXiModel s * boundaryDecompletion s / (2 * pairedXiModel 1)) :=
    (differentiable_pairedXiModel.continuous.mul
      boundaryDecompletion_differentiable.continuous).div_const _
  have hv : pairedXiModel 1 * boundaryDecompletion 1 / (2 * pairedXiModel 1) = 1 := by
    rw [hD]
    field_simp [pairedXiModel_one_ne_zero]
  have hlim := (hc.tendsto (1 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change s ≠ 1 at hs
  rw [pairedRiemannModel]
  field_simp [pairedXiModel_one_ne_zero, sub_ne_zero.mpr hs]

/-- Literal Riemann Gamma completion throughout the Euler and critical half-planes. -/
theorem pairedRiemannModel_gamma_completion {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    Complex.Gammaℝ s * pairedRiemannModel s = pairedRiemannCompletion s := by
  have h0 : s ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hs
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [pairedRiemannModel, boundaryDecompletion_eq h0, pairedRiemannCompletion]
  field_simp [pairedXiModel_one_ne_zero, h0, sub_ne_zero.mpr h1, hΓ]
  ring

theorem pairedRiemannCompletion_one_sub (s : ℂ) :
    pairedRiemannCompletion (1 - s) = pairedRiemannCompletion s := by
  rw [pairedRiemannCompletion, pairedRiemannCompletion, pairedXiModel_one_sub]
  congr 1
  ring

/-- The same Gamma factor gives the exact completed functional equation. -/
theorem pairedRiemannModel_functionalEquation {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    Complex.Gammaℝ (1 - s) * pairedRiemannModel (1 - s) =
      Complex.Gammaℝ s * pairedRiemannModel s := by
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h1' : (1 : ℂ) - s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith only [hs.1, hr]
  have hp : 0 < ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs.2]
  rw [pairedRiemannModel_gamma_completion hp h1',
    pairedRiemannModel_gamma_completion hs.1 h1, pairedRiemannCompletion_one_sub]

theorem pairedRiemannModel_zeros_in_strip {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    pairedRiemannModel s = 0 ↔ pairedXiModel s = 0 := by
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hs.1
  rw [pairedRiemannModel, boundaryDecompletion_eq h0]
  simp only [div_eq_zero_iff, mul_eq_zero, inv_eq_zero, hΓ, h0,
    pairedXiModel_one_ne_zero, sub_ne_zero.mpr h1, two_ne_zero, or_false, false_or]

/-- An unconditional Gamma-normalized, order-one landing countermodel with the actual
Riemann count up to an error of one and exact analytic multiplicities. -/
theorem exists_riemann_gamma_counting_model_without_landing :
    ∃ L G : ℂ → ℂ,
      MeromorphicOn L univ ∧ DifferentiableOn ℂ L ({1}ᶜ : Set ℂ) ∧
      Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 1) ∧
      Differentiable ℂ G ∧ (∀ s, G (1 - s) = G s) ∧
      (∀ s, G (conj s) = conj (G s)) ∧ G (1 / 2) = 1 ∧
      (∀ s : ℂ, 0 < s.re → s ≠ 1 →
        Complex.Gammaℝ s * L s = G s / (G 1 * s * (s - 1))) ∧
      (∀ p : ℝ, 1 < p → p ≤ 2 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ s : ℂ, ‖G s‖ ≤ Real.exp (C * ‖s - 1 / 2‖ ^ p)) ∧
      (∀ s : ℂ, G s = 0 → analyticOrderAt G s = 1 ∧
        0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2) ∧
      (∀ T : ℝ, |({s : ℂ | G s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard : ℝ) -
        (xiZeroCount T : ℝ)| ≤ 1) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        |({s : ℂ | G s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard : ℝ) -
          routeKSmoothRVMCount T| ≤ C * Real.log T) ∧
      ∃ Z : ZeroConfig, Z.carrier = {s | G s = 0} ∧
        (∀ s ∈ Z.carrier, analyticOrderAt G s = (Z.mult s : ℕ∞)) ∧
        ApproachesLine Z ∧ (rightOf Z 0).Infinite ∧ ¬ LandingLaw Z := by
  refine ⟨pairedRiemannModel, pairedXiModel, meromorphicOn_pairedRiemannModel,
    differentiableOn_pairedRiemannModel, pairedRiemannModel_residue_one,
    differentiable_pairedXiModel, pairedXiModel_one_sub, pairedXiModel_conj,
    pairedXiModel_half, fun s hs h1 => pairedRiemannModel_gamma_completion hs h1,
    ?_, ?_, pairedXi_zero_count_discrepancy, pairedXiModel_riemannVonMangoldt,
    pairedXiConfig, rfl, pairedXiConfig_mult_eq_analyticOrder,
    pairedXiConfig_approachesLine, pairedXiConfig_infinite_right,
    not_pairedXiConfig_landingLaw⟩
  · intro p hp hp₂
    obtain ⟨C, hC, hbound⟩ := pairedXiProduct_growth hp hp₂
    exact ⟨C, hC, fun s => hbound (s - 1 / 2)⟩
  · intro s hs
    obtain ⟨q, rfl⟩ := (pairedXiModel_eq_zero_iff s).mp hs
    have hstrip := pairedXiModel_zero_strip hs
    exact ⟨analyticOrderAt_pairedXiModel q, hstrip.1, hstrip.2,
      fun hline => pairedXiModel_ne_zero_on_line hline hs⟩

#print axioms pairedRiemannModel_residue_one
#print axioms pairedRiemannModel_functionalEquation
#print axioms exists_riemann_gamma_counting_model_without_landing

end GaloisForLFunctions.InfiniteRankWeilTheory
