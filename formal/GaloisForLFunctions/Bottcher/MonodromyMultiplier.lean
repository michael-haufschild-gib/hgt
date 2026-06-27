/-
# Böttcher tower — Tier 3: period ⟹ monodromy multiplier of order 2ⁿ

Chains the verified period formula (`period_eq`: `∮_γ dlogφ_c = 2πi·(enclosed mass)`)
to the dyadic order count (`orderOf_dyadicRoot`). When the loop encloses a depth-`n`
Cantor cylinder of equilibrium mass `2⁻ⁿ`, the monodromy multiplier `exp(∮_γ dlogφ_c)`
is `exp(2πi/2ⁿ)` — a primitive `2ⁿ`-th root of unity.

This is the order+multiplier content of the `mono` input to the disconnected case
(`algIndep_of_unbounded_monodromy`). The one remaining (analytic) piece is that
continuation around `γ` realises this multiplier as a field automorphism of the germ
field — the germ-field/deck-transformation construction.
-/
import GaloisForLFunctions.Bottcher.Period
import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.Bottcher.Brolin

open Complex Metric MeasureTheory

namespace Bottcher

/-- **Period ⟹ dyadic multiplier order.** If the loop `C(c,R)` is separated from
`supp μ_c` and encloses equilibrium mass exactly `2⁻ⁿ` (a depth-`n` Cantor cylinder
under Brolin's balanced measure), the monodromy multiplier `exp(∮_γ dlogφ_c)` has
order exactly `2ⁿ`. -/
theorem multiplier_orderOf_of_mass (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℂ} {R : ℝ}
    (n : ℕ) (h0 : 0 ≤ R) (hsphere : μ (sphere c R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ))
    (hmass : (μ (ball c R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ)) = 2 ^ n := by
  rw [period_eq μ h0 hsphere hint, hmass,
      show 2 * (Real.pi : ℂ) * Complex.I * ((((2 ^ n : ℕ) : ℝ))⁻¹ : ℝ)
         = 2 * (Real.pi : ℂ) * Complex.I / (((2 ^ n : ℕ) : ℂ)) from by push_cast; ring]
  exact orderOf_dyadicRoot n

/-- GAP-A/hDisc period bridge for the packaged Brolin measure `μ_c`.
Once a `BrolinMeasure c` is supplied, its underlying Riesz measure is a probability
measure and can be fed directly into the contour-period formula. -/
theorem period_eq_brolinMeasure {c : ℂ} (M : BrolinMeasure c) {a : ℂ} {R : ℝ}
    (h0 : 0 ≤ R) (hsphere : M.μ (sphere a R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod M.μ)) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂M.μ)
      = 2 * (Real.pi : ℂ) * Complex.I * (M.μ (ball a R)).toReal := by
  haveI : IsProbabilityMeasure M.μ := M.probOn.1
  exact period_eq M.μ h0 hsphere hint

/-- A separated circle has an integrable Cauchy kernel against any finite
measure.  This is the local hDisc analytic input used to discharge the raw
Fubini integrability hypothesis in `period_eq`. -/
theorem circleCauchyKernel_integrable_of_ae_separated
    (μ : Measure ℂ) [IsFiniteMeasure μ] {a : ℂ} {R δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ),
      δ ≤ ‖circleMap a R p.1 - p.2‖) :
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ) := by
  refine Integrable.of_bound ?_ (|R| * δ⁻¹) ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [hsep] with p hp
    rcases p with ⟨θ, ζ⟩
    dsimp only [Function.uncurry]
    have hderiv : ‖deriv (circleMap a R) θ‖ = |R| := by
      rw [(hasDerivAt_circleMap a R θ).deriv, norm_mul]
      simp [circleMap]
    have hinv : ‖(circleMap a R θ - ζ)⁻¹‖ ≤ δ⁻¹ := by
      rw [norm_inv]
      gcongr
    rw [norm_smul, hderiv]
    exact mul_le_mul_of_nonneg_left hinv (abs_nonneg R)

/-- Existential separated-loop form of
`circleCauchyKernel_integrable_of_ae_separated`. -/
theorem circleCauchyKernel_integrable_of_exists_ae_separated
    (μ : Measure ℂ) [IsFiniteMeasure μ] {a : ℂ} {R : ℝ}
    (hsep : ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ),
        δ ≤ ‖circleMap a R p.1 - p.2‖) :
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ) := by
  rcases hsep with ⟨δ, hδ, hδsep⟩
  exact circleCauchyKernel_integrable_of_ae_separated μ hδ hδsep

/-- GAP-A/hDisc period bridge for the constructed limiting measure `brolinMuOne`.
This uses the actual no-hypothesis Brolin limit constructed in `Brolin.lean`,
not the stronger packaged Riesz interface. -/
theorem period_eq_brolinMuOne (c : ℂ) {a : ℂ} {R : ℝ}
    (h0 : 0 ≤ R) (hsphere : brolinMuOne c (sphere a R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c))) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  exact period_eq (brolinMuOne c) h0 hsphere hint

/-- GAP-A/hDisc period bridge for `brolinMuOne` with the Fubini
integrability hypothesis discharged by separated-loop geometry. -/
theorem period_eq_brolinMuOne_of_exists_ae_separated
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : brolinMuOne c (sphere a R) = 0)
    (hsep : ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
        δ ≤ ‖circleMap a R p.1 - p.2‖) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  exact period_eq_brolinMuOne c h0 hsphere
    (circleCauchyKernel_integrable_of_exists_ae_separated (brolinMuOne c) hsep)

/-- A circle disjoint from `K_c` has zero mass for the constructed limiting
measure. -/
theorem brolinMuOne_sphere_eq_zero_of_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ}
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    brolinMuOne c (sphere a R) = 0 :=
  measure_mono_null hsphere (brolinMuOne_hDiscCore c).1.2

/-- If the parametrized circle is uniformly separated from `K_c`, then the
geometric circle is disjoint from `K_c`. -/
theorem sphere_subset_filledJulia_compl_of_circle_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ} (h0 : 0 ≤ R) (hδ : 0 < δ)
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    sphere a R ⊆ (filledJulia c)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff]
  intro hK
  have hrange : Set.range (circleMap a R) = sphere a R := by
    rw [range_circleMap, abs_of_nonneg h0]
  rw [← hrange] at hz
  rcases hz with ⟨θ, rfl⟩
  have hbad : δ ≤ 0 := by
    simpa using hsep θ (circleMap a R θ) hK
  linarith

/-- A circle disjoint from the compact filled Julia set is uniformly separated
from it. -/
theorem exists_circle_filledJulia_separation_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
        δ ≤ ‖circleMap a R θ - ζ‖ := by
  rcases (filledJulia c).eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨1, one_pos, ?_⟩
    intro _θ ζ hζ
    rw [hKempty] at hζ
    simp at hζ
  · have hScompact : IsCompact (sphere a R) := isCompact_sphere a R
    have hKcompact : IsCompact (filledJulia c) := isCompact_filledJulia c
    have hprodcompact : IsCompact (sphere a R ×ˢ filledJulia c) :=
      hScompact.prod hKcompact
    have hSne : (sphere a R).Nonempty :=
      ⟨circleMap a R 0, circleMap_mem_sphere a h0 0⟩
    have hprodne : (sphere a R ×ˢ filledJulia c).Nonempty := by
      rcases hSne with ⟨x, hx⟩
      rcases hKne with ⟨y, hy⟩
      exact ⟨(x, y), hx, hy⟩
    have hcont : ContinuousOn (fun p : ℂ × ℂ => ‖p.1 - p.2‖)
        (sphere a R ×ˢ filledJulia c) :=
      ((continuous_fst.sub continuous_snd).norm).continuousOn
    rcases hprodcompact.exists_isMinOn hprodne hcont with ⟨p, hp, hpmin⟩
    have hpnorm_pos : 0 < ‖p.1 - p.2‖ := by
      have hpS : p.1 ∈ sphere a R := hp.1
      have hpK : p.2 ∈ filledJulia c := hp.2
      have hne : p.1 - p.2 ≠ 0 := by
        intro hzero
        have heq : p.1 = p.2 := sub_eq_zero.mp hzero
        exact (hsphere hpS) (by simpa [heq] using hpK)
      exact norm_pos_iff.mpr hne
    refine ⟨‖p.1 - p.2‖ / 2, by linarith, ?_⟩
    intro θ ζ hζ
    have hpθζ : (circleMap a R θ, ζ) ∈ sphere a R ×ˢ filledJulia c :=
      ⟨circleMap_mem_sphere a h0 θ, hζ⟩
    have hmin := hpmin hpθζ
    dsimp at hmin
    linarith

/-- Support of `brolinMuOne` upgrades pointwise separation from `K_c` to the
product-a.e. separation required by the circle Cauchy-kernel bound. -/
theorem brolinMuOne_circle_ae_separated_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ}
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
      δ ≤ ‖circleMap a R p.1 - p.2‖ := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  have hnull : ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c))
      {p : ℝ × ℂ | p.2 ∉ filledJulia c} = 0 := by
    have hset : {p : ℝ × ℂ | p.2 ∉ filledJulia c} = Set.univ ×ˢ (filledJulia c)ᶜ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, (brolinMuOne_hDiscCore c).1.2, mul_zero]
  have hpairs :
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
        p.2 ∈ filledJulia c := by
    exact (mem_ae_iff).2 hnull
  filter_upwards [hpairs] with p hp
  exact hsep p.1 p.2 hp

/-- The constructed limiting measure has an integrable circle Cauchy kernel
whenever the circle is uniformly separated from `K_c`. -/
theorem brolinMuOne_cauchyKernel_integrable_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)) := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  exact circleCauchyKernel_integrable_of_ae_separated
    (brolinMuOne c) hδ
    (brolinMuOne_circle_ae_separated_of_filledJulia_separated c hsep)

/-- GAP-A/hDisc period bridge with explicit Fubini integrability retained for
internal reuse. -/
theorem period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl_with_integrability
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c))) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal :=
  period_eq_brolinMuOne c h0
    (brolinMuOne_sphere_eq_zero_of_subset_filledJulia_compl c hsphere) hint

/-- GAP-A/hDisc period bridge for a loop disjoint from `K_c`.  Compactness
supplies the separation needed for Fubini integrability. -/
theorem period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal := by
  rcases exists_circle_filledJulia_separation_of_sphere_subset_filledJulia_compl
    c h0 hsphere with ⟨δ, hδ, hsep⟩
  exact period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl_with_integrability
    c h0 hsphere
    (brolinMuOne_cauchyKernel_integrable_of_filledJulia_separated c hδ hsep)

/-- GAP-A/hDisc period bridge for a circle uniformly separated from `K_c`.
The constructed limiting measure supplies support; the separation supplies both
sphere-nullity and Fubini integrability. -/
theorem period_eq_brolinMuOne_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ} (h0 : 0 ≤ R) (hδ : 0 < δ)
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal :=
  period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl_with_integrability c h0
    (sphere_subset_filledJulia_compl_of_circle_filledJulia_separated c h0 hδ hsep)
    (brolinMuOne_cauchyKernel_integrable_of_filledJulia_separated c hδ hsep)

/-- GAP-A/hDisc period bridge for a loop separated from `K_c`, with both
measure-theoretic inputs supplied by the constructed limiting measure: support
gives sphere-nullity and separation gives Fubini integrability. -/
theorem period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl_of_exists_ae_separated
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hsep : ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
        δ ≤ ‖circleMap a R p.1 - p.2‖) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMuOne c) (ball a R)).toReal :=
  period_eq_brolinMuOne_of_exists_ae_separated c h0
    (brolinMuOne_sphere_eq_zero_of_subset_filledJulia_compl c hsphere) hsep

/-- GAP-A/hDisc multiplier bridge for `μ_c`: if a separated loop encloses Brolin
mass `2⁻ⁿ`, the corresponding Cauchy-transform period gives a primitive
`2ⁿ`-th multiplier. -/
theorem multiplier_orderOf_brolinMeasure_of_mass {c : ℂ} (M : BrolinMeasure c)
    {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : M.μ (sphere a R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod M.μ))
    (hmass : (M.μ (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂M.μ)) = 2 ^ n := by
  haveI : IsProbabilityMeasure M.μ := M.probOn.1
  exact multiplier_orderOf_of_mass M.μ n h0 hsphere hint hmass

/-- GAP-A/hDisc multiplier bridge for the constructed limiting measure
`brolinMuOne`.  Once a loop encloses mass `2⁻ⁿ`, the Cauchy-transform period of
the constructed measure gives a primitive `2ⁿ`-th multiplier. -/
theorem multiplier_orderOf_brolinMuOne_of_mass (c : ℂ)
    {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : brolinMuOne c (sphere a R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)))
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  exact multiplier_orderOf_of_mass (brolinMuOne c) n h0 hsphere hint hmass

/-- GAP-A/hDisc multiplier bridge for `brolinMuOne` with Fubini
integrability supplied by separated-loop geometry. -/
theorem multiplier_orderOf_brolinMuOne_of_mass_of_exists_ae_separated
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : brolinMuOne c (sphere a R) = 0)
    (hsep : ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
        δ ≤ ‖circleMap a R p.1 - p.2‖)
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n := by
  haveI : IsProbabilityMeasure (brolinMuOne c) := by
    dsimp [brolinMuOne]
    infer_instance
  exact multiplier_orderOf_brolinMuOne_of_mass c n h0 hsphere
    (circleCauchyKernel_integrable_of_exists_ae_separated (brolinMuOne c) hsep) hmass

/-- GAP-A/hDisc multiplier bridge with explicit Fubini integrability retained
for internal reuse. -/
theorem multiplier_orderOf_brolinMuOne_of_mass_of_sphere_subset_filledJulia_compl_with_integrability
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)))
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n :=
  multiplier_orderOf_brolinMuOne_of_mass c n h0
    (brolinMuOne_sphere_eq_zero_of_subset_filledJulia_compl c hsphere) hint hmass

/-- GAP-A/hDisc multiplier bridge for a circle uniformly separated from
`K_c`.  The only remaining geometric input is the enclosed Brolin mass. -/
theorem multiplier_orderOf_brolinMuOne_of_mass_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ} (n : ℕ) (h0 : 0 ≤ R) (hδ : 0 < δ)
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖)
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n :=
  multiplier_orderOf_brolinMuOne_of_mass_of_sphere_subset_filledJulia_compl_with_integrability
    c n h0
    (sphere_subset_filledJulia_compl_of_circle_filledJulia_separated c h0 hδ hsep)
    (brolinMuOne_cauchyKernel_integrable_of_filledJulia_separated c hδ hsep) hmass

/-- GAP-A/hDisc multiplier bridge for a loop disjoint from `K_c`; compactness
supplies the separation needed for Fubini integrability.  The remaining input
is exactly the enclosed Brolin mass. -/
theorem multiplier_orderOf_brolinMuOne_of_mass_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n := by
  rcases exists_circle_filledJulia_separation_of_sphere_subset_filledJulia_compl
    c h0 hsphere with ⟨δ, hδ, hsep⟩
  exact multiplier_orderOf_brolinMuOne_of_mass_of_filledJulia_separated
    c n h0 hδ hsep hmass

/-- GAP-A/hDisc multiplier bridge for a loop separated from `K_c`, with
sphere-nullity and Fubini integrability discharged before the dyadic order
calculation. -/
theorem multiplier_orderOf_brolinMuOne_of_mass_of_sphere_subset_filledJulia_compl_of_exists_ae_separated
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hsep : ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMuOne c)),
        δ ≤ ‖circleMap a R p.1 - p.2‖)
    (hmass : ((brolinMuOne c) (ball a R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOne c)) = 2 ^ n :=
  multiplier_orderOf_brolinMuOne_of_mass_of_exists_ae_separated c n h0
    (brolinMuOne_sphere_eq_zero_of_subset_filledJulia_compl c hsphere) hsep hmass

/-- A circle disjoint from `K_c` has zero mass for the zero-target constructed
limiting measure `brolinMu`. -/
theorem brolinMu_sphere_eq_zero_of_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ}
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    brolinMu c (sphere a R) = 0 :=
  measure_mono_null hsphere (brolinMu_hDiscCore c).1.2

/-- Support of the zero-target constructed limiting measure upgrades pointwise
separation from `K_c` to the product-a.e. separation needed for the circle
Cauchy-kernel bound. -/
theorem brolinMu_circle_ae_separated_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ}
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMu c)),
      δ ≤ ‖circleMap a R p.1 - p.2‖ := by
  haveI : IsProbabilityMeasure (brolinMu c) := (brolinMu_hDiscCore c).1.1
  have hnull : ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMu c))
      {p : ℝ × ℂ | p.2 ∉ filledJulia c} = 0 := by
    have hset : {p : ℝ × ℂ | p.2 ∉ filledJulia c} = Set.univ ×ˢ (filledJulia c)ᶜ := by
      ext p
      simp
    rw [hset, Measure.prod_prod, (brolinMu_hDiscCore c).1.2, mul_zero]
  have hpairs :
      ∀ᵐ p ∂((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMu c)),
        p.2 ∈ filledJulia c := by
    exact (mem_ae_iff).2 hnull
  filter_upwards [hpairs] with p hp
  exact hsep p.1 p.2 hp

/-- The zero-target constructed limiting measure has an integrable circle
Cauchy kernel whenever the circle is uniformly separated from `K_c`. -/
theorem brolinMu_cauchyKernel_integrable_of_filledJulia_separated
    (c : ℂ) {a : ℂ} {R δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ θ : ℝ, ∀ ζ : ℂ, ζ ∈ filledJulia c →
      δ ≤ ‖circleMap a R θ - ζ‖) :
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap a R) θ • (circleMap a R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod (brolinMu c)) := by
  haveI : IsProbabilityMeasure (brolinMu c) := (brolinMu_hDiscCore c).1.1
  exact circleCauchyKernel_integrable_of_ae_separated
    (brolinMu c) hδ
    (brolinMu_circle_ae_separated_of_filledJulia_separated c hsep)

/-- GAP-A/hDisc period bridge for the zero-target constructed limiting measure
`brolinMu`, for a loop disjoint from `K_c`.  Compactness supplies the
separation needed for Fubini integrability. -/
theorem period_eq_brolinMu_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMu c)
      = 2 * (Real.pi : ℂ) * Complex.I * ((brolinMu c) (ball a R)).toReal := by
  rcases exists_circle_filledJulia_separation_of_sphere_subset_filledJulia_compl
    c h0 hsphere with ⟨δ, hδ, hsep⟩
  haveI : IsProbabilityMeasure (brolinMu c) := (brolinMu_hDiscCore c).1.1
  exact period_eq (brolinMu c) h0
    (brolinMu_sphere_eq_zero_of_subset_filledJulia_compl c hsphere)
    (brolinMu_cauchyKernel_integrable_of_filledJulia_separated c hδ hsep)

/-- GAP-A/hDisc multiplier bridge for the zero-target constructed limiting
measure `brolinMu`.  The remaining input is exactly the enclosed Brolin mass. -/
theorem multiplier_orderOf_brolinMu_of_mass_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hmass : ((brolinMu c) (ball a R)).toReal =
      (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf (Complex.exp (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMu c)) =
      2 ^ n := by
  rcases exists_circle_filledJulia_separation_of_sphere_subset_filledJulia_compl
    c h0 hsphere with ⟨δ, hδ, hsep⟩
  haveI : IsProbabilityMeasure (brolinMu c) := (brolinMu_hDiscCore c).1.1
  exact multiplier_orderOf_of_mass (brolinMu c) n h0
    (brolinMu_sphere_eq_zero_of_subset_filledJulia_compl c hsphere)
    (brolinMu_cauchyKernel_integrable_of_filledJulia_separated c hδ hsep)
    hmass

/-- GAP-A/hDisc period bridge stated directly for the zero-target limiting
Riesz-measure object. -/
theorem period_eq_brolinMuRieszMeasure_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuRieszMeasure c)
      = 2 * (Real.pi : ℂ) * Complex.I *
        ((brolinMuRieszMeasure c) (ball a R)).toReal := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact period_eq_brolinMu_of_sphere_subset_filledJulia_compl c h0 hsphere

/-- GAP-A/hDisc multiplier bridge stated directly for the zero-target limiting
Riesz-measure object.  The remaining input is exactly the enclosed mass of that
constructed measure. -/
theorem multiplier_orderOf_brolinMuRieszMeasure_of_mass_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hmass : ((brolinMuRieszMeasure c) (ball a R)).toReal =
      (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf
      (Complex.exp
        (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuRieszMeasure c)) =
      2 ^ n := by
  rw [brolinMuRieszMeasure_eq_brolinMu] at hmass ⊢
  exact multiplier_orderOf_brolinMu_of_mass_of_sphere_subset_filledJulia_compl
    c n h0 hsphere hmass

/-- GAP-A/hDisc period bridge stated directly for the canonical limiting
Riesz-measure object. -/
theorem period_eq_brolinMuOneRieszMeasure_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ) :
    (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOneRieszMeasure c)
      = 2 * (Real.pi : ℂ) * Complex.I *
        ((brolinMuOneRieszMeasure c) (ball a R)).toReal := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne]
  exact period_eq_brolinMuOne_of_sphere_subset_filledJulia_compl c h0 hsphere

/-- GAP-A/hDisc multiplier bridge stated directly for the canonical limiting
Riesz-measure object.  The remaining input is exactly the enclosed mass of that
constructed measure. -/
theorem multiplier_orderOf_brolinMuOneRieszMeasure_of_mass_of_sphere_subset_filledJulia_compl
    (c : ℂ) {a : ℂ} {R : ℝ} (n : ℕ) (h0 : 0 ≤ R)
    (hsphere : sphere a R ⊆ (filledJulia c)ᶜ)
    (hmass : ((brolinMuOneRieszMeasure c) (ball a R)).toReal =
      (((2 ^ n : ℕ) : ℝ))⁻¹) :
    orderOf
      (Complex.exp
        (∮ z in C(a, R), ∫ ζ, (z - ζ)⁻¹ ∂brolinMuOneRieszMeasure c)) =
      2 ^ n := by
  rw [brolinMuOneRieszMeasure_eq_brolinMuOne] at hmass ⊢
  exact multiplier_orderOf_brolinMuOne_of_mass_of_sphere_subset_filledJulia_compl
    c n h0 hsphere hmass

end Bottcher
