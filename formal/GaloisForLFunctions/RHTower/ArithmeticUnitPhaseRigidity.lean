import GaloisForLFunctions.RHTower.ArithmeticPrimeSievePhase
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Exact local classification of the arithmetic unit-phase factorization

The literal unit remainder is the conjugate of a holomorphic source `G`. On a connected open
strip domain, the proposed identity `Im(g(1)) = Im(ζ H)` is equivalent to `G + ζ H = c` for one
real constant. The rational boundary separates all distinct positive-height zeros. At a zero,
a holomorphic phase germ exists exactly when the zero is simple and on the critical line.
The converse constructs the removable quotient from analytic divided differences.

These are unconditional classification theorems. They do not assert the existence of such a
germ at every zero, simplicity of all zeros, or RH. The global and finite-cover obstructions
using the analytic Hardy theorem are isolated in `ArithmeticUnitPhaseNoGo`.
-/

open Complex Filter Set
open scoped Topology

namespace RHTower.DeletionMixedRefinement
noncomputable section

/-- The holomorphic rational boundary of the unconjugated unit source. -/
def unitPhaseBoundary (s : ℂ) : ℂ := -(s * (1 - s))⁻¹ / 2

/-- The unconjugated literal unit remainder, retaining the full zeta discrepancy. -/
def unitPhaseSource (s : ℂ) : ℂ := unitPhaseBoundary s - normalizedMinimumZeta s

/-- The proposed phase identity at every point of a domain, including its zeros. -/
def UnitPhaseIdentity (U : Set ℂ) (H : ℂ → ℂ) : Prop :=
  ∀ s ∈ U, (normalizedWeightedRemainder s 1).im = (riemannZeta s * H s).im

/-- The critical strip is open. -/
theorem unitPhaseStrip_open : IsOpen minimumStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- The critical strip is nonempty and connected. -/
theorem unitPhaseStrip_connected : IsConnected minimumStrip :=
  ⟨⟨1 / 2, by norm_num [minimumStrip]⟩,
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected⟩

/-- Strip membership excludes all rational denominators used in the source. -/
theorem unitPhaseStrip_denominators {s : ℂ} (hs : s ∈ minimumStrip) :
    s ≠ 0 ∧ s ≠ 1 ∧ s + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; subst s; norm_num [minimumStrip] at hs
  · intro h; subst s; norm_num [minimumStrip] at hs
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    have := hs.1
    linarith

/-- Zeta is analytic throughout the critical strip. -/
theorem unitPhaseZeta_analytic : AnalyticOnNhd ℂ riemannZeta minimumStrip := by
  have h : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  intro s hs
  exact (h.analyticOnNhd isOpen_compl_singleton) s
    (by simpa using (unitPhaseStrip_denominators hs).2.1)

/-- The rational zero boundary is analytic throughout the strip. -/
theorem unitPhaseBoundary_analytic : AnalyticOnNhd ℂ unitPhaseBoundary minimumStrip := by
  intro s hs
  have hd := unitPhaseStrip_denominators hs
  exact (((analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).inv
    (mul_ne_zero hd.1 (sub_ne_zero.mpr hd.2.1.symm))).neg).div
      analyticAt_const (by norm_num)

/-- The literal unconjugated unit source is analytic throughout the strip. -/
theorem unitPhaseSource_analytic : AnalyticOnNhd ℂ unitPhaseSource minimumStrip := by
  intro s hs
  have hd := unitPhaseStrip_denominators hs
  exact (unitPhaseBoundary_analytic s hs).sub ((unitPhaseZeta_analytic s hs).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hd.1 hd.2.2))

/-- Exact link to the existing arithmetic remainder; conjugation is retained. -/
theorem normalizedWeightedRemainder_one_eq_star_source {s : ℂ} (hs : s ∈ minimumStrip) :
    normalizedWeightedRemainder s 1 = star (unitPhaseSource s) := by
  rw [normalizedWeightedRemainder_one_eq_boundary hs.1 hs.2]
  simp [unitPhaseSource, unitPhaseBoundary, minimumZeroBoundary, normalizedMinimumZeta,
    star_sub, star_div₀, star_neg, star_inv₀, star_mul]
  ring

/-- The conjugation changes the proposed identity into reality of the source sum. -/
theorem unitPhaseIdentity_iff_source_im_zero {U : Set ℂ} {H : ℂ → ℂ}
    (hU : U ⊆ minimumStrip) :
    UnitPhaseIdentity U H ↔ ∀ s ∈ U, (unitPhaseSource s + riemannZeta s * H s).im = 0 := by
  simp only [UnitPhaseIdentity]
  constructor <;> intro h s hs <;>
    have he := normalizedWeightedRemainder_one_eq_star_source (hU hs)
  · have hi := h s hs
    rw [he, Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.add_im]
    linarith
  · have hi := h s hs
    rw [he, Complex.star_def, Complex.conj_im]
    simp only [Complex.add_im] at hi
    linarith

/-- Open mapping gives the exhaustive real-constant classification on a connected domain. -/
theorem unitPhaseIdentity_iff_real_constant {U : Set ℂ} {H : ℂ → ℂ}
    (hU : U ⊆ minimumStrip) (ho : IsOpen U) (hc : IsConnected U)
    (hH : AnalyticOnNhd ℂ H U) :
    UnitPhaseIdentity U H ↔
      ∃ c : ℝ, ∀ s ∈ U, unitPhaseSource s + riemannZeta s * H s = c := by
  rw [unitPhaseIdentity_iff_source_im_zero hU]
  constructor
  · intro h
    have ha : AnalyticOnNhd ℂ (fun s => unitPhaseSource s + riemannZeta s * H s) U :=
      fun s hs => (unitPhaseSource_analytic s (hU hs)).add
        ((unitPhaseZeta_analytic s (hU hs)).mul (hH s hs))
    obtain ⟨c, he⟩ := ha.eq_const_add_im_mul_I_of_re_eq_const h ho hc
    exact ⟨c, by simpa using he⟩
  · rintro ⟨c, he⟩ s hs
    rw [he s hs]
    simp

/-- The rational boundary identifies precisely equal points or reflection partners. -/
theorem unitPhaseBoundary_eq_iff {s t : ℂ} :
    unitPhaseBoundary s = unitPhaseBoundary t ↔ s = t ∨ s + t = 1 := by
  have h : unitPhaseBoundary s = unitPhaseBoundary t ↔ s * (1 - s) = t * (1 - t) := by
    simp only [unitPhaseBoundary, div_left_inj' (by norm_num : (2 : ℂ) ≠ 0),
      neg_inj, inv_inj]
  rw [h]
  constructor
  · intro he
    have hp : (s - t) * (1 - s - t) = 0 := by linear_combination he
    rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl (sub_eq_zero.mp hp)
    · right; linear_combination -hp
  · rintro (rfl | he)
    · rfl
    · have ht : t = 1 - s := by linear_combination he
      rw [ht]
      ring

/-- Each connected phase chart contains at most one positive-height zero. -/
theorem unitPhaseIdentity_positive_zeros_subsingleton {U : Set ℂ} {H : ℂ → ℂ}
    (hU : U ⊆ minimumStrip) (ho : IsOpen U) (hc : IsConnected U)
    (hH : AnalyticOnNhd ℂ H U) (hi : UnitPhaseIdentity U H) :
    Set.Subsingleton {s | s ∈ U ∧ 0 < s.im ∧ riemannZeta s = 0} := by
  obtain ⟨c, he⟩ := (unitPhaseIdentity_iff_real_constant hU ho hc hH).mp hi
  intro s hs t ht
  have hb : unitPhaseBoundary s = unitPhaseBoundary t := by
    have h1 := he s hs.1
    have h2 := he t ht.1
    simp [unitPhaseSource, normalizedMinimumZeta, hs.2.2, ht.2.2] at h1 h2
    exact h1.trans h2.symm
  rcases unitPhaseBoundary_eq_iff.mp hb with heq | heq
  · exact heq
  · have hm := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.one_im] at hm
    linarith [hs.2.1, ht.2.1]


/-- Every real constant gives an analytic multiplier on a zero-free strip domain. -/
theorem unitPhaseIdentity_zero_free {U : Set ℂ} (hU : U ⊆ minimumStrip)
    (hz : ∀ s ∈ U, riemannZeta s ≠ 0) (c : ℝ) :
    AnalyticOnNhd ℂ (fun s => ((c : ℂ) - unitPhaseSource s) / riemannZeta s) U ∧
      UnitPhaseIdentity U (fun s => ((c : ℂ) - unitPhaseSource s) / riemannZeta s) := by
  refine ⟨fun s hs => (analyticAt_const.sub (unitPhaseSource_analytic s (hU hs))).div
    (unitPhaseZeta_analytic s (hU hs)) (hz s hs), ?_⟩
  apply (unitPhaseIdentity_iff_source_im_zero hU).mpr
  intro s hs
  have he : unitPhaseSource s + riemannZeta s *
      (((c : ℂ) - unitPhaseSource s) / riemannZeta s) = (c : ℂ) := by
    field_simp [hz s hs]
    ring
  rw [he]
  simp

/-- On a connected zero-free domain these real-constant quotients exhaust all multipliers. -/
theorem unitPhaseIdentity_zero_free_iff {U : Set ℂ} {H : ℂ → ℂ}
    (hU : U ⊆ minimumStrip) (ho : IsOpen U) (hc : IsConnected U)
    (hH : AnalyticOnNhd ℂ H U) (hz : ∀ s ∈ U, riemannZeta s ≠ 0) :
    UnitPhaseIdentity U H ↔
      ∃ c : ℝ, ∀ s ∈ U, H s = ((c : ℂ) - unitPhaseSource s) / riemannZeta s := by
  rw [unitPhaseIdentity_iff_real_constant hU ho hc hH]
  constructor
  · rintro ⟨c, he⟩
    refine ⟨c, fun s hs => ?_⟩
    apply (eq_div_iff (hz s hs)).mpr
    linear_combination he s hs
  · rintro ⟨c, he⟩
    refine ⟨c, fun s hs => ?_⟩
    rw [he s hs]
    field_simp [hz s hs]
    ring

/-- A multiplier analytic at the parameter, satisfying the identity throughout a neighborhood. -/
def UnitPhaseGerm (ρ : ℂ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
    ∀ᶠ s in 𝓝 ρ, (normalizedWeightedRemainder s 1).im = (riemannZeta s * H s).im

/-- A phase germ gives a real constant on a neighborhood, not merely at its center. -/
theorem unitPhaseGerm_real_constant {ρ : ℂ} {H : ℂ → ℂ}
    (hρ : ρ ∈ minimumStrip) (hH : AnalyticAt ℂ H ρ)
    (hi : ∀ᶠ s in 𝓝 ρ,
      (normalizedWeightedRemainder s 1).im = (riemannZeta s * H s).im) :
    ∃ c : ℝ, ∀ᶠ s in 𝓝 ρ, unitPhaseSource s + riemannZeta s * H s = c := by
  have hstrip : ∀ᶠ s in 𝓝 ρ, s ∈ minimumStrip := unitPhaseStrip_open.mem_nhds hρ
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp
    (hstrip.and (hH.eventually_analyticAt.and hi))
  have hs : Metric.ball ρ r ⊆ minimumStrip := fun s hs => (hb hs).1
  have ha : AnalyticOnNhd ℂ H (Metric.ball ρ r) := fun s hs => (hb hs).2.1
  have he : UnitPhaseIdentity (Metric.ball ρ r) H := fun s hs => (hb hs).2.2
  obtain ⟨c, hc⟩ := (unitPhaseIdentity_iff_real_constant hs Metric.isOpen_ball
    (Metric.isConnected_ball hr) ha).mp he
  exact ⟨c, Filter.eventually_of_mem (Metric.ball_mem_nhds ρ hr) hc⟩

/-- The boundary imaginary part records signed displacement from the critical line. -/
theorem unitPhaseBoundary_im (s : ℂ) :
    (unitPhaseBoundary s).im =
      s.im * (1 - 2 * s.re) / (2 * Complex.normSq (s * (1 - s))) := by
  simp only [unitPhaseBoundary, Complex.div_ofNat_im, Complex.neg_im, Complex.inv_im,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- At positive height, the rational boundary is real exactly on the critical line. -/
theorem unitPhaseBoundary_im_eq_zero_iff {ρ : ℂ} (hρ : ρ ∈ minimumStrip)
    (ht : 0 < ρ.im) : (unitPhaseBoundary ρ).im = 0 ↔ ρ.re = 1 / 2 := by
  have hd := unitPhaseStrip_denominators hρ
  have hnorm : Complex.normSq (ρ * (1 - ρ)) ≠ 0 :=
    (not_congr Complex.normSq_eq_zero).mpr (mul_ne_zero hd.1 (sub_ne_zero.mpr hd.2.1.symm))
  rw [unitPhaseBoundary_im, div_eq_zero_iff]
  constructor
  · intro h
    have hn := h.resolve_right (mul_ne_zero (by norm_num) hnorm)
    have hr := (mul_eq_zero.mp hn).resolve_left (ne_of_gt ht)
    linarith
  · intro h
    left
    rw [h]
    ring

/-- The exact complex derivative of the rational boundary. -/
theorem hasDerivAt_unitPhaseBoundary {s : ℂ} (hs : s ∈ minimumStrip) :
    HasDerivAt unitPhaseBoundary ((1 - 2 * s) / (2 * (s * (1 - s)) ^ 2)) s := by
  have hd := unitPhaseStrip_denominators hs
  have hp := (hasDerivAt_id s).mul ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))
  have hi := ((hp.inv (mul_ne_zero hd.1 (sub_ne_zero.mpr hd.2.1.symm))).neg).div_const 2
  convert! hi using 1
  dsimp [unitPhaseBoundary]
  field_simp
  ring

/-- Differentiating a phase germ at a zero fixes its nonzero first-order balance. -/
theorem unitPhaseGerm_tangent {ρ : ℂ} {H : ℂ → ℂ}
    (hρ : ρ ∈ minimumStrip) (hz : riemannZeta ρ = 0) (hH : AnalyticAt ℂ H ρ)
    (hi : ∀ᶠ s in 𝓝 ρ,
      (normalizedWeightedRemainder s 1).im = (riemannZeta s * H s).im) :
    deriv riemannZeta ρ * (H ρ - 1 / (ρ * (ρ + 1))) =
      -(1 - 2 * ρ) / (2 * (ρ * (1 - ρ)) ^ 2) := by
  obtain ⟨c, hc⟩ := unitPhaseGerm_real_constant hρ hH hi
  have hd := unitPhaseStrip_denominators hρ
  have hz' : HasDerivAt riemannZeta (deriv riemannZeta ρ) ρ :=
    (unitPhaseZeta_analytic ρ hρ).differentiableAt.hasDerivAt
  have hq : HasDerivAt normalizedMinimumZeta (deriv riemannZeta ρ / (ρ * (ρ + 1))) ρ := by
    convert! hz'.fun_div ((hasDerivAt_id ρ).mul
      ((hasDerivAt_id ρ).add (hasDerivAt_const ρ (1 : ℂ))))
      (mul_ne_zero hd.1 hd.2.2) using 1
    simp [hz]
    field_simp
  have hp : HasDerivAt (fun s => riemannZeta s * H s)
      (deriv riemannZeta ρ * H ρ) ρ := by
    simpa only [hz, zero_mul, add_zero] using hz'.fun_mul hH.differentiableAt.hasDerivAt
  have hf := ((hasDerivAt_unitPhaseBoundary hρ).sub hq).add hp
  have he := hf.unique ((hasDerivAt_const ρ (c : ℂ)).congr_of_eventuallyEq hc)
  change (1 - 2 * ρ) / (2 * (ρ * (1 - ρ)) ^ 2) -
      deriv riemannZeta ρ / (ρ * (ρ + 1)) + deriv riemannZeta ρ * H ρ = 0 at he
  linear_combination he

/-- A phase germ at a positive-height zero forces both critical location and simplicity. -/
theorem unitPhaseGerm_necessary {ρ : ℂ} (hρ : ρ ∈ minimumStrip)
    (ht : 0 < ρ.im) (hz : riemannZeta ρ = 0) (hg : UnitPhaseGerm ρ) :
    ρ.re = 1 / 2 ∧ deriv riemannZeta ρ ≠ 0 := by
  obtain ⟨H, hH, hi⟩ := hg
  obtain ⟨c, hc⟩ := unitPhaseGerm_real_constant hρ hH hi
  have hc0 := hc.self_of_nhds
  simp [unitPhaseSource, normalizedMinimumZeta, hz] at hc0
  have him : (unitPhaseBoundary ρ).im = 0 := by rw [hc0]; simp
  refine ⟨(unitPhaseBoundary_im_eq_zero_iff hρ ht).mp him, ?_⟩
  have he := unitPhaseGerm_tangent hρ hz hH hi
  have hd := unitPhaseStrip_denominators hρ
  have hn : (1 : ℂ) - 2 * ρ ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  have hn' : -(1 - 2 * ρ) / (2 * (ρ * (1 - ρ)) ^ 2) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hn) (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (mul_ne_zero hd.1 (sub_ne_zero.mpr hd.2.1.symm))))
  intro h
  rw [h, zero_mul] at he
  exact hn' he.symm

/-- Analytic divided differences construct the multiplier through a simple critical zero. -/
theorem unitPhaseGerm_of_simple_critical_zero {ρ : ℂ} (hρ : ρ ∈ minimumStrip)
    (ht : 0 < ρ.im) (hz : riemannZeta ρ = 0)
    (hline : ρ.re = 1 / 2) (hsimple : deriv riemannZeta ρ ≠ 0) : UnitPhaseGerm ρ := by
  let c : ℝ := (unitPhaseBoundary ρ).re
  have hc : unitPhaseSource ρ = (c : ℂ) := by
    simp only [unitPhaseSource, normalizedMinimumZeta, hz, zero_div, sub_zero]
    apply Complex.ext
    · rfl
    · simpa using (unitPhaseBoundary_im_eq_zero_iff hρ ht).mpr hline
  let F : ℂ → ℂ := fun s => (c : ℂ) - unitPhaseSource s
  have hF : AnalyticAt ℂ F ρ := analyticAt_const.sub (unitPhaseSource_analytic ρ hρ)
  have hF0 : F ρ = 0 := by simp [F, hc]
  have hZ := unitPhaseZeta_analytic ρ hρ
  have hDF := RHTower.analyticAt_dslope_of_analyticAt hF hF
  have hDZ := RHTower.analyticAt_dslope_of_analyticAt hZ hZ
  have hd0 : dslope riemannZeta ρ ρ ≠ 0 := by simpa using hsimple
  let H : ℂ → ℂ := fun s => dslope F ρ s / dslope riemannZeta ρ s
  refine ⟨H, hDF.div hDZ hd0, ?_⟩
  filter_upwards [unitPhaseStrip_open.mem_nhds hρ, hDZ.continuousAt.eventually_ne hd0]
    with s hs hds
  have hzval : riemannZeta s = (s - ρ) * dslope riemannZeta ρ s := by
    simpa [hz, smul_eq_mul] using (sub_smul_dslope riemannZeta ρ s).symm
  have hfval : F s = (s - ρ) * dslope F ρ s := by
    simpa [hF0, smul_eq_mul] using (sub_smul_dslope F ρ s).symm
  have he : unitPhaseSource s + riemannZeta s * H s = (c : ℂ) := by
    have hm : riemannZeta s * H s = F s := by
      rw [hzval, hfval]
      dsimp [H]
      field_simp
    rw [hm]
    dsimp [F]
    ring
  rw [normalizedWeightedRemainder_one_eq_star_source hs, Complex.star_def, Complex.conj_im]
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im] at hi
  linarith

/-- Exact local survivor: phase-factor existence is equivalent to a simple critical zero. -/
theorem unitPhaseGerm_iff_simple_critical_zero {ρ : ℂ} (hρ : ρ ∈ minimumStrip)
    (ht : 0 < ρ.im) (hz : riemannZeta ρ = 0) :
    UnitPhaseGerm ρ ↔ ρ.re = 1 / 2 ∧ deriv riemannZeta ρ ≠ 0 :=
  ⟨unitPhaseGerm_necessary hρ ht hz, fun h =>
    unitPhaseGerm_of_simple_critical_zero hρ ht hz h.1 h.2⟩

end
end RHTower.DeletionMixedRefinement
