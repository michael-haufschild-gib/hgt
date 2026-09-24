import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePShiftedAnalyticRigidity
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourcePoleResidue
import GaloisForLFunctions.RHTower.PositiveMGFBoundaryResidue

/-!
# Fixed-amplitude oscillation of the literal Route-P source

A critical-line zeta zero gives a nonzero imaginary boundary residue of the
source Laplace transform. If the source had an eventual one-sided constant
bound, its shifted positive tail would carry that residue while its real
boundary Abel mass were only the shift constant. Positivity forces the
residue norm below that mass. Choosing a smaller constant contradicts the
bound in either sign.

This is a source-side oscillation theorem, not a payment of Route-P's
coupled arithmetic debts or an ordered-history Xi intertwiner.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private theorem routePShiftedMGF_eq_source_of_re_pos
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0)
    {z : ℂ} (hz : 0 < z.re) :
    complexMGF id (routePShiftedMeasure epsilon B 1 T) ((1 : ℂ) - z) =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z -
        routePSourceSignedHeadLaplace epsilon T z +
        (B : ℂ) * Complex.exp (-z * (T : ℂ)) / z := by
  have h := routePSourceLaplaceUnderShift_eq_continuation_of_re_pos
    hT hpos hepsilon hz
  unfold routePSourceLaplaceUnderShift at h
  have heps : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  have hmul := (div_eq_iff heps).mp h
  linear_combination hmul

private theorem routePShiftedMGF_real_boundary_mass
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0) :
    Tendsto (fun σ : ℝ =>
      σ * mgf id (routePShiftedMeasure epsilon B 1 T) (1 - σ))
      (𝓝[>] (0 : ℝ)) (𝓝 B) := by
  let μ := routePShiftedMeasure epsilon B 1 T
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hF0 : ContinuousAt routePSourceLaplaceContinuation 0 :=
    (analyticAt_routePSourceLaplaceContinuation_of_low_height
      (by norm_num) (by norm_num)).continuousAt
  have hF : Tendsto (fun σ : ℝ =>
      routePSourceLaplaceContinuation (σ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (routePSourceLaplaceContinuation 0)) :=
    hF0.tendsto.comp hσ
  have hHead0 : ContinuousAt (routePSourceSignedHeadLaplace epsilon T) 0 :=
    (differentiable_routePSourceSignedHeadLaplace epsilon T 0).continuousAt
  have hHead : Tendsto (fun σ : ℝ =>
      routePSourceSignedHeadLaplace epsilon T (σ : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePSourceSignedHeadLaplace epsilon T 0)) :=
    hHead0.tendsto.comp hσ
  have hExp : Tendsto (fun σ : ℝ =>
      Complex.exp (-(σ : ℂ) * (T : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt
        (fun z : ℂ => Complex.exp (-z * (T : ℂ))) 0 := by fun_prop
    simpa [Function.comp_def] using hcont.tendsto.comp hσ
  have hFterm : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * routePSourceLaplaceContinuation (σ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hσ.mul hF
  have hHeadterm : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * routePSourceSignedHeadLaplace epsilon T (σ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hσ.mul hHead
  have hCombo : Tendsto (fun σ : ℝ =>
      (epsilon : ℂ) * ((σ : ℂ) * routePSourceLaplaceContinuation (σ : ℂ)) -
        (σ : ℂ) * routePSourceSignedHeadLaplace epsilon T (σ : ℂ) +
        (B : ℂ) * Complex.exp (-(σ : ℂ) * (T : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (B : ℂ)) := by
    simpa using ((hFterm.const_mul (epsilon : ℂ)).sub hHeadterm).add
      (hExp.const_mul (B : ℂ))
  have hMGF : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * complexMGF id μ ((1 : ℂ) - (σ : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (B : ℂ)) := by
    apply hCombo.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    have hz : 0 < (σ : ℂ).re := by simpa using hσpos
    have hEq := routePShiftedMGF_eq_source_of_re_pos
      (epsilon := epsilon) (B := B) (T := T) hT hpos hepsilon hz
    have hσne : (σ : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
    dsimp only [μ]
    rw [hEq]
    field_simp [hσne]
  have hCast : Tendsto (fun σ : ℝ =>
      ((σ * mgf id μ (1 - σ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (B : ℂ)) := by
    convert hMGF using 1
    funext σ
    have hcoord : (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcoord, complexMGF_ofReal]
    push_cast
    rfl
  have hRe := (Complex.continuous_re.tendsto (B : ℂ)).comp hCast
  simpa only [Function.comp_def, Complex.ofReal_re, μ] using hRe

private theorem routePShiftedMGF_imag_boundary_residue
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0)
    (z0 c : ℂ) (hz0re : z0.re = 0) (hz0ne : z0 ≠ 0)
    (hres : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 c)) :
    Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id (routePShiftedMeasure epsilon B 1 T)
        ((1 : ℂ) - ((σ : ℂ) + z0)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((epsilon : ℂ) * c)) := by
  let μ := routePShiftedMeasure epsilon B 1 T
  have hσ : Tendsto (fun σ : ℝ => (σ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hpathNhds : Tendsto (fun σ : ℝ => (σ : ℂ) + z0)
      (𝓝[>] (0 : ℝ)) (𝓝 z0) := by
    simpa using hσ.add_const z0
  have hpathMem : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ),
      (σ : ℂ) + z0 ∈ ({z0}ᶜ : Set ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσpos
    change (σ : ℂ) + z0 ≠ z0
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, hz0re] at hre
    have hσgt : 0 < σ := hσpos
    linarith
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + z0)
      (𝓝[>] (0 : ℝ)) (𝓝[≠] z0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpathNhds, hpathMem⟩
  have hFterm : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * routePSourceLaplaceContinuation ((σ : ℂ) + z0))
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [Function.comp_def, add_sub_cancel_right] using hres.comp hpath
  have hHeadAt : ContinuousAt (routePSourceSignedHeadLaplace epsilon T) z0 :=
    (differentiable_routePSourceSignedHeadLaplace epsilon T z0).continuousAt
  have hHead : Tendsto (fun σ : ℝ =>
      routePSourceSignedHeadLaplace epsilon T ((σ : ℂ) + z0))
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePSourceSignedHeadLaplace epsilon T z0)) :=
    hHeadAt.tendsto.comp hpathNhds
  have hHeadterm : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * routePSourceSignedHeadLaplace epsilon T ((σ : ℂ) + z0))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hσ.mul hHead
  have hCorrAt : ContinuousAt
      (fun z : ℂ => Complex.exp (-z * (T : ℂ)) / z) z0 := by
    have hnum : ContinuousAt
        (fun z : ℂ => Complex.exp (-z * (T : ℂ))) z0 := by fun_prop
    exact hnum.div continuousAt_id hz0ne
  have hCorr : Tendsto (fun σ : ℝ =>
      Complex.exp (-((σ : ℂ) + z0) * (T : ℂ)) / ((σ : ℂ) + z0))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp (-z0 * (T : ℂ)) / z0)) :=
    hCorrAt.tendsto.comp hpathNhds
  have hCorrterm : Tendsto (fun σ : ℝ => (σ : ℂ) *
      (Complex.exp (-((σ : ℂ) + z0) * (T : ℂ)) / ((σ : ℂ) + z0)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hσ.mul hCorr
  have hCombo : Tendsto (fun σ : ℝ =>
      (epsilon : ℂ) *
          ((σ : ℂ) * routePSourceLaplaceContinuation ((σ : ℂ) + z0)) -
        (σ : ℂ) * routePSourceSignedHeadLaplace epsilon T ((σ : ℂ) + z0) +
        (B : ℂ) * ((σ : ℂ) *
          (Complex.exp (-((σ : ℂ) + z0) * (T : ℂ)) / ((σ : ℂ) + z0))))
      (𝓝[>] (0 : ℝ)) (𝓝 ((epsilon : ℂ) * c)) := by
    simpa using ((hFterm.const_mul (epsilon : ℂ)).sub hHeadterm).add
      (hCorrterm.const_mul (B : ℂ))
  apply hCombo.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσpos
  have hz : 0 < ((σ : ℂ) + z0).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hz0re, add_zero]
    exact hσpos
  have hEq := routePShiftedMGF_eq_source_of_re_pos
    (epsilon := epsilon) (B := B) (T := T) hT hpos hepsilon hz
  rw [hEq]
  ring

private theorem routePSource_oneSided_bound_residue
    (z0 c : ℂ) (hz0re : z0.re = 0) (hz0ne : z0 ≠ 0)
    (hres : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 c))
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0) :
    ‖(epsilon : ℂ) * c‖ ≤ B := by
  let μ := routePShiftedMeasure epsilon B 1 T
  have hreal : Tendsto (fun σ : ℝ => σ * mgf id μ (1 - σ))
      (𝓝[>] (0 : ℝ)) (𝓝 B) :=
    routePShiftedMGF_real_boundary_mass hT hpos hepsilon
  have himag : Tendsto (fun σ : ℝ =>
      (σ : ℂ) * complexMGF id μ ((1 : ℂ) - ((σ : ℂ) + z0)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((epsilon : ℂ) * c)) :=
    routePShiftedMGF_imag_boundary_residue
      hT hpos hepsilon z0 c hz0re hz0ne hres
  exact positiveMGF_boundary_residue_norm_le μ z0 hz0re B
    ((epsilon : ℂ) * c) hreal himag

theorem exists_routePSource_fixed_amplitude_two_sided :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ,
      (∃ t : ℝ, T < t ∧ δ < routePSourceRay t) ∧
      (∃ t : ℝ, T < t ∧ routePSourceRay t < -δ) := by
  obtain ⟨T0, hT0, hzeros⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hzeta⟩ := hzeros T0 le_rfl
  have hτ0 : 0 < τ := lt_of_lt_of_le hT0 hτ.1
  let rho : ℂ := linePt τ
  have hre : rho.re = 1 / 2 := by
    dsimp only [rho]
    exact linePt_re τ
  have him : 0 < rho.im := by simpa only [rho, linePt_im] using hτ0
  obtain ⟨m, hm, hres⟩ :=
    routePSourceLaplaceContinuation_residue_of_zero hzeta him
  let z0 : ℂ := rho - 1 / 2
  let c : ℂ := -(m : ℂ) / (rho * (rho + 1 / 2))
  have hz0re : z0.re = 0 := by
    dsimp [z0]
    norm_num [Complex.sub_re]
    linarith
  have hz0ne : z0 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [z0] at this
    linarith
  have hrho : rho ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrhohalf : rho + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hc : c ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
      (mul_ne_zero hrho hrhohalf)
  have hres' : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 c) := by
    simpa only [z0, c] using hres
  let δ : ℝ := ‖c‖ / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (norm_pos_iff.mpr hc) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro T
  let U : ℝ := max T 0
  have hU : 0 ≤ U := le_max_right T 0
  have hTU : T ≤ U := le_max_left T 0
  constructor
  · by_contra h
    have hpos : ∀ t, U < t →
        0 ≤ (-1 : ℝ) * routePSourceRay t + δ := by
      intro t ht
      have hle : routePSourceRay t ≤ δ :=
        le_of_not_gt (fun hgt => h ⟨t, lt_of_le_of_lt hTU ht, hgt⟩)
      nlinarith
    have hbound := routePSource_oneSided_bound_residue z0 c
      hz0re hz0ne hres' hU hpos (by norm_num : (-1 : ℝ) ≠ 0)
    have hnorm : ‖c‖ ≤ δ := by simpa using hbound
    dsimp [δ] at hnorm
    linarith [norm_pos_iff.mpr hc]
  · by_contra h
    have hpos : ∀ t, U < t →
        0 ≤ (1 : ℝ) * routePSourceRay t + δ := by
      intro t ht
      have hge : -δ ≤ routePSourceRay t :=
        le_of_not_gt (fun hlt => h ⟨t, lt_of_le_of_lt hTU ht, hlt⟩)
      nlinarith
    have hbound := routePSource_oneSided_bound_residue z0 c
      hz0re hz0ne hres' hU hpos (by norm_num : (1 : ℝ) ≠ 0)
    have hnorm : ‖c‖ ≤ δ := by simpa using hbound
    dsimp [δ] at hnorm
    linarith [norm_pos_iff.mpr hc]

end
end RHTower
