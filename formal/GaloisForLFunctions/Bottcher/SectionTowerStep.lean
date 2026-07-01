/-
# The Böttcher section tower: extension step (helpers)

Helpers for the sqrt-descent: circle membership, the bridge from a `TowerSection`'s raw winding
field to `windInt` of its section loop, and the transported point-winding (any point strictly
below the circle's level has winding `2πi` — sublevel transport to `0`).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionTower

open Complex Set Filter Metric

namespace Bottcher

theorem norm_circleMap_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
  simp [circleMap, Complex.norm_exp, abs_of_pos hr]

theorem circleMap_mem_annulusSet {r rlo rhi : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi)
    (θ : ℝ) : circleMap 0 r θ ∈ annulusSet rlo rhi := by
  constructor
  · rw [norm_circleMap_zero hr]; exact h1
  · rw [norm_circleMap_zero hr]; exact h2

/-- The section loop of a tower section at an interior radius. -/
noncomputable def TowerSection.loop {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) : C1Loop :=
  sectionLoop S.an (circleMap_mem_annulusSet hr h1 h2)

/-- The raw winding field is `windInt` of the section loop about `0`. -/
theorem TowerSection.windInt_loop_zero {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) :
    windInt (S.loop hr h1 h2) 0 = 2 * (Real.pi : ℂ) * Complex.I := by
  have hraw := S.wind r h1 h2
  rw [← hraw]
  apply intervalIntegral.integral_congr
  intro θ _
  show ((S.loop hr h1 h2).γ θ - 0)⁻¹ * (S.loop hr h1 h2).γ' θ = _
  rw [sub_zero]
  rfl

/-- The loop of a tower section runs at constant level `log r`. -/
theorem TowerSection.loop_level {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) (θ : ℝ) :
    greenFunctionDyn c ((S.loop hr h1 h2).γ θ) = Real.log r := by
  show greenFunctionDyn c (S.T (circleMap 0 r θ)) = Real.log r
  rw [S.level _ (circleMap_mem_annulusSet hr h1 h2 θ), norm_circleMap_zero hr]

/-- **Transported point winding.**  Any point strictly below the circle's level has winding `2πi`
about the section loop (sublevel transport to `0` + the tower's winding invariant). -/
theorem TowerSection.windInt_loop_point {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi)
    (h0 : greenFunctionDyn c 0 < Real.log r)
    {p : ℂ} (hp : greenFunctionDyn c p < Real.log r) :
    windInt (S.loop hr h1 h2) p = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [windInt_eq_windInt_zero_of_level (S.loop hr h1 h2) h0 (S.loop_level hr h1 h2) hp]
  exact S.windInt_loop_zero hr h1 h2

/-- The critical value's level: `G_c(c) = 2·G_c(0)`. -/
theorem greenFunctionDyn_critical_value (c : ℂ) :
    greenFunctionDyn c c = 2 * greenFunctionDyn c 0 := by
  have := greenFunctionDyn_quadratic c 0
  rw [show quadratic c 0 = c from by unfold quadratic; ring] at this
  exact this

/-- `logDeriv` respects eventual equality. -/
theorem logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[nhds w] g) :
    logDeriv f w = logDeriv g w := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.self_of_nhds]

end Bottcher

namespace Bottcher
open Complex Set Filter Metric


/-- `circleMap` at `θ + π` is the antipode. -/
theorem circleMap_zero_add_pi (ρ θ : ℝ) :
    circleMap 0 ρ (θ + Real.pi) = -circleMap 0 ρ θ := by
  simp only [circleMap, zero_add]
  rw [show ((θ + Real.pi : ℝ) : ℂ) * Complex.I = θ * Complex.I + Real.pi * Complex.I from by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **Winding parity of an even section.**  An even, analytic, nonvanishing function on a
symmetric annulus has circle windings in `2·2πi·ℤ`; in particular the winding is never `2πi`. -/
theorem even_section_winding_ne {a b : ℝ} {s : ℂ → ℂ} (ha : 0 < a)
    (hs_an : AnalyticOnNhd ℂ s (annulusSet a b)) (hs_ne : ∀ w ∈ annulusSet a b, s w ≠ 0)
    (heven : ∀ w ∈ annulusSet a b, s (-w) = s w)
    {ρ : ℝ} (hρ1 : a < ρ) (hρ2 : ρ < b) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (s (circleMap 0 ρ θ))⁻¹
      * (deriv s (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)))
    ≠ 2 * (Real.pi : ℂ) * Complex.I := by
  intro hfull
  have hρpos : (0:ℝ) < ρ := lt_trans ha hρ1
  have hcm : ∀ θ : ℝ, circleMap 0 ρ θ ∈ annulusSet a b :=
    circleMap_mem_annulusSet hρpos hρ1 hρ2
  have hnegmem : ∀ w ∈ annulusSet a b, -w ∈ annulusSet a b := by
    rintro w ⟨h1, h2⟩
    exact ⟨by rwa [norm_neg], by rwa [norm_neg]⟩
  -- the derivative of an even function is odd
  have hderiv_odd : ∀ w ∈ annulusSet a b, deriv s (-w) = -deriv s w := by
    intro w hw
    have hev : (fun z => s (-z)) =ᶠ[nhds w] s := by
      filter_upwards [(isOpen_annulusSet a b).mem_nhds hw] with z hz
      exact heven z hz
    have h1 : deriv (fun z => s (-z)) w = deriv s w := hev.deriv_eq
    have h2 : HasDerivAt (fun z => s (-z)) (-deriv s (-w)) w := by
      have h3 : HasDerivAt s (deriv s (-w)) (-w) :=
        (hs_an _ (hnegmem w hw)).differentiableAt.hasDerivAt
      have h4 : HasDerivAt (fun z : ℂ => -z) (-1) w := by
        simpa using (hasDerivAt_id w).neg
      have h6 : HasDerivAt (s ∘ fun z : ℂ => -z) (deriv s (-w) * (-1)) w :=
        HasDerivAt.comp w h3 h4
      have h7 : HasDerivAt (fun z => s (-z)) (deriv s (-w) * (-1)) w := h6
      simpa [mul_comm] using h7
    have h5 : deriv (fun z => s (-z)) w = -deriv s (-w) := h2.deriv
    rw [h5] at h1
    linear_combination -h1
  -- the integrand is π-periodic
  set F : ℝ → ℂ := fun θ => (s (circleMap 0 ρ θ))⁻¹
    * (deriv s (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) with hFdef
  have hFper : ∀ θ : ℝ, F (θ + Real.pi) = F θ := by
    intro θ
    show (s (circleMap 0 ρ (θ + Real.pi)))⁻¹
        * (deriv s (circleMap 0 ρ (θ + Real.pi)) * (circleMap 0 ρ (θ + Real.pi) * Complex.I))
      = (s (circleMap 0 ρ θ))⁻¹
        * (deriv s (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
    rw [circleMap_zero_add_pi, heven _ (hcm θ), hderiv_odd _ (hcm θ)]
    ring
  have hFcont : Continuous F := by
    have h1 : Continuous (fun θ => s (circleMap 0 ρ θ)) :=
      hs_an.continuousOn.comp_continuous (continuous_circleMap 0 ρ) hcm
    have h2 : Continuous (fun θ => deriv s (circleMap 0 ρ θ)) :=
      (hs_an.deriv).continuousOn.comp_continuous (continuous_circleMap 0 ρ) hcm
    have h3 : ∀ θ, s (circleMap 0 ρ θ) ≠ 0 := fun θ => hs_ne _ (hcm θ)
    exact (h1.inv₀ h3).mul (h2.mul ((continuous_circleMap 0 ρ).mul continuous_const))
  -- the full winding splits into two π-halves
  have hsplit : (∫ θ in (0:ℝ)..(2 * Real.pi), F θ)
      = (∫ θ in (0:ℝ)..Real.pi, F θ) + ∫ θ in Real.pi..(2 * Real.pi), F θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hFcont.intervalIntegrable _ _) (hFcont.intervalIntegrable _ _)).symm
  have hshift : (∫ θ in Real.pi..(2 * Real.pi), F θ) = ∫ θ in (0:ℝ)..Real.pi, F θ := by
    have h1 : (∫ u in (0:ℝ)..Real.pi, F (u + Real.pi))
        = ∫ u in ((0:ℝ) + Real.pi)..(Real.pi + Real.pi), F u :=
      intervalIntegral.integral_comp_add_right F Real.pi
    have h2 : (∫ u in (0:ℝ)..Real.pi, F (u + Real.pi)) = ∫ u in (0:ℝ)..Real.pi, F u :=
      intervalIntegral.integral_congr (fun u _ => hFper u)
    have h3 : (∫ u in ((0:ℝ) + Real.pi)..(Real.pi + Real.pi), F u)
        = ∫ u in Real.pi..(2 * Real.pi), F u := by
      congr 1 <;> ring
    rw [← h3, ← h1, h2]
  -- the half-loop
  have hhalfdiff : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v / 2) (1 / 2 : ℝ) u := by
    intro u
    simpa using (hasDerivAt_id u).div_const 2
  set L2 : C1Loop :=
    { γ := fun u => s (circleMap 0 ρ (u / 2))
      γ' := fun u => deriv s (circleMap 0 ρ (u / 2))
        * (((1 / 2 : ℝ) : ℂ) * (circleMap 0 ρ (u / 2) * Complex.I))
      cont := hs_an.continuousOn.comp_continuous
        ((continuous_circleMap 0 ρ).comp (continuous_id.div_const 2)) (fun u => hcm _)
      cont' := by
        have h2 : Continuous (fun u : ℝ => deriv s (circleMap 0 ρ (u / 2))) :=
          (hs_an.deriv).continuousOn.comp_continuous
            ((continuous_circleMap 0 ρ).comp (continuous_id.div_const 2)) (fun u => hcm _)
        exact h2.mul (continuous_const.mul (((continuous_circleMap 0 ρ).comp
          (continuous_id.div_const 2)).mul continuous_const))
      deriv := by
        intro u _
        have h1 : HasDerivAt (fun v : ℝ => circleMap 0 ρ (v / 2))
            (((1 / 2 : ℝ) : ℂ) * (circleMap 0 ρ (u / 2) * Complex.I)) u := by
          have h2 := hasDerivAt_circleMap 0 ρ (u / 2)
          have h3 := h2.scomp u (hhalfdiff u)
          simpa [Complex.real_smul] using h3
        have h4 : HasDerivAt s (deriv s (circleMap 0 ρ (u / 2))) (circleMap 0 ρ (u / 2)) :=
          (hs_an _ (hcm _)).differentiableAt.hasDerivAt
        exact h4.comp u h1
      closed := by
        show s (circleMap 0 ρ (2 * Real.pi / 2)) = s (circleMap 0 ρ (0 / 2))
        rw [show (2 * Real.pi / 2 : ℝ) = 0 + Real.pi from by ring,
          circleMap_zero_add_pi]
        rw [show (0 / 2 : ℝ) = 0 from by ring]
        exact heven _ (hcm 0) } with hL2def
  have hL2A : L2.Avoids 0 := by
    intro θ h
    exact hs_ne _ (hcm _) h
  obtain ⟨n, hn⟩ := exists_int_windInt L2 hL2A
  -- the half-loop winding is the half-integral
  have hL2val : windInt L2 0 = ∫ θ in (0:ℝ)..Real.pi, F θ := by
    have h1 : windInt L2 0 = ∫ u in (0:ℝ)..(2 * Real.pi), F (u / 2) * ((1 / 2 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _
      show (L2.γ u - 0)⁻¹ * L2.γ' u = F (u / 2) * ((1 / 2 : ℝ) : ℂ)
      rw [sub_zero]
      show (s (circleMap 0 ρ (u / 2)))⁻¹
          * (deriv s (circleMap 0 ρ (u / 2))
            * (((1 / 2 : ℝ) : ℂ) * (circleMap 0 ρ (u / 2) * Complex.I)))
        = (s (circleMap 0 ρ (u / 2)))⁻¹
          * (deriv s (circleMap 0 ρ (u / 2)) * (circleMap 0 ρ (u / 2) * Complex.I))
          * ((1 / 2 : ℝ) : ℂ)
      ring
    have h2 : (∫ u in (0:ℝ)..(2 * Real.pi), F (u / 2) * ((1 / 2 : ℝ) : ℂ))
        = ((1 / 2 : ℝ) : ℂ) * ∫ u in (0:ℝ)..(2 * Real.pi), F (u / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      ring
    have h3 : (∫ u in (0:ℝ)..(2 * Real.pi), F (u / 2))
        = (2⁻¹ : ℝ)⁻¹ • ∫ u in ((2⁻¹ : ℝ) * 0)..((2⁻¹ : ℝ) * (2 * Real.pi)), F u := by
      have h4 := intervalIntegral.integral_comp_mul_left
        (a := (0:ℝ)) (b := 2 * Real.pi) F (by norm_num : (2⁻¹ : ℝ) ≠ 0)
      simp only [div_eq_inv_mul]
      exact h4
    rw [h1, h2, h3]
    rw [show ((2⁻¹ : ℝ) * 0 : ℝ) = 0 from by ring,
      show ((2⁻¹ : ℝ) * (2 * Real.pi) : ℝ) = Real.pi from by ring]
    rw [Complex.real_smul]
    push_cast
    ring
  -- assemble the parity contradiction
  have hfull2 : (2:ℂ) * windInt L2 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hL2val]
    have : (∫ θ in (0:ℝ)..(2 * Real.pi), F θ) = 2 * ∫ θ in (0:ℝ)..Real.pi, F θ := by
      rw [hsplit, hshift]
      ring
    rw [← this]
    exact hfull
  rw [hn] at hfull2
  have hπI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcast : ((2 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    have h1 : (2:ℂ) * ((n:ℂ) * (2 * Real.pi * Complex.I)) = 1 * (2 * Real.pi * Complex.I) := by
      rw [hfull2]; ring
    have h2 : ((2:ℂ) * (n:ℂ)) * (2 * Real.pi * Complex.I)
        = 1 * (2 * Real.pi * Complex.I) := by
      rw [← h1]; ring
    have h3 := mul_right_cancel₀ hπI h2
    push_cast
    linear_combination h3
  have : (2 * n : ℤ) = 1 := by exact_mod_cast hcast
  omega
