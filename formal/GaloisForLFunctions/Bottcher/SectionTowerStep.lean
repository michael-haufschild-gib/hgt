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

/-- **Sign constancy.**  A continuous pointwise square root `u` of `v²` (i.e. `u = ±v` pointwise,
`v` nonvanishing) on an open connected set is globally `v` or globally `-v`. -/
theorem sign_constant_on_connected {A : Set ℂ} (hAo : IsOpen A) (hconn : IsConnected A)
    {u v : ℂ → ℂ} (hu : ∀ w ∈ A, ContinuousAt u w) (hv : ∀ w ∈ A, ContinuousAt v w)
    (hvne : ∀ w ∈ A, v w ≠ 0) (hsq : ∀ w ∈ A, u w = v w ∨ u w = -v w) :
    (∀ w ∈ A, u w = v w) ∨ (∀ w ∈ A, u w = -v w) := by
  classical
  have hEopen : IsOpen {z : ℂ | z ∈ A ∧ u z ≠ -v z} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzA, hzne⟩
    have hc : ContinuousAt (fun x => u x + v x) z := (hu z hzA).add (hv z hzA)
    have hne0 : u z + v z ≠ 0 := fun h => hzne (by linear_combination h)
    filter_upwards [hAo.mem_nhds hzA, hc.eventually_ne hne0] with x hx1 hx2
    exact ⟨hx1, fun h => hx2 (by rw [h]; ring)⟩
  have hFopen : IsOpen {z : ℂ | z ∈ A ∧ u z ≠ v z} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzA, hzne⟩
    have hc : ContinuousAt (fun x => u x - v x) z := (hu z hzA).sub (hv z hzA)
    have hne0 : u z - v z ≠ 0 := sub_ne_zero.mpr hzne
    filter_upwards [hAo.mem_nhds hzA, hc.eventually_ne hne0] with x hx1 hx2
    exact ⟨hx1, fun h => hx2 (sub_eq_zero.mp (by rw [← h]; ring))⟩
  by_cases hpos : ∀ w ∈ A, u w = v w
  · exact Or.inl hpos
  push Not at hpos
  obtain ⟨w₁, hw₁A, hw₁⟩ := hpos
  right
  intro w hw
  by_contra hne
  have hweq : u w = v w := (hsq w hw).resolve_right hne
  have hcover : A ⊆ {z : ℂ | z ∈ A ∧ u z ≠ -v z} ∪ {z : ℂ | z ∈ A ∧ u z ≠ v z} := by
    intro z hz
    by_cases h : u z = v z
    · refine Or.inl ⟨hz, fun hcontra => hvne z hz ?_⟩
      have h2 : v z = -v z := h.symm.trans hcontra
      linear_combination ((1:ℂ)/2) * h2
    · exact Or.inr ⟨hz, h⟩
  have hneE : (A ∩ {z : ℂ | z ∈ A ∧ u z ≠ -v z}).Nonempty := by
    refine ⟨w, hw, hw, fun hcontra => hvne w hw ?_⟩
    have h2 : v w = -v w := hweq.symm.trans hcontra
    linear_combination ((1:ℂ)/2) * h2
  have hneF : (A ∩ {z : ℂ | z ∈ A ∧ u z ≠ v z}).Nonempty := ⟨w₁, hw₁A, hw₁A, hw₁⟩
  obtain ⟨z, _, ⟨_, hz1⟩, ⟨_, hz2⟩⟩ := hconn.isPreconnected _ _ hEopen hFopen
    hcover hneE hneF
  rcases hsq z (by assumption) with h | h
  · exact hz2 h
  · exact hz1 h

set_option maxHeartbeats 1600000 in
/-- **The extension step.**  A tower section on `{rlo < ‖w‖ < R₀}` whose source band
`(σ₁, σ₂)` lies strictly above the critical value's level extends across the square root of the
band: there is a tower section on `{√σ₁ < ‖w‖ < R₀}`. -/
theorem tower_extension_step {c : ℂ} {rlo R₀ : ℝ}
    (hrlo : 1 < rlo) (hrloR₀ : rlo ^ 2 < R₀)
    (S : TowerSection c rlo R₀)
    (h0 : greenFunctionDyn c 0 < Real.log rlo)
    {σ₁ σ₂ : ℝ} (hσ₁lo : rlo < σ₁) (hσ₁hi : σ₁ < rlo ^ 2)
    (hσ₂lo : rlo ^ 2 < σ₂) (hσ₂hi : σ₂ ≤ R₀)
    (hcab : greenFunctionDyn c c < Real.log σ₁)
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) :
    ∃ S' : TowerSection c (Real.sqrt σ₁) R₀,
      (∀ w ∈ annulusSet rlo R₀, S'.T w = S.T w) ∧
      (∀ z : ℂ, Real.log (Real.sqrt σ₁) < greenFunctionDyn c z →
        greenFunctionDyn c z < Real.log R₀ →
        z ∈ S'.T '' annulusSet (Real.sqrt σ₁) R₀) := by
  classical
  have hσ₁pos : (0:ℝ) < σ₁ := by nlinarith
  have hσ₂pos : (0:ℝ) < σ₂ := by nlinarith
  have hσ : σ₁ < σ₂ := by nlinarith
  have hs₁ : Real.sqrt σ₁ < rlo := by
    rw [Real.sqrt_lt' (by linarith)]
    exact hσ₁hi
  have hs₂ : rlo < Real.sqrt σ₂ := by
    rw [show rlo = Real.sqrt (rlo ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hσ₂lo
  have hs₁pos : (0:ℝ) < Real.sqrt σ₁ := Real.sqrt_pos.mpr hσ₁pos
  have hs₁s₂ : Real.sqrt σ₁ < Real.sqrt σ₂ := Real.sqrt_lt_sqrt (le_of_lt hσ₁pos) hσ
  have hs₂R₀ : Real.sqrt σ₂ < R₀ := by
    have h1 : Real.sqrt σ₂ ≤ Real.sqrt R₀ := Real.sqrt_le_sqrt hσ₂hi
    have h2 : Real.sqrt R₀ < R₀ := by
      have hR₀1 : (1:ℝ) < R₀ := by nlinarith
      nth_rewrite 2 [show R₀ = Real.sqrt (R₀ ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
    linarith
  -- the squared-argument membership
  have hsqmem : ∀ w : ℂ, w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) →
      w ^ 2 ∈ annulusSet σ₁ σ₂ := by
    rintro w ⟨h1, h2⟩
    constructor
    · rw [norm_pow]
      calc σ₁ = Real.sqrt σ₁ ^ 2 := (Real.sq_sqrt (le_of_lt hσ₁pos)).symm
        _ < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    · rw [norm_pow]
      calc ‖w‖ ^ 2 < Real.sqrt σ₂ ^ 2 := by nlinarith [norm_nonneg w, hs₁pos.trans h1]
        _ = σ₂ := Real.sq_sqrt (le_of_lt hσ₂pos)
  have hsrcmem : ∀ v : ℂ, v ∈ annulusSet σ₁ σ₂ → v ∈ annulusSet rlo R₀ := by
    rintro v ⟨h1, h2⟩
    exact ⟨lt_trans hσ₁lo h1, lt_of_lt_of_le h2 hσ₂hi⟩
  -- the pulled-back radicand g := T(w²) − c on the target band
  set g : ℂ → ℂ := fun w => S.T (w ^ 2) - c with hgdef
  have hg_an : AnalyticOnNhd ℂ g (annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)) := by
    intro w hw
    have h1 : AnalyticAt ℂ (fun w : ℂ => w ^ 2) w := analyticAt_id.pow 2
    have h2 : AnalyticAt ℂ S.T (w ^ 2) := S.an _ (hsrcmem _ (hsqmem w hw))
    have h3 : AnalyticAt ℂ (S.T ∘ fun w : ℂ => w ^ 2) w :=
      AnalyticAt.comp (g := S.T) (f := fun w : ℂ => w ^ 2) h2 h1
    exact h3.sub analyticAt_const
  have hg_ne : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂), g w ≠ 0 := by
    intro w hw h
    have hval : S.T (w ^ 2) = c := by
      have := sub_eq_zero.mp h
      exact this
    have hlev := S.level _ (hsrcmem _ (hsqmem w hw))
    rw [hval] at hlev
    have h1 : Real.log σ₁ < Real.log ‖w ^ 2‖ := by
      apply Real.log_lt_log hσ₁pos
      exact (hsqmem w hw).1
    rw [← hlev] at h1
    linarith
  -- level of g-arguments: the band sits strictly above the critical level h
  have hbandh : greenFunctionDyn c 0 < Real.log (Real.sqrt σ₁) := by
    have h2h := greenFunctionDyn_critical_value c
    have hG0 : 0 ≤ greenFunctionDyn c 0 := greenFunctionDyn_nonneg c 0
    have hlogs : Real.log (Real.sqrt σ₁) = Real.log σ₁ / 2 := by
      rw [Real.log_sqrt (le_of_lt hσ₁pos)]
    rw [hlogs]
    rw [h2h] at hcab
    linarith
  -- the core radius and its square
  set ρ : ℝ := (Real.sqrt σ₁ + Real.sqrt σ₂) / 2 with hρdef
  have hρ1 : Real.sqrt σ₁ < ρ := by rw [hρdef]; linarith
  have hρ2 : ρ < Real.sqrt σ₂ := by rw [hρdef]; linarith
  have hρpos : (0:ℝ) < ρ := lt_trans hs₁pos hρ1
  have hρsq₁ : σ₁ < ρ ^ 2 := by
    have h1 : Real.sqrt σ₁ ^ 2 < ρ ^ 2 := by nlinarith [hs₁pos]
    rwa [Real.sq_sqrt (le_of_lt hσ₁pos)] at h1
  have hρsq₂ : ρ ^ 2 < σ₂ := by
    have h1 : ρ ^ 2 < Real.sqrt σ₂ ^ 2 := by nlinarith [hρpos]
    rwa [Real.sq_sqrt (le_of_lt hσ₂pos)] at h1
  have hρsqrlo : rlo < ρ ^ 2 := lt_trans hσ₁lo hρsq₁
  have hρsqR₀ : ρ ^ 2 < R₀ := lt_of_lt_of_le hρsq₂ hσ₂hi
  have hρsqpos : (0:ℝ) < ρ ^ 2 := by positivity
  -- T never takes the value c on the source band
  have hTnec : ∀ v ∈ annulusSet σ₁ σ₂, S.T v ≠ c := by
    intro v hv h
    have hlev := S.level _ (hsrcmem _ hv)
    rw [h] at hlev
    have h1 : Real.log σ₁ < Real.log ‖v‖ := Real.log_lt_log hσ₁pos hv.1
    rw [← hlev] at h1
    linarith
  -- the parametric g-winding: at every band radius, the doubled source winding
  have hgwindAll : ∀ r : ℝ, Real.sqrt σ₁ < r → r < Real.sqrt σ₂ →
      (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv g (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I))
      = ((2 ^ 1 * 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    intro r hr1 hr2
    have hrpos : (0:ℝ) < r := lt_trans hs₁pos hr1
    have hrsq₁ : σ₁ < r ^ 2 := by
      have h1 : Real.sqrt σ₁ ^ 2 < r ^ 2 := by nlinarith [hs₁pos]
      rwa [Real.sq_sqrt (le_of_lt hσ₁pos)] at h1
    have hrsq₂ : r ^ 2 < σ₂ := by
      have h1 : r ^ 2 < Real.sqrt σ₂ ^ 2 := by nlinarith [hrpos]
      rwa [Real.sq_sqrt (le_of_lt hσ₂pos)] at h1
    have hrsqrlo : rlo < r ^ 2 := lt_trans hσ₁lo hrsq₁
    have hrsqR₀ : r ^ 2 < R₀ := lt_of_lt_of_le hrsq₂ hσ₂hi
    have hrsqpos : (0:ℝ) < r ^ 2 := by positivity
    set δ : ℝ → ℂ := fun u => S.T (circleMap 0 (r ^ 2) u) - c with hδdef
    set δ' : ℝ → ℂ := fun u =>
      deriv S.T (circleMap 0 (r ^ 2) u) * (circleMap 0 (r ^ 2) u * Complex.I) with hδ'def
    have hcmsq : ∀ u : ℝ, circleMap 0 (r ^ 2) u ∈ annulusSet σ₁ σ₂ := by
      intro u
      exact circleMap_mem_annulusSet hrsqpos hrsq₁ hrsq₂ u
    have hδcont : Continuous δ := by
      have h1 : ContinuousOn S.T (annulusSet rlo R₀) := S.an.continuousOn
      exact (h1.comp_continuous (continuous_circleMap 0 (r ^ 2))
        (fun u => hsrcmem _ (hcmsq u))).sub continuous_const
    have hδ'cont : Continuous δ' := by
      have h1 : ContinuousOn (deriv S.T) (annulusSet rlo R₀) := (S.an.deriv).continuousOn
      exact (h1.comp_continuous (continuous_circleMap 0 (r ^ 2))
        (fun u => hsrcmem _ (hcmsq u))).mul
        ((continuous_circleMap 0 (r ^ 2)).mul continuous_const)
    have hδne : ∀ u : ℝ, δ u ≠ 0 := by
      intro u h
      exact hTnec _ (hcmsq u)
        (sub_eq_zero.mp (show S.T (circleMap 0 (r ^ 2) u) - c = 0 from h))
    have hδper : Function.Periodic δ (2 * Real.pi) := by
      intro u
      show S.T (circleMap 0 (r ^ 2) (u + 2 * Real.pi)) - c
        = S.T (circleMap 0 (r ^ 2) u) - c
      rw [periodic_circleMap 0 (r ^ 2) u]
    have hδ'per : Function.Periodic δ' (2 * Real.pi) := by
      intro u
      show deriv S.T (circleMap 0 (r ^ 2) (u + 2 * Real.pi))
          * (circleMap 0 (r ^ 2) (u + 2 * Real.pi) * Complex.I)
        = deriv S.T (circleMap 0 (r ^ 2) u) * (circleMap 0 (r ^ 2) u * Complex.I)
      rw [periodic_circleMap 0 (r ^ 2) u]
    have hcmsqid : ∀ θ : ℝ, (circleMap 0 r θ) ^ 2 = circleMap 0 (r ^ 2) (2 * θ) := by
      intro θ
      simp only [circleMap, zero_add]
      rw [mul_pow, ← Complex.exp_nat_mul]
      congr 1
      · push_cast; ring
      · congr 1
        push_cast
        ring
    have hstep1 : ∀ θ : ℝ,
        logDeriv g (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)
        = (δ (2 * θ))⁻¹ * (2 * δ' (2 * θ)) := by
      intro θ
      set w : ℂ := circleMap 0 r θ with hwdef
      have hwmem : w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) :=
        circleMap_mem_annulusSet hrpos hr1 hr2 θ
      have hDdiff : DifferentiableAt ℂ (fun z => S.T z - c) (w ^ 2) :=
        ((S.an _ (hsrcmem _ (hsqmem w hwmem))).differentiableAt).sub_const c
      have hsqdiff : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) w :=
        (hasDerivAt_pow 2 w).differentiableAt
      have hcomp : logDeriv g w
          = logDeriv (fun z => S.T z - c) (w ^ 2) * deriv (fun z : ℂ => z ^ 2) w := by
        have h1 : g = (fun z => S.T z - c) ∘ (fun z : ℂ => z ^ 2) := rfl
        rw [h1]
        exact logDeriv_comp hDdiff hsqdiff
      have hderivsq : deriv (fun z : ℂ => z ^ 2) w = 2 * w := by
        have h6 := (hasDerivAt_pow 2 w).deriv
        rw [h6]
        push_cast
        ring
      have hlogD : logDeriv (fun z => S.T z - c) (w ^ 2)
          = deriv S.T (w ^ 2) / (S.T (w ^ 2) - c) := by
        rw [logDeriv_apply]
        congr 1
        exact deriv_sub_const c
      have hw2 : w ^ 2 = circleMap 0 (r ^ 2) (2 * θ) := hcmsqid θ
      have hRHS : (δ (2 * θ))⁻¹ * (2 * δ' (2 * θ))
          = (S.T (w ^ 2) - c)⁻¹ * (2 * (deriv S.T (w ^ 2) * (w ^ 2 * Complex.I))) := by
        show (S.T (circleMap 0 (r ^ 2) (2 * θ)) - c)⁻¹
            * (2 * (deriv S.T (circleMap 0 (r ^ 2) (2 * θ))
                * (circleMap 0 (r ^ 2) (2 * θ) * Complex.I)))
          = _
        rw [← hw2]
      rw [hcomp, hderivsq, hlogD, hRHS]
      have hne2 : S.T (w ^ 2) - c ≠ 0 := fun h => hTnec _ (hsqmem w hwmem) (sub_eq_zero.mp h)
      field_simp
    rw [intervalIntegral.integral_congr (fun θ _ => hstep1 θ)]
    have hdouble := windInt_double (a := 0) hδcont hδ'cont hδne hδper hδ'per
    have hLHS : (∫ θ in (0:ℝ)..(2 * Real.pi), (δ (2 * θ))⁻¹ * (2 * δ' (2 * θ)))
        = ∫ θ in (0:ℝ)..(2 * Real.pi), (δ (2 * θ) - 0)⁻¹ * (2 * δ' (2 * θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      show (δ (2 * θ))⁻¹ * (2 * δ' (2 * θ)) = (δ (2 * θ) - 0)⁻¹ * (2 * δ' (2 * θ))
      rw [sub_zero]
    have hinner : (∫ θ in (0:ℝ)..(2 * Real.pi), (δ θ - 0)⁻¹ * δ' θ)
        = windInt (S.loop hrsqpos hrsqrlo hrsqR₀) c := by
      apply intervalIntegral.integral_congr
      intro θ _
      show (δ θ - 0)⁻¹ * δ' θ = ((S.loop hrsqpos hrsqrlo hrsqR₀).γ θ - c)⁻¹
        * (S.loop hrsqpos hrsqrlo hrsqR₀).γ' θ
      rw [sub_zero]
      rfl
    have hlogσ₁pos : 0 < Real.log σ₁ :=
      Real.log_pos (by nlinarith)
    have hlogrhosq : Real.log σ₁ < Real.log (r ^ 2) :=
      Real.log_lt_log hσ₁pos hrsq₁
    have h0' : greenFunctionDyn c 0 < Real.log (r ^ 2) := by
      have h1 : Real.log (Real.sqrt σ₁) = Real.log σ₁ / 2 :=
        Real.log_sqrt (le_of_lt hσ₁pos)
      rw [h1] at hbandh
      linarith
    have hp' : greenFunctionDyn c c < Real.log (r ^ 2) := by linarith
    have hpoint := S.windInt_loop_point hrsqpos hrsqrlo hrsqR₀ h0' hp'
    rw [hLHS, hdouble, hinner, hpoint]
    push_cast
    ring
  have hgwind := hgwindAll ρ hρ1 hρ2
  obtain ⟨s, hs_an, hs_sq, hs_ne⟩ :=
    exists_pow_root_on_annulus hs₁pos hρ1 hρ2 hg_an hg_ne 1 1 hgwind
  have hs_sq' : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂), s w ^ 2 = g w := by
    intro w hw
    have := hs_sq w hw
    rwa [pow_one 2] at this
  -- (3) the s-winding: half the g-winding, at every band radius
  have hlogs : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂),
      logDeriv g w = 2 * logDeriv s w := by
    intro w hw
    have hev : g =ᶠ[nhds w] (fun z => s z ^ 2) := by
      filter_upwards [(isOpen_annulusSet _ _).mem_nhds hw] with z hz
      exact (hs_sq' z hz).symm
    rw [logDeriv_congr_of_eventuallyEq hev,
      logDeriv_fun_pow ((hs_an w hw).differentiableAt)]
    push_cast
    ring
  have hswind : ∀ r : ℝ, Real.sqrt σ₁ < r → r < Real.sqrt σ₂ →
      (∫ θ in (0:ℝ)..(2 * Real.pi), (s (circleMap 0 r θ))⁻¹
        * (deriv s (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)))
      = 2 * (Real.pi : ℂ) * Complex.I := by
    intro r hr1 hr2
    have hrpos : (0:ℝ) < r := lt_trans hs₁pos hr1
    have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) :=
      circleMap_mem_annulusSet hrpos hr1 hr2
    have hcongr : ∀ θ : ℝ,
        logDeriv g (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)
        = 2 * ((s (circleMap 0 r θ))⁻¹
            * (deriv s (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I))) := by
      intro θ
      rw [hlogs _ (hcm θ)]
      rw [logDeriv_apply]
      ring
    have h1 := hgwindAll r hr1 hr2
    rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ),
      intervalIntegral.integral_const_mul] at h1
    have h2 : ((2 ^ 1 * 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        = 2 * (2 * (Real.pi:ℂ) * Complex.I) := by push_cast; ring
    rw [h2] at h1
    exact mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0) h1
  -- (4) s is odd on the band
  have hsodd : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂), s (-w) = -s w := by
    -- the two closed sets where the ratio is ±1 cover the connected band
    have hnegmem : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂),
        -w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) := by
      rintro w ⟨h1, h2⟩
      exact ⟨by rwa [norm_neg], by rwa [norm_neg]⟩
    have hsq_ratio : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂),
        s (-w) = s w ∨ s (-w) = -s w := by
      intro w hw
      have h1 : s (-w) ^ 2 = s w ^ 2 := by
        rw [hs_sq' _ (hnegmem w hw), hs_sq' _ hw]
        show S.T ((-w) ^ 2) - c = S.T (w ^ 2) - c
        rw [neg_pow, show (-1:ℂ)^2 = 1 from by norm_num, one_mul]
      have h2 : (s (-w) - s w) * (s (-w) + s w) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (by linear_combination h)
    set E : Set ℂ := {w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) | s (-w) = s w} with hEdef
    set F : Set ℂ := {w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) | s (-w) = -s w} with hFdef
    have hscont : ContinuousOn s (annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)) :=
      hs_an.continuousOn
    -- both sets are closed in the band; if E is nonempty, evenness propagates everywhere
    by_contra hcon
    push Not at hcon
    obtain ⟨w₁, hw₁, hw₁ne⟩ := hcon
    -- w₁ ∈ E by the dichotomy
    have hw₁E : s (-w₁) = s w₁ := by
      rcases hsq_ratio w₁ hw₁ with h | h
      · exact h
      · exact absurd h hw₁ne
    -- E and F are relatively clopen (closed by continuity, open by local dichotomy + continuity)
    -- use preconnectedness through ambient-open sets
    have hEopen : IsOpen {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
        ∧ s (-w) ≠ -s w} := by
      rw [isOpen_iff_mem_nhds]
      rintro w ⟨hwA, hwne⟩
      have hc1 : ContinuousAt (fun z => s (-z) + s z) w := by
        have h1 : ContinuousAt s (-w) := (hs_an _ (hnegmem w hwA)).continuousAt
        have h2 : ContinuousAt s w := (hs_an _ hwA).continuousAt
        exact ((h1.comp (continuousAt_neg)).add h2)
      have hne0 : s (-w) + s w ≠ 0 := by
        intro h
        exact hwne (by linear_combination h)
      have hev := hc1.eventually_ne hne0
      filter_upwards [(isOpen_annulusSet _ _).mem_nhds hwA, hev] with z hz1 hz2
      refine ⟨hz1, ?_⟩
      intro h
      exact hz2 (by linear_combination h)
    have hFopen : IsOpen {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
        ∧ s (-w) ≠ s w} := by
      rw [isOpen_iff_mem_nhds]
      rintro w ⟨hwA, hwne⟩
      have hc1 : ContinuousAt (fun z => s (-z) - s z) w := by
        have h1 : ContinuousAt s (-w) := (hs_an _ (hnegmem w hwA)).continuousAt
        have h2 : ContinuousAt s w := (hs_an _ hwA).continuousAt
        exact ((h1.comp (continuousAt_neg)).sub h2)
      have hne0 : s (-w) - s w ≠ 0 := sub_ne_zero.mpr hwne
      have hev := hc1.eventually_ne hne0
      filter_upwards [(isOpen_annulusSet _ _).mem_nhds hwA, hev] with z hz1 hz2
      refine ⟨hz1, ?_⟩
      intro h
      exact hz2 (sub_eq_zero.mpr h)
    -- preconnectedness of the band splits on the two opens
    have hcover : annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
        ⊆ {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) ∧ s (-w) ≠ -s w}
          ∪ {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) ∧ s (-w) ≠ s w} := by
      intro w hw
      by_cases h : s (-w) = -s w
      · right
        refine ⟨hw, ?_⟩
        rw [h]
        intro h2
        have hzero : s w = 0 := by linear_combination (-(1:ℂ)/2) * h2
        exact hs_ne w hw hzero
      · exact Or.inl ⟨hw, h⟩
    have hconn := isConnected_annulus hs₁pos hs₁s₂
    have hneE : (annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
        ∩ {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) ∧ s (-w) ≠ -s w}).Nonempty :=
      ⟨w₁, hw₁, hw₁, by
        rw [hw₁E]
        intro h
        exact hs_ne w₁ hw₁ (by linear_combination ((1:ℂ)/2) * h)⟩
    have hneF : (annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
        ∩ {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) ∧ s (-w) ≠ s w}).Nonempty := by
      -- if F-side were empty, s would be globally even: refute by the winding parity
      by_contra hFe
      push Not at hFe
      have heven : ∀ w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂), s (-w) = s w := by
        intro w hw
        by_contra hne
        have hmem : w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)
            ∩ {w : ℂ | w ∈ annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) ∧ s (-w) ≠ s w} :=
          ⟨hw, hw, hne⟩
        rw [hFe] at hmem
        exact hmem
      -- parity contradiction at the core radius ρ
      exact absurd (hswind ρ hρ1 hρ2)
        (even_section_winding_ne hs₁pos hs_an hs_ne heven hρ1 hρ2)
    obtain ⟨v, hvA, ⟨_, hv1⟩, ⟨_, hv2⟩⟩ := hconn.isPreconnected _ _ hEopen hFopen
      hcover hneE hneF
    rcases hsq_ratio v hvA with h | h
    · exact hv2 h
    · exact hv1 h
  -- (5) sign-normalization against T on the overlap, then glue
  set B₁ : Set ℂ := annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂) with hB₁def
  set B₂ : Set ℂ := annulusSet rlo R₀ with hB₂def
  set O : Set ℂ := annulusSet rlo (Real.sqrt σ₂) with hOdef
  have hO1 : ∀ w ∈ O, w ∈ B₁ := by
    rintro w ⟨h1, h2⟩
    exact ⟨lt_trans hs₁ h1, h2⟩
  have hO2 : ∀ w ∈ O, w ∈ B₂ := by
    rintro w ⟨h1, h2⟩
    exact ⟨h1, lt_trans h2 hs₂R₀⟩
  have hOsq : ∀ w ∈ O, w ^ 2 ∈ B₂ := by
    rintro w ⟨h1, h2⟩
    have hw1 : (1:ℝ) < ‖w‖ := lt_trans hrlo h1
    constructor
    · rw [norm_pow]; nlinarith
    · rw [norm_pow]
      have h3 : ‖w‖ ^ 2 < Real.sqrt σ₂ ^ 2 := by nlinarith
      rw [Real.sq_sqrt (le_of_lt hσ₂pos)] at h3
      linarith
  have hTneO : ∀ w ∈ O, S.T w ≠ 0 := by
    intro w hw h
    have hlev := S.level _ (hO2 w hw)
    rw [h] at hlev
    have h1 : Real.log rlo < Real.log ‖w‖ := Real.log_lt_log (by linarith) hw.1
    rw [← hlev] at h1
    linarith
  have hsqO : ∀ w ∈ O, s w = S.T w ∨ s w = -S.T w := by
    intro w hw
    have h1 : s w ^ 2 = S.T w ^ 2 := by
      rw [hs_sq' _ (hO1 w hw)]
      show S.T (w ^ 2) - c = S.T w ^ 2
      rw [S.fe w (hO2 w hw) (hOsq w hw)]
      ring
    have h2 : (s w - S.T w) * (s w + S.T w) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  have hOconn : IsConnected O := isConnected_annulus (by linarith) hs₂
  have hOopen : IsOpen O := isOpen_annulusSet _ _
  have hsign := sign_constant_on_connected hOopen hOconn
    (fun w hw => (hs_an _ (hO1 w hw)).continuousAt)
    (fun w hw => (S.an _ (hO2 w hw)).continuousAt)
    hTneO hsqO
  -- the normalized root s'
  have hkey : ∃ s' : ℂ → ℂ, AnalyticOnNhd ℂ s' B₁ ∧
      (∀ w ∈ B₁, s' w ^ 2 = S.T (w ^ 2) - c) ∧ (∀ w ∈ B₁, s' w ≠ 0) ∧
      (∀ w ∈ B₁, s' (-w) = -s' w) ∧
      (∀ r : ℝ, Real.sqrt σ₁ < r → r < Real.sqrt σ₂ →
        (∫ θ in (0:ℝ)..(2 * Real.pi), (s' (circleMap 0 r θ))⁻¹
          * (deriv s' (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)))
        = 2 * (Real.pi : ℂ) * Complex.I) ∧
      (∀ w ∈ O, s' w = S.T w) := by
    rcases hsign with hpos | hneg
    · exact ⟨s, hs_an, hs_sq', hs_ne, hsodd, hswind, hpos⟩
    · refine ⟨fun w => -s w, hs_an.neg, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        have := hs_sq' w hw
        show (-s w) ^ 2 = S.T (w ^ 2) - c
        rw [neg_pow]
        simpa using this
      · intro w hw
        simpa using hs_ne w hw
      · intro w hw
        have := hsodd w hw
        show -s (-w) = -(-s w)
        rw [this]
      · intro r hr1 hr2
        have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ B₁ :=
          circleMap_mem_annulusSet (lt_trans hs₁pos hr1) hr1 hr2
        have hcongr : ∀ θ : ℝ,
            ((fun w => -s w) (circleMap 0 r θ))⁻¹
              * (deriv (fun w => -s w) (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I))
            = (s (circleMap 0 r θ))⁻¹
              * (deriv s (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)) := by
          intro θ
          have hd : deriv (fun w => -s w) (circleMap 0 r θ) = -deriv s (circleMap 0 r θ) := by
            have h1 : HasDerivAt s (deriv s (circleMap 0 r θ)) (circleMap 0 r θ) :=
              (hs_an _ (hcm θ)).differentiableAt.hasDerivAt
            exact h1.neg.deriv
          rw [hd]
          show (-s (circleMap 0 r θ))⁻¹
              * (-deriv s (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)) = _
          rw [inv_neg]
          ring
        rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
        exact hswind r hr1 hr2
      · intro w hw
        have := hneg w hw
        show -s w = S.T w
        rw [this]
        ring
  obtain ⟨s', hs'_an, hs'_sq, hs'_ne, hs'_odd, hs'_wind, hs'T⟩ := hkey
  -- glue into the extended section
  have hinter : B₁ ∩ B₂ = O := by
    ext w
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨h3, h2⟩
    · intro hw
      exact ⟨hO1 w hw, hO2 w hw⟩
  have hagree : Set.EqOn s' S.T (B₁ ∩ B₂) := by
    intro w hw
    rw [hinter] at hw
    exact hs'T w hw
  obtain ⟨Tn, hTn_an, hTn_s, hTn_T⟩ := analyticOnNhd_glue_twoChart
    (isOpen_annulusSet _ _) (isOpen_annulusSet _ _) hs'_an S.an hagree
  have hunion : B₁ ∪ B₂ = annulusSet (Real.sqrt σ₁) R₀ := by
    ext w
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, lt_trans h2 hs₂R₀⟩
      · exact ⟨lt_trans hs₁ h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h : ‖w‖ < Real.sqrt σ₂
      · exact Or.inl ⟨h1, h⟩
      · push Not at h
        exact Or.inr ⟨lt_of_lt_of_le hs₂ h, h2⟩
  -- membership dispatchers
  have hmem₁ : ∀ w : ℂ, Real.sqrt σ₁ < ‖w‖ → ‖w‖ < Real.sqrt σ₂ → Tn w = s' w :=
    fun w h1 h2 => hTn_s ⟨h1, h2⟩
  have hmem₂ : ∀ w : ℂ, rlo < ‖w‖ → ‖w‖ < R₀ → Tn w = S.T w :=
    fun w h1 h2 => hTn_T ⟨h1, h2⟩
  -- level identity of the glued map, for the surjectivity clause
  have hTnlev : ∀ w ∈ annulusSet (Real.sqrt σ₁) R₀,
      greenFunctionDyn c (Tn w) = Real.log ‖w‖ := by
    rintro w ⟨h1, h2⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · rw [hmem₁ w h1 h]
      have hwB₁ : w ∈ B₁ := ⟨h1, h⟩
      have hfe : quadratic c (s' w) = S.T (w ^ 2) := by
        unfold quadratic
        rw [hs'_sq w hwB₁]
        ring
      have h3 := greenFunctionDyn_quadratic c (s' w)
      rw [hfe, S.level _ (hsrcmem _ (hsqmem w hwB₁))] at h3
      have h4 : Real.log ‖w ^ 2‖ = 2 * Real.log ‖w‖ := by
        rw [norm_pow, Real.log_pow]
        push_cast
        ring
      rw [h4] at h3
      linarith
    · push Not at h
      rw [hmem₂ w (lt_of_lt_of_le hs₂ h) h2]
      exact S.level w ⟨lt_of_lt_of_le hs₂ h, h2⟩
  -- oddness of the glued map, for the sign correction in the pull-back
  have hTnodd : ∀ w ∈ annulusSet (Real.sqrt σ₁) R₀, Tn (-w) = -Tn w := by
    rintro w ⟨h1, h2⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · have hneg : Tn (-w) = s' (-w) := by
        apply hmem₁ <;> rwa [norm_neg]
      rw [hneg, hmem₁ w h1 h, hs'_odd w ⟨h1, h⟩]
    · push Not at h
      have hneg : Tn (-w) = S.T (-w) := by
        apply hmem₂ <;> rw [norm_neg]
        · exact lt_of_lt_of_le hs₂ h
        · exact h2
      rw [hneg, hmem₂ w (lt_of_lt_of_le hs₂ h) h2,
        S.odd w ⟨lt_of_lt_of_le hs₂ h, h2⟩]
  refine ⟨{ T := Tn, an := ?_, level := ?_, odd := ?_, fe := ?_, inj := ?_, dne := ?_, wind := ?_ },
    fun w hw => hTn_T hw, ?_⟩
  · rw [← hunion]
    exact hTn_an
  · -- level
    rintro w ⟨h1, h2⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · rw [hmem₁ w h1 h]
      have hwB₁ : w ∈ B₁ := ⟨h1, h⟩
      have hfe : quadratic c (s' w) = S.T (w ^ 2) := by
        unfold quadratic
        rw [hs'_sq w hwB₁]
        ring
      have h3 := greenFunctionDyn_quadratic c (s' w)
      rw [hfe, S.level _ (hsrcmem _ (hsqmem w hwB₁))] at h3
      have h4 : Real.log ‖w ^ 2‖ = 2 * Real.log ‖w‖ := by
        rw [norm_pow]
        rw [Real.log_pow]
        push_cast
        ring
      rw [h4] at h3
      linarith
    · push Not at h
      rw [hmem₂ w (lt_of_lt_of_le hs₂ h) h2]
      exact S.level w ⟨lt_of_lt_of_le hs₂ h, h2⟩
  · -- odd
    rintro w ⟨h1, h2⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · have hneg : Tn (-w) = s' (-w) := by
        apply hmem₁ <;> rwa [norm_neg]
      rw [hneg, hmem₁ w h1 h, hs'_odd w ⟨h1, h⟩]
    · push Not at h
      have hneg : Tn (-w) = S.T (-w) := by
        apply hmem₂ <;> rw [norm_neg]
        · exact lt_of_lt_of_le hs₂ h
        · exact h2
      rw [hneg, hmem₂ w (lt_of_lt_of_le hs₂ h) h2,
        S.odd w ⟨lt_of_lt_of_le hs₂ h, h2⟩]
  · -- functional equation
    rintro w ⟨h1, h2⟩ ⟨h3, h4⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · have hwB₁ : w ∈ B₁ := ⟨h1, h⟩
      have hsq : w ^ 2 ∈ annulusSet σ₁ σ₂ := hsqmem w hwB₁
      have h5 : Tn (w ^ 2) = S.T (w ^ 2) := by
        apply hmem₂
        · exact lt_trans hσ₁lo hsq.1
        · exact lt_of_lt_of_le hsq.2 hσ₂hi
      rw [h5, hmem₁ w h1 h]
      linear_combination -hs'_sq w hwB₁
    · push Not at h
      have hwB₂lo : rlo < ‖w‖ := lt_of_lt_of_le hs₂ h
      have hsqlo : rlo < ‖w ^ 2‖ := by
        rw [norm_pow]
        nlinarith [lt_trans hrlo hwB₂lo]
      rw [hmem₂ w hwB₂lo h2, hmem₂ (w ^ 2) hsqlo h4]
      exact S.fe w ⟨hwB₂lo, h2⟩ ⟨hsqlo, h4⟩
  · -- injectivity
    rintro w₁ ⟨h1, h2⟩ w₂ ⟨h3, h4⟩ heq
    -- equal levels force equal radii
    have hlev : ∀ w : ℂ, Real.sqrt σ₁ < ‖w‖ → ‖w‖ < R₀ →
        greenFunctionDyn c (Tn w) = Real.log ‖w‖ := by
      intro w ha hb
      by_cases h : ‖w‖ < Real.sqrt σ₂
      · rw [hmem₁ w ha h]
        have hwB₁ : w ∈ B₁ := ⟨ha, h⟩
        have hfe : quadratic c (s' w) = S.T (w ^ 2) := by
          unfold quadratic
          rw [hs'_sq w hwB₁]
          ring
        have h3' := greenFunctionDyn_quadratic c (s' w)
        rw [hfe, S.level _ (hsrcmem _ (hsqmem w hwB₁))] at h3'
        have h4' : Real.log ‖w ^ 2‖ = 2 * Real.log ‖w‖ := by
          rw [norm_pow, Real.log_pow]
          push_cast
          ring
        rw [h4'] at h3'
        linarith
      · push Not at h
        rw [hmem₂ w (lt_of_lt_of_le hs₂ h) hb]
        exact S.level w ⟨lt_of_lt_of_le hs₂ h, hb⟩
    have hnorm : ‖w₁‖ = ‖w₂‖ := by
      have e1 := hlev w₁ h1 h2
      have e2 := hlev w₂ h3 h4
      rw [heq] at e1
      have : Real.log ‖w₁‖ = Real.log ‖w₂‖ := by rw [← e1, ← e2]
      have hp1 : (0:ℝ) < ‖w₁‖ := lt_trans hs₁pos h1
      have hp2 : (0:ℝ) < ‖w₂‖ := lt_trans hs₁pos h3
      calc ‖w₁‖ = Real.exp (Real.log ‖w₁‖) := (Real.exp_log hp1).symm
        _ = Real.exp (Real.log ‖w₂‖) := by rw [this]
        _ = ‖w₂‖ := Real.exp_log hp2
    by_cases h : rlo < ‖w₁‖
    · -- both deep in the old section
      have h₂' : rlo < ‖w₂‖ := by rwa [hnorm] at h
      rw [hmem₂ w₁ h h2, hmem₂ w₂ h₂' h4] at heq
      exact S.inj ⟨h, h2⟩ ⟨h₂', h4⟩ heq
    · push Not at h
      -- both in the new band; square and use the old injectivity
      have hb₁ : ‖w₁‖ < Real.sqrt σ₂ := lt_of_le_of_lt h hs₂
      have hb₂ : ‖w₂‖ < Real.sqrt σ₂ := by rwa [hnorm] at hb₁
      have hw₁B : w₁ ∈ B₁ := ⟨h1, hb₁⟩
      have hw₂B : w₂ ∈ B₁ := ⟨h3, hb₂⟩
      rw [hmem₁ w₁ h1 hb₁, hmem₁ w₂ h3 hb₂] at heq
      have hsq' : S.T (w₁ ^ 2) = S.T (w₂ ^ 2) := by
        have e1 := hs'_sq w₁ hw₁B
        have e2 := hs'_sq w₂ hw₂B
        have : S.T (w₁ ^ 2) - c = S.T (w₂ ^ 2) - c := by
          rw [← e1, ← e2, heq]
        linear_combination this
      have hmem₁' : w₁ ^ 2 ∈ B₂ := hsrcmem _ (hsqmem w₁ hw₁B)
      have hmem₂' : w₂ ^ 2 ∈ B₂ := hsrcmem _ (hsqmem w₂ hw₂B)
      have hsqeq : w₁ ^ 2 = w₂ ^ 2 := S.inj hmem₁' hmem₂' hsq'
      have hpm : w₂ = w₁ ∨ w₂ = -w₁ := by
        have h5 : (w₂ - w₁) * (w₂ + w₁) = 0 := by linear_combination -hsqeq
        rcases mul_eq_zero.mp h5 with h6 | h6
        · exact Or.inl (sub_eq_zero.mp h6)
        · exact Or.inr (by linear_combination h6)
      rcases hpm with h6 | h6
      · exact h6.symm
      · exfalso
        rw [h6, hs'_odd w₁ hw₁B] at heq
        have h7 : s' w₁ = 0 := by linear_combination ((1:ℂ)/2) * heq
        exact hs'_ne w₁ hw₁B h7
  · -- derivative nonvanishing
    rintro w ⟨h1, h2⟩
    by_cases h : ‖w‖ < Real.sqrt σ₂
    · have hwB₁ : w ∈ B₁ := ⟨h1, h⟩
      have hder : deriv Tn w = deriv s' w := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [(isOpen_annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)).mem_nhds hwB₁]
          with z hz
        exact hTn_s hz
      rw [hder]
      have hs'd : HasDerivAt s' (deriv s' w) w :=
        (hs'_an w hwB₁).differentiableAt.hasDerivAt
      have hLd : HasDerivAt (fun x => s' x ^ 2) (2 * s' w * deriv s' w) w := by
        have h4 := hs'd.pow 2
        have h5 : (2:ℕ) * s' w ^ (2 - 1) * deriv s' w = 2 * s' w * deriv s' w := by
          push_cast
          ring
        rwa [h5] at h4
      have hRd : HasDerivAt (fun x : ℂ => S.T (x ^ 2) - c)
          (deriv S.T (w ^ 2) * (2 * w)) w := by
        have h3 : HasDerivAt S.T (deriv S.T (w ^ 2)) (w ^ 2) :=
          (S.an _ (hsrcmem _ (hsqmem w hwB₁))).differentiableAt.hasDerivAt
        have h4 : HasDerivAt (fun x : ℂ => x ^ 2) (2 * w) w := by
          have h5 := hasDerivAt_pow 2 w
          have h6 : ((2:ℕ):ℂ) * w ^ (2 - 1) = 2 * w := by push_cast; ring
          rwa [h6] at h5
        exact (HasDerivAt.comp w h3 h4).sub_const c
      have hEqF : (fun x => s' x ^ 2) =ᶠ[nhds w] (fun x : ℂ => S.T (x ^ 2) - c) := by
        filter_upwards [(isOpen_annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)).mem_nhds hwB₁]
          with z hz
        exact hs'_sq z hz
      have h7 : HasDerivAt (fun x : ℂ => S.T (x ^ 2) - c) (2 * s' w * deriv s' w) w :=
        hLd.congr_of_eventuallyEq hEqF.symm
      have hEqD : deriv S.T (w ^ 2) * (2 * w) = 2 * s' w * deriv s' w := hRd.unique h7
      intro h0
      rw [h0, mul_zero] at hEqD
      have hwne : w ≠ 0 := annulus_mem_ne_zero hs₁pos hwB₁
      have hne : deriv S.T (w ^ 2) * (2 * w) ≠ 0 :=
        mul_ne_zero (S.dne _ (hsrcmem _ (hsqmem w hwB₁)))
          (mul_ne_zero two_ne_zero hwne)
      exact hne hEqD
    · push Not at h
      have hwB₂ : w ∈ B₂ := ⟨lt_of_lt_of_le hs₂ h, h2⟩
      have hder : deriv Tn w = deriv S.T w := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [(isOpen_annulusSet rlo R₀).mem_nhds hwB₂] with z hz
        exact hTn_T hz
      rw [hder]
      exact S.dne w hwB₂
  · -- winding
    intro r hr1 hr2
    have hrpos : (0:ℝ) < r := lt_trans hs₁pos hr1
    by_cases h : rlo < r
    · -- congruent to the old section's loop
      have hcongr : ∀ θ : ℝ,
          (Tn (circleMap 0 r θ))⁻¹
            * (deriv Tn (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I))
          = (S.T (circleMap 0 r θ))⁻¹
            * (deriv S.T (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)) := by
        intro θ
        have hcm : circleMap 0 r θ ∈ B₂ := circleMap_mem_annulusSet hrpos h hr2 θ
        have hval : Tn (circleMap 0 r θ) = S.T (circleMap 0 r θ) := hTn_T hcm
        have hder : deriv Tn (circleMap 0 r θ) = deriv S.T (circleMap 0 r θ) := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [(isOpen_annulusSet rlo R₀).mem_nhds hcm] with z hz
          exact hTn_T hz
        rw [hval, hder]
      rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
      exact S.wind r h hr2
    · push Not at h
      have hb : r < Real.sqrt σ₂ := lt_of_le_of_lt h hs₂
      have hcongr : ∀ θ : ℝ,
          (Tn (circleMap 0 r θ))⁻¹
            * (deriv Tn (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I))
          = (s' (circleMap 0 r θ))⁻¹
            * (deriv s' (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)) := by
        intro θ
        have hcm : circleMap 0 r θ ∈ B₁ := circleMap_mem_annulusSet hrpos hr1 hb θ
        have hval : Tn (circleMap 0 r θ) = s' (circleMap 0 r θ) := hTn_s hcm
        have hder : deriv Tn (circleMap 0 r θ) = deriv s' (circleMap 0 r θ) := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [(isOpen_annulusSet (Real.sqrt σ₁) (Real.sqrt σ₂)).mem_nhds hcm]
            with z hz
          exact hTn_s hz
        rw [hval, hder]
      rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
      exact hs'_wind r hr1 hb
  · -- band surjectivity
    intro z hz1 hz2
    rcases lt_or_ge (Real.log rlo) (greenFunctionDyn c z) with hcase | hcase
    · obtain ⟨w, hw, hweq⟩ := hsurj z hcase hz2
      refine ⟨w, ⟨lt_trans hs₁ hw.1, hw.2⟩, ?_⟩
      show Tn w = z
      rw [hmem₂ w hw.1 hw.2]
      exact hweq
    · -- pull the point back through the quadratic and take the odd-corrected root
      have hlogsq : Real.log (Real.sqrt σ₁) = Real.log σ₁ / 2 :=
        Real.log_sqrt (le_of_lt hσ₁pos)
      have hfz1 : Real.log rlo < greenFunctionDyn c (quadratic c z) := by
        rw [greenFunctionDyn_quadratic]
        have h1 : Real.log rlo < Real.log σ₁ :=
          Real.log_lt_log (by linarith) hσ₁lo
        rw [hlogsq] at hz1
        linarith
      have hfz2 : greenFunctionDyn c (quadratic c z) < Real.log R₀ := by
        rw [greenFunctionDyn_quadratic]
        have h1 : Real.log (rlo ^ 2) < Real.log R₀ :=
          Real.log_lt_log (by positivity) hrloR₀
        rw [Real.log_pow] at h1
        push_cast at h1
        have h2 : greenFunctionDyn c z ≤ Real.log rlo := hcase
        linarith
      obtain ⟨w', hw', hw'eq⟩ := hsurj (quadratic c z) hfz1 hfz2
      obtain ⟨w, hwsq⟩ := IsSepClosed.exists_pow_nat_eq w' 2
      -- the root coordinate sits in the new band, at the level of z
      have hGz0 : 0 < greenFunctionDyn c z := by
        have h1 : 0 < Real.log (Real.sqrt σ₁) := by
          rw [hlogsq]
          have := Real.log_pos (show (1:ℝ) < σ₁ from by nlinarith)
          linarith
        linarith
      have hnw' : Real.log ‖w'‖ = 2 * greenFunctionDyn c z := by
        have h1 := S.level w' hw'
        rw [hw'eq, greenFunctionDyn_quadratic] at h1
        linarith
      have hnw : Real.log ‖w‖ = greenFunctionDyn c z := by
        have h1 : ‖w‖ ^ 2 = ‖w'‖ := by
          rw [← hwsq, norm_pow]
        have h2 : 2 * Real.log ‖w‖ = Real.log ‖w'‖ := by
          rw [← h1, Real.log_pow]
          push_cast
          ring
        linarith [hnw', h2]
      have hwann : w ∈ annulusSet (Real.sqrt σ₁) R₀ := by
        have hwpos : (0:ℝ) < ‖w‖ := by
          by_contra hcon
          push Not at hcon
          have h1 : ‖w‖ = 0 := le_antisymm hcon (norm_nonneg w)
          rw [h1] at hnw
          have h2 : Real.log (0:ℝ) = 0 := Real.log_zero
          rw [h2] at hnw
          linarith
        constructor
        · calc Real.sqrt σ₁ = Real.exp (Real.log (Real.sqrt σ₁)) :=
              (Real.exp_log (Real.sqrt_pos.mpr hσ₁pos)).symm
            _ < Real.exp (Real.log ‖w‖) := Real.exp_lt_exp.mpr (by rw [hnw]; exact hz1)
            _ = ‖w‖ := Real.exp_log hwpos
        · calc ‖w‖ = Real.exp (Real.log ‖w‖) := (Real.exp_log hwpos).symm
            _ < Real.exp (Real.log R₀) := Real.exp_lt_exp.mpr (by rw [hnw]; exact hz2)
            _ = R₀ := Real.exp_log (by nlinarith)
      -- the squared relation: Tn w is a square root of z², so ±z
      have hwB₁ : w ∈ B₁ := by
        refine ⟨hwann.1, ?_⟩
        have h1 : Real.log ‖w‖ ≤ Real.log rlo := by
          rw [hnw]
          exact hcase
        have h2 : ‖w‖ ≤ rlo := by
          have hwpos : (0:ℝ) < ‖w‖ := lt_trans (Real.sqrt_pos.mpr hσ₁pos) hwann.1
          calc ‖w‖ = Real.exp (Real.log ‖w‖) := (Real.exp_log hwpos).symm
            _ ≤ Real.exp (Real.log rlo) := Real.exp_le_exp.mpr h1
            _ = rlo := Real.exp_log (by linarith)
        exact lt_of_le_of_lt h2 hs₂
      have hsq : Tn w ^ 2 = z ^ 2 := by
        rw [hmem₁ w hwB₁.1 hwB₁.2, hs'_sq w hwB₁]
        have h1 : w ^ 2 = w' := hwsq
        rw [h1, hw'eq]
        unfold quadratic
        ring
      have hpm : Tn w = z ∨ Tn w = -z := by
        have h5 : (Tn w - z) * (Tn w + z) = 0 := by linear_combination hsq
        rcases mul_eq_zero.mp h5 with h6 | h6
        · exact Or.inl (sub_eq_zero.mp h6)
        · exact Or.inr (by linear_combination h6)
      rcases hpm with h6 | h6
      · exact ⟨w, hwann, h6⟩
      · refine ⟨-w, ?_, ?_⟩
        · constructor <;> rw [norm_neg]
          · exact hwann.1
          · exact hwann.2
        · show Tn (-w) = z
          rw [hTnodd w hwann, h6]
          ring


/-- **The tower descent.**  For every `ε > 0` there is a tower section whose bottom level is
within `ε` of the critical level `h = G_c(0)`, on an annulus whose top `R₀` clears
`exp(4h + 1)` (room for the sub-critical chain). -/
theorem exists_tower_deep_of_anchor (c : ℂ) {ε : ℝ} (hε : 0 < ε) (M : ℝ)
    {Ra Rinj : ℝ} (hRa1 : 1 < Ra) (hRaG : Real.exp (greenFunctionDyn c 0) < Ra)
    (hanchor : ∀ rhi : ℝ, Ra < rhi → ∃ S : TowerSection c Ra rhi,
      (∀ w ∈ annulusSet Ra rhi,
        bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
      (∀ z : ℂ, Real.log Ra < greenFunctionDyn c z →
        greenFunctionDyn c z < Real.log rhi → z ∈ S.T '' annulusSet Ra rhi)) :
    ∃ (rlo R₀ : ℝ), 1 < rlo ∧ rlo ≤ Ra ∧ Ra < R₀ ∧ rlo ^ 2 < R₀ ∧
      M < R₀ ∧
      greenFunctionDyn c 0 < Real.log rlo ∧
      Real.log rlo < greenFunctionDyn c 0 + ε ∧
      ∃ S : TowerSection c rlo R₀,
        (∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ →
          bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
        (∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
          greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hh0 : 0 ≤ h := greenFunctionDyn_nonneg c 0
  set R₀ : ℝ := Ra ^ 2 + max M 0 + 1 with hR₀def
  have hMnn : (0:ℝ) ≤ max M 0 := le_max_right M 0
  have hR₀Ra : Ra < R₀ := by
    rw [hR₀def]; nlinarith
  have hRasqR₀ : Ra ^ 2 < R₀ := by
    rw [hR₀def]; nlinarith
  have hR₀exp : M < R₀ := by
    have h1 : M ≤ max M 0 := le_max_left M 0
    rw [hR₀def]; nlinarith
  obtain ⟨S₀, hS₀φ, hS₀surj⟩ := hanchor R₀ hR₀Ra
  have hhRa : h < Real.log Ra := by
    calc h = Real.log (Real.exp h) := (Real.log_exp h).symm
      _ < Real.log Ra := Real.log_lt_log (Real.exp_pos h) hRaG
  -- the one-step descent with uniform gap contraction
  have hstep : ∀ rlo : ℝ, 1 < rlo → rlo ^ 2 < R₀ → h < Real.log rlo → rlo ≤ Ra →
      (∃ S : TowerSection c rlo R₀,
        (∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ →
          bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
        (∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
          greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀)) →
      ∃ rlo' : ℝ, 1 < rlo' ∧ rlo' ^ 2 < R₀ ∧ h < Real.log rlo' ∧ rlo' ≤ Ra ∧
        Real.log rlo' - h ≤ (3/4) * (Real.log rlo - h) ∧
        ∃ S' : TowerSection c rlo' R₀,
          (∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ →
            bottcherCoord c (S'.T w) = w ∧ S'.T w ∈ escapeOpen c ∧ Rinj < ‖S'.T w‖) ∧
          (∀ z : ℂ, Real.log rlo' < greenFunctionDyn c z →
            greenFunctionDyn c z < Real.log R₀ → z ∈ S'.T '' annulusSet rlo' R₀) := by
    intro rlo h1 h2 h3 hRale hS
    obtain ⟨S, hSφ, hSsurj⟩ := hS
    set ℓ : ℝ := Real.log rlo with hℓdef
    have hℓ0 : 0 < ℓ := Real.log_pos h1
    have hrlopos : (0:ℝ) < rlo := by linarith
    have hrloexp : rlo = Real.exp ℓ := (Real.exp_log hrlopos).symm
    -- the source bottom level: 1.5ℓ above 2h, else h + ℓ
    set τ : ℝ := if 2 * h < ℓ then (3/2) * ℓ else h + ℓ with hτdef
    have hτ2h : 2 * h < τ := by
      rw [hτdef]
      by_cases hc : 2 * h < ℓ
      · rw [if_pos hc]; nlinarith
      · rw [if_neg hc]; linarith
    have hτℓ : ℓ < τ := by
      rw [hτdef]
      by_cases hc : 2 * h < ℓ
      · rw [if_pos hc]; nlinarith
      · rw [if_neg hc]
        push Not at hc
        -- here ℓ ≤ 2h with ℓ > h forces 0 < h
        have hhpos : 0 < h := by linarith
        linarith
    have hτ2ℓ : τ < 2 * ℓ := by
      rw [hτdef]
      by_cases hc : 2 * h < ℓ
      · rw [if_pos hc]; nlinarith
      · rw [if_neg hc]; linarith
    have hgap : τ / 2 - h ≤ (3/4) * (ℓ - h) := by
      rw [hτdef]
      by_cases hc : 2 * h < ℓ
      · rw [if_pos hc]; nlinarith
      · rw [if_neg hc]; nlinarith
    -- the step with σ₁ := exp τ, σ₂ := R₀
    set σ₁ : ℝ := Real.exp τ with hσ₁def
    have hσ₁rlo : rlo < σ₁ := by
      rw [hσ₁def, hrloexp]
      exact Real.exp_lt_exp.mpr hτℓ
    have hσ₁sq : σ₁ < rlo ^ 2 := by
      rw [hσ₁def, hrloexp, ← Real.exp_nat_mul]
      apply Real.exp_lt_exp.mpr
      push_cast
      linarith
    have hcab : greenFunctionDyn c c < Real.log σ₁ := by
      rw [hσ₁def, Real.log_exp, greenFunctionDyn_critical_value c]
      exact hτ2h
    obtain ⟨S', hS'T, hS'surj⟩ :=
      tower_extension_step h1 h2 S h3 hσ₁rlo hσ₁sq h2 le_rfl hcab hSsurj
    have hS'φ : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ →
        bottcherCoord c (S'.T w) = w ∧ S'.T w ∈ escapeOpen c ∧ Rinj < ‖S'.T w‖ := by
      intro w hw1 hw2
      have hwold : w ∈ annulusSet rlo R₀ := ⟨lt_of_le_of_lt hRale hw1, hw2⟩
      rw [hS'T w hwold]
      exact hSφ w hw1 hw2
    have hs₁rlo : Real.sqrt σ₁ < rlo := by
      rw [Real.sqrt_lt' (by linarith)]
      exact hσ₁sq
    have hS'surj' : ∀ z : ℂ, Real.log (Real.sqrt σ₁) < greenFunctionDyn c z →
        greenFunctionDyn c z < Real.log R₀ → z ∈ S'.T '' annulusSet (Real.sqrt σ₁) R₀ :=
      hS'surj
    refine ⟨Real.sqrt σ₁, ?_, ?_, ?_, by linarith, ?_, S', hS'φ, hS'surj'⟩
    · have h4 : (0:ℝ) < τ := by linarith
      have h5 : (1:ℝ) < σ₁ := by
        rw [hσ₁def]
        calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ < Real.exp τ := Real.exp_lt_exp.mpr h4
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ < Real.sqrt σ₁ := Real.sqrt_lt_sqrt (by norm_num) h5
    · have h4 : Real.sqrt σ₁ ^ 2 = σ₁ := Real.sq_sqrt (le_of_lt (Real.exp_pos _))
      rw [h4]
      calc σ₁ < rlo ^ 2 := hσ₁sq
        _ < R₀ := h2
    · have h4 : Real.log (Real.sqrt σ₁) = τ / 2 := by
        rw [Real.log_sqrt (le_of_lt (Real.exp_pos _)), Real.log_exp]
      rw [h4]
      linarith
    · have h4 : Real.log (Real.sqrt σ₁) = τ / 2 := by
        rw [Real.log_sqrt (le_of_lt (Real.exp_pos _)), Real.log_exp]
      rw [h4]
      linarith
  -- iterate: geometric decay of the level gap
  have hiter : ∀ n : ℕ, ∃ rlo : ℝ, 1 < rlo ∧ rlo ^ 2 < R₀ ∧ h < Real.log rlo ∧ rlo ≤ Ra ∧
      Real.log rlo - h ≤ (3/4) ^ n * (Real.log Ra - h) ∧
      ∃ S : TowerSection c rlo R₀,
        (∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ →
          bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
        (∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
          greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) := by
    intro n
    induction n with
    | zero =>
        refine ⟨Ra, hRa1, hRasqR₀, hhRa, le_refl Ra, by norm_num, S₀, ?_, hS₀surj⟩
        intro w hw1 hw2
        exact hS₀φ w ⟨hw1, hw2⟩
    | succ m ih =>
        obtain ⟨rlo, h1, h2, h3, hle, h4, hS⟩ := ih
        obtain ⟨rlo', h1', h2', h3', hle', h4', hS'⟩ := hstep rlo h1 h2 h3 hle hS
        refine ⟨rlo', h1', h2', h3', hle', ?_, hS'⟩
        calc Real.log rlo' - h ≤ (3/4) * (Real.log rlo - h) := h4'
          _ ≤ (3/4) * ((3/4) ^ m * (Real.log Ra - h)) := by nlinarith
          _ = (3/4) ^ (m + 1) * (Real.log Ra - h) := by ring
  -- pick n with the gap below ε
  have hgap0 : (0:ℝ) < Real.log Ra - h := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (3/4:ℝ) ^ n * (Real.log Ra - h) < ε := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show (0:ℝ) < ε / (Real.log Ra - h) from by positivity)
      (by norm_num : (3:ℝ)/4 < 1)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hgap0] at hn
    nlinarith
  obtain ⟨rlo, h1, h2, h3, hle, h4, hS⟩ := hiter n
  exact ⟨rlo, R₀, h1, hle, hR₀Ra, h2, hR₀exp, h3, by linarith, hS⟩

/-- The self-contained form: anchor obtained internally. -/
theorem exists_tower_deep (c : ℂ) {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ (rlo Rb R₀ Rinj : ℝ), 1 < rlo ∧ rlo ≤ Rb ∧ Rb < R₀ ∧ rlo ^ 2 < R₀ ∧
      M < R₀ ∧
      greenFunctionDyn c 0 < Real.log rlo ∧
      Real.log rlo < greenFunctionDyn c 0 + ε ∧
      Set.InjOn (bottcherCoord c) {z : ℂ | Rinj < ‖z‖} ∧
      ∃ S : TowerSection c rlo R₀,
        (∀ w : ℂ, Rb < ‖w‖ → ‖w‖ < R₀ →
          bottcherCoord c (S.T w) = w ∧ S.T w ∈ escapeOpen c ∧ Rinj < ‖S.T w‖) ∧
        (∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
          greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) := by
  obtain ⟨Ra, Rinj, hRa1, hRaG, hInj, _hRinjbd, hanchor⟩ := exists_tower_anchor c
  obtain ⟨rlo, R₀, h1, h2, h3, h4, h5, h6, h7, hS⟩ :=
    exists_tower_deep_of_anchor c hε M hRa1 hRaG hanchor
  exact ⟨rlo, Ra, R₀, Rinj, h1, h2, h3, h4, h5, h6, h7, hInj, hS⟩

end Bottcher
