import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.Readout
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.Heights


/-!
# Finite-height camera for arbitrary coefficients

The carrier determines the isolating windows. Absolute Lorentzian mass pays
for their far tail, so the explicit moment height applies to complex weights
without an integral multiplicity or a lower bound on nonzero coefficients.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- The polynomial-isolation camera error for all coefficients of bounded absolute mass. -/
theorem weighted_rvm_readout_core {lam β M' K' ℓ c K MK ρ α q S'' T u a ε D C₀ η r : ℝ} {k m J : ℕ}
    {Z : ZeroConfig} {z₀ : ℂ} {s : Finset ℂ}
    (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hM' : 0 ≤ M') (hlam0 : 0 < lam)
    (hβ0 : 0 < β) (hβlam : β ≤ lam) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M'))
    (hK : K = c / 2 + 2) (hK' : 0 ≤ K') (hMK0 : 0 < MK) (hρ0 : 0 < ρ)
    (hα : α = 1 / (8 * MK * (1 + ρ))) (hα0 : 0 < α) (hq : q = max 0 (Real.log α⁻¹))
    (hS''1 : 1 ≤ S'') (hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8)
    (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC₀ℓ : |C₀| ≤ ℓ * D) (hDa : π * D / 2 + 2 * ε ≤ a)
    (hη : η = T ^ (-M')) (hkK : (K + K') * u ^ 2 ≤ k) (hk1 : 1 ≤ k)
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    (hmle : (m : ℝ) ≤ MK * u ^ 2) (hmε : (m : ℝ) / ε ≤ ρ * u)
    (hbig : 6 * slowConst lam ℓ M' ≤ Real.exp u) (h4lam : 4 * lam ≤ Real.exp u)
    (hz₀ : |z₀.im - T| ≤ T / 4) (hz₀re : |z₀.re - 1 / 2| ≤ 1 / 2)
    (hr0 : 0 ≤ r) (hr : r ≤ T ^ (-(M' + slowExponent lam + 1)))
    (hiso' : ∀ z, z ∈ Z.carrier → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r) (hds : ∀ z, z ∈ Z.carrier → ‖z - z₀‖ ≤ r → z ∈ s) :
    ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ ≠ 0 ∧
      ∀ weights : ℂ → ℂ, (∀ z, weights z ≠ 0 → z ∈ Z.carrier) →
        (Summable fun z => ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) →
        (∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) ≤ S'' →
        ∀ j : ℕ, j ≤ J →
          ApertureWindow a (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
          ‖weightedImage weights (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁))
              (localWindow z₀.im G₁) /
              ((-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀) -
            ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
            (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
              Real.exp (-(K' * u ^ 3)) := by
  have hu0 : 0 < u := by linarith only [hu1]
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hD0 : 0 < D := by linarith only [hD1]
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hT0 _
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith only [Real.exp_pos u, Real.pi_gt_three]
  have hT2 : 2 ≤ T := by
    linarith only [Real.add_one_le_exp u, hu1, hET]
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  -- the slow rate and the disc radius
  have hΛ := six_slowRate_le_rpow hu1 hTu hM' hlam0 hβlam hD1 hDup hC₀ℓ hε hη hbig
  have hΛ0 : 0 ≤ slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 :=
    slowRate_nonneg (by positivity) (localSlack_nonneg hD0) hη0 zero_le_one
  have hDT : 4 * D ≤ T ^ 2 := by
    have h1 : 4 * D ≤ 4 * lam * Real.exp u := by
      have hh := mul_le_mul_of_nonneg_left (hDup.trans (mul_le_mul_of_nonneg_left
        (show u ≤ Real.exp u by linarith only [Real.add_one_le_exp u]) hlam0.le)) (by norm_num : (0 : ℝ) ≤ 4)
      linarith only [hh]
    have h2 : 4 * lam * Real.exp u ≤ Real.exp u * Real.exp u :=
      mul_le_mul_of_nonneg_right h4lam (Real.exp_pos u).le
    have h3 : Real.exp u * Real.exp u ≤ T ^ 2 := by
      rw [sq]; exact mul_le_mul hET hET (Real.exp_pos u).le hT0.le
    exact h1.trans (h2.trans h3)
  obtain ⟨hrD, hrΛ⟩ := disc_radius_small hT2
    (by unfold slowExponent; linarith only [mul_pos Real.pi_pos hlam0, hlam0, hM'] :
      1 ≤ M' + slowExponent lam) hr hΛ0
    hΛ hD0 hDT
  have hrR : r ≤ T / 4 := by
    exact (hrD.trans (min_le_right _ _)).trans (by linarith only [hT2])
  -- the moments, read from the image
  obtain ⟨F₁, G₁, hF₁, hG₁, hfl, hread⟩ := weighted_discMoment_readout_slow hD0 hη0 hε0 hDa hb hbs hb1 hk1
    hm hbm (C0 := 1) (fun w => by rw [one_mul]; exact hb0 w) hz₀re (R := T / 4)
    (by positivity) hr0 hrR hrD hrΛ hiso' hcount' hsd hds
  have hfl0 : 0 < windowFloor (2 * D⁻¹) (localSlack D C₀) η :=
    windowFloor_pos (by positivity) (localSlack_nonneg hD0) hη0
  have hΦ0 := norm_pos_iff.mp (lt_of_lt_of_le (pow_pos hfl0 2) hfl)
  refine ⟨F₁, G₁, hF₁, hG₁, hΦ0, fun weights hweights hweightsSum hStail j hj => ?_⟩
  -- the tail
  have hSg0 : 0 ≤ ∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by linarith only [Complex.normSq_nonneg (gammaOf z)])
  have hQ0 : 0 < (1 + T / 4) ^ (2 * k - 2) := by positivity
  have hQne := hQ0.ne'
  have hflne : windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≠ 0 := (pow_pos hfl0 2).ne'
  have hexp : Real.exp (-(2 * K' * u ^ 3)) / 4 ≤ Real.exp (-(K' * u ^ 3)) := by
    have hK3 : 0 ≤ K' * u ^ 3 := mul_nonneg hK' (pow_pos hu0 3).le
    have he : Real.exp (-(2 * K' * u ^ 3)) ≤ Real.exp (-(K' * u ^ 3)) :=
      Real.exp_le_exp.mpr (by linarith only [hK3])
    linarith only [he, Real.exp_pos (-(2 * K' * u ^ 3))]
  obtain ⟨Tl, hTl⟩ : ∃ Tl, Tl = (windowGrowth (2 * D⁻¹) (localSlack D C₀) *
      (4 * (1 + (m : ℝ) / ε)) ^ m * 1 * Real.exp ε) ^ 2 * Real.exp a *
        (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + T / 4) ^ (2 * k - 2)) *
          ∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z)) := ⟨_, rfl⟩
  have hTl0 : 0 ≤ Tl := by rw [hTl]; exact mul_nonneg (by positivity) hSg0
  have htail : Tl / windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤ Real.exp (-(K' * u ^ 3)) := by
    rw [hTl]
    refine (camera_tail_budget (z₀ := z₀) (Sg := ∑' z, ‖weights z‖ /
      (1 + Complex.normSq (gammaOf z))) hu1 hTu hM' hlam0 hβlam hℓ0 hc hK hMK0 hρ0 hα hα0 hq
      hS''1 hu_bud ha hε hε0 hD1 hDup hC₀ℓ hη hη0 hkK hk1 hmle hmε hz₀ hSg0
      hStail (le_of_eq ?_)).trans hexp
    unfold localCameraConst
    field_simp
  obtain ⟨hFj, hbd⟩ := hread weights hweights hweightsSum j hj
  rw [← hTl] at hbd
  refine ⟨hFj, (readout_div_le hfl0 hfl hTl0 hbd).trans (add_le_add ?_ htail)⟩
  exact mul_le_mul_of_nonneg_left hΛ
    (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _))

private theorem weightedCameraMomentHeight_eq_of_parameters (J : ℕ)
    {θ lam A S M' K' β ℓ e c K MK ρ α q S'' V U₀ : ℝ}
    (hβ : β = lam - θ / 2) (hℓ : ℓ = 2 * π * A / lam)
    (he : e = 6 * slackBound ℓ * (1 + slackBound ℓ))
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M'))
    (hK : K = c / 2 + 2) (hMK : MK = e * lam + K + K' + 2 + J)
    (hρ : ρ = 8 * MK / β) (hα : α = 1 / (8 * MK * (1 + ρ)))
    (hq : q = max 0 (Real.log α⁻¹)) (hS'' : S'' = max S 1)
    (hV : V = max (6 * cameraSlowConstant lam ℓ M') (4 * lam) + 1)
    (hU₀ : U₀ = max (max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V)) :
    cameraMomentHeight J θ lam A S M' K' = 2 * π * Real.exp U₀ := by
  rw [hU₀, hV, hS'', hq, hα, hρ, hMK, hK, hc, he, hℓ, hβ]
  rfl

/-- The disc moments are read at every height above the finite camera expression. -/
theorem weighted_discMoment_readout_rvm_explicit (J : ℕ) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight J θ lam A S M' K' ≤ T →
      ∀ Z : ZeroConfig,
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, z ∈ Z.carrier → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
        (∀ z, z ∈ Z.carrier → ‖z - z₀‖ ≤ r → z ∈ s) →
        ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₁ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G₁ ∧
          pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ ≠ 0 ∧
          ∀ weights : ℂ → ℂ, (∀ z, weights z ≠ 0 → z ∈ Z.carrier) →
            (Summable fun z => ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) →
            (∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) ≤ S →
            ∀ j : ℕ, j ≤ J →
              ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
              ‖weightedImage weights (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁))
                  (localWindow z₀.im G₁) /
                  ((-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀) -
                ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
                (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
                  Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith only [hθ, hlam]
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - θ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith only [hlam]
  have hβlam : β ≤ lam := by rw [hβ]; linarith only [hθ]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 * π * A / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have : 0 ≤ slackBound ℓ := by unfold slackBound; positivity
  have he0 : 0 ≤ e := by rw [he]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * growthRate ℓ * lam ^ 2 +
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M') := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith only [hc0]
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = e * lam + K + K' + 2 + J := ⟨_, rfl⟩
  have hMK0 : 0 < MK := by rw [hMK]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 8 * MK / β := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 1 / (8 * MK * (1 + ρ)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = max 0 (Real.log α⁻¹) := ⟨_, rfl⟩
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨V, hV⟩ : ∃ V, V = max (6 * cameraSlowConstant lam ℓ M') (4 * lam) + 1 := ⟨_, rfl⟩
  have hV0 : 0 < V := by
    rw [hV]
    linarith only [hlam0, le_max_right (6 * cameraSlowConstant lam ℓ M') (4 * lam)]
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V) := ⟨_, rfl⟩
  have hheight := weightedCameraMomentHeight_eq_of_parameters J
    hβ hℓ he hc hK hMK hρ hα hq hS'' hV hU₀
  intro T hT Z hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  rw [hheight] at hT
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by
    rw [le_div_iff₀ h2π0]
    linarith only [hT]
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith only [hu1]
  have hu_lam : 2 * π / lam ≤ u :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans huU₀
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) hTdiv)]
    field_simp
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hEV : V ≤ Real.exp u := by
    have h1 : Real.log V ≤ u := (le_max_right _ _).trans huU₀
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr h1
  have hbig : 6 * slowConst lam ℓ M' ≤ Real.exp u := by
    rw [hV] at hEV
    have hmax := le_max_left (6 * cameraSlowConstant lam ℓ M') (4 * lam)
    have hslow := slowConst_le_cameraSlowConstant (M' := M') hlam0 hℓ0
    linarith only [hEV, hmax, hslow]
  have h4lam : 4 * lam ≤ Real.exp u := by
    rw [hV] at hEV
    linarith only [hEV, le_max_right (6 * cameraSlowConstant lam ℓ M') (4 * lam)]
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith only [Real.exp_pos u, Real.pi_gt_three]
  have hT1 : 1 ≤ T := (Real.one_le_exp hu0.le).trans hET
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  obtain ⟨hDa, hD1, hDup, hC₀ℓ⟩ :=
    rvm_density_facts hθ hlam hA hβ hℓ hu0 hu_lam ha hε hD hC₀
  have hD0 : 0 < D := by linarith only [hD1]
  obtain ⟨η, hη⟩ : ∃ η, η = T ^ (-M') := ⟨_, rfl⟩
  -- decay order `k = ⌈(K + K') u²⌉₊` and spline order `m = ⌈W⌉₊ + k + J`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈(K + K') * u ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + (k + J) := ⟨_, rfl⟩
  obtain ⟨hkK, hk1, hm', hmle, hmε⟩ :=
    rvm_order_facts hK1 hK' he0 hlam0 hβ0 hMK hρ hu1 hε hDup hW0 hWle hk hmdef
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m := hWdef ▸ hm'
  -- the cluster near `z₀`
  have hsub_band : ∀ z : ℂ, |z.im - z₀.im| ≤ T / 4 → |z.im - T| ≤ T / 2 := fun z hz => by
    have h1 := abs_le.mp hz
    have h2 := abs_le.mp hz₀
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hiso' : ∀ z, z ∈ Z.carrier → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖ :=
    fun z hcz hzR => by rw [hη]; exact hiso z hcz (hsub_band z hzR)
  have hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
    intro s x y hxy hs
    have hc1 := hcount s x y hxy fun z hz =>
      ⟨(hs z hz).1, hsub_band z (hs z hz).2.1, (hs z hz).2.2⟩
    rw [← hC₀] at hc1
    have hDθ : θ / (2 * π) * u ≤ D := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith only [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    exact hc1.trans (add_le_add hmul (le_refl C₀))
  have hSbound : S ≤ S'' := by rw [hS'']; exact le_max_left _ _
  obtain ⟨F₁, G₁, hF₁, hG₁, hΦ, hread⟩ := weighted_rvm_readout_core (lam := lam) (β := β) (M' := M') (K' := K') (ℓ := ℓ)
    (c := c) (K := K) (MK := MK) (ρ := ρ) (α := α) (q := q) (S'' := S'')
    (T := T) (u := u) (a := a) (ε := ε) (D := D) (C₀ := C₀) (η := η) (r := r)
    (k := k) (m := m) (J := J) (Z := Z) (z₀ := z₀) (s := s)
    hu1 hTu hM' hlam0 hβ0 hβlam hℓ0 hc hK hK' hMK0 hρ0 hα hα0 hq hS''1
    hu_bud ha hε hD1 hDup hC₀ℓ hDa hη hkK hk1 hm hmle hmε hbig h4lam hz₀ hz₀re hr0 hr hiso' hcount' hsd hds

  exact ⟨F₁, G₁, hF₁, hG₁, hΦ, fun weights hw hs hS =>
    hread weights hw hs (hS.trans hSbound)⟩

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weighted_rvm_readout_core
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weighted_discMoment_readout_rvm_explicit
