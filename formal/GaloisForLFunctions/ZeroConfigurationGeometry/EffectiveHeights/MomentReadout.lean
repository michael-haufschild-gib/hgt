import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.Heights

/-!
# Cluster moment readout at a specified height

The explicit logarithmic threshold fixes the bump order, isolation floor,
relative variation and tail. It yields the original moment error at every
height above `cameraMomentHeight`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

private theorem cameraMomentHeight_eq_of_parameters (J : ℕ)
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
theorem discMoment_readout_rvm_explicit (J : ℕ) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (_hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight J θ lam A S M' K' ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
        (∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) →
        ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₁ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G₁ ∧
          pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ ≠ 0 ∧
          ∀ j : ℕ, j ≤ J →
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
            ‖(Z.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁) -
                Z'.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁)) /
                ((-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀) -
              ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
              (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - θ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβlam : β ≤ lam := by rw [hβ]; linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 * π * A / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * growthRate ℓ * lam ^ 2 +
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M') := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith
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
  have hV0 : 0 < V := by rw [hV]; linarith [le_max_right (6 * cameraSlowConstant lam ℓ M') (4 * lam)]
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V) := ⟨_, rfl⟩
  have hheight := cameraMomentHeight_eq_of_parameters J
    hβ hℓ he hc hK hMK hρ hα hq hS'' hV hU₀
  intro T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  rw [hheight] at hT
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by rw [le_div_iff₀ h2π0]; linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith
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
    rw [hV] at hEV; linarith [le_max_right (6 * cameraSlowConstant lam ℓ M') (4 * lam)]
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith [Real.exp_pos u, Real.pi_gt_three]
  have hT1 : 1 ≤ T := (Real.one_le_exp hu0.le).trans hET
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  obtain ⟨hDa, hD1, hDup, hC₀ℓ⟩ :=
    rvm_density_facts hθ hlam hA hβ hℓ hu0 hu_lam ha hε hD hC₀
  have hD0 : 0 < D := by linarith
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
    rw [abs_le]; constructor <;> linarith
  have hiso' : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖ :=
    fun z hcz hzR => by rw [hη]; exact hiso z hcz (hsub_band z hzR)
  have hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
    intro s x y hxy hs
    have hc1 := hcount s x y hxy fun z hz =>
      ⟨(hs z hz).1, hsub_band z (hs z hz).2.1, (hs z hz).2.2⟩
    rw [← hC₀] at hc1
    have hDθ : θ / (2 * π) * u ≤ D := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    linarith
  have hSbound : S ≤ S'' := by rw [hS'']; exact le_max_left _ _
  exact rvm_readout_core (lam := lam) (β := β) (M' := M') (K' := K') (ℓ := ℓ)
    (c := c) (K := K) (MK := MK) (ρ := ρ) (α := α) (q := q) (S'' := S'')
    (T := T) (u := u) (a := a) (ε := ε) (D := D) (C₀ := C₀) (η := η) (r := r)
    (k := k) (m := m) (J := J) (Z := Z) (Z' := Z') (z₀ := z₀) (s := s)
    hu1 hTu hM' hlam0 hβ0 hβlam hℓ0 hc hK hK' hMK0 hρ0 hα hα0 hq hS''1
    hu_bud ha hε hD1 hDup hC₀ℓ hDa hη hkK hk1 hm hmle hmε hbig h4lam hZ hZ'
    (hStail.trans hSbound) hz₀ hz₀re hr0 hr hiso' hcount' hsd hds


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.discMoment_readout_rvm_explicit
