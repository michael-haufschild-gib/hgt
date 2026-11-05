import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.Heights

/-!
# Explicit heights for point isolation and multiplicity

Polynomial isolation, multiplicity readout, and reciprocal-logarithmic
localization hold at the finite expressions `cameraPointHeight` and
`cameraLogIsolationHeight`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

private theorem cameraPointHeight_eq_of_parameters
    {θ lam A S M β ℓ e c K MK ρ α q S'' U₀ : ℝ}
    (hβ : β = lam - θ / 2) (hℓ : ℓ = 2 * π * A / lam)
    (he : e = 6 * slackBound ℓ * (1 + slackBound ℓ))
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M))
    (hK : K = c / 2 + 2) (hMK : MK = e * lam + K + 2)
    (hρ : ρ = 8 * MK / β) (hα : α = 1 / (8 * MK * (1 + ρ)))
    (hq : q = max 0 (Real.log α⁻¹)) (hS'' : S'' = max S 1)
    (hU₀ : U₀ = max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) :
    cameraPointHeight θ lam A S M = 2 * π * Real.exp U₀ := by
  rw [hU₀, hS'', hq, hα, hρ, hMK, hK, hc, he, hℓ, hβ]
  simp only [cameraPointHeight, cameraBaseLogHeight, Nat.cast_zero, add_zero]

/-- Polynomially isolated points have a quantitative camera above the stated finite height. -/
theorem exists_subspacing_isolating_windows_explicit {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (_hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∀ T : ℝ, cameraPointHeight θ lam A S M ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          ∃ F G : ℝ → ℂ,
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
            pointImage F G z₀ ≠ 0 ∧
            (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
              pointImage F G z = 0) ∧
            ‖(Z.W F G - Z'.W F G) / pointImage F G z₀ - multDiff Z Z' z₀‖ ≤ 1 / 4 := by
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
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M) := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith only [hc0]
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = e * lam + K + 2 := ⟨_, rfl⟩
  have hMK0 : 0 < MK := by rw [hMK]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 8 * MK / β := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 1 / (8 * MK * (1 + ρ)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = max 0 (Real.log α⁻¹) := ⟨_, rfl⟩
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1) := ⟨_, rfl⟩
  have hheight := cameraPointHeight_eq_of_parameters
    hβ hℓ he hc hK hMK hρ hα hq hS'' hU₀
  intro T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hc_ne hiso
  rw [hheight] at hT
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by rw [le_div_iff₀ h2π0]; linarith only [hT]
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u := ((le_max_left _ _).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith only [hu1]
  have hu_lam : 2 * π / lam ≤ u := ((le_max_right _ _).trans (le_max_left _ _)).trans huU₀
  have hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u :=
    (le_max_right _ _).trans huU₀
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) hTdiv)]
    field_simp
  have hT0 : 0 < T := by rw [hTu]; positivity
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  obtain ⟨hDa, hD1, hDup, hC₀ℓ⟩ :=
    rvm_density_facts hθ hlam hA hβ hℓ hu0 hu_lam ha hε hD hC₀
  have hD0 : 0 < D := by linarith only [hD1]
  obtain ⟨η, hη⟩ : ∃ η, η = T ^ (-M) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hT0 _
  -- decay order `k = ⌈K u²⌉₊` and spline order `m = ⌈W⌉₊ + k`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈K * u ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + k := ⟨_, rfl⟩
  obtain ⟨hkK', hk1, hm', hmle, hmε⟩ :=
    rvm_order_facts (J := 0) (K' := 0) hK1 (le_refl 0) he0 hlam0 hβ0
      (by simpa only [add_zero, Nat.cast_zero] using hMK) hρ hu1 hε hDup hW0 hWle
      (by simpa only [add_zero] using hk) (by simpa only [Nat.add_zero] using hmdef)
  have hkK : K * u ^ 2 ≤ k := by simpa only [add_zero] using hkK'
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m := by
    simpa only [Nat.add_zero, hWdef] using hm'
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  have hsub_band : ∀ z : ℂ, |z.im - z₀.im| ≤ T / 4 → |z.im - T| ≤ T / 2 := fun z hz => by
    have h1 := abs_le.mp hz
    have h2 := abs_le.mp hz₀
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hiso' : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 → η ≤ ‖z - z₀‖ :=
    fun z hne hcz hzR => by rw [hη]; exact hiso z hne hcz (hsub_band z hzR)
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
        (div_le_div_of_nonneg_right (by linarith only [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    exact hc1.trans (add_le_add hmul (le_refl C₀))
  obtain ⟨F, G, hFw, hGw, _, hP0_ne, hnear, htail⟩ :=
    exists_isolating_window_pair_of_bump hD0 hη0 hε0 hDa hb hbs hb1 hk1 hm (C0 := 1) hbm
      (fun w => by rw [one_mul]; exact hb0 w) hZ hZ' (R := T / 4) (by positivity) hc_ne hiso'
      hcount'
  refine ⟨F, G, hFw, hGw, hP0_ne, hnear, ?_⟩
  have hSg0 : 0 ≤ ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by linarith only [Complex.normSq_nonneg (gammaOf z)])
  have hSbound : S ≤ S'' := by rw [hS'']; exact le_max_left _ _
  exact subspacing_camera_budget hu1 hTu hM hlam0 hβlam hℓ0 hc hK hMK0 hρ0 hα hα0 hq hS''1
    hu_bud ha hε hε0 hD1 hDup hC₀ℓ hη hη0 hkK hk1 hmle hmε hz₀ hSg0
    (hStail.trans hSbound) htail




/-- Mimics have equal multiplicities at every polynomially isolated point above the explicit height. -/
theorem multDiff_eq_zero_of_subspacing_isolated_explicit {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∀ T : ℝ, cameraPointHeight θ lam A S M ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          multDiff Z Z' z₀ = 0 := by
  have hwin := exists_subspacing_isolating_windows_explicit hθ hlam hA hS hM
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hiso
  by_contra hc
  obtain ⟨F, G, hFw, hGw, _, _, hle⟩ := hwin T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hc hiso
  rw [W_eq_of_mimic hZ hZ' hW hFw hGw, sub_self, zero_div, zero_sub, norm_neg] at hle
  linarith only [hle, one_le_norm_multDiff hc]


/-- Every remaining discrepancy has a polynomially close neighbour above the explicit height. -/
theorem exists_nearCollision_of_mimic_above_half_density_explicit {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∀ T : ℝ, cameraPointHeight θ lam A S M ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ ‖z - z₀‖ < T ^ (-M) := by
  have hexact := multDiff_eq_zero_of_subspacing_isolated_explicit hθ hlam hA hS hM
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hc
  by_contra hall
  push Not at hall
  exact hc (hexact T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hall)


/-- The point camera reads integer multiplicity to error one quarter at the explicit height. -/
theorem exists_window_pair_reads_mult_subspacing_explicit {θ lam A S M : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) :
    ∀ T : ℝ, cameraPointHeight θ lam A S M ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖Z.carrier.indicator (fun w => (Z.mult w : ℂ)) z‖ /
          (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ ∈ Z.carrier, |z₀.im - T| ≤ T / 4 →
          (∀ z ∈ Z.carrier, z ≠ z₀ → |z.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖z - z₀‖) →
          ∃ F G : ℝ → ℂ,
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
            pointImage F G z₀ ≠ 0 ∧
            Z.W F G ≠ 0 ∧
            (∀ z ∈ Z.carrier, z ≠ z₀ → |z.im - z₀.im| ≤ T / 4 → pointImage F G z = 0) ∧
            ‖Z.W F G / pointImage F G z₀ - (Z.mult z₀ : ℂ)‖ ≤ 1 / 4 := by
  have hwin := exists_subspacing_isolating_windows_explicit hθ hlam hA hS hM
  intro T hT Z hZ hStail hcount z₀ hz₀car hz₀ hiso
  have hmd : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 ↔ z ∈ Z.carrier := fun z => by
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz]
      exact ⟨fun _ => hz,
        fun _ => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Z.one_le_mult z hz))⟩
    · rw [Set.indicator_of_notMem hz]
      exact ⟨fun h => False.elim (h rfl), fun h => False.elim (hz h)⟩
  have hStail' : ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S := by
    simpa only [multDiff_emptyZeroConfig] using hStail
  obtain ⟨F, G, hFw, hGw, hP0, hnear, hle⟩ := hwin T hT Z emptyZeroConfig hZ
    temperedConfig_emptyZeroConfig hStail'
    (fun s x y hxy hs => hcount s x y hxy fun z hz =>
      ⟨(hmd z).mp (hs z hz).1, (hs z hz).2.1, (hs z hz).2.2⟩)
    z₀ hz₀ ((hmd z₀).mpr hz₀car)
    (fun z hne hcz hzR => hiso z ((hmd z).mp hcz) hne hzR)
  rw [W_emptyZeroConfig, sub_zero, multDiff_emptyZeroConfig, Set.indicator_of_mem hz₀car] at hle
  have hW_ne : Z.W F G ≠ 0 := by
    intro h0
    rw [h0, zero_div, zero_sub, norm_neg, Complex.norm_natCast] at hle
    have h1 : (1 : ℝ) ≤ (Z.mult z₀ : ℝ) := by exact_mod_cast Z.one_le_mult z₀ hz₀car
    linarith only [hle, h1]
  exact ⟨F, G, hFw, hGw, hP0, hW_ne,
    fun z hzc hne hzR => hnear z hne ((hmd z).mpr hzc) hzR, hle⟩


private theorem camera_inverse_height_le_log_scale {T δ : ℝ} (hδ : 0 < δ) (hT3 : 3 ≤ T)
    (hTδ : 2 / δ * max 0 (Real.log (2 / δ)) ≤ T) :
    T ^ (-1 : ℝ) ≤ δ / Real.log T := by
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogle : Real.log T ≤ δ * T := by
    have h := log_le_mul_add_log_inv hT0 (show 0 < δ / 2 by positivity)
    have hinv : (δ / 2)⁻¹ = 2 / δ := by field_simp
    rw [hinv] at h
    have h1 : Real.log (2 / δ) ≤ max 0 (Real.log (2 / δ)) := le_max_right _ _
    have h2 : max 0 (Real.log (2 / δ)) ≤ δ / 2 * T := by
      calc max 0 (Real.log (2 / δ)) = δ / 2 * (2 / δ * max 0 (Real.log (2 / δ))) := by field_simp
        _ ≤ δ / 2 * T := mul_le_mul_of_nonneg_left hTδ (by positivity)
    linarith
  rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hT0 hlog0]
  linarith

/-- Finite height for isolation at any prescribed fraction of reciprocal logarithmic spacing. -/
def cameraLogIsolationHeight (θ lam A S δ : ℝ) : ℝ :=
  max (cameraPointHeight θ lam A S 1) (2 / δ * max 0 (Real.log (2 / δ)))

/-- Isolation at any prescribed fraction of reciprocal logarithmic spacing determines multiplicity. -/
theorem multDiff_eq_zero_of_littleO_inv_log_isolated_explicit {θ lam A S δ : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∀ T : ℝ, cameraLogIsolationHeight θ lam A S δ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 →
          (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
            δ / Real.log T ≤ ‖z - z₀‖) →
          multDiff Z Z' z₀ = 0 := by
  have hexact := multDiff_eq_zero_of_subspacing_isolated_explicit hθ hlam hA hS
    (show (0 : ℝ) ≤ 1 by norm_num)
  have hT₁ := cameraPointHeight_ge θ lam A S 1
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hiso
  have hTp : cameraPointHeight θ lam A S 1 ≤ T := (le_max_left _ _).trans hT
  have hT3 : 3 ≤ T := by
    have : 2 * π * 1 ≤ 2 * π * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp zero_le_one) (by positivity)
    linarith only [this, Real.pi_gt_three, hT₁, hTp]
  have hle := camera_inverse_height_le_log_scale hδ hT3 ((le_max_right _ _).trans hT)
  exact hexact T ((le_max_left _ _).trans hT) Z Z' hZ hZ' hW hStail hcount z₀ hz₀
    fun z hne hcz hzR => hle.trans (hiso z hne hcz hzR)

/-- Every discrepancy has a neighbour within the prescribed reciprocal-logarithmic scale. -/
theorem exists_nearCollision_littleO_inv_log_explicit {θ lam A S δ : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∀ T : ℝ, cameraLogIsolationHeight θ lam A S δ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  have hexact := multDiff_eq_zero_of_littleO_inv_log_isolated_explicit hθ hlam hA hS hδ
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hc
  by_contra hall
  push Not at hall
  exact hc (hexact T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hall)


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_subspacing_isolating_windows_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.multDiff_eq_zero_of_subspacing_isolated_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_nearCollision_of_mimic_above_half_density_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_window_pair_reads_mult_subspacing_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.multDiff_eq_zero_of_littleO_inv_log_isolated_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_nearCollision_littleO_inv_log_explicit
