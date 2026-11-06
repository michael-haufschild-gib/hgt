import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowSolutionsAreBounded
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheRenewalReadoutHasAnExplicitModulus

/-!
# The sup bound of a window solution is explicit

`exists_ae_norm_le_of_window_equation` shows that a window solution is bounded, with a constant depending on
the solution. Knowing this, the double causal average can be split: the near part of the kernel sees the sup
norm with the small factor `V(ρ)`, the far part sees the `L¹` norm with the factor `1/ρ`. So a forcing dominated
by `C₀ + Σ_j c_j |u(x − ℓ_j)|`, with `K ≥ Σ_j c_j` and `K V(ρ) ≤ ½`, gives

  `‖u‖_∞ ≤ 2 (C₀ + (2/a) ‖u‖₁ + K ‖u‖₁ / ρ)` (`ae_norm_le_of_window_equation_explicit`).

The constant depends only on `C₀, K, a` and a bound for the `L¹` mass, so the Green operator of a window family is
uniformly bounded on `L^∞`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open _root_.RHTower CanonicalSystemOfTheWindowTower HTGeometry

local notation "v" => logarithmicCausalKernel
local notation "V" => logarithmicRenewalMass

/-- The solution is bounded by the double causal average of the forcing, with an explicit constant. -/
theorem ae_enorm_le_causalGamma_explicit (a : SuzukiPositiveAperture) (u g : suzukiApertureHilbert a)
    (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2)) :
    ∀ᵐ x ∂volume, ‖(u : RealLineL2) x‖ₑ ≤
      ENNReal.ofReal (2 / a.1) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) +
        causalGamma (fun z => ‖(g : RealLineL2) z‖ₑ) x := by
  obtain ⟨ur, hur⟩ : ∃ ur, ur = logarithmicApertureReflection a u := ⟨_, rfl⟩
  obtain ⟨gr, hgr⟩ : ∃ gr, gr = logarithmicApertureReflection a g := ⟨_, rfl⟩
  have huu : HasLogarithmicEnergy (ur : RealLineL2) := by
    rw [hur]
    exact hasLogarithmicEnergy_reflection hu
  have hse := logarithmic_interval_equation_reflection a u g hsolve
  rw [← hur, ← hgr] at hse
  have hL := ae_left_bound a u g hu hsolve
  have hR := ae_left_bound a ur gr huu hse
  have hgm : Measurable fun z => ‖(g : RealLineL2) z‖ₑ :=
    (Lp.stronglyMeasurable (g : RealLineL2)).measurable.enorm
  have hneg := fun {p : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), p x) =>
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  have hur' : ∀ᵐ x ∂(volume : Measure ℝ), (ur : RealLineL2) x = (u : RealLineL2) (-x) := by
    rw [hur]
    exact l2Reflection_ae (u : RealLineL2)
  have hgr' : ∀ᵐ x ∂(volume : Measure ℝ), ‖(gr : RealLineL2) x‖ₑ = ‖(g : RealLineL2) (-x)‖ₑ := by
    rw [hgr]
    exact (l2Reflection_ae (g : RealLineL2)).mono fun x hx => by
      change ‖l2Reflection (g : RealLineL2) x‖ₑ = _
      rw [hx]
  have hmass : ∫⁻ z, ‖(ur : RealLineL2) z‖ₑ = ∫⁻ z, ‖(u : RealLineL2) z‖ₑ := by
    calc
      _ = ∫⁻ z, ‖(u : RealLineL2) (-z)‖ₑ := lintegral_congr_ae (hur'.mono fun z hz => by rw [hz])
      _ = _ := lintegral_neg_eq_self (fun z => ‖(u : RealLineL2) z‖ₑ)
  have hsame : ∀ x, causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) =
      causalGamma (fun z => ‖(g : RealLineL2) z‖ₑ) x := by
    intro x
    have h1 : causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) ≤
        causalGamma (fun z => ‖(g : RealLineL2) (-z)‖ₑ) (-x) :=
      causalGamma_mono_ae (hgr'.mono fun z hz => hz.le) _
    have h2 : causalGamma (fun z => ‖(g : RealLineL2) (-z)‖ₑ) (-x) ≤
        causalGamma (fun z => ‖(gr : RealLineL2) z‖ₑ) (-x) :=
      causalGamma_mono_ae (hgr'.mono fun z hz => hz.ge) _
    rw [le_antisymm h1 h2]
    exact causalGamma_reflect hgm x
  have hconst : ENNReal.ofReal (2 / a.1 / 2) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) ≤
      ENNReal.ofReal (2 / a.1) * (∫⁻ z, ‖(u : RealLineL2) z‖ₑ) := by
    have hpos : 0 < 2 / a.1 := div_pos two_pos a.2
    have hle : 2 / a.1 / 2 ≤ 2 / a.1 := by linarith only [hpos]
    gcongr
  filter_upwards [hL, hneg hR, hneg hur'] with x h1 h2 h3
  rcases le_total x 0 with hx | hx
  · refine (h1 hx).trans ?_
    gcongr
  · have h4 := h2 (by linarith)
    rw [h3, neg_neg, hsame, hmass] at h4
    refine h4.trans ?_
    gcongr

/-- The forward causal average splits into a sup part with the factor `V(ρ)` and an `L¹` part with `1/ρ`. -/
theorem fwdAvg_causalDensity_le {h : ℝ → ℝ≥0∞} (hh : Measurable h) {S : ℝ≥0∞}
    (hS : ∀ᵐ y ∂volume, h y ≤ S) {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) :
    fwdAvg causalDensity h y ≤
      ENNReal.ofReal (V ρ) * S + ENNReal.ofReal (1 / ρ) * ∫⁻ z, h z := by
  have hK := measurable_causalDensity
  have hS' := (measurePreserving_add_left (volume : Measure ℝ) y).quasiMeasurePreserving.ae hS
  have hind : Measurable ((Ioc (0 : ℝ) ρ).indicator causalDensity) := hK.indicator measurableSet_Ioc
  have hpt : ∀ᵐ r ∂(volume : Measure ℝ), causalDensity r * h (y + r) ≤
      (Ioc (0 : ℝ) ρ).indicator causalDensity r * S + ENNReal.ofReal (1 / ρ) * h (y + r) := by
    filter_upwards [hS'] with r hr
    by_cases hr0 : r ≤ 0
    · rw [causalDensity_of_nonpos hr0, zero_mul]
      exact zero_le
    push Not at hr0
    by_cases hrρ : r ≤ ρ
    · rw [indicator_of_mem (show r ∈ Ioc (0 : ℝ) ρ from ⟨hr0, hrρ⟩)]
      calc
        _ ≤ causalDensity r * S := by gcongr
        _ ≤ _ := le_self_add
    · push Not at hrρ
      have hk : causalDensity r ≤ ENNReal.ofReal (1 / ρ) :=
        ENNReal.ofReal_le_ofReal ((antitoneOn_logarithmicCausalKernel hρ hr0 hrρ.le).trans
          (logarithmicCausalKernel_le_inv hρ))
      calc
        _ ≤ ENNReal.ofReal (1 / ρ) * h (y + r) := by gcongr
        _ ≤ _ := le_add_self
  have hmass : ∫⁻ r, (Ioc (0 : ℝ) ρ).indicator causalDensity r = ENNReal.ofReal (V ρ) := by
    rw [lintegral_indicator measurableSet_Ioc]
    change _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) ρ, v t)
    rw [ofReal_integral_eq_lintegral_ofReal logarithmicCausalKernel_mass_one.1.integrableOn
      (Eventually.of_forall logarithmicCausalKernel_nonneg)]
    rfl
  calc
    _ ≤ ∫⁻ r, ((Ioc (0 : ℝ) ρ).indicator causalDensity r * S +
        ENNReal.ofReal (1 / ρ) * h (y + r)) := lintegral_mono_ae hpt
    _ = (∫⁻ r, (Ioc (0 : ℝ) ρ).indicator causalDensity r) * S +
        ENNReal.ofReal (1 / ρ) * ∫⁻ r, h (y + r) := by
      rw [lintegral_add_left (hind.mul_const S), lintegral_mul_const _ hind,
        lintegral_const_mul (ENNReal.ofReal (1 / ρ))
          (show Measurable fun r => h (y + r) from hh.comp (measurable_const_add y))]
    _ = _ := by
      rw [hmass, lintegral_add_left_eq_self h y]

/-- The double causal average obeys the same split bound. -/
theorem causalGamma_le_split {h : ℝ → ℝ≥0∞} (hh : Measurable h) {S : ℝ≥0∞}
    (hS : ∀ᵐ y ∂volume, h y ≤ S) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    causalGamma h x ≤ ENNReal.ofReal (V ρ) * S + ENNReal.ofReal (1 / ρ) * ∫⁻ z, h z := by
  have hK := measurable_causalDensity
  have hK1 := lintegral_causalDensity
  unfold causalGamma bwdAvg
  calc
    _ ≤ ∫⁻ t, causalDensity t * (ENNReal.ofReal (V ρ) * S + ENNReal.ofReal (1 / ρ) * ∫⁻ z, h z) :=
      lintegral_mono fun t => by
        gcongr
        exact fwdAvg_causalDensity_le hh hS hρ _
    _ = _ := by
      rw [lintegral_mul_const _ hK, hK1, one_mul]

/-- **The explicit sup bound of a window solution.** -/
theorem ae_norm_le_of_window_equation_explicit {ι : Type*} (a : SuzukiPositiveAperture)
    (u g : suzukiApertureHilbert a) (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ f : suzukiApertureHilbert a, HasLogarithmicEnergy (f : RealLineL2) →
      logarithmicFullForm (f : RealLineL2) (u : RealLineL2) =
        inner ℂ (f : RealLineL2) (g : RealLineL2))
    (J : Finset ι) {c : ι → ℝ} (ℓ : ι → ℝ) (hc : ∀ j, 0 ≤ c j) {C₀ K L ρ : ℝ} (hC₀ : 0 ≤ C₀)
    (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (hK : ∑ j ∈ J, c j ≤ K) (hρ : 0 < ρ) (hsmall : K * V ρ ≤ 1 / 2)
    (hL : ∫⁻ z, ‖(u : RealLineL2) z‖ₑ ≤ ENNReal.ofReal L)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤
      C₀ + ∑ j ∈ J, c j * ‖(u : RealLineL2) (x - ℓ j)‖) :
    ∀ᵐ x ∂volume, ‖(u : RealLineL2) x‖ ≤ 2 * (C₀ + 2 / a.1 * L + K * L / ρ) := by
  obtain ⟨C, hC0, hCb⟩ := exists_ae_norm_le_of_window_equation a u g hu hsolve J ℓ hc hC₀ hg
  obtain ⟨w, hw⟩ : ∃ w, w = fun x => ‖(u : RealLineL2) x‖ₑ := ⟨_, rfl⟩
  have hwm : Measurable w := by
    rw [hw]
    exact (Lp.stronglyMeasurable (u : RealLineL2)).measurable.enorm
  obtain ⟨S, hSd⟩ : ∃ S, S = essSup w volume := ⟨_, rfl⟩
  have hwS : ∀ᵐ y ∂volume, w y ≤ S := by
    rw [hSd]
    exact ENNReal.ae_le_essSup w
  have hSfin : S ≠ ∞ := by
    have hle : S ≤ ENNReal.ofReal C := by
      rw [hSd]
      refine essSup_le_of_ae_le _ (hCb.mono fun x hx => ?_)
      rw [hw]
      change ‖(u : RealLineL2) x‖ₑ ≤ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx
    exact (hle.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ j ∈ J, ENNReal.ofReal (c j) := ⟨_, rfl⟩
  have hAK : A ≤ ENNReal.ofReal K := by
    rw [hA, ← ENNReal.ofReal_sum_of_nonneg fun j _ => hc j]
    exact ENNReal.ofReal_le_ofReal hK
  obtain ⟨T, hT⟩ : ∃ T, T = transSum J (fun j => ENNReal.ofReal (c j)) ℓ w := ⟨_, rfl⟩
  have hTm : Measurable T := by
    rw [hT]
    exact measurable_transSum _ _ _ hwm
  have hTS : ∀ᵐ y ∂volume, T y ≤ A * S := by
    have hall : ∀ᵐ y ∂(volume : Measure ℝ), ∀ j ∈ J, w (y - ℓ j) ≤ S :=
      (Filter.eventually_all_finset J).mpr fun j _ =>
        (measurePreserving_sub_right (volume : Measure ℝ) (ℓ j)).quasiMeasurePreserving.ae hwS
    filter_upwards [hall] with y hy
    rw [hT, hA, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => by
      gcongr
      exact hy j hj
  have hTI : ∫⁻ y, T y = A * ∫⁻ y, w y := by
    rw [hT, hA]
    exact lintegral_transSum _ _ _ hwm
  have hdom : ∀ᵐ y ∂(volume : Measure ℝ), ‖(g : RealLineL2) y‖ₑ ≤ ENNReal.ofReal C₀ + T y := by
    filter_upwards [hg] with x hx
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add hC₀ (Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (norm_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hc j) (norm_nonneg _)]
    congr 1
    rw [hT]
    unfold transSum
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hc j), ofReal_norm, hw]
  have hK₁ := measurable_causalDensity
  have hK1 := lintegral_causalDensity
  have hγ (x : ℝ) : causalGamma (fun y => ENNReal.ofReal C₀ + T y) x =
      ENNReal.ofReal C₀ + causalGamma T x := by
    unfold causalGamma
    have he : fwdAvg causalDensity (fun y => ENNReal.ofReal C₀ + T y) =
        fun y => ENNReal.ofReal C₀ + fwdAvg causalDensity T y := by
      funext y
      rw [fwdAvg_add_const hK₁, hK1, one_mul]
    rw [he, bwdAvg_add_const hK₁, hK1, one_mul]
  -- The pointwise inequality in terms of `S`.
  have hpoint : ∀ᵐ x ∂volume, w x ≤
      ENNReal.ofReal (2 / a.1) * (∫⁻ z, w z) + (ENNReal.ofReal C₀ +
        (ENNReal.ofReal (V ρ) * (A * S) + ENNReal.ofReal (1 / ρ) * (A * ∫⁻ z, w z))) := by
    filter_upwards [ae_enorm_le_causalGamma_explicit a u g hu hsolve] with x hx
    have h1 := causalGamma_mono_ae hdom x
    rw [hγ] at h1
    have h2 := causalGamma_le_split hTm hTS hρ x
    rw [hTI] at h2
    rw [hw]
    simp only []
    refine hx.trans ?_
    rw [← hw]
    gcongr
    exact h1.trans (by gcongr)
  have hS_le : S ≤ ENNReal.ofReal (2 / a.1) * (∫⁻ z, w z) + (ENNReal.ofReal C₀ +
        (ENNReal.ofReal (V ρ) * (A * S) + ENNReal.ofReal (1 / ρ) * (A * ∫⁻ z, w z))) := by
    rw [hSd]
    rw [← hSd]
    exact hSd ▸ essSup_le_of_ae_le _ (hpoint.mono fun x hx => by rw [← hSd] at *; exact hx)
  -- Pass to real numbers.
  obtain ⟨s, hs⟩ : ∃ s, s = S.toReal := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ ENNReal.toReal_nonneg
  have hSs : S = ENNReal.ofReal s := by
    rw [hs, ENNReal.ofReal_toReal hSfin]
  have hLw : ∫⁻ z, w z ≤ ENNReal.ofReal L := by
    rw [hw]
    exact hL
  have hdiv : 0 ≤ 2 / a.1 := div_nonneg zero_le_two a.2.le
  have hV0 := logarithmicRenewalMass_nonneg ρ
  have hinv : 0 ≤ 1 / ρ := (one_div_pos.mpr hρ).le
  have hbound : S ≤ ENNReal.ofReal (2 / a.1 * L + (C₀ + (V ρ * (K * s) + 1 / ρ * (K * L)))) := by
    refine hS_le.trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hC₀ (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hdiv,
      ENNReal.ofReal_mul hV0, ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hinv, ENNReal.ofReal_mul hK0]
    gcongr
    · rw [hSs]
  have hreal : s ≤ 2 / a.1 * L + (C₀ + (V ρ * (K * s) + 1 / ρ * (K * L))) := by
    have hnn : 0 ≤ 2 / a.1 * L + (C₀ + (V ρ * (K * s) + 1 / ρ * (K * L))) := by positivity
    have h := ENNReal.toReal_le_of_le_ofReal hnn hbound
    rwa [← hs] at h
  have habs : V ρ * (K * s) ≤ 1 / 2 * s := by
    have := mul_le_mul_of_nonneg_right hsmall hs0
    linarith only [this]
  have hfinal : s ≤ 2 * (C₀ + 2 / a.1 * L + K * L / ρ) := by
    have he : 1 / ρ * (K * L) = K * L / ρ := by ring
    rw [he] at hreal
    linarith only [hreal, habs]
  filter_upwards [hwS] with x hx
  have hx' : ‖(u : RealLineL2) x‖ₑ ≤ ENNReal.ofReal s := by
    rw [← hSs]
    rw [hw] at hx
    exact hx
  rw [← ofReal_norm] at hx'
  exact ((ENNReal.ofReal_le_ofReal_iff hs0).mp hx').trans hfinal

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
