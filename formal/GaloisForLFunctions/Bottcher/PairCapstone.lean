/-
# The disconnected pair capstone (level-compatible case)

`NoRelation ℂ(z) φ_{c₁} φ_{c₂}` for escape parameters whose geometry is level-compatible: below a
`(c₁,c₂)`-threshold `cap`, the first parameter's basin sits above the second's critical level.
Then the whole `c₁`-tower domain embeds in the `c₂`-band, where the band-surjective section
inverse IS the extended second Böttcher coordinate: `GBExt := S₂.inv` glued with the crude far
coordinate.  Everything else — radicand, loops, transcendence — is the banked machinery.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherTowerData
import GaloisForLFunctions.Bottcher.PairMonodromy

open Complex Set Filter Metric

namespace Bottcher

set_option maxHeartbeats 1600000 in
/-- **The pair tower data.**  Beyond an explicit threshold, level compatibility supplies the
full `towerdataF` package for the genuine pair of Böttcher germs on a common far domain:
`F₁` and the odd loops from `c₁`'s dyadic tower, `GBExt` from `c₂`'s band inverse. -/
theorem bottcher_towerDataF_pair (c₁ c₂ : ℂ)
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc₂ : (0:ℂ) ∉ filledJulia c₂) :
    ∃ cap₀ : ℝ, ∀ cap : ℝ, cap₀ ≤ cap →
    (∀ z : ℂ, 0 < greenFunctionDyn c₁ z → greenFunctionDyn c₁ z ≤ cap →
      (∀ n : ℕ, (quadratic c₁)^[n] z ≠ 0) →
      2 * greenFunctionDyn c₂ 0 < greenFunctionDyn c₂ z) →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U.Infinite ∧
      ∃ (a₁ a₂ : analyticSubring U),
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₁)) = (a₁ : Filter.Germ (𝓟 U) ℂ) ∧
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
      (∀ z ∈ U, bottcherFarBound c₂ hc₂ < ‖z‖) ∧
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt GBExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₁ ^ (2 ^ k) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) := by
  classical
  set h₂ : ℝ := greenFunctionDyn c₂ 0 with hh₂def
  have hh₂0 : 0 < h₂ := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c₂ 0) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c₂ 0).mp h1.symm) hc₂
  obtain ⟨Ra₂, Rinj₂, hRa₂1, hRa₂G, hInj₂, _hRinj₂bd, hanchor₂⟩ := exists_tower_anchor c₂
  -- the threshold absorbing every internal choice
  set cap₀ : ℝ := max (max (bottcherBallBound c₁ + 1) (Real.log Ra₂ + 3))
    (max (max (Real.log (max 2 ‖c₁‖) + 2) (Real.log (max 2 ‖c₂‖) + 2))
      (max (Real.log (max (bottcherFarBound c₁ hc₁) (bottcherFarBound c₂ hc₂)) + 2)
        (max 10 (2 * greenFunctionDyn c₂ 0 + 3))))
    with hcap₀def
  refine ⟨cap₀, ?_⟩
  intro cap hcap hlevel
  set cut : ℝ := Real.exp (cap - 1) with hcutdef
  -- generous facts about the threshold
  have hcap10 : (10:ℝ) ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hcap2h₂ : 2 * h₂ + 3 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def, hh₂def]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hcapBB : bottcherBallBound c₁ + 1 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_left (le_max_left _ _)
  have hcapRa₂ : Real.log Ra₂ + 3 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_left (le_max_right _ _)
  have hcapc₁ : Real.log (max 2 ‖c₁‖) + 2 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hcapc₂ : Real.log (max 2 ‖c₂‖) + 2 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hcapFB : Real.log (max (bottcherFarBound c₁ hc₁) (bottcherFarBound c₂ hc₂)) + 2 ≤ cap := by
    refine le_trans ?_ hcap
    rw [hcap₀def]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  -- the cut clears both crude thresholds and both far bounds
  have hcutc₂ : max 2 ‖c₂‖ < cut := by
    rw [hcutdef]
    calc max 2 ‖c₂‖ = Real.exp (Real.log (max 2 ‖c₂‖)) := by
          rw [Real.exp_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _))]
      _ < Real.exp (cap - 1) := Real.exp_lt_exp.mpr (by linarith)
  have hcutc₁ : max 2 ‖c₁‖ < cut := by
    rw [hcutdef]
    calc max 2 ‖c₁‖ = Real.exp (Real.log (max 2 ‖c₁‖)) := by
          rw [Real.exp_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _))]
      _ < Real.exp (cap - 1) := Real.exp_lt_exp.mpr (by linarith)
  have hFBpos₁ : 1 < bottcherFarBound c₁ hc₁ := one_lt_bottcherFarBound c₁ hc₁
  have hFBpos₂ : 1 < bottcherFarBound c₂ hc₂ := one_lt_bottcherFarBound c₂ hc₂
  have hcutFB : max (bottcherFarBound c₁ hc₁) (bottcherFarBound c₂ hc₂) < cut := by
    rw [hcutdef]
    calc max (bottcherFarBound c₁ hc₁) (bottcherFarBound c₂ hc₂)
        = Real.exp (Real.log (max (bottcherFarBound c₁ hc₁) (bottcherFarBound c₂ hc₂))) := by
          rw [Real.exp_log (lt_trans one_pos (lt_of_lt_of_le hFBpos₁ (le_max_left _ _)))]
      _ < Real.exp (cap - 1) := Real.exp_lt_exp.mpr (by linarith)
  -- the common far domain
  set BU : ℝ := cut + 1 with hBUdef
  set U : Set ℂ := annulusSet BU (2 * BU) with hUdef
  have hcutpos : (0:ℝ) < cut := Real.exp_pos _
  have hBU1 : 1 < BU := by
    rw [hBUdef]
    linarith
  have hBU2 : BU < 2 * BU := by linarith
  have hUo : IsOpen U := isOpen_annulusSet _ _
  have hUconn : IsConnected U := isConnected_annulus (by linarith) hBU2
  have hUne : U.Nonempty := hUconn.nonempty
  have hUinf : U.Infinite := by
    have h1 : (Set.Ioo BU (2 * BU)).Infinite := Set.Ioo_infinite hBU2
    have h2 : ((fun t : ℝ => (t : ℂ)) '' Set.Ioo BU (2 * BU)).Infinite :=
      h1.image (fun a _ b _ hab => by exact_mod_cast hab)
    apply h2.mono
    rintro z ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have htpos : (0:ℝ) < t := by linarith
    constructor <;> simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    · exact ht1
    · exact ht2
  have hUfar₁ : ∀ z ∈ U, bottcherFarBound c₁ hc₁ < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have h2 : bottcherFarBound c₁ hc₁ ≤ max (bottcherFarBound c₁ hc₁)
        (bottcherFarBound c₂ hc₂) := le_max_left _ _
    linarith [hcutFB]
  have hUfar₂ : ∀ z ∈ U, bottcherFarBound c₂ hc₂ < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have h2 : bottcherFarBound c₂ hc₂ ≤ max (bottcherFarBound c₁ hc₁)
        (bottcherFarBound c₂ hc₂) := le_max_right _ _
    linarith [hcutFB]
  have hUcut : ∀ z ∈ U, cut < ‖z‖ := by
    rintro z ⟨h1, _⟩
    linarith
  -- the first coordinate's tower data on U
  obtain ⟨a₁, ha₁, hdata₁⟩ := bottcherFarBound_spec c₁ hc₁ U hUo hUconn.isPreconnected
    hUne hUinf hUfar₁
  -- the second coordinate's germ on U
  have hUesc₂ : U ⊆ escapeOpen c₂ := by
    rintro z hz
    show max 2 ‖c₂‖ < ‖z‖
    have := hUcut z hz
    linarith [hcutc₂]
  have hφ₂anU : AnalyticOnNhd ℂ (bottcherCoord c₂) U := fun z hz =>
    (differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂) z (hUesc₂ hz)
  set a₂ : analyticSubring U :=
    ⟨Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂), bottcherCoord c₂, hφ₂anU, rfl⟩
    with ha₂def
  -- the second coordinate's band tower
  obtain ⟨rlo₂, R₀₂, hrlo₂1, hrlo₂Ra, hRa₂R₀, hrlo₂sq, hM₂R₀, hlow₂, hhi₂, S₂, hfar₂,
    hbandsurj₂⟩ :=
    exists_tower_deep_of_anchor c₂ (show (0:ℝ) < h₂ from hh₂0)
      (Real.exp (max cap (bottcherBallBound c₂) + 3)) hRa₂1 hRa₂G hanchor₂
  have hR₀₂big : max cap (bottcherBallBound c₂) + 3 < Real.log R₀₂ := by
    have h1 : Real.exp (max cap (bottcherBallBound c₂) + 3) < R₀₂ := hM₂R₀
    have h2 := Real.log_lt_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hrlo₂2h : Real.log rlo₂ < 2 * h₂ := by
    rw [hh₂def] at hhi₂ ⊢
    linarith
  refine ⟨U, hUo, hUconn.isPreconnected, hUne, hUinf, a₁, a₂, ha₁, rfl, hUfar₂, ?_⟩
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae,
    hrad, hExtpos, hExtorb, hloops⟩ := hdata₁ d
  -- the glued second coordinate on the extended domain
  set GBExtF : ℂ → ℂ := fun z =>
    if cut < ‖z‖ then bottcherCoord c₂ z else S₂.inv z with hGBdef
  -- band membership for the bounded part
  have hbandmem : ∀ z ∈ Ext, ‖z‖ ≤ 4 * cut →
      z ∈ S₂.T '' annulusSet rlo₂ R₀₂ := by
    intro z hz hznorm
    apply hbandsurj₂
    · -- the level exceeds the band bottom
      rcases le_or_gt ‖z‖ cut with hcase | hcase
      · -- bounded part: the level hypothesis fires
        have hG₁pos : 0 < greenFunctionDyn c₁ z := hExtpos z hz
        have hG₁cap : greenFunctionDyn c₁ z ≤ cap := by
          by_contra hcon
          push Not at hcon
          have h1 : bottcherBallBound c₁ < greenFunctionDyn c₁ z := by linarith
          obtain ⟨hfar1, hlog1⟩ := far_of_green_gt_ballBound c₁ h1
          have h2 : cap - 1 < Real.log ‖z‖ := by linarith
          have h3 : cut < ‖z‖ := by
            rw [hcutdef]
            calc Real.exp (cap - 1) < Real.exp (Real.log ‖z‖) := Real.exp_lt_exp.mpr h2
              _ = ‖z‖ := Real.exp_log (by
                  have := lt_of_le_of_lt (le_max_left 2 ‖c₁‖) hfar1
                  linarith)
          linarith
        have h4 := hlevel z hG₁pos hG₁cap (hExtorb z hz)
        linarith [hrlo₂2h]
      · -- collar part: the crude comparison fires
        have hesc₂ : max 2 ‖c₂‖ < ‖z‖ := lt_trans hcutc₂ hcase
        have hzK₂ : z ∉ filledJulia c₂ := not_mem_filledJulia
          (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂))
          (lt_of_le_of_lt (le_max_left _ _) hesc₂)
        have habs := greenLimit_abs_sub_log
          (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂))
          (lt_of_le_of_lt (le_max_left _ _) hesc₂)
        have hval : greenFunctionDyn c₂ z = greenLimit c₂ z := by
          unfold greenFunctionDyn
          rw [if_neg hzK₂]
        have hcorr : 2 * ‖c₂‖ / ‖z‖ ^ 2 ≤ 1 := by
          have h3 : ‖c₂‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂)
          have h3' : (2:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hesc₂
          rw [div_le_one (by nlinarith)]
          nlinarith
        have hlow : Real.log ‖z‖ - 1 ≤ greenFunctionDyn c₂ z := by
          rw [hval]
          have h4 := abs_le.mp habs
          linarith [h4.1]
        have h5 : cap - 1 < Real.log ‖z‖ := by
          rw [hcutdef] at hcase
          have h6 := Real.log_lt_log (Real.exp_pos _) hcase
          rwa [Real.log_exp] at h6
        have h7 : Real.log rlo₂ < 2 * h₂ + 1 := by linarith [hrlo₂2h]
        linarith
    · -- the level is below the band top
      rcases le_or_gt ‖z‖ (max 2 ‖c₂‖) with hcase | hcase
      · have h1 := le_bottcherBallBound c₂ hcase
        have h2 : bottcherBallBound c₂ ≤ max cap (bottcherBallBound c₂) := le_max_right _ _
        linarith [hR₀₂big]
      · have hcrude := greenFunctionDyn_le_crude
          (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hcase))
          (lt_of_le_of_lt (le_max_left _ _) hcase)
        have h3 : Real.log ‖z‖ ≤ Real.log (4 * cut) := by
          apply Real.log_le_log (by
            have := lt_of_le_of_lt (le_max_left 2 ‖c₂‖) hcase
            linarith) hznorm
        have h4 : Real.log (4 * cut) = Real.log 4 + (cap - 1) := by
          rw [hcutdef, Real.log_mul (by norm_num) (by positivity), Real.log_exp]
        have h5 : Real.log 4 ≤ 2 := by
          have h6 : (4:ℝ) ≤ Real.exp 2 := by
            have h7 : (2:ℝ) ≤ Real.exp 1 := by
              nlinarith [Real.add_one_le_exp (1:ℝ)]
            have h8 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
              rw [← Real.exp_add]
              norm_num
            nlinarith [Real.exp_pos (1:ℝ)]
          calc Real.log 4 ≤ Real.log (Real.exp 2) :=
                Real.log_le_log (by norm_num) h6
            _ = 2 := Real.log_exp 2
        have h8 : cap ≤ max cap (bottcherBallBound c₂) := le_max_left _ _
        linarith [hR₀₂big]
  -- the collar agreement
  have hagree : ∀ z ∈ Ext, cut < ‖z‖ → ‖z‖ ≤ 4 * cut →
      bottcherCoord c₂ z = S₂.inv z := by
    intro z hz hzlo hzhi
    have hmem := hbandmem z hz hzhi
    have hw := S₂.inv_mem hmem
    have hTw : S₂.T (S₂.inv z) = z := S₂.inv_right hmem
    -- the fibre coordinate is in the far band of the second anchor
    have hwlog : Real.log ‖S₂.inv z‖ = greenFunctionDyn c₂ z := S₂.norm_inv hmem
    have hG₂z : Real.log Ra₂ + 1 < greenFunctionDyn c₂ z := by
      -- crude lower bound beyond the cut
      have hesc₂ : max 2 ‖c₂‖ < ‖z‖ := lt_trans hcutc₂ hzlo
      have hzK₂ : z ∉ filledJulia c₂ := not_mem_filledJulia
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂))
        (lt_of_le_of_lt (le_max_left _ _) hesc₂)
      have habs := greenLimit_abs_sub_log
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂))
        (lt_of_le_of_lt (le_max_left _ _) hesc₂)
      have hval : greenFunctionDyn c₂ z = greenLimit c₂ z := by
        unfold greenFunctionDyn
        rw [if_neg hzK₂]
      have hcorr : 2 * ‖c₂‖ / ‖z‖ ^ 2 ≤ 1 := by
        have h3 : ‖c₂‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc₂)
        have h3' : (2:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hesc₂
        rw [div_le_one (by nlinarith)]
        nlinarith
      have hlow : Real.log ‖z‖ - 1 ≤ greenFunctionDyn c₂ z := by
        rw [hval]
        have h4 := abs_le.mp habs
        linarith [h4.1]
      have h5 : cap - 1 < Real.log ‖z‖ := by
        rw [hcutdef] at hzlo
        have h6 := Real.log_lt_log (Real.exp_pos _) hzlo
        rwa [Real.log_exp] at h6
      linarith
    have hwRa : Ra₂ < ‖S₂.inv z‖ := by
      calc Ra₂ = Real.exp (Real.log Ra₂) := (Real.exp_log (by linarith)).symm
        _ < Real.exp (Real.log ‖S₂.inv z‖) := by
            apply Real.exp_lt_exp.mpr
            rw [hwlog]
            linarith
        _ = ‖S₂.inv z‖ := Real.exp_log (by
            have := hw.1
            linarith)
    have hid := (hfar₂ (S₂.inv z) hwRa hw.2).1
    rw [hTw] at hid
    exact hid
  -- analyticity of the glued coordinate
  have hGBan : AnalyticOnNhd ℂ GBExtF Ext := by
    intro z hz
    rcases lt_trichotomy ‖z‖ cut with hcase | hcase | hcase
    · -- bounded: agree with the band inverse near z
      have hev : GBExtF =ᶠ[nhds z] S₂.inv := by
        have hopen : IsOpen {w : ℂ | ‖w‖ < cut} :=
          isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds hcase] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = S₂.inv w
        rw [if_neg (by push Not; exact le_of_lt hw)]
      exact ((S₂.inv_analytic z (hbandmem z hz (by linarith))).congr hev.symm)
    · -- boundary: everything near agrees with the band inverse
      have hev : GBExtF =ᶠ[nhds z] S₂.inv := by
        have hopen : IsOpen ({w : ℂ | ‖w‖ < 2 * cut} ∩ Ext) := by
          apply IsOpen.inter _ hExto
          exact isOpen_lt continuous_norm continuous_const
        have hzmem : z ∈ {w : ℂ | ‖w‖ < 2 * cut} ∩ Ext := by
          constructor
          · show ‖z‖ < 2 * cut
            rw [hcase]
            linarith
          · exact hz
        filter_upwards [hopen.mem_nhds hzmem] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = S₂.inv w
        by_cases hf : cut < ‖w‖
        · rw [if_pos hf]
          exact hagree w hw.2 hf (by
            have h9 : ‖w‖ < 2 * cut := hw.1
            linarith)
        · rw [if_neg hf]
      have hzband : z ∈ S₂.T '' annulusSet rlo₂ R₀₂ := by
        apply hbandmem z hz
        rw [hcase]
        linarith
      exact ((S₂.inv_analytic z hzband).congr hev.symm)
    · -- far: agree with the crude coordinate near z
      have hev : GBExtF =ᶠ[nhds z] bottcherCoord c₂ := by
        have hopen : IsOpen {w : ℂ | cut < ‖w‖} :=
          isOpen_lt continuous_const continuous_norm
        filter_upwards [hopen.mem_nhds hcase] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = bottcherCoord c₂ w
        rw [if_pos hw]
      have hφan : AnalyticAt ℂ (bottcherCoord c₂) z := by
        apply (differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂)
        show max 2 ‖c₂‖ < ‖z‖
        linarith [hcutc₂]
      exact (hφan.congr hev.symm)
  set aGB : analyticSubring Ext :=
    ⟨Filter.Germ.coeRingHom (𝓟 Ext) GBExtF, GBExtF, hGBan, rfl⟩ with haGBdef
  -- the restriction clause for the second germ
  have hGBrestrict : restrictAnalytic hUExt aGB = a₂ := by
    apply Subtype.ext
    have hL : ((restrictAnalytic hUExt aGB : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) GBExtF := by
      show ((aGB : Filter.Germ (𝓟 Ext) ℂ).compTendsto id
        (Filter.tendsto_principal_principal.mpr (fun x hx => hUExt hx))) = _
      have h1 : (aGB : Filter.Germ (𝓟 Ext) ℂ)
          = Filter.Germ.coeRingHom (𝓟 Ext) GBExtF := rfl
      rw [h1]
      show ((GBExtF : Filter.Germ (𝓟 Ext) ℂ).compTendsto id _) = (GBExtF : Filter.Germ (𝓟 U) ℂ)
      rw [Filter.Germ.coe_compTendsto]
      rfl
    rw [hL]
    have hR : ((a₂ : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂) := rfl
    rw [hR]
    have hev : (GBExtF : ℂ → ℂ) =ᶠ[𝓟 U] (bottcherCoord c₂) := by
      apply Filter.eventually_principal.mpr
      intro z hz
      show (if cut < ‖z‖ then bottcherCoord c₂ z else S₂.inv z) = bottcherCoord c₂ z
      rw [if_pos (hUcut z hz)]
    exact Filter.Germ.coe_eq.mpr hev
  exact ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, aGB, k, hk1, hdk, hFan, hFne, hae,
    hrad, hGBrestrict, hloops⟩

end Bottcher

namespace Bottcher

/-- **[q62, disconnected pair, level-compatible case.]**  For escape parameters `c₁, c₂` whose
geometry is level-compatible beyond the explicit threshold — every NON-PRECRITICAL point of the
first basin's bounded window sits above the second's critical Green level — the two genuine
inverse Böttcher germs are algebraically independent over `ℂ(z)` on a common far domain: the
first coordinate's dyadic radical tower carries the second's extended coordinate, and the Kummer
machinery closes.  The precritical exemption is what makes the hypothesis satisfiable (the
critical point `0` itself always lies in the window); its satisfiability locus is the geometric
condition that `K_{c₂} ∖ K_{c₁}`-points in the window are precritical for `c₁` or absent.
Axiom-clean, no sorries anywhere below. -/
theorem q62_pair_of_level_compatible (c₁ c₂ : ℂ)
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc₂ : (0:ℂ) ∉ filledJulia c₂) :
    ∃ cap₀ : ℝ, ∀ cap : ℝ, cap₀ ≤ cap →
    (∀ z : ℂ, 0 < greenFunctionDyn c₁ z → greenFunctionDyn c₁ z ≤ cap →
      (∀ n : ℕ, (quadratic c₁)^[n] z ≠ 0) →
      2 * greenFunctionDyn c₂ 0 < greenFunctionDyn c₂ z) →
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (a₁ a₂ : analyticSubring U),
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₁)) = (a₁ : Filter.Germ (𝓟 U) ℂ) ∧
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
      (haveI := isDomain_analyticSubring U hUo hUc hUne
       haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
       NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
         (algebraMap (analyticSubring U) (meroField U) a₂)) := by
  obtain ⟨cap₀, hmain⟩ := bottcher_towerDataF_pair c₁ c₂ hc₁ hc₂
  refine ⟨cap₀, ?_⟩
  intro cap hcap hlevel
  obtain ⟨U, hUo, hUc, hUne, hUinf, a₁, a₂, ha₁, ha₂, hUfar₂, hdata⟩ := hmain cap hcap hlevel
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine ⟨U, hUo, hUc, hUne, hUinf, a₁, a₂, ha₁, ha₂, ?_⟩
  apply q62_pair_disconnected_of_towerdataF hc₂ hUo hUc hUne hUinf hUfar₂ a₁ a₂ ha₂ ?_ hdata
  -- the first germ is nonzero: the Böttcher coordinate never vanishes
  intro hzero
  have h1 : a₁ = 0 := by
    have hinj := IsFractionRing.injective (analyticSubring U) (meroField U)
    apply hinj
    rw [hzero, map_zero]
  have h2 : (a₁ : Filter.Germ (𝓟 U) ℂ) = 0 := by rw [h1]; rfl
  rw [← ha₁] at h2
  have h3 : (bottcherCoord c₁ : ℂ → ℂ) =ᶠ[𝓟 U] (fun _ => (0:ℂ)) :=
    Filter.Germ.coe_eq.mp h2
  obtain ⟨z, hz⟩ := hUne
  exact bottcherCoord_ne_zero c₁ z ((Filter.eventually_principal.mp h3) z hz)

end Bottcher

namespace Bottcher

/-- **The glued second coordinate, abstractly.**  Given a band tower for `c₂` whose image
covers the bounded window and whose fibres are far over the collar, the crude coordinate and the
band inverse glue to a single analytic extension of `φ_{c₂}` on any domain in the window. -/
theorem exists_GBExt_glue (c₂ : ℂ) {rlo₂ R₀₂ Ra₂ Rinj₂ : ℝ} (hrlo₂1 : 1 < rlo₂)
    (S₂ : TowerSection c₂ rlo₂ R₀₂)
    (hfar₂ : ∀ w : ℂ, Ra₂ < ‖w‖ → ‖w‖ < R₀₂ →
      bottcherCoord c₂ (S₂.T w) = w ∧ S₂.T w ∈ escapeOpen c₂ ∧ Rinj₂ < ‖S₂.T w‖)
    {cut : ℝ} (hcutc₂ : max 2 ‖c₂‖ < cut)
    {Ext : Set ℂ} (hExto : IsOpen Ext)
    (hbandmem : ∀ z ∈ Ext, ‖z‖ ≤ 4 * cut → z ∈ S₂.T '' annulusSet rlo₂ R₀₂)
    (hcollarG : ∀ z ∈ Ext, cut < ‖z‖ → ‖z‖ ≤ 4 * cut →
      Real.log Ra₂ < greenFunctionDyn c₂ z) :
    ∃ GBExtF : ℂ → ℂ, AnalyticOnNhd ℂ GBExtF Ext ∧
      (∀ z : ℂ, cut < ‖z‖ → GBExtF z = bottcherCoord c₂ z) := by
  classical
  have hcutpos : (0:ℝ) < cut := lt_trans (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
    hcutc₂
  set GBExtF : ℂ → ℂ := fun z =>
    if cut < ‖z‖ then bottcherCoord c₂ z else S₂.inv z with hGBdef
  have hRa₂pos : (0:ℝ) < Ra₂ ∨ True := Or.inr trivial
  -- the collar agreement
  have hagree : ∀ z ∈ Ext, cut < ‖z‖ → ‖z‖ ≤ 4 * cut →
      bottcherCoord c₂ z = S₂.inv z := by
    intro z hz hzlo hzhi
    have hmem := hbandmem z hz hzhi
    have hw := S₂.inv_mem hmem
    have hTw : S₂.T (S₂.inv z) = z := S₂.inv_right hmem
    have hwlog : Real.log ‖S₂.inv z‖ = greenFunctionDyn c₂ z := S₂.norm_inv hmem
    have hG₂z : Real.log Ra₂ < greenFunctionDyn c₂ z := hcollarG z hz hzlo hzhi
    have hwpos : (0:ℝ) < ‖S₂.inv z‖ := lt_trans (by linarith) hw.1
    have hwRa : Ra₂ < ‖S₂.inv z‖ := by
      rcases le_or_gt Ra₂ 0 with hRa0 | hRa0
      · linarith
      · calc Ra₂ = Real.exp (Real.log Ra₂) := (Real.exp_log hRa0).symm
          _ < Real.exp (Real.log ‖S₂.inv z‖) := by
              apply Real.exp_lt_exp.mpr
              rw [hwlog]
              linarith
          _ = ‖S₂.inv z‖ := Real.exp_log hwpos
    have hid := (hfar₂ (S₂.inv z) hwRa hw.2).1
    rw [hTw] at hid
    exact hid
  refine ⟨GBExtF, ?_, ?_⟩
  · intro z hz
    rcases lt_trichotomy ‖z‖ cut with hcase | hcase | hcase
    · have hev : GBExtF =ᶠ[nhds z] S₂.inv := by
        have hopen : IsOpen {w : ℂ | ‖w‖ < cut} :=
          isOpen_lt continuous_norm continuous_const
        filter_upwards [hopen.mem_nhds hcase] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = S₂.inv w
        rw [if_neg (by push Not; exact le_of_lt hw)]
      exact ((S₂.inv_analytic z (hbandmem z hz (by linarith))).congr hev.symm)
    · have hev : GBExtF =ᶠ[nhds z] S₂.inv := by
        have hopen : IsOpen ({w : ℂ | ‖w‖ < 2 * cut} ∩ Ext) := by
          apply IsOpen.inter _ hExto
          exact isOpen_lt continuous_norm continuous_const
        have hzmem : z ∈ {w : ℂ | ‖w‖ < 2 * cut} ∩ Ext := by
          constructor
          · show ‖z‖ < 2 * cut
            rw [hcase]
            linarith
          · exact hz
        filter_upwards [hopen.mem_nhds hzmem] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = S₂.inv w
        by_cases hf : cut < ‖w‖
        · rw [if_pos hf]
          exact hagree w hw.2 hf (by
            have h9 : ‖w‖ < 2 * cut := hw.1
            linarith)
        · rw [if_neg hf]
      have hzband : z ∈ S₂.T '' annulusSet rlo₂ R₀₂ := by
        apply hbandmem z hz
        rw [hcase]
        linarith
      exact ((S₂.inv_analytic z hzband).congr hev.symm)
    · have hev : GBExtF =ᶠ[nhds z] bottcherCoord c₂ := by
        have hopen : IsOpen {w : ℂ | cut < ‖w‖} :=
          isOpen_lt continuous_const continuous_norm
        filter_upwards [hopen.mem_nhds hcase] with w hw
        show (if cut < ‖w‖ then bottcherCoord c₂ w else S₂.inv w) = bottcherCoord c₂ w
        rw [if_pos hw]
      have hφan : AnalyticAt ℂ (bottcherCoord c₂) z := by
        apply (differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂)
        show max 2 ‖c₂‖ < ‖z‖
        linarith [hcutc₂]
      exact (hφan.congr hev.symm)
  · intro z hzfar
    show (if cut < ‖z‖ then bottcherCoord c₂ z else S₂.inv z) = bottcherCoord c₂ z
    rw [if_pos hzfar]

end Bottcher
