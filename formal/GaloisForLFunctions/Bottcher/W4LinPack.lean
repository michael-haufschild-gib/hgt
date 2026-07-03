/-
# The packaged root tower (W4-lin assembly)

The slim tower with the glued `2^m`-th root of the pushed second Böttcher coordinate: the
section, the scaffold chain, and the deepest lobe (intermediate lobes dropped — they break the
path structure of the gluing chain), carrying an analytic `Φ` with
`Φ^(2^m) = φ_{c₂} ∘ f_{c₂}^{[m]}` on the whole domain.  Everything is assembled from the
banked bricks of `W4LinWinding`; the ONE conditional input is `ChainOverlapsConnected` — the
preconnectedness of the deep consecutive overlaps (the 3-component sub-case of task #139).
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.MixedTowerExt
import GaloisForLFunctions.Bottcher.PatchSquareLocalize
import GaloisForLFunctions.Bottcher.LiftExists
import GaloisForLFunctions.Bottcher.PairMonodromy
import GaloisForLFunctions.Bottcher.W4LinOverlap
import GaloisForLFunctions.Bottcher.W4LinWinding

open Complex Set Filter Metric Topology

namespace Bottcher

/-- **The conditional connectivity interface** (tasks #139/#140): every deep consecutive
overlap of a wedge-slit scaffold chain — scaffold pair or scaffold–lobe — is preconnected.
The banked level-1 case (`overlap_section_scaffold_connected`) needs no clause.

The chain data carries the certified doubling window `(J₁, J₂)` (fold-1 form,
`2J − 2π ∈ (α, β)`): this pins the equality locus of `σ_{j+1}∘sq` and `σ_j` to the window's
component, which — for slit centers with the window in the middle fold-slot — is the unique
component of its antipodal parity class; the antipode argument kills the rest.  Without the
doubling clause the statement is FALSE (an adversarial branch choice puts the equality locus
on both end components; see the pipeline card addendum 5). -/
def ChainOverlapsConnected (c : ℂ) {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (ra rb RW θs : ℝ) : Prop :=
  ∀ (J₁ J₂ : ℝ) (σ : ℕ → ℂ → ℂ) (SL : ℕ → ℂ → ℂ) (k : ℕ), 1 ≤ k →
    θs + Real.pi / 8 ≤ J₁ → J₁ < J₂ → J₂ ≤ θs + 2 * Real.pi - Real.pi / 8 →
    θs + Real.pi / 8 ≤ 2 * J₁ - 2 * Real.pi →
    2 * J₂ - 2 * Real.pi ≤ θs + 2 * Real.pi - Real.pi / 8 →
    σ 0 = S.T →
    (∀ j : ℕ, ScaffoldProps c S.T
      (arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)) j (σ j)) →
    (∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      σ (j + 1) v ^ 2 = σ j v - c) →
    (∀ j : ℕ, ScaffoldProps c S.T (annulusSet ra rb) j (SL j)) →
    (∀ j : ℕ, ∀ v ∈ arcAnnulus ra rb (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      SL j v = σ j v) →
    (∀ j : ℕ, ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, σ (j + 1) (w ^ 2) = σ j w) →
    (∀ j : ℕ, 1 ≤ j → j + 1 ≤ k → IsPreconnected
      ((σ j '' arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)) ∩
       (σ (j + 1) '' arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)))) ∧
    IsPreconnected
      ((σ k '' arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)) ∩
       (SL k '' annulusSet ra rb))

end Bottcher


namespace Bottcher

set_option maxHeartbeats 3200000 in
/-- **The slim root tower.**  The section, the wedge-slit scaffold chain, and the depth-`k`
lobe assemble into a connected open `Ext` with the reach/level/floor exports of the slit tower
AND an analytic `Φ` with `Φ^(2^m) = φ_{c₂} ∘ f_{c₂}^{[m]}` on `Ext`, nonvanishing — the glued
root of the pushed second coordinate.  Conditional on exactly `ChainOverlapsConnected`. -/
theorem exists_tower_ext_slit_s_withRoot {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (hc100 : (100:ℝ) ≤ ‖c‖)
    (hh1 : 1 ≤ greenFunctionDyn c 0)
    (hlow18 : greenFunctionDyn c 0 + 1/8 ≤ Real.log rlo)
    {ra rb RW : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbRW : rb < RW) (hRWR : RW < R₀)
    (hra54 : 5 * greenFunctionDyn c 0 / 4 ≤ Real.log ra)
    (hrb14 : Real.log rb ≤ 2 * greenFunctionDyn c 0 - 1/4)
    (hraRW : ra ^ 2 < RW)
    (hRW12 : Real.log RW ≤ 4 * greenFunctionDyn c 0 - 1/2)
    (hRW72 : Real.log RW ≤ 7 * greenFunctionDyn c 0 / 2)
    {s : ℝ} (hs2 : 2 ≤ s) (hs40 : s ^ 2 ≤ ‖c‖ / 40)
    {θs : ℝ} (hθs1 : -Real.pi ≤ θs) (hθs2 : θs ≤ 2 * Real.pi)
    (havoid : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ∉ Metric.closedBall c (s ^ 2))
    {c₂ : ℂ} (hc₂2 : (2:ℝ) ≤ ‖c₂‖) (hsc₂ : Real.sqrt (2 * ‖c₂‖) + 1 ≤ s)
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀)
    (hgap : Real.exp (2 * Real.log rlo) < RW)
    (hconn : ChainOverlapsConnected c S ra rb RW θs)
    (k : ℕ) (hk1 : 1 ≤ k) :
    ∃ (Ext : Set ℂ) (SL : ℂ → ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧
      S.T '' annulusSet rlo R₀ ⊆ Ext ∧
      (∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) ∧
      (∀ z ∈ Ext, z ∈ S.T '' annulusSet rlo R₀ ∨
        greenFunctionDyn c z < 2 * greenFunctionDyn c 0) ∧
      (∀ z ∈ Ext, s < ‖z‖) ∧
      AnalyticOnNhd ℂ SL (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SL v) = S.T v) ∧
      (∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k) ∧
      (∀ v ∈ annulusSet ra rb, SL v ∈ Ext) ∧
      ∃ (m : ℕ) (Φ : ℂ → ℂ),
        AnalyticOnNhd ℂ Φ Ext ∧
        (∀ z ∈ Ext, Φ z ^ 2 ^ m = bottcherCoord c₂ ((quadratic c₂)^[m] z)) ∧
        (∀ z ∈ Ext, Φ z ≠ 0) := by
  classical
  have hh0 : 0 < greenFunctionDyn c 0 := by linarith
  have hlow : greenFunctionDyn c 0 < Real.log rlo := by linarith
  have hrb2h : Real.log rb < 2 * greenFunctionDyn c 0 := by linarith
  have hRW4h : Real.log RW < 4 * greenFunctionDyn c 0 := by linarith
  have hh18pos : (0:ℝ) < greenFunctionDyn c 0 - 1/8 := by linarith
  -- the wedge-slit scaffold at the prescribed angle
  have hslitne : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ≠ c := by
    intro v hv heq
    exact havoid v hv (by rw [heq]; exact Metric.mem_closedBall_self (by positivity))
  obtain ⟨α, β, J₁, J₂, hαeq, hβeq, hαβ, hβα, hαJ₁, hJ₁J₂, hJ₂β, hJ₁dbl, hJ₂dbl, σ, hσ0, hσP,
    hσsq, hσdbl, hσne⟩ :=
    exists_scaffold_chain_window S hrlo hra hraRW hRWR hRW4h hh0 hlow hθs1 hθs2 hslitne
  have havoidA : ∀ v ∈ arcAnnulus ra RW α β, S.T v ∉ Metric.closedBall c (s ^ 2) := by
    rw [hαeq, hβeq]
    exact havoid
  obtain ⟨SL, hSL0, hSLP, hSLsq, hSLmatch, hSLne⟩ :=
    exists_matched_lobes S hrlo hlow hra hrb hrbRW hRWR hrb2h hαβ hσ0 hσP hσsq
  have hrapos : (0:ℝ) < ra := by linarith
  have hrlopos : (0:ℝ) < rlo := by linarith
  have hraRW' : ra < RW := lt_trans hrb hrbRW
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  set B : Set ℂ := annulusSet ra rb with hBdef
  set P0 : Set ℂ := S.T '' annulusSet rlo R₀ with hP0def
  set Pσ : ℕ → Set ℂ := fun j => σ j '' A with hPσdef
  set PLk : Set ℂ := SL k '' B with hPLdef
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hBopen : IsOpen B := isOpen_annulusSet _ _
  have hP0open : IsOpen P0 :=
    isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) S.an S.dne
  have hP0conn : IsConnected P0 :=
    (isConnected_annulus hrlopos (by nlinarith [sq_nonneg rlo] :
      rlo < R₀)).image _ (S.an.continuousOn)
  have hPσopen : ∀ j, IsOpen (Pσ j) := fun j =>
    isOpen_image_of_analytic_dne hAopen (hσP j).1 (hσP j).2.2.2.1
  have hAconn : IsConnected A := isConnected_arcAnnulus hrapos hraRW' hαβ
  have hPσconn : ∀ j, IsConnected (Pσ j) := fun j =>
    hAconn.image _ ((hσP j).1.continuousOn)
  have hBconn : IsConnected B := isConnected_annulus hrapos hrb
  have hPLopen : IsOpen PLk :=
    isOpen_image_of_analytic_dne hBopen (hSLP k).1 (hSLP k).2.2.2.1
  have hPLconn : IsConnected PLk := hBconn.image _ ((hSLP k).1.continuousOn)
  -- overlap witnesses
  have hrasqrt : ra < Real.sqrt RW := by
    have h1 : Real.sqrt (ra ^ 2) < Real.sqrt RW :=
      Real.sqrt_lt_sqrt (by positivity) hraRW
    rwa [Real.sqrt_sq (le_of_lt hrapos)] at h1
  have hWne : (arcAnnulus ra (Real.sqrt RW) J₁ J₂).Nonempty :=
    (isConnected_arcAnnulus hrapos hrasqrt hJ₁J₂).nonempty
  have hWsubA : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ A := by
    intro w hw
    have h1 : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ arcAnnulus ra RW J₁ J₂ :=
      arcAnnulus_mono_radius (Real.sqrt_pos.mpr (by linarith)) (by
        have h2 : Real.sqrt RW < Real.sqrt (RW ^ 2) :=
          Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
        rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ RW)] at h2
        linarith)
    exact arcAnnulus_mono hαJ₁ hJ₂β (h1 hw)
  have hWsq : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, w ^ 2 ∈ A := by
    intro w hw
    apply sq_mem_arcAnnulus (r' := ra) (R' := Real.sqrt RW) _ _ hJ₁dbl hJ₂dbl hw
    · linarith [Real.log_pos (show (1:ℝ) < ra from by nlinarith)]
    · rw [show 2 * Real.log (Real.sqrt RW) = Real.log RW from by
        rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ RW)]; ring]
  have hAsubS : ∀ v ∈ A, v ∈ annulusSet rlo R₀ := by
    intro v hv
    have h1 := arcAnnulus_subset α β hrapos hraRW' hv
    exact ⟨lt_trans hra h1.1, lt_trans h1.2 hRWR⟩
  have hover0 : (P0 ∩ Pσ 1).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ 1 (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl 0 w hw
      rw [h1, hσ0]
      exact ⟨w, hAsubS w (hWsubA hw), rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hoverσ : ∀ j : ℕ, (Pσ j ∩ Pσ (j+1)).Nonempty := by
    intro j
    obtain ⟨w, hw⟩ := hWne
    refine ⟨σ (j+1) (w ^ 2), ?_, ?_⟩
    · have h1 := hσdbl j w hw
      rw [h1]
      exact ⟨w, hWsubA hw, rfl⟩
    · exact ⟨w ^ 2, hWsq w hw, rfl⟩
  have hCne : (arcAnnulus ra rb α β).Nonempty :=
    (isConnected_arcAnnulus hrapos hrb hαβ).nonempty
  have hCsubB : arcAnnulus ra rb α β ⊆ B := arcAnnulus_subset _ _ hrapos hrb
  have hCsubA : arcAnnulus ra rb α β ⊆ A :=
    arcAnnulus_mono_radius (by linarith) (le_of_lt hrbRW)
  have hoverL : (PLk ∩ Pσ k).Nonempty := by
    obtain ⟨v, hv⟩ := hCne
    refine ⟨SL k v, ⟨v, hCsubB hv, rfl⟩, ?_⟩
    rw [hSLmatch k v hv]
    exact ⟨v, hCsubA hv, rfl⟩
  -- per-piece Green levels
  have hlev_P0 : ∀ z ∈ P0, Real.log rlo < greenFunctionDyn c z ∧
      greenFunctionDyn c z < Real.log R₀ := by
    rintro z ⟨v, hv, rfl⟩
    rw [S.level v hv]
    constructor
    · exact Real.log_lt_log hrlopos hv.1
    · exact Real.log_lt_log (lt_trans hrlopos hv.1) hv.2
  have hlev_Pσ : ∀ j : ℕ, ∀ z ∈ Pσ j,
      Real.log ra / 2 ^ j < greenFunctionDyn c z ∧
      greenFunctionDyn c z < Real.log RW / 2 ^ j := by
    rintro j z ⟨v, hv, rfl⟩
    rw [(hσP j).2.1 v hv]
    have h1 := arcAnnulus_subset α β hrapos hraRW' hv
    have h2 : (0:ℝ) < 2 ^ j := by positivity
    constructor
    · exact div_lt_div_of_pos_right (Real.log_lt_log hrapos h1.1) h2
    · exact div_lt_div_of_pos_right
        (Real.log_lt_log (lt_trans hrapos h1.1) h1.2) h2
  have hlev_PL : ∀ z ∈ PLk,
      Real.log ra / 2 ^ k < greenFunctionDyn c z ∧
      greenFunctionDyn c z < Real.log rb / 2 ^ k := by
    rintro z ⟨v, hv, rfl⟩
    rw [(hSLP k).2.1 v hv]
    have h2 : (0:ℝ) < 2 ^ k := by positivity
    constructor
    · exact div_lt_div_of_pos_right (Real.log_lt_log hrapos hv.1) h2
    · exact div_lt_div_of_pos_right (Real.log_lt_log (lt_trans hrapos hv.1) hv.2) h2
  -- per-piece norm floor
  have hnorm_P0 : ∀ z ∈ P0, s < ‖z‖ := by
    intro z hz
    apply lt_norm_of_greenFunctionDyn_gt_s hc100 hs40
    have h1 := (hlev_P0 z hz).1
    linarith
  have hnorm_Pσ1 : ∀ z ∈ Pσ 1, s < ‖z‖ := by
    rintro z ⟨v, hv, rfl⟩
    have hsq1 : σ 1 v ^ 2 = σ 0 v - c := hσsq 0 v hv
    rw [hσ0] at hsq1
    have h5 := havoidA v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at h5
    have h4 : s ^ 2 < ‖S.T v - c‖ := not_le.mp h5
    have hn2 : ‖σ 1 v‖ ^ 2 = ‖S.T v - c‖ := by
      rw [← norm_pow, hsq1]
    nlinarith [norm_nonneg (σ 1 v), hs2]
  have hnorm_Pσdeep : ∀ j : ℕ, 2 ≤ j → ∀ z ∈ Pσ j, s < ‖z‖ := by
    intro j hj z hz
    apply lt_norm_of_greenFunctionDyn_lt_s hc100 hs40
    have h1 := (hlev_Pσ j z hz).2
    have h3 : (4:ℝ) ≤ 2 ^ j := by
      calc (4:ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
    have h4 : Real.log RW / 2 ^ j ≤ Real.log RW / 4 := by
      apply div_le_div_of_nonneg_left _ (by norm_num) h3
      have := Real.log_pos (show (1:ℝ) < RW by nlinarith)
      linarith
    linarith
  have hnorm_Pσ : ∀ j : ℕ, 1 ≤ j → ∀ z ∈ Pσ j, s < ‖z‖ := by
    intro j hj
    rcases eq_or_lt_of_le hj with h1 | h1
    · rw [← h1]
      exact hnorm_Pσ1
    · exact hnorm_Pσdeep j h1
  have hnorm_PL : ∀ z ∈ PLk, s < ‖z‖ := by
    intro z hz
    apply lt_norm_of_greenFunctionDyn_lt_s hc100 hs40
    have h1 := (hlev_PL z hz).2
    have h3 : (2:ℝ) ≤ 2 ^ k := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
    have h4 : Real.log rb / 2 ^ k ≤ Real.log rb / 2 := by
      apply div_le_div_of_nonneg_left _ (by norm_num) h3
      have := Real.log_pos (show (1:ℝ) < rb by nlinarith)
      linarith
    linarith
  -- the uniform push and the target function
  obtain ⟨m, hm⟩ := exists_uniform_push hc₂2 hsc₂
  set g : ℂ → ℂ := fun z => bottcherCoord c₂ ((quadratic c₂)^[m] z) with hgdef
  have hquad₂_an : ∀ (j : ℕ) (z : ℂ), AnalyticAt ℂ ((quadratic c₂)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simpa using analyticAt_id
    | succ w ih =>
        intro z
        rw [show (quadratic c₂)^[w+1] = (quadratic c₂)^[w] ∘ quadratic c₂ from
          Function.iterate_succ _ _]
        have h2 : AnalyticAt ℂ (quadratic c₂) z := by
          unfold quadratic
          exact (analyticAt_id.pow 2).add analyticAt_const
        exact (ih (quadratic c₂ z)).comp h2
  have hg_an_pt : ∀ z : ℂ, s ≤ ‖z‖ → AnalyticAt ℂ g z := by
    intro z hz
    have h1 : (quadratic c₂)^[m] z ∈ escapeOpen c₂ := by
      show max 2 ‖c₂‖ < ‖(quadratic c₂)^[m] z‖
      have h2 := hm z hz
      have h3 := norm_nonneg c₂
      apply max_lt <;> linarith
    exact (analyticOnNhd_bottcherCoord_full c₂ _ h1).comp (hquad₂_an m z)
  have hg_ne_all : ∀ z : ℂ, g z ≠ 0 := fun z => bottcherCoord_ne_zero c₂ _
  -- per-piece roots
  -- (0) the section root
  have hfloorP0 : ∀ w ∈ annulusSet rlo R₀, Real.sqrt (2 * ‖c₂‖) < ‖S.T w‖ := by
    intro w hw
    have h1 : S.T w ∈ P0 := ⟨w, hw, rfl⟩
    have h2 := hnorm_P0 _ h1
    linarith [Real.sqrt_nonneg (2 * ‖c₂‖), hsc₂]
  have hpushP0 : ∀ w ∈ annulusSet rlo R₀, 4 * ‖c₂‖ + 2 < ‖(quadratic c₂)^[m] (S.T w)‖ := by
    intro w hw
    exact hm _ (le_of_lt (hnorm_P0 _ ⟨w, hw, rfl⟩))
  obtain ⟨Φ₀, hΦ₀an, hΦ₀pow, hΦ₀ne⟩ :=
    exists_pow_root_on_towerSection_image S hrlo (by nlinarith [sq_nonneg rlo] : rlo < R₀)
      hc₂2 m hfloorP0 hpushP0
  -- (j) the scaffold roots
  have hσroot : ∀ j : ℕ, ∃ Φj : ℂ → ℂ, 1 ≤ j →
      AnalyticOnNhd ℂ Φj (Pσ j) ∧
      (∀ z ∈ Pσ j, Φj z ^ 2 ^ m = g z) ∧ (∀ z ∈ Pσ j, Φj z ≠ 0) := by
    intro j
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact ⟨fun _ => 1, fun h => absurd h (by omega)⟩
    · obtain ⟨Φj, h1, h2, h3⟩ := exists_pow_root_on_simplyConnImage hAopen
        (isSimplyConnected_arcAnnulus hrapos hraRW' hαβ hβα)
        (hσP j).1 (hσP j).2.2.1 (hσP j).2.2.2.1
        (fun z hz => hg_an_pt z (le_of_lt (hnorm_Pσ j h0 z hz)))
        (fun z _ => hg_ne_all z) m
      exact ⟨Φj, fun _ => ⟨h1, h2, h3⟩⟩
  -- (k+1) the lobe root, with vanishing core winding
  have hlobefloor : ∀ w ∈ B, Real.sqrt (2 * ‖c₂‖) < ‖SL k w‖ := by
    intro w hw
    have h2 := hnorm_PL _ ⟨w, hw, rfl⟩
    linarith [hsc₂]
  have hlobewind : (∫ θ in (0:ℝ)..(2 * Real.pi),
      logDeriv (fun w => g (SL k w)) (circleMap 0 ((ra + rb) / 2) θ)
        * (circleMap 0 ((ra + rb) / 2) θ * Complex.I))
      = ((2 ^ m * 0 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    set ρL : ℝ := (ra + rb) / 2 with hρLdef
    have hρ1 : ra < ρL := by rw [hρLdef]; linarith
    have hρ2 : ρL < rb := by rw [hρLdef]; linarith
    have hρ0 : (0:ℝ) < ρL := by rw [hρLdef]; linarith
    have hcirc : ∀ θ : ℝ, circleMap 0 ρL θ ∈ B := by
      intro θ
      have hnormc : ‖circleMap 0 ρL θ‖ = ρL := by
        simp [circleMap, Complex.norm_exp, abs_of_pos hρ0]
      exact ⟨by rw [hnormc]; exact hρ1, by rw [hnormc]; exact hρ2⟩
    set ℓL : C1Loop := sectionLoop (hSLP k).1 hcirc with hℓLdef
    have hℓLγ : ∀ θ, ℓL.γ θ = SL k (circleMap 0 ρL θ) := fun θ => rfl
    have hfarL : ∀ θ, Real.sqrt (2 * ‖c₂‖) < ‖ℓL.γ θ‖ := by
      intro θ
      rw [hℓLγ]
      exact hlobefloor _ (hcirc θ)
    have hpushL : ∀ θ : ℝ, 4 * ‖c₂‖ + 2 < ‖(quadratic c₂)^[m] (ℓL.γ θ)‖ := by
      intro θ
      rw [hℓLγ]
      exact hm _ (le_of_lt (hnorm_PL _ ⟨_, hcirc θ, rfl⟩))
    have hperiod := period_push_bottcher hc₂2 ℓL hfarL m hpushL
    have hwind0 : windInt ℓL 0 = 0 := by
      apply windInt_eq_zero_of_level_lt c ℓL
        (show (0:ℝ) < Real.log rb / 2 ^ k by
          have := Real.log_pos (show (1:ℝ) < rb by nlinarith)
          positivity)
      · intro θ
        rw [hℓLγ, (hSLP k).2.1 _ (hcirc θ)]
        have hnormc : ‖circleMap 0 ρL θ‖ = ρL := by
          simp [circleMap, Complex.norm_exp, abs_of_pos hρ0]
        rw [hnormc]
        exact (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 ^ k)).mpr
          (Real.log_le_log (by linarith) (by rw [hρLdef]; linarith))
      · show Real.log rb / 2 ^ k < greenFunctionDyn c 0
        have h3 : (2:ℝ) ≤ 2 ^ k := by
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
        have h4 : Real.log rb / 2 ^ k ≤ Real.log rb / 2 := by
          apply div_le_div_of_nonneg_left _ (by norm_num) h3
          have := Real.log_pos (show (1:ℝ) < rb by nlinarith)
          linarith
        linarith
    have hint : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
        logDeriv (fun w => g (SL k w)) (circleMap 0 ρL θ)
          * (circleMap 0 ρL θ * Complex.I)
        = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (ℓL.γ θ) * ℓL.γ' θ := by
      intro θ _
      have hesc : (quadratic c₂)^[m] (SL k (circleMap 0 ρL θ))
          ∈ escapeOpen c₂ := by
        show max 2 ‖c₂‖ < _
        have h2 := hm _ (le_of_lt (hnorm_PL _ ⟨_, hcirc θ, rfl⟩))
        have h3 := norm_nonneg c₂
        apply max_lt <;> linarith
      have hld : logDeriv (fun w => g (SL k w)) (circleMap 0 ρL θ)
          = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m])
              (SL k (circleMap 0 ρL θ))
            * _root_.deriv (SL k) (circleMap 0 ρL θ) := by
        have hcomp : (fun w => g (SL k w))
            = (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) ∘ SL k := rfl
        rw [hcomp]
        apply logDeriv_comp
        · exact ((analyticOnNhd_bottcherCoord_full c₂ _ hesc).comp
            (hquad₂_an m _)).differentiableAt
        · exact ((hSLP k).1 _ (hcirc θ)).differentiableAt
      rw [hld]
      show _ = logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m])
          (SL k (circleMap 0 ρL θ))
        * (_root_.deriv (SL k) (circleMap 0 ρL θ)
            * (circleMap 0 ρL θ * Complex.I))
      ring
    calc (∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv (fun w => g (SL k w)) (circleMap 0 ρL θ)
            * (circleMap 0 ρL θ * Complex.I))
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            logDeriv (bottcherCoord c₂ ∘ (quadratic c₂)^[m]) (ℓL.γ θ) * ℓL.γ' θ :=
          intervalIntegral.integral_congr hint
      _ = 2 ^ m * windInt ℓL 0 := hperiod
      _ = ((2 ^ m * 0 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [hwind0]
          push_cast
          ring
  obtain ⟨ΦL, hΦLan, hΦLpow, hΦLne⟩ :=
    exists_pow_root_on_biholoImage (show (1:ℝ) < ra by nlinarith) hrb
      (hSLP k).1 (hSLP k).2.2.1 (hSLP k).2.2.2.1
      (fun z hz => hg_an_pt z (le_of_lt (hnorm_PL z hz)))
      (fun z _ => hg_ne_all z) m 0 hlobewind
  -- instantiate the conditional connectivity
  have hσP' : ∀ j : ℕ, ScaffoldProps c S.T
      (arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8)) j (σ j) := by
    intro j
    rw [← hαeq, ← hβeq]
    exact hσP j
  have hσsq' : ∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8)
      (θs + 2 * Real.pi - Real.pi / 8), σ (j + 1) v ^ 2 = σ j v - c := by
    intro j v hv
    apply hσsq j v
    rw [hAdef, hαeq, hβeq]
    exact hv
  have hSLmatch' : ∀ j : ℕ, ∀ v ∈ arcAnnulus ra rb (θs + Real.pi / 8)
      (θs + 2 * Real.pi - Real.pi / 8), SL j v = σ j v := by
    intro j v hv
    apply hSLmatch j v
    rw [hαeq, hβeq]
    exact hv
  obtain ⟨hconnσ, hconnL⟩ := hconn J₁ J₂ σ SL k hk1
    (by rw [← hαeq]; exact hαJ₁) hJ₁J₂ (by rw [← hβeq]; exact hJ₂β)
    (by rw [← hαeq]; exact hJ₁dbl) (by rw [← hβeq]; exact hJ₂dbl)
    hσ0 hσP' hσsq' hSLP hSLmatch' hσdbl
  have hconnσA : ∀ j : ℕ, 1 ≤ j → j + 1 ≤ k → IsPreconnected (Pσ j ∩ Pσ (j + 1)) := by
    intro j h1 h2
    have := hconnσ j h1 h2
    rwa [← hαeq, ← hβeq] at this
  have hconnLA : IsPreconnected (Pσ k ∩ PLk) := by
    have := hconnL
    rwa [← hαeq, ← hβeq] at this
  -- the level-1 overlap is connected unconditionally
  have hconn01 : IsPreconnected (P0 ∩ Pσ 1) := by
    have h1 := overlap_section_scaffold_connected S hrlo hra hraRW' hRWR hαβ hgap
      (hσP 1).1 (hσP 1).2.1 hsurj
    exact h1.isPreconnected
  -- the V-sequence
  set V : ℕ → Set ℂ := fun i => if i = 0 then P0 else if i ≤ k then Pσ i else PLk with hVdef
  have hV0 : V 0 = P0 := rfl
  have hVj : ∀ j : ℕ, 1 ≤ j → j ≤ k → V j = Pσ j := by
    intro j h1 h2
    rw [hVdef]
    simp only [if_neg (by omega : ¬ j = 0), if_pos h2]
  have hVhi : ∀ j : ℕ, k < j → V j = PLk := by
    intro j h1
    rw [hVdef]
    simp only [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j ≤ k)]
  have hVopen : ∀ i : ℕ, IsOpen (V i) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, hV0]; exact hP0open
    · rcases le_or_gt i k with h1 | h1
      · rw [hVj i h0 h1]; exact hPσopen i
      · rw [hVhi i h1]; exact hPLopen
  set Ext : Set ℂ := ⋃ i ∈ Finset.range (k + 2), V i with hExtdef
  have hVsub : ∀ i : ℕ, i ≤ k + 1 → V i ⊆ Ext := by
    intro i hi z hz
    exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hz
  have hVcases : ∀ z ∈ Ext, z ∈ P0 ∨ (∃ j, 1 ≤ j ∧ j ≤ k ∧ z ∈ Pσ j) ∨ z ∈ PLk := by
    intro z hz
    rw [hExtdef, Set.mem_iUnion₂] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    simp only [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · left
      rw [h0, hV0] at hzi
      exact hzi
    · rcases le_or_gt i k with h1 | h1
      · right; left
        exact ⟨i, h0, h1, by rwa [hVj i h0 h1] at hzi⟩
      · right; right
        rwa [hVhi i h1] at hzi
  choose Φσ hΦσ using hσroot
  refine ⟨Ext, SL k, ?_, ?_, ?_, ?_, ?_, ?_, (hSLP k).1, (hSLP k).2.2.2.2, (hSLP k).2.1, ?_, ?_⟩
  · -- open
    exact isOpen_biUnion (fun i _ => hVopen i)
  · -- connected: chain induction
    have hstep : ∀ n : ℕ, n ≤ k + 1 → IsConnected (⋃ i ∈ Finset.range (n + 1), V i) := by
      intro n
      induction n with
      | zero =>
          intro _
          have h0 : (⋃ i ∈ Finset.range (0 + 1), V i) = P0 := by
            rw [show (0:ℕ) + 1 = 1 from rfl, Finset.range_one]
            simp [hV0]
          rw [h0]
          exact hP0conn
      | succ w ih =>
          intro hw
          have hsplit : (⋃ i ∈ Finset.range (w + 2), V i)
              = (⋃ i ∈ Finset.range (w + 1), V i) ∪ V (w + 1) := by
            have h2 : w + 2 = (w + 1) + 1 := by omega
            rw [h2, Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
          rw [hsplit]
          have hwc : IsConnected (⋃ i ∈ Finset.range (w + 1), V i) := ih (by omega)
          have hVw1 : IsConnected (V (w + 1)) := by
            rcases le_or_gt (w + 1) k with h1 | h1
            · rw [hVj (w + 1) (by omega) h1]
              exact hPσconn _
            · rw [hVhi (w + 1) h1]
              exact hPLconn
          have hover : ((⋃ i ∈ Finset.range (w + 1), V i) ∩ V (w + 1)).Nonempty := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0
              obtain ⟨z, hz1, hz2⟩ := hover0
              have hm0 : z ∈ V 0 := by rw [hV0]; exact hz1
              have hm1 : z ∈ V 1 := by
                rw [hVj 1 le_rfl (by omega)]
                exact hz2
              exact ⟨z, Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hm0, hm1⟩
            · rcases le_or_gt (w + 1) k with h1 | h1
              · obtain ⟨z, hz1, hz2⟩ := hoverσ w
                have hmw : z ∈ V w := by
                  rw [hVj w h0 (by omega)]
                  exact hz1
                have hmw1 : z ∈ V (w + 1) := by
                  rw [hVj (w + 1) (by omega) h1]
                  exact hz2
                exact ⟨z, Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hmw, hmw1⟩
              · have h3 : w = k := by omega
                obtain ⟨z, hz1, hz2⟩ := hoverL
                have hmw : z ∈ V w := by
                  rw [hVj w h0 (by omega), h3]
                  exact hz2
                have hmw1 : z ∈ V (w + 1) := by
                  rw [hVhi (w + 1) h1]
                  exact hz1
                exact ⟨z, Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hmw, hmw1⟩
          obtain ⟨z, hz1, hz2⟩ := hover
          exact IsConnected.union ⟨z, hz1, hz2⟩ hwc hVw1
    have := hstep (k + 1) le_rfl
    rwa [hExtdef]
  · -- P0 ⊆ Ext
    have h1 := hVsub 0 (by omega)
    rwa [hV0] at h1
  · -- reach
    intro z hz
    rcases hVcases z hz with hzP | ⟨j, hj1, hjk, hzσ⟩ | hzL
    · exact ⟨0, by omega, by simpa using hzP⟩
    · obtain ⟨v, hv, rfl⟩ := hzσ
      refine ⟨j, hjk, ?_⟩
      rw [(hσP j).2.2.2.2 v hv]
      exact ⟨v, hAsubS v hv, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := hzL
      refine ⟨k, le_rfl, ?_⟩
      rw [(hSLP k).2.2.2.2 v hv]
      refine ⟨v, ?_, rfl⟩
      exact ⟨lt_trans hra hv.1, lt_trans hv.2 (lt_trans hrbRW hRWR)⟩
  · -- levels
    intro z hz
    rcases hVcases z hz with hzP | ⟨j, hj1, hjk, hzσ⟩ | hzL
    · exact Or.inl hzP
    · right
      have h1 := (hlev_Pσ j z hzσ).2
      have h3 : (2:ℝ) ≤ 2 ^ j := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
      have h4 : Real.log RW / 2 ^ j ≤ Real.log RW / 2 := by
        apply div_le_div_of_nonneg_left _ (by norm_num) h3
        have := Real.log_pos (show (1:ℝ) < RW by nlinarith)
        linarith
      linarith
    · right
      have h1 := (hlev_PL z hzL).2
      have h3 : (2:ℝ) ≤ 2 ^ k := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
      have h4 : Real.log rb / 2 ^ k ≤ Real.log rb / 2 := by
        apply div_le_div_of_nonneg_left _ (by norm_num) h3
        have := Real.log_pos (show (1:ℝ) < rb by nlinarith)
        linarith
      linarith
  · -- norm floor
    intro z hz
    rcases hVcases z hz with hzP | ⟨j, hj1, hjk, hzσ⟩ | hzL
    · exact hnorm_P0 z hzP
    · exact hnorm_Pσ j hj1 z hzσ
    · exact hnorm_PL z hzL
  · -- SL v ∈ Ext
    intro v hv
    have h1 : SL k v ∈ PLk := ⟨v, hv, rfl⟩
    have h2 := hVsub (k + 1) le_rfl
    rw [hVhi (k + 1) (by omega)] at h2
    exact h2 h1
  · -- THE ROOT: sequential glue
    set βs : ℕ → ℂ → ℂ := fun i => if i = 0 then Φ₀ else if i ≤ k then Φσ i else ΦL
      with hβsdef
    have hβs0 : βs 0 = Φ₀ := rfl
    have hβsj : ∀ j : ℕ, 1 ≤ j → j ≤ k → βs j = Φσ j := by
      intro j h1 h2
      rw [hβsdef]
      simp only [if_neg (by omega : ¬ j = 0), if_pos h2]
    have hβshi : ∀ j : ℕ, k < j → βs j = ΦL := by
      intro j h1
      rw [hβsdef]
      simp only [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j ≤ k)]
    have hVan : ∀ i : ℕ, i ≤ k + 1 → AnalyticOnNhd ℂ (βs i) (V i) := by
      intro i _
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0, hβs0, hV0]
        exact hΦ₀an
      · rcases le_or_gt i k with h1 | h1
        · rw [hβsj i h0 h1, hVj i h0 h1]
          exact (hΦσ i h0).1
        · rw [hβshi i h1, hVhi i h1]
          exact hΦLan
    have hVpow : ∀ i : ℕ, i ≤ k + 1 → ∀ z ∈ V i, βs i z ^ 2 ^ m = g z := by
      intro i _
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0, hβs0, hV0]
        intro z hz
        exact hΦ₀pow z hz
      · rcases le_or_gt i k with h1 | h1
        · rw [hβsj i h0 h1, hVj i h0 h1]
          exact (hΦσ i h0).2.1
        · rw [hβshi i h1, hVhi i h1]
          exact hΦLpow
    -- numeric band facts
    have hRWlog0 : (0:ℝ) ≤ Real.log RW := by
      have := Real.log_pos (show (1:ℝ) < RW by nlinarith)
      linarith
    have hlrh : greenFunctionDyn c 0 ≤ Real.log rlo := by linarith
    -- pairwise disjointness of non-consecutive pieces
    have hkill_P0_σ : ∀ j : ℕ, 2 ≤ j → P0 ∩ Pσ j = ∅ := by
      intro j hj
      apply disjoint_of_green_bands (hlev_P0) (hlev_Pσ j)
      exact green_band_separation_section hRW72 hRWlog0 hlrh hh0 hj
    have hkill_σσ : ∀ i j : ℕ, 1 ≤ i → i + 2 ≤ j → Pσ i ∩ Pσ j = ∅ := by
      intro i j _ hij
      apply disjoint_of_green_bands (hlev_Pσ i) (hlev_Pσ j)
      exact green_band_separation hra54 hRW72 hRWlog0 hh0 hij
    have hrbra2 : Real.log rb ≤ 2 * Real.log ra := by linarith
    have hkill_P0_L : P0 ∩ PLk = ∅ := by
      apply disjoint_of_green_bands (hlev_P0) (hlev_PL)
      have h3 : (2:ℝ) ≤ 2 ^ k := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
      have h4 : Real.log rb / 2 ^ k ≤ Real.log rb / 2 := by
        apply div_le_div_of_nonneg_left _ (by norm_num) h3
        have := Real.log_pos (show (1:ℝ) < rb by nlinarith)
        linarith
      linarith
    have hkill_σL : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ k → Pσ i ∩ PLk = ∅ := by
      intro i _ hik
      apply disjoint_of_green_bands (hlev_Pσ i) (hlev_PL)
      have h1 : (0:ℝ) ≤ Real.log ra := by
        have := Real.log_pos (show (1:ℝ) < ra by nlinarith)
        linarith
      have h2 : Real.log rb / 2 ^ k ≤ Real.log ra / 2 ^ (k - 1) := by
        have h3 : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h3]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc Real.log rb * 2 ^ (k - 1) ≤ 2 * Real.log ra * 2 ^ (k - 1) := by
              nlinarith [hrbra2, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (k - 1)]
          _ = Real.log ra * (2 * 2 ^ (k - 1)) := by ring
      have h5 : Real.log ra / 2 ^ (k - 1) ≤ Real.log ra / 2 ^ i := by
        apply div_le_div_of_nonneg_left h1 (by positivity)
        apply pow_le_pow_right₀ (by norm_num)
        omega
      linarith
    -- the cumulative overlaps reduce to the last pair
    have hcum : ∀ j : ℕ, j ≤ k + 1 →
        IsPreconnected ((⋃ i ∈ Finset.range j, V i) ∩ V j) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        have he : (⋃ i ∈ Finset.range 0, V i) = (∅ : Set ℂ) := by simp
        rw [he, Set.empty_inter]
        exact isPreconnected_empty
      · have hred : (⋃ i ∈ Finset.range j, V i) ∩ V j = V (j - 1) ∩ V j := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_iUnion₂]
          constructor
          · rintro ⟨⟨i, hi, hzi⟩, hzj⟩
            simp only [Finset.mem_range] at hi
            by_cases hij : i = j - 1
            · exact ⟨by rwa [← hij], hzj⟩
            · exfalso
              have hij2 : i + 2 ≤ j := by omega
              have hempty : V i ∩ V j = ∅ := by
                rcases Nat.eq_zero_or_pos i with hi0 | hi0
                · rcases le_or_gt j k with hjk | hjk
                  · rw [hi0, hV0, hVj j (by omega) hjk]
                    exact hkill_P0_σ j (by omega)
                  · rw [hi0, hV0, hVhi j hjk]
                    exact hkill_P0_L
                · rcases le_or_gt j k with hjk | hjk
                  · rw [hVj i hi0 (by omega), hVj j (by omega) hjk]
                    exact hkill_σσ i j hi0 hij2
                  · rw [hVj i hi0 (by omega), hVhi j hjk]
                    exact hkill_σL i hi0 (by omega)
              have : z ∈ V i ∩ V j := ⟨hzi, hzj⟩
              rw [hempty] at this
              exact this
          · rintro ⟨hzj1, hzj⟩
            exact ⟨⟨j - 1, by simp only [Finset.mem_range]; omega, hzj1⟩, hzj⟩
        rw [hred]
        by_cases hj1 : j = 1
        · -- j = 1: the section–scaffold overlap
          subst hj1
          show IsPreconnected (V 0 ∩ V 1)
          rw [hV0, hVj 1 le_rfl (by omega)]
          exact hconn01
        · rcases le_or_gt j k with hjk | hjk
          · -- 2 ≤ j ≤ k: scaffold pair
            have hj1 : 1 ≤ j - 1 := by omega
            have hsucc : (j - 1) + 1 = j := by omega
            rw [hVj (j - 1) hj1 (by omega), hVj j (by omega) hjk]
            have := hconnσA (j - 1) hj1 (by omega)
            rwa [hsucc] at this
          · -- j = k + 1: scaffold–lobe
            have hj1 : j - 1 = k := by omega
            rw [hVj (j - 1) (by omega) (by omega), hVhi j hjk, hj1]
            exact hconnLA
    obtain ⟨Φ, hΦan, hΦpow, hΦne, _⟩ :=
      exists_pow_root_glue_of_seq (N := 2 ^ m) Nat.one_le_two_pow V βs (k + 1)
        (fun i _ => hVopen i) (fun z _ => hg_ne_all z) hVan hVpow hcum
    exact ⟨m, Φ, hΦan, hΦpow, hΦne⟩

end Bottcher

namespace Bottcher

/-- **Forward invariance of the escape region** `{max 2 ‖c‖ < ‖z‖}` under `f_c`. -/
theorem escapeOpen_mem_quadratic {c z : ℂ} (hz : z ∈ escapeOpen c) :
    quadratic c z ∈ escapeOpen c := by
  have h1 : max 2 ‖c‖ < ‖z‖ := hz
  have h2 : (2:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) h1
  have h3 : ‖c‖ < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) h1
  have h4 : ‖z ^ 2‖ ≤ ‖quadratic c z‖ + ‖c‖ := by
    have h5 : quadratic c z = z ^ 2 + c := rfl
    calc ‖z ^ 2‖ = ‖(z ^ 2 + c) + (-c)‖ := by ring_nf
      _ ≤ ‖z ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
      _ = ‖quadratic c z‖ + ‖c‖ := by rw [← h5, norm_neg]
  show max 2 ‖c‖ < ‖quadratic c z‖
  rw [norm_pow] at h4
  apply max_lt
  · nlinarith
  · nlinarith

end Bottcher

namespace Bottcher

/-- **The chain-overlap interface is a theorem** (task #140): under the working radius/level
window and the normalized slit position `θs ∈ [−3π/8, 13π/8]`, `ChainOverlapsConnected` holds —
each consecutive scaffold overlap is the `σ_j`-image of the certified fold slot
(`scaffold_scaffold_overlap_preconnected`), and the scaffold–lobe overlap is the image of the
thin arc annulus (`scaffold_lobe_overlap_preconnected`).  Slit centers below `−3π/8` are served
by the `+2π` renormalization at the call site. -/
theorem chainOverlapsConnected_of_normalized {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    {ra rb RW θs : ℝ}
    (hrlo : 1 < rlo) (hra : rlo < ra) (hrab : ra < rb) (hrbRW : rb < RW)
    (hraRW : ra ^ 2 < RW) (hRWR : RW < R₀)
    (hh0 : 0 < greenFunctionDyn c 0)
    (hra54 : 5 * greenFunctionDyn c 0 / 4 ≤ Real.log ra)
    (hRW72 : Real.log RW ≤ 7 * greenFunctionDyn c 0 / 2)
    (hθlo : -(3 * Real.pi / 8) ≤ θs) (hθhi : θs ≤ 13 * Real.pi / 8) :
    ChainOverlapsConnected c S ra rb RW θs := by
  have hπ := Real.pi_pos
  intro J₁ J₂ σ SL k _hk1 hαJ₁ hJ₁J₂ hJ₂β hJ₁dbl hJ₂dbl _hσ0 hσP _hσsq hSLP hSLmatch hdbl
  constructor
  · intro j _hj1 _hjk
    exact scaffold_scaffold_overlap_preconnected S hrlo hra hraRW hRWR hh0 hra54 hRW72
      (by ring) (by linarith) (by linarith)
      (hσP j) (hσP (j + 1)) hαJ₁ hJ₁J₂ hJ₂β hJ₁dbl hJ₂dbl (hdbl j)
  · have hover := scaffold_lobe_overlap_preconnected S hra (by linarith) hrab hrbRW hRWR
      (by linarith : θs + Real.pi / 8 < θs + 2 * Real.pi - Real.pi / 8)
      (hσP k).1 (hσP k).2.2.2.2 (hSLP k).2.2.2.2 (hSLmatch k)
    exact hover

set_option maxHeartbeats 3200000 in
/-- **Linear-gap pair tower data.**  For a disconnected `c` with `‖c‖ ≥ 1000` and any second
parameter `c₂` with `(√(2‖c₂‖)+1)² ≤ ‖c‖/300`, the far domain carries the full pair package:
the `c`-radical tower with its odd loops AND the glued second coordinate `GBExt` restricting to
the `φ_{c₂}` germ — UNCONDITIONAL: the chain-overlap connectivity is a theorem
(`chainOverlapsConnected_of_normalized`) after renormalizing the slit center by a full turn
when it falls below `−3π/8`. -/
theorem bottcher_towerDataG_linGapRoot (c c₂ : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) (hc₂2 : (2:ℝ) ≤ ‖c₂‖)
    (hsgap : (Real.sqrt (2 * ‖c₂‖) + 1) ^ 2 ≤ ‖c‖ / 300) :
    ∃ Bmin : ℝ, 1 < Bmin ∧
    ∀ (U : Set ℂ), IsOpen U → IsPreconnected U → U.Nonempty → U.Infinite →
      (∀ z ∈ U, Bmin < ‖z‖) →
      ∃ (a₁ a₂ : analyticSubring U),
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c)) = (a₁ : Filter.Germ (𝓟 U) ℂ) ∧
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
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
  set s : ℝ := Real.sqrt (2 * ‖c₂‖) + 1 with hsdef
  have hsqrt2 : (2:ℝ) ≤ Real.sqrt (2 * ‖c₂‖) := by
    have h1 : Real.sqrt 4 ≤ Real.sqrt (2 * ‖c₂‖) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hs2 : (2:ℝ) ≤ s := by rw [hsdef]; linarith
  have hsc₂ : Real.sqrt (2 * ‖c₂‖) + 1 ≤ s := le_of_eq hsdef.symm
  have hs300 : s ^ 2 ≤ ‖c‖ / 300 := by rw [hsdef]; exact hsgap
  have hs40 : s ^ 2 ≤ ‖c‖ / 40 := by linarith
  have hc₂c : 2 * ‖c₂‖ ≤ s ^ 2 := by
    have h1 : Real.sqrt (2 * ‖c₂‖) ^ 2 = 2 * ‖c₂‖ := Real.sq_sqrt (by positivity)
    rw [hsdef]
    nlinarith [Real.sqrt_nonneg (2 * ‖c₂‖)]
  have hsmall : 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 ≤ 1/100 * (‖c‖ ^ 2 - ‖c‖) := by
    have h1 : 2 * s ^ 2 * ‖c‖ ≤ 2 / 300 * ‖c‖ ^ 2 := by nlinarith
    have h2 : s ^ 4 ≤ ‖c‖ ^ 2 / 90000 := by nlinarith [sq_nonneg (s ^ 2)]
    nlinarith [sq_nonneg ‖c‖]
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have hh0 : 0 < h := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c 0) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c 0).mp h1.symm) hc
  have h2h := abs_le.mp (abs_two_greenCritical_sub_log_le hc100)
  rw [← hhdef] at h2h
  have hexp1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have hexp6 : Real.exp 6 ≤ 1000 := by
    have h1 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h1]
    calc Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le hexp1 6
      _ ≤ 1000 := by norm_num
  have hlogc6 : (6:ℝ) ≤ Real.log ‖c‖ := by
    have h1 : Real.exp 6 ≤ ‖c‖ := le_trans hexp6 hc1000
    calc (6:ℝ) = Real.log (Real.exp 6) := (Real.log_exp 6).symm
      _ ≤ Real.log ‖c‖ := Real.log_le_log (Real.exp_pos 6) h1
  have hh1 : 1 ≤ h := by linarith [h2h.1]
  obtain ⟨Ra, Rinj, hRa1, hRaG, hInj, _hRinjbd, hanchor⟩ := exists_tower_anchor c
  set Bmin : ℝ := max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
    (max (Real.exp (4 * h + 2)) (Real.exp (bottcherBallBound c + 2))) + 1 with hBmindef
  have hBminc3 : ‖c‖ + 3 < Bmin := by
    have h1 : ‖c‖ + 3 ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) (Real.exp (bottcherBallBound c + 2))) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBmin1 : (1:ℝ) < Bmin := by linarith [norm_nonneg c]
  have hBminRb : Real.exp (Real.log Ra + 2) < Bmin := by
    have h1 : Real.exp (Real.log Ra + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) (Real.exp (bottcherBallBound c + 2))) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBmin4h : Real.exp (4 * h + 2) < Bmin := by
    have h1 : Real.exp (4 * h + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) (Real.exp (bottcherBallBound c + 2))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    rw [hBmindef]
    linarith
  have hBminBB : Real.exp (bottcherBallBound c + 2) < Bmin := by
    have h1 : Real.exp (bottcherBallBound c + 2)
        ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
          (max (Real.exp (4 * h + 2)) (Real.exp (bottcherBallBound c + 2))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hBmindef]
    linarith
  have hBminpos : (0:ℝ) < Bmin := by linarith
  have hBmin2 : (2:ℝ) < Bmin := by linarith [norm_nonneg c]
  obtain ⟨rlo, R₀, hrlo1, hrloRb, hRbR₀, hrlosq, hMR₀, hlow, hhi, S, hfar, hbandsurj⟩ :=
    exists_tower_deep_of_anchor c (by positivity : (0:ℝ) < h / 2)
      (max (Real.exp (4 * h + 2)) (Bmin * Real.exp 3)) hRa1 hRaG hanchor
  rw [← hhdef] at hlow hhi
  set Rb : ℝ := Ra with hRbdef
  have hlogR₀ : 4 * h + 2 < Real.log R₀ := by
    have h0 : Real.exp (4 * h + 2) < R₀ :=
      lt_of_le_of_lt (le_max_left _ _) hMR₀
    have h1 : Real.log (Real.exp (4 * h + 2)) < Real.log R₀ :=
      Real.log_lt_log (Real.exp_pos _) h0
    rwa [Real.log_exp] at h1
  have hBminR₀ : Bmin * Real.exp 3 < R₀ := lt_of_le_of_lt (le_max_right _ _) hMR₀
  have hRbpos : (0:ℝ) < Rb := by
    rw [hRbdef]
    linarith
  have hGfar : ∀ z : ℂ, Bmin < ‖z‖ → Real.log Rb < greenFunctionDyn c z := by
    intro z hz
    apply green_far_gt c (Real.log Rb) z
    apply max_lt
    · exact lt_trans hBminc3 hz
    · exact lt_trans hBminRb hz
  have hEscfar : ∀ z : ℂ, Bmin < ‖z‖ → z ∈ escapeOpen c := by
    intro z hz
    show max 2 ‖c‖ < ‖z‖
    apply max_lt
    · linarith
    · linarith [hBminc3, hz]
  set Afar : Set ℂ := {z : ℂ | Bmin < ‖z‖} with hAfardef
  have hAfaro : IsOpen Afar := isOpen_lt continuous_const continuous_norm
  have hAfarconn : IsConnected Afar := isConnected_norm_gt (by linarith : (0:ℝ) < Bmin)
  have hφanA : AnalyticOnNhd ℂ (bottcherCoord c) Afar := fun z hz =>
    (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) z (hEscfar z hz)
  have hc₂small : ‖c₂‖ ≤ ‖c‖ / 600 := by linarith
  have hAfarEsc₂ : Afar ⊆ escapeOpen c₂ := by
    intro z hz
    show max 2 ‖c₂‖ < ‖z‖
    have h1 : Bmin < ‖z‖ := hz
    apply max_lt
    · linarith
    · linarith [hBminc3]
  have hφ₂anA : AnalyticOnNhd ℂ (bottcherCoord c₂) Afar :=
    (analyticOnNhd_bottcherCoord_full c₂).mono hAfarEsc₂
  -- raise the inner radius
  set rlo' : ℝ := max rlo (Real.exp (h + 1/8)) with hrlo'def
  have hrlole : rlo ≤ rlo' := le_max_left _ _
  set S' : TowerSection c rlo' R₀ := S.restrictLo hrlole with hS'def
  have hrlo'1 : 1 < rlo' := lt_of_lt_of_le hrlo1 hrlole
  have hrlo'pos : (0:ℝ) < rlo' := by linarith
  have hrlo'lt : rlo' < Real.exp (3 * h / 2) := by
    apply max_lt
    · have h1 : rlo = Real.exp (Real.log rlo) := (Real.exp_log (by linarith)).symm
      rw [h1]
      exact Real.exp_lt_exp.mpr (by linarith)
    · exact Real.exp_lt_exp.mpr (by linarith)
  have hlow18' : h + 1/8 ≤ Real.log rlo' := by
    have h1 : Real.exp (h + 1/8) ≤ rlo' := le_max_right _ _
    calc h + 1/8 = Real.log (Real.exp (h + 1/8)) := (Real.log_exp _).symm
      _ ≤ Real.log rlo' := Real.log_le_log (Real.exp_pos _) h1
  have hlr'32 : Real.log rlo' < 3 * h / 2 := by
    have h1 := Real.log_lt_log hrlo'pos hrlo'lt
    rwa [Real.log_exp] at h1
  have hfar' : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S'.T w) = w :=
    fun w h1 h2 => (hfar w h1 h2).1
  have hsurj' : ∀ z : ℂ, Real.log rlo' < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S'.T '' annulusSet rlo' R₀ := by
    intro z h1 h2
    have h3 : Real.log rlo ≤ Real.log rlo' := Real.log_le_log (by linarith) hrlole
    obtain ⟨v, hv, hveq⟩ := hbandsurj z (by linarith) h2
    refine ⟨v, ?_, hveq⟩
    have h4 : greenFunctionDyn c (S.T v) = Real.log ‖v‖ := S.level v hv
    have h5 : Real.log ‖v‖ = greenFunctionDyn c z := by rw [← h4, hveq]
    have hvpos : (0:ℝ) < ‖v‖ := lt_trans (by linarith) hv.1
    refine ⟨?_, hv.2⟩
    have h6 : Real.log rlo' < Real.log ‖v‖ := by rw [h5]; exact h1
    calc rlo' = Real.exp (Real.log rlo') := (Real.exp_log hrlo'pos).symm
      _ < Real.exp (Real.log ‖v‖) := Real.exp_lt_exp.mpr h6
      _ = ‖v‖ := Real.exp_log hvpos
  have hrlo_ceiling : Real.log rlo' ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2 := by
    have h1 : Real.log (‖c‖ ^ 2) ≤ Real.log (‖c‖ ^ 2 + ‖c‖) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [h2h.2, hlr'32, hh0]
  have hrlo2h : Real.log rlo' < 2 * h - 1/4 := by linarith [hlr'32, hh1]
  have hR₀4h : 4 * h + 1 < Real.log R₀ := by linarith [hlogR₀]
  obtain ⟨θs, hθs1, hθs2, hθwin⟩ :=
    exists_slit_center_avoiding_patch_s S' hc1000 hrlo'1 hRa1 hRbR₀ hfar' hrlo_ceiling
      hrlo2h hR₀4h hsurj' hs2 hs40 hsmall
  -- renormalize the slit center into the fold-friendly window [−3π/8, 13π/8]
  have hπ := Real.pi_pos
  set θsN : ℝ := if θs < -(3 * Real.pi / 8) then θs + 2 * Real.pi else θs with hθsNdef
  have hθNlo : -(3 * Real.pi / 8) ≤ θsN := by
    rw [hθsNdef]
    by_cases hcase : θs < -(3 * Real.pi / 8)
    · rw [if_pos hcase]
      linarith
    · rw [if_neg hcase]
      linarith [not_lt.mp hcase]
  have hθNhi : θsN ≤ 13 * Real.pi / 8 := by
    rw [hθsNdef]
    by_cases hcase : θs < -(3 * Real.pi / 8)
    · rw [if_pos hcase]
      linarith
    · rw [if_neg hcase]
      linarith
  have hθN1 : -Real.pi ≤ θsN := by linarith
  have hθN2 : θsN ≤ 2 * Real.pi := by linarith
  have hshiftN : ∀ ra RW : ℝ,
      arcAnnulus ra RW (θsN + Real.pi / 8) (θsN + 2 * Real.pi - Real.pi / 8)
        = arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8) := by
    intro ra RW
    rw [hθsNdef]
    by_cases hcase : θs < -(3 * Real.pi / 8)
    · rw [if_pos hcase,
        show θs + 2 * Real.pi + Real.pi / 8 = (θs + Real.pi / 8) + 2 * Real.pi from by ring,
        show θs + 2 * Real.pi + 2 * Real.pi - Real.pi / 8
          = (θs + 2 * Real.pi - Real.pi / 8) + 2 * Real.pi from by ring,
        arcAnnulus_shift_two_pi]
    · rw [if_neg hcase]
  refine ⟨Bmin, hBmin1, ?_⟩
  intro U hUo hUc hUne hUinf hUfar
  have hUA : U ⊆ Afar := fun z hz => hUfar z hz
  have hφanU : AnalyticOnNhd ℂ (bottcherCoord c) U := fun z hz => hφanA z (hUA hz)
  have hφ₂anU : AnalyticOnNhd ℂ (bottcherCoord c₂) U := fun z hz => hφ₂anA z (hUA hz)
  set a₁ : analyticSubring U :=
    ⟨Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c), bottcherCoord c, hφanU, rfl⟩ with ha₁def
  set a₂ : analyticSubring U :=
    ⟨Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c₂), bottcherCoord c₂, hφ₂anU, rfl⟩
    with ha₂def
  refine ⟨a₁, a₂, rfl, rfl, ?_⟩
  intro d
  set lr : ℝ := Real.log rlo' with hlrdef
  have hlrh : h < lr := by
    rw [hlrdef]
    linarith [hlow18']
  set ra : ℝ := Real.exp ((3 * lr + 2 * h) / 4) with hradef
  set rb : ℝ := Real.exp ((lr + 2 * h) / 2) with hrbdef
  set RW : ℝ := Real.exp (7 * h / 2) with hRWdef
  have hlrbound : lr < 3 * h / 2 := by
    rw [hlrdef]
    exact hlr'32
  have hrlo'exp : rlo' = Real.exp lr := (Real.exp_log hrlo'pos).symm
  have hR₀exp : R₀ = Real.exp (Real.log R₀) := (Real.exp_log (by
    nlinarith [Real.exp_pos (4 * h + 2), hMR₀])).symm
  have hra : rlo' < ra := by
    rw [hradef, hrlo'exp]
    apply Real.exp_lt_exp.mpr
    linarith
  have hrb : ra < rb := by
    rw [hradef, hrbdef]
    apply Real.exp_lt_exp.mpr
    linarith
  have hrbRW : rb < RW := by
    rw [hrbdef, hRWdef]
    apply Real.exp_lt_exp.mpr
    linarith
  have hRWR : RW < R₀ := by
    rw [hRWdef, hR₀exp]
    apply Real.exp_lt_exp.mpr
    linarith
  have hrb14 : Real.log rb ≤ 2 * h - 1/4 := by
    rw [hrbdef, Real.log_exp]
    linarith
  have hraRW : ra ^ 2 < RW := by
    rw [hradef, hRWdef, ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    push_cast
    linarith
  have hRW12 : Real.log RW ≤ 4 * h - 1/2 := by
    rw [hRWdef, Real.log_exp]
    linarith
  have hra54 : 5 * h / 4 ≤ Real.log ra := by
    rw [hradef, Real.log_exp]
    linarith
  have hRW72 : Real.log RW ≤ 7 * h / 2 := by
    rw [hRWdef, Real.log_exp]
  have hgap' : Real.exp (2 * Real.log rlo') < RW := by
    rw [hRWdef]
    apply Real.exp_lt_exp.mpr
    linarith [hlr'32]
  set k : ℕ := d + 1 with hkdef
  have havoid0 := hθwin ra RW hra (lt_trans hrb hrbRW) hRWR
  have havoid : ∀ v ∈ arcAnnulus ra RW (θsN + Real.pi / 8)
      (θsN + 2 * Real.pi - Real.pi / 8), S'.T v ∉ Metric.closedBall c (s ^ 2) := by
    rw [hshiftN]
    exact havoid0
  have hconnN : ChainOverlapsConnected c S' ra rb RW θsN :=
    chainOverlapsConnected_of_normalized S' hrlo'1 hra hrb hrbRW hraRW hRWR hh0
      hra54 hRW72 hθNlo hθNhi
  obtain ⟨Ext, SL, hExto, hExtc, hP0Ext, hreach, hlevels, hnorm, hSLan, hSLit, hSLlev,
    hSLExt, m, Φ, hΦan, hΦpow, hΦne⟩ :=
    exists_tower_ext_slit_s_withRoot S' hrlo'1 hc100 hh1 hlow18' hra hrb hrbRW hRWR
      hra54 hrb14 hraRW hRW12 hRW72 hs2 hs40 hθN1 hθN2 havoid hc₂2 hsc₂ hsurj' hgap'
      hconnN k (by omega)
  obtain ⟨F, hFan, hFne, hFtop, hFbr⟩ :=
    exists_tower_radicand S' hrlo'1 k hExto hreach
  set F' : ℂ → ℂ := fun z => if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z
    with hF'def
  have hBmin2h : Real.exp (2 * h + 2) < Bmin := by
    refine lt_of_le_of_lt ?_ hBmin4h
    apply Real.exp_le_exp.mpr
    linarith
  have hG2hfar : ∀ z : ℂ, Bmin < ‖z‖ → 2 * h < greenFunctionDyn c z := by
    intro z hzfar
    apply green_far_gt c (2 * h) z
    apply max_lt
    · exact lt_trans hBminc3 hzfar
    · exact lt_trans hBmin2h hzfar
  have hzP0far : ∀ z ∈ Ext, Bmin < ‖z‖ → z ∈ S'.T '' annulusSet rlo' R₀ := by
    intro z hz hzfar
    rcases hlevels z hz with h1 | h1
    · exact h1
    · have := hG2hfar z hzfar
      linarith
  have hoverlap : ∀ z ∈ Ext, Bmin < ‖z‖ → F z = bottcherCoord c z ^ (2 ^ k) := by
    intro z hz hzfar
    have hzP0 := hzP0far z hz hzfar
    have h1 := hFtop z hzP0
    obtain ⟨w, hw, rfl⟩ := hzP0
    have h2 : S'.inv (S'.T w) = w := S'.inv_left hw
    have hwfar : Rb < ‖w‖ := by
      have h3 : Real.log Rb < Real.log ‖w‖ := by
        rw [← S'.level w hw]
        exact hGfar _ hzfar
      have h4 : (0:ℝ) < ‖w‖ := lt_trans (by linarith) hw.1
      calc Rb = Real.exp (Real.log Rb) := (Real.exp_log (by nlinarith)).symm
        _ < Real.exp (Real.log ‖w‖) := Real.exp_lt_exp.mpr h3
        _ = ‖w‖ := Real.exp_log h4
    have h3 : bottcherCoord c (S'.T w) = w := hfar' w hwfar hw.2
    rw [h1, h2, h3]
  set Ext' : Set ℂ := Ext ∪ Afar with hExt'def
  have hExt'o : IsOpen Ext' := hExto.union hAfaro
  have hover : (Ext ∩ Afar).Nonempty := by
    set w₀ : ℂ := ((Bmin * Real.exp 2 : ℝ) : ℂ) with hw₀def
    have hnw₀ : ‖w₀‖ = Bmin * Real.exp 2 := by
      rw [hw₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hexp2 : (1:ℝ) < Real.exp 2 := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    have hRaw₀ : Ra < ‖w₀‖ := by
      rw [hnw₀]
      have h1 : Ra = Real.exp (Real.log Ra) := (Real.exp_log (by linarith)).symm
      have h4 : Ra < Bmin := by
        rw [h1]
        linarith [hBminRb, Real.exp_lt_exp.mpr (show Real.log Ra < Real.log Ra + 2 by linarith)]
      calc Ra < Bmin := h4
        _ = Bmin * 1 := (mul_one _).symm
        _ < Bmin * Real.exp 2 := mul_lt_mul_of_pos_left hexp2 hBminpos
    have hw₀R₀ : ‖w₀‖ < R₀ := by
      rw [hnw₀]
      have h1 : Real.exp 2 < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)
      calc Bmin * Real.exp 2 < Bmin * Real.exp 3 :=
            mul_lt_mul_of_pos_left h1 hBminpos
        _ < R₀ := hBminR₀
    have hrlo'w₀ : rlo' < ‖w₀‖ := by
      rw [hnw₀]
      have h1 : rlo' < Real.exp (4 * h + 2) :=
        lt_trans hrlo'lt (Real.exp_lt_exp.mpr (by linarith))
      calc rlo' < Real.exp (4 * h + 2) := h1
        _ < Bmin := hBmin4h
        _ = Bmin * 1 := (mul_one _).symm
        _ < Bmin * Real.exp 2 := mul_lt_mul_of_pos_left hexp2 hBminpos
    have hw₀ann : w₀ ∈ annulusSet rlo' R₀ := ⟨hrlo'w₀, hw₀R₀⟩
    refine ⟨S'.T w₀, hP0Ext ⟨w₀, hw₀ann, rfl⟩, ?_⟩
    show Bmin < ‖S'.T w₀‖
    obtain ⟨hφid, hesc, hRinj⟩ := hfar w₀ hRaw₀ hw₀R₀
    have hcrude1 : ‖c‖ ≤ ‖S'.T w₀‖ := by
      have h1 : max 2 ‖c‖ < ‖S'.T w₀‖ := hesc
      exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) h1)
    have hcrude2 : (2:ℝ) < ‖S'.T w₀‖ :=
      lt_of_le_of_lt (le_max_left _ _) hesc
    have hGle := greenFunctionDyn_le_crude hcrude1 hcrude2
    have hGval : greenFunctionDyn c (S'.T w₀) = Real.log ‖w₀‖ := S'.level w₀ hw₀ann
    have hlogw₀ : Real.log ‖w₀‖ = Real.log Bmin + 2 := by
      rw [hnw₀, Real.log_mul (by positivity) (by positivity), Real.log_exp]
    have h4 : Real.log Bmin + 1 ≤ Real.log ‖S'.T w₀‖ := by
      rw [hGval, hlogw₀] at hGle
      linarith
    calc Bmin = Real.exp (Real.log Bmin) := (Real.exp_log hBminpos).symm
      _ < Real.exp (Real.log Bmin + 1) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ Real.exp (Real.log ‖S'.T w₀‖) := Real.exp_le_exp.mpr h4
      _ = ‖S'.T w₀‖ := Real.exp_log (by linarith)
  have hExt'c : IsConnected Ext' := by
    obtain ⟨z, hz1, hz2⟩ := hover
    exact IsConnected.union ⟨z, hz1, hz2⟩ hExtc hAfarconn
  have hF'an : AnalyticOnNhd ℂ F' Ext' := by
    intro z hz
    rcases hz with hzE | hzA
    · have hev : F' =ᶠ[nhds z] F := by
        filter_upwards [hExto.mem_nhds hzE] with z' hz'
        show (if Bmin < ‖z'‖ then bottcherCoord c z' ^ (2 ^ k) else F z') = F z'
        by_cases hf : Bmin < ‖z'‖
        · rw [if_pos hf, ← hoverlap z' hz' hf]
        · rw [if_neg hf]
      exact (hFan z hzE).congr hev.symm
    · have hev : F' =ᶠ[nhds z] (fun z' => bottcherCoord c z' ^ (2 ^ k)) := by
        filter_upwards [hAfaro.mem_nhds hzA] with z' hz'
        exact if_pos hz'
      exact ((hφanA z hzA).pow _).congr hev.symm
  have hF'ne : ∀ z ∈ Ext', F' z ≠ 0 := by
    intro z hz
    show (if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z) ≠ 0
    by_cases hf : Bmin < ‖z‖
    · rw [if_pos hf]
      exact pow_ne_zero _ (bottcherCoord_ne_zero c z)
    · rw [if_neg hf]
      rcases hz with hzE | hzA
      · exact hFne z hzE
      · exact absurd hzA hf
  -- the glued second coordinate over the far green-superlevel region
  set tE : ℝ := max (2 * h) (bottcherBallBound c) with htEdef
  set Efar : Set ℂ := {z : ℂ | tE < greenFunctionDyn c z} with hEfardef
  have hEfaro : IsOpen Efar := isOpen_lt continuous_const (continuous_greenFunctionDyn c)
  have hAfarE : Afar ⊆ Efar := by
    intro z hz
    have hzfar : Bmin < ‖z‖ := hz
    show tE < greenFunctionDyn c z
    rw [htEdef]
    apply max_lt
    · exact hG2hfar z hzfar
    · apply green_far_gt c (bottcherBallBound c) z
      apply max_lt
      · exact lt_trans hBminc3 hzfar
      · exact lt_trans hBminBB hzfar
  have hEfarEsc₂ : Efar ⊆ escapeOpen c₂ := by
    intro z hz
    have h1 : bottcherBallBound c < greenFunctionDyn c z :=
      lt_of_le_of_lt (le_max_right _ _) hz
    obtain ⟨h2, _⟩ := far_of_green_gt_ballBound c h1
    show max 2 ‖c₂‖ < ‖z‖
    have h3 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    have h4 : ‖c‖ ≤ max 2 ‖c‖ := le_max_right _ _
    apply max_lt
    · linarith
    · calc ‖c₂‖ ≤ ‖c‖ / 600 := hc₂small
        _ < max 2 ‖c‖ := by linarith
        _ < ‖z‖ := h2
  have hφ₂anE : AnalyticOnNhd ℂ (bottcherCoord c₂) Efar :=
    (analyticOnNhd_bottcherCoord_full c₂).mono hEfarEsc₂
  have hφ₂rootE : ∀ z ∈ Efar, bottcherCoord c₂ z ^ 2 ^ m
      = bottcherCoord c₂ ((quadratic c₂)^[m] z) :=
    fun z hz => (bottcherCoord_iterate_escape (hEfarEsc₂ hz) m).symm
  have hoverΦeq : Efar ∩ Ext = S'.T '' annulusSet (max rlo' (Real.exp tE)) R₀ := by
    ext z
    constructor
    · rintro ⟨hzE, hzX⟩
      have hzP0 : z ∈ S'.T '' annulusSet rlo' R₀ := by
        rcases hlevels z hzX with h1 | h1
        · exact h1
        · have h2 : 2 * h < greenFunctionDyn c z :=
            lt_of_le_of_lt (le_max_left _ _) hzE
          linarith
      obtain ⟨w, hw, rfl⟩ := hzP0
      refine ⟨w, ⟨?_, hw.2⟩, rfl⟩
      apply max_lt
      · exact hw.1
      · have h3 : tE < Real.log ‖w‖ := by
          rw [← S'.level w hw]
          exact hzE
        have h4 : (0:ℝ) < ‖w‖ := lt_trans (by linarith) hw.1
        calc Real.exp tE < Real.exp (Real.log ‖w‖) := Real.exp_lt_exp.mpr h3
          _ = ‖w‖ := Real.exp_log h4
    · rintro ⟨w, hw, rfl⟩
      have hwann : w ∈ annulusSet rlo' R₀ :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hw.1, hw.2⟩
      refine ⟨?_, hP0Ext ⟨w, hwann, rfl⟩⟩
      show tE < greenFunctionDyn c (S'.T w)
      rw [S'.level w hwann]
      have h4 : Real.exp tE < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hw.1
      calc tE = Real.log (Real.exp tE) := (Real.log_exp tE).symm
        _ < Real.log ‖w‖ := Real.log_lt_log (Real.exp_pos _) h4
  have hoverΦconn : IsPreconnected (Efar ∩ Ext) := by
    rw [hoverΦeq]
    by_cases hne : max rlo' (Real.exp tE) < R₀
    · have hpos : (0:ℝ) < max rlo' (Real.exp tE) :=
        lt_of_lt_of_le (Real.exp_pos tE) (le_max_right _ _)
      exact (isConnected_annulus hpos hne).isPreconnected.image _
        ((S'.an.mono (fun w hw =>
          ⟨lt_of_le_of_lt (le_max_left _ _) hw.1, hw.2⟩)).continuousOn)
    · have hempty : annulusSet (max rlo' (Real.exp tE)) R₀ = ∅ := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        exact hne (lt_trans h1 h2)
      rw [hempty, Set.image_empty]
      exact isPreconnected_empty
  obtain ⟨Φ', hΦ'an, hΦ'pow, hΦ'ne, hΦ'far⟩ :=
    glue_pow_root_pair hEfaro hExto hoverΦconn Nat.one_le_two_pow
      (fun z _ => bottcherCoord_ne_zero c₂ ((quadratic c₂)^[m] z))
      hφ₂anE hφ₂rootE hΦan hΦpow
  have hExt'sub : Ext' ⊆ Efar ∪ Ext := by
    rw [hExt'def]
    rintro z (hz | hz)
    · exact Or.inr hz
    · exact Or.inl (hAfarE hz)
  have hΦ'anExt' : AnalyticOnNhd ℂ Φ' Ext' := hΦ'an.mono hExt'sub
  have hΦ'neExt' : ∀ z ∈ Ext', Φ' z ≠ 0 := fun z hz => hΦ'ne z (hExt'sub hz)
  set aExt : analyticSubring Ext' :=
    ⟨Filter.Germ.coeRingHom (𝓟 Ext') F', F', hF'an, rfl⟩ with haExtdef
  set GBExt : analyticSubring Ext' :=
    ⟨Filter.Germ.coeRingHom (𝓟 Ext') Φ', Φ', hΦ'anExt', rfl⟩ with hGBdef
  have hUExt' : U ⊆ Ext' := fun z hz => Or.inr (hUA hz)
  have hEqOn' : Set.EqOn F' (fun z => bottcherCoord c z ^ (2 ^ k)) U := by
    intro z hz
    show (if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z) = _
    rw [if_pos (hUfar z hz)]
  have hEqOnGB : Set.EqOn Φ' (bottcherCoord c₂) U :=
    fun z hz => hΦ'far (hAfarE (hUA hz))
  refine ⟨Ext', hExt'o, hExt'c, hUinf.mono hUExt', hUExt', F', aExt, GBExt, k, ?_, ?_,
    hF'an, hF'ne, rfl, ?_, ?_, ?_⟩
  · omega
  · calc d < 2 ^ d := Nat.lt_two_pow_self
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  · apply Subtype.ext
    have hL : ((restrictAnalytic hUExt' aExt : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) F' := by
      show ((aExt : Filter.Germ (𝓟 Ext') ℂ).compTendsto id
        (Filter.tendsto_principal_principal.mpr (fun x hx => hUExt' hx))) = _
      have h1 : (aExt : Filter.Germ (𝓟 Ext') ℂ)
          = Filter.Germ.coeRingHom (𝓟 Ext') F' := rfl
      rw [h1]
      show ((F' : Filter.Germ (𝓟 Ext') ℂ).compTendsto id _) = (F' : Filter.Germ (𝓟 U) ℂ)
      rw [Filter.Germ.coe_compTendsto]
      rfl
    have hR : (((a₁ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) (fun z => bottcherCoord c z ^ (2 ^ k)) := by
      have h1 : (((a₁ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
          = ((a₁ : Filter.Germ (𝓟 U) ℂ)) ^ (2 ^ k) := by
        push_cast
        rfl
      rw [h1]
      have h2 : (a₁ : Filter.Germ (𝓟 U) ℂ)
          = Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c) := rfl
      rw [h2, ← map_pow]
      rfl
    rw [hL, hR]
    have hev : (F' : ℂ → ℂ) =ᶠ[𝓟 U] (fun z => bottcherCoord c z ^ (2 ^ k)) :=
      Filter.eventually_principal.mpr hEqOn'
    exact Filter.Germ.coe_eq.mpr hev
  · apply Subtype.ext
    have hL : ((restrictAnalytic hUExt' GBExt : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) Φ' := by
      show ((GBExt : Filter.Germ (𝓟 Ext') ℂ).compTendsto id
        (Filter.tendsto_principal_principal.mpr (fun x hx => hUExt' hx))) = _
      have h1 : (GBExt : Filter.Germ (𝓟 Ext') ℂ)
          = Filter.Germ.coeRingHom (𝓟 Ext') Φ' := rfl
      rw [h1]
      show ((Φ' : Filter.Germ (𝓟 Ext') ℂ).compTendsto id _) = (Φ' : Filter.Germ (𝓟 U) ℂ)
      rw [Filter.Germ.coe_compTendsto]
      rfl
    rw [hL]
    have hev : (Φ' : ℂ → ℂ) =ᶠ[𝓟 U] (bottcherCoord c₂ : ℂ → ℂ) :=
      Filter.eventually_principal.mpr hEqOnGB
    exact Filter.Germ.coe_eq.mpr hev
  · intro T hT
    obtain ⟨γ, γ', hγExt, hγc, hγ'c, hγd, hγcl, hγT, hγwind⟩ :=
      exists_tower_loop S' hrlo'1 k hra hrb (lt_trans hrbRW hRWR) hSLan hSLit hSLlev
        hSLExt hFan hFbr T hT
    refine ⟨γ, γ', 0, fun θ => Or.inl (hγExt θ), hγc, hγ'c, hγd, hγcl, hγT, ?_⟩
    have hcongr : ∀ θ : ℝ, logDeriv F' (γ θ) * γ' θ = logDeriv F (γ θ) * γ' θ := by
      intro θ
      congr 1
      apply logDeriv_congr_of_eventuallyEq
      filter_upwards [hExto.mem_nhds (hγExt θ)] with z' hz'
      show (if Bmin < ‖z'‖ then bottcherCoord c z' ^ (2 ^ k) else F z') = F z'
      by_cases hf : Bmin < ‖z'‖
      · rw [if_pos hf, ← hoverlap z' hz' hf]
      · rw [if_neg hf]
    rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
    exact hγwind

end Bottcher

