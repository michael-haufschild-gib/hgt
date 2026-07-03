/-
# The norm-bounded mixed tower data (task B8 close)

For a disconnected parameter with `‖c‖ ≥ 1000`, the far tower-data package of
`bottcher_towerDataG_far` is rebuilt with the norm floor `∀ z ∈ Ext, 2 < ‖z‖`:

* the deep section of `exists_tower_deep_of_anchor` is raised to inner radius
  `max rlo e^{G_c(0) + 1/8}` (`TowerSection.restrictLo`), clearing the `closedBall 0 2`
  pinch band from above;
* `exists_slit_center_avoiding_patch` supplies the slit angle whose wedge window avoids the
  critical-value ball, and `exists_tower_ext_slit` builds the extension domain on that wedge
  with the piecewise norm floor;
* the far region `{Bmin < ‖z‖}` glued on top is beyond `2` trivially.

`q62_phiMero_mixed_far` then instantiates the mixed capstone
`q62_phiMero_mixed_of_normBoundedTower`: for every disconnected `c₁` with `‖c₁‖ ≥ 1000` and
every connected `c₂ ∈ M ∖ {0, −2}`, the two Böttcher coordinates satisfy no algebraic relation
over `ℂ(z)` on a common far domain.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.MixedTowerExt
import GaloisForLFunctions.Bottcher.PatchSquareLocalize
import GaloisForLFunctions.Bottcher.MixedPairCapstone
import GaloisForLFunctions.Bottcher.Rigidity

open Complex Set Filter Metric
open scoped Topology

namespace Bottcher

set_option maxHeartbeats 1600000 in
/-- **Norm-bounded tower data on an arbitrary far domain** (`‖c‖ ≥ 1000`).  As
`bottcher_towerDataG_far`, with the green-positivity and orbit clauses replaced by the norm
floor `∀ z ∈ Ext, 2 < ‖z‖` — the exact geometric input of the mixed q62 capstone. -/
theorem bottcher_towerDataG_mixed (c : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) :
    ∃ Bmin : ℝ, 1 < Bmin ∧
    ∀ (U : Set ℂ), IsOpen U → IsPreconnected U → U.Nonempty → U.Infinite →
      (∀ z ∈ U, Bmin < ‖z‖) →
      ∃ a₂ : analyticSubring U,
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₂ ^ (2 ^ k) ∧
        (∀ z ∈ Ext, 2 < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have hh0 : 0 < h := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c 0) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c 0).mp h1.symm) hc
  -- effective size of the critical level: `2h = log ‖c‖ ± 1/8` and `log ‖c‖ ≥ 6`
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
  -- the far cut, from the anchor and c alone; strict beyond every crude threshold
  set Bmin : ℝ := max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
    (max (Real.exp (4 * h + 2)) 2) + 1 with hBmindef
  have hBmin1 : (1:ℝ) < Bmin := by
    have h1 : (2:ℝ) ≤ max (Real.exp (4 * h + 2)) 2 := le_max_right _ _
    have h2 : max (Real.exp (4 * h + 2)) 2
        ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2))) (max (Real.exp (4 * h + 2)) 2) :=
      le_max_right _ _
    rw [hBmindef]
    linarith
  have hBminc3 : ‖c‖ + 3 < Bmin := by
    have h1 : ‖c‖ + 3 ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBminRb : Real.exp (Real.log Ra + 2) < Bmin := by
    have h1 : Real.exp (Real.log Ra + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBmin4h : Real.exp (4 * h + 2) < Bmin := by
    have h1 : Real.exp (4 * h + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_left _ _) (le_max_right _ _)
    rw [hBmindef]
    linarith
  have hBminpos : (0:ℝ) < Bmin := by linarith
  have hBmin2 : (2:ℝ) < Bmin := by
    have h1 : (2:ℝ) ≤ max (Real.exp (4 * h + 2)) 2 := le_max_right _ _
    have h2 : max (Real.exp (4 * h + 2)) 2
        ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2))) (max (Real.exp (4 * h + 2)) 2) :=
      le_max_right _ _
    rw [hBmindef]
    linarith
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
  -- points beyond Bmin have Green value above log Rb, and are crude-escaping
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
  -- raise the inner radius to clear the ball-2 pinch band
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
  -- restricted far identity and band surjectivity
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
  -- the slit center avoiding the critical-value ball
  have hrlo_ceiling : Real.log rlo' ≤ (Real.log (‖c‖ ^ 2 + ‖c‖) + 1) / 2 := by
    have h1 : Real.log (‖c‖ ^ 2) ≤ Real.log (‖c‖ ^ 2 + ‖c‖) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [h2h.2, hlr'32, hh0]
  have hrlo2h : Real.log rlo' < 2 * h - 1/4 := by linarith [hlr'32, hh1]
  have hR₀4h : 4 * h + 1 < Real.log R₀ := by linarith [hlogR₀]
  obtain ⟨θs, hθs1, hθs2, hθwin⟩ :=
    exists_slit_center_avoiding_patch S' hc1000 hrlo'1 hRa1 hRbR₀ hfar' hrlo_ceiling
      hrlo2h hR₀4h hsurj'
  refine ⟨Bmin, hBmin1, ?_⟩
  intro U hUo hUc hUne hUinf hUfar
  have hUA : U ⊆ Afar := fun z hz => hUfar z hz
  have hφanU : AnalyticOnNhd ℂ (bottcherCoord c) U := fun z hz => hφanA z (hUA hz)
  set a₂ : analyticSubring U :=
    ⟨Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c), bottcherCoord c, hφanU, rfl⟩ with ha₂def
  refine ⟨a₂, rfl, ?_⟩
  intro d
  -- the working radii, exactly as in `bottcher_towerDataG_far`, over the raised inner level
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
  set k : ℕ := d + 1 with hkdef
  have havoid := hθwin ra RW hra (lt_trans hrb hrbRW) hRWR
  obtain ⟨Ext, SL, hExto, hExtc, hP0Ext, hreach, hlevels, hnorm, horbit, hSLan, hSLit, hSLlev,
    hSLdne, hSLExt, _hSLinj⟩ :=
    exists_tower_ext_slit S' hrlo'1 hc100 hh1 hlow18' hra hrb hrbRW hRWR hrb14 hraRW hRW12
      hθs1 hθs2 havoid k
  obtain ⟨F, hFan, hFne, hFtop, hFbr⟩ :=
    exists_tower_radicand S' hrlo'1 k hExto hreach
  -- the far-glued radicand
  set F' : ℂ → ℂ := fun z => if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z
    with hF'def
  -- agreement on the overlap: far Ext-points are far tower-image points
  have hBmin2h : Real.exp (2 * h + 2) < Bmin := by
    refine lt_of_le_of_lt ?_ hBmin4h
    apply Real.exp_le_exp.mpr
    linarith
  have hoverlap : ∀ z ∈ Ext, Bmin < ‖z‖ → F z = bottcherCoord c z ^ (2 ^ k) := by
    intro z hz hzfar
    have hG2h : 2 * h < greenFunctionDyn c z := by
      apply green_far_gt c (2 * h) z
      apply max_lt
      · exact lt_trans hBminc3 hzfar
      · exact lt_trans hBmin2h hzfar
    have hzP0 : z ∈ S'.T '' annulusSet rlo' R₀ := by
      rcases hlevels z hz with h1 | h1
      · exact h1
      · linarith
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
  -- the far-glued extended domain
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
      have h2 : Real.exp (Real.log Ra) < Real.exp (Real.log Ra + 2) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h4 : Ra < Bmin := by
        rw [h1]
        linarith [hBminRb]
      calc Ra < Bmin := h4
        _ = Bmin * 1 := (mul_one _).symm
        _ < Bmin * Real.exp 2 := by
            exact mul_lt_mul_of_pos_left hexp2 hBminpos
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
    have h5 : Bmin < ‖S'.T w₀‖ := by
      calc Bmin = Real.exp (Real.log Bmin) := (Real.exp_log hBminpos).symm
        _ < Real.exp (Real.log Bmin + 1) := Real.exp_lt_exp.mpr (by linarith)
        _ ≤ Real.exp (Real.log ‖S'.T w₀‖) := Real.exp_le_exp.mpr h4
        _ = ‖S'.T w₀‖ := Real.exp_log (by linarith)
    exact h5
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
  set aExt : analyticSubring Ext' :=
    ⟨Filter.Germ.coeRingHom (𝓟 Ext') F', F', hF'an, rfl⟩ with haExtdef
  have hUExt' : U ⊆ Ext' := fun z hz => Or.inr (hUA hz)
  have hEqOn' : Set.EqOn F' (fun z => bottcherCoord c z ^ (2 ^ k)) U := by
    intro z hz
    show (if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z) = _
    rw [if_pos (hUfar z hz)]
  have hnorm' : ∀ z ∈ Ext', 2 < ‖z‖ := by
    rintro z (hzE | hzA)
    · exact hnorm z hzE
    · have h1 : Bmin < ‖z‖ := hzA
      linarith
  refine ⟨Ext', hExt'o, hExt'c, hUinf.mono hUExt', hUExt', F', aExt, k, ?_, ?_, hF'an, hF'ne,
    rfl, ?_, hnorm', ?_⟩
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
    have hR : (((a₂ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) (fun z => bottcherCoord c z ^ (2 ^ k)) := by
      have h1 : (((a₂ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
          = ((a₂ : Filter.Germ (𝓟 U) ℂ)) ^ (2 ^ k) := by
        push_cast
        rfl
      rw [h1]
      have h2 : (a₂ : Filter.Germ (𝓟 U) ℂ)
          = Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c) := rfl
      rw [h2, ← map_pow]
      rfl
    rw [hL, hR]
    have hev : (F' : ℂ → ℂ) =ᶠ[𝓟 U] (fun z => bottcherCoord c z ^ (2 ^ k)) :=
      Filter.eventually_principal.mpr hEqOn'
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
namespace Bottcher

/-- The far radius beyond which every domain carries the norm-bounded mixed tower data. -/
noncomputable def bottcherMixedBound (c : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) : ℝ :=
  (bottcher_towerDataG_mixed c hc hc1000).choose

theorem one_lt_bottcherMixedBound (c : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) : 1 < bottcherMixedBound c hc hc1000 :=
  (bottcher_towerDataG_mixed c hc hc1000).choose_spec.1

theorem bottcherMixedBound_spec (c : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) :
    ∀ (U : Set ℂ), IsOpen U → IsPreconnected U → U.Nonempty → U.Infinite →
      (∀ z ∈ U, bottcherMixedBound c hc hc1000 < ‖z‖) →
      ∃ a₂ : analyticSubring U,
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₂ ^ (2 ^ k) ∧
        (∀ z ∈ Ext, 2 < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) :=
  (bottcher_towerDataG_mixed c hc hc1000).choose_spec.2

/-- **Mixed q62, far disconnected parameter.**  For every disconnected `c₁` with
`‖c₁‖ ≥ 1000` and every connected `c₂ ∈ M ∖ {0, −2}`, the two Böttcher coordinates satisfy no
algebraic relation over `ℂ(z)` on a common far domain. -/
theorem q62_phiMero_mixed_far {c₁ c₂ : ℂ} (hc₁ : (0:ℂ) ∉ filledJulia c₁)
    (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  classical
  set B : ℝ := bottcherMixedBound c₁ hc₁ hc1000 with hBdef
  have hB1 : 1 < B := one_lt_bottcherMixedBound c₁ hc₁ hc1000
  set BU : ℝ := B + ‖c₁‖ + 2 with hBUdef
  have hBU1 : 1 < BU := by
    have := norm_nonneg c₁
    rw [hBUdef]
    linarith
  have hBU2 : BU < 2 * BU := by linarith
  set U : Set ℂ := annulusSet BU (2 * BU) with hUdef
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
  have hUB : ∀ z ∈ U, B < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have := norm_nonneg c₁
    rw [hBUdef] at h1
    linarith
  have hU2lt : ∀ z ∈ U, 2 < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have := norm_nonneg c₁
    rw [hBUdef] at h1
    linarith
  have hU₁ : U ⊆ escapeOpen c₁ := by
    rintro z ⟨h1, _⟩
    show max 2 ‖c₁‖ < ‖z‖
    rw [hBUdef] at h1
    apply max_lt
    · linarith
    · linarith
  have hU₂ : U ⊆ escapeOpen c₂ :=
    subset_escapeOpen_of_two_lt_of_mem_mandelbrot hc₂M hU2lt
  obtain ⟨a₂, ha₂, hdata⟩ := bottcherMixedBound_spec c₁ hc₁ hc1000 U hUo
    hUconn.isPreconnected hUne hUinf hUB
  have ha₂eq : a₂ = phiAnalytic c₁ hU₁ := Subtype.ext (by rw [← ha₂]; rfl)
  refine ⟨U, hUo, hUconn.isPreconnected, hUne, hUinf, hU₁, hU₂, ?_⟩
  apply q62_phiMero_mixed_of_normBoundedTower hUo hUconn.isPreconnected hUne hUinf c₁ c₂
    hU₁ hU₂ hc₂M hc₂0 hc₂2
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hnorm, hloops⟩ := hdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, ?_,
    hnorm, hloops⟩
  rw [hrad, ha₂eq]

end Bottcher

namespace Bottcher

/-- For `‖c‖ ≤ 2`, a set on which `2 < ‖z‖` lies in `escapeOpen c` — the disconnected small-norm
sibling of `subset_escapeOpen_of_two_lt_of_mem_mandelbrot`. -/
theorem subset_escapeOpen_of_two_lt_of_norm_le_two {c : ℂ} (hc : ‖c‖ ≤ 2)
    {S : Set ℂ} (hS : ∀ z ∈ S, 2 < ‖z‖) : S ⊆ escapeOpen c := by
  intro z hz
  simp only [escapeOpen, Set.mem_setOf_eq]
  rw [max_eq_left hc]
  exact hS z hz

/-- **Both-disconnected q62 from a norm-bounded `c₁` scaffold tower, small second parameter.**
As `q62_phiMero_mixed_of_normBoundedTower`, but the second parameter is a *disconnected*
`‖c₂‖ ≤ 2` (transcendence supplied as a hypothesis, e.g. from `bottcher_transcendental_far`):
`escapeOpen c₂ = {2 < ‖z‖}` again contains the tower domain, so `GBExt := φ_{c₂}`-germ.  No
level-compatibility clause. -/
theorem q62_phiMero_pair_of_normBoundedTower
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₂2 : ‖c₂‖ ≤ 2)
    (hGtr₂ : haveI := isDomain_analyticSubring U hUo hUc hUne
             haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
             Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (towerScaffold : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = (phiAnalytic c₁ hU₁) ^ (2 ^ k) ∧
        (∀ z ∈ Ext, 2 < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hF₁ : phiMero c₁ hU₁ ≠ 0 := phiMero_ne_zero hUo hUc hUne hU₁
  apply q62_disconnected_of_towerData hUo hUc hUne hUinf
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) hF₁ hGtr₂
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hnorm, hloops⟩ := towerScaffold d
  have hExtesc : Ext ⊆ escapeOpen c₂ :=
    subset_escapeOpen_of_two_lt_of_norm_le_two hc₂2 hnorm
  exact ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, phiAnalytic c₂ hExtesc, k, hk1, hdk,
    hFan, hFne, hae, hrad, restrictAnalytic_phiAnalytic hUExt c₂ hExtesc hU₂, hloops⟩

/-- **Both-disconnected q62, far first × small second parameter.**  For disconnected `c₁` with
`‖c₁‖ ≥ 1000` and disconnected `c₂` with `‖c₂‖ ≤ 2`, the two Böttcher coordinates satisfy no
algebraic relation over `ℂ(z)` on a common far domain — a region of the disconnected pair space
beyond the level-compatible hypothesis of `bottcher_towerDataF_pair`, closed unconditionally by
the norm-bounded tower. -/
theorem q62_phiMero_pair_far_smallSecond {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc₂2 : ‖c₂‖ ≤ 2) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  classical
  set B : ℝ := bottcherMixedBound c₁ hc₁ hc1000 with hBdef
  have hB1 : 1 < B := one_lt_bottcherMixedBound c₁ hc₁ hc1000
  set FB : ℝ := bottcherFarBound c₂ hc₂ with hFBdef
  have hFB1 : 1 < FB := one_lt_bottcherFarBound c₂ hc₂
  set BU : ℝ := B + FB + ‖c₁‖ + 2 with hBUdef
  have hBU1 : 1 < BU := by
    have := norm_nonneg c₁
    rw [hBUdef]
    linarith
  have hBU2 : BU < 2 * BU := by linarith
  set U : Set ℂ := annulusSet BU (2 * BU) with hUdef
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
  have hUB : ∀ z ∈ U, B < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have := norm_nonneg c₁
    rw [hBUdef] at h1
    linarith
  have hUFB : ∀ z ∈ U, FB < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have := norm_nonneg c₁
    rw [hBUdef] at h1
    linarith
  have hU2lt : ∀ z ∈ U, 2 < ‖z‖ := by
    rintro z ⟨h1, _⟩
    have := norm_nonneg c₁
    rw [hBUdef] at h1
    linarith
  have hU₁ : U ⊆ escapeOpen c₁ := by
    rintro z ⟨h1, _⟩
    show max 2 ‖c₁‖ < ‖z‖
    rw [hBUdef] at h1
    apply max_lt
    · linarith
    · linarith
  have hU₂ : U ⊆ escapeOpen c₂ :=
    subset_escapeOpen_of_two_lt_of_norm_le_two hc₂2 hU2lt
  obtain ⟨a₁', ha₁', hdata⟩ := bottcherMixedBound_spec c₁ hc₁ hc1000 U hUo
    hUconn.isPreconnected hUne hUinf hUB
  have ha₁eq : a₁' = phiAnalytic c₁ hU₁ := Subtype.ext (by rw [← ha₁']; rfl)
  have hGtr₂ : haveI := isDomain_analyticSubring U hUo hUconn.isPreconnected hUne
               haveI := (ratfuncToMero U hUo hUconn.isPreconnected hUne hUinf).toAlgebra
               Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    bottcher_transcendental_far c₂ hc₂ hUo hUconn.isPreconnected hUne hUinf hUFB
      (a₂ := phiAnalytic c₂ hU₂) rfl
  refine ⟨U, hUo, hUconn.isPreconnected, hUne, hUinf, hU₁, hU₂, ?_⟩
  apply q62_phiMero_pair_of_normBoundedTower hUo hUconn.isPreconnected hUne hUinf c₁ c₂
    hU₁ hU₂ hc₂2 hGtr₂
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hnorm, hloops⟩ := hdata d
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, ?_,
    hnorm, hloops⟩
  rw [hrad, ha₁eq]

end Bottcher

namespace Bottcher

/-- **Mixed q62, swapped orientation**: connected `c₁ ∈ M ∖ {0, −2}` × disconnected `c₂` with
`‖c₂‖ ≥ 1000`, by `noRelation_symm`. -/
theorem q62_phiMero_mixed_far_swapped {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₂', hU₁', hNR⟩ :=
    q62_phiMero_mixed_far hc₂ hc1000 hc₁M hc₁0 hc₁2
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁', hU₂', ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_symm hNR

/-- **Both-disconnected q62, swapped orientation**: disconnected `‖c₁‖ ≤ 2` × disconnected
`‖c₂‖ ≥ 1000`, by `noRelation_symm`. -/
theorem q62_phiMero_pair_far_smallFirst {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc₁2 : ‖c₁‖ ≤ 2)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₂', hU₁', hNR⟩ :=
    q62_phiMero_pair_far_smallSecond hc₂ hc1000 hc₁ hc₁2
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁', hU₂', ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_symm hNR

end Bottcher

namespace Bottcher

set_option maxHeartbeats 1600000 in
/-- **`s`-norm-bounded tower data on an arbitrary far domain.**  As
`bottcher_towerDataG_mixed`, with the norm floor raised to `∀ z ∈ Ext, s < ‖z‖`
(`2 ≤ s`, `s² ≤ ‖c‖/40`, patch-square smallness) — the geometric input for disconnected
second parameters up to norm `s`. -/
theorem bottcher_towerDataG_normS (c : ℂ) (hc : (0:ℂ) ∉ filledJulia c)
    (hc1000 : (1000:ℝ) ≤ ‖c‖) {s : ℝ} (hs2 : 2 ≤ s) (hs40 : s ^ 2 ≤ ‖c‖ / 40)
    (hsmall : 2 * s ^ 2 * ‖c‖ + s ^ 4 + 1 ≤ 1/100 * (‖c‖ ^ 2 - ‖c‖)) :
    ∃ Bmin : ℝ, 1 < Bmin ∧
    ∀ (U : Set ℂ), IsOpen U → IsPreconnected U → U.Nonempty → U.Infinite →
      (∀ z ∈ U, Bmin < ‖z‖) →
      ∃ a₂ : analyticSubring U,
      (Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c)) = (a₂ : Filter.Germ (𝓟 U) ℂ) ∧
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₂ ^ (2 ^ k) ∧
        (∀ z ∈ Ext, s < ‖z‖) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hc100 : (100:ℝ) ≤ ‖c‖ := by linarith
  have hh0 : 0 < h := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c 0) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c 0).mp h1.symm) hc
  -- effective size of the critical level: `2h = log ‖c‖ ± 1/8` and `log ‖c‖ ≥ 6`
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
  -- the far cut, from the anchor and c alone; strict beyond every crude threshold
  set Bmin : ℝ := max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
    (max (Real.exp (4 * h + 2)) 2) + 1 with hBmindef
  have hBmin1 : (1:ℝ) < Bmin := by
    have h1 : (2:ℝ) ≤ max (Real.exp (4 * h + 2)) 2 := le_max_right _ _
    have h2 : max (Real.exp (4 * h + 2)) 2
        ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2))) (max (Real.exp (4 * h + 2)) 2) :=
      le_max_right _ _
    rw [hBmindef]
    linarith
  have hBminc3 : ‖c‖ + 3 < Bmin := by
    have h1 : ‖c‖ + 3 ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBminRb : Real.exp (Real.log Ra + 2) < Bmin := by
    have h1 : Real.exp (Real.log Ra + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hBmindef]
    linarith
  have hBmin4h : Real.exp (4 * h + 2) < Bmin := by
    have h1 : Real.exp (4 * h + 2) ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2)))
        (max (Real.exp (4 * h + 2)) 2) := le_trans (le_max_left _ _) (le_max_right _ _)
    rw [hBmindef]
    linarith
  have hBminpos : (0:ℝ) < Bmin := by linarith
  have hBmin2 : (2:ℝ) < Bmin := by
    have h1 : (2:ℝ) ≤ max (Real.exp (4 * h + 2)) 2 := le_max_right _ _
    have h2 : max (Real.exp (4 * h + 2)) 2
        ≤ max (max (‖c‖ + 3) (Real.exp (Real.log Ra + 2))) (max (Real.exp (4 * h + 2)) 2) :=
      le_max_right _ _
    rw [hBmindef]
    linarith
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
  -- points beyond Bmin have Green value above log Rb, and are crude-escaping
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
  -- raise the inner radius to clear the ball-2 pinch band
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
  -- restricted far identity and band surjectivity
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
  -- the slit center avoiding the critical-value ball
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
  refine ⟨Bmin, hBmin1, ?_⟩
  intro U hUo hUc hUne hUinf hUfar
  have hUA : U ⊆ Afar := fun z hz => hUfar z hz
  have hφanU : AnalyticOnNhd ℂ (bottcherCoord c) U := fun z hz => hφanA z (hUA hz)
  set a₂ : analyticSubring U :=
    ⟨Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c), bottcherCoord c, hφanU, rfl⟩ with ha₂def
  refine ⟨a₂, rfl, ?_⟩
  intro d
  -- the working radii, exactly as in `bottcher_towerDataG_far`, over the raised inner level
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
  set k : ℕ := d + 1 with hkdef
  have havoid := hθwin ra RW hra (lt_trans hrb hrbRW) hRWR
  obtain ⟨Ext, SL, hExto, hExtc, hP0Ext, hreach, hlevels, hnorm, horbit, hSLan, hSLit, hSLlev,
    hSLdne, hSLExt, _hSLinj⟩ :=
    exists_tower_ext_slit_s S' hrlo'1 hc100 hh1 hlow18' hra hrb hrbRW hRWR hrb14 hraRW hRW12
      hs2 hs40 hθs1 hθs2 havoid k
  obtain ⟨F, hFan, hFne, hFtop, hFbr⟩ :=
    exists_tower_radicand S' hrlo'1 k hExto hreach
  -- the far-glued radicand
  set F' : ℂ → ℂ := fun z => if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z
    with hF'def
  -- agreement on the overlap: far Ext-points are far tower-image points
  have hBmin2h : Real.exp (2 * h + 2) < Bmin := by
    refine lt_of_le_of_lt ?_ hBmin4h
    apply Real.exp_le_exp.mpr
    linarith
  have hoverlap : ∀ z ∈ Ext, Bmin < ‖z‖ → F z = bottcherCoord c z ^ (2 ^ k) := by
    intro z hz hzfar
    have hG2h : 2 * h < greenFunctionDyn c z := by
      apply green_far_gt c (2 * h) z
      apply max_lt
      · exact lt_trans hBminc3 hzfar
      · exact lt_trans hBmin2h hzfar
    have hzP0 : z ∈ S'.T '' annulusSet rlo' R₀ := by
      rcases hlevels z hz with h1 | h1
      · exact h1
      · linarith
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
  -- the far-glued extended domain
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
      have h2 : Real.exp (Real.log Ra) < Real.exp (Real.log Ra + 2) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h4 : Ra < Bmin := by
        rw [h1]
        linarith [hBminRb]
      calc Ra < Bmin := h4
        _ = Bmin * 1 := (mul_one _).symm
        _ < Bmin * Real.exp 2 := by
            exact mul_lt_mul_of_pos_left hexp2 hBminpos
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
    have h5 : Bmin < ‖S'.T w₀‖ := by
      calc Bmin = Real.exp (Real.log Bmin) := (Real.exp_log hBminpos).symm
        _ < Real.exp (Real.log Bmin + 1) := Real.exp_lt_exp.mpr (by linarith)
        _ ≤ Real.exp (Real.log ‖S'.T w₀‖) := Real.exp_le_exp.mpr h4
        _ = ‖S'.T w₀‖ := Real.exp_log (by linarith)
    exact h5
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
  set aExt : analyticSubring Ext' :=
    ⟨Filter.Germ.coeRingHom (𝓟 Ext') F', F', hF'an, rfl⟩ with haExtdef
  have hUExt' : U ⊆ Ext' := fun z hz => Or.inr (hUA hz)
  have hEqOn' : Set.EqOn F' (fun z => bottcherCoord c z ^ (2 ^ k)) U := by
    intro z hz
    show (if Bmin < ‖z‖ then bottcherCoord c z ^ (2 ^ k) else F z) = _
    rw [if_pos (hUfar z hz)]
  have hnorm' : ∀ z ∈ Ext', s < ‖z‖ := by
    rintro z (hzE | hzA)
    · exact hnorm z hzE
    · have h1 : Bmin < ‖z‖ := hzA
      have hss : s ≤ s ^ 2 / 2 := by nlinarith
      linarith [hs40, hBminc3, hc100]
  refine ⟨Ext', hExt'o, hExt'c, hUinf.mono hUExt', hUExt', F', aExt, k, ?_, ?_, hF'an, hF'ne,
    rfl, ?_, hnorm', ?_⟩
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
    have hR : (((a₂ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
        = Filter.Germ.coeRingHom (𝓟 U) (fun z => bottcherCoord c z ^ (2 ^ k)) := by
      have h1 : (((a₂ ^ (2 ^ k) : analyticSubring U)) : Filter.Germ (𝓟 U) ℂ)
          = ((a₂ : Filter.Germ (𝓟 U) ℂ)) ^ (2 ^ k) := by
        push_cast
        rfl
      rw [h1]
      have h2 : (a₂ : Filter.Germ (𝓟 U) ℂ)
          = Filter.Germ.coeRingHom (𝓟 U) (bottcherCoord c) := rfl
      rw [h2, ← map_pow]
      rfl
    rw [hL, hR]
    have hev : (F' : ℂ → ℂ) =ᶠ[𝓟 U] (fun z => bottcherCoord c z ^ (2 ^ k)) :=
      Filter.eventually_principal.mpr hEqOn'
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

namespace Bottcher

/-- **Both-disconnected q62, quadratic norm gap.**  For disconnected `c₁, c₂` with
`‖c₁‖ ≥ 1000` and `300·(max 2 ‖c₂‖)² ≤ ‖c₁‖`, the two Böttcher coordinates satisfy no
algebraic relation over `ℂ(z)` on a common far domain — the `s`-norm-bounded tower sweeps the
whole moderate-second band `‖c₂‖ ≲ √(‖c₁‖/300)` beyond the level-compatible locus. -/
theorem q62_phiMero_pair_far_general {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂)
    (hgap : 300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  classical
  set s : ℝ := max 2 ‖c₂‖ with hsdef
  have hs2 : (2:ℝ) ≤ s := le_max_left _ _
  have hs0 : (0:ℝ) < s := by linarith
  have hssq : s ^ 2 ≤ ‖c₁‖ / 300 := by nlinarith
  have hs40 : s ^ 2 ≤ ‖c₁‖ / 40 := by linarith
  have hc₁0 : (0:ℝ) < ‖c₁‖ := by linarith
  have hsmall : 2 * s ^ 2 * ‖c₁‖ + s ^ 4 + 1 ≤ 1/100 * (‖c₁‖ ^ 2 - ‖c₁‖) := by
    have h1 : 2 * s ^ 2 * ‖c₁‖ ≤ 2 / 300 * ‖c₁‖ ^ 2 := by nlinarith
    have h2 : s ^ 4 ≤ ‖c₁‖ ^ 2 / 90000 := by nlinarith [sq_nonneg (s ^ 2)]
    nlinarith [sq_nonneg ‖c₁‖]
  obtain ⟨Bmin, hBmin1, hspec⟩ := bottcher_towerDataG_normS c₁ hc₁ hc1000 hs2 hs40 hsmall
  set FB : ℝ := bottcherFarBound c₂ hc₂ with hFBdef
  have hFB1 : 1 < FB := one_lt_bottcherFarBound c₂ hc₂
  set BU : ℝ := Bmin + FB + s + ‖c₁‖ + 2 with hBUdef
  have hBU1 : 1 < BU := by
    rw [hBUdef]
    linarith
  have hBU2 : BU < 2 * BU := by linarith
  set U : Set ℂ := annulusSet BU (2 * BU) with hUdef
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
  have hUB : ∀ z ∈ U, Bmin < ‖z‖ := by
    rintro z ⟨h1, _⟩
    rw [hBUdef] at h1
    linarith
  have hUFB : ∀ z ∈ U, FB < ‖z‖ := by
    rintro z ⟨h1, _⟩
    rw [hBUdef] at h1
    linarith
  have hUs : ∀ z ∈ U, s < ‖z‖ := by
    rintro z ⟨h1, _⟩
    rw [hBUdef] at h1
    linarith
  have hU₁ : U ⊆ escapeOpen c₁ := by
    rintro z ⟨h1, _⟩
    show max 2 ‖c₁‖ < ‖z‖
    rw [hBUdef] at h1
    apply max_lt
    · linarith
    · linarith
  have hU₂ : U ⊆ escapeOpen c₂ := by
    intro z hz
    show max 2 ‖c₂‖ < ‖z‖
    exact hUs z hz
  obtain ⟨a₁', ha₁', hdata⟩ := hspec U hUo hUconn.isPreconnected hUne hUinf hUB
  have ha₁eq : a₁' = phiAnalytic c₁ hU₁ := Subtype.ext (by rw [← ha₁']; rfl)
  have hGtr₂ : haveI := isDomain_analyticSubring U hUo hUconn.isPreconnected hUne
               haveI := (ratfuncToMero U hUo hUconn.isPreconnected hUne hUinf).toAlgebra
               Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    bottcher_transcendental_far c₂ hc₂ hUo hUconn.isPreconnected hUne hUinf hUFB
      (a₂ := phiAnalytic c₂ hU₂) rfl
  refine ⟨U, hUo, hUconn.isPreconnected, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUconn.isPreconnected hUne
  letI := (ratfuncToMero U hUo hUconn.isPreconnected hUne hUinf).toAlgebra
  have hF₁ : phiMero c₁ hU₁ ≠ 0 := phiMero_ne_zero hUo hUconn.isPreconnected hUne hU₁
  apply q62_disconnected_of_towerData hUo hUconn.isPreconnected hUne hUinf
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) hF₁ hGtr₂
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk, hFan, hFne, hae, hrad,
    hnorm, hloops⟩ := hdata d
  have hExtesc : Ext ⊆ escapeOpen c₂ := by
    intro z hz
    show max 2 ‖c₂‖ < ‖z‖
    exact hnorm z hz
  refine ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, phiAnalytic c₂ hExtesc, k, hk1, hdk,
    hFan, hFne, hae, ?_, restrictAnalytic_phiAnalytic hUExt c₂ hExtesc hU₂, hloops⟩
  rw [hrad, ha₁eq]

/-- **Both-disconnected q62, quadratic norm gap, swapped orientation** — by
`noRelation_symm`. -/
theorem q62_phiMero_pair_far_general_swapped {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖)
    (hgap : 300 * (max 2 ‖c₁‖) ^ 2 ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₂', hU₁', hNR⟩ :=
    q62_phiMero_pair_far_general hc₂ hc1000 hc₁ hgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁', hU₂', ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_symm hNR

end Bottcher

namespace Bottcher

/-- **q62 with a quadratic norm gap, no placement hypothesis on the second parameter.**  A far
disconnected parameter (`0 ∉ K_{c₁}`, `‖c₁‖ ≥ 1000`) is algebraically independent from EVERY
parameter `c₂ ∉ {0, −2}` with `300·(max 2 ‖c₂‖)² ≤ ‖c₁‖` — whether `c₂` is connected or
disconnected: the Mandelbrot dichotomy routes to the mixed close or the both-disconnected
close, both served by the same `s`-norm-bounded tower. -/
theorem q62_phiMero_norm_gap {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hgap : 300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  by_cases hM : c₂ ∈ mandelbrot
  · exact q62_phiMero_mixed_far hc₁ hc1000 hM hc₂0 hc₂2
  · exact q62_phiMero_pair_far_general hc₁ hc1000 hM hgap

end Bottcher
