/-
# The disconnected half of all-nonexceptional U0--Bottcher independence

For a disconnected quadratic parameter the critical point is an escaping, nondegenerate saddle
of the Green function.  The first lemma below records the outward side of that saddle: every
neighbourhood of the critical point contains points at strictly larger Green level.  In particular
the connected critical superlevel has a point strictly inside the unit circle.
-/
import GaloisForLFunctions.U0.U0AllNonexceptionalConnected
import GaloisForLFunctions.Bottcher.FigureEight
import GaloisForLFunctions.Bottcher.GreenSuperlevel
import GaloisForLFunctions.Bottcher.SectionInverse
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0NaturalBoundary U0MeroCarrier U0WindowNormalization U0PhiLargeCapstone

namespace U0AllNonexceptional

/-- A disconnected critical point is not a local maximum of the Green function.  More precisely,
there is a point in the open unit disk whose Green value is strictly larger than the critical
value.  This is the outward pair of sectors in the nondegenerate holomorphic saddle model. -/
theorem exists_unitDisk_green_gt_critical {c : ℂ} (hc : Disconnected c) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ greenFunctionDyn c 0 < greenFunctionDyn c z := by
  have h0basin : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨R₀, F, hR₀, hFan₀, hFre₀, _hF'0⟩ := exists_holomorphic_completion_critical hc
  obtain ⟨Rb, hRb, hRbsub⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds h0basin)
  let R : ℝ := min (min R₀ Rb) (1 / 2)
  have hR : 0 < R := lt_min (lt_min hR₀ hRb) (by norm_num)
  have hRR₀ : R ≤ R₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRRb : R ≤ Rb := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRhalf : R ≤ 1 / 2 := min_le_right _ _
  have hbasin : ball (0 : ℂ) R ⊆ (filledJulia c)ᶜ :=
    (ball_subset_ball hRRb).trans hRbsub
  have hFan : AnalyticOnNhd ℂ F (ball (0 : ℂ) R) :=
    hFan₀.mono (ball_subset_ball hRR₀)
  have hFre : EqOn (fun z => (F z).re) (greenLimit c) (ball (0 : ℂ) R) :=
    hFre₀.mono (ball_subset_ball hRR₀)
  have hF'' : deriv (deriv F) 0 ≠ 0 :=
    deriv2_completion_critical_ne_zero hc hR hbasin hFan hFre
  have hFopen : IsOpen (F '' ball (0 : ℂ) R) := by
    rcases hFan.is_constant_or_isOpen (convex_ball (0 : ℂ) R).isPreconnected with hconst | hopen
    · exfalso
      obtain ⟨v, hv⟩ := hconst
      have hderiv_zero : (fun z => deriv F z) =ᶠ[nhds (0 : ℂ)] (fun _ => 0) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
        have hev : F =ᶠ[nhds z] (fun _ => v) := by
          filter_upwards [isOpen_ball.mem_nhds hz] with w hw
          exact hv w hw
        simpa using hev.deriv_eq
      exact hF'' (by simpa using hderiv_zero.deriv_eq)
    · exact hopen _ (Set.Subset.refl _) isOpen_ball
  have hF0mem : F 0 ∈ F '' ball (0 : ℂ) R :=
    ⟨0, Metric.mem_ball_self hR, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hFopen (F 0) hF0mem
  have htarget : F 0 + ((ε / 2 : ℝ) : ℂ) ∈ F '' ball (0 : ℂ) R := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < ε / 2 by linarith)]
    linarith
  obtain ⟨z, hzR, hzF⟩ := htarget
  have hzbasin : z ∉ filledJulia c := hbasin hzR
  have h0G : greenFunctionDyn c 0 = greenLimit c 0 := by
    unfold greenFunctionDyn
    rw [if_neg h0basin]
  have hzG : greenFunctionDyn c z = greenLimit c z := by
    unfold greenFunctionDyn
    rw [if_neg hzbasin]
  refine ⟨z, ?_, ?_⟩
  · have hzR' : ‖z‖ < R := by simpa [mem_ball_zero_iff] using hzR
    linarith
  · rw [h0G, hzG, ← hFre (Metric.mem_ball_self hR), ← hFre hzR]
    change (F 0).re < (F z).re
    rw [hzF]
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

end U0AllNonexceptional

namespace U0AllNonexceptional

/-- Every positive-radius complex ball is infinite. -/
theorem infinite_ball_complex (p : ℂ) {r : ℝ} (hr : 0 < r) : (ball p r).Infinite := by
  have hpre : IsPreconnected (ball p r) := (convex_ball p r).isPreconnected
  refine hpre.infinite_of_nontrivial ⟨p, mem_ball_self hr, p + (r / 2 : ℝ), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < r / 2 by linarith)]
    linarith
  · intro h
    have ha : p + ((r / 2 : ℝ) : ℂ) = p + 0 := by simpa using h.symm
    have : ((r / 2 : ℝ) : ℂ) = 0 := add_left_cancel ha
    exact (show ((r / 2 : ℝ) : ℂ) ≠ 0 by
      exact_mod_cast (ne_of_gt (by linarith : 0 < r / 2))) this

end U0AllNonexceptional

namespace U0AllNonexceptional

/-- A continuous path which starts outside and ends inside the unit circle has a first unit-circle
crossing.  Strictly before that time it stays in the exterior. -/
theorem exists_first_unit_crossing {p q : ℂ} (hp : 1 < ‖p‖) (hq : ‖q‖ < 1)
    (γ : Path p q) :
    ∃ t₀ : Set.Icc (0 : ℝ) 1, ‖γ t₀‖ = 1 ∧
      ∀ t : Set.Icc (0 : ℝ) 1, t < t₀ → 1 < ‖γ t‖ := by
  let g : Set.Icc (0 : ℝ) 1 → ℝ := fun t => ‖γ t‖
  have hg : Continuous g := continuous_norm.comp γ.continuous
  let H : Set (Set.Icc (0 : ℝ) 1) := {t | g t ≤ 1}
  have hHclosed : IsClosed H := by
    exact isClosed_le hg continuous_const
  have hHcompact : IsCompact H := hHclosed.isCompact
  have hHne : H.Nonempty := by
    refine ⟨⟨1, by simp⟩, ?_⟩
    change ‖γ (1 : Set.Icc (0 : ℝ) 1)‖ ≤ 1
    simpa using hq.le
  obtain ⟨t₀, ht₀H, ht₀least⟩ := hHcompact.exists_isLeast hHne
  have ht₀pos : 0 < (t₀ : ℝ) := by
    by_contra h
    push Not at h
    have ht₀zero : t₀ = (0 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      exact le_antisymm h t₀.2.1
    have hp' : ‖p‖ ≤ 1 := by
      have := ht₀H
      change ‖γ t₀‖ ≤ 1 at this
      simpa [ht₀zero] using this
    linarith
  have ht₀eq : g t₀ = 1 := by
    apply le_antisymm ht₀H
    by_contra h
    push Not at h
    have ht₀open : t₀ ∈ {t | g t < 1} := h
    have hopen : IsOpen {t : Set.Icc (0 : ℝ) 1 | g t < 1} :=
      isOpen_lt hg continuous_const
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen t₀ ht₀open
    let η : ℝ := min ((t₀ : ℝ) / 2) (δ / 2)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hηt : η ≤ (t₀ : ℝ) / 2 := min_le_left _ _
    have hηδ : η ≤ δ / 2 := min_le_right _ _
    let s : ℝ := (t₀ : ℝ) - η
    have hs0 : 0 ≤ s := by dsimp [s]; linarith
    have hs1 : s ≤ 1 := by dsimp [s]; linarith [t₀.2.2]
    let t' : Set.Icc (0 : ℝ) 1 := ⟨s, hs0, hs1⟩
    have ht'lt : t' < t₀ := by
      change s < (t₀ : ℝ)
      dsimp [s]
      linarith
    have ht'ball : t' ∈ ball t₀ δ := by
      rw [mem_ball]
      change dist s (t₀ : ℝ) < δ
      rw [Real.dist_eq]
      have hsub : s - (t₀ : ℝ) = -η := by dsimp [s]; ring
      rw [hsub, abs_neg, abs_of_pos hη]
      linarith
    have ht'H : t' ∈ H := by
      change g t' ≤ 1
      exact (hδsub ht'ball).le
    exact (not_le_of_gt ht'lt) (ht₀least ht'H)
  refine ⟨t₀, ht₀eq, ?_⟩
  intro t htt
  by_contra h
  push Not at h
  have htH : t ∈ H := h
  exact (not_le_of_gt htt) (ht₀least htH)

end U0AllNonexceptional

namespace U0AllNonexceptional

/-- For every requested far radius, the disconnected critical Green superlevel contains a path
from beyond that radius to the open unit disk.  The path has a first unit-circle crossing, and its
initial segment remains in the exterior. -/
theorem exists_far_to_first_unit_crossing {c : ℂ} (hc : Disconnected c) (A L : ℝ)
    (hL : greenFunctionDyn c 0 < L) :
    ∃ (p q : ℂ) (γ : Path p q) (t₀ : Set.Icc (0 : ℝ) 1),
      A < ‖p‖ ∧ L < greenFunctionDyn c p ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        greenFunctionDyn c 0 < greenFunctionDyn c (γ t)) ∧
      ‖q‖ < 1 ∧ ‖γ t₀‖ = 1 ∧
      (∀ t : Set.Icc (0 : ℝ) 1, t < t₀ → 1 < ‖γ t‖) := by
  have h0basin : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hhpos : 0 < greenFunctionDyn c 0 := by
    unfold greenFunctionDyn
    rw [if_neg h0basin]
    exact disconnected_green_critical_pos hc
  obtain ⟨q, hqnorm, hqG⟩ := exists_unitDisk_green_gt_critical hc
  let B : ℝ := max (‖c‖ + 3) (Real.exp (L + 2))
  let T : ℝ := max A B + 1
  let p : ℂ := (T : ℂ)
  have hBpos : 0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have hTpos : 0 < T := by
    dsimp [T]
    have := le_max_right A B
    linarith
  have hpNorm : ‖p‖ = T := by
    dsimp [p]
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
  have hBT : B < ‖p‖ := by
    rw [hpNorm]
    dsimp [T]
    have := le_max_right A B
    linarith
  have hAT : A < ‖p‖ := by
    rw [hpNorm]
    dsimp [T]
    have := le_max_left A B
    linarith
  have hpGL : L < greenFunctionDyn c p := by
    apply green_far_gt c L p
    simpa [B] using hBT
  have hpG : greenFunctionDyn c 0 < greenFunctionDyn c p := lt_trans hL hpGL
  let D : Set ℂ := {z | greenFunctionDyn c 0 < greenFunctionDyn c z}
  have hDo : IsOpen D := isOpen_lt continuous_const (continuous_greenFunctionDyn c)
  have hDc : IsConnected D := isConnected_green_superlevel c hhpos
  have hDpath : IsPathConnected D := hDo.isConnected_iff_isPathConnected.mp hDc
  have hpD : p ∈ D := hpG
  have hqD : q ∈ D := hqG
  let joined : JoinedIn D p q := hDpath.joinedIn p hpD q hqD
  let γ : Path p q := joined.somePath
  have hγD : ∀ t : Set.Icc (0 : ℝ) 1, γ t ∈ D := joined.somePath_mem
  have hpone : 1 < ‖p‖ := by
    rw [hpNorm]
    have hBtwo : 2 < B := by
      dsimp [B]
      have hexp : 2 < Real.exp (L + 2) := by
        have hlog2 : Real.log 2 < 2 := Real.log_two_lt_d9.le.trans_lt (by norm_num)
        calc 2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ < Real.exp (L + 2) :=
            Real.exp_lt_exp.mpr (by linarith)
      exact lt_of_lt_of_le hexp (le_max_right _ _)
    dsimp [T]
    have := le_max_right A B
    linarith
  obtain ⟨t₀, ht₀norm, hbefore⟩ := exists_first_unit_crossing hpone hqnorm γ
  refine ⟨p, q, γ, t₀, hAT, hpGL, ?_, hqnorm, ht₀norm, hbefore⟩
  intro t
  exact hγD t

end U0AllNonexceptional

namespace U0AllNonexceptional

/-- **Disconnected canonical circle window.**  Above the escaping critical point's Green level,
the tower section is a biholomorphism from a round annulus onto a Green band.  Choosing the band
around a compact first-crossing path gives an analytic inverse branch from a canonical far ball to
a unit-circle point.  Restricting the exterior part to the path component makes the U0 lens
preconnected without imposing any parameter-size hypothesis. -/
theorem exists_disconnected_canonical_circle_window {c : ℂ} (hc : Disconnected c) :
    ∃ (U : Set ℂ) (z₀ : ℂ) (Ω : Set ℂ) (β : ℂ → ℂ),
      IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U.Infinite ∧
      U ⊆ escapeOpen c ∧
      (∀ z ∈ U, bottcherFarBound c ((disconnected_iff_zero_not_mem c).mp hc) < ‖z‖) ∧
      IsOpen Ω ∧ IsPreconnected Ω ∧ IsPreconnected (Ω ∩ U0NaturalBoundary.Ext) ∧
      z₀ ∈ Ω ∧ ‖z₀‖ = 1 ∧ U ⊆ Ω ∩ U0NaturalBoundary.Ext ∧
      AnalyticOnNhd ℂ β Ω ∧
      (∀ z ∈ U, β z = bottcherCoord c z) := by
  classical
  have hc0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hhpos : 0 < greenFunctionDyn c 0 := by
    unfold greenFunctionDyn
    rw [if_neg hc0]
    exact disconnected_green_critical_pos hc
  obtain ⟨Ra, Rinj, hRa1, hRaG, _hInj, _hRinj, hanchor⟩ := exists_tower_anchor c
  have hRapos : 0 < Ra := lt_trans zero_lt_one hRa1
  have hhlogRa : greenFunctionDyn c 0 < Real.log Ra := by
    calc greenFunctionDyn c 0 = Real.log (Real.exp (greenFunctionDyn c 0)) :=
          (Real.log_exp _).symm
      _ < Real.log Ra := Real.log_lt_log (Real.exp_pos _) hRaG
  let L : ℝ := Real.log Ra + 1
  have hhL : greenFunctionDyn c 0 < L := by dsimp [L]; linarith
  let A : ℝ := max (bottcherFarBound c hc0) 2
  obtain ⟨p, q, γ, t₀, hpA, hpL, hγD, hqnorm, hz₀norm, hbefore⟩ :=
    exists_far_to_first_unit_crossing hc A L hhL
  let gv : Set.Icc (0 : ℝ) 1 → ℝ := fun t => greenFunctionDyn c (γ t)
  have hgvcont : Continuous gv := (continuous_greenFunctionDyn c).comp γ.continuous
  have hgvcompact : IsCompact (Set.range gv) := isCompact_range hgvcont
  obtain ⟨m, ⟨tm, rfl⟩, hmleast⟩ := hgvcompact.exists_isLeast (Set.range_nonempty gv)
  obtain ⟨M, ⟨tM, rfl⟩, hMgreatest⟩ := hgvcompact.exists_isGreatest (Set.range_nonempty gv)
  have hhm : greenFunctionDyn c 0 < gv tm := hγD tm
  let ε : ℝ := (gv tm - greenFunctionDyn c 0) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let Mtop : ℝ := Real.exp (gv tM + 1)
  obtain ⟨rlo, R₀, hrlo1, hrloRa, hRaR₀, hrlosqR₀, hMtopR₀,
      hhlo, hloε, S, hSfar, hSsurj⟩ :=
    exists_tower_deep_of_anchor c hε Mtop hRa1 hRaG hanchor
  have hrlopos : 0 < rlo := lt_trans zero_lt_one hrlo1
  have hR₀pos : 0 < R₀ := lt_trans hRapos hRaR₀
  have hloPath : ∀ t, Real.log rlo < gv t := by
    intro t
    have hmle : gv tm ≤ gv t := hmleast ⟨t, rfl⟩
    dsimp [ε] at hloε
    linarith
  have hhiPath : ∀ t, gv t < Real.log R₀ := by
    intro t
    have hleM : gv t ≤ gv tM := hMgreatest ⟨t, rfl⟩
    have hlogtop : gv tM + 1 < Real.log R₀ := by
      calc gv tM + 1 = Real.log Mtop := by simp [Mtop]
        _ < Real.log R₀ := Real.log_lt_log (Real.exp_pos _) hMtopR₀
    linarith
  let Ωtower : Set ℂ := S.T '' annulusSet rlo R₀
  have hΩtowero : IsOpen Ωtower := S.isOpen_image
  have hΩtowerc : IsConnected Ωtower :=
    (isConnected_annulus hrlopos (lt_of_le_of_lt hrloRa hRaR₀)).image S.T S.an.continuousOn
  have hpathΩ : ∀ t, γ t ∈ Ωtower := by
    intro t
    exact hSsurj (γ t) (hloPath t) (hhiPath t)
  have hpΩ : p ∈ Ωtower := by simpa using hpathΩ (0 : Set.Icc (0 : ℝ) 1)
  have hz₀Ω : γ t₀ ∈ Ωtower := hpathΩ t₀
  have hβpA : S.inv p ∈ annulusSet rlo R₀ := S.inv_mem hpΩ
  have hβpRa : Ra < ‖S.inv p‖ := by
    have hnormpos : 0 < ‖S.inv p‖ := lt_trans hrlopos hβpA.1
    calc Ra = Real.exp (Real.log Ra) := (Real.exp_log hRapos).symm
      _ < Real.exp (Real.log ‖S.inv p‖) := Real.exp_lt_exp.mpr (by
          rw [S.norm_inv hpΩ]
          dsimp [L] at hpL
          linarith)
      _ = ‖S.inv p‖ := Real.exp_log hnormpos
  have hpExt : p ∈ U0NaturalBoundary.Ext := by
    show 1 < ‖p‖
    exact lt_trans (by norm_num : (1 : ℝ) < 2) (lt_of_le_of_lt (le_max_right _ _) hpA)
  have hpFar : bottcherFarBound c hc0 < ‖p‖ :=
    lt_of_le_of_lt (le_max_left _ _) hpA
  let Sseg : Set ℂ := γ '' Set.Iio t₀
  have ht₀ne : t₀ ≠ (0 : Set.Icc (0 : ℝ) 1) := by
    intro h
    have := hz₀norm
    rw [h] at this
    have hpone : 1 < ‖p‖ := hpExt
    have this' : ‖p‖ = 1 := by simpa using this
    exact ne_of_gt hpone this'
  have ht₀pos : (0 : Set.Icc (0 : ℝ) 1) < t₀ :=
    lt_of_le_of_ne (bot_le : (0 : Set.Icc (0 : ℝ) 1) ≤ t₀) (Ne.symm ht₀ne)
  have h0Iio : (0 : Set.Icc (0 : ℝ) 1) ∈ Set.Iio t₀ := ht₀pos
  have hSsegc : IsPreconnected Sseg :=
    isPreconnected_Iio.image γ γ.continuous.continuousOn
  have hSsegSub : Sseg ⊆ Ωtower ∩ U0NaturalBoundary.Ext := by
    rintro z ⟨t, htt, rfl⟩
    exact ⟨hpathΩ t, hbefore t htt⟩
  have hpSseg : p ∈ Sseg := by
    refine ⟨0, h0Iio, ?_⟩
    simp
  let W : Set ℂ := connectedComponentIn (Ωtower ∩ U0NaturalBoundary.Ext) p
  have hWo : IsOpen W :=
    (hΩtowero.inter U0NaturalBoundary.isOpen_Ext).connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWsub : W ⊆ Ωtower ∩ U0NaturalBoundary.Ext :=
    connectedComponentIn_subset _ _
  have hpW : p ∈ W := mem_connectedComponentIn (hSsegSub hpSseg)
  have hSsegW : Sseg ⊆ W := by
    simpa [W] using hSsegc.subset_connectedComponentIn hpSseg hSsegSub
  have ht₀cl : t₀ ∈ closure (Set.Iio t₀) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    let η : ℝ := min ((t₀ : ℝ) / 2) (δ / 2)
    have ht₀valpos : (0 : ℝ) < (t₀ : ℝ) := by exact ht₀pos
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    have hηt : η ≤ (t₀ : ℝ) / 2 := min_le_left _ _
    have hηδ : η ≤ δ / 2 := min_le_right _ _
    let s : ℝ := (t₀ : ℝ) - η
    have hs0 : 0 ≤ s := by dsimp [s]; linarith [t₀.2.1]
    have hs1 : s ≤ 1 := by dsimp [s]; linarith [t₀.2.2]
    let t' : Set.Icc (0 : ℝ) 1 := ⟨s, hs0, hs1⟩
    refine ⟨t', ?_, ?_⟩
    · change s < (t₀ : ℝ)
      dsimp [s]
      linarith
    · change dist (t₀ : ℝ) s < δ
      rw [Real.dist_eq]
      have hsub : (t₀ : ℝ) - s = η := by dsimp [s]; ring
      rw [hsub, abs_of_pos hη]
      linarith
  have hz₀clSeg : γ t₀ ∈ closure Sseg := by
    apply image_closure_subset_closure_image γ.continuous
    exact ⟨t₀, ht₀cl, rfl⟩
  have hz₀clW : γ t₀ ∈ closure W := closure_mono hSsegW hz₀clSeg
  obtain ⟨rΩ, hrΩ, hrΩsub⟩ := Metric.isOpen_iff.mp hΩtowero (γ t₀) hz₀Ω
  let r : ℝ := min rΩ (1 / 2)
  have hr : 0 < r := lt_min hrΩ (by norm_num)
  have hrrΩ : r ≤ rΩ := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := min_le_right _ _
  have hballΩ : ball (γ t₀) r ⊆ Ωtower := (ball_subset_ball hrrΩ).trans hrΩsub
  obtain ⟨y, hyW, hyd⟩ := Metric.mem_closure_iff.mp hz₀clW r hr
  have hyball : y ∈ ball (γ t₀) r := by rwa [mem_ball, dist_comm]
  have hlensc : IsPreconnected (ball (γ t₀) r ∩ U0NaturalBoundary.Ext) :=
    by simpa [inter_comm, U0NaturalBoundary.Ext] using!
      U0Transcendence.lens_preconnected (γ t₀) hz₀norm hr hrhalf
  have hlensSub : ball (γ t₀) r ∩ U0NaturalBoundary.Ext ⊆
      Ωtower ∩ U0NaturalBoundary.Ext := fun z hz => ⟨hballΩ hz.1, hz.2⟩
  have hcompEq : connectedComponentIn (Ωtower ∩ U0NaturalBoundary.Ext) p =
      connectedComponentIn (Ωtower ∩ U0NaturalBoundary.Ext) y := connectedComponentIn_eq hyW
  have hlensW : ball (γ t₀) r ∩ U0NaturalBoundary.Ext ⊆ W := by
    have hsub := hlensc.subset_connectedComponentIn
      (show y ∈ ball (γ t₀) r ∩ U0NaturalBoundary.Ext from ⟨hyball, (hWsub hyW).2⟩) hlensSub
    simpa [W, hcompEq] using hsub
  let Ω : Set ℂ := W ∪ ball (γ t₀) r
  have hΩo : IsOpen Ω := hWo.union isOpen_ball
  have hΩc : IsPreconnected Ω :=
    hWc.union y hyW hyball (convex_ball (γ t₀) r).isPreconnected
  have hΩExt : Ω ∩ U0NaturalBoundary.Ext = W := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzW | hzball, hzExt⟩
      · exact hzW
      · exact hlensW ⟨hzball, hzExt⟩
    · intro z hzW
      exact ⟨Or.inl hzW, (hWsub hzW).2⟩
  have hΩsubTower : Ω ⊆ Ωtower := by
    rintro z (hzW | hzball)
    · exact (hWsub hzW).1
    · exact hballΩ hzball
  have hβcontp : ContinuousAt S.inv p := (S.inv_analytic p hpΩ).continuousAt
  have hevβ : ∀ᶠ z in nhds p, S.inv z ∈ annulusSet Ra R₀ := by
    apply hβcontp.preimage_mem_nhds
    exact (isOpen_annulusSet Ra R₀).mem_nhds ⟨hβpRa, hβpA.2⟩
  have hevΩ : ∀ᶠ z in nhds p, z ∈ Ωtower := hΩtowero.mem_nhds hpΩ
  have hevExt : ∀ᶠ z in nhds p, z ∈ U0NaturalBoundary.Ext :=
    U0NaturalBoundary.isOpen_Ext.mem_nhds hpExt
  have hevFar : ∀ᶠ z in nhds p, bottcherFarBound c hc0 < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hpFar
  obtain ⟨rU, hrU, hrUsub⟩ := Metric.mem_nhds_iff.mp (hevβ.and (hevΩ.and (hevExt.and hevFar)))
  let U : Set ℂ := ball p rU
  have hUo : IsOpen U := isOpen_ball
  have hUc : IsPreconnected U := (convex_ball p rU).isPreconnected
  have hpU : p ∈ U := mem_ball_self hrU
  have hUne : U.Nonempty := ⟨p, hpU⟩
  have hUinf : U.Infinite := infinite_ball_complex p hrU
  have hUesc : U ⊆ escapeOpen c := by
    intro z hz
    have hzall := hrUsub hz
    have hzβ : S.inv z ∈ annulusSet Ra R₀ := hzall.1
    have hzΩt : z ∈ Ωtower := hzall.2.1
    have hright := S.inv_right hzΩt
    have hfar := hSfar (S.inv z) hzβ.1 hzβ.2
    rw [hright] at hfar
    exact hfar.2.1
  have hUFar : ∀ z ∈ U, bottcherFarBound c hc0 < ‖z‖ :=
    fun z hz => (hrUsub hz).2.2.2
  have hUS : U ⊆ Ωtower ∩ U0NaturalBoundary.Ext :=
    fun z hz => ⟨(hrUsub hz).2.1, (hrUsub hz).2.2.1⟩
  have hUW : U ⊆ W := by
    simpa [W] using hUc.subset_connectedComponentIn hpU hUS
  have hUΩ : U ⊆ Ω ∩ U0NaturalBoundary.Ext := by
    intro z hz
    rw [hΩExt]
    exact hUW hz
  have hβeq : ∀ z ∈ U, S.inv z = bottcherCoord c z := by
    intro z hz
    have hzall := hrUsub hz
    have hzβ : S.inv z ∈ annulusSet Ra R₀ := hzall.1
    have hzΩt : z ∈ Ωtower := hzall.2.1
    have hright := S.inv_right hzΩt
    have hfar := hSfar (S.inv z) hzβ.1 hzβ.2
    rw [hright] at hfar
    exact hfar.1.symm
  refine ⟨U, γ t₀, Ω, S.inv, hUo, hUc, hUne, hUinf, hUesc, hUFar,
    hΩo, hΩc, ?_, ?_, hz₀norm, hUΩ, ?_, hβeq⟩
  · rw [hΩExt]
    exact hWc
  · exact Or.inr (mem_ball_self hr)
  · exact S.inv_analytic.mono hΩsubTower


end U0AllNonexceptional

namespace U0AllNonexceptional

/-- **Disconnected all-parameter card, unconditional.**  For every disconnected quadratic
parameter, the actual canonical far Böttcher germ is algebraically independent from `u₀`.
The critical-superlevel tower supplies the analytic branch reaching the unit circle, while the
far carrier remains a literal restriction of `bottcherCoord`. -/
theorem u0_phi_independence_disconnected_canonical (c : ℂ) (hc : Disconnected c) :
    CanonicalPhiU0IndependenceAt c := by
  obtain ⟨U, z₀, Ω, β, hUo, hUc, hUne, hUinf, hUesc, hUFar,
    hΩo, hΩc, hDc, hz₀Ω, hz₀norm, hUΩ, hβΩ, hβU⟩ :=
    exists_disconnected_canonical_circle_window hc
  have hUExt : U ⊆ U0NaturalBoundary.Ext :=
    hUesc.trans (U0CardTheorems.escapeOpen_subset_U0Ext c)
  refine ⟨U, hUo, hUc, hUne, hUinf, hUesc, ?_⟩
  refine u0_window_independence_of_transcendental_engine hUo hUc hUne hUinf hUExt
    (bottcherCoord c) (phiAnalytic c hUesc) rfl ?_ ?_
  · exact bottcher_transcendental_far c ((disconnected_iff_zero_not_mem c).mp hc)
      hUo hUc hUne hUinf hUFar rfl
  · intro P' j₀ hj₀ hnd hrel
    have hndβ : ∃ z ∈ Ω ∩ U0NaturalBoundary.Ext,
        coeffFun β (P'.coeff j₀) z ≠ 0 := by
      obtain ⟨z, hzU, hz⟩ := hnd
      refine ⟨z, hUΩ hzU, ?_⟩
      simpa only [coeffFun, hβU z hzU] using hz
    refine u0_windowed_no_relation_nondegenerate hΩo hΩc hDc hβΩ
      hz₀Ω hz₀norm P' hj₀ hndβ hUo hUne hUΩ ?_
    intro z hzU
    rw [hβU z hzU]
    exact hrel z hzU

/-- **All nonexceptional U0--Böttcher independence, unconditional.** -/
theorem u0_phi_independence_all_nonexceptional_canonical :
    ∀ c : ℂ, c ≠ 0 → c ≠ (-2 : ℂ) → CanonicalPhiU0IndependenceAt c := by
  intro c hc0 hc2
  by_cases hcM : c ∈ mandelbrot
  · exact u0_phi_independence_connected_canonical c hcM hc0 hc2
  · exact u0_phi_independence_disconnected_canonical c hcM

end U0AllNonexceptional
