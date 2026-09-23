/-
# Connectivity of Green superlevel sets `{G_c > s}`

The winding certificates of the band tower need: a point at Green level above the loop's level is
"outside" (winding `0`).  The route (`WindingCertificates.windInt_eq_on_preconnected` + far-field
vanishing) requires exactly that the superlevel set `{G_c > s}` is CONNECTED, for `s > 0`.

Proof, with no potential-theory imports: the superlevel set is open (`continuous_greenFunctionDyn`)
and contains the connected exterior of a large disk (`greenLimit_lower_bound`).  A connected
component missing the far field would be bounded; the maximum of `G_c` over its closure is
attained either on the frontier — but a frontier point has `G = max > s`, so an absorbed ball
pulls it into the (open) component, contradiction — or at an interior point, where `G_c = Re F`
for a local holomorphic conjugate (`exists_local_greenConjugate_basin`), so the maximum-modulus
principle (`Complex.eventually_eq_of_isLocalMax_norm` on `exp F`) makes `G_c` locally constant;
propagating (clopen-in-component) gives `G_c ≡ max` on the component, and the frontier
contradiction returns.  So every component meets the far field, which welds them all.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.GreenContinuity

open Complex Set Filter Topology Metric

namespace Bottcher

/-- The exterior of a disk is connected (image of a half-plane under `exp`). -/
theorem isConnected_norm_gt {R : ℝ} (hR : 0 < R) : IsConnected {z : ℂ | R < ‖z‖} := by
  have himg : {z : ℂ | R < ‖z‖} = Complex.exp '' {ξ : ℂ | Real.log R < ξ.re} := by
    ext z
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro h1
      have hz0 : z ≠ 0 := by
        rintro rfl; simp only [norm_zero] at h1; linarith
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log hR h1
    · rintro ⟨ξ, h1, rfl⟩
      rw [Complex.norm_exp]
      calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
        _ < Real.exp ξ.re := Real.exp_lt_exp.mpr h1
  rw [himg]
  apply IsConnected.image
  · apply Convex.isConnected (convex_halfSpace_re_gt _)
    exact ⟨((Real.log R + 1 : ℝ) : ℂ), by simp⟩
  · exact Complex.continuous_exp.continuousOn

/-- **Local constancy of `G_c` at an interior local maximum in the basin** — the maximum-modulus
principle through the local holomorphic conjugate. -/
theorem green_eventually_const_of_isLocalMax {c z : ℂ} (hz : z ∉ filledJulia c)
    (hmax : IsLocalMax (greenFunctionDyn c) z) :
    ∀ᶠ w in 𝓝 z, greenFunctionDyn c w = greenFunctionDyn c z := by
  obtain ⟨r, F, hr, hFan, hFre⟩ := exists_local_greenConjugate_basin hz
  obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.1 (isClosed_filledJulia c).isOpen_compl z hz
  set ρ : ℝ := min r r' with hρdef
  have hρpos : 0 < ρ := lt_min hr hr'
  have hballK : ball z ρ ⊆ (filledJulia c)ᶜ :=
    fun w hw => hball' (ball_subset_ball (min_le_right r r') hw)
  have hballF : ball z ρ ⊆ ball z r := ball_subset_ball (min_le_left r r')
  have hGeq : ∀ w ∈ ball z ρ, greenFunctionDyn c w = (F w).re := by
    intro w hw
    have hwK : w ∉ filledJulia c := hballK hw
    unfold greenFunctionDyn
    rw [if_neg hwK]
    exact (hFre (hballF hw)).symm
  have hballnhds : ball z ρ ∈ 𝓝 z := Metric.ball_mem_nhds z hρpos
  -- `exp ∘ F` has a local max of norm at z
  have hmax' : IsLocalMax (norm ∘ fun w => Complex.exp (F w)) z := by
    show ∀ᶠ w in 𝓝 z, (norm ∘ fun w => Complex.exp (F w)) w
      ≤ (norm ∘ fun w => Complex.exp (F w)) z
    filter_upwards [hmax, hballnhds] with w hw hwball
    show ‖Complex.exp (F w)‖ ≤ ‖Complex.exp (F z)‖
    rw [Complex.norm_exp, Complex.norm_exp, ← hGeq w hwball,
      ← hGeq z (Metric.mem_ball_self hρpos)]
    exact Real.exp_le_exp.mpr hw
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => Complex.exp (F w)) w := by
    filter_upwards [hballnhds] with w hw
    exact (Complex.differentiable_exp.differentiableAt).comp w
      ((hFan w (hballF hw)).differentiableAt)
  have hconst := Complex.eventually_eq_of_isLocalMax_norm hdiff hmax'
  filter_upwards [hconst, hballnhds] with w hw hwball
  have hnorm : Real.exp ((F w).re) = Real.exp ((F z).re) := by
    rw [← Complex.norm_exp, ← Complex.norm_exp, hw]
  have hre : (F w).re = (F z).re := Real.exp_injective hnorm
  rw [hGeq w hwball, hre, ← hGeq z (Metric.mem_ball_self hρpos)]

/-- **The Green superlevel set `{G_c > s}` is connected** (`s > 0`).  Every component reaches the
connected far field: a bounded component's closure carries a maximum of `G_c`, which is forbidden
both on the frontier (ball absorption into the open component) and in the interior (local
constancy by the maximum principle, propagated). -/
theorem isConnected_green_superlevel (c : ℂ) {s : ℝ} (hs : 0 < s) :
    IsConnected {z : ℂ | s < greenFunctionDyn c z} := by
  classical
  set Ω : Set ℂ := {z : ℂ | s < greenFunctionDyn c z} with hΩdef
  have hΩo : IsOpen Ω := isOpen_lt continuous_const (continuous_greenFunctionDyn c)
  -- the far threshold
  set R₀ : ℝ := max (‖c‖ + 3) (Real.exp (s + 2)) with hR₀def
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hfar : ∀ z : ℂ, R₀ < ‖z‖ → z ∈ Ω := by
    intro z hz
    have hc3 : ‖c‖ + 3 ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz)
    have hc : ‖c‖ ≤ ‖z‖ := by linarith
    have h2 : 2 < ‖z‖ := by linarith [norm_nonneg c]
    have hK : z ∉ filledJulia c := not_mem_filledJulia hc h2
    have hlb := greenLimit_lower_bound hc h2
    have hlog : s + 2 < Real.log ‖z‖ := by
      have h1 : Real.exp (s + 2) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
      calc s + 2 = Real.log (Real.exp (s + 2)) := (Real.log_exp _).symm
        _ < Real.log ‖z‖ := Real.log_lt_log (Real.exp_pos _) h1
    have hcorr : 2 * ‖c‖ / ‖z‖ ^ (2 : ℕ) ≤ 1 := by
      have hz2 : 2 * ‖c‖ ≤ ‖z‖ ^ (2 : ℕ) := by nlinarith [norm_nonneg c]
      rw [div_le_one (by nlinarith [norm_nonneg c] : (0:ℝ) < ‖z‖ ^ (2 : ℕ))]
      exact hz2
    show s < greenFunctionDyn c z
    unfold greenFunctionDyn
    rw [if_neg hK]
    linarith
  have hfarConn : IsConnected {z : ℂ | R₀ < ‖z‖} := isConnected_norm_gt hR₀pos
  have hfarsub : {z : ℂ | R₀ < ‖z‖} ⊆ Ω := fun z hz => hfar z hz
  have hfarpt : ((R₀ + 1 : ℝ) : ℂ) ∈ {z : ℂ | R₀ < ‖z‖} := by
    simp only [mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]
    linarith
  -- ball absorption into components
  have habsorb : ∀ (z₀ : ℂ), ∀ p ∈ Ω, ∀ ρ > 0, ball p ρ ⊆ Ω →
      (ball p ρ ∩ connectedComponentIn Ω z₀).Nonempty →
      p ∈ connectedComponentIn Ω z₀ := by
    intro z₀ p hp ρ hρ hball ⟨y, hyB, hyW⟩
    have h1 : ball p ρ ⊆ connectedComponentIn Ω y :=
      (convex_ball p ρ).isPreconnected.subset_connectedComponentIn hyB hball
    have h2 : connectedComponentIn Ω z₀ = connectedComponentIn Ω y :=
      connectedComponentIn_eq hyW
    rw [← h2] at h1
    exact h1 (Metric.mem_ball_self hρ)
  -- every component reaches the far field
  have hreach : ∀ z₀ ∈ Ω, ∃ w ∈ connectedComponentIn Ω z₀, R₀ < ‖w‖ := by
    intro z₀ hz₀
    by_contra hcon
    push Not at hcon
    set W : Set ℂ := connectedComponentIn Ω z₀ with hWdef
    have hWo : IsOpen W := hΩo.connectedComponentIn
    have hWsub : W ⊆ Ω := connectedComponentIn_subset Ω z₀
    have hz₀W : z₀ ∈ W := mem_connectedComponentIn hz₀
    have hWbd : W ⊆ closedBall (0 : ℂ) R₀ := by
      intro w hw
      rw [mem_closedBall, dist_zero_right]
      exact hcon w hw
    -- the maximum of G over the compact closure
    have hclcomp : IsCompact (closure W) :=
      (isCompact_closedBall (0:ℂ) R₀).of_isClosed_subset isClosed_closure
        ((closure_minimal hWbd Metric.isClosed_closedBall))
    obtain ⟨zm, hzmcl, hzmmax⟩ := hclcomp.exists_isMaxOn ⟨z₀, subset_closure hz₀W⟩
      (continuous_greenFunctionDyn c).continuousOn
    have hzmΩ : zm ∈ Ω := by
      have h1 : greenFunctionDyn c z₀ ≤ greenFunctionDyn c zm := hzmmax (subset_closure hz₀W)
      have h2 : s < greenFunctionDyn c z₀ := hz₀
      show s < greenFunctionDyn c zm
      linarith
    by_cases hzmW : zm ∈ W
    · -- interior maximum: G is locally constant, propagate over the component
      have hlocconst : ∀ w ∈ W, greenFunctionDyn c w = greenFunctionDyn c zm →
          ∀ᶠ v in 𝓝 w, greenFunctionDyn c v = greenFunctionDyn c zm := by
        intro w hwW hweq
        have hwK : w ∉ filledJulia c := by
          intro hmem
          have h0 : greenFunctionDyn c w = 0 := by
            unfold greenFunctionDyn; rw [if_pos hmem]
          have h1 : s < greenFunctionDyn c w := hWsub hwW
          rw [h0] at h1
          linarith
        have hwmax : IsLocalMax (greenFunctionDyn c) w := by
          show ∀ᶠ v in 𝓝 w, greenFunctionDyn c v ≤ greenFunctionDyn c w
          filter_upwards [hWo.mem_nhds hwW] with v hv
          rw [hweq]
          exact hzmmax (subset_closure hv)
        have := green_eventually_const_of_isLocalMax hwK hwmax
        filter_upwards [this] with v hv
        rw [hv, hweq]
      -- clopen propagation: {w ∈ W | greenFunctionDyn c w = greenFunctionDyn c zm} = W
      have hconstW : ∀ w ∈ W, greenFunctionDyn c w = greenFunctionDyn c zm := by
        by_contra hcon2
        push Not at hcon2
        obtain ⟨w₁, hw₁W, hw₁ne⟩ := hcon2
        set U : Set ℂ := ⋃ (p : ℂ) (_ : p ∈ W ∧ greenFunctionDyn c p = greenFunctionDyn c zm),
          {v | v ∈ W ∧ greenFunctionDyn c v = greenFunctionDyn c zm ∧ v ∈ ball p 1}ᶜᶜ with hUdef
        -- simpler: U := interior points where G = greenFunctionDyn c zm eventually; V := {G ≠ greenFunctionDyn c zm}
        clear hUdef U
        set V : Set ℂ := {v : ℂ | greenFunctionDyn c v ≠ greenFunctionDyn c zm} with hVdef
        have hVo : IsOpen V := by
          have : V = (greenFunctionDyn c ⁻¹' {greenFunctionDyn c zm})ᶜ := by
            ext v; simp [hVdef]
          rw [this]
          exact (IsClosed.preimage (continuous_greenFunctionDyn c) isClosed_singleton).isOpen_compl
        set U : Set ℂ := {v : ℂ | ∀ᶠ u in 𝓝 v, greenFunctionDyn c u = greenFunctionDyn c zm} with hUdef
        have hUo : IsOpen U := by
          rw [isOpen_iff_mem_nhds]
          intro v hv
          obtain ⟨t, htnhds, ht⟩ := eventually_iff_exists_mem.mp hv
          rw [_root_.mem_nhds_iff] at htnhds
          obtain ⟨t', ht't, ht'o, hvt'⟩ := htnhds
          rw [_root_.mem_nhds_iff]
          refine ⟨t', ?_, ht'o, hvt'⟩
          intro u hu
          show ∀ᶠ x in 𝓝 u, greenFunctionDyn c x = greenFunctionDyn c zm
          filter_upwards [ht'o.mem_nhds hu] with x hx
          exact ht x (ht't hx)
        have hcover : W ⊆ U ∪ V := by
          intro w hw
          by_cases hG : greenFunctionDyn c w = greenFunctionDyn c zm
          · exact Or.inl (hlocconst w hw hG)
          · exact Or.inr hG
        have hneU : (W ∩ U).Nonempty := ⟨zm, hzmW, hlocconst zm hzmW rfl⟩
        have hneV : (W ∩ V).Nonempty := ⟨w₁, hw₁W, hw₁ne⟩
        obtain ⟨v, _, hvU, hvV⟩ :=
          (isPreconnected_connectedComponentIn (F := Ω) (x := z₀)) U V hUo hVo
            hcover hneU hneV
        exact hvV hvU.self_of_nhds
      -- G ≡ greenFunctionDyn c zm on W; the frontier gives the contradiction
      have hfrne : (frontier W).Nonempty := by
        by_contra hfr
        rw [Set.not_nonempty_iff_eq_empty] at hfr
        rcases frontier_eq_empty_iff.mp hfr with h | h
        · rw [h] at hz₀W; exact hz₀W
        · have := hWbd (h ▸ (Set.mem_univ (((R₀ + 1 : ℝ) : ℂ))))
          rw [mem_closedBall, dist_zero_right] at this
          have : R₀ + 1 ≤ R₀ := by
            calc R₀ + 1 = ‖(((R₀ + 1 : ℝ)) : ℂ)‖ := by
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
              _ ≤ R₀ := this
          linarith
      obtain ⟨wfr, hwfr⟩ := hfrne
      have hwfrcl : wfr ∈ closure W := hwfr.1
      have hwfrnotW : wfr ∉ W := by
        intro hmem
        exact hwfr.2 (by rw [hWo.interior_eq]; exact hmem)
      have hGwfr : greenFunctionDyn c wfr = greenFunctionDyn c zm := by
        have h1 : closure W ⊆ closure {v : ℂ | greenFunctionDyn c v = greenFunctionDyn c zm} :=
          closure_mono (fun w hw => hconstW w hw)
        have h2 : IsClosed {v : ℂ | greenFunctionDyn c v = greenFunctionDyn c zm} :=
          IsClosed.preimage (continuous_greenFunctionDyn c) isClosed_singleton
        exact (h2.closure_eq ▸ h1) hwfrcl
      have hwfrΩ : wfr ∈ Ω := by
        show s < greenFunctionDyn c wfr
        rw [hGwfr]
        exact hzmΩ
      obtain ⟨ρ, hρpos, hρball⟩ := Metric.isOpen_iff.1 hΩo wfr hwfrΩ
      have hmeets : (ball wfr ρ ∩ W).Nonempty := by
        rw [Metric.mem_closure_iff] at hwfrcl
        obtain ⟨y, hyW, hyd⟩ := hwfrcl ρ hρpos
        exact ⟨y, by rwa [Metric.mem_ball, dist_comm], hyW⟩
      exact hwfrnotW (habsorb z₀ wfr hwfrΩ ρ hρpos hρball hmeets)
    · -- frontier maximum: direct ball absorption
      obtain ⟨ρ, hρpos, hρball⟩ := Metric.isOpen_iff.1 hΩo zm hzmΩ
      have hmeets : (ball zm ρ ∩ W).Nonempty := by
        rw [Metric.mem_closure_iff] at hzmcl
        obtain ⟨y, hyW, hyd⟩ := hzmcl ρ hρpos
        exact ⟨y, by rwa [Metric.mem_ball, dist_comm], hyW⟩
      exact hzmW (habsorb z₀ zm hzmΩ ρ hρpos hρball hmeets)
  -- weld: every component contains the far field
  have hz₁ : ((R₀ + 1 : ℝ) : ℂ) ∈ Ω := hfarsub hfarpt
  refine ⟨⟨_, hz₁⟩, ?_⟩
  have hΩeq : Ω = connectedComponentIn Ω (((R₀ + 1 : ℝ)) : ℂ) := by
    apply Set.Subset.antisymm
    · intro z₁ hz₁'
      obtain ⟨w₁, hw₁W, hw₁far⟩ := hreach z₁ hz₁'
      have hfarW : {z : ℂ | R₀ < ‖z‖} ⊆ connectedComponentIn Ω z₁ := by
        have h1 : {z : ℂ | R₀ < ‖z‖} ⊆ connectedComponentIn Ω w₁ :=
          hfarConn.isPreconnected.subset_connectedComponentIn hw₁far hfarsub
        rwa [← connectedComponentIn_eq hw₁W] at h1
      have h2 : ((R₀ + 1 : ℝ) : ℂ) ∈ connectedComponentIn Ω z₁ := hfarW hfarpt
      have h3 := connectedComponentIn_eq h2
      rw [← h3]
      exact mem_connectedComponentIn hz₁'
    · exact connectedComponentIn_subset Ω _
  rw [hΩeq]
  exact isPreconnected_connectedComponentIn

end Bottcher
