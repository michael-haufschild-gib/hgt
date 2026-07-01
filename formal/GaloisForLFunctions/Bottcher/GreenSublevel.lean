/-
# Connectivity of Green sublevel sets `{G_c < L}` above the critical level

The tower's inside-winding certificates reduce to a single evaluation at `0` once the sublevel set
`{G_c < L}` is connected — this file proves that for every `L > h := G_c(0)`:

* **anchor** (`L` huge): every sublevel point rides a `ψ`-radial path (the far-field inverse of
  `φ_c`, at constant angular coordinate, `G(ψ v) = log ‖v‖` decreasing) into a central ball;
* **descent**: `{G < L} = f_c⁻¹({G < 2L})` (global functional equation), and the preimage of a
  connected open set CONTAINING THE CRITICAL VALUE `c` is connected: `f_c` is open (open mapping
  theorem) and proper, so each component of the preimage maps onto the target, hence contains the
  unique preimage `0` of `c`.  The threshold `L > h` is exactly `c ∈ {G < 2L}`.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenPullback
import GaloisForLFunctions.Bottcher.BottcherFarFieldSurjective

open Complex Set Filter Metric Topology

namespace Bottcher

/-- Iterated global functional equation: `G_c(f^[n] z) = 2^n · G_c(z)`. -/
theorem greenFunctionDyn_iterate (c z : ℂ) (n : ℕ) :
    greenFunctionDyn c ((quadratic c)^[n] z) = 2 ^ n * greenFunctionDyn c z := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', greenFunctionDyn_quadratic, ih, pow_succ]
      ring

/-- Crude upper bound: `G_c ≤ log ‖z‖ + 1` on the crude escape regime. -/
theorem greenFunctionDyn_le_crude {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    greenFunctionDyn c z ≤ Real.log ‖z‖ + 1 := by
  have hK : z ∉ filledJulia c := not_mem_filledJulia hc hz
  have habs := greenLimit_abs_sub_log hc hz
  have hcorr : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 1 := by
    have h1 : 2 * ‖c‖ ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg c]
    rw [div_le_one (by nlinarith [norm_nonneg c] : (0:ℝ) < ‖z‖ ^ 2)]
    exact h1
  unfold greenFunctionDyn
  rw [if_neg hK]
  have := (abs_le.mp habs).2
  linarith

/-- Global bound on the non-crude region: `G_c ≤ log((max 2 ‖c‖)² + ‖c‖) + 1` for
`‖z‖ ≤ max 2 ‖c‖` (first-escape overshoot). -/
theorem greenFunctionDyn_le_small {c z : ℂ} (hz : ‖z‖ ≤ max 2 ‖c‖) :
    greenFunctionDyn c z ≤ Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) + 1 := by
  have hB₀ : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
  have hlogpos : 0 ≤ Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) := by
    apply Real.log_nonneg
    nlinarith [norm_nonneg c]
  by_cases hK : z ∈ filledJulia c
  · unfold greenFunctionDyn
    rw [if_pos hK]
    linarith
  · obtain ⟨N, hN⟩ := exists_orbit_gt hK (max 2 ‖c‖)
    -- take the least escape time
    have hex : ∃ n, max 2 ‖c‖ < ‖(quadratic c)^[n] z‖ := ⟨N, hN⟩
    classical
    set N₀ := Nat.find hex with hN₀def
    have hN₀ : max 2 ‖c‖ < ‖(quadratic c)^[N₀] z‖ := Nat.find_spec hex
    have hN₀pos : 0 < N₀ := by
      rcases Nat.eq_zero_or_pos N₀ with h0 | h
      · exfalso
        rw [h0] at hN₀
        simp only [Function.iterate_zero, id_eq] at hN₀
        linarith
      · exact h
    have hprev : ‖(quadratic c)^[N₀ - 1] z‖ ≤ max 2 ‖c‖ := by
      by_contra hcon
      push Not at hcon
      exact Nat.find_min hex (by omega : N₀ - 1 < N₀) hcon
    have hover : ‖(quadratic c)^[N₀] z‖ ≤ (max 2 ‖c‖) ^ 2 + ‖c‖ := by
      have harg : (quadratic c)^[N₀] z = quadratic c ((quadratic c)^[N₀ - 1] z) := by
        conv_lhs => rw [show N₀ = (N₀ - 1) + 1 from by omega]
        rw [Function.iterate_succ_apply']
      rw [harg]
      unfold quadratic
      calc ‖((quadratic c)^[N₀ - 1] z) ^ 2 + c‖
          ≤ ‖((quadratic c)^[N₀ - 1] z) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (max 2 ‖c‖) ^ 2 + ‖c‖ := by
            rw [norm_pow]
            have := hprev
            nlinarith [norm_nonneg ((quadratic c)^[N₀ - 1] z)]
    have hcrude₂ : 2 < ‖(quadratic c)^[N₀] z‖ :=
      lt_of_le_of_lt hB₀ hN₀
    have hcrudec : ‖c‖ ≤ ‖(quadratic c)^[N₀] z‖ :=
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN₀)
    have hup := greenFunctionDyn_le_crude hcrudec hcrude₂
    have hit := greenFunctionDyn_iterate c z N₀
    have hlogmono : Real.log ‖(quadratic c)^[N₀] z‖
        ≤ Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) := by
      apply Real.log_le_log (by linarith)
      exact hover
    have hGpos : 0 ≤ greenFunctionDyn c z := greenFunctionDyn_nonneg c z
    have h2N : (1:ℝ) ≤ 2 ^ N₀ := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have hle : greenFunctionDyn c z ≤ greenFunctionDyn c ((quadratic c)^[N₀] z) := by
      rw [hit]
      nlinarith
    linarith

/-- The quadratic map is proper. -/
theorem isProperMap_quadratic (c : ℂ) : IsProperMap (quadratic c) := by
  rw [isProperMap_iff_tendsto_cocompact]
  refine ⟨continuous_quadratic c, ?_⟩
  have hnorm : Tendsto (fun z : ℂ => ‖quadratic c z‖) (cocompact ℂ) atTop := by
    have h2 : Tendsto (fun z : ℂ => ‖z‖ * ‖z‖ - ‖c‖) (cocompact ℂ) atTop := by
      have hmul := (tendsto_norm_cocompact_atTop (E := ℂ)).atTop_mul_atTop₀
        (tendsto_norm_cocompact_atTop (E := ℂ))
      exact tendsto_atTop_add_const_right _ (-‖c‖) hmul
    apply tendsto_atTop_mono _ h2
    intro z
    have h3 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
      calc ‖z ^ 2‖ = ‖(z ^ 2 + c) + (-c)‖ := by ring_nf
        _ ≤ ‖z ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
        _ = ‖z ^ 2 + c‖ + ‖c‖ := by rw [norm_neg]
    have h4 : ‖z ^ 2‖ = ‖z‖ * ‖z‖ := by rw [norm_pow]; ring
    show ‖z‖ * ‖z‖ - ‖c‖ ≤ ‖quadratic c z‖
    unfold quadratic
    linarith [h3, h4.symm.le]
  have hcob : Filter.cocompact ℂ = Filter.comap norm Filter.atTop := by
    rw [comap_norm_atTop, ← Metric.cobounded_eq_cocompact]
  rw [show Tendsto (quadratic c) (cocompact ℂ) (cocompact ℂ) ↔
      Tendsto (quadratic c) (cocompact ℂ) (Filter.comap norm Filter.atTop) from by
    rw [← hcob]]
  rw [Filter.tendsto_comap_iff]
  exact hnorm

/-- The quadratic map is open (open mapping theorem; it is nonconstant). -/
theorem isOpenMap_quadratic (c : ℂ) : IsOpenMap (quadratic c) := by
  have han : AnalyticOnNhd ℂ (quadratic c) univ := by
    intro z _
    unfold quadratic
    exact (analyticAt_id.pow 2).add analyticAt_const
  rcases han.is_constant_or_isOpen isPreconnected_univ with ⟨w, hw⟩ | hopen
  · exfalso
    have h0 := hw 0 (mem_univ 0)
    have h1 := hw 1 (mem_univ 1)
    unfold quadratic at h0 h1
    have hcontra : (1:ℂ) = 0 := by linear_combination h1 - h0
    exact one_ne_zero hcontra
  · intro U hU
    exact hopen U (subset_univ U) hU

/-- **Connected preimage through the critical value.**  The `f_c`-preimage of a connected open set
containing the critical value `c` is connected: each component of the preimage maps onto the
target (open map + closed map from properness, tube trick), hence contains the unique
`f_c`-preimage `0` of `c`. -/
theorem isConnected_quadratic_preimage {c : ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U) (hcU : c ∈ U) :
    IsConnected ((quadratic c) ⁻¹' U) := by
  classical
  set P : Set ℂ := (quadratic c) ⁻¹' U with hPdef
  have hPo : IsOpen P := hUo.preimage (continuous_quadratic c)
  have h0P : (0:ℂ) ∈ P := by
    show quadratic c 0 ∈ U
    unfold quadratic
    simpa using hcU
  have hclosedmap : IsClosedMap (quadratic c) := (isProperMap_quadratic c).isClosedMap
  -- every component of P contains 0
  have hcomp : ∀ x ∈ P, (0:ℂ) ∈ connectedComponentIn P x := by
    intro x hx
    set W : Set ℂ := connectedComponentIn P x with hWdef
    have hWo : IsOpen W := hPo.connectedComponentIn
    have hWP : W ⊆ P := connectedComponentIn_subset P x
    have hxW : x ∈ W := mem_connectedComponentIn hx
    have hfWo : IsOpen (quadratic c '' W) := isOpenMap_quadratic c W hWo
    -- P ∖ W is open (union of the other components)
    have hPWo : IsOpen (P \ W) := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hVo : IsOpen (connectedComponentIn P y) := hPo.connectedComponentIn
      have hsub : connectedComponentIn P y ⊆ P \ W := by
        intro v hv
        refine ⟨connectedComponentIn_subset P y hv, ?_⟩
        intro hvW
        apply hy.2
        have h1 : connectedComponentIn P y = connectedComponentIn P v :=
          connectedComponentIn_eq hv
        have h2 : connectedComponentIn P x = connectedComponentIn P v :=
          connectedComponentIn_eq hvW
        rw [hWdef, h2, ← h1]
        exact mem_connectedComponentIn hy.1
      exact Filter.mem_of_superset (hVo.mem_nhds (mem_connectedComponentIn hy.1)) hsub
    -- the image f(W) is relatively clopen in U: the complement U ∖ f(W) is open
    have hcompl_open : IsOpen ((quadratic c '' ((P \ W)ᶜ))ᶜ) := by
      have : IsClosed (quadratic c '' ((P \ W)ᶜ)) := hclosedmap _ hPWo.isClosed_compl
      exact this.isOpen_compl
    have hUdiff : U \ quadratic c '' W = U ∩ (quadratic c '' ((P \ W)ᶜ))ᶜ := by
      ext u
      constructor
      · rintro ⟨huU, hunW⟩
        refine ⟨huU, ?_⟩
        rintro ⟨y, hy, rfl⟩
        rw [Set.mem_compl_iff, Set.mem_diff, not_and, not_not] at hy
        have hyP : y ∈ P := by
          show quadratic c y ∈ U
          exact huU
        exact hunW ⟨y, hy hyP, rfl⟩
      · rintro ⟨huU, hcomp'⟩
        refine ⟨huU, ?_⟩
        rintro ⟨y, hyW, rfl⟩
        apply hcomp'
        refine ⟨y, ?_, rfl⟩
        rw [Set.mem_compl_iff, Set.mem_diff, not_and, not_not]
        intro _
        exact hyW
    -- clopen dichotomy in the connected U
    have hcover : U ⊆ (quadratic c '' W) ∪ (quadratic c '' ((P \ W)ᶜ))ᶜ := by
      intro u hu
      by_cases hw : u ∈ quadratic c '' W
      · exact Or.inl hw
      · right
        have hmem : u ∈ U \ quadratic c '' W := ⟨hu, hw⟩
        rw [hUdiff] at hmem
        exact hmem.2
    have hneW : (U ∩ quadratic c '' W).Nonempty :=
      ⟨quadratic c x, hWP hxW, ⟨x, hxW, rfl⟩⟩
    by_cases hall : (U ∩ (quadratic c '' ((P \ W)ᶜ))ᶜ).Nonempty
    · -- both pieces nonempty would disconnect U
      obtain ⟨v, hvU, hv1, hv2⟩ := hUc.isPreconnected _ _ hfWo hcompl_open hcover hneW hall
      exfalso
      obtain ⟨y, hyW, rfl⟩ := hv1
      apply hv2
      refine ⟨y, ?_, rfl⟩
      rw [Set.mem_compl_iff, Set.mem_diff, not_and, not_not]
      intro _
      exact hyW
    · -- f(W) = U ∋ c, so 0 ∈ W
      have hUsub : U ⊆ quadratic c '' W := by
        intro u hu
        by_cases hw : u ∈ quadratic c '' W
        · exact hw
        · exfalso
          apply hall
          have hmem : u ∈ U \ quadratic c '' W := ⟨hu, hw⟩
          rw [hUdiff] at hmem
          exact ⟨u, hu, hmem.2⟩
      obtain ⟨y, hyW, hyc⟩ := hUsub hcU
      have hy0 : y = 0 := by
        have : y ^ 2 = 0 := by
          have := hyc
          unfold quadratic at this
          linear_combination this
        exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this
      rw [← hy0]
      exact hyW
  -- all components share 0, so P is connected
  refine ⟨⟨0, h0P⟩, ?_⟩
  have hPeq : P = connectedComponentIn P 0 := by
    apply Set.Subset.antisymm
    · intro x hx
      have h1 : connectedComponentIn P x = connectedComponentIn P 0 :=
        connectedComponentIn_eq (hcomp x hx)
      rw [← h1]
      exact mem_connectedComponentIn hx
    · exact connectedComponentIn_subset P 0
  rw [hPeq]
  exact isPreconnected_connectedComponentIn

/-- **The sublevel anchor**: for all sufficiently large `M`, the sublevel set `{G_c < M}` is
connected — every deep point rides a `ψ`-radial path (constant Böttcher angle, decreasing level)
into the central ball. -/
theorem exists_sublevel_anchor (c : ℂ) :
    ∃ M₁ : ℝ, ∀ M : ℝ, M₁ ≤ M → IsConnected {z : ℂ | greenFunctionDyn c z < M} := by
  classical
  set R : ℝ := 2 * max 2 ‖c‖ + 16 * ‖c‖ + 17 with hRdef
  have hmax2 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
  have hmaxc : ‖c‖ ≤ max 2 ‖c‖ := le_max_right _ _
  have hR1 : 2 * max 2 ‖c‖ < R := by rw [hRdef]; nlinarith [norm_nonneg c]
  have hR2 : 16 * ‖c‖ < R ^ 2 := by rw [hRdef]; nlinarith [norm_nonneg c]
  have hRpos : (0:ℝ) < R := by rw [hRdef]; nlinarith [norm_nonneg c]
  obtain ⟨ψ, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far hR1 hR2
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  set R₁ : ℝ := max R' 1 with hR₁def
  have hR₁pos : (0:ℝ) < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the level identity along ψ
  have hGψ : ∀ v : ℂ, R₁ < ‖v‖ → greenFunctionDyn c (ψ v) = Real.log ‖v‖ := by
    intro v hv
    obtain ⟨zv, hzv, hzveq⟩ := hRpre v (lt_of_le_of_lt (le_max_left _ _) hv)
    have hzvc : ‖c‖ ≤ ‖zv‖ := by
      have : max 2 ‖c‖ < R := by nlinarith [norm_nonneg c]
      linarith [le_trans hmaxc this.le, hzv]
    have hzv2 : 2 < ‖zv‖ := by
      have : max 2 ‖c‖ < R := by nlinarith [norm_nonneg c]
      linarith [le_trans hmax2 this.le, hzv]
    have hK : zv ∉ filledJulia c := not_mem_filledJulia hzvc hzv2
    have hψv : ψ v = zv := by rw [← hzveq]; exact hψleft zv hzv
    rw [hψv]
    unfold greenFunctionDyn
    rw [if_neg hK]
    have hnorm := norm_bottcherCoord hzvc hzv2
    rw [← hzveq, hnorm]
    unfold bottcherModulus
    rw [Real.log_exp]
  -- ψ is continuous at deep points
  have hψcont : ∀ v : ℂ, R₁ < ‖v‖ → ContinuousAt ψ v := by
    intro v hv
    obtain ⟨zv, hzv, hzveq⟩ := hRpre v (lt_of_le_of_lt (le_max_left _ _) hv)
    rw [← hzveq]
    exact (hψan zv hzv).continuousAt
  set M₁ : ℝ := Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) + Real.log (R + R₁ + 3) + 10 with hM₁def
  have hlog1 : 0 ≤ Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) :=
    Real.log_nonneg (by nlinarith [norm_nonneg c])
  have hlog2 : Real.log R < Real.log (R + R₁ + 3) := Real.log_lt_log hRpos (by linarith)
  have hlog2' : Real.log R₁ < Real.log (R + R₁ + 3) := Real.log_lt_log hR₁pos (by linarith)
  have hlog2'' : 0 ≤ Real.log (R + R₁ + 3) := Real.log_nonneg (by nlinarith)
  refine ⟨M₁, ?_⟩
  intro M hM
  set Ω : Set ℂ := {z : ℂ | greenFunctionDyn c z < M} with hΩdef
  have hΩo : IsOpen Ω := isOpen_lt (continuous_greenFunctionDyn c) continuous_const
  have hM4 : Real.log ((max 2 ‖c‖) ^ 2 + ‖c‖) + 4 ≤ M := by
    rw [hM₁def] at hM; linarith
  have hMR : Real.log (R + R₁ + 3) + 4 ≤ M := by
    rw [hM₁def] at hM; linarith
  -- the central ball
  set B : Set ℂ := ball (0:ℂ) (Real.exp (M - 1)) with hBdef
  have hBΩ : B ⊆ Ω := by
    intro y hy
    rw [hBdef, mem_ball, dist_zero_right] at hy
    show greenFunctionDyn c y < M
    by_cases hyc : ‖y‖ ≤ max 2 ‖c‖
    · have := greenFunctionDyn_le_small (c := c) hyc
      linarith
    · push Not at hyc
      have hy2 : 2 < ‖y‖ := lt_of_le_of_lt hmax2 hyc
      have hycn : ‖c‖ ≤ ‖y‖ := le_of_lt (lt_of_le_of_lt hmaxc hyc)
      have := greenFunctionDyn_le_crude hycn hy2
      have hlogy : Real.log ‖y‖ < M - 1 := by
        calc Real.log ‖y‖ < Real.log (Real.exp (M - 1)) :=
              Real.log_lt_log (by linarith) hy
          _ = M - 1 := Real.log_exp _
      linarith
  have h0Ω : (0:ℂ) ∈ Ω := hBΩ (by
    rw [hBdef, mem_ball, dist_zero_right, norm_zero]
    positivity)
  have h0B : (0:ℂ) ∈ B := by
    rw [hBdef, mem_ball, dist_zero_right, norm_zero]
    positivity
  -- ψ lands deep
  have hψdeep : ∀ v : ℂ, R₁ < ‖v‖ → R < ‖ψ v‖ := by
    intro v hv
    obtain ⟨zv, hzv, hzveq⟩ := hRpre v (lt_of_le_of_lt (le_max_left _ _) hv)
    have hψv : ψ v = zv := by rw [← hzveq]; exact hψleft zv hzv
    rw [hψv]
    exact hzv
  -- every point joins the component of 0
  have hjoin : ∀ z ∈ Ω, z ∈ connectedComponentIn Ω 0 := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact (convex_ball _ _).isPreconnected.subset_connectedComponentIn h0B hBΩ hzB
    · rw [hBdef, mem_ball, dist_zero_right] at hzB
      push Not at hzB
      have hzR : R < ‖z‖ := by
        have h2 : R < Real.exp (M - 1) := by
          calc R = Real.exp (Real.log R) := (Real.exp_log hRpos).symm
            _ < Real.exp (M - 1) := Real.exp_lt_exp.mpr (by linarith)
        linarith
      have hmaxR : max 2 ‖c‖ < R := by nlinarith [norm_nonneg c]
      have hzc : ‖c‖ ≤ ‖z‖ := by linarith [le_trans hmaxc hmaxR.le]
      have hz2 : 2 < ‖z‖ := by linarith [le_trans hmax2 hmaxR.le]
      have hzK : z ∉ filledJulia c := not_mem_filledJulia hzc hz2
      set w : ℂ := bottcherCoord c z with hwdef
      have hwnorm : ‖w‖ = Real.exp (greenLimit c z) := by
        rw [hwdef, norm_bottcherCoord hzc hz2]
        unfold bottcherModulus
        rfl
      have hGz : greenFunctionDyn c z = greenLimit c z := by
        unfold greenFunctionDyn; rw [if_neg hzK]
      have hlogw : Real.log ‖w‖ = greenFunctionDyn c z := by
        rw [hwnorm, Real.log_exp, hGz]
      have hwpos : (0:ℝ) < ‖w‖ := by rw [hwnorm]; positivity
      have hwne : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hwpos; exact lt_irrefl _ hwpos
      set ρ₁ : ℝ := Real.exp (M - 2) with hρ₁def
      have hρ₁pos : 0 < ρ₁ := Real.exp_pos _
      have hρ₁R₁ : R₁ < ρ₁ := by
        calc R₁ = Real.exp (Real.log R₁) := (Real.exp_log hR₁pos).symm
          _ < Real.exp (M - 2) := by
            apply Real.exp_lt_exp.mpr
            have : Real.log R₁ ≤ Real.log (R + R₁ + 3) :=
              Real.log_le_log hR₁pos (by linarith)
            linarith
      -- corr bound at deep points
      have hcorrbound : ∀ y : ℂ, R < ‖y‖ → 2 * ‖c‖ / ‖y‖ ^ 2 < 1 := by
        intro y hy
        have hypos : (0:ℝ) < ‖y‖ := lt_trans hRpos hy
        rw [div_lt_one (by positivity)]
        nlinarith [norm_nonneg c]
      -- the level of w is at least M − 2
      have hwlev : M - 2 ≤ Real.log ‖w‖ := by
        have h1 : Real.log ‖z‖ - 1 ≤ greenFunctionDyn c z := by
          have habs := greenLimit_abs_sub_log hzc hz2
          have hcorr : 2 * ‖c‖ / ‖z‖ ^ 2 < 1 := hcorrbound z hzR
          rw [hGz]
          have := (abs_le.mp habs).1
          linarith
        have h2 : M - 1 ≤ Real.log ‖z‖ := by
          calc M - 1 = Real.log (Real.exp (M - 1)) := (Real.log_exp _).symm
            _ ≤ Real.log ‖z‖ := Real.log_le_log (Real.exp_pos _) hzB
        rw [hlogw]
        linarith
      have hρ₁w : ρ₁ ≤ ‖w‖ := by
        calc ρ₁ = Real.exp (M - 2) := rfl
          _ ≤ Real.exp (Real.log ‖w‖) := Real.exp_le_exp.mpr hwlev
          _ = ‖w‖ := Real.exp_log hwpos
      -- the radial path
      set rad : ℝ → ℝ := fun t => (1 - t) * ‖w‖ + t * ρ₁ with hraddef
      set p : ℝ → ℂ := fun t => ψ (((rad t : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w) with hpdef
      have hradmem : ∀ t ∈ Set.Icc (0:ℝ) 1, ρ₁ ≤ rad t ∧ rad t ≤ ‖w‖ := by
        intro t ht
        constructor
        · rw [hraddef]
          simp only
          nlinarith [ht.1, ht.2]
        · rw [hraddef]
          simp only
          nlinarith [ht.1, ht.2]
      have hargnorm : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
          ‖((rad t : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w‖ = rad t := by
        intro t ht
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hρ₁pos
            (hradmem t ht).1), abs_of_pos hwpos]
        field_simp
      have hargdeep : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
          R₁ < ‖((rad t : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w‖ := by
        intro t ht
        rw [hargnorm t ht]
        exact lt_of_lt_of_le hρ₁R₁ (hradmem t ht).1
      have hplev : ∀ t ∈ Set.Icc (0:ℝ) 1, greenFunctionDyn c (p t) = Real.log (rad t) := by
        intro t ht
        rw [hpdef]
        simp only
        rw [hGψ _ (hargdeep t ht), hargnorm t ht]
      have hpΩ : ∀ t ∈ Set.Icc (0:ℝ) 1, p t ∈ Ω := by
        intro t ht
        show greenFunctionDyn c (p t) < M
        rw [hplev t ht]
        calc Real.log (rad t) ≤ Real.log ‖w‖ :=
              Real.log_le_log (lt_of_lt_of_le hρ₁pos (hradmem t ht).1) (hradmem t ht).2
          _ = greenFunctionDyn c z := hlogw
          _ < M := hz
      have hpcont : ContinuousOn p (Set.Icc (0:ℝ) 1) := by
        intro t ht
        have hargcont : Continuous (fun s : ℝ =>
            ((rad s : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w) := by
          rw [hraddef]
          fun_prop
        have hcomp : ContinuousAt
            (ψ ∘ fun s : ℝ => ((rad s : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w) t :=
          ContinuousAt.comp (g := ψ)
            (f := fun s : ℝ => ((rad s : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w)
            (hψcont _ (hargdeep t ht)) hargcont.continuousAt
        exact hcomp.continuousWithinAt
      have hp0 : p 0 = z := by
        rw [hpdef]
        simp only
        have harg : ((rad 0 : ℝ) : ℂ) * (((‖w‖ : ℝ) : ℂ))⁻¹ * w = w := by
          rw [hraddef]
          simp only
          rw [show ((1:ℝ) - 0) * ‖w‖ + 0 * ρ₁ = ‖w‖ from by ring]
          have hne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero]
            linarith
          field_simp
        rw [harg, hwdef]
        exact hψleft z hzR
      have hp1B : p 1 ∈ B := by
        have hp1lev : greenFunctionDyn c (p 1) = M - 2 := by
          rw [hplev 1 (by constructor <;> norm_num)]
          rw [hraddef]
          simp only
          rw [show ((1:ℝ) - 1) * ‖w‖ + 1 * ρ₁ = ρ₁ from by ring, hρ₁def, Real.log_exp]
        have hp1deep : R < ‖p 1‖ := by
          rw [hpdef]
          exact hψdeep _ (hargdeep 1 (by constructor <;> norm_num))
        have hp1c : ‖c‖ ≤ ‖p 1‖ := by linarith [le_trans hmaxc hmaxR.le]
        have hp12 : 2 < ‖p 1‖ := by linarith [le_trans hmax2 hmaxR.le]
        have hp1K : p 1 ∉ filledJulia c := not_mem_filledJulia hp1c hp12
        have habs := greenLimit_abs_sub_log hp1c hp12
        have hcorr := hcorrbound (p 1) hp1deep
        have hGp1 : greenFunctionDyn c (p 1) = greenLimit c (p 1) := by
          unfold greenFunctionDyn; rw [if_neg hp1K]
        have hlogp1 : Real.log ‖p 1‖ < M - 1 := by
          have h1 := (abs_le.mp habs).1
          rw [← hGp1, hp1lev] at h1
          linarith
        rw [hBdef, mem_ball, dist_zero_right]
        calc ‖p 1‖ = Real.exp (Real.log ‖p 1‖) :=
              (Real.exp_log (by linarith : (0:ℝ) < ‖p 1‖)).symm
          _ < Real.exp (M - 1) := Real.exp_lt_exp.mpr hlogp1
      -- absorb the path into the component of 0
      have hKp : IsPreconnected (p '' Set.Icc (0:ℝ) 1) :=
        (isPreconnected_Icc).image p hpcont
      have hKpΩ : p '' Set.Icc (0:ℝ) 1 ⊆ Ω := by
        rintro y ⟨t, ht, rfl⟩
        exact hpΩ t ht
      have hp1mem : p 1 ∈ p '' Set.Icc (0:ℝ) 1 :=
        ⟨1, by constructor <;> norm_num, rfl⟩
      have h1 : p '' Set.Icc (0:ℝ) 1 ⊆ connectedComponentIn Ω (p 1) :=
        hKp.subset_connectedComponentIn hp1mem hKpΩ
      have h2 : p 1 ∈ connectedComponentIn Ω 0 :=
        (convex_ball _ _).isPreconnected.subset_connectedComponentIn h0B hBΩ hp1B
      have h3 : connectedComponentIn Ω 0 = connectedComponentIn Ω (p 1) :=
        connectedComponentIn_eq h2
      rw [h3]
      apply h1
      rw [← hp0]
      exact ⟨0, by constructor <;> norm_num, rfl⟩
  refine ⟨⟨0, h0Ω⟩, ?_⟩
  have hΩeq : Ω = connectedComponentIn Ω 0 := by
    apply Set.Subset.antisymm
    · exact fun z hz => hjoin z hz
    · exact connectedComponentIn_subset Ω 0
  rw [hΩeq]
  exact isPreconnected_connectedComponentIn

/-- **Connectivity of Green sublevel sets above the critical level.**  For `L > G_c(0)`,
`{G_c < L}` is connected: downward induction from the anchor by
`{G < L} = f_c⁻¹({G < 2L})` and the critical-value preimage lemma. -/
theorem isConnected_green_sublevel (c : ℂ) {L : ℝ}
    (hL : greenFunctionDyn c 0 < L) :
    IsConnected {z : ℂ | greenFunctionDyn c z < L} := by
  obtain ⟨M₁, hM₁⟩ := exists_sublevel_anchor c
  have hLpos : 0 < L := lt_of_le_of_lt (greenFunctionDyn_nonneg c 0) hL
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M₁ ≤ 2 ^ n * L := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M₁ / L) (one_lt_two (α := ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hLpos] at hn
    linarith
  suffices h : ∀ k : ℕ, k ≤ n → IsConnected {z : ℂ | greenFunctionDyn c z < 2 ^ (n - k) * L} by
    have := h n (le_refl n)
    simpa using this
  intro k
  induction k with
  | zero =>
      intro _
      have harg : n - 0 = n := by omega
      rw [harg]
      exact hM₁ _ hn
  | succ m ih =>
      intro hmn
      have hprev := ih (by omega)
      have hsplit : n - m = (n - (m + 1)) + 1 := by omega
      have harg : {z : ℂ | greenFunctionDyn c z < 2 ^ (n - (m + 1)) * L}
          = (quadratic c) ⁻¹' {z : ℂ | greenFunctionDyn c z < 2 ^ (n - m) * L} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_setOf_eq, greenFunctionDyn_quadratic]
        rw [hsplit, pow_succ]
        constructor <;> intro h <;> nlinarith [greenFunctionDyn_nonneg c z]
      rw [harg]
      apply isConnected_quadratic_preimage
        (isOpen_lt (continuous_greenFunctionDyn c) continuous_const) hprev
      show greenFunctionDyn c c < 2 ^ (n - m) * L
      have hGc : greenFunctionDyn c c = 2 * greenFunctionDyn c 0 := by
        have := greenFunctionDyn_quadratic c 0
        rw [show quadratic c 0 = c from by unfold quadratic; ring] at this
        exact this
      have h2nm : (2:ℝ) ≤ 2 ^ (n - m) := by
        have h1 : 1 ≤ n - m := by omega
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - m) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
      rw [hGc]
      nlinarith [greenFunctionDyn_nonneg c 0]

end Bottcher
