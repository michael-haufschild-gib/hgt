/-
# The one-slit scaffold chain

The bridging pieces of the Böttcher tower data all live on ONE fixed arc annulus `A*`: radii
`(ra, RW)` with `2h < (2 log ra + log RW)/1` and `log RW < 4h`, arguments omitting the single ray
through the unique zero of `S.T − c` (which sits at radius `e^{2h}`).  Every deeper radicand
`σⱼ − c` (`j ≥ 1`) has its critical-value preimages at radius `e^{2^{j+1}h} > RW`, so the whole
chain `σⱼ₊₁ = √(σⱼ − c)` extracts on the SAME simply connected arc — no further slits.  Signs are
normalized by the doubling link `σⱼ₊₁(w²) = σⱼ(w)` on a fixed sub-box (branch-2 of the
argument-doubling preimage; pure interval arithmetic).  The chain carries analyticity, the level
identity, injectivity, nonvanishing derivative, the iterate identity `f^[j] ∘ σⱼ = S.T`, the
square link, and the doubling link.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherTowerScaffold

open Complex Set Filter Metric Topology

namespace Bottcher

/-- Squaring maps an arc annulus into the arc annulus of doubled logs, arguments shifted by
one full turn. -/
theorem sq_mem_arcAnnulus {r R α β r' R' J₁ J₂ : ℝ}
    (hr' : Real.log r ≤ 2 * Real.log r') (hR' : 2 * Real.log R' ≤ Real.log R)
    (hJ₁ : α ≤ 2 * J₁ - 2 * Real.pi) (hJ₂ : 2 * J₂ - 2 * Real.pi ≤ β)
    {w : ℂ} (hw : w ∈ arcAnnulus r' R' J₁ J₂) : w ^ 2 ∈ arcAnnulus r R α β := by
  obtain ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ := hw
  refine ⟨2 * ξ - 2 * Real.pi * Complex.I, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show Real.log r < (2 * ξ - 2 * Real.pi * Complex.I).re
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show (2 * ξ - 2 * Real.pi * Complex.I).re < Real.log R
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show α < (2 * ξ - 2 * Real.pi * Complex.I).im
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show (2 * ξ - 2 * Real.pi * Complex.I).im < β
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · have h5 : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I 1
      simpa [mul_comm, mul_assoc] using this
    rw [Complex.exp_sub, h5, div_one, sq, ← Complex.exp_add]
    ring_nf

/-- The single-depth properties of a scaffold layer over the base section `S` on domain `A`. -/
def ScaffoldProps (c : ℂ) (S : ℂ → ℂ) (A : Set ℂ) (j : ℕ) (σj : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ σj A ∧
  (∀ v ∈ A, greenFunctionDyn c (σj v) = Real.log ‖v‖ / 2 ^ j) ∧
  Set.InjOn σj A ∧
  (∀ v ∈ A, deriv σj v ≠ 0) ∧
  (∀ v ∈ A, (quadratic c)^[j] (σj v) = S v)

/-- **The one-slit scaffold chain at a prescribed slit angle.**  The slit center `θs` is an
input, and the window `(θs + π/8, θs + 2π − π/8)` is exported by equations: any caller that
knows the critical-value preimage patch sits inside the excluded wedge (e.g. via
`PatchSquareLocalize`) can convert its own avoidance knowledge onto the working arc. -/
theorem exists_scaffold_chain_window {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo)
    {ra RW : ℝ} (hra : rlo < ra) (hraRW : ra ^ 2 < RW) (hRWR : RW < R₀)
    (hRW4h : Real.log RW < 4 * greenFunctionDyn c 0)
    (hh0 : 0 < greenFunctionDyn c 0)
    (hlow : greenFunctionDyn c 0 < Real.log rlo)
    {θs : ℝ} (hθs1 : -Real.pi ≤ θs) (hθs2 : θs ≤ 2 * Real.pi)
    (hslitne : ∀ v ∈ arcAnnulus ra RW (θs + Real.pi / 8) (θs + 2 * Real.pi - Real.pi / 8),
      S.T v ≠ c) :
    ∃ α β J₁ J₂ : ℝ, α = θs + Real.pi / 8 ∧ β = θs + 2 * Real.pi - Real.pi / 8 ∧
      α < β ∧ β ≤ α + 2 * Real.pi ∧
      α ≤ J₁ ∧ J₁ < J₂ ∧ J₂ ≤ β ∧ α ≤ 2 * J₁ - 2 * Real.pi ∧ 2 * J₂ - 2 * Real.pi ≤ β ∧
      ∃ σ : ℕ → ℂ → ℂ,
        σ 0 = S.T ∧
        (∀ j : ℕ, ScaffoldProps c S.T (arcAnnulus ra RW α β) j (σ j)) ∧
        (∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW α β, σ (j+1) v ^ 2 = σ j v - c) ∧
        (∀ j : ℕ, ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂,
          σ (j+1) (w ^ 2) = σ j w) ∧
        (∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW α β, σ j v ≠ 0) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hrapos : (0:ℝ) < ra := by linarith
  have hra1 : (1:ℝ) < ra := by nlinarith
  have hRW1 : (1:ℝ) < RW := by nlinarith
  have hraRW' : ra < RW := by nlinarith
  have hRWpos : (0:ℝ) < RW := by linarith
  have hlogra : (0:ℝ) < Real.log ra := Real.log_pos hra1
  have hlogRW : (0:ℝ) < Real.log RW := Real.log_pos hRW1
  have hlograRW : Real.log ra < Real.log RW := Real.log_lt_log hrapos hraRW'
  have hlograsq : 2 * Real.log ra < Real.log RW := by
    have h1 : Real.log (ra ^ 2) < Real.log RW := Real.log_lt_log (by positivity) hraRW
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  set m : ℝ := Real.pi / 8 with hmdef
  have hπ := Real.pi_pos
  set α : ℝ := θs + m with hαdef
  set β : ℝ := θs + 2 * Real.pi - m with hβdef
  have hαβ : α < β := by rw [hαdef, hβdef, hmdef]; linarith
  have hβα : β ≤ α + 2 * Real.pi := by rw [hαdef, hβdef]; linarith
  -- the branch-2 doubling window
  set J₁ : ℝ := max α (α / 2 + Real.pi) with hJ₁def
  set J₂ : ℝ := min β (β / 2 + Real.pi) with hJ₂def
  have hJ₁J₂ : J₁ < J₂ := by
    rw [hJ₁def, hJ₂def]
    apply max_lt <;> apply lt_min
    · exact hαβ
    · rw [hαdef, hβdef, hmdef]; linarith
    · rw [hαdef, hβdef, hmdef]; linarith
    · linarith
  have hαJ₁ : α ≤ J₁ := le_max_left _ _
  have hJ₂β : J₂ ≤ β := min_le_left _ _
  have hJ₁dbl : α ≤ 2 * J₁ - 2 * Real.pi := by
    have h1 : α / 2 + Real.pi ≤ J₁ := le_max_right _ _
    linarith
  have hJ₂dbl : 2 * J₂ - 2 * Real.pi ≤ β := by
    have h1 : J₂ ≤ β / 2 + Real.pi := min_le_right _ _
    linarith
  -- the fixed arc and its facts
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hAsc : IsSimplyConnected A := isSimplyConnected_arcAnnulus hrapos hraRW' hαβ hβα
  have hAsub : A ⊆ annulusSet ra RW := arcAnnulus_subset _ _ hrapos hraRW'
  have hAsubS : ∀ v ∈ A, v ∈ annulusSet rlo R₀ := fun v hv =>
    ⟨lt_trans hra (hAsub hv).1, lt_trans (hAsub hv).2 hRWR⟩
  have hlogv : ∀ v ∈ A, Real.log ra < Real.log ‖v‖ ∧ Real.log ‖v‖ < Real.log RW := by
    intro v hv
    exact ⟨Real.log_lt_log hrapos (hAsub hv).1,
      Real.log_lt_log (lt_trans hrapos (hAsub hv).1) (hAsub hv).2⟩
  -- the sub-box for the doubling link
  have hsqrtRW : Real.sqrt RW < RW := by
    have h1 : Real.sqrt RW < Real.sqrt (RW ^ 2) := by
      apply Real.sqrt_lt_sqrt (le_of_lt hRWpos)
      nlinarith
    rwa [Real.sqrt_sq (le_of_lt hRWpos)] at h1
  have hrasqrt : ra < Real.sqrt RW := by
    have h1 : Real.sqrt (ra ^ 2) < Real.sqrt RW :=
      Real.sqrt_lt_sqrt (by positivity) hraRW
    rwa [Real.sqrt_sq (le_of_lt hrapos)] at h1
  have hWsub : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ A := by
    intro w hw
    have h1 : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ arcAnnulus ra RW J₁ J₂ := by
      rintro z ⟨ξ, ⟨b1, b2, b3, b4⟩, rfl⟩
      exact ⟨ξ, ⟨b1, lt_of_lt_of_le b2 (Real.log_le_log (Real.sqrt_pos.mpr hRWpos)
        (le_of_lt hsqrtRW)), b3, b4⟩, rfl⟩
    exact arcAnnulus_mono hαJ₁ hJ₂β (h1 hw)
  have hWsq : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, w ^ 2 ∈ A := by
    intro w hw
    apply sq_mem_arcAnnulus (r' := ra) (R' := Real.sqrt RW) _ _ hJ₁dbl hJ₂dbl hw
    · linarith
    · rw [show 2 * Real.log (Real.sqrt RW) = Real.log RW from by
        rw [Real.log_sqrt (le_of_lt hRWpos)]; ring]
  have hWne : (arcAnnulus ra (Real.sqrt RW) J₁ J₂).Nonempty := by
    have := isConnected_arcAnnulus hrapos hrasqrt hJ₁J₂
    exact this.nonempty
  have hWconn : IsConnected (arcAnnulus ra (Real.sqrt RW) J₁ J₂) :=
    isConnected_arcAnnulus hrapos hrasqrt hJ₁J₂
  have hWopen : IsOpen (arcAnnulus ra (Real.sqrt RW) J₁ J₂) := isOpen_arcAnnulus _ _ _ _
  -- level positivity on A and on the window
  have hlevpos : ∀ v ∈ A, (0:ℝ) < Real.log ‖v‖ := fun v hv => lt_trans hlogra (hlogv v hv).1
  -- radicand nonvanishing at any depth
  have hrad_ne : ∀ j : ℕ, ∀ σj : ℂ → ℂ, ScaffoldProps c S.T A j σj →
      ∀ v ∈ A, σj v - c ≠ 0 := by
    intro j σj hP v hv hcon
    obtain ⟨han, hlev, hinj, hdne, hit⟩ := hP
    have hveq : σj v = c := sub_eq_zero.mp hcon
    have h1 := hlev v hv
    rw [hveq, greenFunctionDyn_critical_value c] at h1
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have h2 : σj v = S.T v := by
        have := hit v hv
        simpa using this
      exact hslitne v hv (by rw [← h2, hveq])
    · have h2 : Real.log ‖v‖ = 2 ^ j * (2 * h) := by
        field_simp at h1
        linarith
      have h3 : (2:ℝ) ^ j ≥ 2 := by
        calc (2:ℝ) ^ j ≥ 2 ^ 1 := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
          _ = 2 := by norm_num
      have h4 := (hlogv v hv).2
      nlinarith
  -- the pair invariant
  set W : Set ℂ := arcAnnulus ra (Real.sqrt RW) J₁ J₂ with hWdef
  set PairProps : ℕ → (ℂ → ℂ) → (ℂ → ℂ) → Prop := fun j σa σb =>
    ScaffoldProps c S.T A j σa ∧ ScaffoldProps c S.T A (j+1) σb ∧
    (∀ v ∈ A, σb v ^ 2 = σa v - c) ∧
    (∀ w ∈ W, σb (w ^ 2) = σa w) ∧
    (∀ v ∈ A, σa v ≠ 0) ∧ (∀ v ∈ A, σb v ≠ 0) with hPPdef
  -- generic root extraction with all ScaffoldProps
  have hroot : ∀ j : ℕ, ∀ σj : ℂ → ℂ, ScaffoldProps c S.T A j σj →
      ∃ s : ℂ → ℂ, ScaffoldProps c S.T A (j+1) s ∧ (∀ v ∈ A, s v ^ 2 = σj v - c) ∧
        (∀ v ∈ A, s v ≠ 0) := by
    intro j σj hP
    obtain ⟨han, hlev, hinj, hdne, hit⟩ := hP
    have hg_ne := hrad_ne j σj ⟨han, hlev, hinj, hdne, hit⟩
    have hg_an : AnalyticOnNhd ℂ (fun v => σj v - c) A := fun v hv =>
      (han v hv).sub analyticAt_const
    obtain ⟨s, hs_an, hs_sq⟩ := exists_analyticOnNhd_pow_eq hAsc hAopen hg_an hg_ne
      (by norm_num : 1 ≤ 2)
    have hs_ne : ∀ v ∈ A, s v ≠ 0 := by
      intro v hv h0
      have h1 := hs_sq v hv
      rw [h0, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
      exact hg_ne v hv h1.symm
    refine ⟨s, ⟨hs_an, ?_, ?_, ?_, ?_⟩, hs_sq, hs_ne⟩
    · intro v hv
      have hfe : quadratic c (s v) = σj v := by
        unfold quadratic
        rw [hs_sq v hv]
        ring
      have h1 := greenFunctionDyn_quadratic c (s v)
      rw [hfe, hlev v hv] at h1
      rw [pow_succ]
      field_simp at h1 ⊢
      linarith
    · intro v₁ h₁ v₂ h₂ heq
      have h3 : σj v₁ = σj v₂ := by
        have e1 := hs_sq v₁ h₁
        have e2 := hs_sq v₂ h₂
        have h4 : σj v₁ - c = σj v₂ - c := by rw [← e1, ← e2, heq]
        linear_combination h4
      exact hinj h₁ h₂ h3
    · intro v hv
      have hs_d : HasDerivAt s (deriv s v) v := (hs_an v hv).differentiableAt.hasDerivAt
      have hLd : HasDerivAt (fun x => s x ^ 2) (2 * s v * deriv s v) v := by
        have h4 := hs_d.pow 2
        have h5 : (2:ℕ) * s v ^ (2 - 1) * deriv s v = 2 * s v * deriv s v := by
          push_cast
          ring
        rwa [h5] at h4
      have hRd : HasDerivAt (fun x => σj x - c) (deriv σj v) v :=
        ((han v hv).differentiableAt.hasDerivAt).sub_const c
      have hEqF : (fun x => s x ^ 2) =ᶠ[nhds v] (fun x => σj x - c) := by
        filter_upwards [hAopen.mem_nhds hv] with z hz
        exact hs_sq z hz
      have h7 : HasDerivAt (fun x => σj x - c) (2 * s v * deriv s v) v :=
        hLd.congr_of_eventuallyEq hEqF.symm
      have hEqD : deriv σj v = 2 * s v * deriv s v := hRd.unique h7
      intro h0
      rw [h0, mul_zero] at hEqD
      exact hdne v hv hEqD
    · intro v hv
      have hfe : quadratic c (s v) = σj v := by
        unfold quadratic
        rw [hs_sq v hv]
        ring
      rw [Function.iterate_succ_apply, hfe]
      exact hit v hv
  -- negating a layer preserves everything except the links
  have hneg_layer : ∀ j : ℕ, ∀ s : ℂ → ℂ, 1 ≤ j → ScaffoldProps c S.T A j s →
      ScaffoldProps c S.T A j (fun v => -s v) := by
    intro j s hj hP
    obtain ⟨han, hlev, hinj, hdne, hit⟩ := hP
    refine ⟨han.neg, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [← hlev v hv]
      show greenFunctionDyn c (-(s v)) = _
      rw [greenFunctionDyn_neg]
    · intro v₁ h₁ v₂ h₂ heq
      apply hinj h₁ h₂
      have h3 : -(s v₁) = -(s v₂) := heq
      linear_combination -h3
    · intro v hv
      have h1 : HasDerivAt s (deriv s v) v := (han v hv).differentiableAt.hasDerivAt
      have h2 : deriv (fun x => -s x) v = -deriv s v := h1.neg.deriv
      rw [h2]
      simpa using hdne v hv
    · intro v hv
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, Function.iterate_succ_apply]
      have h1 : quadratic c (-(s v)) = quadratic c (s v) := by
        unfold quadratic
        ring_nf
      show (quadratic c)^[j'] ((quadratic c) (-s v)) = S.T v
      rw [h1, ← Function.iterate_succ_apply]
      have := hit v hv
      rwa [add_comm 1 j'] at this
  -- the sign-matched step for pairs
  have hstep : ∀ j : ℕ, ∀ σa σb : ℂ → ℂ, PairProps j σa σb →
      ∃ σc : ℂ → ℂ, PairProps (j+1) σb σc := by
    intro j σa σb hPP
    obtain ⟨hPa, hPb, hsq, hdbl, haneA, hbneA⟩ := hPP
    obtain ⟨s, hPs, hs_sq, hs_ne'⟩ := hroot (j+1) σb hPb
    -- the doubling dichotomy against σb
    have hdich : ∀ w ∈ W, s (w ^ 2) = σb w ∨ s (w ^ 2) = -σb w := by
      intro w hw
      have h1 : s (w ^ 2) ^ 2 = σb (w ^ 2) - c := hs_sq _ (hWsq w hw)
      have h2 : σb w ^ 2 = σa w - c := hsq w (hWsub hw)
      have h3 : σb (w ^ 2) = σa w := hdbl w hw
      have h4 : s (w ^ 2) ^ 2 = σb w ^ 2 := by rw [h1, h3, ← h2]
      have h5 : (s (w ^ 2) - σb w) * (s (w ^ 2) + σb w) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact Or.inl (sub_eq_zero.mp h6)
      · exact Or.inr (by linear_combination h6)
    have hucont : ∀ w ∈ W, ContinuousAt (fun x => s (x ^ 2)) w := by
      intro w hw
      have h1 : ContinuousAt s (w ^ 2) := (hPs.1 _ (hWsq w hw)).continuousAt
      have h2 : ContinuousAt (fun x : ℂ => x ^ 2) w := (continuous_pow 2).continuousAt
      exact ContinuousAt.comp (x := w) (g := s) (f := fun x : ℂ => x ^ 2) h1 h2
    have hbne : ∀ w ∈ W, σb w ≠ 0 := by
      intro w hw hcon
      have h1 := hsq w (hWsub hw)
      rw [hcon, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
      exact hrad_ne j σa hPa w (hWsub hw) h1.symm
    have hsign := sign_constant_on_connected hWopen hWconn
      (u := fun w => s (w ^ 2)) (v := σb)
      hucont
      (fun w hw => (hPb.1 w (hWsub hw)).continuousAt)
      hbne
      hdich
    rcases hsign with hpos | hneg
    · exact ⟨s, hPb, hPs, hs_sq, hpos, hbneA, hs_ne'⟩
    · refine ⟨fun v => -s v, hPb, hneg_layer (j+2) s (by omega) hPs, ?_, ?_, hbneA, ?_⟩
      · intro v hv
        have := hs_sq v hv
        show (-s v) ^ 2 = σb v - c
        rw [neg_pow]
        simpa using this
      · intro w hw
        show -s (w ^ 2) = σb w
        have h1 : s (w ^ 2) = -σb w := hneg w hw
        rw [h1]
        ring
      · intro v hv
        show -s v ≠ 0
        simpa using hs_ne' v hv
  -- the base pair
  have hbase : ∃ σ₁ : ℂ → ℂ, PairProps 0 S.T σ₁ := by
    have hP0 : ScaffoldProps c S.T A 0 S.T := by
      refine ⟨S.an.mono hAsubS, ?_, S.inj.mono hAsubS, fun v hv => S.dne v (hAsubS v hv), ?_⟩
      · intro v hv
        rw [S.level v (hAsubS v hv)]
        simp
      · intro v hv
        simp
    obtain ⟨s, hPs, hs_sq, hs_ne'⟩ := hroot 0 S.T hP0
    have hTneA : ∀ v ∈ A, S.T v ≠ 0 := by
      intro v hv hcon
      have h1 := S.level v (hAsubS v hv)
      rw [hcon] at h1
      have h3 := (hlogv v hv).1
      have h4 : Real.log rlo < Real.log ra := Real.log_lt_log (by linarith) hra
      have h5 : greenFunctionDyn c 0 < Real.log rlo := hlow
      linarith
    have hdich : ∀ w ∈ W, s (w ^ 2) = S.T w ∨ s (w ^ 2) = -S.T w := by
      intro w hw
      have h1 : s (w ^ 2) ^ 2 = S.T (w ^ 2) - c := hs_sq _ (hWsq w hw)
      have h2 : S.T (w ^ 2) = S.T w ^ 2 + c :=
        S.fe w (hAsubS w (hWsub hw)) (hAsubS _ (hWsq w hw))
      have h4 : s (w ^ 2) ^ 2 = S.T w ^ 2 := by rw [h1, h2]; ring
      have h5 : (s (w ^ 2) - S.T w) * (s (w ^ 2) + S.T w) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact Or.inl (sub_eq_zero.mp h6)
      · exact Or.inr (by linear_combination h6)
    have hTneW : ∀ w ∈ W, S.T w ≠ 0 := by
      intro w hw hcon
      have h1 := S.level w (hAsubS w (hWsub hw))
      rw [hcon] at h1
      have h3 := (hlogv w (hWsub hw)).1
      have h4 : Real.log rlo < Real.log ra := Real.log_lt_log (by linarith) hra
      linarith
    have hucont : ∀ w ∈ W, ContinuousAt (fun x => s (x ^ 2)) w := by
      intro w hw
      have h1 : ContinuousAt s (w ^ 2) := (hPs.1 _ (hWsq w hw)).continuousAt
      have h2 : ContinuousAt (fun x : ℂ => x ^ 2) w := (continuous_pow 2).continuousAt
      exact ContinuousAt.comp (x := w) (g := s) (f := fun x : ℂ => x ^ 2) h1 h2
    have hsign := sign_constant_on_connected hWopen hWconn
      (u := fun w => s (w ^ 2)) (v := S.T)
      hucont
      (fun w hw => (S.an w (hAsubS w (hWsub hw))).continuousAt)
      hTneW hdich
    have hP0' : ScaffoldProps c S.T A 0 S.T := hP0
    rcases hsign with hpos | hneg
    · exact ⟨s, hP0', hPs, hs_sq, hpos, hTneA, hs_ne'⟩
    · refine ⟨fun v => -s v, hP0', hneg_layer 1 s le_rfl hPs, ?_, ?_, hTneA, ?_⟩
      · intro v hv
        have := hs_sq v hv
        show (-s v) ^ 2 = S.T v - c
        rw [neg_pow]
        simpa using this
      · intro w hw
        show -s (w ^ 2) = S.T w
        have h1 : s (w ^ 2) = -S.T w := hneg w hw
        rw [h1]
        ring
      · intro v hv
        show -s v ≠ 0
        simpa using hs_ne' v hv
  obtain ⟨σ₁, hpair0⟩ := hbase
  choose! nextfn hnextfn using hstep
  -- the chain of consecutive pairs
  set chain : ℕ → (ℂ → ℂ) × (ℂ → ℂ) := fun n =>
    Nat.rec ((S.T, σ₁) : (ℂ → ℂ) × (ℂ → ℂ))
      (fun j p => (p.2, nextfn j p.1 p.2)) n with hchaindef
  have hchain : ∀ j : ℕ, PairProps j (chain j).1 (chain j).2 := by
    intro j
    induction j with
    | zero => exact hpair0
    | succ n ih => exact hnextfn n (chain n).1 (chain n).2 ih
  have hchainlink : ∀ j : ℕ, (chain (j+1)).1 = (chain j).2 := fun j => rfl
  set σ : ℕ → ℂ → ℂ := fun j => (chain j).1 with hσdef
  have hσsucc : ∀ j : ℕ, σ (j+1) = (chain j).2 := fun j => rfl
  refine ⟨α, β, J₁, J₂, by rw [hαdef, hmdef], by rw [hβdef, hmdef], hαβ, hβα, hαJ₁, hJ₁J₂, hJ₂β, hJ₁dbl, hJ₂dbl, σ, rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hchain j).1
  · intro j v hv
    have := (hchain j).2.2.1 v hv
    rwa [← hσsucc j] at this
  · intro j w hw
    have := (hchain j).2.2.2.1 w hw
    rwa [← hσsucc j] at this
  · intro j v hv
    exact (hchain j).2.2.2.2.1 v hv

/-- **The one-slit scaffold chain.** -/
theorem exists_scaffold_chain {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo)
    {ra RW : ℝ} (hra : rlo < ra) (hraRW : ra ^ 2 < RW) (hRWR : RW < R₀)
    (hRW4h : Real.log RW < 4 * greenFunctionDyn c 0)
    (hh0 : 0 < greenFunctionDyn c 0)
    (hlow : greenFunctionDyn c 0 < Real.log rlo) :
    ∃ α β J₁ J₂ : ℝ, α < β ∧ β ≤ α + 2 * Real.pi ∧
      α ≤ J₁ ∧ J₁ < J₂ ∧ J₂ ≤ β ∧ α ≤ 2 * J₁ - 2 * Real.pi ∧ 2 * J₂ - 2 * Real.pi ≤ β ∧
      ∃ σ : ℕ → ℂ → ℂ,
        σ 0 = S.T ∧
        (∀ j : ℕ, ScaffoldProps c S.T (arcAnnulus ra RW α β) j (σ j)) ∧
        (∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW α β, σ (j+1) v ^ 2 = σ j v - c) ∧
        (∀ j : ℕ, ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂,
          σ (j+1) (w ^ 2) = σ j w) ∧
        (∀ j : ℕ, ∀ v ∈ arcAnnulus ra RW α β, σ j v ≠ 0) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hrapos : (0:ℝ) < ra := by linarith
  have hraRW' : ra < RW := by nlinarith
  set m : ℝ := Real.pi / 8 with hmdef
  have hπ := Real.pi_pos
  -- the slit angle: through the unique S.T = c point of the band, or 0
  have hslit : ∃ θs : ℝ, -Real.pi ≤ θs ∧ θs ≤ Real.pi ∧
      ∀ v ∈ arcAnnulus ra RW (θs + m) (θs + 2 * Real.pi - m), S.T v ≠ c := by
    by_cases hzero : ∃ vz ∈ annulusSet ra RW, S.T vz = c
    · obtain ⟨vz, hvz, hPvz⟩ := hzero
      have hvzne : vz ≠ 0 := by
        intro h0
        rw [h0] at hvz
        simp only [annulusSet, mem_setOf_eq, norm_zero] at hvz
        linarith [hvz.1]
      refine ⟨Complex.arg vz, (Complex.neg_pi_lt_arg vz).le, Complex.arg_le_pi vz, ?_⟩
      intro v hv hveq
      have hvann : v ∈ annulusSet ra RW :=
        arcAnnulus_subset _ _ hrapos hraRW' hv
      have hveqz : v = vz := S.inj
        ⟨lt_trans hra hvann.1, lt_trans hvann.2 hRWR⟩
        ⟨lt_trans hra hvz.1, lt_trans hvz.2 hRWR⟩ (by rw [hveq, hPvz])
      obtain ⟨ξ, hξbox, hξexp⟩ := hv
      have hlogeq : Complex.exp ξ = Complex.exp (Complex.log vz) := by
        rw [hξexp, Complex.exp_log hvzne, hveqz]
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hlogeq
      have him' : ξ.im = Complex.arg vz + (n : ℝ) * (2 * Real.pi) := by
        have him := congrArg Complex.im hn
        rw [show ((n : ℂ) * (2 * Real.pi * Complex.I)) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I from by push_cast; ring] at him
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.log_im] at him
        rw [him]
        ring
      have h3 := hξbox.2.2.1
      have h4 := hξbox.2.2.2
      rw [him'] at h3 h4
      have h5 : m < (n : ℝ) * (2 * Real.pi) := by linarith
      have h6 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi - m := by linarith
      have h7 : (0:ℝ) < (n:ℝ) := by nlinarith
      have h8 : (n:ℝ) < 1 := by nlinarith
      have h9 : (0:ℤ) < n := by exact_mod_cast h7
      have h10 : n < (1:ℤ) := by exact_mod_cast h8
      omega
    · exact ⟨0, by linarith, by linarith, fun v hv hveq =>
        hzero ⟨v, arcAnnulus_subset _ _ hrapos hraRW' hv, hveq⟩⟩
  obtain ⟨θs, hθs1, hθs2, hslitne⟩ := hslit
  obtain ⟨α, β, J₁, J₂, _, _, hrest⟩ :=
    exists_scaffold_chain_window S hrlo hra hraRW hRWR hRW4h hh0 hlow hθs1
      (by linarith [Real.pi_pos] : θs ≤ 2 * Real.pi)
      (by rw [← hmdef]; exact hslitne)
  exact ⟨α, β, J₁, J₂, hrest⟩

/-- **Fold-0 doubling inclusion.**  Squaring maps an arc annulus into the arc annulus of
doubled logs with arguments doubled IN PLACE (no full-turn shift) — the branch-0 twin of
`sq_mem_arcAnnulus`.  Together the two folds realize both sign classes of the doubling link:
which one a given chain satisfies is exactly the branch parity of `σ_{j+1}`. -/
theorem sq_mem_arcAnnulus_fold0 {r R α β r' R' J₁ J₂ : ℝ}
    (hr' : Real.log r ≤ 2 * Real.log r') (hR' : 2 * Real.log R' ≤ Real.log R)
    (hJ₁ : α ≤ 2 * J₁) (hJ₂ : 2 * J₂ ≤ β)
    {w : ℂ} (hw : w ∈ arcAnnulus r' R' J₁ J₂) : w ^ 2 ∈ arcAnnulus r R α β := by
  obtain ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ := hw
  refine ⟨2 * ξ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show Real.log r < (2 * ξ).re
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show (2 * ξ).re < Real.log R
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show α < (2 * ξ).im
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · show (2 * ξ).im < β
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  · rw [sq, ← Complex.exp_add]
    ring_nf

/-- **The fold-0 doubling window always exists**: under the `[−π, π]` slit normalization the
in-place window `(max α (α/2), min β (β/2))` is a nonempty sub-interval of `(α, β)` whose
doubling stays in `(α, β)`. -/
theorem fold0_window_exists {θs m : ℝ} (hm : 0 < m) (hm8 : m ≤ Real.pi / 8)
    (hθs1 : -Real.pi ≤ θs) (hθs2 : θs ≤ Real.pi) :
    ∃ K₁ K₂ : ℝ, θs + m ≤ K₁ ∧ K₁ < K₂ ∧ K₂ ≤ θs + 2 * Real.pi - m ∧
      θs + m ≤ 2 * K₁ ∧ 2 * K₂ ≤ θs + 2 * Real.pi - m := by
  have hπ := Real.pi_pos
  set α : ℝ := θs + m with hαdef
  set β : ℝ := θs + 2 * Real.pi - m with hβdef
  refine ⟨max α (α / 2), min β (β / 2), le_max_left _ _, ?_, min_le_left _ _, ?_, ?_⟩
  · apply max_lt <;> apply lt_min
    · rw [hαdef, hβdef]; linarith
    · rw [hαdef, hβdef]; linarith
    · rw [hαdef, hβdef]; linarith
    · rw [hαdef, hβdef]; linarith
  · have h1 : α / 2 ≤ max α (α / 2) := le_max_right _ _
    linarith
  · have h1 : min β (β / 2) ≤ β / 2 := min_le_right _ _
    linarith
