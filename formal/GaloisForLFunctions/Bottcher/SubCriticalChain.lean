/-
# The sub-critical inverse-branch chain

Below the critical-value level `G_c(c) = 2h`, the inverse branches of `f_c` over a tower section
extract WITHOUT doubling: each step is a square root of `Sⱼ − c` on a fixed band annulus, whose
core winding about `c` VANISHES (the outside certificate `windInt_eq_zero_of_level_lt`: the loop
runs at levels below `2h`, and `c` sits at level `2h` in the connected superlevel set).  So
`exists_pow_root_on_annulus` applies with `m = 0`, and the chain
`S₀-chain = S.T`, `Sⱼ₊₁ = √(Σⱼ − c)` carries: analyticity, the level identity
`G_c ∘ Σⱼ = log‖·‖ / 2ʲ`, injectivity, nonvanishing derivative, and the iterate identity
`f^[j] ∘ Σⱼ = S.T` — the depth-`j` Branner–Hubbard lobe sections.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionInverse

open Complex Set Filter Metric

namespace Bottcher

/-- **The sub-critical chain.**  Over a band strictly below the critical-value level, the tower
section admits inverse-branch sections of every depth. -/
theorem exists_subcritical_chain {c : ℂ} {rlo R₀ : ℝ}
    (S : TowerSection c rlo R₀) (hrlo : 1 < rlo)
    {ra rb : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbR : rb < R₀)
    (hrb2h : Real.log rb < 2 * greenFunctionDyn c 0) :
    ∀ j : ℕ, ∃ Sj : ℂ → ℂ,
      AnalyticOnNhd ℂ Sj (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, greenFunctionDyn c (Sj v) = Real.log ‖v‖ / 2 ^ j) ∧
      Set.InjOn Sj (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, deriv Sj v ≠ 0) ∧
      (∀ v ∈ annulusSet ra rb, (quadratic c)^[j] (Sj v) = S.T v) := by
  classical
  have hrapos : (0:ℝ) < ra := by linarith
  have hra1 : (1:ℝ) < ra := by linarith
  have hsub : ∀ v : ℂ, v ∈ annulusSet ra rb → v ∈ annulusSet rlo R₀ := by
    rintro v ⟨h1, h2⟩
    exact ⟨lt_trans hra h1, lt_trans h2 hrbR⟩
  have hlogpos : ∀ v : ℂ, v ∈ annulusSet ra rb → 0 < Real.log ‖v‖ := by
    rintro v ⟨h1, h2⟩
    exact Real.log_pos (lt_trans hra1 h1)
  have hloglt : ∀ v : ℂ, v ∈ annulusSet ra rb → Real.log ‖v‖ < Real.log rb := by
    rintro v ⟨h1, h2⟩
    exact Real.log_lt_log (lt_trans hrapos h1) h2
  intro j
  induction j with
  | zero =>
      refine ⟨S.T, S.an.mono (fun v hv => hsub v hv), ?_, ?_, ?_, ?_⟩
      · intro v hv
        rw [S.level v (hsub v hv)]
        simp
      · exact S.inj.mono (fun v hv => hsub v hv)
      · exact fun v hv => S.dne v (hsub v hv)
      · intro v hv
        simp
  | succ j ih =>
      obtain ⟨Sj, han, hlev, hinj, hdne, hit⟩ := ih
      have h2pow : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      -- the radicand Σⱼ − c is analytic and nonvanishing on the band
      set g : ℂ → ℂ := fun v => Sj v - c with hgdef
      have hg_an : AnalyticOnNhd ℂ g (annulusSet ra rb) := fun v hv =>
        (han v hv).sub analyticAt_const
      have hg_ne : ∀ v ∈ annulusSet ra rb, g v ≠ 0 := by
        intro v hv h
        have hval : Sj v = c := sub_eq_zero.mp h
        have h1 := hlev v hv
        rw [hval, greenFunctionDyn_critical_value c] at h1
        have h2 : Real.log ‖v‖ / 2 ^ j ≤ Real.log ‖v‖ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hlogpos v hv]
        have h3 := hloglt v hv
        linarith
      -- the core winding about c vanishes: the outside certificate
      set ρ : ℝ := (ra + rb) / 2 with hρdef
      have hρ1 : ra < ρ := by rw [hρdef]; linarith
      have hρ2 : ρ < rb := by rw [hρdef]; linarith
      have hρpos : (0:ℝ) < ρ := by linarith
      have hcm : ∀ θ : ℝ, circleMap 0 ρ θ ∈ annulusSet ra rb :=
        circleMap_mem_annulusSet hρpos hρ1 hρ2
      set ℓj : C1Loop := sectionLoop han hcm with hℓdef
      have hwind0 : windInt ℓj c = 0 := by
        apply windInt_eq_zero_of_level_lt c ℓj
          (show (0:ℝ) < Real.log rb from Real.log_pos (by linarith))
        · intro θ
          show greenFunctionDyn c (Sj (circleMap 0 ρ θ)) ≤ Real.log rb
          rw [hlev _ (hcm θ)]
          have h1 : Real.log ‖circleMap 0 ρ θ‖ < Real.log rb := hloglt _ (hcm θ)
          have h2 : 0 < Real.log ‖circleMap 0 ρ θ‖ := hlogpos _ (hcm θ)
          have h3 : Real.log ‖circleMap 0 ρ θ‖ / 2 ^ j ≤ Real.log ‖circleMap 0 ρ θ‖ := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          linarith
        · exact lt_of_lt_of_le hrb2h (by
            rw [greenFunctionDyn_critical_value c])
      -- convert to the raw winding of the radicand
      have hgwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
          = ((2 ^ (1 : ℕ) * 0 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        have hcongr : ∀ θ : ℝ,
            logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
            = (ℓj.γ θ - c)⁻¹ * ℓj.γ' θ := by
          intro θ
          have h1 : logDeriv g (circleMap 0 ρ θ)
              = deriv Sj (circleMap 0 ρ θ) / (Sj (circleMap 0 ρ θ) - c) := by
            rw [logDeriv_apply]
            congr 1
            exact deriv_sub_const c
          rw [h1]
          show deriv Sj (circleMap 0 ρ θ) / (Sj (circleMap 0 ρ θ) - c)
              * (circleMap 0 ρ θ * Complex.I)
            = (Sj (circleMap 0 ρ θ) - c)⁻¹
              * (deriv Sj (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
          ring
        rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
        show windInt ℓj c = _
        rw [hwind0]
        push_cast
        ring
      obtain ⟨s, hs_an, hs_sq, hs_ne⟩ :=
        exists_pow_root_on_annulus hrapos hρ1 hρ2 hg_an hg_ne 1 0 hgwind
      have hs_sq' : ∀ v ∈ annulusSet ra rb, s v ^ (2 : ℕ) = Sj v - c := by
        intro v hv
        have := hs_sq v hv
        rwa [pow_one 2] at this
      refine ⟨s, hs_an, ?_, ?_, ?_, ?_⟩
      · -- level identity
        intro v hv
        have hfe : quadratic c (s v) = Sj v := by
          unfold quadratic
          rw [hs_sq' v hv]
          ring
        have h1 := greenFunctionDyn_quadratic c (s v)
        rw [hfe, hlev v hv] at h1
        rw [pow_succ]
        field_simp at h1 ⊢
        linarith
      · -- injectivity
        intro v₁ h₁ v₂ h₂ heq
        have h3 : Sj v₁ = Sj v₂ := by
          have e1 := hs_sq' v₁ h₁
          have e2 := hs_sq' v₂ h₂
          have : Sj v₁ - c = Sj v₂ - c := by rw [← e1, ← e2, heq]
          linear_combination this
        exact hinj h₁ h₂ h3
      · -- derivative nonvanishing
        intro v hv
        have hs_d : HasDerivAt s (deriv s v) v := (hs_an v hv).differentiableAt.hasDerivAt
        have hLd : HasDerivAt (fun x => s x ^ (2 : ℕ)) (2 * s v * deriv s v) v := by
          have h4 := hs_d.pow 2
          have h5 : (2:ℕ) * s v ^ (2 - 1) * deriv s v = 2 * s v * deriv s v := by
            push_cast
            ring
          rwa [h5] at h4
        have hRd : HasDerivAt (fun x => Sj x - c) (deriv Sj v) v :=
          ((han v hv).differentiableAt.hasDerivAt).sub_const c
        have hEqF : (fun x => s x ^ (2 : ℕ)) =ᶠ[nhds v] (fun x => Sj x - c) := by
          filter_upwards [(isOpen_annulusSet ra rb).mem_nhds hv] with z hz
          exact hs_sq' z hz
        have h7 : HasDerivAt (fun x => Sj x - c) (2 * s v * deriv s v) v :=
          hLd.congr_of_eventuallyEq hEqF.symm
        have hEqD : deriv Sj v = 2 * s v * deriv s v := hRd.unique h7
        intro h0
        rw [h0, mul_zero] at hEqD
        exact hdne v hv hEqD
      · -- iterate identity
        intro v hv
        have hfe : quadratic c (s v) = Sj v := by
          unfold quadratic
          rw [hs_sq' v hv]
          ring
        rw [Function.iterate_succ_apply, hfe]
        exact hit v hv

end Bottcher
