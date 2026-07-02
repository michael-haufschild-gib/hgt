/-
# The Böttcher tower data: matched lobes

The loop of the tower data must traverse a FULL circle, so it lives on lobe sections defined on
honest annuli `(ra, rb)` below the critical-value level — the `m = 0` outside-certificate roots of
`SubCriticalChain`, here rebuilt with their signs matched to the one-slit scaffold chain
(`SLⱼ = σⱼ` on the common arc), which is what chains the lobe pieces into the connected `Ext`.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.BottcherScaffoldChain
import GaloisForLFunctions.Bottcher.SubCriticalChain

open Complex Set Filter Metric Topology

namespace Bottcher

/-- Arc annuli are monotone in the outer radius. -/
theorem arcAnnulus_mono_radius {ra rb RW α β : ℝ} (hpos : 0 < rb) (hle : rb ≤ RW) :
    arcAnnulus ra rb α β ⊆ arcAnnulus ra RW α β := by
  rintro z ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩
  exact ⟨ξ, ⟨h1, lt_of_lt_of_le h2 (Real.log_le_log hpos hle), h3, h4⟩, rfl⟩

/-- **The σ-matched lobe chain.**  Full-annulus inverse-branch sections at every depth on the
band `(ra, rb)` below the critical-value level, agreeing with the scaffold chain on the common
arc. -/
theorem exists_matched_lobes {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo)
    {ra rb RW α β : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbRW : rb < RW) (hRWR : RW < R₀)
    (hrb2h : Real.log rb < 2 * greenFunctionDyn c 0)
    (hαβ : α < β)
    {σ : ℕ → ℂ → ℂ}
    (hσ0 : σ 0 = S.T)
    (hσ : ∀ j, ScaffoldProps c S.T (arcAnnulus ra RW α β) j (σ j))
    (hσsq : ∀ j, ∀ v ∈ arcAnnulus ra RW α β, σ (j+1) v ^ 2 = σ j v - c) :
    ∃ SL : ℕ → ℂ → ℂ,
      SL 0 = S.T ∧
      (∀ j, ScaffoldProps c S.T (annulusSet ra rb) j (SL j)) ∧
      (∀ j, ∀ v ∈ annulusSet ra rb, SL (j+1) v ^ 2 = SL j v - c) ∧
      (∀ j, ∀ v ∈ arcAnnulus ra rb α β, SL j v = σ j v) := by
  classical
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hrapos : (0:ℝ) < ra := by linarith
  have hra1 : (1:ℝ) < ra := by linarith
  have hrbpos : (0:ℝ) < rb := by linarith
  have hlogra : (0:ℝ) < Real.log ra := Real.log_pos hra1
  set B : Set ℂ := annulusSet ra rb with hBdef
  set C : Set ℂ := arcAnnulus ra rb α β with hCdef
  have hCB : C ⊆ B := arcAnnulus_subset _ _ hrapos hrb
  have hCA : C ⊆ arcAnnulus ra RW α β := arcAnnulus_mono_radius hrbpos (le_of_lt hrbRW)
  have hCconn : IsConnected C := isConnected_arcAnnulus hrapos hrb hαβ
  have hCopen : IsOpen C := isOpen_arcAnnulus _ _ _ _
  have hBsub : ∀ v : ℂ, v ∈ B → v ∈ annulusSet rlo R₀ := by
    rintro v ⟨h1, h2⟩
    exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  have hlogv : ∀ v : ℂ, v ∈ B → 0 < Real.log ‖v‖ ∧ Real.log ‖v‖ < Real.log rb := by
    rintro v ⟨h1, h2⟩
    exact ⟨Real.log_pos (lt_trans hra1 h1), Real.log_lt_log (lt_trans hrapos h1) h2⟩
  -- radicand nonvanishing on the band at every depth (levels below 2h)
  have hrad_ne : ∀ j : ℕ, ∀ SLj : ℂ → ℂ,
      (∀ v ∈ B, greenFunctionDyn c (SLj v) = Real.log ‖v‖ / 2 ^ j) →
      ∀ v ∈ B, SLj v - c ≠ 0 := by
    intro j SLj hlev v hv hcon
    have hveq : SLj v = c := sub_eq_zero.mp hcon
    have h1 := hlev v hv
    rw [hveq, greenFunctionDyn_critical_value c] at h1
    have h2 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 := (hlogv v hv).1
    have h4 := (hlogv v hv).2
    have h5 : Real.log ‖v‖ / 2 ^ j ≤ Real.log ‖v‖ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- the σ-side radicand is nonvanishing on the common arc
  have hσrad_ne : ∀ j : ℕ, ∀ v ∈ C, σ j v - c ≠ 0 := by
    intro j v hv hcon
    have hveq : σ j v = c := sub_eq_zero.mp hcon
    have h1 := (hσ j).2.1 v (hCA hv)
    rw [hveq, greenFunctionDyn_critical_value c] at h1
    have h2 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 := (hlogv v (hCB hv)).1
    have h4 := (hlogv v (hCB hv)).2
    have h5 : Real.log ‖v‖ / 2 ^ j ≤ Real.log ‖v‖ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- one lobe step: root on the band, sign-matched to σ (j+1) on C
  have hstep : ∀ j : ℕ, ∀ SLj : ℂ → ℂ,
      ScaffoldProps c S.T B j SLj → (∀ v ∈ C, SLj v = σ j v) →
      ∃ SLj1 : ℂ → ℂ, ScaffoldProps c S.T B (j+1) SLj1 ∧
        (∀ v ∈ B, SLj1 v ^ 2 = SLj v - c) ∧
        (∀ v ∈ C, SLj1 v = σ (j+1) v) := by
    intro j SLj hP hmatch
    obtain ⟨han, hlev, hinj, hdne, hit⟩ := hP
    have hg_ne := hrad_ne j SLj hlev
    have hg_an : AnalyticOnNhd ℂ (fun v => SLj v - c) B := fun v hv =>
      (han v hv).sub analyticAt_const
    -- outside winding certificate at the core radius
    set ρ : ℝ := (ra + rb) / 2 with hρdef
    have hρ1 : ra < ρ := by rw [hρdef]; linarith
    have hρ2 : ρ < rb := by rw [hρdef]; linarith
    have hρpos : (0:ℝ) < ρ := by linarith
    have hcm : ∀ θ : ℝ, circleMap 0 ρ θ ∈ B :=
      circleMap_mem_annulusSet hρpos hρ1 hρ2
    set ℓj : C1Loop := sectionLoop han hcm with hℓdef
    have hwind0 : windInt ℓj c = 0 := by
      apply windInt_eq_zero_of_level_lt c ℓj
        (show (0:ℝ) < Real.log rb from Real.log_pos (by linarith))
      · intro θ
        show greenFunctionDyn c (SLj (circleMap 0 ρ θ)) ≤ Real.log rb
        rw [hlev _ (hcm θ)]
        have h1 := (hlogv _ (hcm θ)).2
        have h2 := (hlogv _ (hcm θ)).1
        have h3 : Real.log ‖circleMap 0 ρ θ‖ / 2 ^ j ≤ Real.log ‖circleMap 0 ρ θ‖ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
        linarith
      · rw [greenFunctionDyn_critical_value c]
        exact hrb2h
    have hgwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun v => SLj v - c) (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
        = ((2 ^ 1 * 0 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have hcongr : ∀ θ : ℝ,
          logDeriv (fun v => SLj v - c) (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
          = (ℓj.γ θ - c)⁻¹ * ℓj.γ' θ := by
        intro θ
        have h1 : logDeriv (fun v => SLj v - c) (circleMap 0 ρ θ)
            = deriv SLj (circleMap 0 ρ θ) / (SLj (circleMap 0 ρ θ) - c) := by
          rw [logDeriv_apply]
          congr 1
          exact deriv_sub_const c
        rw [h1]
        show deriv SLj (circleMap 0 ρ θ) / (SLj (circleMap 0 ρ θ) - c)
            * (circleMap 0 ρ θ * Complex.I)
          = (SLj (circleMap 0 ρ θ) - c)⁻¹
            * (deriv SLj (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
      show windInt ℓj c = _
      rw [hwind0]
      push_cast
      ring
    obtain ⟨s, hs_an, hs_sq, hs_ne⟩ :=
      exists_pow_root_on_annulus hrapos hρ1 hρ2 hg_an hg_ne 1 0 hgwind
    have hs_sq' : ∀ v ∈ B, s v ^ 2 = SLj v - c := by
      intro v hv
      have := hs_sq v hv
      rwa [pow_one 2] at this
    -- the full ScaffoldProps package for the root
    have hProps : ∀ t : ℂ → ℂ, (∀ v ∈ B, t v ^ 2 = SLj v - c) →
        AnalyticOnNhd ℂ t B → ScaffoldProps c S.T B (j+1) t := by
      intro t ht_sq ht_an
      have ht_ne : ∀ v ∈ B, t v ≠ 0 := by
        intro v hv h0
        have h1 := ht_sq v hv
        rw [h0, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
        exact hg_ne v hv h1.symm
      refine ⟨ht_an, ?_, ?_, ?_, ?_⟩
      · intro v hv
        have hfe : quadratic c (t v) = SLj v := by
          unfold quadratic
          rw [ht_sq v hv]
          ring
        have h1 := greenFunctionDyn_quadratic c (t v)
        rw [hfe, hlev v hv] at h1
        rw [pow_succ]
        field_simp at h1 ⊢
        linarith
      · intro v₁ h₁ v₂ h₂ heq
        have h3 : SLj v₁ = SLj v₂ := by
          have e1 := ht_sq v₁ h₁
          have e2 := ht_sq v₂ h₂
          have h4 : SLj v₁ - c = SLj v₂ - c := by rw [← e1, ← e2, heq]
          linear_combination h4
        exact hinj h₁ h₂ h3
      · intro v hv
        have ht_d : HasDerivAt t (deriv t v) v := (ht_an v hv).differentiableAt.hasDerivAt
        have hLd : HasDerivAt (fun x => t x ^ 2) (2 * t v * deriv t v) v := by
          have h4 := ht_d.pow 2
          have h5 : (2:ℕ) * t v ^ (2 - 1) * deriv t v = 2 * t v * deriv t v := by
            push_cast
            ring
          rwa [h5] at h4
        have hRd : HasDerivAt (fun x => SLj x - c) (deriv SLj v) v :=
          ((han v hv).differentiableAt.hasDerivAt).sub_const c
        have hEqF : (fun x => t x ^ 2) =ᶠ[nhds v] (fun x => SLj x - c) := by
          filter_upwards [(isOpen_annulusSet ra rb).mem_nhds hv] with z hz
          exact ht_sq z hz
        have h7 : HasDerivAt (fun x => SLj x - c) (2 * t v * deriv t v) v :=
          hLd.congr_of_eventuallyEq hEqF.symm
        have hEqD : deriv SLj v = 2 * t v * deriv t v := hRd.unique h7
        intro h0
        rw [h0, mul_zero] at hEqD
        exact hdne v hv hEqD
      · intro v hv
        have hfe : quadratic c (t v) = SLj v := by
          unfold quadratic
          rw [ht_sq v hv]
          ring
        rw [Function.iterate_succ_apply, hfe]
        exact hit v hv
    -- the sign against σ (j+1) on C
    have hdich : ∀ v ∈ C, s v = σ (j+1) v ∨ s v = -σ (j+1) v := by
      intro v hv
      have h1 : s v ^ 2 = SLj v - c := hs_sq' v (hCB hv)
      have h2 : σ (j+1) v ^ 2 = σ j v - c := hσsq j v (hCA hv)
      have h3 : SLj v = σ j v := hmatch v hv
      have h4 : s v ^ 2 = σ (j+1) v ^ 2 := by rw [h1, h3, ← h2]
      have h5 : (s v - σ (j+1) v) * (s v + σ (j+1) v) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact Or.inl (sub_eq_zero.mp h6)
      · exact Or.inr (by linear_combination h6)
    have hσne : ∀ v ∈ C, σ (j+1) v ≠ 0 := by
      intro v hv hcon
      have h1 := hσsq j v (hCA hv)
      rw [hcon, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h1
      exact hσrad_ne j v hv h1.symm
    have hsign := sign_constant_on_connected hCopen hCconn
      (u := s) (v := σ (j+1))
      (fun v hv => (hs_an v (hCB hv)).continuousAt)
      (fun v hv => ((hσ (j+1)).1 v (hCA hv)).continuousAt)
      hσne hdich
    rcases hsign with hpos | hneg
    · exact ⟨s, hProps s hs_sq' hs_an, hs_sq', hpos⟩
    · refine ⟨fun v => -s v, hProps _ ?_ hs_an.neg, ?_, ?_⟩
      · intro v hv
        have := hs_sq' v hv
        show (-s v) ^ 2 = SLj v - c
        rw [neg_pow]
        simpa using this
      · intro v hv
        have := hs_sq' v hv
        show (-s v) ^ 2 = SLj v - c
        rw [neg_pow]
        simpa using this
      · intro v hv
        show -s v = σ (j+1) v
        rw [hneg v hv]
        ring
  -- assemble the chain
  have hbase : ScaffoldProps c S.T B 0 S.T ∧ (∀ v ∈ C, S.T v = σ 0 v) := by
    constructor
    · refine ⟨S.an.mono hBsub, ?_, S.inj.mono hBsub, fun v hv => S.dne v (hBsub v hv), ?_⟩
      · intro v hv
        rw [S.level v (hBsub v hv)]
        simp
      · intro v hv
        simp
    · intro v hv
      rw [hσ0]
  choose! nextfn hnextfn using hstep
  set SL : ℕ → ℂ → ℂ := fun n =>
    Nat.rec S.T (fun j prev => nextfn j prev) n with hSLdef
  have hSLprops : ∀ j : ℕ, ScaffoldProps c S.T B j (SL j) ∧ (∀ v ∈ C, SL j v = σ j v) := by
    intro j
    induction j with
    | zero => exact hbase
    | succ n ih =>
        obtain ⟨hP, hmatch⟩ := ih
        obtain ⟨hP', hsq', hmatch'⟩ := hnextfn n (SL n) hP hmatch
        exact ⟨hP', hmatch'⟩
  have hSLsq : ∀ j : ℕ, ∀ v ∈ B, SL (j+1) v ^ 2 = SL j v - c := by
    intro j
    obtain ⟨hP, hmatch⟩ := hSLprops j
    obtain ⟨_, hsq', _⟩ := hnextfn j (SL j) hP hmatch
    exact hsq'
  exact ⟨SL, rfl, fun j => (hSLprops j).1, hSLsq, fun j => (hSLprops j).2⟩

end Bottcher

namespace Bottcher

/-- **The extended domain and deep lobe at depth `k`.**  One connected open `Ext` containing the
tower image, on which every point reaches the tower image within `k` iterates, together with the
depth-`k` lobe section whose circle images provide the loops. -/
theorem exists_tower_ext {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (hh0 : 0 < greenFunctionDyn c 0)
    (hlow : greenFunctionDyn c 0 < Real.log rlo)
    {ra rb RW : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbRW : rb < RW) (hRWR : RW < R₀)
    (hrb2h : Real.log rb < 2 * greenFunctionDyn c 0)
    (hraRW : ra ^ 2 < RW)
    (hRW4h : Real.log RW < 4 * greenFunctionDyn c 0)
    (k : ℕ) :
    ∃ (Ext : Set ℂ) (SL : ℂ → ℂ),
      IsOpen Ext ∧ IsConnected Ext ∧
      S.T '' annulusSet rlo R₀ ⊆ Ext ∧
      (∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) ∧
      AnalyticOnNhd ℂ SL (annulusSet ra rb) ∧
      (∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SL v) = S.T v) ∧
      (∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k) ∧
      (∀ v ∈ annulusSet ra rb, deriv SL v ≠ 0) ∧
      (∀ v ∈ annulusSet ra rb, SL v ∈ Ext) := by
  classical
  obtain ⟨α, β, J₁, J₂, hαβ, hβα, hαJ₁, hJ₁J₂, hJ₂β, hJ₁dbl, hJ₂dbl, σ, hσ0, hσP, hσsq, hσdbl⟩ :=
    exists_scaffold_chain S hrlo hra hraRW hRWR hRW4h hh0 hlow
  obtain ⟨SL, hSL0, hSLP, hSLsq, hSLmatch⟩ :=
    exists_matched_lobes S hrlo hra hrb hrbRW hRWR hrb2h hαβ hσ0 hσP hσsq
  have hrapos : (0:ℝ) < ra := by linarith
  have hrlopos : (0:ℝ) < rlo := by linarith
  have hraRW' : ra < RW := lt_trans hrb hrbRW
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  set B : Set ℂ := annulusSet ra rb with hBdef
  set P0 : Set ℂ := S.T '' annulusSet rlo R₀ with hP0def
  set Pσ : ℕ → Set ℂ := fun j => σ j '' A with hPσdef
  set PL : ℕ → Set ℂ := fun j => SL j '' B with hPLdef
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hBopen : IsOpen B := isOpen_annulusSet _ _
  have hAconn : IsConnected A := isConnected_arcAnnulus hrapos hraRW' hαβ
  have hBconn : IsConnected B := isConnected_annulus hrapos hrb
  have hP0open : IsOpen P0 :=
    isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) S.an S.dne
  have hP0conn : IsConnected P0 :=
    (isConnected_annulus hrlopos (by nlinarith [sq_nonneg rlo] :
      rlo < R₀)).image _ (S.an.continuousOn)
  have hPσopen : ∀ j, IsOpen (Pσ j) := fun j =>
    isOpen_image_of_analytic_dne hAopen (hσP j).1 (hσP j).2.2.2.1
  have hPσconn : ∀ j, IsConnected (Pσ j) := fun j =>
    hAconn.image _ ((hσP j).1.continuousOn)
  have hPLopen : ∀ j, IsOpen (PL j) := fun j =>
    isOpen_image_of_analytic_dne hBopen (hSLP j).1 (hSLP j).2.2.2.1
  have hPLconn : ∀ j, IsConnected (PL j) := fun j =>
    hBconn.image _ ((hSLP j).1.continuousOn)
  -- the doubling window is nonempty
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
  -- pairwise overlaps
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
  have hoverL : ∀ j : ℕ, (PL j ∩ Pσ j).Nonempty := by
    intro j
    obtain ⟨v, hv⟩ := hCne
    refine ⟨SL j v, ⟨v, hCsubB hv, rfl⟩, ?_⟩
    rw [hSLmatch j v hv]
    exact ⟨v, hCsubA hv, rfl⟩
  have hPσ0sub : Pσ 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hσ0]
    exact ⟨v, hAsubS v hv, rfl⟩
  have hPL0sub : PL 0 ⊆ P0 := by
    rintro z ⟨v, hv, rfl⟩
    rw [hSL0]
    refine ⟨v, ?_, rfl⟩
    obtain ⟨h1, h2⟩ := hv
    exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  -- the growing union, defined recursively so the recurrence is definitional
  set Conn : ℕ → Set ℂ := fun n =>
    Nat.rec P0 (fun j prev => prev ∪ (Pσ (j+1) ∪ PL (j+1))) n with hConndef
  have hConnsucc : ∀ n : ℕ, Conn (n+1) = Conn n ∪ (Pσ (n+1) ∪ PL (n+1)) := fun n => rfl
  have hP0Conn : ∀ n : ℕ, P0 ⊆ Conn n := by
    intro n
    induction n with
    | zero => exact fun z hz => hz
    | succ n ih =>
        rw [hConnsucc n]
        exact fun z hz => Or.inl (ih hz)
  have hPσConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → Pσ j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact hPσ0sub
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inl hz)
  have hPLConn : ∀ n : ℕ, ∀ j : ℕ, j ≤ n → PL j ⊆ Conn n := by
    intro n
    induction n with
    | zero =>
        intro j hj
        interval_cases j
        exact fun z hz => hPL0sub hz
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n+1) with hlt | hge
        · rw [hConnsucc n]
          exact fun z hz => Or.inl (ih j (by omega) hz)
        · have hj' : j = n + 1 := by omega
          subst hj'
          rw [hConnsucc n]
          exact fun z hz => Or.inr (Or.inr hz)
  have hConnConn : ∀ n : ℕ, IsConnected (Conn n) ∧ IsOpen (Conn n) := by
    intro n
    induction n with
    | zero => exact ⟨hP0conn, hP0open⟩
    | succ n ih =>
        obtain ⟨ihc, iho⟩ := ih
        rw [hConnsucc n]
        have hover : ∃ z, z ∈ Conn n ∧ z ∈ Pσ (n+1) := by
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · subst hn0
            obtain ⟨z, hz1, hz2⟩ := hover0
            exact ⟨z, hP0Conn 0 hz1, hz2⟩
          · obtain ⟨z, hz1, hz2⟩ := hoverσ n
            exact ⟨z, hPσConn n n le_rfl hz1, hz2⟩
        have h2 : IsConnected (Pσ (n+1) ∪ PL (n+1)) := by
          obtain ⟨z, hz1, hz2⟩ := hoverL (n+1)
          exact IsConnected.union ⟨z, hz2, hz1⟩ (hPσconn (n+1)) (hPLconn (n+1))
        obtain ⟨z, hz1, hz2⟩ := hover
        refine ⟨IsConnected.union ⟨z, hz1, Or.inl hz2⟩ ihc h2, ?_⟩
        exact iho.union ((hPσopen (n+1)).union (hPLopen (n+1)))
  have hreach : ∀ n : ℕ, ∀ z ∈ Conn n, ∃ j : ℕ, j ≤ n ∧
      (quadratic c)^[j] z ∈ P0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        exact ⟨0, le_rfl, by simpa using hz⟩
    | succ n ih =>
        intro z hz
        rw [hConnsucc n] at hz
        rcases hz with hz | hz
        · obtain ⟨j, hj, hzj⟩ := ih z hz
          exact ⟨j, by omega, hzj⟩
        · rcases hz with hzσ | hzL
          · obtain ⟨v, hv, rfl⟩ := hzσ
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hσP (n+1)).2.2.2.2 v hv]
            exact ⟨v, hAsubS v hv, rfl⟩
          · obtain ⟨v, hv, rfl⟩ := hzL
            refine ⟨n+1, le_rfl, ?_⟩
            rw [(hSLP (n+1)).2.2.2.2 v hv]
            refine ⟨v, ?_, rfl⟩
            obtain ⟨h1, h2⟩ := hv
            exact ⟨lt_trans hra h1, lt_trans h2 (lt_trans hrbRW hRWR)⟩
  refine ⟨Conn k, SL k, (hConnConn k).2, (hConnConn k).1, hP0Conn k, hreach k,
    (hSLP k).1, (hSLP k).2.2.2.2, (hSLP k).2.1, (hSLP k).2.2.2.1, ?_⟩
  intro v hv
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact hPL0sub ⟨v, hv, rfl⟩
  · exact hPLConn k k le_rfl ⟨v, hv, rfl⟩

end Bottcher

namespace Bottcher

/-- **The inverse collapse**: on the tower image, `S.inv` intertwines `f` with squaring. -/
theorem TowerSection.inv_map_quadratic {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    (hrlo : 0 < rlo)
    {y : ℂ} (hy : y ∈ S.T '' annulusSet rlo rhi)
    (hfy : quadratic c y ∈ S.T '' annulusSet rlo rhi) :
    S.inv (quadratic c y) = (S.inv y) ^ 2 := by
  obtain ⟨w, hw, rfl⟩ := hy
  rw [S.inv_left hw]
  obtain ⟨w', hw', hw'eq⟩ := hfy
  have hlev : greenFunctionDyn c (quadratic c (S.T w)) = 2 * Real.log ‖w‖ := by
    rw [greenFunctionDyn_quadratic, S.level w hw]
  have hlev' : Real.log ‖w'‖ = 2 * Real.log ‖w‖ := by
    rw [← S.level w' hw', hw'eq, hlev]
  have hnorm : ‖w ^ 2‖ = ‖w'‖ := by
    rw [norm_pow]
    have h1 : Real.log (‖w‖ ^ 2) = Real.log ‖w'‖ := by
      rw [Real.log_pow, hlev']
      push_cast
      ring
    have h2 : (0:ℝ) < ‖w‖ ^ 2 := by
      have := lt_trans hrlo hw.1
      positivity
    have h3 : (0:ℝ) < ‖w'‖ := lt_trans hrlo hw'.1
    calc ‖w‖ ^ 2 = Real.exp (Real.log (‖w‖ ^ 2)) := (Real.exp_log h2).symm
      _ = Real.exp (Real.log ‖w'‖) := by rw [h1]
      _ = ‖w'‖ := Real.exp_log h3
  have hsqmem : w ^ 2 ∈ annulusSet rlo rhi := by
    rw [annulusSet, mem_setOf_eq, hnorm]
    exact hw'
  have hfe : quadratic c (S.T w) = S.T (w ^ 2) := by
    unfold quadratic
    rw [S.fe w hw hsqmem]
  rw [hfe, S.inv_left hsqmem]

/-- **Iterated coherence**: if both the `i`-th and `j`-th iterates land on the tower image,
the inverse of the deeper iterate is the dyadic power of the shallower one. -/
theorem TowerSection.inv_iterate_coherence {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    (hrlo : 1 < rlo)
    {z : ℂ} {i j : ℕ} (hij : i ≤ j)
    (hi : (quadratic c)^[i] z ∈ S.T '' annulusSet rlo rhi)
    (hj : (quadratic c)^[j] z ∈ S.T '' annulusSet rlo rhi) :
    S.inv ((quadratic c)^[j] z) = (S.inv ((quadratic c)^[i] z)) ^ (2 ^ (j - i)) := by
  have hrlopos : (0:ℝ) < rlo := by linarith
  set w : ℂ := S.inv ((quadratic c)^[i] z) with hwdef
  have hwmem : w ∈ annulusSet rlo rhi := S.inv_mem hi
  have hTw : S.T w = (quadratic c)^[i] z := S.inv_right hi
  set m : ℕ := j - i with hmdef
  -- level bookkeeping: powers of w stay in the annulus up to m
  have hlogw : 0 < Real.log ‖w‖ := Real.log_pos (lt_trans hrlo hwmem.1)
  have hlevj : greenFunctionDyn c ((quadratic c)^[j] z) = 2 ^ m * Real.log ‖w‖ := by
    have h1 : (quadratic c)^[j] z = (quadratic c)^[m] ((quadratic c)^[i] z) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h1, ← hTw, greenFunctionDyn_iterate, S.level w hwmem]
  obtain ⟨wj, hwj, hwjeq⟩ := hj
  have hlogwj : Real.log ‖wj‖ = 2 ^ m * Real.log ‖w‖ := by
    rw [← S.level wj hwj, hwjeq, hlevj]
  have hpow : ∀ l : ℕ, l ≤ m → w ^ (2 ^ l) ∈ annulusSet rlo rhi := by
    intro l hl
    have h1 : ‖w ^ (2 ^ l)‖ = ‖w‖ ^ (2 ^ l) := norm_pow _ _
    constructor
    · rw [h1]
      have hw1 : (1:ℝ) ≤ ‖w‖ := le_of_lt (lt_trans hrlo hwmem.1)
      calc rlo < ‖w‖ := hwmem.1
        _ ≤ ‖w‖ ^ (2 ^ l) := le_self_pow₀ hw1 (by positivity)
    · rw [h1]
      have h2 : Real.log (‖w‖ ^ (2 ^ l)) ≤ Real.log ‖wj‖ := by
        rw [Real.log_pow, hlogwj]
        have h3 : (2:ℝ) ^ l ≤ 2 ^ m := by
          apply pow_le_pow_right₀ (by norm_num) hl
        push_cast
        nlinarith
      have h4 : (0:ℝ) < ‖w‖ ^ (2 ^ l) := by
        have := lt_trans hrlopos hwmem.1
        positivity
      have h5 : ‖w‖ ^ (2 ^ l) ≤ ‖wj‖ := by
        calc ‖w‖ ^ (2 ^ l) = Real.exp (Real.log (‖w‖ ^ (2 ^ l))) := (Real.exp_log h4).symm
          _ ≤ Real.exp (Real.log ‖wj‖) := Real.exp_le_exp.mpr h2
          _ = ‖wj‖ := Real.exp_log (lt_trans hrlopos hwj.1)
      exact lt_of_le_of_lt h5 hwj.2
  have hfe := S.iterate_fe m hpow
  have h1 : (quadratic c)^[j] z = S.T (w ^ (2 ^ m)) := by
    have h2 : (quadratic c)^[j] z = (quadratic c)^[m] ((quadratic c)^[i] z) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h2, ← hTw, hfe]
  rw [h1, S.inv_left (hpow m le_rfl)]

end Bottcher

namespace Bottcher

open Classical in
/-- **The global radicand.**  On a domain with the `k`-step reach-back property, the coherent
family `F_j = (S.inv ∘ f^[j])^(2^(k−j))` glues to a single analytic nonvanishing `F` that equals
`(S.inv)^(2^k)` on the tower image and collapses along depth-`k` sections. -/
theorem exists_tower_radicand {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (k : ℕ) {Ext : Set ℂ} (hExto : IsOpen Ext)
    (hreach : ∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
      (∀ z ∈ S.T '' annulusSet rlo R₀, F z = (S.inv z) ^ (2 ^ k)) ∧
      (∀ z ∈ Ext, ∀ j : ℕ, j ≤ k → (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀ →
        F z = (S.inv ((quadratic c)^[j] z)) ^ (2 ^ (k - j))) := by
  classical
  set P0 : Set ℂ := S.T '' annulusSet rlo R₀ with hP0def
  have hP0open : IsOpen P0 :=
    isOpen_image_of_analytic_dne (isOpen_annulusSet _ _) S.an S.dne
  set good : ℂ → Prop := fun z => ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ P0 with hgooddef
  set F : ℂ → ℂ := fun z =>
    if hz : good z then (S.inv ((quadratic c)^[Nat.find hz] z)) ^ (2 ^ (k - Nat.find hz))
    else 1 with hFdef
  -- iterates are analytic everywhere
  have hquad_an : ∀ j : ℕ, ∀ z : ℂ, AnalyticAt ℂ ((quadratic c)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simpa using analyticAt_id
    | succ n ih =>
        intro z
        have h1 : (quadratic c)^[n+1] = (quadratic c)^[n] ∘ quadratic c := by
          rw [Function.iterate_succ]
        rw [h1]
        have h2 : AnalyticAt ℂ (quadratic c) z := by
          unfold quadratic
          exact (analyticAt_id.pow 2).add analyticAt_const
        exact (ih (quadratic c z)).comp h2
  -- the fixed-depth branch is analytic wherever its iterate lands in P0
  have hbranch_an : ∀ j : ℕ, ∀ z : ℂ, (quadratic c)^[j] z ∈ P0 →
      AnalyticAt ℂ (fun x => (S.inv ((quadratic c)^[j] x)) ^ (2 ^ (k - j))) z := by
    intro j z hz
    have h1 : AnalyticAt ℂ S.inv ((quadratic c)^[j] z) := S.inv_analytic _ hz
    exact ((h1.comp (hquad_an j z)).pow _)
  -- the coherent value identity: F agrees with any valid branch
  have hFval : ∀ z : ℂ, ∀ j : ℕ, j ≤ k → (quadratic c)^[j] z ∈ P0 →
      F z = (S.inv ((quadratic c)^[j] z)) ^ (2 ^ (k - j)) := by
    intro z j hjk hjP
    have hgz : good z := ⟨j, hjk, hjP⟩
    have hFz : F z = (S.inv ((quadratic c)^[Nat.find hgz] z)) ^ (2 ^ (k - Nat.find hgz)) := by
      rw [hFdef]
      simp only [hgz, dif_pos]
    obtain ⟨hle, hfindP⟩ := Nat.find_spec hgz
    set i : ℕ := Nat.find hgz with hidef
    have hij : i ≤ j := Nat.find_le ⟨hjk, hjP⟩
    have hcoh := S.inv_iterate_coherence hrlo hij hfindP hjP
    rw [hFz, hcoh, ← pow_mul]
    congr 1
    have h2 : 2 ^ (j - i) * 2 ^ (k - j) = 2 ^ (k - i) := by
      rw [← pow_add]
      congr 1
      omega
    exact h2.symm
  refine ⟨F, ?_, ?_, ?_, fun z _ => hFval z⟩
  · -- analyticity: near any point, F agrees with the branch at the point's own witness depth
    intro z hz
    obtain ⟨j, hjk, hjP⟩ := hreach z hz
    have hev : F =ᶠ[nhds z] (fun x => (S.inv ((quadratic c)^[j] x)) ^ (2 ^ (k - j))) := by
      have hcont : ContinuousAt ((quadratic c)^[j]) z := (hquad_an j z).continuousAt
      filter_upwards [hcont.preimage_mem_nhds (hP0open.mem_nhds hjP)] with x hx
      exact hFval x j hjk hx
    exact ((hbranch_an j z hjP).congr hev.symm)
  · -- nonvanishing: the inverse takes values in the annulus, norms above rlo > 1
    intro z hz
    obtain ⟨j, hjk, hjP⟩ := hreach z hz
    rw [hFval z j hjk hjP]
    apply pow_ne_zero
    intro h0
    have h1 := S.inv_mem hjP
    rw [h0] at h1
    simp only [annulusSet, mem_setOf_eq, norm_zero] at h1
    linarith [h1.1]
  · -- the tower-image identity (depth 0)
    intro z hzP
    have h1 := hFval z 0 (Nat.zero_le k) (by simpa using hzP)
    simpa using h1

end Bottcher

namespace Bottcher

/-- **The odd loop.**  A depth-`k` lobe circle, at a radius dodging any countable set through the
level fibration; the radicand collapses along it to the identity chart, so its `dlog`-period is
exactly `2πi`. -/
theorem exists_tower_loop {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hrlo : 1 < rlo) (k : ℕ)
    {ra rb : ℝ} (hra : rlo < ra) (hrb : ra < rb) (hrbR : rb < R₀)
    {SL : ℂ → ℂ} (hSLan : AnalyticOnNhd ℂ SL (annulusSet ra rb))
    (hSLit : ∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SL v) = S.T v)
    (hSLlev : ∀ v ∈ annulusSet ra rb, greenFunctionDyn c (SL v) = Real.log ‖v‖ / 2 ^ k)
    {Ext : Set ℂ} (hSLExt : ∀ v ∈ annulusSet ra rb, SL v ∈ Ext)
    {F : ℂ → ℂ} (hFan : AnalyticOnNhd ℂ F Ext)
    (hFbr : ∀ z ∈ Ext, ∀ j : ℕ, j ≤ k → (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀ →
      F z = (S.inv ((quadratic c)^[j] z)) ^ (2 ^ (k - j)))
    (T : Set ℂ) (hT : T.Countable) :
    ∃ (γ γ' : ℝ → ℂ),
      (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
      (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
      γ (2 * Real.pi) = γ 0 ∧
      (∀ θ : ℝ, γ θ ∉ T) ∧
      (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I * (2 * ((0:ℤ) : ℂ) + 1) := by
  classical
  have hrapos : (0:ℝ) < ra := by linarith
  -- dodge the countable set through the level fibration
  set badR : Set ℝ := (fun t => Real.exp (2 ^ k * greenFunctionDyn c t)) '' T with hbadRdef
  have hbadRc : badR.Countable := hT.image _
  obtain ⟨r, hrIoo, hrbad⟩ : ∃ r ∈ Set.Ioo ra rb, r ∉ badR := by
    by_contra hcon
    push_neg at hcon
    have h2 : (Set.Ioo ra rb).Countable := hbadRc.mono hcon
    have h3 := Cardinal.mk_le_aleph0_iff.mpr h2
    rw [Cardinal.mk_Ioo_real hrb] at h3
    exact absurd h3 (not_le.mpr Cardinal.aleph0_lt_continuum)
  obtain ⟨hr1, hr2⟩ := hrIoo
  have hrpos : (0:ℝ) < r := lt_trans hrapos hr1
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ annulusSet ra rb :=
    circleMap_mem_annulusSet hrpos hr1 hr2
  set ℓ : C1Loop := sectionLoop hSLan hcm with hℓdef
  -- the collapse F ∘ γ = circleMap
  have hcmS : ∀ θ : ℝ, circleMap 0 r θ ∈ annulusSet rlo R₀ := by
    intro θ
    obtain ⟨h1, h2⟩ := hcm θ
    exact ⟨lt_trans hra h1, lt_trans h2 hrbR⟩
  have hiter : ∀ θ : ℝ, (quadratic c)^[k] (SL (circleMap 0 r θ))
      ∈ S.T '' annulusSet rlo R₀ := by
    intro θ
    rw [hSLit _ (hcm θ)]
    exact ⟨circleMap 0 r θ, hcmS θ, rfl⟩
  have hcollapse : ∀ θ : ℝ, F (SL (circleMap 0 r θ)) = circleMap 0 r θ := by
    intro θ
    have h1 := hFbr (SL (circleMap 0 r θ)) (hSLExt _ (hcm θ)) k le_rfl (hiter θ)
    rw [h1, hSLit _ (hcm θ), S.inv_left (hcmS θ)]
    simp
  -- avoidance
  have havoid : ∀ θ : ℝ, SL (circleMap 0 r θ) ∉ T := by
    intro θ hmem
    apply hrbad
    refine ⟨SL (circleMap 0 r θ), hmem, ?_⟩
    show Real.exp (2 ^ k * greenFunctionDyn c (SL (circleMap 0 r θ))) = r
    rw [hSLlev _ (hcm θ)]
    have h1 : ‖circleMap 0 r θ‖ = r := by
      simp [circleMap, abs_of_pos hrpos]
    rw [h1]
    have h2 : (2:ℝ) ^ k * (Real.log r / 2 ^ k) = Real.log r := by
      field_simp
    rw [h2, Real.exp_log hrpos]
  -- the winding: the integrand is constantly I
  have hFγd : ∀ θ : ℝ, deriv F (ℓ.γ θ) * ℓ.γ' θ = circleMap 0 r θ * Complex.I := by
    intro θ
    have hFd : HasDerivAt F (deriv F (ℓ.γ θ)) (ℓ.γ θ) :=
      (hFan _ (hSLExt _ (hcm θ))).differentiableAt.hasDerivAt
    have hγd : HasDerivAt ℓ.γ (ℓ.γ' θ) θ := by
      have h1 : HasDerivAt SL (deriv SL (circleMap 0 r θ)) (circleMap 0 r θ) :=
        (hSLan _ (hcm θ)).differentiableAt.hasDerivAt
      have h2 := hasDerivAt_circleMap 0 r θ
      exact h1.comp θ h2
    have hcomp : HasDerivAt (fun t => F (ℓ.γ t)) (deriv F (ℓ.γ θ) * ℓ.γ' θ) θ :=
      hFd.comp θ hγd
    have hFγ : (fun t => F (ℓ.γ t)) = fun t => circleMap 0 r t := by
      funext t
      exact hcollapse t
    rw [hFγ] at hcomp
    have hcm_d : HasDerivAt (fun t => circleMap 0 r t) (circleMap 0 r θ * Complex.I) θ := by
      simpa using hasDerivAt_circleMap 0 r θ
    exact hcomp.unique hcm_d
  refine ⟨ℓ.γ, ℓ.γ', fun θ => hSLExt _ (hcm θ), ℓ.cont, ℓ.cont', ℓ.deriv, ℓ.closed,
    havoid, ?_⟩
  have hcongr : ∀ θ : ℝ, logDeriv F (ℓ.γ θ) * ℓ.γ' θ = Complex.I := by
    intro θ
    rw [logDeriv_apply]
    have h1 := hFγd θ
    have h2 : F (ℓ.γ θ) = circleMap 0 r θ := hcollapse θ
    have h3 : circleMap 0 r θ ≠ 0 := circleMap_ne_center (ne_of_gt hrpos)
    rw [h2, div_mul_eq_mul_div, h1, mul_comm (circleMap 0 r θ) Complex.I,
      mul_div_assoc, div_self h3, mul_one]
  rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  push_cast
  ring

end Bottcher
