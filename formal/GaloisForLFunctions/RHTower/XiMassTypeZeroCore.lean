import GaloisForLFunctions.RHTower.XiMassLogRetreatTail
import GaloisForLFunctions.RHTower.XiMassGradedConeSharpness
import GaloisForLFunctions.RHTower.XiMassPrefixQuadratureDefect

/-!
# Type-zero collapse of every asymptotically caustic boundary

A height family has vertical type zero when it is `O(e^{εu})` for every `ε > 0`.  Because the
exterior action `Γ_a(κ) = κ/2 − a√(κ²−1)` is continuous and vanishes at the balance slope, the
exterior true-prime tail past any moving boundary with `H(u)/u → κ_B` has type zero — with no
sign, monotonicity, or power-law assumption on the retreat.

Consequently the true-prime cone truncated at any such moving boundary has type zero exactly
when every mass-shifted Xi point has zero transverse displacement, i.e. exactly under the Riemann
hypothesis.  The exact core may therefore be shortened by every sublinear retreat from the
caustic, not only by the `u^{1/10}` and logarithmic layers.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Vertical type zero on the positive ray. -/
def XiMassTypeZero (A : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ u : ℝ in atTop, ‖A u‖ ≤ C * Real.exp (ε * u)

/-- The true-prime cone truncated at a moving height. -/
def xiMassMovingPrimeCone (a sigma : ℝ) (Hgt : ℝ → ℝ) (u : ℝ) : ℂ :=
  ∑ k ∈ conePrimeIndex ⌊Real.exp (Hgt u)⌋₊,
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)

theorem xiMassCriticalTruePrimeCone_eq_movingCone {a sigma kappa : ℝ} (hkappa : 1 < kappa)
    (u : ℝ) :
    xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      = xiMassMovingPrimeCone a sigma (fun v => kappa * v) u := by
  classical
  rw [xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassConeDepthOfSlope_height hkappa,
    xiMassMovingPrimeCone, conePrimeIndex]

/-! ## The exterior block at a moving height -/

theorem sum_norm_exteriorBlock_height_le {a sigma kappa0 u H : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa0 : 1 < kappa0) (hu : 0 < u) (hcone : kappa0 * u ≤ H) (N : ℕ) :
    ∑ k ∈ conePrimeIndex N \ conePrimeIndex ⌊Real.exp H⌋₊,
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)‖
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 / Real.sqrt u
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
  classical
  have hconv := sum_conePrimeIndex_sdiff_eq
    (M₀ := ⌊Real.exp H⌋₊) (M₁ := N)
    (g := fun p : ℕ => ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖)
  rw [hconv]
  have hsub : (Finset.Ioc ⌊Real.exp H⌋₊ N).filter (fun p => Nat.Prime p)
      ⊆ (Nat.primesBelow (N + 1)).filter (fun p : ℕ => Real.exp H < (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hgt, hle⟩, hprime⟩ := hp
    rw [Finset.mem_filter, Nat.mem_primesBelow]
    refine ⟨⟨by omega, hprime⟩, ?_⟩
    have h1 := Nat.lt_floor_add_one (Real.exp H)
    have h2 : ((⌊Real.exp H⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hgt
    linarith
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => norm_nonneg _) ?_
  exact sum_norm_exteriorTail_movingSlope_le ha hsigma hkappa0 hu hcone N

/-- **Two cutoff cones above a common exterior height differ by at most the exterior tail.** -/
theorem norm_conePrimeIndexSum_sub_le {a sigma kappa0 u H : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa0 : 1 < kappa0) (hu : 0 < u) (hcone : kappa0 * u ≤ H)
    {M N : ℕ} (hM : ⌊Real.exp H⌋₊ ≤ M) (hN : ⌊Real.exp H⌋₊ ≤ N) :
    ‖(∑ k ∈ conePrimeIndex M, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
        - ∑ k ∈ conePrimeIndex N, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)‖
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 / Real.sqrt u
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
  classical
  have hkey : ∀ P Q : ℕ, ⌊Real.exp H⌋₊ ≤ P → Q ≤ P → ⌊Real.exp H⌋₊ ≤ Q →
      ‖(∑ k ∈ conePrimeIndex P, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
          - ∑ k ∈ conePrimeIndex Q,
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)‖
        ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa0 / Real.sqrt u
          * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
    intro P Q hP hQP hQ
    have hsplit : (∑ k ∈ conePrimeIndex P \ conePrimeIndex Q,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
        + ∑ k ∈ conePrimeIndex Q, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)
        = ∑ k ∈ conePrimeIndex P,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2) :=
      Finset.sum_sdiff (conePrimeIndex_subset hQP)
    have hval : (∑ k ∈ conePrimeIndex P,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
        - ∑ k ∈ conePrimeIndex Q, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)
        = ∑ k ∈ conePrimeIndex P \ conePrimeIndex Q,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2) := by
      rw [← hsplit]
      ring
    rw [hval]
    refine (norm_sum_le _ _).trans ?_
    have hsubset : conePrimeIndex P \ conePrimeIndex Q
        ⊆ conePrimeIndex P \ conePrimeIndex ⌊Real.exp H⌋₊ := by
      intro k hk
      rw [Finset.mem_sdiff] at hk ⊢
      exact ⟨hk.1, fun hcon => hk.2 (conePrimeIndex_subset hQ hcon)⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      fun i _ _ => norm_nonneg _) ?_
    exact sum_norm_exteriorBlock_height_le ha hsigma hkappa0 hu hcone P
  rcases le_total N M with h | h
  · exact hkey M N hM h hN
  · have hstep := hkey N M hN h hM
    rw [← norm_neg] at hstep
    have hneg : -((∑ k ∈ conePrimeIndex N,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
        - ∑ k ∈ conePrimeIndex M, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
        = (∑ k ∈ conePrimeIndex M,
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
          - ∑ k ∈ conePrimeIndex N,
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2) := by ring
    rwa [hneg] at hstep

/-- The exterior action at a slope, written on the cone. -/
theorem xiMassAction_at_slope {a kappa u : ℝ} (hkappa : 1 < kappa) (hu : 0 ≤ u) :
    kappa * u / 2 - a * Real.sqrt ((kappa * u) ^ 2 - u ^ 2)
      = -(xiMassBesselConeExponent a kappa) * u := by
  have hk2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hfac : (kappa * u) ^ 2 - u ^ 2 = u ^ 2 * (kappa ^ 2 - 1) := by ring
  rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq hu, xiMassBesselConeExponent]
  ring

/-! ## The line-growth predicate is an eventual condition -/

theorem xiMassCriticalBesselConeLineGrowth_of_eventually {a sigma kappa lam : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hlam : 0 ≤ lam)
    (h : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖
        ≤ C * Real.exp (lam * u)) :
    XiMassCriticalBesselConeLineGrowth a sigma kappa lam := by
  classical
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hVnn := xiMassVerticalBound_nonneg sigma
  obtain ⟨C, hC⟩ := h
  obtain ⟨u₀, hu₀⟩ := (hC.and (eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
  have hu₀0 : (0 : ℝ) ≤ u₀ := (hu₀ u₀ le_rfl).2
  refine ⟨max C ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ)
      * (Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) * xiMassVerticalBound sigma)),
    fun u hu => ?_⟩
  have hexp1 : (1 : ℝ) ≤ Real.exp (lam * u) := Real.one_le_exp (mul_nonneg hlam hu)
  rcases le_or_gt u₀ u with hcase | hcase
  · have hbase := (hu₀ u hcase).1
    have hle : C ≤ max C ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ)
        * (Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) * xiMassVerticalBound sigma)) :=
      le_max_left _ _
    nlinarith [hbase, hle, hexp1]
  · rw [xiMassCriticalTruePrimeCone_eq_movingCone hkappa, xiMassMovingPrimeCone]
    have hmono : ⌊Real.exp (kappa * u)⌋₊ ≤ ⌊Real.exp (kappa * u₀)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith [hcase.le]))
    have hb := norm_conePrimeIndexSum_le (a := a) (sigma := sigma) ha hsigma u
      ⌊Real.exp (kappa * u)⌋₊
    have hm := conePrimeIndexSumBound_mono (sigma := sigma) hmono hVnn
    have hle : (⌊Real.exp (kappa * u₀)⌋₊ : ℝ)
        * (Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) * xiMassVerticalBound sigma)
        ≤ max C ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ)
          * (Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) * xiMassVerticalBound sigma)) :=
      le_max_right _ _
    have hnn : (0 : ℝ) ≤ (⌊Real.exp (kappa * u₀)⌋₊ : ℝ)
        * (Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) * xiMassVerticalBound sigma) := by
      have h1 : (0 : ℝ) ≤ (⌊Real.exp (kappa * u₀)⌋₊ : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ Real.log ((⌊Real.exp (kappa * u₀)⌋₊ : ℝ) + 1) :=
        Real.log_nonneg (by linarith)
      exact mul_nonneg h1 (mul_nonneg h2 hVnn)
    nlinarith [hb, hm, hle, hexp1, hnn]

/-! ## The exterior action is continuous and vanishes at the caustic -/

theorem continuous_xiMassBesselConeExponent (a : ℝ) :
    Continuous (fun kappa : ℝ => xiMassBesselConeExponent a kappa) := by
  simp only [xiMassBesselConeExponent]
  fun_prop

theorem xiMassBesselConeExponent_sharpSlope_eq_zero {a : ℝ} (ha : 1 / 2 < a) :
    xiMassBesselConeExponent a (xiMassSpacelikeSharpSlope a) = 0 := by
  have hval := xiMassBesselConeExponent_gradedConeSlope ha le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [xiMassGradedConeSlope_zero ha] at hval
  linarith

theorem xiMassGradedConeSlope_lt_sharpSlope {a lam : ℝ} (ha : 1 / 2 < a) (hlam : 0 < lam)
    (hlamhalf : lam < 1 / 2) :
    xiMassGradedConeSlope a lam < xiMassSpacelikeSharpSlope a := by
  by_contra hcon
  have hge : xiMassSpacelikeSharpSlope a ≤ xiMassGradedConeSlope a lam := not_lt.mp hcon
  have hkB : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hmono := xiMassBesselConeExponent_mono ha hkB hge
  have hzero := xiMassBesselConeExponent_sharpSlope_eq_zero ha
  have hval := xiMassBesselConeExponent_gradedConeSlope ha hlam.le hlamhalf.le
  linarith

/-! ## The type-zero criterion -/

set_option maxHeartbeats 1200000 in
/-- **(23.5) The type-zero criterion at every asymptotically caustic boundary.**  For every moving
height whose slope tends to the balance slope, the truncated true-prime cone has vertical type
zero exactly under the Riemann hypothesis.  No sign, monotonicity, or power-law assumption on the
retreat is used. -/
theorem riemannHypothesis_iff_typeZero_movingPrimeCone {a c sigma : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) {Hgt : ℝ → ℝ}
    (hratio : Tendsto (fun u : ℝ => Hgt u / u) atTop (nhds (xiMassSpacelikeSharpSlope a))) :
    RiemannHypothesis ↔ XiMassTypeZero (xiMassMovingPrimeCone a sigma Hgt) := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkB : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hkB0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := lt_trans zero_lt_one hkB
  have hzeroB := xiMassBesselConeExponent_sharpSlope_eq_zero ha
  have hev_slope : ∀ kap : ℝ, kap < xiMassSpacelikeSharpSlope a →
      ∀ᶠ u : ℝ in atTop, kap * u ≤ Hgt u := by
    intro kap hkap
    have h1 : ∀ᶠ u : ℝ in atTop, kap < Hgt u / u := hratio.eventually_const_lt hkap
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with u hu hupos
    rw [lt_div_iff₀ hupos] at hu
    linarith
  constructor
  · -- RH forces type zero
    intro hRH ε hε0
    obtain ⟨C, hC⟩ := (riemannHypothesis_iff_xiMassCriticalBesselConeLineBound hhalf hca hsigma
      hkB le_rfl).1 hRH
    have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0 le_rfl)
    obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
    have hk0one : 1 < k0 := by rw [← hk0def]; linarith
    have hk0lt : k0 < xiMassSpacelikeSharpSlope a := by rw [← hk0def]; linarith
    have hCT : 0 ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 := by
      rw [xiMassBesselExteriorSqrtTailConstant]
      have h1 : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma k0 :=
        xiMassBesselExteriorSqrtConstant_nonneg ha0 hk0one
      have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
        primeLogRpowTailConstant_nonneg (by linarith)
      have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
      exact mul_nonneg h1 (mul_nonneg h3.le h2)
    have hmin : Tendsto (fun u : ℝ => min (Hgt u / u) (xiMassSpacelikeSharpSlope a)) atTop
        (nhds (xiMassSpacelikeSharpSlope a)) := by
      have hstep := hratio.min (tendsto_const_nhds (x := xiMassSpacelikeSharpSlope a))
      simpa using hstep
    have hact : Tendsto
        (fun u : ℝ => -(xiMassBesselConeExponent a
          (min (Hgt u / u) (xiMassSpacelikeSharpSlope a)))) atTop (nhds 0) := by
      have hcont : Continuous
          (fun k : ℝ => -(xiMassBesselConeExponent a k)) :=
        (continuous_xiMassBesselConeExponent a).neg
      have hstep := (hcont.tendsto (xiMassSpacelikeSharpSlope a)).comp hmin
      rw [hzeroB, neg_zero] at hstep
      exact hstep
    have hevε : ∀ᶠ u : ℝ in atTop,
        -(xiMassBesselConeExponent a (min (Hgt u / u) (xiMassSpacelikeSharpSlope a))) ≤ ε :=
      hact.eventually_le_const hε0
    refine ⟨C + xiMassBesselExteriorSqrtTailConstant a sigma k0, ?_⟩
    filter_upwards [hev_slope k0 hk0lt, hevε, eventually_ge_atTop (1 : ℝ)] with u hu1 hu2 hu3
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu3
    obtain ⟨kk, hkk⟩ : ∃ k : ℝ, min (Hgt u / u) (xiMassSpacelikeSharpSlope a) = k := ⟨_, rfl⟩
    have hkkmul : kk * u = min (Hgt u) (xiMassSpacelikeSharpSlope a * u) := by
      rw [← hkk, min_mul_of_nonneg _ _ hupos.le, div_mul_cancel₀ _ (ne_of_gt hupos)]
    have hk0le : k0 * u ≤ kk * u := by
      rw [hkkmul]
      exact le_min hu1 (by nlinarith [hk0lt])
    have hkone : 1 < kk := by nlinarith [hk0le, hupos, hk0one]
    have hMH : ⌊Real.exp (kk * u)⌋₊ ≤ ⌊Real.exp (Hgt u)⌋₊ := by
      refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
      rw [hkkmul]
      exact min_le_left _ _
    have hMB : ⌊Real.exp (kk * u)⌋₊ ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ := by
      refine Nat.floor_mono (Real.exp_le_exp.2 ?_)
      rw [hkkmul]
      exact min_le_right _ _
    have hsub := norm_conePrimeIndexSum_sub_le (a := a) (sigma := sigma) (kappa0 := k0)
      (u := u) (H := kk * u) ha hsigma hk0one hupos hk0le
      (M := ⌊Real.exp (Hgt u)⌋₊) (N := ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊) hMH hMB
    rw [xiMassAction_at_slope hkone hupos.le] at hsub
    rw [hkk] at hu2
    have hexpmono : Real.exp (-(xiMassBesselConeExponent a kk) * u) ≤ Real.exp (ε * u) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [hu2, hupos]
    have hrootge : (1 : ℝ) ≤ Real.sqrt u := by
      have := Real.sqrt_le_sqrt hu3
      rwa [Real.sqrt_one] at this
    have hdiv : xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u
        ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt u)]
      nlinarith [hCT, hrootge]
    have hbase := hC u hupos.le
    rw [xiMassCriticalTruePrimeCone_eq_movingCone hkB, xiMassMovingPrimeCone] at hbase
    have hexp1 : (1 : ℝ) ≤ Real.exp (ε * u) := Real.one_le_exp (by positivity)
    have hsplit : xiMassMovingPrimeCone a sigma Hgt u
        = (∑ k ∈ conePrimeIndex ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊,
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
          + ((∑ k ∈ conePrimeIndex ⌊Real.exp (Hgt u)⌋₊,
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
            - ∑ k ∈ conePrimeIndex ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊,
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)) := by
      rw [xiMassMovingPrimeCone]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hprod : xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kk) * u)
        ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 * Real.exp (ε * u) := by
      have hnn : (0 : ℝ) ≤ xiMassBesselExteriorSqrtTailConstant a sigma k0 / Real.sqrt u := by
        positivity
      exact mul_le_mul hdiv hexpmono (Real.exp_nonneg _) hCT
    nlinarith [hbase, hsub, hprod, hexp1, hCT, hC0]
  · -- type zero forces RH
    intro hTZ
    have hall : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ q : XiZeroCopy,
        |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ ε := by
      intro ε hε0 hεhalf
      obtain ⟨Cz, hCz⟩ := hTZ ε hε0
      have hkone : 1 < xiMassGradedConeSlope a ε := one_lt_xiMassGradedConeSlope ha hε0.le hεhalf
      have hklt : xiMassGradedConeSlope a ε < xiMassSpacelikeSharpSlope a :=
        xiMassGradedConeSlope_lt_sharpSlope ha hε0 hεhalf
      have hslopeval := xiMassBesselConeExponent_gradedConeSlope ha hε0.le hεhalf.le
      have hCT : 0 ≤ xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε) := by
        rw [xiMassBesselExteriorSqrtTailConstant]
        have h1 : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma (xiMassGradedConeSlope a ε) :=
          xiMassBesselExteriorSqrtConstant_nonneg ha0 hkone
        have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
          primeLogRpowTailConstant_nonneg (by linarith)
        have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
        exact mul_nonneg h1 (mul_nonneg h3.le h2)
      have hgrowth : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
          ‖xiMassCriticalTruePrimeCone a sigma
            (xiMassConeDepthOfSlope (xiMassGradedConeSlope a ε)) u‖ ≤ C * Real.exp (ε * u) := by
        refine ⟨Cz + xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε), ?_⟩
        filter_upwards [hCz, hev_slope _ hklt, eventually_ge_atTop (1 : ℝ)] with u hu1 hu2 hu3
        have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu3
        have hMle : ⌊Real.exp (xiMassGradedConeSlope a ε * u)⌋₊ ≤ ⌊Real.exp (Hgt u)⌋₊ :=
          Nat.floor_mono (Real.exp_le_exp.2 hu2)
        have hsub := norm_conePrimeIndexSum_sub_le (a := a) (sigma := sigma)
          (kappa0 := xiMassGradedConeSlope a ε) (u := u)
          (H := xiMassGradedConeSlope a ε * u) ha hsigma hkone hupos le_rfl
          (M := ⌊Real.exp (xiMassGradedConeSlope a ε * u)⌋₊)
          (N := ⌊Real.exp (Hgt u)⌋₊) le_rfl hMle
        rw [xiMassAction_at_slope hkone hupos.le, hslopeval] at hsub
        have hrootge : (1 : ℝ) ≤ Real.sqrt u := by
          have := Real.sqrt_le_sqrt hu3
          rwa [Real.sqrt_one] at this
        have hdiv : xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε)
            / Real.sqrt u
            ≤ xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε) := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.sqrt u)]
          nlinarith [hCT, hrootge]
        have hprod : xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε)
            / Real.sqrt u * Real.exp (ε * u)
            ≤ xiMassBesselExteriorSqrtTailConstant a sigma (xiMassGradedConeSlope a ε)
              * Real.exp (ε * u) :=
          mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)
        rw [xiMassCriticalTruePrimeCone_eq_movingCone hkone, xiMassMovingPrimeCone]
        have hsplit : (∑ k ∈ conePrimeIndex ⌊Real.exp (xiMassGradedConeSlope a ε * u)⌋₊,
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
            = xiMassMovingPrimeCone a sigma Hgt u
              + ((∑ k ∈ conePrimeIndex ⌊Real.exp (xiMassGradedConeSlope a ε * u)⌋₊,
                  xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
                - ∑ k ∈ conePrimeIndex ⌊Real.exp (Hgt u)⌋₊,
                  xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)) := by
          rw [xiMassMovingPrimeCone]
          ring
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        nlinarith [hu1, hsub, hprod]
      exact (xiMassCriticalBesselConeLineGrowth_iff_mass_displacement_le hhalf hca hsigma hkone
        hε0.le (le_of_eq hslopeval)).1
        (xiMassCriticalBesselConeLineGrowth_of_eventually ha0 hsigma hkone hε0.le hgrowth)
    have hdisp : ∀ q : XiZeroCopy,
        |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ 0 := by
      intro q
      by_contra hcon
      have hpos : 0 < |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| := by
        rcases le_or_gt |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| 0 with h | h
        · exact absurd h hcon
        · exact h
      obtain ⟨m, hm⟩ : ∃ m : ℝ, min (1 / 2 : ℝ)
          |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| = m := ⟨_, rfl⟩
      have hm0 : 0 < m := by
        rw [← hm]
        exact lt_min (by norm_num) hpos
      have hstep := hall (m / 2) (by linarith) (by
        have : m ≤ 1 / 2 := by rw [← hm]; exact min_le_left _ _
        linarith) q
      have hle : m ≤ |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| := by
        rw [← hm]
        exact min_le_right _ _
      linarith
    have hgrowth0 := (xiMassCriticalBesselConeLineGrowth_iff_mass_displacement_le hhalf hca hsigma
      hkB (le_refl 0) (by rw [hzeroB]; norm_num)).2 hdisp
    obtain ⟨C, hC⟩ := hgrowth0
    refine (riemannHypothesis_iff_xiMassCriticalBesselConeLineBound hhalf hca hsigma hkB
      le_rfl).2 ⟨C, fun u hu => ?_⟩
    have := hC u hu
    simpa using this

/-! ## Stability of type zero -/

theorem XiMassTypeZero.add {A B : ℝ → ℂ} (hA : XiMassTypeZero A) (hB : XiMassTypeZero B) :
    XiMassTypeZero (fun u => A u + B u) := by
  intro ε hε
  obtain ⟨CA, hCA⟩ := hA ε hε
  obtain ⟨CB, hCB⟩ := hB ε hε
  refine ⟨CA + CB, ?_⟩
  filter_upwards [hCA, hCB] with u hu1 hu2
  refine (norm_add_le _ _).trans ?_
  nlinarith [hu1, hu2]

theorem XiMassTypeZero.sub {A B : ℝ → ℂ} (hA : XiMassTypeZero A) (hB : XiMassTypeZero B) :
    XiMassTypeZero (fun u => A u - B u) := by
  intro ε hε
  obtain ⟨CA, hCA⟩ := hA ε hε
  obtain ⟨CB, hCB⟩ := hB ε hε
  refine ⟨CA + CB, ?_⟩
  filter_upwards [hCA, hCB] with u hu1 hu2
  refine (norm_sub_le _ _).trans ?_
  nlinarith [hu1, hu2]

theorem XiMassTypeZero.congr {A B : ℝ → ℂ} (hA : XiMassTypeZero A) (h : ∀ u, A u = B u) :
    XiMassTypeZero B := by
  intro ε hε
  obtain ⟨C, hC⟩ := hA ε hε
  refine ⟨C, ?_⟩
  filter_upwards [hC] with u hu
  rw [← h u]
  exact hu

end

end RHTower
