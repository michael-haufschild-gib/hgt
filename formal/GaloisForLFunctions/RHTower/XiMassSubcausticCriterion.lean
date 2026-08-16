import GaloisForLFunctions.RHTower.XiMassPrefixQuadratureDefect

/-!
# The subcaustic RH criterion

The moving quadrature defect at the retreated cutoff `⌊e^{κ_B u − L u^{1/10}}⌋` differs from the
defect at the caustic cutoff by

* the prime-discrepancy annulus between the two heights, which vanishes in the whole closed
  coefficient chamber, and
* two integer edge corrections, each bounded by `√e · ∫ e^{-σ|x|}dx` because the continuum weight
  `e^{h/2}` grows only half as fast as the cutoff spacing `e^{-h}` shrinks.

On the initial height range both defects are bounded by a function of their cutoffs alone.  Hence
the two boundedness statements are equivalent, and the Riemann hypothesis is equivalent to uniform
boundedness of the quadrature defect strictly inside the entropy--action caustic.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The prefix defect difference in terms of the window defect and two edge corrections. -/
theorem prefixDefect_sub_eq_window {a sigma u H T : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hHT : H ≤ T) :
    xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp T⌋₊
        - xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp H⌋₊
      = ((∑ p ∈ primeLogWindow H T, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
          - ∫ h in H..T, xiMassCriticalGrowingFourierProfile a sigma u h)
        + (∫ h in H..Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1),
            xiMassCriticalGrowingFourierProfile a sigma u h)
        - ∫ h in T..Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1),
            xiMassCriticalGrowingFourierProfile a sigma u h := by
  classical
  have hfl : ⌊Real.exp H⌋₊ ≤ ⌊Real.exp T⌋₊ := Nat.floor_mono (Real.exp_le_exp.2 hHT)
  have hcont := continuous_xiMassCriticalGrowingFourierProfile ha hsigma u
  have hA : (∫ h in H..Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h)
      + ∫ h in Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1)..Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h
      = ∫ h in H..Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hB : (∫ h in H..Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h)
      + ∫ h in Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1)..T,
        xiMassCriticalGrowingFourierProfile a sigma u h
      = ∫ h in H..T, xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hC : (∫ h in Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1)..T,
        xiMassCriticalGrowingFourierProfile a sigma u h)
      = -∫ h in T..Real.log ((⌊Real.exp T⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_symm _ _
  rw [xiMassPrefixQuadratureDefect_sub ha hsigma hfl, primeLogWindow]
  linear_combination -hA - hB + hC

/-- **The two defects differ by a bounded amount.** -/
theorem exists_norm_prefixDefect_caustic_sub_le {a sigma L : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hL : 0 < L)
    (hvanish : Tendsto (fun u : ℝ =>
        ‖(∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
              (xiMassSpacelikeSharpSlope a * u),
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
          - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
              xiMassCriticalGrowingFourierProfile a sigma u h‖) atTop (nhds 0)) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        - xiMassPrefixQuadratureDefect a sigma u
            ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hMnn := xiMassVerticalBound_nonneg sigma
  -- the eventual regime
  have hgrow : Tendsto (fun u : ℝ => u ^ ((9 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev1 : ∀ᶠ u : ℝ in atTop,
      ‖(∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
            (xiMassSpacelikeSharpSlope a * u),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
            xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ 1 :=
    hvanish.eventually_le_const (by norm_num)
  have hev2 : ∀ᶠ u : ℝ in atTop,
      L / xiMassSpacelikeSharpSlope a ≤ u ^ ((9 : ℝ) / 10) := hgrow.eventually_ge_atTop _
  obtain ⟨u₁, hu₁⟩ := ((hev1.and hev2).and (eventually_ge_atTop (0 : ℝ))).exists_forall_of_atTop
  have hu₁0 : (0 : ℝ) ≤ u₁ := (hu₁ u₁ le_rfl).2
  refine ⟨max (1 + 2 * (Real.exp (1 / 2) * xiMassVerticalBound sigma))
    (2 * xiMassPrefixDefectBound sigma ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊),
    fun u hu => ?_⟩
  have hHle : xiMassSubcausticHeight a L u ≤ xiMassSpacelikeSharpSlope a * u := by
    rw [xiMassSubcausticHeight]
    have : (0 : ℝ) ≤ L * u ^ ((1 : ℝ) / 10) := by positivity
    linarith
  rcases le_or_gt u₁ u with hcase | hcase
  · -- the asymptotic regime
    obtain ⟨⟨hD, hpow⟩, _⟩ := hu₁ u hcase
    have hupos : (0 : ℝ) < u := by
      rcases eq_or_lt_of_le hu with h | h
      · exfalso
        have hzero : (0 : ℝ) ^ ((9 : ℝ) / 10) = 0 := Real.zero_rpow (by norm_num)
        rw [← h, hzero] at hpow
        have : (0 : ℝ) < L / xiMassSpacelikeSharpSlope a := by positivity
        linarith
      · exact h
    have hH0 : 0 ≤ xiMassSubcausticHeight a L u := by
      rw [xiMassSubcausticHeight]
      have hsplit : u ^ ((1 : ℝ) / 10) * u ^ ((9 : ℝ) / 10) = u := by
        rw [← Real.rpow_add hupos]
        norm_num
      have hpow0 : (0 : ℝ) < u ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hupos _
      have h1 : L ≤ xiMassSpacelikeSharpSlope a * u ^ ((9 : ℝ) / 10) := by
        rw [div_le_iff₀ hkap] at hpow
        linarith
      have h2 : L * u ^ ((1 : ℝ) / 10)
          ≤ xiMassSpacelikeSharpSlope a * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right h1 hpow0.le
      have h3 : xiMassSpacelikeSharpSlope a * u ^ ((9 : ℝ) / 10) * u ^ ((1 : ℝ) / 10)
          = xiMassSpacelikeSharpSlope a * u := by
        rw [mul_assoc, mul_comm (u ^ ((9 : ℝ) / 10)), hsplit]
      rw [h3] at h2
      linarith
    have hT0 : (0 : ℝ) ≤ xiMassSpacelikeSharpSlope a * u := by positivity
    have hdec := prefixDefect_sub_eq_window (a := a) (sigma := sigma) (u := u)
      (H := xiMassSubcausticHeight a L u) (T := xiMassSpacelikeSharpSlope a * u)
      ha0 hsigma hHle
    have he1 := norm_integral_growing_edge_le (a := a) (sigma := sigma) (u := u)
      (H := xiMassSubcausticHeight a L u) ha0 hsigma hH0
    have he2 := norm_integral_growing_edge_le (a := a) (sigma := sigma) (u := u)
      (H := xiMassSpacelikeSharpSlope a * u) ha0 hsigma hT0
    rw [hdec]
    refine le_trans ?_ (le_max_left _ _)
    calc ‖((∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
              (xiMassSpacelikeSharpSlope a * u),
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
            - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
                xiMassCriticalGrowingFourierProfile a sigma u h)
          + (∫ h in (xiMassSubcausticHeight a L u)..Real.log
              ((⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊ : ℝ) + 1),
              xiMassCriticalGrowingFourierProfile a sigma u h)
          - ∫ h in (xiMassSpacelikeSharpSlope a * u)..Real.log
              ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1),
              xiMassCriticalGrowingFourierProfile a sigma u h‖
        ≤ ‖((∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
                (xiMassSpacelikeSharpSlope a * u),
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
              - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
                  xiMassCriticalGrowingFourierProfile a sigma u h)
            + (∫ h in (xiMassSubcausticHeight a L u)..Real.log
                ((⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊ : ℝ) + 1),
                xiMassCriticalGrowingFourierProfile a sigma u h)‖
          + ‖∫ h in (xiMassSpacelikeSharpSlope a * u)..Real.log
              ((⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊ : ℝ) + 1),
              xiMassCriticalGrowingFourierProfile a sigma u h‖ := norm_sub_le _ _
      _ ≤ 1 + (Real.exp (1 / 2) * xiMassVerticalBound sigma)
            + Real.exp (1 / 2) * xiMassVerticalBound sigma := by
          have := norm_add_le
            ((∑ p ∈ primeLogWindow (xiMassSubcausticHeight a L u)
                (xiMassSpacelikeSharpSlope a * u),
              xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
              - ∫ h in (xiMassSubcausticHeight a L u)..(xiMassSpacelikeSharpSlope a * u),
                  xiMassCriticalGrowingFourierProfile a sigma u h)
            (∫ h in (xiMassSubcausticHeight a L u)..Real.log
                ((⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊ : ℝ) + 1),
                xiMassCriticalGrowingFourierProfile a sigma u h)
          linarith [this, hD, he1, he2]
      _ = 1 + 2 * (Real.exp (1 / 2) * xiMassVerticalBound sigma) := by ring
  · -- the initial regime
    have hmono1 : ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith [hcase.le, hkap]))
    have hmono2 : ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊
        ≤ ⌊Real.exp (xiMassSpacelikeSharpSlope a * u₁)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith [hHle, hcase.le, hkap]))
    have hb1 := norm_xiMassPrefixQuadratureDefect_le (a := a) (sigma := sigma) ha0 hsigma u
      ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
    have hb2 := norm_xiMassPrefixQuadratureDefect_le (a := a) (sigma := sigma) ha0 hsigma u
      ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊
    have hm1 := xiMassPrefixDefectBound_mono (sigma := sigma) hmono1
    have hm2 := xiMassPrefixDefectBound_mono (sigma := sigma) hmono2
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans ?_ (le_max_right _ _)
    linarith

/-- The subcaustic quadrature-defect line bound. -/
def XiMassSubcausticQuadratureDefectLineBound (a sigma L : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassPrefixQuadratureDefect a sigma u
      ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊‖ ≤ C

/-- **(19.7) The subcaustic RH criterion.**  There is a positive coefficient chamber inside which
RH is equivalent to uniform boundedness of the prime-discrepancy quadrature defect at the
retreated cutoff `⌊e^{κ_B u − L u^{1/10}}⌋`. -/
theorem exists_riemannHypothesis_iff_xiMassSubcausticQuadratureDefectLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ L : ℝ, 0 < L → L ≤ Lc →
      (RiemannHypothesis ↔ XiMassSubcausticQuadratureDefectLineBound a sigma L) := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  obtain ⟨Lc, hLc0, hLc⟩ := exists_tendsto_subcausticWindowDefect_zero ha hsigma
  refine ⟨Lc, hLc0, fun L hL hLle => ?_⟩
  obtain ⟨C₀, hC₀⟩ := exists_norm_prefixDefect_caustic_sub_le ha hsigma hL (hLc L hL hLle)
  have hcaustic := riemannHypothesis_iff_xiMassCriticalBesselQuadratureDefectLineBound
    (a := a) (c := c) (sigma := sigma) (kappa := xiMassSpacelikeSharpSlope a)
    hhalf hca hsigma hkone le_rfl
  rw [hcaustic, XiMassCriticalBesselQuadratureDefectLineBound,
    XiMassSubcausticQuadratureDefectLineBound]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + C₀, fun u hu => ?_⟩
    have hB := hC u hu
    rw [xiMassCriticalPrimeQuadratureDefect_eq_prefix hkone u] at hB
    have hdiff := hC₀ u hu
    have hsplit : xiMassPrefixQuadratureDefect a sigma u
        ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊
        = xiMassPrefixQuadratureDefect a sigma u
            ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
          - (xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
            - xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊) := by ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add hB hdiff)
  · rintro ⟨C, hC⟩
    refine ⟨C + C₀, fun u hu => ?_⟩
    have hS := hC u hu
    have hdiff := hC₀ u hu
    rw [xiMassCriticalPrimeQuadratureDefect_eq_prefix hkone u]
    have hsplit : xiMassPrefixQuadratureDefect a sigma u
        ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
        = xiMassPrefixQuadratureDefect a sigma u
            ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊
          + (xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSpacelikeSharpSlope a * u)⌋₊
            - xiMassPrefixQuadratureDefect a sigma u
              ⌊Real.exp (xiMassSubcausticHeight a L u)⌋₊) := by ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hS hdiff)

end

end RHTower
