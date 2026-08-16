import GaloisForLFunctions.RHTower.XiMassSubcausticVanishing
import GaloisForLFunctions.RHTower.XiMassBesselConeQuadratureDefect

/-!
# The quadrature defect at an integer cutoff

The prime--continuum quadrature defect of the moving mass profile below an integer cutoff `M` is

`Q(u,M) = ∑_{p ≤ M} (log p) p^{-1/2} F_u(log p) − ∫_0^{log(M+1)} e^{h/2} F_u(h) dh`.

Since the mass Fourier profile obeys the vertical bound `|F_u(h)| ≤ ∫ e^{-σ|x|}dx` uniformly in
both the height and the vertical time, the defect at a fixed cutoff is bounded by a function of
the cutoff alone.  Two such defects differ by the corresponding prime annulus minus the continuum
integral between the two cone edges.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The uniform vertical bound -/

/-- The uniform vertical bound of the mass Fourier profile. -/
def xiMassVerticalBound (sigma : ℝ) : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))

theorem xiMassVerticalBound_nonneg (sigma : ℝ) : 0 ≤ xiMassVerticalBound sigma := by
  rw [xiMassVerticalBound]
  exact MeasureTheory.integral_nonneg fun x => Real.exp_nonneg _

theorem norm_stripFourier_le_verticalBound {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u w : ℝ) :
    ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (w : ℂ)‖
      ≤ xiMassVerticalBound sigma :=
  norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u w

theorem norm_xiMassCenteredPrimeAtom_le_verticalBound {a sigma u : ℝ} {p : ℕ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hp : p.Prime) :
    ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p‖
      ≤ Real.log p * xiMassVerticalBound sigma := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith) _
  rw [xiMassCenteredPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_prime hp]
  have hF := norm_stripFourier_le_verticalBound ha hsigma u (Real.log p)
  have hMnn := xiMassVerticalBound_nonneg sigma
  have hstep : Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))
      * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) ((Real.log p : ℝ) : ℂ)‖
      ≤ Real.log p * 1 * xiMassVerticalBound sigma := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hlog) hF (norm_nonneg _) ?_
    exact mul_nonneg hlog (by norm_num)
  simpa using hstep

theorem norm_xiMassCriticalGrowingFourierProfile_le_verticalBound {a sigma u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) :
    ‖xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ Real.exp (h / 2) * xiMassVerticalBound sigma := by
  rw [xiMassCriticalGrowingFourierProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_stripFourier_le_verticalBound ha hsigma u h)
    (Real.exp_nonneg _)

theorem continuous_xiMassCriticalGrowingFourierProfile {a sigma : ℝ} (ha : 0 < a)
    (hsigma : 0 < sigma) (u : ℝ) :
    Continuous (xiMassCriticalGrowingFourierProfile a sigma u) := by
  rw [continuous_iff_continuousAt]
  intro h
  exact (hasDerivAt_xiMassCriticalGrowingFourierProfile ha hsigma u h).continuousAt

/-! ## The defect at an integer cutoff -/

/-- The prime--continuum quadrature defect below an integer cutoff. -/
def xiMassPrefixQuadratureDefect (a sigma u : ℝ) (M : ℕ) : ℂ :=
  (∑ k ∈ conePrimeIndex M, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
    - ∫ h in (0 : ℝ)..Real.log ((M : ℝ) + 1), xiMassCriticalGrowingFourierProfile a sigma u h

/-- The bound on the defect at a fixed cutoff, uniform in the vertical time. -/
def xiMassPrefixDefectBound (sigma : ℝ) (M : ℕ) : ℝ :=
  (2 * (M : ℝ) + 1) * Real.log ((M : ℝ) + 1) * xiMassVerticalBound sigma

theorem xiMassPrefixDefectBound_nonneg (sigma : ℝ) (M : ℕ) :
    0 ≤ xiMassPrefixDefectBound sigma M := by
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have h1 : (0 : ℝ) ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h2 : (0 : ℝ) ≤ 2 * (M : ℝ) + 1 := by positivity
  rw [xiMassPrefixDefectBound]
  exact mul_nonneg (mul_nonneg h2 h1) (xiMassVerticalBound_nonneg sigma)

theorem xiMassPrefixDefectBound_mono {sigma : ℝ} {M N : ℕ} (h : M ≤ N) :
    xiMassPrefixDefectBound sigma M ≤ xiMassPrefixDefectBound sigma N := by
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMN : ((M : ℝ)) ≤ (N : ℝ) := by exact_mod_cast h
  have h1 : Real.log ((M : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hstep : (2 * (M : ℝ) + 1) * Real.log ((M : ℝ) + 1)
      ≤ (2 * (N : ℝ) + 1) * Real.log ((N : ℝ) + 1) := by
    refine mul_le_mul (by linarith) h1 h2 (by positivity)
  rw [xiMassPrefixDefectBound, xiMassPrefixDefectBound]
  exact mul_le_mul_of_nonneg_right hstep (xiMassVerticalBound_nonneg sigma)

/-- **The defect at a fixed cutoff is bounded uniformly in the vertical time.** -/
theorem norm_xiMassPrefixQuadratureDefect_le {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u : ℝ) (M : ℕ) :
    ‖xiMassPrefixQuadratureDefect a sigma u M‖ ≤ xiMassPrefixDefectBound sigma M := by
  classical
  have hMnn := xiMassVerticalBound_nonneg sigma
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlogM : (0 : ℝ) ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  -- the prime part
  have hsum : ‖∑ k ∈ conePrimeIndex M,
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)‖
      ≤ (M : ℝ) * (Real.log ((M : ℝ) + 1) * xiMassVerticalBound sigma) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ conePrimeIndex M,
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)‖
          ≤ Real.log ((M : ℝ) + 1) * xiMassVerticalBound sigma := by
      intro k hk
      rw [mem_conePrimeIndex] at hk
      refine (norm_xiMassCenteredPrimeAtom_le_verticalBound ha hsigma hk.2).trans ?_
      have hle : ((k + 2 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
        have : ((k + 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk.1
        linarith
      have hlog : Real.log ((k + 2 : ℕ) : ℝ) ≤ Real.log ((M : ℝ) + 1) :=
        Real.log_le_log (by positivity) hle

      exact mul_le_mul_of_nonneg_right hlog hMnn
    have hcard : ((conePrimeIndex M).card : ℝ) ≤ (M : ℝ) := by
      have h3 : (conePrimeIndex M).card ≤ M := by
        rw [conePrimeIndex]
        calc (Finset.filter (fun k => Nat.Prime (k + 2)) (Finset.range (M - 1))).card
            ≤ (Finset.range (M - 1)).card := Finset.card_filter_le _ _
          _ = M - 1 := Finset.card_range _
          _ ≤ M := Nat.sub_le _ _
      exact_mod_cast h3
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hlogM hMnn)
  -- the continuum part
  have hint : ‖∫ h in (0 : ℝ)..Real.log ((M : ℝ) + 1),
      xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ ((M : ℝ) + 1) * xiMassVerticalBound sigma * Real.log ((M : ℝ) + 1) := by
    have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) (Real.log ((M : ℝ) + 1)),
        ‖xiMassCriticalGrowingFourierProfile a sigma u x‖
          ≤ ((M : ℝ) + 1) * xiMassVerticalBound sigma := by
      intro x hx
      rw [Set.uIoc_of_le hlogM] at hx
      refine (norm_xiMassCriticalGrowingFourierProfile_le_verticalBound ha hsigma).trans ?_
      have hxe : Real.exp (x / 2) ≤ (M : ℝ) + 1 := by
        have h1 : x / 2 ≤ Real.log ((M : ℝ) + 1) := by linarith [hx.1, hx.2]
        have h2 := Real.exp_le_exp.2 h1
        rwa [Real.exp_log (by positivity)] at h2
      exact mul_le_mul_of_nonneg_right hxe hMnn
    have hres := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rwa [sub_zero, abs_of_nonneg hlogM] at hres
  rw [xiMassPrefixQuadratureDefect, xiMassPrefixDefectBound]
  refine (norm_sub_le _ _).trans ?_
  nlinarith [hsum, hint, hMnn, hlogM]

/-! ## Identification and differences -/

theorem xiMassCriticalPrimeQuadratureDefect_eq_prefix {a sigma kappa : ℝ} (hkappa : 1 < kappa)
    (u : ℝ) :
    xiMassCriticalPrimeQuadratureDefect a sigma (xiMassConeDepthOfSlope kappa) u
      = xiMassPrefixQuadratureDefect a sigma u ⌊Real.exp (kappa * u)⌋₊ := by
  classical
  rw [xiMassCriticalPrimeQuadratureDefect, xiMassPrefixQuadratureDefect,
    xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassCriticalConeEdge,
    xiMassConeDepthOfSlope_height hkappa, conePrimeIndex]

theorem xiMassPrefixQuadratureDefect_sub {a sigma u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    xiMassPrefixQuadratureDefect a sigma u M₂ - xiMassPrefixQuadratureDefect a sigma u M₁
      = (∑ p ∈ (Finset.Ioc M₁ M₂).filter (fun p => Nat.Prime p),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in Real.log ((M₁ : ℝ) + 1)..Real.log ((M₂ : ℝ) + 1),
            xiMassCriticalGrowingFourierProfile a sigma u h := by
  classical
  have hcont := continuous_xiMassCriticalGrowingFourierProfile ha hsigma u
  have hsplit : (∫ h in (0 : ℝ)..Real.log ((M₁ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h)
      + ∫ h in Real.log ((M₁ : ℝ) + 1)..Real.log ((M₂ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h
      = ∫ h in (0 : ℝ)..Real.log ((M₂ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have hsum : (∑ k ∈ conePrimeIndex M₂ \ conePrimeIndex M₁,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
      + ∑ k ∈ conePrimeIndex M₁, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2)
      = ∑ k ∈ conePrimeIndex M₂, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2) :=
    Finset.sum_sdiff (conePrimeIndex_subset h)
  have hwin : (∑ k ∈ conePrimeIndex M₂ \ conePrimeIndex M₁,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
      = ∑ p ∈ (Finset.Ioc M₁ M₂).filter (fun p => Nat.Prime p),
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p :=
    sum_conePrimeIndex_sdiff_eq
      (g := fun p : ℕ => xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
  rw [xiMassPrefixQuadratureDefect, xiMassPrefixQuadratureDefect, ← hwin, ← hsplit, ← hsum]
  ring

/-! ## The integer edge correction -/

theorem norm_integral_growing_edge_le {a sigma u H : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hH : 0 ≤ H) :
    ‖∫ h in H..Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1),
        xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ Real.exp (1 / 2) * xiMassVerticalBound sigma := by
  have hMnn := xiMassVerticalBound_nonneg sigma
  have hEpos : (0 : ℝ) < Real.exp H := Real.exp_pos H
  have hfl : (0 : ℝ) ≤ (⌊Real.exp H⌋₊ : ℝ) := Nat.cast_nonneg _
  have hflle : ((⌊Real.exp H⌋₊ : ℕ) : ℝ) ≤ Real.exp H := Nat.floor_le hEpos.le
  have hHW : H ≤ Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) := by
    have h1 : Real.exp H < (⌊Real.exp H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 := Real.log_lt_log hEpos h1
    rw [Real.log_exp] at h2
    exact h2.le
  have hgap : Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) - H ≤ Real.exp (-H) := by
    have hle : ((⌊Real.exp H⌋₊ : ℝ) + 1) ≤ Real.exp H * (1 + Real.exp (-H)) := by
      have hinv : Real.exp H * Real.exp (-H) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [hflle, hinv]
    have hpos : (0 : ℝ) < (⌊Real.exp H⌋₊ : ℝ) + 1 := by linarith
    have hstep := Real.log_le_log hpos hle
    rw [Real.log_mul (ne_of_gt hEpos) (by positivity), Real.log_exp] at hstep
    have hlog1 : Real.log (1 + Real.exp (-H)) ≤ Real.exp (-H) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + Real.exp (-H) by positivity)
      linarith
    linarith
  have hexpH : Real.exp (-H) ≤ 1 := by
    have := Real.exp_le_exp.2 (show -H ≤ (0 : ℝ) by linarith)
    simpa using this
  have hWle : Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) ≤ H + 1 := by linarith
  have hbd : ∀ x ∈ Set.uIoc H (Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1)),
      ‖xiMassCriticalGrowingFourierProfile a sigma u x‖
        ≤ Real.exp ((H + 1) / 2) * xiMassVerticalBound sigma := by
    intro x hx
    rw [Set.uIoc_of_le hHW] at hx
    refine (norm_xiMassCriticalGrowingFourierProfile_le_verticalBound ha hsigma).trans ?_
    have hxe : Real.exp (x / 2) ≤ Real.exp ((H + 1) / 2) :=
      Real.exp_le_exp.2 (by linarith [hx.2, hWle])
    exact mul_le_mul_of_nonneg_right hxe hMnn
  have hres := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  refine hres.trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) - H)]
  have hprod : Real.exp ((H + 1) / 2) * (Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) - H)
      ≤ Real.exp ((H + 1) / 2) * Real.exp (-H) :=
    mul_le_mul_of_nonneg_left hgap (Real.exp_nonneg _)
  have hval : Real.exp ((H + 1) / 2) * Real.exp (-H) ≤ Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hchain : Real.exp ((H + 1) / 2) * xiMassVerticalBound sigma
      * (Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) - H)
      ≤ Real.exp (1 / 2) * xiMassVerticalBound sigma := by
    have hstep : Real.exp ((H + 1) / 2) * (Real.log ((⌊Real.exp H⌋₊ : ℝ) + 1) - H)
        ≤ Real.exp (1 / 2) := le_trans hprod hval
    nlinarith [hstep, hMnn]
  exact hchain

end

end RHTower
