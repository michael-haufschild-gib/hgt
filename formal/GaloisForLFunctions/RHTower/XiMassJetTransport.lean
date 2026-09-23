import GaloisForLFunctions.RHTower.XiMassCausticIterateWindow

/-!
# The jet operator transported to the conjugated carrier

The caustic-null jet operator on the mass profile and the operator `L` on the conjugated carrier are
the same object seen in two gauges:

`(4a⁴ − ∂²)ⁿ ( e^{-aZ}·G ) = e^{-aZ}·Lⁿ G`.

The induction is the single-step identity `4a⁴(e^{-aZ}G) − (e^{-aZ}G)″ = e^{-aZ}(c₀G + c₁G′ − G″)`
together with the fact that the region is open, so functions agreeing on it have equal derivatives
there.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The caustic-null jet operator iterated on the mass profile. -/
def xiMassJetIterate (a : ℝ) (τ : ℂ) : ℕ → ℂ → ℂ
  | 0 => xiMassBesselHeightSide a τ
  | k + 1 => fun ζ => 4 * (a : ℂ) ^ (4 : ℕ) * xiMassJetIterate a τ k ζ
      - deriv (deriv (xiMassJetIterate a τ k)) ζ

theorem xiMassJetIterate_succ (a : ℝ) (τ : ℂ) (k : ℕ) (ζ : ℂ) :
    xiMassJetIterate a τ (k + 1) ζ
      = 4 * (a : ℂ) ^ (4 : ℕ) * xiMassJetIterate a τ k ζ
        - deriv (deriv (xiMassJetIterate a τ k)) ζ := rfl

/-- **The two gauges agree.** -/
theorem xiMassJetIterate_eqOn {a : ℝ} (ha : 0 < a) (τ : ℂ) (k : ℕ) :
    Set.EqOn (xiMassJetIterate a τ k)
      (fun ζ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ) * xiCausticIterate a τ k ζ)
      (xiMassHeightRegion τ) := by
  have hopen := isOpen_xiMassHeightRegion τ
  induction k with
  | zero =>
      intro ζ _
      exact xiMassBesselHeightSide_eq_conjugated a τ ζ
  | succ k ih =>
      intro ζ hζ
      set F : ℂ → ℂ := fun v : ℂ =>
        Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v) * xiCausticIterate a τ k v with hFdef
      have hΦdiff : ∀ v : ℂ, v ∈ xiMassHeightRegion τ →
          HasDerivAt (xiCausticIterate a τ k) (deriv (xiCausticIterate a τ k) v) v := by
        intro v hv
        exact ((differentiableOn_xiCausticIterate ha τ k).differentiableAt
          (hopen.mem_nhds hv)).hasDerivAt
      have hana : AnalyticOnNhd ℂ (xiCausticIterate a τ k) (xiMassHeightRegion τ) :=
        (differentiableOn_xiCausticIterate ha τ k).analyticOnNhd hopen
      have hΦdiff2 : ∀ v : ℂ, v ∈ xiMassHeightRegion τ →
          HasDerivAt (deriv (xiCausticIterate a τ k))
            (deriv (deriv (xiCausticIterate a τ k)) v) v := by
        intro v hv
        exact ((hana.deriv.differentiableOn).differentiableAt (hopen.mem_nhds hv)).hasDerivAt
      -- first derivative in the conjugated gauge
      have hF1 : Set.EqOn (deriv F)
          (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v)
            * (deriv (xiCausticIterate a τ k) v
              - (a : ℂ) * xiMassRadiusRate τ v * xiCausticIterate a τ k v))
          (xiMassHeightRegion τ) := by
        intro v hv
        exact (hasDerivAt_expNegRadius_mul (a := a) hv (hΦdiff v hv)).deriv
      have hstep1 : Set.EqOn (deriv (xiMassJetIterate a τ k)) (deriv F)
          (xiMassHeightRegion τ) := by
        intro v hv
        exact Filter.EventuallyEq.deriv_eq (ih.eventuallyEq_of_mem (hopen.mem_nhds hv))
      have hstep2 : deriv (deriv (xiMassJetIterate a τ k)) ζ = deriv (deriv F) ζ :=
        Filter.EventuallyEq.deriv_eq (hstep1.eventuallyEq_of_mem (hopen.mem_nhds hζ))
      have hstep3 : deriv (deriv F) ζ
          = deriv (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v)
              * (deriv (xiCausticIterate a τ k) v
                - (a : ℂ) * xiMassRadiusRate τ v * xiCausticIterate a τ k v)) ζ :=
        Filter.EventuallyEq.deriv_eq (hF1.eventuallyEq_of_mem (hopen.mem_nhds hζ))
      have hstep4 : deriv (fun v : ℂ => Complex.exp (-(a : ℂ) * xiMassHeightRadius τ v)
              * (deriv (xiCausticIterate a τ k) v
                - (a : ℂ) * xiMassRadiusRate τ v * xiCausticIterate a τ k v)) ζ
          = Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ)
            * (deriv (deriv (xiCausticIterate a τ k)) ζ
              - (a : ℂ) * (1 / xiMassHeightRadius τ ζ - ζ ^ (2 : ℕ) / xiMassHeightRadius τ ζ ^ (3 : ℕ))
                  * xiCausticIterate a τ k ζ
              - 2 * (a : ℂ) * xiMassRadiusRate τ ζ * deriv (xiCausticIterate a τ k) ζ
              + (a : ℂ) ^ (2 : ℕ) * xiMassRadiusRate τ ζ ^ (2 : ℕ) * xiCausticIterate a τ k ζ) :=
        (hasDerivAt_expNegRadius_caustic (a := a) hζ (hΦdiff ζ hζ) (hΦdiff2 ζ hζ)).deriv
      rw [xiMassJetIterate_succ, ih hζ, hstep2, hstep3, hstep4]
      show 4 * (a : ℂ) ^ (4 : ℕ) * (Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ)
            * xiCausticIterate a τ k ζ)
          - Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ)
            * (deriv (deriv (xiCausticIterate a τ k)) ζ
              - (a : ℂ) * (1 / xiMassHeightRadius τ ζ - ζ ^ (2 : ℕ) / xiMassHeightRadius τ ζ ^ (3 : ℕ))
                  * xiCausticIterate a τ k ζ
              - 2 * (a : ℂ) * xiMassRadiusRate τ ζ * deriv (xiCausticIterate a τ k) ζ
              + (a : ℂ) ^ (2 : ℕ) * xiMassRadiusRate τ ζ ^ (2 : ℕ) * xiCausticIterate a τ k ζ)
        = Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ζ) * xiCausticIterate a τ (k + 1) ζ
      rw [xiCausticIterate_succ, xiCausticCoeffZero, xiCausticCoeffOne,
        xiMassCausticSymbolC_eq_sub_sq hζ, xiMassRadiusRate]
      ring

/-- **(22.7) The caustic-null jet raises the transport power.**  The `n`-th caustic-null jet of the
mass profile, read on the balance ray, decays by a further half power of the height per application
while keeping the full exterior Bessel exponential. -/
theorem exists_norm_xiMassJetIterate_window_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n
          (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖
        ≤ C / Real.sqrt u ^ (n + 1)
          * Real.exp (-(a * Real.sqrt ((xiMassSpacelikeSharpSlope a * u) ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
  obtain ⟨C, u₀, hC, hu₀, hbound⟩ := exists_norm_xiCausticIterate_window_le ha hsigma n
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  refine ⟨C, u₀, hC, hu₀, ?_⟩
  intro u hu
  have huw : xiMassWindowThreshold a ≤ u := le_trans hu₀ hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) huw
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set h : ℝ := xiMassSpacelikeSharpSlope a * u with hhdef
  have huh : u ≤ h := by
    rw [hhdef]
    nlinarith [hκ1, hu0]
  have hmem : ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
    rw [hτdef, hhdef]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha huw ?_
    simp [Real.sqrt_nonneg]
  have hgauge := xiMassJetIterate_eqOn ha0 τ n hmem
  rw [hgauge]
  have hpropeq : τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ) = xiMassSpacelikePropagationArgument sigma u h := by
    rw [xiMassSpacelikePropagationArgument_eq, hτdef]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ)))) := by
    rw [Complex.norm_exp]
    congr 1
    have hre := re_mul_xiMassHeightRadius a τ ((h : ℝ) : ℂ)
    have hneg : (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
        = -((a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ)) := by ring
    rw [hneg, Complex.neg_re, hre]
  have hgap : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))
      ≤ HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hpropeq]
    have hmono : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ≤ Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg sigma])
    exact le_trans hmono (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu0.le huh)
  have hexple : Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ))))
      ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hgap, ha0]
  have hΦ := hbound u hu
  rw [← hτdef, ← hhdef] at hΦ
  have hΦ0 : (0 : ℝ) ≤ ‖xiCausticIterate a τ n ((h : ℝ) : ℂ)‖ := norm_nonneg _
  calc ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
          * xiCausticIterate a τ n ((h : ℝ) : ℂ)‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ))))
        * ‖xiCausticIterate a τ n ((h : ℝ) : ℂ)‖ := by rw [norm_mul, hexpnorm]
    _ ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) * (C / Real.sqrt u ^ (n + 1)) :=
        mul_le_mul hexple hΦ hΦ0 (Real.exp_pos _).le
    _ = C / Real.sqrt u ^ (n + 1) * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by ring

/-- **(22.7) across the whole balance window.**  The bound of the previous theorem holds uniformly
for every height in the square-root window about the balance ray. -/
theorem exists_norm_xiMassJetIterate_window_le' {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ t : ℝ,
      |t| ≤ Real.sqrt u / 2 →
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n
          (((xiMassSpacelikeSharpSlope a * u + t : ℝ)) : ℂ)‖
        ≤ C / Real.sqrt u ^ (n + 1)
          * Real.exp (-(a * Real.sqrt ((xiMassSpacelikeSharpSlope a * u + t) ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
  obtain ⟨C, u₀, hC, hu₀, hbound⟩ := exists_norm_xiCausticIterate_window_le' ha hsigma n
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκgap : (0 : ℝ) < xiMassSpacelikeSharpSlope a - 1 := by linarith
  refine ⟨C, max u₀ ((1 / (2 * (xiMassSpacelikeSharpSlope a - 1))) ^ (2 : ℕ)),
    hC, le_trans hu₀ (le_max_left _ _), ?_⟩
  intro u hu t ht
  have hu0' : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have hugap : ((1 / (2 * (xiMassSpacelikeSharpSlope a - 1))) ^ (2 : ℕ) : ℝ) ≤ u :=
    le_trans (le_max_right _ _) hu
  have huw : xiMassWindowThreshold a ≤ u := le_trans hu₀ hu0'
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) huw
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hrsq : Real.sqrt u ^ (2 : ℕ) = u := Real.sq_sqrt hu0.le
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set h : ℝ := xiMassSpacelikeSharpSlope a * u + t with hhdef
  have hrgap : 1 / (2 * (xiMassSpacelikeSharpSlope a - 1)) ≤ Real.sqrt u := by
    have hnn : (0 : ℝ) ≤ 1 / (2 * (xiMassSpacelikeSharpSlope a - 1)) := by positivity
    nlinarith [hugap, hrsq, hr0]
  have huh : u ≤ h := by
    have habs := (abs_le.mp ht).1
    have hmul : 1 ≤ Real.sqrt u * (2 * (xiMassSpacelikeSharpSlope a - 1)) := by
      rwa [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (xiMassSpacelikeSharpSlope a - 1))] at hrgap
    have hstep := mul_le_mul_of_nonneg_right hmul hr0.le
    have hkey : Real.sqrt u / 2 ≤ (xiMassSpacelikeSharpSlope a - 1) * u := by
      nlinarith [hstep, hrsq]
    rw [hhdef]
    linarith
  have hcast : (((xiMassSpacelikeSharpSlope a * u + t : ℝ)) : ℂ)
      = (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + (t : ℂ) := by push_cast; ring
  have hmem : ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
    rw [hτdef, hhdef, hcast]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha huw ?_
    have hid : (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + (t : ℂ)
        - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) = (t : ℂ) := by ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs]
    linarith [ht, hr0]
  have hgauge := xiMassJetIterate_eqOn ha0 τ n hmem
  rw [show (((xiMassSpacelikeSharpSlope a * u + t : ℝ)) : ℂ) = ((h : ℝ) : ℂ) by rw [hhdef],
    hgauge]
  have hpropeq : τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ) = xiMassSpacelikePropagationArgument sigma u h := by
    rw [xiMassSpacelikePropagationArgument_eq, hτdef]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ)))) := by
    rw [Complex.norm_exp]
    congr 1
    have hre := re_mul_xiMassHeightRadius a τ ((h : ℝ) : ℂ)
    have hneg : (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
        = -((a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ)) := by ring
    rw [hneg, Complex.neg_re, hre]
  have hgap : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))
      ≤ HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hpropeq]
    have hmono : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ≤ Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg sigma])
    exact le_trans hmono (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu0.le huh)
  have hexple : Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ))))
      ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hgap, ha0]
  have hΦ := hbound u hu0' t ht
  rw [← hτdef] at hΦ
  rw [show (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + (t : ℂ) = ((h : ℝ) : ℂ) by
    rw [hhdef]; push_cast; ring] at hΦ
  have hΦ0 : (0 : ℝ) ≤ ‖xiCausticIterate a τ n ((h : ℝ) : ℂ)‖ := norm_nonneg _
  calc ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
          * xiCausticIterate a τ n ((h : ℝ) : ℂ)‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ (2 : ℕ) + ((h : ℝ) : ℂ) ^ (2 : ℕ))))
        * ‖xiCausticIterate a τ n ((h : ℝ) : ℂ)‖ := by rw [norm_mul, hexpnorm]
    _ ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) * (C / Real.sqrt u ^ (n + 1)) :=
        mul_le_mul hexple hΦ hΦ0 (Real.exp_pos _).le
    _ = C / Real.sqrt u ^ (n + 1) * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by ring

end

end RHTower
