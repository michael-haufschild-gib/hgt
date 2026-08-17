import GaloisForLFunctions.RHTower.XiMassGenericWindowDiscrepancy
import GaloisForLFunctions.RHTower.XiMassJetComplexWindow
import GaloisForLFunctions.RHTower.XiMassJetSourceSide
import GaloisForLFunctions.RHTower.XiMassJetPrimeTail

/-!
# The window discrepancy estimate for the jet-modified receiver

Instantiating the generic `(19.3)` at the caustic-null jet: the profile is the damped iterated jet,
its height derivative is the Cauchy estimate of the previous module, and both carry the envelope
`D·u^{-(2N+1)/2}·e^{-h/2}e^{-a√(h²−u²)}` on the square-root window.  The prime-discrepancy annulus of
the modified receiver is therefore bounded by the same shape as the base one, with the extra jet
gain inside the constant.
-/

/-!
# The damped jet receiver on the window, and the filtered `(19.3)`

The generic window-discrepancy estimate is stated for a `C¹` receiver `G` on the annulus together
with a pointwise envelope for `G` and `G'`.  For the jet-modified receiver the natural `G` is the
half-damped profile `h ↦ e^{-h/2}·Jet_k(h)`, whose value at a prime log is exactly the jet prime
atom and whose product with `e^h` is the growing continuum profile.  Both envelopes come from the
`√u`-window transport bound and its Cauchy derivative companion, so the filtered `(19.3)` inherits
the full jet gain `u^{-(k+1)/2}`.
-/

open Complex Filter MeasureTheory Set

namespace RHTower

noncomputable section

/-- The damped jet profile as a function of the real height. -/
def xiMassJetDampedHeight (a : ℝ) (k : ℕ) (τ : ℂ) (h : ℝ) : ℂ :=
  ((Real.exp (-h / 2) : ℝ) : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ)

/-- Its height derivative. -/
def xiMassJetDampedHeightDeriv (a : ℝ) (k : ℕ) (τ : ℂ) (h : ℝ) : ℂ :=
  ((Real.exp (-h / 2) : ℝ) : ℂ) *
    (deriv (xiMassJetIterate a τ k) ((h : ℝ) : ℂ)
      - (1 / 2 : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ))

theorem hasDerivAt_xiMassJetDampedHeight {a : ℝ} (ha : 0 < a) {τ : ℂ} (k : ℕ) {h : ℝ}
    (hmem : ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ) :
    HasDerivAt (xiMassJetDampedHeight a k τ) (xiMassJetDampedHeightDeriv a k τ h) h := by
  have hdiff : DifferentiableAt ℂ (xiMassJetIterate a τ k) ((h : ℝ) : ℂ) :=
    (differentiableOn_xiMassJetIterate ha τ k).differentiableAt
      ((isOpen_xiMassHeightRegion τ).mem_nhds hmem)
  have hjet : HasDerivAt (fun s : ℝ => xiMassJetIterate a τ k ((s : ℝ) : ℂ))
      (deriv (xiMassJetIterate a τ k) ((h : ℝ) : ℂ)) h := hdiff.hasDerivAt.comp_ofReal
  have hexp : HasDerivAt (fun s : ℝ => ((Real.exp (-s / 2) : ℝ) : ℂ))
      (((-(1 / 2) * Real.exp (-h / 2) : ℝ) : ℂ)) h := by
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (-(1 / 2) * Real.exp (-h / 2)) h := by
      have hlin : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2)) h := by
        have h0 := ((hasDerivAt_id h).neg).div_const 2
        refine h0.congr_deriv ?_
        norm_num
      have hexp0 := hlin.exp
      refine hexp0.congr_deriv ?_
      ring
    exact hr.ofReal_comp
  have hmul := hexp.mul hjet
  refine hmul.congr_deriv ?_
  rw [xiMassJetDampedHeightDeriv]
  push_cast
  ring

theorem continuousOn_xiMassJetDampedHeightDeriv {a : ℝ} (ha : 0 < a) {τ : ℂ} (k : ℕ)
    {s : Set ℝ} (hs : ∀ h ∈ s, ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ) :
    ContinuousOn (xiMassJetDampedHeightDeriv a k τ) s := by
  have hana : AnalyticOnNhd ℂ (xiMassJetIterate a τ k) (xiMassHeightRegion τ) :=
    analyticOnNhd_xiMassJetIterate ha τ k
  have hopen := isOpen_xiMassHeightRegion τ
  intro h hh
  have hmem := hs h hh
  have hd1 : DifferentiableAt ℂ (deriv (xiMassJetIterate a τ k)) ((h : ℝ) : ℂ) :=
    (hana.deriv).differentiableOn.differentiableAt (hopen.mem_nhds hmem)
  have hd0 : DifferentiableAt ℂ (xiMassJetIterate a τ k) ((h : ℝ) : ℂ) :=
    (differentiableOn_xiMassJetIterate ha τ k).differentiableAt (hopen.mem_nhds hmem)
  have hofReal : ContinuousAt (fun s : ℝ => ((s : ℝ) : ℂ)) h := by fun_prop
  have hc1 : ContinuousAt (fun s : ℝ => deriv (xiMassJetIterate a τ k) ((s : ℝ) : ℂ)) h :=
    ContinuousAt.comp (g := deriv (xiMassJetIterate a τ k))
      (f := fun s : ℝ => ((s : ℝ) : ℂ)) (x := h) hd1.continuousAt hofReal
  have hc0 : ContinuousAt (fun s : ℝ => xiMassJetIterate a τ k ((s : ℝ) : ℂ)) h :=
    ContinuousAt.comp (g := xiMassJetIterate a τ k)
      (f := fun s : ℝ => ((s : ℝ) : ℂ)) (x := h) hd0.continuousAt hofReal
  have hce : ContinuousAt (fun s : ℝ => ((Real.exp (-s / 2) : ℝ) : ℂ)) h := by fun_prop
  have : ContinuousAt (xiMassJetDampedHeightDeriv a k τ) h := by
    unfold xiMassJetDampedHeightDeriv
    exact hce.mul (hc1.sub (continuousAt_const.mul hc0))
  exact this.continuousWithinAt

theorem lseriesTerm_vonMangoldt_prime_eq {p : ℕ} (hp : p.Prime) :
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) p
      = ((Real.log p : ℝ) : ℂ) * ((Real.exp (-(Real.log p) / 2) : ℝ) : ℂ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpne : p ≠ 0 := hp.pos.ne'
  rw [LSeries.term_of_ne_zero hpne, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hcpow : ((p : ℂ)) ^ (1 / 2 : ℂ) = (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hp0.le]
  have hinv : ((Real.exp (-(Real.log p) / 2) : ℝ) : ℂ) = ((((p : ℝ) ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ) := by
    congr 1
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_neg]
    congr 1
    ring
  have hpos : (0 : ℝ) < ((p : ℝ) ^ (1 / 2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  rw [hcpow, hinv, Complex.ofReal_inv]
  rw [div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
/-- **(19.3) for the jet-modified receiver.**  The prime-discrepancy annulus of the modified
receiver obeys the base bound with the jet gain `u^{-(k+1)/2}` inside the constant. -/
theorem exists_norm_primeLogWindow_jetQuadratureDefect_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (k : ℕ) :
    ∃ D u₀ : ℝ, 0 < D ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ H T CE cE : ℝ,
      0 ≤ CE → 0 ≤ cE → u < H → H ≤ T →
      |H - xiMassSpacelikeSharpSlope a * u| ≤ Real.sqrt u / 8 →
      |T - xiMassSpacelikeSharpSlope a * u| ≤ Real.sqrt u / 8 →
      (∀ h : ℝ, H ≤ h → h ≤ T →
        |xiMassThetaLogDiscrepancy h|
          ≤ CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10)))) →
      ‖(∑ p ∈ primeLogWindow H T,
            xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k p)
          - ∫ h in H..T, ((Real.exp (h / 2) : ℝ) : ℂ) *
              xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) k ((h : ℝ) : ℂ)‖
        ≤ (2 + 1 / (a - 1 / 2)) * (CE * (D / Real.sqrt u ^ (k + 1))
            * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
            * Real.exp (-(cE * H ^ ((1 : ℝ) / 10)))) := by
  obtain ⟨C, u₁, hC, hu₁, hwin⟩ := exists_norm_xiMassJetIterate_window_le' ha hsigma k
  obtain ⟨C', u₂, hC', hu₂, hder⟩ := exists_norm_deriv_xiMassJetIterate_window_le ha hsigma k
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  refine ⟨C + C', max (max u₁ u₂) 1, by positivity,
    le_trans (by simp) (le_max_right _ _), ?_⟩
  intro u hu H T CE cE hCE hcE hHu hHT hHw hTw hE
  have hu1' : u₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu2' : u₂ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hH0 : (0 : ℝ) ≤ H := le_trans hu0.le hHu.le
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set S : ℝ := Real.sqrt u ^ (k + 1) with hSdef
  have hS : (0 : ℝ) < S := by rw [hSdef]; exact pow_pos hr0 _
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  -- every height of the annulus lies in the `√u/8` window
  have hwindow : ∀ h : ℝ, H ≤ h → h ≤ T → |h - κ * u| ≤ Real.sqrt u / 8 := by
    intro h hHh hhT
    rw [abs_le] at hHw hTw ⊢
    exact ⟨by linarith [hHw.1], by linarith [hTw.2]⟩
  have hregion : ∀ h : ℝ, H ≤ h → h ≤ T → ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
    intro h hHh hhT
    rw [hτdef]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha (le_trans hu₁ hu1') ?_
    have hid : ((h : ℝ) : ℂ) - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)
        = (((h - xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs]
    have hw := hwindow h hHh hhT
    rw [hκdef] at hw
    linarith [hr0]
  -- the two pointwise envelopes
  have henvJ : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖
        ≤ C / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    intro h hHh hhT
    have hw := hwindow h hHh hhT
    have hbnd := hwin u hu1' (h - κ * u) (by linarith [hw, hr0])
    have heq : xiMassSpacelikeSharpSlope a * u + (h - κ * u) = h := by rw [hκdef]; ring
    rw [heq] at hbnd
    rw [hτdef, hSdef]
    exact hbnd
  have henvD : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖deriv (xiMassJetIterate a τ k) ((h : ℝ) : ℂ)‖
        ≤ C' / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    intro h hHh hhT
    have hw := hwindow h hHh hhT
    rw [hτdef, hSdef]
    exact hder u hu2' h hw
  have hmonoS : ∀ x y : ℝ, x ≤ y → x / S ≤ y / S := by
    intro x y hxy
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hxy (inv_pos.2 hS).le
  have henv : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖xiMassJetDampedHeight a k τ h‖
        ≤ (C + C') / S
          * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    intro h hHh hhT
    rw [xiMassJetDampedHeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-h / 2) * ‖xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖
        ≤ Real.exp (-h / 2)
            * (C / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
          mul_le_mul_of_nonneg_left (henvJ h hHh hhT) (Real.exp_pos _).le
      _ ≤ Real.exp (-h / 2)
            * ((C + C') / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hmonoS _ _ (by linarith)) (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = (C + C') / S
            * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by ring
  have henv' : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖xiMassJetDampedHeightDeriv a k τ h‖
        ≤ (C + C') / S
          * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    intro h hHh hhT
    rw [xiMassJetDampedHeightDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hsub : ‖deriv (xiMassJetIterate a τ k) ((h : ℝ) : ℂ)
        - (1 / 2 : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖
        ≤ (C' + C / 2) / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
      refine le_trans (norm_sub_le _ _) ?_
      have hhalf : ‖(1 / 2 : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖
          = (1 / 2) * ‖xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖ := by
        rw [norm_mul]
        norm_num
      rw [hhalf]
      have h1 := henvD h hHh hhT
      have h2 := henvJ h hHh hhT
      have hval : (C' + C / 2) / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
          = C' / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
            + (1 / 2) * (C / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
        field_simp
      rw [hval]
      linarith [h1, h2]
    calc Real.exp (-h / 2) * ‖deriv (xiMassJetIterate a τ k) ((h : ℝ) : ℂ)
            - (1 / 2 : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ)‖
        ≤ Real.exp (-h / 2)
            * ((C' + C / 2) / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
          mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
      _ ≤ Real.exp (-h / 2)
            * ((C + C') / S * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hmonoS _ _ (by linarith)) (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = (C + C') / S
            * (Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by ring
  -- Abel summation data
  have hG : ∀ x ∈ Set.Icc H T,
      HasDerivAt (xiMassJetDampedHeight a k τ) (xiMassJetDampedHeightDeriv a k τ x) x := by
    intro x hx
    exact hasDerivAt_xiMassJetDampedHeight ha0 k (hregion x hx.1 hx.2)
  have hG'int : IntervalIntegrable (xiMassJetDampedHeightDeriv a k τ) volume H T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hHT]
    exact continuousOn_xiMassJetDampedHeightDeriv ha0 k (fun h hh => hregion h hh.1 hh.2)
  have hgen := norm_primeLogWindow_generic_quadratureDefect_le
    (G := xiMassJetDampedHeight a k τ) (G' := xiMassJetDampedHeightDeriv a k τ)
    ha hu0 hHu hH0 hHT hCE hcE (by positivity : (0 : ℝ) ≤ (C + C') / S)
    hE henv henv' hG hG'int
  -- identify both sides with the jet objects
  have hsum : (∑ p ∈ primeLogWindow H T,
        ((Real.log p : ℝ) : ℂ) * xiMassJetDampedHeight a k τ (Real.log p))
      = ∑ p ∈ primeLogWindow H T, xiMassJetPrimeAtom a τ k p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := (mem_primeLogWindow.1 hp).2
    rw [xiMassJetPrimeAtom, lseriesTerm_vonMangoldt_prime_eq hpp, xiMassJetDampedHeight]
    ring
  have hint : (∫ h in H..T, xiMassJetDampedHeight a k τ h * ((Real.exp h : ℝ) : ℂ))
      = ∫ h in H..T, ((Real.exp (h / 2) : ℝ) : ℂ) * xiMassJetIterate a τ k ((h : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun h _ => ?_
    rw [xiMassJetDampedHeight]
    have hexp : Real.exp (-h / 2) * Real.exp h = Real.exp (h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    push_cast
    ring
  rw [hsum, hint] at hgen
  exact hgen

end

end RHTower
