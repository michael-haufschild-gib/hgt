import GaloisForLFunctions.ExclusionOfTheCriticalState.Energy.PolarChargeCoercivity
import GaloisForLFunctions.RHTower.WeilMarkovOnePoleHyperplane
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow

/-!
# The charge hyperplane has its own critical ratio

On half-line profiles Weil's bare form is the Markov form `M = arch − prime` plus the pole term
`2(C² − S²) = 2 A(G) B(G)`, `A = ∫ G e^{−u/2}`, `B = ∫ G e^{u/2}`; `B` is the growing polar
charge. On the charge hyperplane `B = 0` the pole term vanishes and the confined form is
`Q_R = M + a(R) W₈`.

* **The half-line one-pole-hyperplane law** (`riemannHypothesis_iff_halfLine_markov_nonneg`). RH
  iff `M ≥ 0` on every `C²` compactly supported test of the half line `u < 0` with `B = 0`.
  `M` and the hyperplane are translation invariant, so the criterion on the line moves to the
  half line.
* **Two-sided bound at the critical state.** With `a = a(W₀)` there is `γ > 0` such that
  `M ≥ −(a − γ) W₈` on the charge hyperplane of the energy domain
  (`criticalState_markov_ge_on_chargeHyperplane`), and `M < 0` at some smooth test of it
  (`criticalState_exists_markov_neg_on_chargeHyperplane`).
* **A second critical ratio.** There is `R₁ > W₀` such that for `0 < R ≤ R₁` the confined form is
  nonnegative on the charge hyperplane (`criticalState_chargeHyperplane_nonneg_beyond_threshold`):
  every plane of the energy domain contains a direction with `Q_R ≥ 0`, so `Q_R` has at most one
  negative square (`criticalState_no_negative_plane_beyond_threshold`). For large `R` the form is
  negative on the hyperplane (`criticalState_chargeHyperplane_eventually_negative`). The charge
  hyperplane has its own critical ratio `W₁ ∈ (W₀, ∞)`, and the second critical ratio of `Q_R` is
  at least `W₁`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-! ### Translation -/

/-- The Markov form reads only the autocorrelation, so it is translation invariant. -/
theorem markovEnergy_comp_add (f : ℝ → ℝ) (c : ℝ) :
    markovEnergy (fun u => ((f (u + c) : ℝ) : ℂ)) = markovEnergy (fun u => (f u : ℂ)) := by
  have e : (fun u => ((f (u + c) : ℝ) : ℂ)) =
      ArithmeticCastelnuovoSeveri.translate (-c) (fun u => (f u : ℂ)) := by
    funext u
    show ((f (u + c) : ℝ) : ℂ) = ((f (u - -c) : ℝ) : ℂ)
    rw [sub_neg_eq_add]
  have h : EF.weilTest (fun u => ((f (u + c) : ℝ) : ℂ)) (fun u => ((f (u + c) : ℝ) : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
    funext y
    rw [e, weilTest_translate, sub_self, sub_zero]
  unfold markovEnergy
  rw [h]

theorem growingPolarCharge_eq (G : ℝ → ℝ) :
    growingPolarCharge G = ∫ u, G u * Real.exp (u / 2) := by
  unfold growingPolarCharge
  congr 1
  funext u
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring]

/-- Translating left by `c` scales the growing charge by `e^{−c/2}`. -/
theorem growingPolarCharge_comp_add (f : ℝ → ℝ) (c : ℝ) :
    growingPolarCharge (fun u => f (u + c)) = Real.exp (-(c / 2)) * growingPolarCharge f := by
  unfold growingPolarCharge
  have h := integral_add_right_eq_self (μ := volume)
    (fun v => f v * Real.exp ((1 / 2 : ℝ) * (v - c))) c
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext v
  rw [show (1 / 2 : ℝ) * (v - c) = -(c / 2) + (1 / 2) * v by ring, Real.exp_add]
  ring

/-! ### The half-line one-pole-hyperplane law -/

/-- **RH is positivity of the Markov form on the half-line charge hyperplane.** -/
theorem riemannHypothesis_iff_halfLine_markov_nonneg :
    RiemannHypothesis ↔ ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G →
      (∀ u, 0 ≤ u → G u = 0) → growingPolarCharge G = 0 → 0 ≤ archForm G - primeSum G := by
  rw [riemannHypothesis_iff_forall_exp_half_moment_zero_markovEnergy_nonneg]
  constructor
  · intro h G hG hGc _ hz
    rw [← markovEnergy_ofReal_eq_archForm_sub_primeSum hG hGc]
    exact h G hG hGc (by rw [← growingPolarCharge_eq]; exact hz)
  · intro h F hF hFc h0
    obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_closedBall 0
    set c : ℝ := |R| + 1 with hc
    have hG : ContDiff ℝ 2 (fun u => F (u + c)) := hF.comp (contDiff_id.add contDiff_const)
    have hGc : HasCompactSupport (fun u => F (u + c)) :=
      hFc.comp_homeomorph (Homeomorph.addRight c)
    have hGs : ∀ u, 0 ≤ u → F (u + c) = 0 := by
      intro u hu
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have h1 := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
      have h2 := le_abs_self (u + c)
      have h3 := le_abs_self R
      linarith
    have hz : growingPolarCharge (fun u => F (u + c)) = 0 := by
      rw [growingPolarCharge_comp_add, growingPolarCharge_eq, h0, mul_zero]
    have := h _ hG hGc hGs hz
    rwa [← markovEnergy_ofReal_eq_archForm_sub_primeSum hG hGc, markovEnergy_comp_add] at this

/-! ### At the critical state -/

/-- A finite window threshold excludes RH. -/
theorem not_riemannHypothesis_of_windowThreshold_eq {W₀ : ℝ}
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) : ¬ RiemannHypothesis := by
  intro hRH
  have htop : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = ⊤ := by
    simp only [iInf_eq_top]
    exact riemannHypothesis_iff_windowThreshold_eq_top.mp hRH
  rw [ht] at htop
  exact EReal.coe_ne_top _ htop

/-- **The Markov form is bounded below on the charge hyperplane**: `M ≥ −(a(W₀) − γ) W₈`. -/
theorem criticalState_markov_ge_on_chargeHyperplane {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G → growingPolarCharge G = 0 →
      -(criticalAliasCoefficient W₀ - γ) * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        archForm G - primeSum G := by
  obtain ⟨γ, hγ, h⟩ := criticalState_charge_zero_coercivity hW ht hF
  refine ⟨γ, hγ, fun hG hz => ?_⟩
  have h1 := h hG hz
  rw [fullEnergy_of_growingPolarCharge_zero W₀ hG hz, halfLineExpMass_eq_full hG.support] at h1
  linarith

/-- **The Markov form is negative somewhere on the charge hyperplane** when the threshold is
finite. -/
theorem criticalState_exists_markov_neg_on_chargeHyperplane {W₀ : ℝ}
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧ HasCompactSupport G ∧ (∀ u, 0 ≤ u → G u = 0) ∧
      growingPolarCharge G = 0 ∧ archForm G - primeSum G < 0 := by
  have hn := not_riemannHypothesis_of_windowThreshold_eq ht
  rw [riemannHypothesis_iff_halfLine_markov_nonneg] at hn
  push Not at hn
  exact hn

/-- **Beyond the threshold the charge hyperplane stays nonnegative**: some `R₁ > W₀` keeps
`Q_R ≥ 0` on the charge hyperplane for every `0 < R ≤ R₁`. -/
theorem criticalState_chargeHyperplane_nonneg_beyond_threshold {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ R₁ : ℝ, W₀ < R₁ ∧ ∀ R : ℝ, 0 < R → R ≤ R₁ → ∀ {G : ℝ → ℝ},
      CriticalHalfLineEnergyDomain G → growingPolarCharge G = 0 →
        0 ≤ criticalHalfLineFullEnergy R G := by
  obtain ⟨γ, hγ, h⟩ := criticalState_charge_zero_coercivity hW ht hF
  set a := criticalAliasCoefficient 1 with ha_def
  have ha : 0 < a := criticalAliasCoefficient_positive one_pos
  have haW : 0 < a / W₀ := div_pos ha hW
  set δ := min γ (a / W₀) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδγ : δ < γ := by
    have := min_le_left γ (a / W₀)
    rw [hδ_def]
    linarith
  have hδa : δ < a / W₀ := by
    have := min_le_right γ (a / W₀)
    rw [hδ_def]
    linarith
  have hden : 0 < a / W₀ - δ := by linarith
  refine ⟨a / (a / W₀ - δ), ?_, fun R hR hRR G hG hz => ?_⟩
  · rw [lt_div_iff₀ hden, mul_sub, mul_div_cancel₀ _ hW.ne']
    nlinarith
  · have h1 := h hG hz
    have hc := criticalHalfLineFullEnergy_change_ratio R W₀ hG
    rw [criticalAliasCoefficient_eq_div R, criticalAliasCoefficient_eq_div W₀] at hc
    have hRa : a / W₀ - δ ≤ a / R := by
      rw [le_div_iff₀ hR]
      rw [le_div_iff₀ hden] at hRR
      linarith
    have hM : 0 ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
      integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    rw [hc]
    nlinarith

/-- **At most one negative square below the second ratio.** For `0 < R ≤ R₁` every plane of the
energy domain contains a nonzero direction with `Q_R ≥ 0`. -/
theorem criticalState_no_negative_plane_beyond_threshold {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ R₁ : ℝ, W₀ < R₁ ∧ ∀ R : ℝ, 0 < R → R ≤ R₁ → ∀ {G₁ G₂ : ℝ → ℝ},
      CriticalHalfLineEnergyDomain G₁ → CriticalHalfLineEnergyDomain G₂ →
      ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧
        0 ≤ criticalHalfLineFullEnergy R (fun u => s * G₁ u + t * G₂ u) := by
  obtain ⟨R₁, hR₁, h⟩ := criticalState_chargeHyperplane_nonneg_beyond_threshold hW ht hF
  refine ⟨R₁, hR₁, fun R hR hRR G₁ G₂ h₁ h₂ => ?_⟩
  have hcomb : ∀ s t : ℝ, CriticalHalfLineEnergyDomain (fun u => s * G₁ u + t * G₂ u) :=
    fun s t => (h₁.const_mul s).add_const_mul h₂ t
  have hch : ∀ s t : ℝ, growingPolarCharge (fun u => s * G₁ u + t * G₂ u) =
      s * growingPolarCharge G₁ + t * growingPolarCharge G₂ := by
    intro s t
    have i1 := integrable_halfLineLaplace_of_domain h₁ (s := 1 / 2) (by norm_num)
    have i2 := integrable_halfLineLaplace_of_domain h₂ (s := 1 / 2) (by norm_num)
    unfold growingPolarCharge
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (i1.const_mul s) (i2.const_mul t), integral_const_mul, integral_const_mul]
  by_cases h0 : growingPolarCharge G₁ = 0 ∧ growingPolarCharge G₂ = 0
  · exact ⟨1, 0, by simp, h R hR hRR (hcomb 1 0) (by rw [hch, h0.1, h0.2]; ring)⟩
  · refine ⟨growingPolarCharge G₂, -growingPolarCharge G₁, fun he => h0 ?_,
      h R hR hRR (hcomb _ _) (by rw [hch]; ring)⟩
    simp only [Prod.mk.injEq, neg_eq_zero] at he
    exact ⟨he.2, he.1⟩

/-- **The charge hyperplane eventually turns negative**: a smooth charge-free test with negative
Markov energy has `Q_R < 0` for all large ratios. -/
theorem criticalState_chargeHyperplane_eventually_negative {W₀ : ℝ}
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ growingPolarCharge G = 0 ∧
      ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ R : ℝ, R₂ ≤ R → criticalHalfLineFullEnergy R G < 0 := by
  obtain ⟨G, hG, hGc, hGs, hz, hneg⟩ := criticalState_exists_markov_neg_on_chargeHyperplane ht
  have hd := criticalHalfLineEnergyDomain_of_compact_negative hG hGc hGs
  set M := ∫ u, G u ^ 2 * Real.exp (-(8 * u)) with hM_def
  have hM : 0 ≤ M := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  set a := criticalAliasCoefficient 1 with ha_def
  have ha : 0 < a := criticalAliasCoefficient_positive one_pos
  set m := archForm G - primeSum G with hm_def
  have hm : 0 < -m := by linarith
  have hR₂ : 0 < (a * M + 1) / -m := by positivity
  refine ⟨G, hd, hz, (a * M + 1) / -m, hR₂, fun R hR => ?_⟩
  have hRpos : 0 < R := hR₂.trans_le hR
  rw [fullEnergy_of_growingPolarCharge_zero R hd hz, halfLineExpMass_eq_full hGs,
    criticalAliasCoefficient_eq_div R]
  have hkey : a * M < -m * R := by
    rw [div_le_iff₀ hm] at hR
    linarith
  have hlt : a / R * M < -m := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hRpos]
    linarith
  linarith

/-- **The confined half-line one-bound-state law.** Either RH, or the critical state exists at
`W₀` and the charge hyperplane has a critical ratio strictly between `W₀` and `∞`: nonnegative up
to some `R₁ > W₀` (so `Q_R` has at most one negative square there), negative at a fixed test for
all large `R`. -/
theorem riemannHypothesis_or_chargeHyperplane_critical_ratio :
    RiemannHypothesis ∨ ∃ (W₀ R₁ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧ W₀ < R₁ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      (∀ R : ℝ, 0 < R → R ≤ R₁ → ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        growingPolarCharge G = 0 → 0 ≤ criticalHalfLineFullEnergy R G) ∧
      ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ growingPolarCharge G = 0 ∧
        ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ R : ℝ, R₂ ≤ R → criticalHalfLineFullEnergy R G < 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · obtain ⟨R₁, hR₁, h₁⟩ := criticalState_chargeHyperplane_nonneg_beyond_threshold hW ht hF
    exact Or.inr ⟨W₀, R₁, F, hW, hR₁, ht, hF, fun R hR hRR G hG hz => h₁ R hR hRR hG hz,
      criticalState_chargeHyperplane_eventually_negative ht⟩

#print axioms riemannHypothesis_iff_halfLine_markov_nonneg
#print axioms riemannHypothesis_or_chargeHyperplane_critical_ratio
#print axioms criticalState_no_negative_plane_beyond_threshold

end GaloisForLFunctions.ExclusionOfTheCriticalState
