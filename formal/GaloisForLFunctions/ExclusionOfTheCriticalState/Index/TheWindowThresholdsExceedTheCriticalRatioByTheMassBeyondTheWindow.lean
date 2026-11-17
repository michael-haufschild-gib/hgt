import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GalerkinProbeStatesConvergeToTheCriticalState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarIsCoerciveAndPrimeBlind
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay

/-!
# The window thresholds exceed the critical ratio by the mass of the state beyond the window

\`W₀ = inf_A R₁(A)\`, where the threshold \`R₁(A)\` of the window \`[−A, 0]\` (\`windowThreshold\`) is the
infimum of the critical multiples \`R*(H) = 7J(1) M₈(H)/(a_φ (−Q(H)))\` of its tests with \`Q(H) < 0\`.
At its critical multiple a negative window test is a null direction of the confined form,
\`Q_{R*(H)}(H) = 0\` (\`fullEnergy_testCriticalMultiple_eq_zero\`), so \`Q_{W₀}(H) = (a(W₀) − a(R*)) W₈(H)\`.
The second critical ratio \`R₂ > W₀\` is a spectral gap at the state
(\`exists_sign_exponentialMass_sub_le\`): normalized to \`W₈(H) = W₈(F)\`, the test is within
\`O(R*(H) − W₀)\` of \`±F\` in \`W₈\` and in \`Q_{W₀}\` (\`criticalState_window_stability\`).

* **The state is the limit of the window states** (\`exists_windowTests_tendsto_criticalRatio\`,
  \`criticalState_tendsto_of_windowTests\`): negative window tests with critical multiples tending to
  \`W₀\` exist, and every such sequence converges, after normalization and a choice of signs, to the
  state in \`W₈\` and in \`Q_{W₀}\`.
* **No window attains the critical ratio** (\`criticalState_windowThreshold_ge\`,
  \`criticalState_lt_windowThreshold\`). A window test vanishes left of \`−A\`, so its distance to \`±F\`
  is at least the confinement mass of the state there:
  \`R₁(A) ≥ W₀ + c ∫_{u<−A} F² e^{−8u}\` with \`c > 0\` independent of \`A\`. The state has mass on
  every ray, so \`R₁(A) > W₀\` for every \`A\`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis

local notation "W8" => criticalHalfLineExponentialPair

/-! ### A negative window test at its critical multiple -/

/-- A window test vanishes on \`[0, ∞)\`. -/
theorem isWindowTest_eq_zero_of_nonneg {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) {u : ℝ}
    (hu : 0 ≤ u) : H u = 0 := by
  rcases hu.lt_or_eq with h | rfl
  · exact hH.vanish u fun hm => absurd hm.2 (not_le.mpr h)
  · have h1 : Tendsto H (𝓝[>] 0) (𝓝 (H 0)) :=
      hH.contDiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr'
      (eventually_nhdsWithin_of_forall fun v (hv : 0 < v) =>
        (hH.vanish v fun hm => absurd hm.2 (not_le.mpr hv)).symm)
    exact tendsto_nhds_unique h1 h2

theorem exponentialMass_eight_eq (H : ℝ → ℝ) :
    exponentialMass 8 H = ∫ u, H u ^ 2 * Real.exp (-(8 * u)) :=
  integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)

/-- A window test with \`Q(H) < 0\` has positive confinement mass. -/
theorem exponentialMass_pos_of_weilQuad_neg {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hQ : weilQuad H < 0) : 0 < exponentialMass 8 H := by
  rcases (exponentialMass_nonneg 8 H).lt_or_eq with h | h
  · exact h
  · have := weilQuad_ge_neg_exponentialMass hH (by norm_num : (1 : ℝ) < 8)
    rw [← h, mul_zero, neg_zero] at this
    linarith

/-- At the critical multiple the confinement coefficient is \`−Q(H)/M₈(H)\`. -/
theorem criticalAliasCoefficient_testCriticalMultiple {H : ℝ → ℝ} (hQ : weilQuad H < 0)
    (hM : 0 < exponentialMass 8 H) :
    criticalAliasCoefficient (testCriticalMultiple H) = -weilQuad H / exponentialMass 8 H := by
  have hκ := splineAtom_pos
  unfold splineAtom at hκ
  have hP : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := fun h => by
    rw [h, div_zero] at hκ; exact lt_irrefl 0 hκ
  have hS : (∫ u, tiltedUnitSpline u) ≠ 0 := fun h => by
    rw [h] at hκ; simp at hκ
  have hJ := tiltedJordanOne_pos.ne'
  have hq := hQ.ne
  have hm := hM.ne'
  unfold criticalAliasCoefficient testCriticalMultiple splineAtom
  field_simp

/-- **A negative window test is a null direction at its critical multiple**:
\`Q_{R*(H)}(H) = 0\`. -/
theorem fullEnergy_testCriticalMultiple_eq_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hQ : weilQuad H < 0) : criticalHalfLineFullEnergy (testCriticalMultiple H) H = 0 := by
  have hM := exponentialMass_pos_of_weilQuad_neg hH hQ
  rw [fullEnergy_eq_weilQuad_add hH.contDiff hH.hasCompactSupport
      (fun u hu => isWindowTest_eq_zero_of_nonneg hH hu),
    criticalAliasCoefficient_testCriticalMultiple hQ hM, ← exponentialMass_eight_eq,
    div_mul_cancel₀ _ hM.ne']
  ring

/-- The critical multiple of a negative window test is at least \`W₀\`. -/
theorem le_testCriticalMultiple {W₀ : ℝ}
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {A : ℝ} (hA : 0 ≤ A)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) (hQ : weilQuad H < 0) : W₀ ≤ testCriticalMultiple H := by
  have h1 : windowThreshold A ≤ (testCriticalMultiple H : EReal) :=
    iInf_le_of_le H (iInf_le_of_le hH (iInf_le _ hQ))
  have h2 : (W₀ : EReal) ≤ windowThreshold A := by
    rw [← ht]; exact iInf_le_of_le A (iInf_le _ hA)
  exact EReal.coe_le_coe_iff.mp (h2.trans h1)

/-! ### Stability -/

/-- **Stability of the window problem at the state.** There is \`C > 0\` such that every window
test \`H\` with \`Q(H) < 0\`, normalized to \`W₈(F)\`, is within \`C (R*(H) − W₀)\` of \`F\` or of \`−F\`,
in \`W₈\` and in \`Q_{W₀}\`. -/
theorem criticalState_window_stability {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H → weilQuad H < 0 →
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        W8 (fun u => Real.sqrt (W8 F F / W8 H H) * H u - s * F u)
            (fun u => Real.sqrt (W8 F F / W8 H H) * H u - s * F u) ≤
          C * (testCriticalMultiple H - W₀) ∧
        criticalHalfLineFullEnergy W₀ (fun u => Real.sqrt (W8 F F / W8 H H) * H u - s * F u) ≤
          C * (testCriticalMultiple H - W₀) := by
  obtain ⟨R₂, hR₂, hnot, -, -⟩ := criticalState_secondCriticalState hW ht hF
  have hnot₂ : ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R₂ G₁ G₂ := hnot R₂ (hW.trans hR₂) le_rfl
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hm : 0 < W8 F F := exponentialPair_self_pos hnull.1 hnull.2.1
  have hδ : 0 < criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂ := by
    have := criticalAliasCoefficient_lt hW hR₂; linarith
  have ha₁ : 0 < criticalAliasCoefficient 1 := criticalAliasCoefficient_positive one_pos
  set δ := criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂
  set K : ℝ := criticalAliasCoefficient 1 * W8 F F / W₀ ^ 2
  have hK : 0 < K := by positivity
  refine ⟨2 * K / δ + K, by positivity, fun A hA H hH hQ => ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_window hH
  have hM := exponentialMass_pos_of_weilQuad_neg hH hQ
  have hMH : 0 < W8 H H := by
    rw [criticalHalfLineExponentialPair_self, ← exponentialMass_eight_eq]; exact hM
  set R := testCriticalMultiple H
  have hRW : W₀ ≤ R := le_testCriticalMultiple ht hA hH hQ
  have hRpos : 0 < R := hW.trans_le hRW
  set c := Real.sqrt (W8 F F / W8 H H)
  have hc2 : c ^ 2 = W8 F F / W8 H H := Real.sq_sqrt (div_nonneg hm.le hMH.le)
  have hG : CriticalHalfLineEnergyDomain (fun u => c * H u) := hd.const_mul c
  have hGm : W8 (fun u => c * H u) (fun u => c * H u) = W8 F F := by
    have e : W8 (fun u => c * H u) (fun u => c * H u) = c ^ 2 * W8 H H := by
      rw [criticalHalfLineExponentialPair_self, criticalHalfLineExponentialPair_self]
      simp_rw [mul_pow, mul_assoc]; exact integral_const_mul _ _
    rw [e, hc2, div_mul_cancel₀ _ hMH.ne']
  -- the energy at the critical ratio is the confinement defect of the critical multiple
  have hQG : criticalHalfLineFullEnergy W₀ (fun u => c * H u) =
      (criticalAliasCoefficient W₀ - criticalAliasCoefficient R) * W8 F F := by
    rw [criticalHalfLineFullEnergy_const_mul, fullEnergy_change_ratio W₀ R hd,
      fullEnergy_testCriticalMultiple_eq_zero hH hQ, zero_add, hc2]
    field_simp
  have hda : criticalAliasCoefficient W₀ - criticalAliasCoefficient R ≤
      criticalAliasCoefficient 1 * (R - W₀) / W₀ ^ 2 := by
    have e : criticalAliasCoefficient W₀ - criticalAliasCoefficient R =
        criticalAliasCoefficient 1 * (R - W₀) / (W₀ * R) := by
      rw [criticalAliasCoefficient_eq_div W₀, criticalAliasCoefficient_eq_div R]
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (mul_nonneg ha₁.le (by linarith)) (by positivity)
      (by nlinarith)
  have hQb : criticalHalfLineFullEnergy W₀ (fun u => c * H u) ≤ K * (R - W₀) := by
    rw [hQG]
    calc (criticalAliasCoefficient W₀ - criticalAliasCoefficient R) * W8 F F
        ≤ criticalAliasCoefficient 1 * (R - W₀) / W₀ ^ 2 * W8 F F :=
          mul_le_mul_of_nonneg_right hda hm.le
      _ = K * (R - W₀) := by simp only [K]; ring
  obtain ⟨s, hs, hdist⟩ := exists_sign_exponentialMass_sub_le hW ht hF hR₂ hnot₂ hG hGm
  have hRW' : 0 ≤ R - W₀ := by linarith
  refine ⟨s, hs, ?_, ?_⟩
  · refine hdist.trans ?_
    rw [div_le_iff₀ hδ]
    have h2 : 2 * (K * (R - W₀)) = 2 * K / δ * (R - W₀) * δ := by field_simp
    nlinarith [mul_nonneg hK.le hRW', mul_nonneg hδ.le hRW']
  · have e : (fun u => c * H u - s * F u) = fun u => c * H u + (-s) * F u := by
      funext u; ring
    rw [e, fullEnergy_add_const_mul_criticalState hW ht hF hG]
    refine hQb.trans ?_
    have : 0 ≤ 2 * K / δ * (R - W₀) := by positivity
    nlinarith

/-! ### The state is the limit of the window states -/

/-- **Window tests approach the critical ratio**: there are negative window tests whose critical
multiples tend to \`W₀\`. -/
theorem exists_windowTests_tendsto_criticalRatio {W₀ : ℝ}
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ∃ (A : ℕ → ℝ) (H : ℕ → ℝ → ℝ), (∀ k, 0 ≤ A k) ∧ (∀ k, IsWindowTest (A k) (H k)) ∧
      (∀ k, weilQuad (H k) < 0) ∧
      Tendsto (fun k => testCriticalMultiple (H k)) atTop (𝓝 W₀) := by
  have hex : ∀ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∃ H : ℝ → ℝ, IsWindowTest A H ∧ weilQuad H < 0 ∧
      testCriticalMultiple H < W₀ + 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) <
        ((W₀ + 1 / ((k : ℝ) + 1) : ℝ) : EReal) := by
      rw [ht, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨A, hA⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hA0, hA⟩ := iInf_lt_iff.mp hA
    obtain ⟨H, hH⟩ := iInf_lt_iff.mp hA
    obtain ⟨hHw, hH⟩ := iInf_lt_iff.mp hH
    obtain ⟨hQ, hH⟩ := iInf_lt_iff.mp hH
    exact ⟨A, hA0, H, hHw, hQ, EReal.coe_lt_coe_iff.mp hH⟩
  choose A hA H hH hQ hR using hex
  refine ⟨A, H, hA, hH, hQ, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun k => le_testCriticalMultiple ht (hA k) (hH k) (hQ k)) (fun k => (hR k).le)
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add W₀

/-- **E-M19: the state is the limit of the window states.** If negative window tests \`H_k\` have
critical multiples tending to \`W₀\`, then, normalized to \`W₈(F)\` and with suitable signs \`s_k = ±1\`,
they converge to the critical state in \`W₈\` and in the critical energy \`Q_{W₀}\`. -/
theorem criticalState_tendsto_of_windowTests {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {A : ℕ → ℝ} {H : ℕ → ℝ → ℝ} (hA : ∀ k, 0 ≤ A k)
    (hH : ∀ k, IsWindowTest (A k) (H k)) (hQ : ∀ k, weilQuad (H k) < 0)
    (hR : Tendsto (fun k => testCriticalMultiple (H k)) atTop (𝓝 W₀)) :
    ∃ s : ℕ → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧
      Tendsto (fun k => W8 (fun u => Real.sqrt (W8 F F / W8 (H k) (H k)) * H k u - s k * F u)
        (fun u => Real.sqrt (W8 F F / W8 (H k) (H k)) * H k u - s k * F u)) atTop (𝓝 0) ∧
      Tendsto (fun k => criticalHalfLineFullEnergy W₀
        (fun u => Real.sqrt (W8 F F / W8 (H k) (H k)) * H k u - s k * F u)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hstab⟩ := criticalState_window_stability hW ht hF
  choose s hs hW8 hQW using fun k => hstab (A k) (hA k) (H k) (hH k) (hQ k)
  have hlim : Tendsto (fun k => C * (testCriticalMultiple (H k) - W₀)) atTop (𝓝 0) := by
    simpa using (hR.sub_const W₀).const_mul C
  have hD : ∀ k, CriticalHalfLineEnergyDomain
      (fun u => Real.sqrt (W8 F F / W8 (H k) (H k)) * H k u - s k * F u) := fun k => by
    have h := ((criticalHalfLineEnergyDomain_of_window (hH k)).const_mul
      (Real.sqrt (W8 F F / W8 (H k) (H k)))).add_const_mul
        (criticalHalfLineEnergyDomain_of_groundState hF) (-s k)
    convert h using 2 with u
    ring
  refine ⟨s, hs, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => by
        rw [criticalHalfLineExponentialPair_self]
        exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hW8
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW ht (hD k)) hQW

/-! ### No window attains the critical ratio -/

/-- The state has confinement mass on every ray: \`∫_{u<−A} F² e^{−8u} > 0\`. -/
theorem criticalState_tailMass_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (A : ℝ) :
    0 < ∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u)) := by
  have hint : IntegrableOn (fun u => F u ^ 2 * Real.exp (-(8 * u))) (Iio (-A)) :=
    (criticalHalfLineEnergyDomain_of_groundState hF).exponential.integrableOn
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Iio (-A))] fun u => F u ^ 2 * Real.exp (-(8 * u)) :=
    ae_of_all _ fun u => by simp only [Pi.zero_apply]; positivity
  rcases (setIntegral_nonneg measurableSet_Iio fun u _ => by positivity :
      (0 : ℝ) ≤ ∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 h.symm
    refine (criticalState_changes_sign_on_every_ray hW ht hF A).1 ?_
    filter_upwards [hz] with u hu
    have h0 : F u ^ 2 = 0 := by
      simp only [Pi.zero_apply] at hu
      rcases mul_eq_zero.1 hu with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    rw [pow_eq_zero_iff two_ne_zero |>.1 h0]

/-- **The window thresholds exceed \`W₀\` by the confinement mass beyond the window.** There is
\`c > 0\` with \`R₁(A) ≥ W₀ + c ∫_{u<−A} F² e^{−8u}\` for every \`A ≥ 0\`. -/
theorem criticalState_windowThreshold_ge {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 ≤ A →
      ((W₀ + c * ∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u)) : ℝ) : EReal) ≤
        windowThreshold A := by
  obtain ⟨C, hC, hstab⟩ := criticalState_window_stability hW ht hF
  refine ⟨C⁻¹, inv_pos.mpr hC, fun A hA => ?_⟩
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => EReal.coe_le_coe_iff.mpr ?_
  obtain ⟨s, hs, hW8, -⟩ := hstab A hA H hH hQ
  set c := Real.sqrt (W8 F F / W8 H H)
  have hX : CriticalHalfLineEnergyDomain (fun u => c * H u - s * F u) := by
    have h := ((criticalHalfLineEnergyDomain_of_window hH).const_mul c).add_const_mul
      (criticalHalfLineEnergyDomain_of_groundState hF) (-s)
    convert h using 2 with u
    ring
  have htail : (∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u))) ≤
      W8 (fun u => c * H u - s * F u) (fun u => c * H u - s * F u) := by
    rw [criticalHalfLineExponentialPair_self]
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have heq : (∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u))) =
        ∫ u in Iio (-A), (c * H u - s * F u) ^ 2 * Real.exp (-(8 * u)) := by
      refine setIntegral_congr_fun measurableSet_Iio fun u hu => ?_
      have hHu : H u = 0 := hH.vanish u fun hm => absurd hm.1 (not_le.mpr hu)
      simp only [hHu, mul_zero, zero_sub, neg_sq, mul_pow, hs2, one_mul]
    rw [heq]
    exact setIntegral_le_integral hX.exponential
      (ae_of_all _ fun u => by simp only [Pi.zero_apply]; positivity)
  have h := htail.trans hW8
  have h' : C⁻¹ * ∫ u in Iio (-A), F u ^ 2 * Real.exp (-(8 * u)) ≤ testCriticalMultiple H - W₀ := by
    rw [inv_mul_le_iff₀ hC]; exact h
  linarith

/-- **No window attains the critical ratio**: \`W₀ < R₁(A)\` for every \`A ≥ 0\`. -/
theorem criticalState_lt_windowThreshold {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {A : ℝ} (hA : 0 ≤ A) :
    (W₀ : EReal) < windowThreshold A := by
  obtain ⟨c, hc, h⟩ := criticalState_windowThreshold_ge hW ht hF
  have hτ := criticalState_tailMass_pos hW ht hF A
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ (mul_pos hc hτ))) (h A hA)

end GaloisForLFunctions.ExclusionOfTheCriticalState

#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.criticalState_window_stability
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.criticalState_tendsto_of_windowTests
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.criticalState_windowThreshold_ge
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.criticalState_lt_windowThreshold
