import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.NonpositiveDirectionsHaveNormalizedChargedProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ChargedWeilProfilesHaveStrongLimits
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentExcludesChargedLimitProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarModeTopWindowLipschitzTransfer
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleCorrectorRetainsItsSignedWindowBenefit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarPaymentThresholdGrowsExponentially
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PrimitiveCriticalThresholdEqualsWindowThreshold

/-!
# The whole-space critical threshold equals polar payment

A nonpositive sequence retains a scalar pole coordinate and a strongly compact
collar profile. The exact signed polar limit and the critical Gamma lower bound
contradict the strict reserve supplied by payment at a larger ratio. Compact-band
lifting and suprema give the threshold identity and its onset bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Finset RHTower Zeta23
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri WindowTowerOfSpecZ
  CohomologyOfWindowsOfSpecZ WindowVisibilityLaw

/-- A jointly normalized critical collar sequence cannot have nonpositive charged energy below
polar payment. Strong compactness preserves the pole coordinate and the exact signed source. -/
theorem no_charged_atomic_sequence_below_polarPayment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hpay : ∀ A : ℝ, 0 ≤ A → PolarPaymentAt S A)
    {N_seq : ℕ → ℕ} (hstrict : StrictMono N_seq) (hN : ∀ k, 1 ≤ N_seq k)
    (z : (k : ℕ) → EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k))) (β : ℕ → ℝ)
    (hz0 : ∀ k n, n ≤ N_seq k / linearDefectCutoff (c (N_seq k)) → primeHorizonExtension (z k) n = 0)
    {K_W K_S K_Q : ℝ} (hKW : 0 ≤ K_W) (hKS : 0 < K_S)
    (hzS : ∀ k, topCollarSeventhMass (N_seq k / linearDefectCutoff (c (N_seq k)))
      (N_seq k) (primeHorizonExtension (z k)) ≤ K_S)
    (hnorm : ∀ k, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
      (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k) u ^ 2) + β k ^ 2 = 1)
    (hW : ∀ k, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline
      (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k) u ^ 2 * Real.exp (-(8 * u))) ≤ K_W)
    (hsupp : ∀ (k : ℕ) (u : ℝ), 1 / ((k : ℝ) + 1) < u →
      normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension (z k))
        (c (N_seq k)) (N_seq k) u = 0)
    (hQ : ∀ k, weilQuad (normalizedCentredAtomicTest tiltedUnitSpline
      (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k)) ≤ K_Q)
    (hsharp : ∀ k, weilQuad (normalizedCentredAtomicTest tiltedUnitSpline
      (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k)) +
      (∫ u, tiltedUnitSpline u ^ 2) *
        ((Real.log (N_seq k) / c (N_seq k)) * completeWeilEnergy tiltedUnitSpline (c (N_seq k))
          (N_seq k) (normalizedRamanujanHorizonVector 1 (N_seq k)) * β k ^ 2) +
      2 * (∫ u, tiltedUnitSpline u ^ 2) * β k *
        (Real.sqrt (Real.log (N_seq k)) / c (N_seq k) *
          ⟪conductorResidualVector (c (N_seq k)) 1 (N_seq k), z k⟫) ≤ 1 / ((k : ℝ) + 1)) : False := by
  let U := fun k => normalizedCentredAtomicTest tiltedUnitSpline
    (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k)
  have hUd : ∀ k, ContDiff ℝ 2 (U k) := fun k =>
    contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline
      (zero_lt_one.trans_le (hc (N_seq k))) (hN k) _
  have hUc : ∀ k, HasCompactSupport (U k) := fun k =>
    hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero
      (zero_lt_one.trans_le (hc (N_seq k))) (hN k) _
  obtain ⟨F, β₀, s, hs, hFm, hFi, hF2, hFnorm, hF8, hF8bound, hFzero, hL2, hL1, hβ⟩ :=
    exists_strong_charged_limit_of_bounded_weilQuad hUd hUc hnorm hKW hW hsupp hQ
  let J := N_seq ∘ s
  have hJ : StrictMono J := hstrict.comp hs
  have hmass : ∀ j, (∫ u, U (s j) u ^ 2) ≤ 1 := fun j => by
    linarith only [hnorm (s j), sq_nonneg (β (s j))]
  have hcritJ : Tendsto (fun j => c (J j) ^ 8 / Real.log (J j)) atTop (𝓝 R) :=
    hcrit.comp hJ.tendsto_atTop
  have hgamma : ∀ T : ℝ, Real.exp ArithmeticPositivityTheory.factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ K_Q := by
    intro T hT
    by_contra hh
    have hev := eventually_lt_weilQuad_of_subsequence_L1_limit hJ
      (fun j => hc (J j)) hR hcritJ (fun j => primeHorizonExtension (z (s j)))
      hmass hKW (fun j => hW (s j)) hFi hL1 hT (lt_of_not_ge hh)
    obtain ⟨j, hj⟩ := hev.exists
    exact not_lt_of_ge (hQ (s j)) hj
  have hpolar := tendsto_polar_residual_pairing_of_strong_limit hc hR hcrit hJ
    (fun j => hN (s j)) (fun j => z (s j)) (fun j => hz0 (s j)) hKS
    (fun j => hzS (s j)) hFm hFi hF2 hF8 hFzero hgamma hL2
  have hself := (tendsto_critical_pole_window_cost hc hR hcrit).comp hJ.tendsto_atTop
  let I₁ := ∫ u, tiltedUnitSpline u
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  let q := I₂ * criticalPoleWindowCost R * β₀ ^ 2 +
    2 * I₁ * β₀ * (∫ u, F u * polarSourceProfile u)
  let Q := fun j => I₂ *
      ((Real.log (J j) / c (J j)) * completeWeilEnergy tiltedUnitSpline (c (J j))
        (J j) (normalizedRamanujanHorizonVector 1 (J j)) * β (s j) ^ 2) +
    2 * I₂ * β (s j) * (Real.sqrt (Real.log (J j)) / c (J j) *
      ⟪conductorResidualVector (c (J j)) 1 (J j), z (s j)⟫)
  have hQlim : Tendsto Q atTop (𝓝 q) := by
    have ht := ((hself.mul (hβ.pow 2)).const_mul I₂).add
      ((hβ.mul hpolar).const_mul (2 * I₂))
    convert ht using 1
    · funext j
      dsimp only [Q, completeWeilEnergy, Function.comp_def]
      ring
    · congr 1
      dsimp only [q, I₁, I₂]
      field_simp [integral_tiltedUnitSpline_sq_pos.ne']
  have heps : Tendsto (fun j => 1 / ((s j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hs.tendsto_atTop
  have hcharged : ∀ T : ℝ, Real.exp ArithmeticPositivityTheory.factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u))) + q ≤ 0 := by
    intro T hT
    let G := truncatedWeilForm F T + criticalAliasCoefficient R *
      (∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u)))
    by_contra hh
    have hpos : 0 < G + q := lt_of_not_ge hh
    let b := (G - q) / 2
    have hb : b < G := by dsimp only [b]; linarith only [hpos]
    have hqb : -q < b := by dsimp only [b]; linarith only [hpos]
    have hlo := eventually_lt_weilQuad_of_subsequence_L1_limit hJ
      (fun j => hc (J j)) hR hcritJ (fun j => primeHorizonExtension (z (s j)))
      hmass hKW (fun j => hW (s j)) hFi hL1 hT hb
    have hupper := heps.sub hQlim
    rw [zero_sub] at hupper
    obtain ⟨j, hjlo, hjup⟩ := (hlo.and (hupper.eventually (gt_mem_nhds hqb))).exists
    have hj := hsharp (s j)
    rw [add_assoc] at hj
    change weilQuad (U (s j)) + Q j ≤ 1 / ((s j : ℝ) + 1) at hj
    change b < weilQuad (U (s j)) at hjlo
    linarith only [hjlo, hjup, hj]
  exact no_charged_limit_profile_below_polarPayment hR hRS hpay hFm hFi hF2
    (by linarith only [hFnorm, sq_nonneg β₀]) hF8 hFzero
    (by rw [hFnorm]; norm_num) (fun T hT => by
      have hh := hcharged T hT
      dsimp only [q, I₁, I₂] at hh
      linarith only [hh])

#print axioms no_charged_atomic_sequence_below_polarPayment

/-- Every critical curve strictly below a ratio paying all polar windows is eventually positive
on the entire horizon space. -/
theorem eventually_wholeSpace_positive_of_polarPayment
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hpay : ∀ A : ℝ, 0 ≤ A → PolarPaymentAt S A) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
      0 < completeWeilEnergy tiltedUnitSpline (c N) N x := by
  by_contra hnot
  obtain ⟨K_W, K_S, K_Q, hKW, hKS, _, hbridge⟩ :=
    exists_normalized_charged_collar_bridge hc hR hcrit
  let P := fun (ε : ℝ) (N : ℕ) (β : ℝ) (z : EuclideanSpace ℝ (PrimeHorizonIndex N)) =>
    let U := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N
    (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) ∧
    (∫ u, U u ^ 2) + β ^ 2 = 1 ∧
    (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W ∧
    topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ K_S ∧
    weilQuad U ≤ K_Q ∧
    weilQuad U + (∫ u, tiltedUnitSpline u ^ 2) *
      ((Real.log N / c N) * completeWeilEnergy tiltedUnitSpline (c N) N
        (normalizedRamanujanHorizonVector 1 N) * β ^ 2) +
      2 * (∫ u, tiltedUnitSpline u ^ 2) * β *
        (Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫) ≤ ε
  let BadAt := fun N : ℕ => ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
    x ≠ 0 ∧ completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0
  have hbad : ∃ᶠ N : ℕ in atTop, BadAt N := by
    rw [Filter.not_eventually] at hnot
    exact hnot.mono fun N hN => by
      simp only [not_forall, not_lt] at hN
      obtain ⟨x, hne, he⟩ := hN
      exact ⟨x, hne, he⟩
  let GoodAt := fun k N : ℕ => 1 ≤ N ∧ c N / (N : ℝ) ≤ 1 / ((k : ℝ) + 1) ∧
    ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
      completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0 →
      ∃ β z, P (1 / ((k : ℝ) + 1)) N β z
  have hwidth : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hgood : ∀ k, ∀ᶠ N : ℕ in atTop, GoodAt k N := by
    intro k
    filter_upwards [eventually_ge_atTop 1,
      hwidth.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))),
      hbridge (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))] with N hN hw hb
    exact ⟨hN, hw.le, hb⟩
  have hex : ∀ k M : ℕ, ∃ N, M ≤ N ∧ GoodAt k N ∧ BadAt N := by
    intro k M
    obtain ⟨N, hbadN, hMN, hgoodN⟩ :=
      (hbad.and_eventually ((eventually_ge_atTop M).and (hgood k))).exists
    exact ⟨N, hMN, hgoodN, hbadN⟩
  let N_seq : ℕ → ℕ := fun k => Nat.recOn k (Classical.choose (hex 0 1))
    (fun j prev => Classical.choose (hex (j + 1) (prev + 1)))
  have hstep : ∀ k, GoodAt k (N_seq k) ∧ BadAt (N_seq k) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hex 0 1)).2
    | succ j => exact (Classical.choose_spec (hex (j + 1) (N_seq j + 1))).2
  have hstrict : StrictMono N_seq := strictMono_nat_of_lt_succ fun k =>
    Nat.lt_of_succ_le (Classical.choose_spec (hex (k + 1) (N_seq k + 1))).1
  have hchosen : ∀ k : ℕ, ∃ β z, P (1 / ((k : ℝ) + 1)) (N_seq k) β z := by
    intro k
    obtain ⟨x, hne, he⟩ := (hstep k).2
    exact (hstep k).1.2.2 x hne he
  let β := fun k => Classical.choose (hchosen k)
  let z := fun k => Classical.choose (Classical.choose_spec (hchosen k))
  have hP : ∀ k : ℕ, P (1 / ((k : ℝ) + 1)) (N_seq k) (β k) (z k) :=
    fun k => Classical.choose_spec (Classical.choose_spec (hchosen k))
  apply no_charged_atomic_sequence_below_polarPayment hc hR hRS hcrit hpay hstrict
    (fun k => (hstep k).1.1) z β (fun k => (hP k).1) hKW.le hKS
    (fun k => (hP k).2.2.2.1) (fun k => (hP k).2.1) (fun k => (hP k).2.2.1)
    ?_ (fun k => (hP k).2.2.2.2.1) (fun k => (hP k).2.2.2.2.2)
  intro k u hu
  exact normalizedCentredAtomicTest_vanish_above_width
    (zero_lt_one.trans_le (hc (N_seq k))) (hstep k).1.1 (primeHorizonExtension (z k))
    ((hstep k).1.2.1.trans_lt hu)

#print axioms eventually_wholeSpace_positive_of_polarPayment

/-- Every closed critical band strictly below a paying ratio is eventually positive. -/
theorem eventuallyCriticalPosDef_of_polarPayment {Rstar S : ℝ}
    (_hRstar : 0 < Rstar) (hRS : Rstar < S)
    (hpay : ∀ A : ℝ, 0 ≤ A → PolarPaymentAt S A) :
    EventuallyCriticalPosDef Rstar := by
  obtain ⟨R₀, hR₀, hsmall⟩ := exists_pos_eventuallyCriticalPosDef
  by_cases hle : Rstar ≤ R₀
  · filter_upwards [hsmall,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with N hpos hL
    intro c hc1 hc8 x hne
    exact hpos hc1 (hc8.trans (mul_le_mul_of_nonneg_right hle hL)) hne
  · have hband := eventually_uniform_critical_band_of_curve (P := fun N c =>
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
          0 < completeWeilEnergy tiltedUnitSpline c N x) hR₀ (not_le.mp hle).le
        (fun R hR c hc hcrit => eventually_wholeSpace_positive_of_polarPayment hc
          (hR₀.trans_le hR.1) (hR.2.trans_lt hRS) hcrit hpay)
    filter_upwards [hsmall, hband] with N hpos hbandN
    intro c hc1 hc8 x hne
    by_cases hcsmall : c ^ 8 ≤ R₀ * Real.log (N : ℝ)
    · exact hpos hc1 hcsmall hne
    · exact hbandN c hc1 (not_le.mp hcsmall).le hc8 x hne

/-- Polar payment on every compact window suffices for the whole-space critical threshold. -/
theorem polarPaymentCriticalThreshold_le_criticalPositivityThreshold :
    polarPaymentCriticalThreshold ≤ criticalPositivityThreshold := by
  refine sSup_le ?_
  rintro _ ⟨S, ⟨hS, hpay⟩, rfl⟩
  refine le_of_forall_lt fun c hc => ?_
  rcases le_or_gt c 0 with hc0 | hc0
  · exact lt_of_le_of_lt hc0 criticalPositivityThreshold_pos
  · lift c to ℝ using ⟨(hc.trans (EReal.coe_lt_top S)).ne,
      (lt_trans EReal.bot_lt_zero hc0).ne'⟩
    have hc_pos : 0 < c := EReal.coe_pos.mp hc0
    have hcS : c < S := EReal.coe_lt_coe_iff.mp hc
    let R : ℝ := (c + S) / 2
    have hR : 0 < R := by dsimp only [R]; linarith only [hc_pos, hS]
    have hRS : R < S := by dsimp only [R]; linarith only [hcS]
    have hcR : (c : EReal) < (R : EReal) := EReal.coe_lt_coe_iff.mpr (by
      dsimp only [R]; linarith only [hcS])
    exact hcR.trans_le (le_sSup ⟨R,
      ⟨hR, eventuallyCriticalPosDef_of_polarPayment hR hRS hpay⟩, rfl⟩)

/-- The whole-space positivity threshold is exactly the polar-payment threshold. -/
theorem criticalPositivityThreshold_eq_polarPaymentCriticalThreshold :
    criticalPositivityThreshold = polarPaymentCriticalThreshold :=
  le_antisymm criticalPositivityThreshold_le_polarPaymentCriticalThreshold
    polarPaymentCriticalThreshold_le_criticalPositivityThreshold

/-- Eventual strict positivity and nonnegativity have the same whole-space threshold. -/
theorem criticalNonnegativityThreshold_eq_polarPaymentCriticalThreshold :
    criticalNonnegativityThreshold = polarPaymentCriticalThreshold :=
  le_antisymm criticalNonnegativityThreshold_le_polarPaymentCriticalThreshold
    (polarPaymentCriticalThreshold_le_criticalPositivityThreshold.trans
      criticalPositivityThreshold_le_criticalNonnegativityThreshold)

/-- The whole-space critical threshold grows exponentially with the onset aperture. -/
theorem exp_mul_le_criticalPositivityThreshold :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {a : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
        ((c₁ * Real.exp (c₂ * a) : ℝ) : EReal) ≤ criticalPositivityThreshold := by
  rw [criticalPositivityThreshold_eq_polarPaymentCriticalThreshold]
  exact exp_mul_le_polarPaymentCriticalThreshold

/-- A finite whole-space threshold satisfies the logarithmic onset lower bound. -/
theorem log_criticalPositivityThreshold_ge_mul_onsetAperture :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (criticalPositivityThreshold ≠ ⊤ →
        ∀ {a : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
          Real.log c₁ + c₂ * a ≤ Real.log criticalPositivityThreshold.toReal) := by
  rw [criticalPositivityThreshold_eq_polarPaymentCriticalThreshold]
  exact log_polarPaymentCriticalThreshold_ge_mul_onsetAperture

/-- Whole-space, polar and primitive infinite thresholds coincide with infinite onset and RH. -/
theorem criticalThresholds_eq_top_equivalences :
    (criticalPositivityThreshold = ⊤ ↔ polarPaymentCriticalThreshold = ⊤) ∧
    (polarPaymentCriticalThreshold = ⊤ ↔ poleOrthogonalCriticalThreshold = ⊤) ∧
    (poleOrthogonalCriticalThreshold = ⊤ ↔ onsetAperture zetaZeroConfig = ⊤) ∧
    (onsetAperture zetaZeroConfig = ⊤ ↔ RiemannHypothesis) := by
  have hp := polarPaymentCriticalThreshold_eq_top_iff_onsetAperture_eq_top
  have ho : poleOrthogonalCriticalThreshold = ⊤ ↔ onsetAperture zetaZeroConfig = ⊤ := by
    rw [poleOrthogonalCriticalThreshold_eq_highConductorCriticalThreshold]
    exact highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.trans
      riemannHypothesis_iff_onsetAperture_zeta_eq_top
  exact ⟨by rw [criticalPositivityThreshold_eq_polarPaymentCriticalThreshold],
    hp.trans ho.symm, ho, riemannHypothesis_iff_onsetAperture_zeta_eq_top.symm⟩

#print axioms criticalPositivityThreshold_eq_polarPaymentCriticalThreshold
#print axioms criticalNonnegativityThreshold_eq_polarPaymentCriticalThreshold
#print axioms exp_mul_le_criticalPositivityThreshold
#print axioms log_criticalPositivityThreshold_ge_mul_onsetAperture
#print axioms criticalThresholds_eq_top_equivalences

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
