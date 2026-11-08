import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimitiveDirectionsHaveCompactCollarProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# The primitive critical threshold is the window threshold

A nonpositive primitive sequence has a nonzero compact collar profile. Normalizing
its mass contradicts the continuum window pencil below its first threshold.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Every positive critical curve below all continuum window thresholds is eventually positive
on the primitive hyperplane. -/
theorem eventually_primitive_positive_of_critical_curve
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hlt : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      x ∈ (conductorSubspace 1 N)ᗮ → x ≠ 0 →
      0 < completeWeilEnergy tiltedUnitSpline (c N) N x := by
  by_contra hnot
  obtain ⟨K_W, K_L, hKW, _, hbridge⟩ := exists_critical_primitive_collar_weilQuad_bridge hc hR hcrit
  let BadAt (N : ℕ) : Prop := ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
    x ∈ (conductorSubspace 1 N)ᗮ ∧ x ≠ 0 ∧ completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0
  have hbad : ∃ᶠ N : ℕ in atTop, BadAt N := by
    rw [Filter.not_eventually] at hnot
    exact hnot.mono fun N hN => by simpa only [not_forall, not_imp, not_lt] using hN
  let GoodAt (k N : ℕ) : Prop := 1 ≤ N ∧ c N / (N : ℝ) ≤ 1 / ((k : ℝ) + 1) ∧
    ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      x ∈ (conductorSubspace 1 N)ᗮ → x ≠ 0 →
      completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0 →
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients (N / linearDefectCutoff (c N)) (primeHorizonExtension w)) (c N) N
        0 < ∫ u, U u ^ 2 ∧
        (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W * (∫ u, U u ^ 2) ∧
        weilQuad U ≤ (1 / ((k : ℝ) + 1)) * (∫ u, U u ^ 2)
  have hwidth : Tendsto (fun N : ℕ => c N / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hgood : ∀ k, ∀ᶠ N : ℕ in atTop, GoodAt k N := by
    intro k
    filter_upwards [eventually_ge_atTop 1,
      hwidth.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))),
      hbridge (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))] with N hN hw hbr
    refine ⟨hN, hw.le, fun x hx hne he => ?_⟩
    obtain ⟨w, _, hm, hW, _, hq⟩ := hbr x hx hne he
    exact ⟨w, hm, hW, hq⟩
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
  let c_seq := fun k => c (N_seq k)
  have hbr_k : ∀ k, ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)),
      let U := normalizedCentredAtomicTest tiltedUnitSpline
        (atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k)) (primeHorizonExtension w))
        (c_seq k) (N_seq k)
      0 < ∫ u, U u ^ 2 ∧
      (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W * (∫ u, U u ^ 2) ∧
      weilQuad U ≤ (1 / ((k : ℝ) + 1)) * (∫ u, U u ^ 2) := by
    intro k
    obtain ⟨x, hx, hne, he⟩ := (hstep k).2
    exact (hstep k).1.2.2 x hx hne he
  let w_seq := fun k => Classical.choose (hbr_k k)
  let y_raw : ℕ → ℕ → ℝ := fun k =>
    atomicTailCoefficients (N_seq k / linearDefectCutoff (c_seq k)) (primeHorizonExtension (w_seq k))
  let U_raw : ℕ → ℝ → ℝ := fun k =>
    normalizedCentredAtomicTest tiltedUnitSpline (y_raw k) (c_seq k) (N_seq k)
  have hU_raw_pos : ∀ k, 0 < ∫ u, U_raw k u ^ 2 := fun k => (Classical.choose_spec (hbr_k k)).1
  let ν : ℕ → ℝ := fun k => Real.sqrt (∫ u, U_raw k u ^ 2)
  have hν_pos : ∀ k, 0 < ν k := fun k => Real.sqrt_pos.mpr (hU_raw_pos k)
  have hν_sq : ∀ k, ν k ^ 2 = ∫ u, U_raw k u ^ 2 := fun k => Real.sq_sqrt (hU_raw_pos k).le
  let y_norm : ℕ → ℕ → ℝ := fun k n => (ν k)⁻¹ * y_raw k n
  let V : ℕ → ℝ → ℝ := fun k =>
    normalizedCentredAtomicTest tiltedUnitSpline (y_norm k) (c_seq k) (N_seq k)
  have hV_eq : ∀ k, V k = fun u => (ν k)⁻¹ * U_raw k u := fun k =>
    normalizedCentredAtomicTest_const_mul (ν k)⁻¹ (y_raw k) (c_seq k) (N_seq k)
  have hUd : ∀ k, ContDiff ℝ 2 (U_raw k) := fun k =>
    contDiff_const.mul (contDiff_centredAtomicTest contDiff_tiltedUnitSpline _ _ _)
  have hUc : ∀ k, HasCompactSupport (U_raw k) := fun k =>
    (hasCompactSupport_centredAtomicTest tiltedUnitSpline_eq_zero (y_raw k)
      (zero_lt_one.trans_le (hc (N_seq k))) (hstep k).1.1).mul_left
  have hV_norm : ∀ k, (∫ u, V k u ^ 2) = 1 := by
    intro k
    rw [hV_eq k]
    simp_rw [mul_pow]
    rw [integral_const_mul, inv_pow, ← hν_sq k, inv_mul_cancel₀ (pow_ne_zero 2 (hν_pos k).ne')]
  let M₈ := K_W
  have hM₈_pos : 0 < M₈ := hKW
  have hV_M₈ : ∀ k, (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ := by
    intro k
    obtain ⟨_, hb2, _⟩ := Classical.choose_spec (hbr_k k)
    have heq : (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) =
        (ν k)⁻¹ ^ 2 * ∫ u, U_raw k u ^ 2 * Real.exp (-(8 * u)) := by
      rw [hV_eq k, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only; ring)
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left hb2 (sq_nonneg (ν k)⁻¹)
    have hid : (ν k)⁻¹ ^ 2 * (M₈ * ∫ u, U_raw k u ^ 2) = M₈ := by
      have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
      rw [inv_pow, hν_sq k, mul_comm M₈, inv_mul_cancel_left₀ hne]
    linarith only [hm, hid]
  have hV_wq : ∀ (k : ℕ), weilQuad (V k) ≤ 1 / (Nat.cast k + 1) := by
    intro k
    obtain ⟨_, _, hb3⟩ := Classical.choose_spec (hbr_k k)
    rw [hV_eq k, weilQuad_const_mul (hUd k) (hUc k) (ν k)⁻¹]
    have hm := mul_le_mul_of_nonneg_left hb3 (sq_nonneg (ν k)⁻¹)
    have hid : (ν k)⁻¹ ^ 2 * ((1 / (Nat.cast k + 1)) * ∫ u, U_raw k u ^ 2) =
        1 / (Nat.cast k + 1) := by
      have hne : (∫ u, U_raw k u ^ 2) ≠ 0 := (hU_raw_pos k).ne'
      rw [inv_pow, hν_sq k, mul_comm (1 / (Nat.cast k + 1)), inv_mul_cancel_left₀ hne]
    linarith only [hm, hid]
  exact no_nonpositive_atomic_sequence_below_windowThreshold hR hlt hstrict
    (fun k => (hstep k).1.1) (fun k => hc (N_seq k)) (hcrit.comp hstrict.tendsto_atTop)
    (fun k => (hstep k).1.2.1) y_norm hV_norm hM₈_pos hV_M₈ hV_wq

/-- Every ratio below the global window threshold is eventually positive on the primitive
hyperplane, uniformly in the critical band. -/
theorem eventuallyPoleOrthogonalPosDef_of_lt_iInf_windowThreshold {Rstar : ℝ} (hRstar : 0 < Rstar)
    (hlt : (Rstar : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) :
    EventuallyPoleOrthogonalPosDef Rstar := by
  obtain ⟨R₀, hR₀, hsmall⟩ := exists_pos_eventuallyCriticalPosDef
  by_cases hle : Rstar ≤ R₀
  · filter_upwards [hsmall,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with N hpos hL
    intro c hc1 hc8 z _ hne
    exact hpos hc1 (hc8.trans (mul_le_mul_of_nonneg_right hle hL)) hne
  · have hband := eventually_uniform_critical_band_of_curve (P := fun N c =>
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ∈ (conductorSubspace 1 N)ᗮ → x ≠ 0 →
          0 < completeWeilEnergy tiltedUnitSpline c N x) hR₀ (not_le.mp hle).le
        (fun R hR c hc hcrit => eventually_primitive_positive_of_critical_curve hc
          (hR₀.trans_le hR.1) hcrit ((EReal.coe_le_coe_iff.mpr hR.2).trans_lt hlt))
    filter_upwards [hsmall, hband] with N hpos hbandN
    intro c hc1 hc8 z hz hne
    by_cases hcsmall : c ^ 8 ≤ R₀ * Real.log (N : ℝ)
    · exact hpos hc1 hcsmall hne
    · exact hbandN c hc1 (not_le.mp hcsmall).le hc8 z hz hne

/-- The primitive critical threshold dominates every continuum window infimum. -/
theorem iInf_windowThreshold_le_poleOrthogonalCriticalThreshold :
    (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) ≤ poleOrthogonalCriticalThreshold := by
  have hpos_thr : (0 : EReal) < poleOrthogonalCriticalThreshold :=
    criticalPositivityThreshold_pos.trans_le criticalPositivityThreshold_le_poleOrthogonalCriticalThreshold
  cases hW : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) with
  | bot => exact bot_le
  | top =>
    rw [top_le_iff]
    refine (EReal.eq_top_iff_forall_lt _).mpr fun r => ?_
    set R : ℝ := max (r + 1) 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hrR : (r : EReal) < (R : EReal) :=
      EReal.coe_lt_coe_iff.mpr (by dsimp only [R]; linarith [le_max_left (r + 1) 1])
    have hlt_W : (R : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
      rw [hW]; exact EReal.coe_lt_top R
    exact hrR.trans_le
      (le_sSup ⟨R, ⟨hR, eventuallyPoleOrthogonalPosDef_of_lt_iInf_windowThreshold hR hlt_W⟩, rfl⟩)
  | coe M =>
    rcases le_or_gt M 0 with hM0 | hM0
    · exact (EReal.coe_le_coe_iff.mpr hM0).trans hpos_thr.le
    · by_contra hnot_le
      push Not at hnot_le
      cases hT : poleOrthogonalCriticalThreshold with
      | bot =>
        rw [hT] at hpos_thr
        exact not_lt_bot hpos_thr
      | top =>
        rw [hT] at hnot_le
        exact not_top_lt hnot_le
      | coe T =>
        rw [hT, EReal.coe_lt_coe_iff] at hnot_le
        rw [hT, EReal.coe_pos] at hpos_thr
        set Rstar : ℝ := (T + M) / 2
        have hRstar : 0 < Rstar := by dsimp only [Rstar]; linarith
        have hlt_W : (Rstar : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
          rw [hW, EReal.coe_lt_coe_iff]; dsimp only [Rstar]; linarith
        have hle_T : (Rstar : EReal) ≤ (T : EReal) := by
          rw [← hT]
          exact le_sSup
            ⟨Rstar, ⟨hRstar, eventuallyPoleOrthogonalPosDef_of_lt_iInf_windowThreshold hRstar hlt_W⟩,
              rfl⟩
        have hRT : Rstar ≤ T := EReal.coe_le_coe_iff.mp hle_T
        dsimp only [Rstar] at hRT
        linarith

/-- The primitive critical threshold equals the infimum of continuum window thresholds. -/
theorem poleOrthogonalCriticalThreshold_eq_iInf_windowThreshold :
    poleOrthogonalCriticalThreshold = ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
  apply le_antisymm
  · exact poleOrthogonalCriticalThreshold_le_highConductorCriticalThreshold.trans
      highConductorCriticalThreshold_eq_iInf_windowThreshold.le
  · exact iInf_windowThreshold_le_poleOrthogonalCriticalThreshold

#print axioms eventually_primitive_positive_of_critical_curve
#print axioms poleOrthogonalCriticalThreshold_eq_iInf_windowThreshold

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
