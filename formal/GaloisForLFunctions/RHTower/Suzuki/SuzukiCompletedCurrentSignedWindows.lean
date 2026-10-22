import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilXiScrewGreenConnection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOriginRemainderRegularity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstGap
import GaloisForLFunctions.RHTower.RoutePCompletedErrorOneSidedLandau
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewAlmostPeriodic

/-!
# Both signed excursions of the literal Suzuki current

The actual logarithmic cusp makes `Psi(h)/h` arbitrarily large near zero. An eventual
one-sided bound on the completed Mellin error would imply RH by the existing signed
Landau theorem. The resulting uniform recurrence of the actual screw series transports
both orientations of the cusp to the bounded-current ray, a contradiction. The RH
assumption is thus discharged inside the proof.

The right derivative is proved at every positive point, including prime-power seams.
Right continuity upgrades both signed excursions to positive-length closed windows.
At zero frequency these are exactly windows of the full Gamma--polar--prime symbol,
which therefore has no eventual pointwise lower bound. This does not decide positivity
of its quadratic form on aperture-supported vectors, or the Riemann hypothesis.
-/

open Filter Topology Set
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

private theorem exp_floor_right_stable (t : ℝ) :
    ∀ᶠ r in 𝓝[≥] t, ⌊Real.exp r⌋₊ = ⌊Real.exp t⌋₊ := by
  have hu : ∀ᶠ r in 𝓝 t,
      Real.exp r < (⌊Real.exp t⌋₊ : ℝ) + 1 :=
    Real.continuous_exp.continuousAt.eventually_lt_const (Nat.lt_floor_add_one _)
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr htr
  apply le_antisymm
  · have h : ⌊Real.exp r⌋₊ < ⌊Real.exp t⌋₊ + 1 :=
      (Nat.floor_lt (Real.exp_pos r).le).mpr (by simpa using hr)
    omega
  · exact Nat.floor_mono (Real.exp_le_exp.mpr htr)

/-- The literal arithmetic screw has this right derivative even at a prime-power seam. -/
theorem hasDerivWithinAt_suzukiPsi_right {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt suzukiPsi (ccmGuinandWeilXiScrewRightSlope t) (Ici t) t := by
  let K := Finset.Icc 2 ⌊Real.exp t⌋₊
  let P : ℝ → ℝ := fun r => ∑ n ∈ K, screwPrimeWeight n * (r - Real.log n)
  have hP : HasDerivAt P (∑ n ∈ K, screwPrimeWeight n) t := by
    apply HasDerivAt.fun_sum
    intro n hn
    simpa using ((hasDerivAt_id t).sub_const (Real.log n)).const_mul (screwPrimeWeight n)
  have hmass : (∑ n ∈ K, screwPrimeWeight n) = criticalMellinPrimeMass t := by
    rw [criticalMellinPrimeMass_eq_atomSum]
    apply Finset.sum_congr rfl
    intro n hn
    exact (criticalMellinAtomWeight_eq_screwPrimeWeight
      (by have := (Finset.mem_Icc.mp hn).1; omega)).symm
  rw [hmass] at hP
  have hp : screwPrimeSum =ᶠ[𝓝[≥] t] P := by
    filter_upwards [exp_floor_right_stable t] with r hr
    simp only [screwPrimeSum, P, K, hr]
  have hp0 : screwPrimeSum t = P t := rfl
  have hprime := hP.hasDerivWithinAt.congr_of_eventuallyEq hp hp0
  have hraw := (hasDerivAt_ccmGuinandWeilXiScrewSmoothPart ht).hasDerivWithinAt.sub hprime
  have heq : suzukiPsi =ᶠ[𝓝[≥] t]
      fun r => ccmGuinandWeilXiScrewSmoothPart r - screwPrimeSum r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact suzukiPsi_eq_smoothPart_sub_screwPrimeSum (ht.le.trans hr)
  exact hraw.congr_of_eventuallyEq heq (suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht.le)

private theorem suzuki_cusp_secant (C : ℝ) :
    ∃ h : ℝ, 0 < h ∧ C * h < suzukiPsi h := by
  have hrem : ∀ᶠ t in 𝓝[>] (0 : ℝ), suzukiOriginRemainderPos t / t < 1 :=
    tendsto_suzukiOriginRemainderPos_div_id.eventually_lt_const (by norm_num)
  have hlog : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Real.log t < -2 * (C + suzukiOriginLinearCoeff + 1) :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot _
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < Real.log 2 :=
    (eventually_lt_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2))).filter_mono
      nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hr, hl, hs⟩ :=
    (hpos.and (hrem.and (hlog.and hsmall))).exists
  have heq := suzuki_equation_two_two t
  rw [abs_of_pos ht, screwPrimeSum_eq_zero_of_lt_log_two hs] at heq
  have hremEq : suzukiOriginRemainder t = suzukiOriginRemainderPos t := by
    simp only [suzukiOriginRemainder, abs_of_pos ht]
  rw [hremEq] at heq
  have hneg : suzukiSourceScrew t = -suzukiPsi t := by simp only [suzukiSourceScrew, suzukiPsi, neg_neg]
  rw [hneg] at heq
  have hr' := (div_lt_iff₀ ht).mp hr
  have hl' := mul_lt_mul_of_pos_right hl ht
  exact ⟨t, ht, by nlinarith⟩

private theorem signed_suzuki_secant_le {ε C L u v : ℝ}
    (hbound : ∀ t : ℝ, L ≤ t → ε * ccmGuinandWeilXiScrewRightSlope t ≤ C)
    (hu : 0 < u) (hLu : L ≤ u) (huv : u ≤ v) :
    ε * (suzukiPsi v - suzukiPsi u) ≤ C * (v - u) := by
  have hf : ε * suzukiPsi v ≤ ε * suzukiPsi u + C * (v - u) := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := fun t => ε * suzukiPsi t) (f' := fun t => ε * ccmGuinandWeilXiScrewRightSlope t)
      (a := u) (b := v) (continuous_const.mul continuous_suzukiPsi).continuousOn
      (fun t ht => (hasDerivWithinAt_suzukiPsi_right (hu.trans_le ht.1)).const_mul ε)
      (B := fun t => ε * suzukiPsi u + C * (t - u)) (B' := fun _ => C)
    · simp
    · fun_prop
    · intro t ht
      simpa using (((hasDerivAt_id t).sub_const u).const_mul C).const_add
        (ε * suzukiPsi u) |>.hasDerivWithinAt
    · intro t ht
      exact hbound t (hLu.trans ht.1)
    · exact ⟨huv, le_rfl⟩
  nlinarith

private theorem no_signed_suzuki_slope_bound_of_rh
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (C L : ℝ)
    (hb : ∀ t : ℝ, L ≤ t → ε * ccmGuinandWeilXiScrewRightSlope t ≤ C) : False := by
  obtain ⟨h, hh, hcusp⟩ := suzuki_cusp_secant (C + 1)
  have hap : _root_.HTGeometry.IsBohrAlmostPeriodic suzukiPsi := by
    have heq : suzukiPsi = xiCriticalScrewSeries :=
      funext (suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH)
    rw [heq]
    exact isBohrAlmostPeriodic_screwSeries xiCriticalScrewWeight_nonneg
      (summable_xiCriticalScrewWeight_of_rh hRH)
  obtain ⟨D, _, hD⟩ := hap (h / 4) (by positivity)
  obtain ⟨τ, hτ, hrec⟩ := hD (max L 0 + h + 1)
  have hτ0 : 0 < τ - h := by have := le_max_right L 0; linarith [hτ.1]
  have hτL : L ≤ τ - h := by have := le_max_left L 0; linarith [hτ.1]
  have hzero := hrec 0
  have hpos := hrec h
  have hneg := hrec (-h)
  simp only [zero_add, suzukiPsi_zero, sub_zero, Real.norm_eq_abs] at hzero
  simp only [Real.norm_eq_abs] at hpos hneg
  rw [suzukiPsi_neg] at hneg
  have hz := abs_le.mp hzero
  have hp := abs_le.mp hpos
  have hn := abs_le.mp hneg
  rcases hε with rfl | rfl
  · have hs := signed_suzuki_secant_le hb (by linarith : 0 < τ)
      (by linarith : L ≤ τ) (by linarith : τ ≤ h + τ)
    simp only [one_mul] at hs
    nlinarith
  · have hs := signed_suzuki_secant_le hb hτ0 hτL
      (by linarith : τ - h ≤ τ)
    rw [show τ - h = -h + τ by ring] at hs
    simp only [neg_one_mul] at hs
    nlinarith

private theorem completed_error_signed_escape {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (B L : ℝ) : ∃ t : ℝ, max L 1 ≤ t ∧ B < ε * criticalMellinCompletedError t := by
  by_contra! hbound
  let A := max L 1
  let C := |B| + 23 * Real.exp (A / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : B ≤ C := by
    dsimp [C]
    have := le_abs_self B
    have := Real.exp_pos (A / 2)
    linarith
  have hsigned (t : ℝ) : ε * criticalMellinCompletedError t ≤ |criticalMellinCompletedError t| := by
    rcases hε with rfl | rfl
    · simpa using le_abs_self (criticalMellinCompletedError t)
    · simpa using neg_le_abs (criticalMellinCompletedError t)
  have hglobal (t : ℝ) (ht : 0 ≤ t) : ε * criticalMellinCompletedError t ≤ C * (1 + t) := by
    by_cases hAt : A ≤ t
    · exact (hbound t hAt).trans (by nlinarith)
    · have he := Real.exp_le_exp.mpr (show t / 2 ≤ A / 2 by linarith)
      have hEt := (hsigned t).trans (abs_criticalMellinCompletedError_le_sqrt ht)
      have hCt : 23 * Real.exp (t / 2) ≤ C := by
        dsimp [C]; nlinarith [abs_nonneg B]
      exact (hEt.trans hCt).trans (by nlinarith)
  have hRH : RiemannHypothesis := by
    apply riemannHypothesis_of_completedError_oneSided_linear (ε := -ε) (B := C)
    · rcases hε with rfl | rfl <;> simp
    · intro t ht
      nlinarith [hglobal t ht]
  have hlim := tendsto_ccmGuinandWeilXiScrewRightSlope_sub_completedError.const_mul ε
  have hev : ∀ᶠ t : ℝ in atTop,
      ε * (ccmGuinandWeilXiScrewRightSlope t - criticalMellinCompletedError t) <
        ε * (screwLinearCoeff / 2) + 1 :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  apply no_signed_suzuki_slope_bound_of_rh hRH hε
    (B + ε * (screwLinearCoeff / 2) + 1) (max A M)
  intro t ht
  have hEt := hbound t ((le_max_left A M).trans ht)
  have hSt := hM t ((le_max_right A M).trans ht)
  nlinarith

private theorem completed_error_right_continuous (t : ℝ) :
    ContinuousWithinAt criticalMellinCompletedError (Ici t) t := by
  have hmass : ContinuousWithinAt criticalMellinPrimeMass (Ici t) t := by
    apply continuousWithinAt_const.congr_of_eventuallyEq (f := fun _ => criticalMellinPrimeMass t)
    · filter_upwards [exp_floor_right_stable t] with r hr
      simp only [criticalMellinPrimeMass, hr]
    · rfl
  have heq : criticalMellinCompletedError =
      fun r => 4 * Real.sinh (r / 2) - criticalMellinPrimeMass r :=
    funext criticalMellinCompletedError_eq_polar_sub_primeMass
  rw [heq]
  exact (continuous_const.mul (Real.continuous_sinh.comp
    (continuous_id.div_const 2))).continuousWithinAt.sub hmass

private theorem completed_error_signed_window {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (B L : ℝ) : ∃ u v : ℝ, max L 1 ≤ u ∧ u < v ∧
      ∀ t ∈ Icc u v, B < ε * criticalMellinCompletedError t := by
  obtain ⟨u, hu, hBu⟩ := completed_error_signed_escape hε B L
  have hcont := (completed_error_right_continuous u).const_mul ε
  have hev : ∀ᶠ t in 𝓝[≥] u, B < ε * criticalMellinCompletedError t :=
    hcont.eventually_const_lt hBu
  obtain ⟨v, huv, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hev
  exact ⟨u, v, hu, huv, hsub⟩

/-- Both signed completed prime--polar currents exceed every fixed level on positive-length
closed intervals arbitrarily far along the actual logarithmic source. -/
theorem criticalMellinCompletedError_two_signed_windows (B L : ℝ) :
    (∃ u v : ℝ, max L 1 ≤ u ∧ u < v ∧
      ∀ t ∈ Icc u v, B < criticalMellinCompletedError t) ∧
    (∃ u v : ℝ, max L 1 ≤ u ∧ u < v ∧
      ∀ t ∈ Icc u v, criticalMellinCompletedError t < -B) := by
  constructor
  · simpa using completed_error_signed_window (ε := 1) (Or.inl rfl) B L
  · obtain ⟨u, v, hu, huv, hwin⟩ :=
      completed_error_signed_window (ε := -1) (Or.inr rfl) B L
    exact ⟨u, v, hu, huv, fun t ht => by have := hwin t ht; linarith⟩

/-- The complete Gamma--polar--prime symbol has arbitrarily late positive-length aperture
windows beyond either signed level, already at frequency zero. -/
theorem correctedCCMSymbol_zero_two_signed_windows (B L : ℝ) :
    (∃ u v : ℝ, max L 1 ≤ u ∧ u < v ∧
      ∀ a ∈ Icc u v, B < correctedCCMSymbol a 0) ∧
    (∃ u v : ℝ, max L 1 ≤ u ∧ u < v ∧
      ∀ a ∈ Icc u v, correctedCCMSymbol a 0 < -B) := by
  have hscale : ∀ u : ℝ, max (2 * max L 1) 1 ≤ u → max L 1 ≤ u / 2 := by
    intro u hu
    have := (le_max_left (2 * max L 1) 1).trans hu
    linarith
  constructor
  · obtain ⟨u, v, hu, huv, hwin⟩ :=
      (criticalMellinCompletedError_two_signed_windows
        ((B - ccmArchimedeanMultiplier 0) / 2) (2 * max L 1)).1
    refine ⟨u / 2, v / 2, hscale u hu, by linarith, ?_⟩
    intro a ha
    have ha0 : 0 ≤ a := by have := le_max_right L 1; have := hscale u hu; linarith [ha.1]
    have hw := hwin (2 * a) ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have heq := correctedCCMSymbol_zero_sub_archimedean ha0
    linarith
  · obtain ⟨u, v, hu, huv, hwin⟩ :=
      (criticalMellinCompletedError_two_signed_windows
        ((B + ccmArchimedeanMultiplier 0) / 2) (2 * max L 1)).2
    refine ⟨u / 2, v / 2, hscale u hu, by linarith, ?_⟩
    intro a ha
    have ha0 : 0 ≤ a := by have := le_max_right L 1; have := hscale u hu; linarith [ha.1]
    have hw := hwin (2 * a) ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have heq := correctedCCMSymbol_zero_sub_archimedean ha0
    linarith

end
end RHTower
