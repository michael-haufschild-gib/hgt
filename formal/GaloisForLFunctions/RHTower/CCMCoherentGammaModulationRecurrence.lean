import GaloisForLFunctions.RHTower.CCMCoherentGammaPhysicalStability
import GaloisForLFunctions.RHTower.CCMActualHeadSupportedCoherentGamma
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurModulation
import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence

/-!
# Joint recurrence of prime edges and the supported coherent Gamma cost

The terminal phase is included in the same recurrence as every actual prime
phase. This retains the complete prime-prime and prime-terminal interference.
Spatial support projection commutes with modulation, so it cannot erase the
recurrent coherent cost merely by removing invisible parts of the field.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology BigOperators
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem phase_spatial_add (t x h : ℝ) :
    modulationSymbol t (x+h) = modulationSymbol t x * modulationSymbol t h := by
  unfold modulationSymbol
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem translation_ae (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x+h) :=
  (Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)).trans (Eventually.of_forall fun _ => rfl)

theorem logTranslationCLM_modulationMul_apply (h t : ℝ) (f : SoninL2) :
    logTranslationCLM h (modulationMul t f) =
      modulationSymbol t h • modulationMul t (logTranslationCLM h f) := by
  apply Lp.ext
  have hm := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
    |>.eventually (coeFn_modulationMul t f)
  filter_upwards [translation_ae h (modulationMul t f), hm,
    Lp.coeFn_smul (modulationSymbol t h) (modulationMul t (logTranslationCLM h f)),
    coeFn_modulationMul t (logTranslationCLM h f), translation_ae h f]
    with x ht hm hs hmod hf
  change (modulationMul t f) (x+h) = modulationSymbol t (x+h) * f (x+h) at hm
  rw [ht, hm, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmod, hf, phase_spatial_add]
  ring

theorem ccmIncrementSupportProjection_modulationMul
    (a : SuzukiPositiveAperture) (r t : ℝ) (f : SoninL2) :
    ccmIncrementSupportProjection a r (modulationMul t f) =
      modulationMul t (ccmIncrementSupportProjection a r f) := by
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (ccmIncrementSupport a r) (measurableSet_ccmIncrementSupport a r)
      (modulationMul t f),
    indicatorCutoff_ae (ccmIncrementSupport a r) (measurableSet_ccmIncrementSupport a r) f,
    coeFn_modulationMul t f, coeFn_modulationMul t (ccmIncrementSupportProjection a r f)]
    with x hp hf hm hmp
  change (ccmIncrementSupportProjection a r (modulationMul t f)) x =
    (ccmIncrementSupport a r).indicator (fun y => (modulationMul t f) y) x at hp
  change (ccmIncrementSupportProjection a r f) x =
    (ccmIncrementSupport a r).indicator (fun y => f y) x at hf
  rw [hp, hmp, hf]
  by_cases hx : x ∈ ccmIncrementSupport a r
  · rw [indicator_of_mem hx, indicator_of_mem hx, hm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

private theorem phase_clock (d : ℕ) (v : Fin d → ℝ) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      ∀ i, Tendsto (fun j => modulationSymbol (κ j) (v i)) atTop (𝓝 1) := by
  have hc (j : ℕ) :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      (Nat.succ_pos j) (fun i => 2*Real.pi*v i)
  choose k hk _ m hm using hc
  let κ : ℕ → ℝ := fun j => (k j : ℝ)
  have hκ : Tendsto κ atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    change (j : ℝ) ≤ (k j : ℝ)
    exact_mod_cast (Nat.le_succ j).trans (hk j)
  refine ⟨κ,hκ,fun i => ?_⟩
  have hb (j : ℕ) :
      ‖modulationSymbol (κ j) (v i)-1‖ ≤ 2*Real.pi / ((j+1 : ℕ) : ℝ) := by
    have h := (norm_exp_I_mul_real_sub_one_le_mod_two_pi
      ((k j : ℝ)*(2*Real.pi*v i)) (m j i)).trans (hm j i)
    have heq : modulationSymbol (κ j) (v i) =
        Complex.exp (I * (((k j : ℝ)*(2*Real.pi*v i) : ℝ) : ℂ)) := by
      unfold modulationSymbol
      dsimp only [κ]
      congr 1
      push_cast
      ring
    rw [heq]
    exact h
  have hi : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hb0 : Tendsto (fun j : ℕ => 2*Real.pi / ((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using hi.const_mul (2*Real.pi)
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using squeeze_zero (fun j => norm_nonneg _) hb hb0

private theorem phase_spatial_neg (t h : ℝ) :
    modulationSymbol t (-h) = star (modulationSymbol t h) := by
  change modulationSymbol t (-h) = (starRingEnd ℂ) (modulationSymbol t h)
  rw [conj_modulationSymbol]
  unfold modulationSymbol
  congr 1
  push_cast
  ring

private def rotated_field (T : ℝ) (N : ℕ) (t : ℝ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  (∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
    (modulationSymbol t (-Real.log n) • logTranslationCLM (-Real.log n) f)) +
  (ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) •
    (modulationSymbol t (-T) • logTranslationCLM (-T) f)

private theorem field_modulation (T : ℝ) (N : ℕ) (t : ℝ) (f : SoninL2) (r : ℝ) :
    ccmActualHeadQuantileCompletedCoherentField T N (modulationMul t f) r =
      modulationMul t (rotated_field T N t f r) := by
  simp only [ccmActualHeadQuantileCompletedCoherentField, ccmActualHeadQuantileBulkCoherentField,
    ccmActualHeadQuantileCellCoherentField, ccmActualHeadQuantileTerminalCoherentField,
    rotated_field, logTranslationCLM_modulationMul_apply, map_add, map_sum, map_smul]

private theorem supported_cost_recurrence (a : SuzukiPositiveAperture) (N : ℕ)
    (κ : ℕ → ℝ) (f : SoninL2)
    (hp : ∀ n < N, Tendsto (fun j => modulationSymbol (κ j) (-Real.log n)) atTop (𝓝 1))
    (ht : Tendsto (fun j => modulationSymbol (κ j) (-(2*a.1))) atTop (𝓝 1)) :
    Tendsto (fun j => ccmActualHeadSupportedCoherentGammaCost a N (modulationMul (κ j) f))
      atTop (𝓝 (ccmActualHeadSupportedCoherentGammaCost a N f)) := by
  have hpoint (r : ℝ) :
      Tendsto (fun j => rotated_field (2*a.1) N (κ j) f r) atTop
        (𝓝 (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r)) := by
    have hbulk := tendsto_finsetSum (Finset.range N) fun n hn =>
      ((hp n (Finset.mem_range.mp hn)).smul_const (logTranslationCLM (-Real.log n) f)).const_smul
        (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ)
    have hterminal := (ht.smul_const (logTranslationCLM (-(2*a.1)) f)).const_smul
      (ccmActualHeadQuantileTerminalDisplacementDensity (2*a.1) N r : ℂ)
    simpa only [one_smul, rotated_field, ccmActualHeadQuantileCompletedCoherentField,
      ccmActualHeadQuantileBulkCoherentField, ccmActualHeadQuantileCellCoherentField,
      ccmActualHeadQuantileTerminalCoherentField] using hbulk.add hterminal
  have hnorm (j : ℕ) (r : ℝ) :
      ‖ccmActualHeadSupportedCoherentField a N (modulationMul (κ j) f) r‖ =
        ‖ccmIncrementSupportProjection a r (rotated_field (2*a.1) N (κ j) f r)‖ := by
    rw [ccmActualHeadSupportedCoherentField, field_modulation,
      ccmIncrementSupportProjection_modulationMul, GaloisForLFunctions.norm_modulationMul_eq]
  have hmajor := (integrable_ccmOutgoingQuantileGammaChiSquareDensity N).add
    (integrable_ccmActualHeadQuantileTerminalDensity_sq_mul_dual (2*a.1) N)
  let B : ℝ → ℝ := fun r => (2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
    ccmActualHeadQuantileTerminalDisplacementDensity (2*a.1) N r ^ 2) * ‖f‖ ^ 2) *
      ccmGammaHigherBinetDualDensity |r|
  have hB : Integrable B := by
    convert hmajor.const_mul (2*‖f‖^2) using 1
    funext r
    dsimp [B]
    ring
  unfold ccmActualHeadSupportedCoherentGammaCost
  apply tendsto_integral_of_dominated_convergence B
  · intro j
    exact (integrable_ccmActualHeadSupportedCoherentGammaDensity a N _).aestronglyMeasurable
  · exact hB
  · intro j
    filter_upwards with r
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
    have hproj := norm_sq_ccmIncrementSupportProjection a r
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N (modulationMul (κ j) f) r)
    have hle := mul_le_mul_of_nonneg_right
      (show ‖ccmActualHeadSupportedCoherentField a N (modulationMul (κ j) f) r‖^2 ≤
          ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N (modulationMul (κ j) f) r‖^2 by
        dsimp only [ccmActualHeadSupportedCoherentField]
        nlinarith [sq_nonneg ‖ccmActualHeadQuantileCompletedCoherentField
          (2*a.1) N (modulationMul (κ j) f) r -
          ccmActualHeadSupportedCoherentField a N (modulationMul (κ j) f) r‖])
      (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
    have hbound := norm_ccmActualHeadQuantileCompletedCoherentField_sq_mul_dual_le
      (2*a.1) N (modulationMul (κ j) f) r
    rw [GaloisForLFunctions.norm_modulationMul_eq] at hbound
    exact hle.trans hbound
  · filter_upwards with r
    simp_rw [hnorm]
    exact ((((ccmIncrementSupportProjection a r).continuous.tendsto _).comp
      (hpoint r)).norm.pow 2).mul_const (ccmGammaHigherBinetDualDensity |r|)

/-- The full supported cost survives recurrence of every actual prime edge.
No prime-prime or prime-terminal mixed term is omitted. -/
theorem exists_ccmSchurPole_recurrence_with_supportedGammaCost
    (a : SuzukiPositiveAperture) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      (∀ j, ‖ccmApertureModulation a (κ j) (ccmSchurPoleVector a)‖ = ‖ccmSchurPoleVector a‖) ∧
      (∀ g : suzukiApertureHilbert a,
        Tendsto (fun j => inner ℂ g (ccmApertureModulation a (κ j) (ccmSchurPoleVector a)))
          atTop (𝓝 0)) ∧
      Tendsto (fun j => ccmPrimePoleSchurEnergy a
        (ccmApertureModulation a (κ j) (ccmSchurPoleVector a)).1) atTop (𝓝 0) ∧
      Tendsto (fun j => ccmActualHeadSupportedCoherentGammaCost a
        (⌊Real.exp (2*a.1)⌋₊+1) (ccmApertureModulation a (κ j) (ccmSchurPoleVector a)).1)
        atTop (𝓝 (ccmActualHeadSupportedCoherentGammaCost a (⌊Real.exp (2*a.1)⌋₊+1)
          (ccmSchurPoleVector a).1)) := by
  let N := ⌊Real.exp (2*a.1)⌋₊
  let v : Fin (N+2) → ℝ := Fin.cases (-(2*a.1)) (fun i => Real.log (i : ℕ))
  obtain ⟨κ,hκ,hphase⟩ := phase_clock (N+2) v
  have hp (n : ℕ) (hn : n ≤ N) :
      Tendsto (fun j => modulationSymbol (κ j) (Real.log n)) atTop (𝓝 1) :=
    hphase (Fin.succ ⟨n, Nat.lt_succ_of_le hn⟩)
  have hm (n : ℕ) (hn : n < N+1) :
      Tendsto (fun j => modulationSymbol (κ j) (-Real.log n)) atTop (𝓝 1) := by
    have h := ((show Continuous (fun z : ℂ => star z) from continuous_star).tendsto 1).comp
      (hp n (Nat.le_of_lt_succ hn))
    simp only [star_one] at h
    change Tendsto (fun j => star (modulationSymbol (κ j) (Real.log n)))
      atTop (𝓝 1) at h
    simpa only [← phase_spatial_neg] using h
  refine ⟨κ,hκ,fun j => norm_ccmApertureModulation a (κ j) _,
    fun g => (inner_ccmApertureModulation_tendsto_zero a _ g).comp hκ, ?_,
    supported_cost_recurrence a (N+1) κ (ccmSchurPoleVector a).1 hm (hphase 0)⟩
  have he (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      Tendsto (fun j => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleEdgeEnergy a (Real.log n)
          (ccmApertureModulation a (κ j) (ccmSchurPoleVector a)).1) atTop (𝓝 0) := by
    have hs := (hp n (Finset.mem_Icc.mp hn).2).sub_const 1
    simp only [sub_self] at hs
    simp_rw [ccmPrimePoleEdgeEnergy_modulatedPole]
    simpa only [norm_zero, zero_pow two_ne_zero, zero_mul, mul_zero] using
      ((hs.norm.pow 2).mul_const
        (∫ x : ℝ, ccmPrimePoleRowDensity a (Real.log n) (ccmSchurPoleVector a).1 x)).const_mul
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
  simpa only [ccmPrimePoleSchurEnergy, Finset.sum_const_zero, N] using
    tendsto_finsetSum (Finset.Icc 2 N) he

end RHTower
