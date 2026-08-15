import GaloisForLFunctions.RHTower.ProlateSourceVariation

/-!
# The continuous polar charge of the prolate source

Combining the unconditional primitive bound `(11)` with the half-density envelope closes `(18)`:
the constructed mean-zero prolate source has bounded continuous polar charge on every exterior ray,
with a bound that decays in the radial parameter.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- The half-line mean of an even compactly supported source vanishes when its total mass does. -/
theorem intervalIntegral_half_eq_zero_of_even {F : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hFi : Integrable F) (heven : Function.Even F)
    (hvan : ∀ x : ℝ, x ∉ Icc (-L) L → F x = 0) (hmean : (∫ y : ℝ, F y) = 0) :
    (∫ x in (0 : ℝ)..L, F x) = 0 := by
  have hset : (∫ x in Icc (-L) L, F x) = ∫ x : ℝ, F x :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hvan
  have hIcc : (∫ x in (-L : ℝ)..L, F x) = ∫ x in Icc (-L) L, F x := by
    rw [intervalIntegral.integral_of_le (by linarith), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hsplit : (∫ x in (-L : ℝ)..L, F x)
      = (∫ x in (-L : ℝ)..0, F x) + ∫ x in (0 : ℝ)..L, F x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hFi.intervalIntegrable) (hFi.intervalIntegrable)).symm
  have hrefl : (∫ x in (-L : ℝ)..0, F x) = ∫ x in (0 : ℝ)..L, F x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) F
    have h2 : (∫ x in (0 : ℝ)..L, F (-x)) = ∫ x in (0 : ℝ)..L, F x :=
      intervalIntegral.integral_congr fun x _ => heven x
    rw [h2, neg_zero] at h
    exact h.symm
  rw [hrefl] at hsplit
  rw [hIcc, hset, hmean] at hsplit
  linarith

/-- **`(18)` for the explicitly constructed prolate source, with no hypotheses.**  The continuous
polar charge of the source's radial log-source is bounded on every exterior ray, uniformly. -/
theorem exists_prolate_source_polar_charge_bound :
    ∃ (a : ℝ) (F : ℝ → ℝ) (Cf B V : ℝ), 0 < a ∧ 0 ≤ B ∧ 0 ≤ V ∧
      Integrable F ∧ Function.Even F ∧ HasCompactSupport F ∧ (∀ y : ℝ, |F y| ≤ Cf) ∧
      (∫ y : ℝ, F y) = 0 ∧
      ∀ lam α : ℝ, 2 * a ≤ lam → 0 ≤ α →
        |HTGeometry.polarCharge (HTGeometry.radialFullLogSource F lam) α|
          ≤ 4 * (B / Real.sqrt lam) * (V / Real.sqrt lam)
            + 4 * (V / Real.sqrt lam) ^ 2 := by
  obtain ⟨a, Φ, Cf, B, ha, hB0, hsm, heven, hC, hC0, hprim⟩ :=
    exists_prolate_source_polar_primitive_bound
  have hΦc : Continuous Φ := hsm.continuous
  set F : ℝ → ℝ := prolateMeanZeroSource a 2 Φ with hFdef
  set L : ℝ := 3 * a with hLdef
  have hL0 : (0 : ℝ) ≤ L := by rw [hLdef]; positivity
  have hFm : Measurable F := measurable_prolateMeanZeroSource hΦc
  have hFi : Integrable F := integrable_prolateMeanZeroSource ha (by norm_num) hΦc hC hC0
  have hFeven : Function.Even F := even_prolateMeanZeroSource heven
  have hFcs : HasCompactSupport F := hasCompactSupport_prolateMeanZeroSource ha (by norm_num)
  have hFb : ∀ y : ℝ, |F y| ≤ Cf + 2⁻¹ * Cf :=
    fun y => abs_prolateMeanZeroSource_le (by norm_num) hC hC0 y
  have hFmean : (∫ y : ℝ, F y) = 0 :=
    integral_prolateMeanZeroSource ha (by norm_num) hΦc heven hC hC0
  have hzero : ∀ x : ℝ, L < |x| → F x = 0 := by
    intro x hx
    have h1 : x ∉ Icc (-a) a := by
      intro hmem
      have : |x| ≤ a := abs_le.mpr ⟨hmem.1, hmem.2⟩
      rw [hLdef] at hx
      linarith
    have h2 : x ∉ Icc (-(2 * a)) (2 * a) := by
      intro hmem
      have : |x| ≤ 2 * a := abs_le.mpr ⟨hmem.1, hmem.2⟩
      rw [hLdef] at hx
      linarith
    show prolateModeSource a Φ x - 2⁻¹ * prolateModeSource (2 * a) Φ x = 0
    rw [prolateModeSource_eq_zero_of_not_mem ha.le h1,
      prolateModeSource_eq_zero_of_not_mem (by positivity) h2]
    ring
  have hvanIcc : ∀ x : ℝ, x ∉ Icc (-L) L → F x = 0 := by
    intro x hx
    refine hzero x ?_
    by_contra hcon
    push Not at hcon
    exact hx (abs_le.mp hcon)
  have hvan : ∀ x : ℝ, L < x → F x = 0 := by
    intro x hx
    refine hzero x ?_
    rw [abs_of_pos (by linarith : (0 : ℝ) < x)]
    exact hx
  have hLz : F L = 0 := by
    have h1 : (L : ℝ) ∉ Icc (-a) a := by
      intro hmem
      have := hmem.2
      rw [hLdef] at this
      linarith
    have h2 : (L : ℝ) ∉ Icc (-(2 * a)) (2 * a) := by
      intro hmem
      have := hmem.2
      rw [hLdef] at this
      linarith
    show prolateModeSource a Φ L - 2⁻¹ * prolateModeSource (2 * a) Φ L = 0
    rw [prolateModeSource_eq_zero_of_not_mem ha.le h1,
      prolateModeSource_eq_zero_of_not_mem (by positivity) h2]
    ring
  have hvar : BoundedVariationOn F (Icc 0 L) :=
    boundedVariationOn_prolateMeanZeroSource ha (by norm_num) hsm hL0
  have hhalf : (∫ x in (0 : ℝ)..L, F x) = 0 :=
    intervalIntegral_half_eq_zero_of_even hL0 hFi hFeven hvanIcc hFmean
  set V : ℝ := 2 * (eVariationOn F (Icc 0 L)).toReal + |F 0| / 2 with hVdef
  have hV0 : (0 : ℝ) ≤ V := by
    rw [hVdef]
    have h1 : (0 : ℝ) ≤ (eVariationOn F (Icc 0 L)).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ |F 0| := abs_nonneg _
    linarith
  refine ⟨a, F, Cf + 2⁻¹ * Cf, B, V, ha, hB0, hV0, hFi, hFeven, hFcs, hFb, hFmean, ?_⟩
  intro lam α hlam hα
  have hlam0 : (0 : ℝ) < lam := by linarith [mul_pos (by norm_num : (0:ℝ) < 2) ha]
  exact HTGeometry.abs_polarCharge_radialFullLogSource_le_of_measurable
    (L := L) (lam := lam) (a := α) (M := B / Real.sqrt lam) (Cg := Cf + 2⁻¹ * Cf)
    hlam0 hL0 hα hFm hFb hFi.intervalIntegrable hvar hhalf hLz hvan
    (fun t ht => hprim lam t hlam ht)

end RHTower
