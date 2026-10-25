import GaloisForLFunctions.BezoutValuationIncidence.UniformVaughanGramsFollowTheirSmoothRankOneTerm
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicLawsForVaughanSuperpositions
import GaloisForLFunctions.BezoutValuationIncidence.TheCompactArithmeticAmplitudesOfVaughanGrams

/-!
The uniform smooth Gram law identifies every subcritical moving-cutoff limit
with an arithmetic amplitude. The convolution diagonal recovers that amplitude,
giving a complete convergence and finite-fiber classification.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The normalized smooth Gram at arithmetic amplitude `a`. -/
def pmVaughanSmoothLimitMatrix (ε a : ℝ) (i j : Fin 5) : ℝ :=
  subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) * a *
    pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j

private theorem smooth_matrix_eq_coefficient (ε : ℝ) (U V : ℕ) (i j : Fin 5) :
    (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
      pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε) =
      pmVaughanSmoothLimitMatrix ε (deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2) i j := by
  rw [pmVaughanSmoothLimitMatrix]
  ring

/-- A limit of the convolution diagonal recovers the actual harmonic amplitude limit. -/
theorem tendsto_pmVaughanSmoothAmplitude_of_centredGram_diagonal_limit
    {ε L : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (hG : Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) 2 2 /
      (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 L)) :
    Tendsto (fun t => deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2)
      atTop (𝓝 ((1 - 2 * ε) / subHalfZetaCoeff ε ^ 2 * L)) := by
  have hβ : 0 < 1 - 2 * ε := by linarith only [hε2]
  have hc : subHalfZetaCoeff ε ≠ 0 := subHalfZetaCoeff_ne_zero hε (by linarith only [hε2])
  have herr := tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term hε hε2 H U V hH 2 2
  have hlead := hG.sub herr
  simp only [sub_sub_cancel, sub_zero] at hlead
  have h := hlead.const_mul ((1 - 2 * ε) / subHalfZetaCoeff ε ^ 2)
  convert h using 1
  funext t
  change deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2 =
    (1 - 2 * ε) / subHalfZetaCoeff ε ^ 2 *
      ((subHalfZetaCoeff ε * deningerHarmonicPartial (U t) * deningerHarmonicPartial (V t)) ^ 2 *
        (-1) * (-1) / (1 - 2 * ε))
  field_simp [hc, hβ.ne']

/-- Convergence of the arithmetic amplitude determines every centered Gram limit. -/
theorem tendsto_pmPronicVaughanCentredGram_of_amplitude_limit
    {ε a : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (ha : Tendsto (fun t => deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2)
      atTop (𝓝 a)) (i j : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
      (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (pmVaughanSmoothLimitMatrix ε a i j)) := by
  have hlead : Tendsto (fun t =>
      (subHalfZetaCoeff ε * deningerHarmonicPartial (U t) * deningerHarmonicPartial (V t)) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε))
      atTop (𝓝 (pmVaughanSmoothLimitMatrix ε a i j)) := by
    simpa only [smooth_matrix_eq_coefficient, pmVaughanSmoothLimitMatrix] using
      ((ha.const_mul (subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε))).mul_const
        (pmPronicVaughanSmoothSigns i)).mul_const (pmPronicVaughanSmoothSigns j)
  have h := (tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term hε hε2 H U V hH i j).add hlead
  simpa only [sub_add_cancel, zero_add] using h

/-- Every finite moving-cutoff Gram limit has an amplitude in the compact arithmetic set. -/
theorem exists_pmVaughanSmoothAmplitude_of_centredGram_limit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (L : Fin 5 → Fin 5 → ℝ)
    (hG : ∀ i j, Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
      (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j))) :
    ∃ a ∈ pmVaughanSmoothAmplitudeSet, ∀ i j, L i j = pmVaughanSmoothLimitMatrix ε a i j := by
  let a : ℝ := (1 - 2 * ε) / subHalfZetaCoeff ε ^ 2 * L 2 2
  have ha := tendsto_pmVaughanSmoothAmplitude_of_centredGram_diagonal_limit hε hε2 H U V hH (hG 2 2)
  have hamem : a ∈ pmVaughanSmoothAmplitudeSet :=
    isCompact_pmVaughanSmoothAmplitudeSet.isClosed.mem_of_tendsto ha
      (Eventually.of_forall fun t => ⟨(U t, V t), rfl⟩)
  refine ⟨a, hamem, fun i j => ?_⟩
  exact tendsto_nhds_unique (hG i j)
    (tendsto_pmPronicVaughanCentredGram_of_amplitude_limit hε hε2 H U V hH ha i j)

/-- At positive cutoffs, zero normalized centered Gram is exactly divergence of the cutoff product. -/
theorem tendsto_pmPronicVaughanCentredGram_zero_iff_product
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hU : ∀ t, 1 ≤ U t) (hV : ∀ t, 1 ≤ V t) :
    (∀ i j : Fin 5, Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
      (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0)) ↔
      Tendsto (fun t => U t * V t) atTop atTop := by
  constructor
  · intro hG
    apply (tendsto_pmVaughanSmoothAmplitude_zero_iff_product U V hU hV).mp
    simpa only [mul_zero] using
      tendsto_pmVaughanSmoothAmplitude_of_centredGram_diagonal_limit hε hε2 H U V hH (hG 2 2)
  · intro hUV i j
    exact tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product hε hε2 H U V hH hUV i j

/-- Bounded moving coefficients have zero normalized packet energy at independently divergent scales. -/
theorem tendsto_pmPronicVaughanCentredPacket_energy_of_horizon_and_product
    {ε B : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (hUV : Tendsto (fun t => U t * V t) atTop atTop)
    (w : ℕ → Fin 5 → ℝ) (hw : ∀ t i, |w t i| ≤ B) :
    Tendsto (fun t =>
      pronicNorm (pmPronicVaughanCentredPacket ε (U t) (V t) (w t)) (H t) ^ 2 /
        (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have h := (tendsto_pronicNorm_pmPronicVaughanCentredPacket_of_horizon_and_product
    hε hε2 H U V hH hUV w hw).pow 2
  simpa only [div_pow,
    Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h

/-- A nonzero moving Gram limit forces an eventually fixed amplitude in one finite cutoff fiber. -/
theorem eventually_finite_fiber_of_nonzero_centredGram_limit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (L : Fin 5 → Fin 5 → ℝ)
    (hG : ∀ i j, Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
      (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j)))
    (hne : ∃ i j, L i j ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ a ∈ pmVaughanSmoothAmplitudeSet ∧ ∃ N : ℕ,
      (∀ i j, L i j = pmVaughanSmoothLimitMatrix ε a i j) ∧
      ∀ᶠ t : ℕ in atTop, U t < N ∧ V t < N ∧
        deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2 = a := by
  let a : ℝ := (1 - 2 * ε) / subHalfZetaCoeff ε ^ 2 * L 2 2
  have ha := tendsto_pmVaughanSmoothAmplitude_of_centredGram_diagonal_limit hε hε2 H U V hH (hG 2 2)
  have hamem : a ∈ pmVaughanSmoothAmplitudeSet :=
    isCompact_pmVaughanSmoothAmplitudeSet.isClosed.mem_of_tendsto ha
      (Eventually.of_forall fun t => ⟨(U t, V t), rfl⟩)
  have hL (i j : Fin 5) : L i j = pmVaughanSmoothLimitMatrix ε a i j :=
    tendsto_nhds_unique (hG i j)
      (tendsto_pmPronicVaughanCentredGram_of_amplitude_limit hε hε2 H U V hH ha i j)
  have ha0 : 0 < a := by
    have hnonneg := pmVaughanSmoothAmplitudeSet_nonneg hamem
    by_contra h
    have hz : a = 0 := le_antisymm (not_lt.mp h) hnonneg
    obtain ⟨i, j, hij⟩ := hne
    apply hij
    simp only [hL i j, hz, pmVaughanSmoothLimitMatrix, mul_zero, zero_mul]
  obtain ⟨N, hN⟩ := eventually_finite_fiber_of_pmVaughanSmoothAmplitude_tendsto_pos U V ha0 ha
  exact ⟨a, ha0, hamem, N, hL, hN⟩

/-- Positive-cutoff Gram convergence is exactly product escape or eventual constancy of a positive amplitude. -/
theorem pmPronicVaughanCentredGram_converges_iff_escape_or_fixed_amplitude
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hU : ∀ t, 1 ≤ U t) (hV : ∀ t, 1 ≤ V t) :
    (∃ L : Fin 5 → Fin 5 → ℝ, ∀ i j,
      Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
        (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j))) ↔
      Tendsto (fun t => U t * V t) atTop atTop ∨
        ∃ a : ℝ, 0 < a ∧ ∀ᶠ t : ℕ in atTop,
          deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2 = a := by
  constructor
  · rintro ⟨L, hG⟩
    by_cases hzero : ∀ i j, L i j = 0
    · left
      apply (tendsto_pmPronicVaughanCentredGram_zero_iff_product hε hε2 H U V hH hU hV).mp
      intro i j
      simpa only [hzero i j] using hG i j
    · right
      push Not at hzero
      obtain ⟨a, ha, _hamem, _N, _hL, hfinite⟩ :=
        eventually_finite_fiber_of_nonzero_centredGram_limit hε hε2 H U V hH L hG hzero
      exact ⟨a, ha, hfinite.mono fun t ht => ht.2.2⟩
  · rintro (hUV | ⟨a, _ha, heq⟩)
    · exact ⟨fun _ _ => 0, fun i j =>
        tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product hε hε2 H U V hH hUV i j⟩
    · have ha : Tendsto (fun t => deningerHarmonicPartial (U t) ^ 2 * deningerHarmonicPartial (V t) ^ 2)
          atTop (𝓝 a) := (tendsto_congr' heq).mpr tendsto_const_nhds
      exact ⟨pmVaughanSmoothLimitMatrix ε a,
        tendsto_pmPronicVaughanCentredGram_of_amplitude_limit hε hε2 H U V hH ha⟩

/-- Every arithmetic smooth matrix is attained, and positive cutoff schedules produce no other finite limits. -/
theorem pmPronicVaughanCentredGram_limit_set_eq
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (L : Fin 5 → Fin 5 → ℝ) :
    (∃ U V : ℕ → ℕ, (∀ t, 1 ≤ U t) ∧ (∀ t, 1 ≤ V t) ∧ ∀ i j,
      Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
        (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j))) ↔
      ∃ a ∈ pmVaughanSmoothAmplitudeSet, ∀ i j, L i j = pmVaughanSmoothLimitMatrix ε a i j := by
  constructor
  · rintro ⟨U, V, _hU, _hV, hG⟩
    exact exists_pmVaughanSmoothAmplitude_of_centredGram_limit hε hε2 H U V hH L hG
  · rintro ⟨a, hamem, hL⟩
    by_cases ha0 : a = 0
    · subst a
      have hUV : Tendsto (fun t : ℕ => (t + 1) * (t + 1)) atTop atTop := by
        apply tendsto_atTop.2
        intro B
        filter_upwards [eventually_ge_atTop B] with t ht
        have hsq : t + 1 ≤ (t + 1) * (t + 1) := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left (t + 1) (by omega : 1 ≤ t + 1)
        exact ht.trans ((Nat.le_succ t).trans hsq)
      refine ⟨fun t => t + 1, fun t => t + 1,
        fun t => Nat.succ_le_succ (Nat.zero_le t),
        fun t => Nat.succ_le_succ (Nat.zero_le t), fun i j => ?_⟩
      rw [hL i j]
      simpa only [pmVaughanSmoothLimitMatrix, mul_zero, zero_mul] using
        tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product hε hε2 H
          (fun t => t + 1) (fun t => t + 1) hH hUV i j
    · obtain ⟨⟨u, v⟩, huv⟩ := hamem
      change deningerHarmonicPartial u ^ 2 * deningerHarmonicPartial v ^ 2 = a at huv
      have hz : deningerHarmonicPartial 0 = 0 := by simp [deningerHarmonicPartial]
      have hu : 1 ≤ u := by
        by_contra h
        have hu0 : u = 0 := by omega
        apply ha0
        rw [← huv, hu0, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      have hv : 1 ≤ v := by
        by_contra h
        have hv0 : v = 0 := by omega
        apply ha0
        rw [← huv, hv0, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      have ha : Tendsto (fun _t : ℕ => deningerHarmonicPartial u ^ 2 * deningerHarmonicPartial v ^ 2)
          atTop (𝓝 a) := by
        rw [huv]
        exact tendsto_const_nhds
      refine ⟨fun _ => u, fun _ => v, fun _ => hu, fun _ => hv, fun i j => ?_⟩
      rw [hL i j]
      exact tendsto_pmPronicVaughanCentredGram_of_amplitude_limit hε hε2 H
        (fun _ => u) (fun _ => v) hH ha i j

#print axioms tendsto_pmVaughanSmoothAmplitude_of_centredGram_diagonal_limit
#print axioms tendsto_pmPronicVaughanCentredGram_of_amplitude_limit
#print axioms exists_pmVaughanSmoothAmplitude_of_centredGram_limit
#print axioms tendsto_pmPronicVaughanCentredGram_zero_iff_product
#print axioms tendsto_pmPronicVaughanCentredPacket_energy_of_horizon_and_product
#print axioms eventually_finite_fiber_of_nonzero_centredGram_limit
#print axioms pmPronicVaughanCentredGram_converges_iff_escape_or_fixed_amplitude
#print axioms pmPronicVaughanCentredGram_limit_set_eq
end GaloisForLFunctions.BezoutValuationIncidence
