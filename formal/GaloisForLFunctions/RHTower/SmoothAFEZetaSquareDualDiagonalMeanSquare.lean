import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualFrozenAffineMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualVariationSourceSeam
import GaloisForLFunctions.HTGeometry.WeightedHolder

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

theorem measurable_smoothAFEZetaSquareDualFrozenSourceField
    (N : ℕ) :
    Measurable (fun t : ℝ =>
      smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t) := by
  unfold smoothAFEZetaSquareDualSourceField
  apply Measurable.tsum
  intro n
  letI : NeZero (n + 1 : ℂ) := ⟨by
    exact_mod_cast (show n + 1 ≠ 0 by omega)⟩
  exact (measurable_const.mul
    ((continuous_const_cpow (n + 1 : ℂ)).comp (by
      unfold linePt
      fun_prop)).measurable).mul measurable_const

theorem exists_norm_smoothAFEZetaSquareDualFrozenSourceField_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N → ∀ t : ℝ,
      ‖smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t‖ ≤
        C * (N : ℝ) := by
  obtain ⟨K, hK, hhigh⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_frozen_high_le
  let C : ℝ := 4 * K * smoothAFEZetaSquareDivisorMajorant
  have hC : 0 ≤ C := by
    dsimp only [C, smoothAFEZetaSquareDivisorMajorant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN t
  let q : ℕ → ℝ := fun n =>
    (4 * K * (N : ℝ)) *
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hq : Summable q :=
    summable_card_divisors_div_natSucc_rpow_three_halves.mul_left
      (4 * K * (N : ℝ))
  let f : ℕ → ℂ := fun n =>
    ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1) *
        smoothAFEZetaSquareDualWeight (N : ℝ)
          ((n + 1 : ℝ) * (N : ℝ))
  have hpoint : ∀ n : ℕ, ‖f n‖ ≤ q n := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hw0 := hhigh hN (show 1 ≤ n + 1 by omega)
    have hw : ‖smoothAFEZetaSquareDualWeight (N : ℝ)
        ((n + 1 : ℝ) * (N : ℝ))‖ ≤
        4 * K * (N : ℝ) / (n + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hw0
    dsimp only [f, q]
    rw [norm_mul, norm_mul, Complex.norm_natCast,
      norm_natSucc_cpow_linePt_sub_one_dualMass]
    calc
      ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖smoothAFEZetaSquareDualWeight (N : ℝ)
              ((n + 1 : ℝ) * (N : ℝ))‖ ≤
        ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (4 * K * (N : ℝ) / (n + 1 : ℝ)) := by gcongr
      _ = (4 * K * (N : ℝ)) *
          (((n + 1).divisors.card : ℝ) /
            (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
        have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
            (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
          rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
            Real.rpow_add hn, Real.rpow_one]
        rw [Real.rpow_neg hn.le, hp]
        field_simp [hn.ne']
  have hfnorm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpoint hq
  have hf : Summable f := Summable.of_norm hfnorm
  unfold smoothAFEZetaSquareDualSourceField
  change ‖∑' n : ℕ, f n‖ ≤ C * (N : ℝ)
  calc
    ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hfnorm
    _ ≤ ∑' n : ℕ, q n :=
      hfnorm.tsum_le_tsum hpoint hq
    _ = C * (N : ℝ) := by
      dsimp only [q, C, smoothAFEZetaSquareDivisorMajorant]
      rw [tsum_mul_left]
      ring

theorem integrableOn_normSq_smoothAFEZetaSquareDualFrozenSourceField
    {N : ℕ} (hN : 4 ≤ N) :
    IntegrableOn (fun t : ℝ =>
      ‖smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_smoothAFEZetaSquareDualFrozenSourceField_le
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := (C * (N : ℝ)) ^ 2) isCompact_Icc.measure_lt_top.ne
    ((measurable_smoothAFEZetaSquareDualFrozenSourceField N).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound hN t) 2

theorem integrableOn_normSq_smoothAFEZetaSquareDualVariationSourceField_diagonal
    {N : ℕ} (hN : 4 ≤ N) :
    IntegrableOn (fun t : ℝ =>
      ‖smoothAFEZetaSquareDualVariationSourceField
        (N : ℝ) (N : ℝ) t t‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) volume := by
  obtain ⟨C, hC, hDbound⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let M : ℝ := (N : ℝ) * C
  have hpoint : ∀ t ∈ Set.Icc (N : ℝ) (2 * N : ℝ),
      ‖smoothAFEZetaSquareDualVariationSourceField
        (N : ℝ) (N : ℝ) t t‖ ≤ M := by
    intro t ht
    have hNN : (N : ℝ) ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by
      exact ⟨le_rfl, by nlinarith⟩
    rw [smoothAFEZetaSquareDualVariationSourceField_eq_intervalIntegral_derivative
      hN hNN ht]
    have hDb : ∀ r ∈ Set.uIoc (N : ℝ) t,
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ≤ C := by
      intro r hr
      rw [Set.uIoc_of_le ht.1] at hr
      exact hDbound (t := t) hN ⟨hr.1.le, hr.2.trans ht.2⟩
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hDb
    exact hnorm.trans (by
      dsimp only [M]
      have hlen : t - (N : ℝ) ≤ (N : ℝ) := by linarith [ht.2]
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      nlinarith)
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := M ^ 2) isCompact_Icc.measure_lt_top.ne
    ((measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal hN).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hpoint t ht) 2

/-- Complete diagonal inner dual source: frozen base plus height variation. -/
theorem exists_integral_Icc_normSq_smoothAFEZetaSquareDualSourceField_diagonal_le :
    ∃ A K B : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ 0 ≤ B ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ 2) ≤
      2 * (5 * Real.pi * Real.exp 1 *
          (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
        (5 * Real.pi / 2) *
          (B * (1 + Real.log (N : ℝ)) ^ 4) * ((N : ℝ) / 2)) +
      2 * (5 * Real.pi * Real.exp 1 * K * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 3 +
        (5 * Real.pi / 4) * A * (N : ℝ) ^ (201 / 200 : ℝ)) := by
  obtain ⟨B, hB, hFrozen⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualFrozenSourceField_le
  obtain ⟨A, K, hA, hK, hVariation⟩ :=
    exists_integral_Icc_normSq_smoothAFEZetaSquareDualVariationSourceField_le_logCube_add_rpow
  refine ⟨A, K, B, hA, hK, hB, ?_⟩
  intro N hN
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let F : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t
  let V : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t
  have hFint : Integrable (fun t => ‖F t‖ ^ 2) (volume.restrict S) := by
    exact integrableOn_normSq_smoothAFEZetaSquareDualFrozenSourceField hN
  have hVint : Integrable (fun t => ‖V t‖ ^ 2) (volume.restrict S) := by
    exact integrableOn_normSq_smoothAFEZetaSquareDualVariationSourceField_diagonal hN
  have hFm : AEStronglyMeasurable F (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualFrozenSourceField N).aestronglyMeasurable.restrict
  have hVm : AEStronglyMeasurable V (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal hN).aestronglyMeasurable.restrict
  have hsumInt := GaloisForLFunctions.HTGeometry.integrable_normSq_add_measure
    hFm hVm hFint hVint
  have hrhs : Integrable (fun t => 2 * ‖F t‖ ^ 2 + 2 * ‖V t‖ ^ 2)
      (volume.restrict S) := (hFint.const_mul 2).add (hVint.const_mul 2)
  have hpoint : ∀ t, ‖F t + V t‖ ^ 2 ≤ 2 * ‖F t‖ ^ 2 + 2 * ‖V t‖ ^ 2 := by
    intro t
    have htri := norm_add_le (F t) (V t)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖F t‖ - ‖V t‖)]
  have hmono :
      (∫ t, ‖F t + V t‖ ^ 2 ∂(volume.restrict S)) ≤
        ∫ t, 2 * ‖F t‖ ^ 2 + 2 * ‖V t‖ ^ 2 ∂(volume.restrict S) :=
    integral_mono hsumInt hrhs hpoint
  have hsplit :
      (∫ t, 2 * ‖F t‖ ^ 2 + 2 * ‖V t‖ ^ 2 ∂(volume.restrict S)) =
        2 * (∫ t, ‖F t‖ ^ 2 ∂(volume.restrict S)) +
          2 * (∫ t, ‖V t‖ ^ 2 ∂(volume.restrict S)) := by
    rw [integral_add (hFint.const_mul 2) (hVint.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hdiagEq :
      (∫ t in S, ‖smoothAFEZetaSquareDualSourceField (N : ℝ) t t‖ ^ 2) =
        ∫ t in S, ‖F t + V t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [F, V]
    rw [smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation hN ht]
  have hcenter : (3 * (N : ℝ) / 2) - (N : ℝ) / 2 = (N : ℝ) := by ring
  have hcenter' : (3 * (N : ℝ) / 2) + (N : ℝ) / 2 = 2 * (N : ℝ) := by ring
  have hH : 1 ≤ (N : ℝ) / 2 := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    linarith
  have hFb := hFrozen (N := N) (center := 3 * (N : ℝ) / 2)
    (H := (N : ℝ) / 2) hN hH
  rw [hcenter, hcenter'] at hFb
  have hVb := hVariation hN
  rw [hdiagEq]
  exact hmono.trans_eq hsplit |>.trans (by
    dsimp only [F, V, S]
    gcongr)

end RHTower
