import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimeClockGrowth

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

private def sourcePredictorVec (a : ℕ → ℝ) (N l : ℕ) : Lp ℝ 2 cellMeasure :=
  ∑ i ∈ range N, a (i + 1) • predictorVec (i + 1) (clock l)

private theorem sourcePredictorVec_mem (a : ℕ → ℝ) (N l : ℕ) :
    sourcePredictorVec a N l ∈ historySpace l := by
  unfold sourcePredictorVec
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact Submodule.smul_mem _ _ (predictorVec_mem (i + 1) l)

private theorem sourceVec_sub_predictor_norm_le
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N l : ℕ) :
    ‖sourceVec a N - sourcePredictorVec a N l‖ ≤
      (N : ℝ) * Real.sqrt (1 / ((clock l : ℝ) + 1)) := by
  let δ : ℝ := Real.sqrt (1 / ((clock l : ℝ) + 1))
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ 2 = 1 / ((clock l : ℝ) + 1) := by
    exact Real.sq_sqrt (by positivity)
  have hterm (i : ℕ) :
      ‖a (i + 1) • (residueVec (i + 1) - predictorVec (i + 1) (clock l))‖ ≤ δ := by
    have hres := residue_prediction_error (i + 1) (clock l)
    have hnorm : ‖residueVec (i + 1) - predictorVec (i + 1) (clock l)‖ ≤ δ := by
      nlinarith [norm_nonneg (residueVec (i + 1) - predictorVec (i + 1) (clock l))]
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |a (i + 1)| * ‖residueVec (i + 1) - predictorVec (i + 1) (clock l)‖ ≤
        ‖residueVec (i + 1) - predictorVec (i + 1) (clock l)‖ := by
          exact mul_le_of_le_one_left (norm_nonneg _) (ha _)
      _ ≤ δ := hnorm
  have hsum : sourceVec a N - sourcePredictorVec a N l =
      ∑ i ∈ range N, a (i + 1) •
        (residueVec (i + 1) - predictorVec (i + 1) (clock l)) := by
    simp only [sourceVec, sourcePredictorVec, ← Finset.sum_sub_distrib, smul_sub]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ range N,
        ‖a (i + 1) • (residueVec (i + 1) - predictorVec (i + 1) (clock l))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ range N, δ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (N : ℝ) * δ := by simp

private theorem source_layer_norm_le
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N l : ℕ) :
    ‖historyLayer l (sourceVec a N)‖ ≤
      2 * (N : ℝ) * Real.sqrt (1 / ((clock l : ℝ) + 1)) := by
  let e := sourceVec a N - sourcePredictorVec a N l
  have hzero : historyLayer l (sourcePredictorVec a N l) = 0 :=
    historyLayer_apply_eq_zero_of_mem l _ (sourcePredictorVec_mem a N l)
  have hrewrite : historyLayer l (sourceVec a N) = historyLayer l e := by
    rw [show sourceVec a N = e + sourcePredictorVec a N l by simp [e]]
    rw [map_add, hzero, add_zero]
  rw [hrewrite]
  change ‖(historySpace (l + 1)).starProjection e -
      (historySpace l).starProjection e‖ ≤ _
  have hu := (historySpace (l + 1)).norm_starProjection_apply_le e
  have hl := (historySpace l).norm_starProjection_apply_le e
  calc
    _ ≤ ‖(historySpace (l + 1)).starProjection e‖ +
        ‖(historySpace l).starProjection e‖ := norm_sub_le _ _
    _ ≤ 2 * ‖e‖ := by linarith
    _ ≤ 2 * (N : ℝ) * Real.sqrt (1 / ((clock l : ℝ) + 1)) := by
      have h := sourceVec_sub_predictor_norm_le a ha N l
      nlinarith

theorem source_layer_energy_le_clock_tail
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N l : ℕ) :
    ‖historyLayer l (sourceVec a N)‖ ^ (2 : ℕ) ≤
      4 * (N : ℝ) ^ 2 / ((clock l : ℝ) + 1) := by
  have h := source_layer_norm_le a ha N l
  have hsqrt : (Real.sqrt (1 / ((clock l : ℝ) + 1))) ^ 2 =
      1 / ((clock l : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 2 * (N : ℝ) * Real.sqrt (1 / ((clock l : ℝ) + 1)))).mpr h
  calc
    _ ≤ (2 * (N : ℝ) * Real.sqrt (1 / ((clock l : ℝ) + 1))) ^ 2 := hsq
    _ = 4 * (N : ℝ) ^ 2 / ((clock l : ℝ) + 1) := by
      rw [mul_pow, mul_pow, hsqrt]
      ring

theorem moebius_source_layer_energy_le_clock_tail (N l : ℕ) :
    ‖historyLayer l
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) ≤
      4 * (N : ℝ) ^ 2 / ((clock l : ℝ) + 1) := by
  apply source_layer_energy_le_clock_tail
  intro n
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem predictableDrift_layer_energy_le_clock_tail (N l : ℕ) (hlN : l < N) :
    ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ) ≤
      (8 * (N : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := by
  have hsource := moebius_source_layer_energy_le_clock_tail N l
  have hinnovation := signedInnovation_sq_le l
  have hnorm : ‖historyLayer l (predictableDrift N)‖ ≤
      ‖historyLayer l
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ +
        ‖signedInnovation l‖ := by
    rw [historyLayer_predictableDrift_eq_historyLayer_source_sub_innovation,
      if_pos hlN]
    exact norm_sub_le _ _
  have hsq := (sq_le_sq₀ (norm_nonneg (historyLayer l (predictableDrift N)))
    (by positivity : 0 ≤
      ‖historyLayer l
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ +
        ‖signedInnovation l‖)).mpr hnorm
  calc
    _ ≤ (‖historyLayer l
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ +
        ‖signedInnovation l‖) ^ 2 := hsq
    _ ≤ 2 * ‖historyLayer l
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ 2 +
        2 * ‖signedInnovation l‖ ^ 2 := by
          nlinarith [sq_nonneg (‖historyLayer l
            (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ -
            ‖signedInnovation l‖)]
    _ ≤ (8 * (N : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := by
      calc
        _ ≤ 2 * (4 * (N : ℝ) ^ 2 / ((clock l : ℝ) + 1)) +
            2 * (1 / ((clock l : ℝ) + 1)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hsource (by norm_num))
            (mul_le_mul_of_nonneg_left hinnovation (by norm_num))
        _ = (8 * (N : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := by ring

theorem predictableDrift_upperHalf_layer_energy_tendsto_zero
    (N : ℕ → ℕ) (hlo : ∀ l, l + 1 ≤ N l)
    (hhi : ∀ l, N l ≤ 2 * (l + 1)) :
    Tendsto (fun l => ‖historyLayer l (predictableDrift (N l))‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun l : ℕ => 34 * (((l + 1 : ℕ) : ℝ) ^ 2 / (clock l : ℝ)))
      atTop (𝓝 0) := by
    have hshift : Tendsto (fun l : ℕ =>
        (((l + 1 : ℕ) : ℝ) ^ 2 / (clock l : ℝ))) atTop (𝓝 0) := by
      have hbase : Tendsto (fun l : ℕ =>
          4 * ((l : ℝ) ^ 2 / (clock l : ℝ))) atTop (𝓝 0) := by
        simpa using tendsto_sq_div_clock_zero.const_mul (4 : ℝ)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase
      · exact Filter.Eventually.of_forall fun l => div_nonneg (sq_nonneg _) (by positivity)
      · filter_upwards [eventually_ge_atTop (1 : ℕ)] with l hl
        have hnat : l + 1 ≤ 2 * l := by omega
        have hreal : (((l + 1 : ℕ) : ℝ)) ≤ 2 * (l : ℝ) := by exact_mod_cast hnat
        have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (((l + 1 : ℕ) : ℝ)))
          (by positivity : 0 ≤ 2 * (l : ℝ))).mpr hreal
        have hC : (0 : ℝ) ≤ clock l := Nat.cast_nonneg _
        calc
          _ ≤ 4 * (l : ℝ) ^ 2 / (clock l : ℝ) := by
            apply div_le_div_of_nonneg_right _ hC
            nlinarith
          _ = 4 * ((l : ℝ) ^ 2 / (clock l : ℝ)) := by ring
    simpa using hshift.const_mul (34 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun l => pow_nonneg (norm_nonneg _) _
  · exact Filter.Eventually.of_forall fun l => by
      have hlN : l < N l := by have h := hlo l; omega
      have hE := predictableDrift_layer_energy_le_clock_tail (N l) l hlN
      have hNreal : (N l : ℝ) ≤ 2 * ((l + 1 : ℕ) : ℝ) := by
        exact_mod_cast hhi l
      have hsq : (N l : ℝ) ^ 2 ≤ 4 * (((l + 1 : ℕ) : ℝ) ^ 2) := by
        nlinarith [(sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) (N l))
          (by positivity : 0 ≤ 2 * ((l + 1 : ℕ) : ℝ))).mpr hNreal]
      have hL : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)
      have hLsq : (1 : ℝ) ≤ (((l + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
      have hnum : 8 * (N l : ℝ) ^ 2 + 2 ≤
          34 * (((l + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
      have hC : (0 : ℝ) < clock l := by exact_mod_cast clock_pos l
      calc
        _ ≤ (8 * (N l : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := hE
        _ ≤ 34 * (((l + 1 : ℕ) : ℝ) ^ 2) / ((clock l : ℝ) + 1) :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ 34 * (((l + 1 : ℕ) : ℝ) ^ 2) / (clock l : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hC (by linarith)
        _ = 34 * (((l + 1 : ℕ) : ℝ) ^ 2 / (clock l : ℝ)) := by ring

end RHTower.DeletionResidueMartingale
