import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HighCellRemainder
import GaloisForLFunctions.RHTower.CHMDCompactSourceClass

/-!
# Smooth profiles on refining logarithmic cells

Clipped logarithmic samples of compact `C²` profiles have uniformly bounded square mass
and discrete derivative energy. These bounds pay all prime-weighted successor terms at
order `1/N`. A separate logarithmic quadrature bound identifies the limiting Bochner
source integral, retaining signed profiles throughout.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- Samples of a translated logarithmic profile, flattened below the first cell. -/
def logSamples (f : ℝ → ℝ) (R : ℝ) (N a : ℕ) : ℝ :=
  f (Real.log (max a N : ℕ) - Real.log N - R)

/-- The logarithmic sampling map has adjacent increments at most `1/N`. -/
theorem logSamples_step_le {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (R : ℝ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    |logSamples f R N (k + 1) - logSamples f R N k| ≤ (K : ℝ) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  by_cases hk : k < N
  · simp only [logSamples, max_eq_right (by omega : k + 1 ≤ N), max_eq_right hk.le,
      sub_self, abs_zero]
    positivity
  · have hNk : N ≤ k := by omega
    have hk1 := hN.trans hNk
    have hwidth := logCellWidth_pos hk1
    have hh := hf.norm_sub_le (Real.log ((k + 1 : ℕ) : ℝ) - Real.log N - R)
      (Real.log k - Real.log N - R)
    have he : (Real.log ((k + 1 : ℕ) : ℝ) - Real.log N - R) -
        (Real.log k - Real.log N - R) = logCellWidth k := by
      simp only [logCellWidth, Nat.cast_add, Nat.cast_one]
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, he, abs_of_pos hwidth] at hh
    simp only [logSamples, max_eq_left hNk, max_eq_left (by omega : N ≤ k + 1)]
    calc _ ≤ (K : ℝ) * logCellWidth k := hh
      _ ≤ (K : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left
        ((logCellWidth_le_inv hk1).trans
          (one_div_le_one_div_of_le hN0 (by exact_mod_cast hNk))) K.coe_nonneg
      _ = _ := by ring

/-- A fixed multiplicative horizon contains every nonzero sampled coefficient. -/
theorem logSamples_eq_zero_above {f : ℝ → ℝ} (R : ℝ) {N B : ℕ}
    (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, Real.log B - R < u → f u = 0) :
    ∀ a, N * B < a → logSamples f R N a = 0 := by
  intro a ha
  have hNB : N ≤ N * B := by simpa using Nat.mul_le_mul_left N hB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : Real.log ((N * B : ℕ) : ℝ) < Real.log a :=
    Real.log_lt_log (by positivity) (by exact_mod_cast ha)
  rw [Nat.cast_mul, Real.log_mul hN0.ne' hB0.ne'] at hlog
  rw [logSamples, max_eq_left (by omega : N ≤ a)]
  exact hs _ (by linarith only [hlog])

/-- A bounded profile has uniformly bounded square mass on a fixed multiplicative window. -/
theorem cellMass_logSamples_le {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u, |f u| ≤ C) (R : ℝ) {N : ℕ} (hN : 1 ≤ N) (B : ℕ) :
    cellMass (logSamples f R N) N (N * B) ≤ (B : ℝ) * C ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcard : (Icc N (N * B)).card ≤ N * B := by
    calc _ ≤ (Icc 1 (N * B)).card := card_le_card (Icc_subset_Icc_left hN)
      _ = N * B := by simp
  calc cellMass (logSamples f R N) N (N * B)
      ≤ ∑ _a ∈ Icc N (N * B), (1 / (N : ℝ)) * C ^ 2 := by
        apply sum_le_sum
        intro a ha
        have hNa := (mem_Icc.mp ha).1
        have ha1 := hN.trans hNa
        have habs := hf (Real.log (max a N : ℕ) - Real.log N - R)
        have hsq : logSamples f R N a ^ 2 ≤ C ^ 2 := by
          have hh := mul_le_mul habs habs (abs_nonneg _) hC
          simpa only [← pow_two, sq_abs, logSamples] using hh
        exact mul_le_mul ((logCellWidth_le_inv ha1).trans
          (one_div_le_one_div_of_le hN0 (by exact_mod_cast hNa))) hsq
          (sq_nonneg _) (by positivity)
    _ = ((Icc N (N * B)).card : ℝ) * ((1 / (N : ℝ)) * C ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ ((N * B : ℕ) : ℝ) * ((1 / (N : ℝ)) * C ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (B : ℝ) * C ^ 2 := by
      push_cast
      field_simp

/-- Smoothness pays the entire discrete derivative energy, including the support boundary. -/
theorem sobolevEnergy_logSamples_le {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (R : ℝ) {N : ℕ} (hN : 1 ≤ N) (B : ℕ) :
    biarithmeticSobolevEnergy (logSamples f R N) (N * B) ≤ (B : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  calc biarithmeticSobolevEnergy (logSamples f R N) (N * B)
      ≤ ∑ _k ∈ Icc 1 (N * B), ((N * B : ℕ) : ℝ) * ((K : ℝ) / N) ^ 2 := by
        apply sum_le_sum
        intro k hk
        have hstep := logSamples_step_le hf R hN k
        have hsq : (logSamples f R N (k + 1) - logSamples f R N k) ^ 2 ≤
            ((K : ℝ) / N) ^ 2 := by
          have hh := mul_le_mul hstep hstep (abs_nonneg _) (by positivity)
          simpa only [← pow_two, sq_abs] using hh
        exact mul_le_mul (by exact_mod_cast (mem_Icc.mp hk).2) hsq
          (sq_nonneg _) (Nat.cast_nonneg (N * B))
    _ = ((N * B : ℕ) : ℝ) * (((N * B : ℕ) : ℝ) * ((K : ℝ) / N) ^ 2) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = (B : ℝ) ^ 2 * (K : ℝ) ^ 2 := by
      push_cast
      field_simp

theorem primeWeightSum_nonneg (M : ℕ) : 0 ≤ primeWeightSum M :=
  sum_nonneg fun m _ => div_nonneg
    (mul_nonneg (by norm_num) (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
    (Real.sqrt_nonneg m)

/-- The complete signed successor contribution decays on smooth sampled profiles. -/
theorem abs_primeCellRemainder_logSamples_le {f g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u, |f u| ≤ C) {K : NNReal} (hg : LipschitzWith K g)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B) (M : ℕ)
    (hs : ∀ u, Real.log B - R < u → g u = 0) :
    |primeCellRemainder (logSamples f R N) (logSamples g R N) N (N * B) M| ≤
      (primeWeightSum M * (Real.sqrt ((B : ℝ) * C ^ 2) *
        Real.sqrt ((B : ℝ) ^ 2 * (K : ℝ) ^ 2))) / N := by
  have hbound := abs_primeCellRemainder_le (logSamples f R N) (logSamples g R N)
    hN (N * B) M (logSamples_eq_zero_above R hN hB hs)
  rw [mul_div_assoc]
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (primeWeightSum_nonneg M))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul (Real.sqrt_le_sqrt (cellMass_logSamples_le hC hf R hN B))
    (Real.sqrt_le_sqrt (sobolevEnergy_logSamples_le hg R hN B))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Every pair of compact `C²` source profiles admits one common support horizon and a
uniform vanishing bound for all of its signed prime successor terms. -/
theorem exists_compact_logSamples_rate {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧ ∃ D : ℝ, 0 ≤ D ∧
      (∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0 ∧ g u = 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        |primeCellRemainder (logSamples f R N) (logSamples g R N) N (N * B) B| ≤ D / N := by
  obtain ⟨rf, hrf0, hrf⟩ := hfc.exists_pos_le_norm
  obtain ⟨rg, _hrg0, hrg⟩ := hgc.exists_pos_le_norm
  let R : ℝ := max rf rg
  have hR0 : 0 < R := hrf0.trans_le (le_max_left _ _)
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (2 * R))
  have hB0 : (0 : ℝ) < B := (Real.exp_pos _).trans hB
  have hBnat : 0 < B := by exact_mod_cast hB0
  have hB1 : 1 ≤ B := by omega
  have hlog : 2 * R < Real.log B := by
    have hh := Real.log_lt_log (Real.exp_pos (2 * R)) hB
    simpa only [Real.log_exp] using hh
  have hvanish : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0 ∧ g u = 0 := by
    intro u hu
    have hRu : R ≤ |u| := by
      rcases hu with hu | hu
      · linarith only [hu, neg_le_abs u]
      · linarith only [hu, hlog, le_abs_self u]
    exact ⟨hrf u (by simpa only [Real.norm_eq_abs] using (le_max_left rf rg).trans hRu),
      hrg u (by simpa only [Real.norm_eq_abs] using (le_max_right rf rg).trans hRu)⟩
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hCabs : ∀ u, |f u| ≤ C := fun u => by simpa only [Real.norm_eq_abs] using hC u
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hg hgc
  refine ⟨R, hR0, B, hB1,
    primeWeightSum B * (Real.sqrt ((B : ℝ) * C ^ 2) *
      Real.sqrt ((B : ℝ) ^ 2 * (K : ℝ) ^ 2)),
    mul_nonneg (primeWeightSum_nonneg B) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    hvanish, fun N hN => ?_⟩
  exact abs_primeCellRemainder_logSamples_le hC0 hCabs hK R hN hB1 B
    (fun u hu => (hvanish u (Or.inr hu.le)).2)


/-- The real logarithmic left endpoint after moving the first occupied cell to `-R`. -/
def logEndpoint (R : ℝ) (N a : ℕ) : ℝ := Real.log a - Real.log N - R

private theorem endpoint_increment (R : ℝ) (N a : ℕ) :
    logEndpoint R N (a + 1) - logEndpoint R N a = logCellWidth a := by
  simp only [logEndpoint, logCellWidth, Nat.cast_add, Nat.cast_one]
  ring

/-- A logarithmic rectangle pays its error from its width and the source modulus. -/
theorem abs_logCell_integral_sub_le {H : ℝ → ℝ} {K : NNReal} (hH : LipschitzWith K H)
    (R : ℝ) {N a : ℕ} (hN : 1 ≤ N) (hNa : N ≤ a) :
    |(∫ u in logEndpoint R N a..logEndpoint R N (a + 1), H u) -
      logCellWidth a * H (logEndpoint R N a)| ≤ logCellWidth a * ((K : ℝ) / N) := by
  have ha := hN.trans hNa
  have hwidth := logCellWidth_pos ha
  have hinc := endpoint_increment R N a
  have hend : logEndpoint R N a ≤ logEndpoint R N (a + 1) := by linarith only [hwidth, hinc]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hwN : logCellWidth a ≤ 1 / (N : ℝ) :=
    (logCellWidth_le_inv ha).trans (one_div_le_one_div_of_le hN0 (by exact_mod_cast hNa))
  have hint : IntervalIntegrable H volume (logEndpoint R N a) (logEndpoint R N (a + 1)) :=
    hH.continuous.intervalIntegrable _ _
  have hconst : (∫ _u in logEndpoint R N a..logEndpoint R N (a + 1),
      H (logEndpoint R N a)) = logCellWidth a * H (logEndpoint R N a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hinc]
  rw [← hconst, ← intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
  change ‖∫ u in logEndpoint R N a..logEndpoint R N (a + 1),
    (H u - H (logEndpoint R N a))‖ ≤ _
  calc _ ≤ ∫ u in logEndpoint R N a..logEndpoint R N (a + 1),
        ‖H u - H (logEndpoint R N a)‖ := intervalIntegral.norm_integral_le_integral_norm hend
    _ ≤ ∫ _u in logEndpoint R N a..logEndpoint R N (a + 1), (K : ℝ) / N := by
      apply intervalIntegral.integral_mono_on hend
        (hint.sub (continuous_const.intervalIntegrable _ _)).norm
        (continuous_const.intervalIntegrable _ _)
      intro u hu
      have hmod := hH.norm_sub_le u (logEndpoint R N a)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu.1)] at hmod
      calc _ ≤ (K : ℝ) * (u - logEndpoint R N a) := hmod
        _ ≤ (K : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left
          (by linarith only [hu.2, hinc, hwN]) K.coe_nonneg
        _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, hinc]

/-- Total width stays bounded when the integer scale grows through a fixed ratio. -/
theorem sum_logCellWidth_le {N : ℕ} (hN : 1 ≤ N) (B : ℕ) :
    (∑ a ∈ Icc N (N * B), logCellWidth a) ≤ (B : ℝ) := by
  have h := cellMass_logSamples_le (f := fun _ => (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ => by norm_num) 0 hN B
  simpa only [cellMass, logSamples, one_pow, mul_one] using h

/-- Complete logarithmic rectangles converge to the full Bochner integral of the source. -/
theorem abs_logQuadrature_sub_integral_le {H : ℝ → ℝ} {K : NNReal}
    (hH : LipschitzWith K H) (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → H u = 0) :
    |(∑ a ∈ Icc N (N * B), logCellWidth a * H (logEndpoint R N a)) - ∫ u, H u| ≤
      (B : ℝ) * (K : ℝ) / N := by
  have hNB : N ≤ N * B := by simpa using Nat.mul_le_mul_left N hB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hstart : logEndpoint R N N = -R := by unfold logEndpoint; ring
  have hfinish : Real.log B - R ≤ logEndpoint R N (N * B + 1) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((N * B : ℕ) : ℝ))
      (by exact_mod_cast (Nat.le_add_right (N * B) 1) : ((N * B : ℕ) : ℝ) ≤ (N * B + 1 : ℕ))
    rw [Nat.cast_mul, Real.log_mul hN0.ne' hB0.ne'] at h
    unfold logEndpoint
    linarith only [h]
  have hsupport : Function.support H ⊆ Set.Ioc (logEndpoint R N N)
      (logEndpoint R N (N * B + 1)) := by
    intro u hu
    have hlow : -R < u := by
      by_contra h
      exact hu (hs u (Or.inl (by linarith only [h])))
    have hupp : u < Real.log B - R := by
      by_contra h
      exact hu (hs u (Or.inr (by linarith only [h])))
    exact ⟨by simpa only [hstart] using hlow, hupp.le.trans hfinish⟩
  have hset : Ico N (N * B + 1) = Icc N (N * B) := by
    ext a
    simp only [mem_Ico, mem_Icc]
    omega
  have hsum : (∑ a ∈ Icc N (N * B),
      ∫ u in logEndpoint R N a..logEndpoint R N (a + 1), H u) = ∫ u, H u := by
    rw [← hset, intervalIntegral.sum_integral_adjacent_intervals_Ico (by omega)
      (fun a _ => hH.continuous.intervalIntegrable _ _),
      intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  rw [← hsum, ← sum_sub_distrib]
  calc _ ≤ ∑ a ∈ Icc N (N * B),
        |logCellWidth a * H (logEndpoint R N a) -
          ∫ u in logEndpoint R N a..logEndpoint R N (a + 1), H u| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc N (N * B), logCellWidth a * ((K : ℝ) / N) := by
      apply sum_le_sum
      intro a ha
      rw [abs_sub_comm]
      exact abs_logCell_integral_sub_le hH R hN (mem_Icc.mp ha).1
    _ = (∑ a ∈ Icc N (N * B), logCellWidth a) * ((K : ℝ) / N) := (sum_mul _ _ _).symm
    _ ≤ (B : ℝ) * ((K : ℝ) / N) :=
      mul_le_mul_of_nonneg_right (sum_logCellWidth_le hN B) (by positivity)
    _ = _ := by ring

#print axioms abs_primeCellRemainder_logSamples_le
#print axioms exists_compact_logSamples_rate
#print axioms abs_logQuadrature_sub_integral_le
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
