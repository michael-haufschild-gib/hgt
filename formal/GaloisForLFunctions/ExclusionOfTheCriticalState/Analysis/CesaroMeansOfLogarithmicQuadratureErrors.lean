import GaloisForLFunctions.HTGeometry.DixmierIdeal
import GaloisForLFunctions.RHTower.GammaInvGrowth
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Summing logarithmic quadrature errors in absolute Cesàro mean

An error of integrated size o(1/n) sums to o(T) over n ≤ exp(3T). A pointwise
inverse-square majorant makes the remaining cells negligible throughout [0,T].
-/

noncomputable section
open MeasureTheory Finset Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem partial_cell_mass_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hl : Tendsto (fun n : ℕ => ((n:ℝ)+1)*a n) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, ∀ M : ℕ, 1 ≤ M → ∑ k ∈ range M, a k ≤ B + η*(1+Real.log M) := by
  obtain ⟨L,hL⟩ := eventually_atTop.1 (hl.eventually_lt_const hη)
  let b := fun k : ℕ => if k < L then a k else 0
  refine ⟨∑ k ∈ range L, a k,fun M hM => ?_⟩
  have hb (k : ℕ) : a k ≤ b k + η*(1/((k:ℝ)+1)) := by
    by_cases hk : k < L
    · simp only [b,if_pos hk]; exact le_add_of_nonneg_right (by positivity)
    · simp only [b,if_neg hk,zero_add,mul_one_div]
      rw [le_div_iff₀ (by positivity)]
      simpa only [mul_comm] using (hL k (le_of_not_gt hk)).le
  have hsum : ∑ k ∈ range M, b k ≤ ∑ k ∈ range L, a k := by
    simp only [b,← sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2 (mem_filter.1 hk).2) (fun k _ _ => ha k)
  calc _ ≤ ∑ k ∈ range M, (b k + η*(1/((k:ℝ)+1))) := sum_le_sum fun k _ => hb k
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum]
      exact add_le_add hsum (mul_le_mul_of_nonneg_left (ContinuousLinearMap.sum_inv_succ_le_one_add_log M hM) hη.le)

private theorem summable_inv_shifted_square (m : ℕ) : Summable (fun k : ℕ => 1/((((k+m:ℕ):ℝ))+1)^2) := by
  have hs := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) (m+1)).2 hs
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using h

private theorem abs_cell_sum_le {f : ℕ → ℝ → ℝ} {C t : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, |f k t| ≤ (C*Real.exp (2*t))*(1/((k:ℝ)+1)^2)) {M : ℕ} (hM : 1 ≤ M) :
    |∑' k, f k t| ≤ (∑ k ∈ range M, |f k t|) + C*Real.exp (2*t)/M := by
  let D := C*Real.exp (2*t)
  have hd : 0 ≤ D := mul_nonneg hC (Real.exp_pos _).le
  have hs : Summable (fun k => f k t) := Summable.of_norm_bounded
    (by simpa only [Nat.add_zero] using (summable_inv_shifted_square 0).mul_left D) (by simpa only [Real.norm_eq_abs] using hb)
  have ht := (summable_nat_add_iff M).2 hs
  have hg := (summable_inv_shifted_square M).mul_left D
  have htail : |∑' k : ℕ, f (k+M) t| ≤ D/M := by
    calc _ ≤ ∑' k : ℕ, |f (k+M) t| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ht.norm
      _ ≤ ∑' k : ℕ, D*(1/(((k+M:ℕ):ℝ)+1)^2) := Summable.tsum_le_tsum (fun k => hb (k+M)) ht.abs hg
      _ ≤ _ := by
        rw [tsum_mul_left,← mul_one_div D]
        apply mul_le_mul_of_nonneg_left _ hd
        simpa only [Nat.add_comm M] using HilbertSchmidt.tsum_reciprocal_square_tail_le hM
  rw [← hs.sum_add_tsum_nat_add M]
  exact (abs_add_le ..).trans (add_le_add (abs_sum_le_sum_abs _ _) htail)

/-- Integrated cell errors of order o(1/n), with exponentially confined tails,
have vanishing first absolute Cesàro mean when summed over all integer cells. -/
theorem tendsto_abs_cesaro_of_cell_errors {f : ℕ → ℝ → ℝ} (hi : ∀ k, Integrable (f k))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k t, |f k t| ≤ (C*Real.exp (2*t))*(1/((k:ℝ)+1)^2))
    (hl : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(∫ t, |f n t|)) atTop (𝓝 0)) :
    (∀ T : ℝ, IntegrableOn (fun t => ∑' k, f k t) (Ioc 0 T)) ∧
    Tendsto (fun T : ℝ => (∫ t in Ioc 0 T, |∑' k, f k t|)/T) atTop (𝓝 0) := by
  have hs (T : ℝ) (M : ℕ) (hM : 1 ≤ M) : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      |∑' k, f k t| ≤ (∑ k ∈ range M, |f k t|) + C*Real.exp (2*T)/M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (abs_cell_sum_le hC (fun k => hb k t) hM).trans
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith only [ht.2])) hC) (Nat.cast_nonneg _)
  have hmajor (T : ℝ) (M : ℕ) : IntegrableOn (fun t => (∑ k ∈ range M, |f k t|) + C*Real.exp (2*T)/M) (Ioc 0 T) :=
    (integrable_finsetSum _ (fun k _ => (hi k).abs.integrableOn)).add (by simp)
  have hlocal (T : ℝ) : IntegrableOn (fun t => ∑' k, f k t) (Ioc 0 T) := by
    apply (hmajor T 1).mono' ((AEMeasurable.tsum (fun k => (hi k).aemeasurable)).aestronglyMeasurable.restrict)
    simpa only [Real.norm_eq_abs] using hs T 1 le_rfl
  refine ⟨hlocal,?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε/10
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B,hB⟩ := partial_cell_mass_le (fun n => integral_nonneg fun t => abs_nonneg (f n t)) hl hη
  have hBT : Tendsto (fun T : ℝ => B/T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hCT : Tendsto (fun T : ℝ => C*Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_ge_atTop (1:ℝ),hBT.eventually_lt_const hη,hCT.eventually_lt_const hη] with T hT hBT hCT
  let M := ⌈Real.exp (3*T)⌉₊
  have hT0 := zero_lt_one.trans_le hT
  have hm : Real.exp (3*T) ≤ (M:ℝ) := Nat.le_ceil _
  have hM : 1 ≤ M := Nat.ceil_pos.2 (Real.exp_pos _)
  have hlog : Real.log M ≤ 3*T+1 := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast hM : (0:ℝ)<M)).2
    calc (M:ℝ) ≤ Real.exp (3*T)+1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
      _ ≤ Real.exp (3*T)*Real.exp 1 := by
        have he : 1 ≤ Real.exp (3*T) := Real.one_le_exp (by positivity)
        have he' : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
        calc _ ≤ Real.exp (3*T)*2 := by linarith only [he]
          _ ≤ _ := mul_le_mul_of_nonneg_left he' (Real.exp_pos _).le
      _ = _ := (Real.exp_add ..).symm
  have hmexp : C*Real.exp (2*T)/M ≤ C*Real.exp (-T) := by
    calc _ ≤ C*Real.exp (2*T)/Real.exp (3*T) := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hm
      _ = _ := by rw [mul_div_assoc,← Real.exp_sub]; congr 2; ring
  have hfi : (∫ t in Ioc 0 T, |∑' k, f k t|) ≤
      (∑ k ∈ range M, ∫ t, |f k t|) + T*(C*Real.exp (2*T)/M) := by
    apply (integral_mono_ae (hlocal T).abs (hmajor T M) (hs T M hM)).trans
    rw [integral_add (integrable_finsetSum _ (fun k _ => (hi k).abs.integrableOn)) (by simp),
      integral_finsetSum _ (fun k _ => (hi k).abs.integrableOn)]
    apply add_le_add
    · exact sum_le_sum fun k _ => setIntegral_le_integral (hi k).abs (Eventually.of_forall fun _ => abs_nonneg _)
    · simp [Real.volume_Ioc,hT0.le]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (integral_nonneg fun _ => abs_nonneg _) hT0.le)]
  calc _ ≤ ((B+η*(1+Real.log M))+T*(C*Real.exp (2*T)/M))/T :=
           div_le_div_of_nonneg_right (hfi.trans (add_le_add_left (hB M hM) _)) hT0.le
    _ ≤ B/T + 5*η + C*Real.exp (-T) := by
      rw [add_div,add_div,mul_div_cancel_left₀ _ hT0.ne']
      apply add_le_add _ hmexp
      apply add_le_add_right
      rw [div_le_iff₀ hT0]
      calc _ ≤ η*(1+(3*T+1)) := mul_le_mul_of_nonneg_left (add_le_add_right hlog _) hη.le
        _ ≤ _ := by nlinarith only [mul_nonneg hη.le (sub_nonneg.2 hT)]
    _ < ε := by dsimp only [η] at hBT hCT ⊢; linarith only [hBT,hCT,hε]

#print axioms tendsto_abs_cesaro_of_cell_errors

end GaloisForLFunctions.ExclusionOfTheCriticalState
