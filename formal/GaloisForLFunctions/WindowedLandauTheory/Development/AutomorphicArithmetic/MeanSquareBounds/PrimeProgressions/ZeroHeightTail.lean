import GaloisForLFunctions.ShortIntervalPrimesInProgressions.UniformZeroCounts

/-! A logarithmic local zero count yields a logarithmic tail for the Cesàro kernel. -/

open Finset
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

/-- The weights in the discarded height intervals sum to a logarithm divided by the cutoff. -/
theorem sum_log_height_tail {T : ℕ} (hT : 1 ≤ T) (N : ℕ) :
    (∑ n ∈ Ioc T N, Real.log ((n : ℝ) + 3) * (n : ℝ) ^ (-2 : ℝ)) ≤
      2 * (Real.log (4 * (T : ℝ)) + 2) / T := by
  have hT₁ : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT₀ : (0 : ℝ) < T := by linarith
  let A := Real.log (4 * (T : ℝ)) + 2
  have hA : 0 ≤ A := add_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hterm (n : ℕ) (hn : n ∈ Ioc T N) :
      Real.log ((n : ℝ) + 3) * (n : ℝ) ^ (-2 : ℝ) ≤
        (A / Real.sqrt T) * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    have hTn : (T : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
    have hn₁ : (1 : ℝ) ≤ n := hT₁.trans hTn
    have hn₀ : (0 : ℝ) < n := by linarith
    let q : ℝ := n / T
    have hq₁ : 1 ≤ q := (one_le_div hT₀).mpr hTn
    have hq₀ : 0 < q := zero_lt_one.trans_le hq₁
    have hs₁ : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq₁
    have hlogq : Real.log q ≤ 2 * Real.sqrt q := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hq₀)
      rw [Real.log_sqrt hq₀.le] at h
      linarith
    have hsplit : Real.log (4 * (n : ℝ)) = Real.log (4 * (T : ℝ)) + Real.log q := by
      rw [← Real.log_mul (by positivity) hq₀.ne']
      congr 1
      dsimp [q]
      field_simp
    have hlogN : Real.log ((n : ℝ) + 3) ≤ A * Real.sqrt q := by
      calc Real.log ((n : ℝ) + 3) ≤ Real.log (4 * (n : ℝ)) :=
            Real.log_le_log (by positivity) (by linarith)
        _ = Real.log (4 * (T : ℝ)) + Real.log q := hsplit
        _ ≤ A * Real.sqrt q := by
          have h := le_mul_of_one_le_right
            (Real.log_nonneg (show 1 ≤ 4 * (T : ℝ) by linarith)) hs₁
          dsimp [A]
          linarith [hlogq]
    refine (mul_le_mul_of_nonneg_right hlogN (by positivity)).trans_eq ?_
    dsimp [q]
    rw [Real.sqrt_div hn₀.le, Real.sqrt_eq_rpow (n : ℝ)]
    calc A * ((n : ℝ) ^ (1 / 2 : ℝ) / Real.sqrt T) * (n : ℝ) ^ (-2 : ℝ) =
        (A / Real.sqrt T) * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
  calc (∑ n ∈ Ioc T N, Real.log ((n : ℝ) + 3) * (n : ℝ) ^ (-2 : ℝ))
      ≤ ∑ n ∈ Ioc T N, (A / Real.sqrt T) * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
        sum_le_sum hterm
    _ = (A / Real.sqrt T) * ∑ n ∈ Ioc T N, (n : ℝ) ^ (-(3 / 2) : ℝ) :=
        (mul_sum _ _ _).symm
    _ ≤ (A / Real.sqrt T) * (2 / Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_three_halves_le hT N)
          (div_nonneg hA (Real.sqrt_nonneg _))
    _ = 2 * (Real.log (4 * (T : ℝ)) + 2) / T := by
        rw [div_mul_div_comm, Real.mul_self_sqrt hT₀.le, mul_comm A]

/-- A logarithmic bound on each height bin controls the sum of the discarded kernel norms. -/
theorem tsum_height_tail_le {ι : Type*} (height : ι → ℕ) (a : ι → ℝ)
    (hs : Summable a) (ha : ∀ i, 0 ≤ a i) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ (F : Finset ι) (n : ℕ),
      ((F.filter (fun i => height i = n)).card : ℝ) ≤ C * Real.log ((n : ℝ) + 3))
    {T : ℕ} (hT : 1 ≤ T)
    (hbound : ∀ i, T < height i → a i ≤ (height i : ℝ) ^ (-2 : ℝ)) :
    (∑' i, if T < height i then a i else 0) ≤ C * (2 * (Real.log (4 * (T : ℝ)) + 2) / T) := by
  classical
  have hsum : Summable (fun i => if T < height i then a i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs <;> simp [ha])
      (fun i => by split_ifs <;> simp [ha]) hs
  refine hsum.tsum_le_of_sum_le fun F => ?_
  rw [← Finset.sum_filter]
  let G := F.filter (fun i => T < height i)
  change (∑ i ∈ G, a i) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem height hi)]
  have hfiber (n : ℕ) (hn : n ∈ G.image height) :
      ∑ i ∈ G with height i = n, a i ≤ C * (Real.log ((n : ℝ) + 3) * (n : ℝ) ^ (-2 : ℝ)) := by
    have hn' : T < n := by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
      exact (mem_filter.mp hi).2
    calc (∑ i ∈ G with height i = n, a i)
        ≤ ∑ i ∈ G with height i = n, (n : ℝ) ^ (-2 : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          rw [← (mem_filter.mp hi).2]
          exact hbound i ((mem_filter.mp (mem_filter.mp hi).1).2)
      _ ≤ C * (Real.log ((n : ℝ) + 3) * (n : ℝ) ^ (-2 : ℝ)) := by
          rw [sum_const, nsmul_eq_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hcount G n) (by positivity)
  let M := (G.image height).sup id
  have hsub : G.image height ⊆ Ioc T M := by
    intro n hn
    obtain ⟨i, hi, he⟩ := mem_image.mp hn
    exact mem_Ioc.mpr ⟨he ▸ (mem_filter.mp hi).2, le_sup (f := id) hn⟩
  refine (sum_le_sum hfiber).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
    mul_nonneg (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n]))
      (by positivity))).trans (sum_log_height_tail hT M)

end QH.PrimeProgressions
