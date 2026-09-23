import GaloisForLFunctions.RHTower.HeatMultiplierReal

/-!
# The off-centre Poisson bumps are exponentially small

On the fundamental phase window `(0, π]` every Gaussian bump of the Poisson form except the
central one sits at distance at least `π|n|` from the window, so its total mass is
`O(exp(-π/(4x)))` uniformly for `0 < x ≤ 1`.  This is what makes `W_x dθ/(2π)` a Gaussian
approximate identity at `θ = 0` up to exponentially small corrections.
-/

open Complex Filter Topology

namespace RHTower

/-- A geometric majorant on the integer lattice. -/
theorem summable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
  have hnat : Summable (fun k : ℕ => Real.exp (-c * (k : ℝ))) := by
    have hgeom : Summable (fun k : ℕ => (Real.exp (-c)) ^ k) := by
      refine summable_geometric_of_lt_one (Real.exp_nonneg _) ?_
      rw [Real.exp_lt_one_iff]
      linarith
    refine hgeom.congr fun k => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun k => ?_
    congr 1
    rw [abs_of_nonneg (by positivity)]
    norm_cast
  · refine hnat.congr fun k => ?_
    congr 1
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]

/-- The uniform majorant of the off-centre bumps. -/
noncomputable def heatTailMajorant (n : ℤ) : ℝ :=
  if n = 0 then 0 else Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / 4))

theorem heatTailMajorant_nonneg (n : ℤ) : 0 ≤ heatTailMajorant n := by
  rw [heatTailMajorant]
  split
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem summable_heatTailMajorant : Summable heatTailMajorant := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine Summable.of_nonneg_of_le heatTailMajorant_nonneg
    (fun n => ?_) ((summable_exp_neg_mul_abs (c := Real.pi / 4) (by positivity)).mul_left
      (Real.exp (Real.pi / 4)))
  rw [heatTailMajorant]
  have hsq : |(n : ℝ)| ≤ (n : ℝ) ^ (2 : ℕ) := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast h)
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
      nlinarith [sq_abs ((n : ℝ))]
  have hbound : Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / 4))
      ≤ Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4) * |(n : ℝ)|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  split
  · positivity
  · exact hbound

/-- **Off the centre, the Poisson bumps are exponentially small on the phase window.** -/
theorem heatGauss_le_majorant {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ Real.pi) (n : ℤ) (hn : n ≠ 0) :
    heatGauss x n θ ≤ Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hn)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
  have hdist : Real.pi * |(n : ℝ)| ≤ |θ - 2 * Real.pi * (n : ℝ)| := by
    have hlow : 2 * Real.pi * |(n : ℝ)| - Real.pi ≤ |θ - 2 * Real.pi * (n : ℝ)| := by
      have h1 : |2 * Real.pi * (n : ℝ)| - |θ| ≤ |θ - 2 * Real.pi * (n : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (2 * Real.pi * (n : ℝ)) θ
        rwa [abs_sub_comm] at this
      have h2 : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have h3 : |θ| = θ := abs_of_pos hθ0
      rw [h2, h3] at h1
      linarith
    nlinarith
  have hsq : Real.pi ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ) ≤ (θ - 2 * Real.pi * (n : ℝ)) ^ (2 : ℕ) := by
    have habs : |θ - 2 * Real.pi * (n : ℝ)| ^ (2 : ℕ) = (θ - 2 * Real.pi * (n : ℝ)) ^ (2 : ℕ) := sq_abs _
    have hnn : (0 : ℝ) ≤ Real.pi * |(n : ℝ)| := by positivity
    nlinarith [sq_abs ((n : ℝ))]
  rw [heatGauss, heatTailMajorant, if_neg hn, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hstep : Real.pi * ((n : ℝ) ^ (2 : ℕ)) / (4 * x)
      ≤ (θ - 2 * Real.pi * (n : ℝ)) ^ (2 : ℕ) / (4 * Real.pi * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by nlinarith [sq_abs ((n : ℝ))]
  have hsplit : Real.pi / (4 * x) + Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / 4
      ≤ Real.pi * ((n : ℝ) ^ (2 : ℕ)) / (4 * x) := by
    have hA : Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / 4 ≤ Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / (4 * x) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.mpr hn2)) (sub_nonneg.mpr hx1)]
    have hB : Real.pi / (4 * x) + Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) / (4 * x)
        = Real.pi * ((n : ℝ) ^ (2 : ℕ)) / (4 * x) := by
      field_simp
      ring
    linarith
  linarith

/-- The off-centre part of the Poisson form. -/
noncomputable def heatRemainder (x θ : ℝ) : ℝ :=
  ∑' n : ℤ, (if n = 0 then 0 else heatGauss x n θ)

/-- The total tail mass of the majorant. -/
noncomputable def heatTailConst : ℝ := ∑' n : ℤ, heatTailMajorant n

theorem heatTailConst_nonneg : 0 ≤ heatTailConst :=
  tsum_nonneg heatTailMajorant_nonneg

/-- **The Poisson form splits into the central bump and an off-centre remainder.** -/
theorem tsum_heatGauss_split {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    (∑' n : ℤ, heatGauss x n θ) = heatGauss x 0 θ + heatRemainder x θ :=
  Summable.tsum_eq_add_tsum_ite (summable_heatGauss hx θ) 0

theorem heatRemainder_nonneg (x θ : ℝ) : 0 ≤ heatRemainder x θ := by
  refine tsum_nonneg fun n => ?_
  split
  · exact le_rfl
  · exact (heatGauss_pos x n θ).le

/-- **The off-centre remainder is exponentially small, uniformly on the phase window.** -/
theorem heatRemainder_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ Real.pi) :
    heatRemainder x θ ≤ Real.exp (-(Real.pi / (4 * x))) * heatTailConst := by
  have hterm : ∀ n : ℤ, (if n = 0 then 0 else heatGauss x n θ)
      ≤ Real.exp (-(Real.pi / (4 * x))) * heatTailMajorant n := by
    intro n
    by_cases hn : n = 0
    · have hz : heatTailMajorant n = 0 := by rw [heatTailMajorant, if_pos hn]
      rw [if_pos hn, hz, mul_zero]
    · rw [if_neg hn]
      exact heatGauss_le_majorant hx hx1 hθ0 hθ1 n hn
  have hsummable : Summable (fun n : ℤ => (if n = 0 then 0 else heatGauss x n θ)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm
      (summable_heatTailMajorant.mul_left _)
    split
    · exact le_rfl
    · exact (heatGauss_pos x n θ).le
  rw [heatRemainder, heatTailConst, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hterm hsummable (summable_heatTailMajorant.mul_left _)

end RHTower
