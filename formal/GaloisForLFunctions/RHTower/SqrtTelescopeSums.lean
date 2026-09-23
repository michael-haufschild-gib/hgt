import GaloisForLFunctions.RHTower.CCMNonSchattenBirmanSchwinger

/-!
# Two elementary square-root sums

`Σ_{r ≤ N} r^{-1/2} ≤ 2√N` and `Σ_{R ≤ r ≤ N} r^{-3/2} ≤ 2/√(R-1)`, both by telescoping against
`√r` and `1/√r`.
-/

namespace RHTower

noncomputable section

theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, 1 / Real.sqrt r ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := GaloisForLFunctions.RHTower.inv_sqrt_le_telescope (n := N + 1) (by omega)
    have hcast : (((N + 1 : ℕ) : ℝ) - 1) = (N : ℝ) := by push_cast; ring
    rw [hcast] at hstep
    linarith [ih, hstep]

theorem inv_sqrt_cube_le_telescope {r : ℕ} (hr : 2 ≤ r) :
    1 / Real.sqrt ((r : ℝ) ^ (3 : ℕ))
      ≤ 2 * (1 / Real.sqrt ((r - 1 : ℕ) : ℝ) - 1 / Real.sqrt r) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (0 : ℕ) < r := by omega
    exact_mod_cast this
  have hr1 : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < r - 1 := by omega
    exact_mod_cast this
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs' : 0 < Real.sqrt ((r - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hr1
  have hle : Real.sqrt ((r - 1 : ℕ) : ℝ) ≤ Real.sqrt r := by
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.sub_le r 1
  have hsq : Real.sqrt ((r - 1 : ℕ) : ℝ) ^ (2 : ℕ) = ((r - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt hr1.le
  have hsqr : Real.sqrt (r : ℝ) ^ (2 : ℕ) = (r : ℝ) := Real.sq_sqrt hr0.le
  have hdiff : (r : ℝ) - ((r - 1 : ℕ) : ℝ) = 1 := by
    have hc : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ r := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [hc]
    ring
  have hcube : Real.sqrt ((r : ℝ) ^ (3 : ℕ)) = (r : ℝ) * Real.sqrt r := by
    rw [show ((r : ℝ)) ^ (3 : ℕ) = (r : ℝ) ^ (2 : ℕ) * (r : ℝ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hr0.le]
  have hkey : (Real.sqrt r - Real.sqrt ((r - 1 : ℕ) : ℝ))
      * (Real.sqrt r + Real.sqrt ((r - 1 : ℕ) : ℝ)) = 1 := by
    have h : (Real.sqrt r - Real.sqrt ((r - 1 : ℕ) : ℝ))
        * (Real.sqrt r + Real.sqrt ((r - 1 : ℕ) : ℝ))
        = Real.sqrt r ^ (2 : ℕ) - Real.sqrt ((r - 1 : ℕ) : ℝ) ^ (2 : ℕ) := by ring
    rw [h, hsq, hsqr, hdiff]
  have hrhs : 2 * (1 / Real.sqrt ((r - 1 : ℕ) : ℝ) - 1 / Real.sqrt r)
      = 2 * (Real.sqrt r - Real.sqrt ((r - 1 : ℕ) : ℝ))
        / (Real.sqrt ((r - 1 : ℕ) : ℝ) * Real.sqrt r) := by
    field_simp
  rw [hcube, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hS : (0 : ℝ) < Real.sqrt r + Real.sqrt ((r - 1 : ℕ) : ℝ) := by linarith
  refine le_of_mul_le_mul_right ?_ hS
  have hexpand : 2 * (Real.sqrt r - Real.sqrt ((r - 1 : ℕ) : ℝ)) * ((r : ℝ) * Real.sqrt r)
      * (Real.sqrt r + Real.sqrt ((r - 1 : ℕ) : ℝ))
      = 2 * (r : ℝ) * Real.sqrt r := by
    linear_combination (2 * (r : ℝ) * Real.sqrt r) * hkey
  rw [hexpand]
  have h1 : (r : ℝ) * Real.sqrt ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) * Real.sqrt r :=
    mul_le_mul_of_nonneg_left hle hr0.le
  have h2 : ((r - 1 : ℕ) : ℝ) * Real.sqrt r ≤ (r : ℝ) * Real.sqrt r := by
    have hrm : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
    exact mul_le_mul_of_nonneg_right hrm hs.le
  nlinarith [h1, h2, hsq, hsqr]

theorem sum_inv_sqrt_cube_telescope {R : ℕ} (hR : 2 ≤ R) (N : ℕ) (hN : R - 1 ≤ N) :
    ∑ r ∈ Finset.Icc R N, 1 / Real.sqrt ((r : ℝ) ^ (3 : ℕ))
      ≤ 2 / Real.sqrt ((R - 1 : ℕ) : ℝ) - 2 / Real.sqrt (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hempty : Finset.Icc R (R - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    simp
  | succ N hN ih =>
    have hRN : R ≤ N + 1 := by omega
    rw [Finset.sum_Icc_succ_top hRN]
    have hstep := inv_sqrt_cube_le_telescope (r := N + 1) (by omega)
    have hcast : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by simp
    rw [hcast] at hstep
    have hstep' : 1 / Real.sqrt (((N + 1 : ℕ) : ℝ) ^ (3 : ℕ))
        ≤ 2 / Real.sqrt (N : ℝ) - 2 / Real.sqrt (((N + 1 : ℕ)) : ℝ) := by
      rw [mul_sub, mul_one_div, mul_one_div] at hstep
      exact hstep
    linarith [ih, hstep']

/-- The tail sum of `r^{-3/2}`. -/
theorem sum_inv_sqrt_cube_le {R : ℕ} (hR : 2 ≤ R) (N : ℕ) (hN : R - 1 ≤ N) :
    ∑ r ∈ Finset.Icc R N, 1 / Real.sqrt ((r : ℝ) ^ (3 : ℕ))
      ≤ 2 / Real.sqrt ((R - 1 : ℕ) : ℝ) := by
  have h := sum_inv_sqrt_cube_telescope hR N hN
  have hpos : (0 : ℝ) ≤ 2 / Real.sqrt (N : ℝ) := by positivity
  linarith

end

end RHTower
