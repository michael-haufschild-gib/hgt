import GaloisForLFunctions.HTGeometry.ChargedTwoSiteVarianceDefect

/-! # Actual strong-coupling paths approaching the electrostatic variance bound -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- Coupling path kept strictly inside the massless instability window at every nonzero charge gap. -/
def chargedTwoSiteStrongCoupling (d : ℝ) (j : ℕ) : ℝ := Real.log (d ^ (2 : ℕ) + (2 : ℝ) ^ (j + 1))

/-- The actual positive edge coupling is exactly the prescribed geometric path. -/
theorem chargedTwoSiteStrongCoupling_exp (d : ℝ) (j : ℕ) :
    Real.exp (chargedTwoSiteStrongCoupling d j) = d ^ (2 : ℕ) + (2 : ℝ) ^ (j + 1) := by
  exact Real.exp_log (add_pos_of_nonneg_of_pos (sq_nonneg d) (pow_pos (by norm_num) _))

/-- Every stage is an actual growing mode precisely when the fixed charge gap is nonzero. -/
theorem chargedTwoSiteStrongCoupling_growing_iff (c d : ℝ) (j : ℕ) :
    (ChargedTwoSiteHasMode (chargedTwoSiteStrongCoupling d j) 0 c d
      (chargedTwoSiteGrowingFrequency (chargedTwoSiteStrongCoupling d j) 0 c d) ∧
      0 < (chargedTwoSiteGrowingFrequency (chargedTwoSiteStrongCoupling d j) 0 c d).im) ↔ d ≠ 0 := by
  rw [chargedTwoSiteGrowingFrequency_mode_iff, chargedTwoSiteStrongCoupling_exp]
  constructor
  · rintro ⟨h, _⟩ hz
    rw [hz] at h
    norm_num at h
  · intro hd
    refine ⟨?_, ?_⟩
    · simpa using sq_pos_of_ne_zero hd
    · nlinarith [sq_nonneg d, pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1)]

/-- The exact growth deficit admits a geometric upper bound along the actual coupling path. -/
theorem chargedTwoSiteStrongCoupling_defect_bound (d : ℝ) (j : ℕ) :
    0 ≤ d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d ∧
      d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d ≤
        4 * d ^ (4 : ℕ) * (1 / 2 : ℝ) ^ (j + 1) := by
  let k := chargedTwoSiteStrongCoupling d j
  let D := chargedTwoSiteBase k 0 + 2 * d ^ (2 : ℕ) +
    Real.sqrt ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k 0 * d ^ (2 : ℕ))
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [chargedTwoSiteBase_pos k 0, sq_nonneg d,
      Real.sqrt_nonneg ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k 0 * d ^ (2 : ℕ))]
  have hLB : (2 : ℝ) ^ (j + 1) ≤ D := by
    dsimp [D]
    have he : chargedTwoSiteBase k 0 = d ^ (2 : ℕ) + (2 : ℝ) ^ (j + 1) := by
      simp only [chargedTwoSiteBase, k, chargedTwoSiteStrongCoupling_exp, zero_pow (by omega : (2 : ℕ) ≠ 0), add_zero]
    rw [he]
    nlinarith [sq_nonneg d, Real.sqrt_nonneg ((Real.exp k) ^ (2 : ℕ) + 4 * (d ^ (2 : ℕ) + (2 : ℝ) ^ (j + 1)) * d ^ (2 : ℕ))]
  have hid : (d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare k 0 d) * D = 4 * d ^ (4 : ℕ) := by
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul, zero_add] using
      chargedTwoSiteGrowthSquare_variance_defect k 0 d
  have hq : d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare k 0 d = (4 * d ^ (4 : ℕ)) / D := by
    field_simp [hD.ne']
    <;> nlinarith [hid]
  refine ⟨sub_nonneg.mpr (chargedTwoSiteGrowthSquare_le_variance k 0 d), ?_⟩
  change d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare k 0 d ≤ _
  rw [hq]
  calc
    _ ≤ (4 * d ^ (4 : ℕ)) / ((2 : ℝ) ^ (j + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by norm_num) _) hLB
    _ = _ := by simp only [div_eq_mul_inv, one_mul, inv_pow]

/-- The actual signed growth branch converges to the exact electrostatic variance. -/
theorem chargedTwoSiteStrongCoupling_growth_limit (d : ℝ) :
    Tendsto (fun j => chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d) atTop (nhds (d ^ (2 : ℕ))) := by
  have hg : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto (fun j : ℕ => 4 * d ^ (4 : ℕ) * (1 / 2 : ℝ) ^ (j + 1)) atTop (nhds 0) := by
    have hf : (fun j : ℕ => 4 * d ^ (4 : ℕ) * (1 / 2 : ℝ) ^ (j + 1)) =
        (fun j : ℕ => 4 * d ^ (4 : ℕ) * ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ))) := by
      funext j
      rw [pow_succ (1 / 2 : ℝ) j]
    rw [hf]
    simpa only [mul_zero, zero_mul] using (hg.mul_const (1 / 2 : ℝ)).const_mul (4 * d ^ (4 : ℕ))
  have hd : Tendsto (fun j => d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun j => (chargedTwoSiteStrongCoupling_defect_bound d j).1)
      (fun j => (chargedTwoSiteStrongCoupling_defect_bound d j).2)
  have h : Tendsto (fun j => d ^ (2 : ℕ) - (d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d))
      atTop (nhds (d ^ (2 : ℕ) - 0)) := tendsto_const_nhds.sub hd
  have hf : (fun j => d ^ (2 : ℕ) - (d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d)) =
      (fun j => chargedTwoSiteGrowthSquare (chargedTwoSiteStrongCoupling d j) 0 d) := by
    funext j
    ring
  rw [hf, sub_zero] at h
  exact h

end
end GaloisForLFunctions.HTGeometry
