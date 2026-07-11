import Mathlib.Analysis.Calculus.MeanValue
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# The prolate Wronskian: conserved, and killed by the singular endpoints

For two solutions `ψ₁, ψ₂` of the same prolate eigenvalue problem `P_c ψ = χ·ψ`, the modified
Wronskian `W = (1−y²)·(ψ₁ψ₂' − ψ₂ψ₁')` is a conserved quantity: its derivative vanishes
identically (`deriv_prolateWronskian_eq_zero`), by the exact cancellation between the
`−2y`-drift of the weight `1−y²` and the first-order term of the equation.  Hence `W` is a
global constant (`prolateWronskian_apply_eq`).

At the singular endpoint `y = 1` the weight vanishes, so if both solutions and their
derivatives stay bounded on `[0,1)` the constant is squeezed to zero
(`prolateWronskian_eq_zero`), and inside the band the two solutions satisfy the first-order
proportionality relation `ψ₁·ψ₂' = ψ₂·ψ₁'` (`prolate_firstOrder_relation`).  This is the
one-dimensionality mechanism of the singular Sturm–Liouville problem on the band: bounded
solutions of a common eigenvalue are pointwise proportional in first order — no boundary
conditions, the vanishing weight replaces them.
-/

open Filter

namespace RHTower

/-- The modified Wronskian of the prolate problem: `(1−y²)·(ψ₁ψ₂' − ψ₂ψ₁')`. -/
noncomputable def prolateWronskian (ψ₁ ψ₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 - y ^ 2) * (ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y)

theorem hasDerivAt_prolateWronskian {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂)) (y : ℝ) :
    HasDerivAt (prolateWronskian ψ₁ ψ₂)
      (-(2 * y) * (ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y)
        + (1 - y ^ 2) * ((deriv ψ₁ y * deriv ψ₂ y + ψ₁ y * deriv (deriv ψ₂) y)
          - (deriv ψ₂ y * deriv ψ₁ y + ψ₂ y * deriv (deriv ψ₁) y))) y := by
  have hU : HasDerivAt (fun t => ψ₁ t * deriv ψ₂ t - ψ₂ t * deriv ψ₁ t)
      ((deriv ψ₁ y * deriv ψ₂ y + ψ₁ y * deriv (deriv ψ₂) y)
        - (deriv ψ₂ y * deriv ψ₁ y + ψ₂ y * deriv (deriv ψ₁) y)) y :=
    ((h₁1 y).hasDerivAt.mul (h₂2 y).hasDerivAt).sub
      ((h₂1 y).hasDerivAt.mul (h₁2 y).hasDerivAt)
  have hP : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_sub 1
  exact hP.mul hU

/-- **The prolate Wronskian is conserved**: for two solutions of the same eigenvalue problem
its derivative vanishes identically. -/
theorem deriv_prolateWronskian_eq_zero {c χ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y) (y : ℝ) :
    deriv (prolateWronskian ψ₁ ψ₂) y = 0 := by
  rw [(hasDerivAt_prolateWronskian h₁1 h₁2 h₂1 h₂2 y).deriv]
  have k₁ : (1 - y ^ 2) * deriv (deriv ψ₁) y
      = χ * ψ₁ y + 2 * y * deriv ψ₁ y + c ^ 2 * y ^ 2 * ψ₁ y := by
    have h := he₁ y
    simp only [prolateSLAction] at h
    linarith
  have k₂ : (1 - y ^ 2) * deriv (deriv ψ₂) y
      = χ * ψ₂ y + 2 * y * deriv ψ₂ y + c ^ 2 * y ^ 2 * ψ₂ y := by
    have h := he₂ y
    simp only [prolateSLAction] at h
    linarith
  linear_combination ψ₁ y * k₂ - ψ₂ y * k₁

theorem prolateWronskian_apply_eq {c χ : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y) (y z : ℝ) :
    prolateWronskian ψ₁ ψ₂ y = prolateWronskian ψ₁ ψ₂ z :=
  is_const_of_deriv_eq_zero
    (fun t => (hasDerivAt_prolateWronskian h₁1 h₁2 h₂1 h₂2 t).differentiableAt)
    (deriv_prolateWronskian_eq_zero h₁1 h₁2 h₂1 h₂2 he₁ he₂) y z

/-- **The singular endpoint kills the Wronskian.**  If both solutions and their derivatives are
bounded on `[0,1)`, the conserved Wronskian is squeezed to zero by the vanishing weight
`1−y² → 0` at the endpoint. -/
theorem prolateWronskian_eq_zero {c χ C : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y)
    (hb₁ : ∀ y ∈ Set.Ico (0 : ℝ) 1, |ψ₁ y| ≤ C ∧ |deriv ψ₁ y| ≤ C)
    (hb₂ : ∀ y ∈ Set.Ico (0 : ℝ) 1, |ψ₂ y| ≤ C ∧ |deriv ψ₂ y| ≤ C) (z : ℝ) :
    prolateWronskian ψ₁ ψ₂ z = 0 := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans ((hb₁ 0 ⟨le_refl 0, by norm_num⟩).1)
  haveI hne : (nhdsWithin (1 : ℝ) (Set.Ico (0 : ℝ) 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact Set.right_mem_Icc.mpr (by norm_num)
  have hsq : Tendsto (prolateWronskian ψ₁ ψ₂) (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 0) := by
    apply squeeze_zero_norm' (a := fun y : ℝ => 2 * C ^ 2 * (1 - y ^ 2))
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      obtain ⟨hy0, hy1⟩ := hy
      have hy2 : (0 : ℝ) ≤ 1 - y ^ 2 := by nlinarith
      have p1 : |ψ₁ y * deriv ψ₂ y| ≤ C * C := by
        rw [abs_mul]
        exact mul_le_mul (hb₁ y ⟨hy0, hy1⟩).1 (hb₂ y ⟨hy0, hy1⟩).2 (abs_nonneg _) hC0
      have p2 : |ψ₂ y * deriv ψ₁ y| ≤ C * C := by
        rw [abs_mul]
        exact mul_le_mul (hb₂ y ⟨hy0, hy1⟩).1 (hb₁ y ⟨hy0, hy1⟩).2 (abs_nonneg _) hC0
      have habs : |ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y|
          ≤ |ψ₁ y * deriv ψ₂ y| + |ψ₂ y * deriv ψ₁ y| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_neg]))
      have hU : |ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y| ≤ 2 * C ^ 2 := by
        calc |ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y|
            ≤ |ψ₁ y * deriv ψ₂ y| + |ψ₂ y * deriv ψ₁ y| := habs
          _ ≤ C * C + C * C := add_le_add p1 p2
          _ = 2 * C ^ 2 := by ring
      simp only [prolateWronskian, Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg hy2]
      calc (1 - y ^ 2) * |ψ₁ y * deriv ψ₂ y - ψ₂ y * deriv ψ₁ y|
          ≤ (1 - y ^ 2) * (2 * C ^ 2) := mul_le_mul_of_nonneg_left hU hy2
        _ = 2 * C ^ 2 * (1 - y ^ 2) := by ring
    · have hb : Tendsto (fun y : ℝ => 2 * C ^ 2 * (1 - y ^ 2)) (nhds 1)
          (nhds (2 * C ^ 2 * (1 - (1 : ℝ) ^ 2))) :=
        (continuous_const.mul (continuous_const.sub (continuous_pow 2))).tendsto 1
      have h0 : 2 * C ^ 2 * (1 - (1 : ℝ) ^ 2) = 0 := by norm_num
      rw [h0] at hb
      exact tendsto_nhdsWithin_of_tendsto_nhds hb
  have hconst : Tendsto (prolateWronskian ψ₁ ψ₂) (nhdsWithin 1 (Set.Ico (0 : ℝ) 1))
      (nhds (prolateWronskian ψ₁ ψ₂ z)) := by
    have hcz : ∀ y : ℝ, prolateWronskian ψ₁ ψ₂ z = prolateWronskian ψ₁ ψ₂ y := fun y =>
      prolateWronskian_apply_eq h₁1 h₁2 h₂1 h₂2 he₁ he₂ z y
    exact Tendsto.congr hcz tendsto_const_nhds
  exact tendsto_nhds_unique hconst hsq

/-- **First-order proportionality inside the band.**  Two bounded solutions of the same prolate
eigenvalue problem satisfy `ψ₁·ψ₂' = ψ₂·ψ₁'` at every interior point: the one-dimensionality
mechanism of the singular problem. -/
theorem prolate_firstOrder_relation {c χ C : ℝ} {ψ₁ ψ₂ : ℝ → ℝ}
    (h₁1 : Differentiable ℝ ψ₁) (h₁2 : Differentiable ℝ (deriv ψ₁))
    (h₂1 : Differentiable ℝ ψ₂) (h₂2 : Differentiable ℝ (deriv ψ₂))
    (he₁ : ∀ y, prolateSLAction c ψ₁ y = χ * ψ₁ y)
    (he₂ : ∀ y, prolateSLAction c ψ₂ y = χ * ψ₂ y)
    (hb₁ : ∀ y ∈ Set.Ico (0 : ℝ) 1, |ψ₁ y| ≤ C ∧ |deriv ψ₁ y| ≤ C)
    (hb₂ : ∀ y ∈ Set.Ico (0 : ℝ) 1, |ψ₂ y| ≤ C ∧ |deriv ψ₂ y| ≤ C)
    {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ψ₁ y * deriv ψ₂ y = ψ₂ y * deriv ψ₁ y := by
  have hW := prolateWronskian_eq_zero h₁1 h₁2 h₂1 h₂2 he₁ he₂ hb₁ hb₂ y
  simp only [prolateWronskian] at hW
  have hpos : (0 : ℝ) < 1 - y ^ 2 := by
    nlinarith [mul_pos (by linarith [hy.2] : (0 : ℝ) < 1 - y)
      (by linarith [hy.1] : (0 : ℝ) < 1 + y)]
  rcases mul_eq_zero.mp hW with h | h
  · exact absurd h hpos.ne'
  · linarith [sub_eq_zero.mp h]

end RHTower
