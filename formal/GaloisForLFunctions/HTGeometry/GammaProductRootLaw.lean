/-
# The root law for a finite Gamma product of total rate one

A finite product of Gamma values along rays of rates `c i` summing to one, divided by `k!`, has
`k`-th root converging to `∏ c i ^ c i`.  Each factor contributes `(c i/e)^{c i} k^{c i}`; the
powers of `k` multiply to `k`, which cancels the factorial root `k/e`, and the `e`'s cancel exactly
because the rates sum to one.

Main results:
* `prod_rpow_const` — a constant base with a family of exponents.
* `tendsto_div_factorial_rpow_inv` — `k/(k!)^{1/k} → e`.
* `tendsto_prod_norm_Gamma_div_factorial_rpow_inv` —
  **`(∏ ‖Γ(c_i k + β_i)‖ / k!)^{1/k} → ∏ c_i^{c_i}`**.
-/
import GaloisForLFunctions.HTGeometry.GammaVerticalRootAsymptotic

open Filter Topology Real Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A constant base carries a family of exponents to their sum. -/
theorem prod_rpow_const {ι : Type*} (s : Finset ι) {x : ℝ} (hx : 0 < x) (c : ι → ℝ) :
    ∏ i ∈ s, x ^ (c i) = x ^ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.rpow_add hx]

/-- **The reciprocal factorial root**: `k/(k!)^{1/k} → e`. -/
theorem tendsto_div_factorial_rpow_inv :
    Tendsto (fun k : ℕ => (k : ℝ) / (k.factorial : ℝ) ^ (1 / (k : ℝ))) atTop
      (𝓝 (Real.exp 1)) := by
  have h := tendsto_factorial_rpow_inv_div
  have hne : (1 / Real.exp 1 : ℝ) ≠ 0 := by positivity
  have hinv := h.inv₀ hne
  have heq : ((1 : ℝ) / Real.exp 1)⁻¹ = Real.exp 1 := by
    field_simp
  rw [heq] at hinv
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k _
  show ((k.factorial : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ))⁻¹ = (k : ℝ) / (k.factorial : ℝ) ^ (1 / (k : ℝ))
  rw [inv_div]

/-- **The root law for a finite Gamma product of total rate one.** -/
theorem tendsto_prod_norm_Gamma_div_factorial_rpow_inv
    {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1) (β : ι → ℂ) :
    Tendsto (fun k : ℕ => ((∏ i, ‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖)
        / (k.factorial : ℝ)) ^ (1 / (k : ℝ))) atTop
      (𝓝 (∏ i, (c i) ^ (c i))) := by
  classical
  have hi : ∀ i : ι, Tendsto (fun k : ℕ =>
      ‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖ ^ (1 / (k : ℝ)) / (k : ℝ) ^ (c i)) atTop
      (𝓝 ((c i / Real.exp 1) ^ (c i))) :=
    fun i => tendsto_norm_Gamma_linear_rpow_inv_nat (hc i) (β i)
  have hP : Tendsto (fun k : ℕ => ∏ i,
      (‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖ ^ (1 / (k : ℝ)) / (k : ℝ) ^ (c i)))
      atTop (𝓝 (∏ i, (c i / Real.exp 1) ^ (c i))) :=
    tendsto_finsetProd _ (fun i _ => hi i)
  have hlim := hP.mul tendsto_div_factorial_rpow_inv
  have hlimval : (∏ i, (c i / Real.exp 1) ^ (c i)) * Real.exp 1 = ∏ i, (c i) ^ (c i) := by
    have hsplit : ∀ i : ι, (c i / Real.exp 1) ^ (c i)
        = (c i) ^ (c i) / (Real.exp 1) ^ (c i) :=
      fun i => Real.div_rpow (hc i).le (Real.exp_pos 1).le _
    rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_div_distrib,
      prod_rpow_const _ (Real.exp_pos 1) c, hsum, Real.rpow_one]
    field_simp
  rw [hlimval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  show (∏ i, ‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖ ^ (1 / (k : ℝ))
        / (k : ℝ) ^ (c i)) * ((k : ℝ) / (k.factorial : ℝ) ^ (1 / (k : ℝ)))
      = ((∏ i, ‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖) / (k.factorial : ℝ))
        ^ (1 / (k : ℝ))
  rw [Real.div_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hfact.le,
    ← Real.finsetProd_rpow _ _ (fun i _ => norm_nonneg _),
    Finset.prod_div_distrib, prod_rpow_const _ hkpos c, hsum, Real.rpow_one]
  have hfr : (0 : ℝ) < (k.factorial : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hfact _
  field_simp
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

end

end GaloisForLFunctions.HTGeometry
