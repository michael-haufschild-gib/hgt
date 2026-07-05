/-
# RescaleLimit — the doc 25 (E3) elementary limit facts (task #143 / #135 substrate)

Doc 25 (25-tracking-clearance.md) (E3) `[PROVED HERE]`: the rescaling factor
`φ_d(j) = ∏_{i<j}(1 − i/d)` satisfies `φ_d(j) ∈ [0,1]` and `φ_d(j) → 1` pointwise, from which
`Ã_d → g` uniformly on compacts (the domination `Σ|c_j|ρ^j < ∞`). Flat grading: a finite
product bounded by / converging to `1`; nothing new. `SpurRescale` already banks the positivity
(`phi_product_pos_of_le`), the `j > d` vanishing, and the first-order (E5) expansion; the two
facts here complete the `[0,1]` bracket and the pointwise limit.

* `phi_product_le_one` — `φ_d(j) ≤ 1` for `j ≤ d` (each factor in `[0,1]`).
* `phi_product_tendsto_one` — for fixed `j`, `φ_d(j) → 1` as `d → ∞` (each factor `1 − i/d → 1`,
  finite product of limits).
-/
import GaloisForLFunctions.RHTower.SpurRescale

noncomputable section

namespace RHTower

open Filter Topology

/-- **(E3) upper bracket**: `φ_d(j) = ∏_{i<j}(1 − i/d) ≤ 1` for `j ≤ d`, since every factor
lies in `[0,1]` (`i < j ≤ d` ⟹ `0 ≤ i/d ≤ 1`). -/
theorem phi_product_le_one {j d : ℕ} (hjd : j ≤ d) :
    ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d) ≤ 1 := by
  apply Finset.prod_le_one
  · intro i hi
    rw [Finset.mem_range] at hi
    have hid : i < d := lt_of_lt_of_le hi hjd
    have hd : (0 : ℝ) < d := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le i) hid
    have hle : (i : ℝ) / d ≤ 1 := by
      rw [div_le_one hd]; exact_mod_cast hid.le
    have h0 : (0 : ℝ) ≤ (i : ℝ) / d := by positivity
    linarith
  · intro i _
    have : (0 : ℝ) ≤ (i : ℝ) / d := by positivity
    linarith

/-- **(E3) pointwise limit**: for fixed `j`, `φ_d(j) = ∏_{i<j}(1 − i/d) → 1` as `d → ∞`.
Each factor `1 − i/d → 1 − 0 = 1`; the finite product of limits is the limit of the product. -/
theorem phi_product_tendsto_one (j : ℕ) :
    Tendsto (fun d : ℕ => ∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) atTop (nhds 1) := by
  have hprod : (1 : ℝ) = ∏ _i ∈ Finset.range j, (1 : ℝ) := by simp
  rw [hprod]
  apply tendsto_finsetProd
  intro i _
  have h0 : Tendsto (fun d : ℕ => (i : ℝ) / d) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0

end RHTower
