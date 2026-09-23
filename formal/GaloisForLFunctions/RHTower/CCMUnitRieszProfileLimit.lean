import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovTransform

/-!
# The unit-Riesz aperture profile is a cumulative distribution function

The corpus already owns the cell formula, the sharp prefix inequality `2 m sqrt(m+1) <= 3 A_m` and
the resulting nonnegativity of the cell density, together with `W(1) = 0`.  What is added here is
the opposite prefix bound and the boundary value at infinity:

```text
3 A_m <= 2 (m+1) sqrt(m+1),        w(v) <= 1,        1 - 9 e^{-v/2} <= w(v),      w(v) -> 1.
```

Both prefix bounds are exact and elementary.  Together with `w(0) = 0` and nonnegativity of the
density this is the card's equation `(5)`: `d(v) dv` is a probability law fixed by the unit
aperture, independent of the source and of the scale.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The opposite prefix inequality: `3 sum_{r=1}^m sqrt r <= 2 (m+1) sqrt (m+1)`. -/
theorem unitRieszSqrtPrefixMass_upper (m : ℕ) :
    3 * unitRieszSqrtPrefixMass m ≤ 2 * ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) := by
  induction m with
  | zero => simp [unitRieszSqrtPrefixMass]
  | succ m ih =>
      have ha : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
      have hb : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 2) := Real.sqrt_nonneg _
      have hasq : Real.sqrt ((m : ℝ) + 1) ^ (2 : ℕ) = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hbsq : Real.sqrt ((m : ℝ) + 2) ^ (2 : ℕ) = (m : ℝ) + 2 := Real.sq_sqrt (by positivity)
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have ha1 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by nlinarith [hasq, ha, hmnn]
      have hab : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt ((m : ℝ) + 2) := by
        nlinarith [hasq, hbsq, ha, hb]
      have hstep : 3 * Real.sqrt ((m : ℝ) + 1)
          ≤ 2 * ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)
            - 2 * ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) := by
        nlinarith [hasq, hbsq, ha, hb, ha1, hab, hmnn,
          sq_nonneg (Real.sqrt ((m : ℝ) + 2) - Real.sqrt ((m : ℝ) + 1)),
          mul_nonneg ha hb]
      rw [unitRieszSqrtPrefixMass, Finset.sum_range_succ]
      rw [unitRieszSqrtPrefixMass] at ih
      push_cast
      rw [show ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 from by ring]
      linarith [ih, hstep]

/-! ## The profile at infinity -/

theorem sqrtExpSelf (v : ℝ) : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
  rw [sqrt_eq_exp_log_div_two (Real.exp_pos v), Real.log_exp]

theorem unitRieszLogProfile_eq_div (v : ℝ) :
    unitRieszLogProfile v
      = 3 * (⌊Real.exp v⌋₊ : ℝ) / Real.exp v
        - 3 * unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊
          / (Real.exp v * Real.sqrt (Real.exp v)) := by
  have hx : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hsx : (0 : ℝ) < Real.sqrt (Real.exp v) := Real.sqrt_pos.mpr hx
  have h1 : Real.exp (-v) = 1 / Real.exp v := by
    rw [Real.exp_neg]
    ring
  have h2 : Real.exp (-3 * v / 2) = 1 / (Real.exp v * Real.sqrt (Real.exp v)) := by
    rw [sqrtExpSelf, ← Real.exp_add, one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [unitRieszLogProfile, unitRieszCellProfile, h1, h2]
  field_simp

/-- **Upper bound.**  The profile never exceeds `1`. -/
theorem unitRieszLogProfile_le_one (v : ℝ) : unitRieszLogProfile v ≤ 1 := by
  have hx : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hsx : (0 : ℝ) < Real.sqrt (Real.exp v) := Real.sqrt_pos.mpr hx
  have hmle : ((⌊Real.exp v⌋₊ : ℕ) : ℝ) ≤ Real.exp v := Nat.floor_le hx.le
  have hltm : Real.exp v < ((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmnn : (0 : ℝ) ≤ ((⌊Real.exp v⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hprefix := unitRieszSqrtPrefixMass_lower ⌊Real.exp v⌋₊
  have hsqrtmono : Real.sqrt (Real.exp v) ≤ Real.sqrt (((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1) :=
    Real.sqrt_le_sqrt hltm.le
  have hkey : 2 * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) * Real.sqrt (Real.exp v)
      ≤ 3 * unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊ := by
    have h := mul_le_mul_of_nonneg_left hsqrtmono (by positivity : (0 : ℝ) ≤ 2 * ((⌊Real.exp v⌋₊ : ℕ) : ℝ))
    linarith [hprefix, h]
  have hA : 2 * (((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v)
      ≤ 3 * unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊
        / (Real.exp v * Real.sqrt (Real.exp v)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hx (by positivity)]
    nlinarith [hkey, hx, hsx]
  have hC : ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v ≤ 1 := by
    rw [div_le_one hx]
    exact hmle
  rw [unitRieszLogProfile_eq_div v,
    show 3 * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v
      = 3 * (((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v) from by ring]
  linarith [hA, hC]

/-- **Lower bound.**  An explicit envelope: `1 - 9 e^{-v/2} <= w(v)` for `v >= 0`. -/
theorem unitRieszLogProfile_ge {v : ℝ} (hv : 0 ≤ v) :
    1 - 9 / Real.sqrt (Real.exp v) ≤ unitRieszLogProfile v := by
  have hx1 : (1 : ℝ) ≤ Real.exp v := Real.one_le_exp hv
  have hx : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hsx : (0 : ℝ) < Real.sqrt (Real.exp v) := Real.sqrt_pos.mpr hx
  have hsxsq : Real.sqrt (Real.exp v) ^ (2 : ℕ) = Real.exp v := Real.sq_sqrt hx.le
  have hsx1 : (1 : ℝ) ≤ Real.sqrt (Real.exp v) := by nlinarith [hsxsq, hsx, hx1]
  have hmle : ((⌊Real.exp v⌋₊ : ℕ) : ℝ) ≤ Real.exp v := Nat.floor_le hx.le
  have hltm : Real.exp v < ((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hupper := unitRieszSqrtPrefixMass_upper ⌊Real.exp v⌋₊
  have hsnn : (0 : ℝ) ≤ Real.sqrt (((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1) := Real.sqrt_nonneg _
  have hssq : Real.sqrt (((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1) ^ (2 : ℕ) = ((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  -- `sqrt (m+1) ≤ sqrt x + 1`
  have hs1 : Real.sqrt (((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1) ≤ Real.sqrt (Real.exp v) + 1 := by
    nlinarith [hssq, hsxsq, hsnn, hsx, hmle]
  have hkey : 3 * unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊
      ≤ 2 * (Real.exp v + 1) * (Real.sqrt (Real.exp v) + 1) := by
    have h1 : ((⌊Real.exp v⌋₊ : ℕ) : ℝ) + 1 ≤ Real.exp v + 1 := by linarith
    nlinarith [hupper, hs1, hsnn, h1, hsx]
  have hterm2 : 3 * unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊
      / (Real.exp v * Real.sqrt (Real.exp v)) ≤ 2 + 6 / Real.sqrt (Real.exp v) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : (2 + 6 / Real.sqrt (Real.exp v)) * (Real.exp v * Real.sqrt (Real.exp v))
        = 2 * (Real.exp v * Real.sqrt (Real.exp v)) + 6 * Real.exp v := by
      field_simp
    rw [hexp]
    nlinarith [hkey, hsx, hsx1, hx1, hsxsq]
  have hterm1 : 3 - 3 / Real.sqrt (Real.exp v)
      ≤ 3 * (((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v) := by
    rw [mul_div_assoc', le_div_iff₀ hx]
    have hmge : Real.exp v - 1 ≤ ((⌊Real.exp v⌋₊ : ℕ) : ℝ) := by linarith
    have hinv : 3 / Real.sqrt (Real.exp v) * Real.exp v = 3 * Real.sqrt (Real.exp v) := by
      field_simp
      nlinarith [hsxsq]
    have hlhs : (3 - 3 / Real.sqrt (Real.exp v)) * Real.exp v
        = 3 * Real.exp v - 3 * Real.sqrt (Real.exp v) := by
      rw [sub_mul, hinv]
    rw [hlhs]
    linarith [hmge, hsx1]
  rw [unitRieszLogProfile_eq_div v,
    show 3 * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v
      = 3 * (((⌊Real.exp v⌋₊ : ℕ) : ℝ) / Real.exp v) from by ring]
  have hsix : (6 : ℝ) / Real.sqrt (Real.exp v) + 3 / Real.sqrt (Real.exp v)
      = 9 / Real.sqrt (Real.exp v) := by ring
  linarith [hterm1, hterm2, hsix]

/-- **Equation (5), boundary value.**  The unit-Riesz profile increases to `1`: total mass one. -/
theorem tendsto_unitRieszLogProfile_atTop :
    Tendsto unitRieszLogProfile atTop (nhds 1) := by
  have hexp : Tendsto (fun v : ℝ => Real.sqrt (Real.exp v)) atTop atTop := by
    have h : Tendsto (fun v : ℝ => Real.exp (v / 2)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    refine h.congr fun v => (sqrtExpSelf v).symm
  have hinv : Tendsto (fun v : ℝ => 9 / Real.sqrt (Real.exp v)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hexp
  have hlow : Tendsto (fun v : ℝ => 1 - 9 / Real.sqrt (Real.exp v)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    exact unitRieszLogProfile_ge hv
  · filter_upwards with v
    exact unitRieszLogProfile_le_one v

end GaloisForLFunctions.RHTower

end
