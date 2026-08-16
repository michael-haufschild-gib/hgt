import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtAsymptotic

/-!
# Logarithmically weighted dyadic von Mangoldt mass

On a dyadic shell the logarithm is constant to within `log 2`, so weighting the inverse-square-root
von Mangoldt mass by `(log n)^{2m}` multiplies it by `(log X)^{2m}` up to a factor tending to one.
Hence

`∑_{X < n ≤ 2X} Λ(n) n^{-1/2} (log n)^{2m} ~ 2(√2 − 1) √X (log X)^{2m}`.

This is the arithmetic input of every higher radiation order: after subtracting `m` Poincaré terms
the surviving prime mass still grows like `√X (log X)^{2m}`, so no finite jet can absorb it.
-/

open Filter ArithmeticFunction
open scoped Topology BigOperators

namespace RHTower

/-- The dyadic von Mangoldt mass weighted by the inverse square root and a logarithmic power. -/
noncomputable def dyadicSqrtVonMangoldtLogMass (m : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, (vonMangoldt n : ℝ) / Real.sqrt n * Real.log n ^ (2 * m)

theorem dyadicSqrtVonMangoldtLogMass_zero (X : ℝ) :
    dyadicSqrtVonMangoldtLogMass 0 X = dyadicSqrtVonMangoldtMass X := by
  simp [dyadicSqrtVonMangoldtLogMass, dyadicSqrtVonMangoldtMass]

/-- Every summand of a dyadic shell has logarithm between `log X` and `log X + log 2`. -/
theorem log_mem_dyadic {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    Real.log X ≤ Real.log n ∧ Real.log n ≤ Real.log X + Real.log 2 := by
  obtain ⟨hlow, hhigh⟩ := Finset.mem_Ioc.mp hn
  have hXn : X ≤ (n : ℝ) := by
    have := Nat.lt_floor_add_one X
    have hle : (⌊X⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlow
    linarith
  have hn2 : (n : ℝ) ≤ 2 * X := by
    have := Nat.floor_le (by positivity : (0:ℝ) ≤ 2 * X)
    have hle : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hhigh
    linarith
  constructor
  · exact Real.log_le_log hX hXn
  · have : Real.log (n : ℝ) ≤ Real.log (2 * X) :=
      Real.log_le_log (by linarith) hn2
    rwa [Real.log_mul (by norm_num) (ne_of_gt hX), add_comm] at this

/-- The logarithmic weight is squeezed between the two shell endpoints. -/
theorem dyadicSqrtVonMangoldtLogMass_bounds {X : ℝ} (hX : 1 < X) (m : ℕ) :
    Real.log X ^ (2 * m) * dyadicSqrtVonMangoldtMass X
        ≤ dyadicSqrtVonMangoldtLogMass m X ∧
      dyadicSqrtVonMangoldtLogMass m X
        ≤ (Real.log X + Real.log 2) ^ (2 * m) * dyadicSqrtVonMangoldtMass X := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hterm : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      0 ≤ (vonMangoldt n : ℝ) / Real.sqrt n := by
    intro n _
    exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  constructor
  · rw [dyadicSqrtVonMangoldtMass, Finset.mul_sum, dyadicSqrtVonMangoldtLogMass]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hlow, -⟩ := log_mem_dyadic hX0 hn
    have hpow : Real.log X ^ (2 * m) ≤ Real.log n ^ (2 * m) :=
      pow_le_pow_left₀ (le_of_lt hlogpos) hlow (2 * m)
    calc Real.log X ^ (2 * m) * ((vonMangoldt n : ℝ) / Real.sqrt n)
        ≤ Real.log n ^ (2 * m) * ((vonMangoldt n : ℝ) / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hpow (hterm n hn)
      _ = (vonMangoldt n : ℝ) / Real.sqrt n * Real.log n ^ (2 * m) := by ring
  · rw [dyadicSqrtVonMangoldtMass, Finset.mul_sum, dyadicSqrtVonMangoldtLogMass]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hlow, hhigh⟩ := log_mem_dyadic hX0 hn
    have hpow : Real.log n ^ (2 * m) ≤ (Real.log X + Real.log 2) ^ (2 * m) :=
      pow_le_pow_left₀ (le_trans (le_of_lt hlogpos) hlow) hhigh (2 * m)
    calc (vonMangoldt n : ℝ) / Real.sqrt n * Real.log n ^ (2 * m)
        ≤ (vonMangoldt n : ℝ) / Real.sqrt n * (Real.log X + Real.log 2) ^ (2 * m) :=
          mul_le_mul_of_nonneg_left hpow (hterm n hn)
      _ = (Real.log X + Real.log 2) ^ (2 * m) * ((vonMangoldt n : ℝ) / Real.sqrt n) := by ring

/-- The shell distortion factor tends to one. -/
theorem tendsto_logShellRatio (m : ℕ) :
    Tendsto (fun X : ℝ => ((Real.log X + Real.log 2) / Real.log X) ^ (2 * m)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℝ => Real.log X) atTop atTop := Real.tendsto_log_atTop
  have hratio : Tendsto (fun X : ℝ => (Real.log X + Real.log 2) / Real.log X) atTop (𝓝 1) := by
    have hzero : Tendsto (fun X : ℝ => Real.log 2 / Real.log X) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hlog
    have hone : Tendsto (fun X : ℝ => 1 + Real.log 2 / Real.log X) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hzero
    have hcongr : ∀ᶠ X : ℝ in atTop, 1 + Real.log 2 / Real.log X
        = (Real.log X + Real.log 2) / Real.log X := by
      filter_upwards [hlog.eventually_gt_atTop 0] with X hX
      field_simp
    simpa using hone.congr' hcongr
  simpa using hratio.pow (2 * m)

/-- **The logarithmically weighted dyadic prime mass.**  After `m` subtractions the surviving
prime mass of a dyadic shell still grows like `√X (log X)^{2m}`. -/
theorem tendsto_dyadicSqrtVonMangoldtLogMass (m : ℕ) :
    Tendsto (fun X : ℝ => dyadicSqrtVonMangoldtLogMass m X / (Real.sqrt X * Real.log X ^ (2 * m)))
      atTop (𝓝 (2 * (Real.sqrt 2 - 1))) := by
  have hbase := tendsto_dyadicSqrtVonMangoldtMass_div_sqrt
  have hratio := tendsto_logShellRatio m
  have hupper : Tendsto
      (fun X : ℝ => ((Real.log X + Real.log 2) / Real.log X) ^ (2 * m)
        * (dyadicSqrtVonMangoldtMass X / Real.sqrt X)) atTop
      (𝓝 (1 * (2 * (Real.sqrt 2 - 1)))) := hratio.mul hbase
  rw [one_mul] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX0 : 0 < X := lt_trans zero_lt_one hX
    have hlogpos : 0 < Real.log X := Real.log_pos hX
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
    have hlow := (dyadicSqrtVonMangoldtLogMass_bounds hX m).1
    have hstep : dyadicSqrtVonMangoldtMass X / Real.sqrt X
        = Real.log X ^ (2 * m) * dyadicSqrtVonMangoldtMass X
          / (Real.sqrt X * Real.log X ^ (2 * m)) := by
      field_simp
    rw [hstep]
    gcongr
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hX0 : 0 < X := lt_trans zero_lt_one hX
    have hlogpos : 0 < Real.log X := Real.log_pos hX
    have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
    have hhigh := (dyadicSqrtVonMangoldtLogMass_bounds hX m).2
    have hsplit : ((Real.log X + Real.log 2) / Real.log X) ^ (2 * m)
        * (dyadicSqrtVonMangoldtMass X / Real.sqrt X)
        = (Real.log X + Real.log 2) ^ (2 * m) * dyadicSqrtVonMangoldtMass X
          / (Real.sqrt X * Real.log X ^ (2 * m)) := by
      rw [div_pow]
      field_simp
    rw [hsplit]
    gcongr

end RHTower
