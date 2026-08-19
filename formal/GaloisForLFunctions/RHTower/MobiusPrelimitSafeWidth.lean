import GaloisForLFunctions.RHTower.MobiusHalfUnitMomentTower

/-!
# The prelimit safe weighted width

At a positive shift the centered Mertens vector decays like `e^{-βt}` for every `β < 2ω`, so every
weight below `e^{2ωt}` keeps it square integrable.  Reaching the critical line from the Euler base
`s = 1 + 2ω` would instead require weights cofinal in `[0, 1/2 + 2ω)`; the difference is exactly
one half at every positive shift.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The sharp exponential tail bound: any decay rate below `2ω` is available. -/
theorem norm_mobiusWeightedTail_le_of_lt {ω β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2 * ω) (t : ℝ) :
    ‖mobiusWeightedTail (1 + 2 * ω) t‖
      ≤ Real.exp (-(β * t)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β))) := by
  have hsum := summable_mobiusWeightedTailTerm (a := 1 + 2 * ω) (by linarith) t
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + (2 * ω - β)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ,
      ‖(if Real.exp t < (n : ℝ) then mobiusRealWeight (1 + 2 * ω) n else 0)‖
        ≤ Real.exp (-(β * t)) * (n : ℝ) ^ (-(1 + (2 * ω - β))) := by
    intro n
    by_cases h : Real.exp t < (n : ℝ)
    · rw [if_pos h]
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos t) h
      have hbound := norm_mobiusRealWeight_le (1 + 2 * ω) n
      have hsplit : (n : ℝ) ^ (-(1 + 2 * ω))
          = (n : ℝ) ^ (-(1 + (2 * ω - β))) * (n : ℝ) ^ (-β) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      have hmono : (n : ℝ) ^ (-β) ≤ Real.exp t ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos t) (le_of_lt h) (by linarith)
      have hexp : Real.exp t ^ (-β) = Real.exp (-(β * t)) := by
        rw [← Real.exp_mul]
        congr 1
        ring
      rw [hsplit] at hbound
      have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + (2 * ω - β))) := Real.rpow_nonneg hnpos.le _
      calc ‖mobiusRealWeight (1 + 2 * ω) n‖
          ≤ (n : ℝ) ^ (-(1 + (2 * ω - β))) * (n : ℝ) ^ (-β) := hbound
        _ ≤ (n : ℝ) ^ (-(1 + (2 * ω - β))) * Real.exp (-(β * t)) := by
            rw [← hexp]
            exact mul_le_mul_of_nonneg_left hmono hpos
        _ = Real.exp (-(β * t)) * (n : ℝ) ^ (-(1 + (2 * ω - β))) := by ring
    · rw [if_neg h, norm_zero]
      have : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + (2 * ω - β))) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
  calc ‖mobiusWeightedTail (1 + 2 * ω) t‖
      ≤ ∑' n : ℕ, ‖(if Real.exp t < (n : ℝ) then mobiusRealWeight (1 + 2 * ω) n else 0)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, Real.exp (-(β * t)) * (n : ℝ) ^ (-(1 + (2 * ω - β))) :=
        Summable.tsum_le_tsum hterm hsum.norm (hbase.mul_left _)
    _ = Real.exp (-(β * t)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β))) := tsum_mul_left

theorem norm_centeredMertensVector_le_of_lt {ω β : ℝ} (hω : 0 < ω) (hβ0 : 0 ≤ β)
    (hβ : β < 2 * ω) (t : ℝ) :
    ‖centeredMertensVector ω t‖
      ≤ Set.indicator (Set.Ioi (0 : ℝ))
          (fun s => Real.exp (-(β * s)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β)))) t := by
  have hC : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β))) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  rcases le_or_gt t 0 with ht | ht
  · rw [centeredMertensVector_of_nonpos ω ht, norm_zero,
      Set.indicator_of_notMem (by simpa using ht)]
  · rw [centeredMertensVector_eq_tail hω ht,
      Set.indicator_of_mem (Set.mem_Ioi.mpr ht), norm_neg, norm_mul]
    have hb := norm_mobiusWeightedTail_le_of_lt hβ0 hβ t
    have hc := norm_inv_one_add_ofReal_le' hω
    calc ‖(1 : ℂ) / ((1 : ℂ) + (ω : ℂ))‖ * ‖mobiusWeightedTail (1 + 2 * ω) t‖
        ≤ 1 * (Real.exp (-(β * t)) * ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β)))) :=
          mul_le_mul hc hb (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _

/-- **Card equation `(18)`: the prelimit safe weighted width is `2ω`.**  Every weight strictly
below `e^{2ωt}` keeps the centered prelimit Mertens vector square integrable. -/
theorem memLp_weighted_centeredMertensVector {ω α : ℝ} (hω : 0 < ω) (hα0 : 0 ≤ α)
    (hα : α < 2 * ω) :
    MemLp (fun t : ℝ => (Real.exp (α * t) : ℂ) * centeredMertensVector ω t) 2 volume := by
  set β : ℝ := (α + 2 * ω) / 2 with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  have hβ : β < 2 * ω := by rw [hβdef]; linarith
  have hαβ : α < β := by rw [hβdef]; linarith
  set C : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(1 + (2 * ω - β))) with hCdef
  have hC : (0 : ℝ) ≤ C := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  set g : ℝ → ℝ := fun t =>
    Set.indicator (Set.Ioi (0 : ℝ)) (fun s => C * Real.exp (-((β - α) * s))) t with hgdef
  have hgmeas : AEStronglyMeasurable g volume := by
    refine (Measurable.indicator ?_ measurableSet_Ioi).aestronglyMeasurable
    exact measurable_const.mul (Real.measurable_exp.comp (by fun_prop))
  have hgL : MemLp g 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hgmeas).mpr ?_
    have hint : IntegrableOn (fun t : ℝ => C ^ 2 * Real.exp (-(2 * (β - α)) * t))
        (Ioi (0 : ℝ)) volume :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
    have hzero : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → ‖g t‖ ^ 2 = 0 := by
      intro t ht
      simp only [hgdef]
      rw [Set.indicator_of_notMem ht, norm_zero]
      norm_num
    refine (IntegrableOn.integrable_of_ae_notMem_eq_zero (s := Ioi (0 : ℝ)) ?_ ?_)
    · refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
      simp only [hgdef]
      rw [Set.indicator_of_mem ht, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    · exact Filter.Eventually.of_forall hzero
  have hfmeas : AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (α * t) : ℂ) * centeredMertensVector ω t) volume := by
    refine ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (by fun_prop))).measurable.mul (measurable_centeredMertensVector ω)).aestronglyMeasurable
  refine hgL.of_le hfmeas (Filter.Eventually.of_forall fun t => ?_)
  have hb := norm_centeredMertensVector_le_of_lt hω hβ0 hβ t
  rcases le_or_gt t 0 with ht | ht
  · rw [Set.indicator_of_notMem (by simpa using ht)] at hb
    have h0 : centeredMertensVector ω t = 0 := centeredMertensVector_of_nonpos ω ht
    rw [h0, mul_zero, norm_zero]
    positivity
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht)] at hb
    simp only [hgdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc Real.exp (α * t) * ‖centeredMertensVector ω t‖
        ≤ Real.exp (α * t) * (Real.exp (-(β * t)) * C) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = C * Real.exp (-((β - α) * t)) := by
          have hprod : Real.exp (α * t) * Real.exp (-(β * t)) = Real.exp (-((β - α) * t)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc Real.exp (α * t) * (Real.exp (-(β * t)) * C)
              = (Real.exp (α * t) * Real.exp (-(β * t))) * C := by ring
            _ = Real.exp (-((β - α) * t)) * C := by rw [hprod]
            _ = C * Real.exp (-((β - α) * t)) := by ring

/-- **Card equation `(21)`: the invariant missing continuation width.**  The width required to
reach the critical line from the Euler base exceeds the safe width by exactly one half, at every
positive shift. -/
theorem prelimit_missing_width (ω : ℝ) : (1 / 2 + 2 * ω) - 2 * ω = 1 / 2 := by ring

end

end RHTower
