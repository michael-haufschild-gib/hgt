import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ArithmeticPowerRiemannProfiles

/-!
# The Mellin integral of an arithmetic power profile

Integrating a finite inverse staircase gives partial summation with its
boundary term retained. Cancellation makes that boundary vanish, identifying
the improper integral with the limit of the weighted arithmetic sums.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

theorem arithmeticPowerProfile_cut_eq_sum (p : ℝ) (f : ℕ → ℝ)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (_ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (Set.Ioi (1 / (N : ℝ))).indicator (arithmeticPowerProfile p f) t =
      ∑ n ∈ Icc 1 N, f n *
        (if 1 / (N : ℝ) < t ∧ t ≤ 1 / (n : ℝ) then t ^ (-p) else 0) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases htN : 1 / (N : ℝ) < t
  · rw [Set.indicator_of_mem htN, arithmeticPowerProfile,
      sum_inverse_floor_eq (one_div_pos.mpr hNp) htN,
      one_div_one_div, Nat.floor_natCast, mul_sum]
    apply sum_congr rfl
    intro n _
    by_cases hn : t ≤ 1 / (n : ℝ)
    · rw [if_pos hn, if_pos ⟨htN, hn⟩, mul_comm]
    · rw [if_neg hn, if_neg (fun h => hn h.2), mul_zero, mul_zero]
  · rw [Set.indicator_of_notMem htN]
    exact (sum_eq_zero fun n _ => by rw [if_neg (fun h => htN h.1), mul_zero]).symm

/-- Integration of a finite inverse staircase retains precisely its endpoint
summatory term. -/
theorem integral_cut_arithmeticPowerProfile {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (1 / (N : ℝ))).indicator (arithmeticPowerProfile p f) t) =
      ((∑ n ∈ Icc 1 N, f n * (n : ℝ) ^ (-(1 - p))) -
        (N : ℝ) ^ (-(1 - p)) * ∑ n ∈ Icc 1 N, f n) / (1 - p) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNp
  let F := fun n : ℕ => fun t : ℝ =>
    if 1 / (N : ℝ) < t ∧ t ≤ 1 / (n : ℝ) then t ^ (-p) else 0
  have hδn (n : ℕ) (hn : n ∈ Icc 1 N) : 1 / (N : ℝ) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast (mem_Icc.mp hn).1)
      (by exact_mod_cast (mem_Icc.mp hn).2)
  have hi (n : ℕ) (hn : n ∈ Icc 1 N) : IntegrableOn (F n) (Set.Ioc 0 1) :=
    (riemannOn_rpow_interval hp hδ (hδn n hn)).1
  have hval (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∫ t in Set.Ioc (0 : ℝ) 1, F n t) =
        ((n : ℝ) ^ (-(1 - p)) - (N : ℝ) ^ (-(1 - p))) / (1 - p) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hn1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      exact_mod_cast (mem_Icc.mp hn).1
    have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc (1 / (N : ℝ)) (1 / (n : ℝ)) =
        Set.Ioc (1 / (N : ℝ)) (1 / (n : ℝ)) := by
      apply Set.inter_eq_right.mpr
      intro t ht
      exact ⟨hδ.trans ht.1, ht.2.trans hn1⟩
    change (∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioc (1 / (N : ℝ)) (1 / (n : ℝ))).indicator (fun t => t ^ (-p)) t) = _
    rw [setIntegral_indicator measurableSet_Ioc, hset,
      ← intervalIntegral.integral_of_le (hδn n hn),
      integral_rpow (Or.inl (by linarith only [hp1])), show -p + 1 = 1 - p by ring]
    simp only [one_div, Real.inv_rpow hn0.le, Real.inv_rpow hNp.le,
      ← Real.rpow_neg hn0.le, ← Real.rpow_neg hNp.le]
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => arithmeticPowerProfile_cut_eq_sum p f hN ht)]
  rw [integral_finset_sum _ (fun n hn => (hi n hn).const_mul (f n))]
  simp_rw [integral_const_mul]
  rw [sum_congr rfl (fun n hn => congrArg (fun x : ℝ => f n * x) (hval n hn))]
  simp only [← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  ring

/-- Positive inverse cutoffs exhaust the integral of any measurable integrable profile. -/
theorem tendsto_integral_inverse_cut {g : ℝ → ℝ} (hg : Measurable g)
    (hi : IntegrableOn g (Set.Ioc 0 1)) :
    Tendsto (fun N : ℕ => ∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (1 / (N : ℝ))).indicator g t) atTop
      (𝓝 (∫ t in Set.Ioc (0 : ℝ) 1, g t)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => |g t|)
    (fun N => (hg.indicator measurableSet_Ioi).aestronglyMeasurable)
    hi.abs (fun N => Eventually.of_forall fun t => ?_) ?_
  · rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    refine tendsto_const_nhds.congr' ?_
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds ht.1)
    filter_upwards [h] with N hN
    rw [Set.indicator_of_mem hN]

/-- The summatory Mellin integral is the limit of the weighted source series;
absolute summability of the source is unnecessary. -/
theorem tendsto_weighted_sums_arithmeticPowerProfile {p β C : ℝ} {f : ℕ → ℝ}
    (hp : 0 ≤ p) (hβ : 0 ≤ β) (hpos : 0 < p + β) (hsub : p + β < 1)
    (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, |∑ n ∈ Icc 1 N, f n| ≤ C * (N : ℝ) ^ β) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, f n * (n : ℝ) ^ (-(1 - p))) atTop
      (𝓝 ((1 - p) * ∫ t in Set.Ioc (0 : ℝ) 1, arithmeticPowerProfile p f t)) := by
  have hp1 : p < 1 := by linarith only [hβ, hsub]
  have hθ : 0 < 1 - p := by linarith only [hp1]
  have hi := (riemannOn_arithmeticPowerProfile hp hβ hpos hsub hC hbound).1
  have hcut := (tendsto_integral_inverse_cut (measurable_arithmeticPowerProfile p f) hi)
    .const_mul (1 - p)
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - p)) * ∑ n ∈ Icc 1 N, f n)
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (β - (1 - p))) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (show 0 < 1 - p - β by linarith only [hsub])).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
      simpa only [Function.comp_apply, show -(1 - p - β) = β - (1 - p) by ring,
        mul_zero] using h
    apply squeeze_zero_norm' _ hmaj
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hNp.le _)]
    calc
      _ ≤ (N : ℝ) ^ (-(1 - p)) * (C * (N : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left (hbound N) (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hNp]; congr 2; ring
  have h := hcut.add hz
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [integral_cut_arithmeticPowerProfile hp hp1 f hN]
  field_simp [hθ.ne'] <;> ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
