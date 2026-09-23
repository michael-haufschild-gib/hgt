import GaloisForLFunctions.RHTower.CCMUnitRieszProfileLimit

/-!
# The exact layer-cake form of the unit-Riesz quadrature defect

The elementary identity `1 - sqrt u = int_u^(1 : ℕ) dv/(2 sqrt v)` turns the progression sum

```text
g(t) = sum_{1 <= r <= t} (1 - sqrt (r/t))
```

into a single layer-cake integral of the counting function, and its defect from the polar
continuum into the corresponding fractional-part integral:

```text
g(t)   = int_0^(1 : ℕ) floor (t v) dv / (2 sqrt v),
eta(t) = t/3 - g(t) = int_0^(1 : ℕ) (t v - floor (t v)) dv / (2 sqrt v).
```

Since the fractional part lies between `0` and `t v`, and below `1`, this gives the card's `(6)`

```text
0 <= eta(t) <= 1,        0 <= eta(t) <= t/3,
```

with no asymptotics whatsoever.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The layer-cake weight -/

/-- The layer-cake weight `1/(2 sqrt v)`. -/
def layerWeight (v : ℝ) : ℝ := 1 / (2 * Real.sqrt v)

theorem layerWeight_nonneg (v : ℝ) : 0 ≤ layerWeight v := by
  unfold layerWeight
  positivity

theorem layerWeight_eq_rpow {v : ℝ} (hv : 0 ≤ v) :
    layerWeight v = 1 / 2 * v ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_lt_of_le hv with h | h
  · rw [← h]
    unfold layerWeight
    rw [Real.sqrt_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · unfold layerWeight
    rw [Real.rpow_neg h.le, Real.sqrt_eq_rpow]
    have hs : (0 : ℝ) < v ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h _
    field_simp

theorem intervalIntegrable_layerWeight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable layerWeight volume a b := by
  have hrpow : IntervalIntegrable (fun v : ℝ => 1 / 2 * v ^ (-(1 / 2 : ℝ))) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  refine hrpow.congr fun v hv => ?_
  exact (layerWeight_eq_rpow (le_trans (le_min ha hb) (le_of_lt hv.1))).symm

/-- The layer-cake identity `1 - sqrt a = int_a^(1 : ℕ) dv/(2 sqrt v)`. -/
theorem integral_layerWeight {a : ℝ} (ha : 0 < a) :
    (∫ v in a..1, layerWeight v) = 1 - Real.sqrt a := by
  have hderiv : ∀ v ∈ Set.uIcc a 1, HasDerivAt Real.sqrt (layerWeight v) v := by
    intro v hv
    have hvpos : 0 < v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · linarith [h.1]
      · linarith [h.1]
    exact Real.hasDerivAt_sqrt (ne_of_gt hvpos)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_layerWeight ha.le zero_le_one), Real.sqrt_one]

/-- The whole layer has mass one. -/
theorem integral_layerWeight_unit : (∫ v in (0 : ℝ)..1, layerWeight v) = 1 := by
  have hcongr : (∫ v in (0 : ℝ)..1, layerWeight v)
      = ∫ v in (0 : ℝ)..1, 1 / 2 * v ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    exact layerWeight_eq_rpow hv0
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 from by ring]
  rw [Real.one_rpow, Real.zero_rpow (by norm_num)]
  norm_num

/-! ## The layer-cake representation of the progression sum -/

/-- The progression sum `g(t) = sum_{1 <= r <= t} (1 - sqrt (r/t))`. -/
def rieszProgressionSum (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range ⌊t⌋₊, (1 - Real.sqrt (((r : ℝ) + 1) / t))

/-- The quadrature defect `eta(t) = t/3 - g(t)`. -/
def rieszQuadratureDefect (t : ℝ) : ℝ := t / 3 - rieszProgressionSum t

theorem rieszProgressionSum_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ rieszProgressionSum t := by
  refine Finset.sum_nonneg fun r hr => ?_
  have ht0 : (0 : ℝ) < t := by linarith
  have hrM : r + 1 ≤ ⌊t⌋₊ := Finset.mem_range.1 hr
  have hle : ((r : ℝ) + 1) / t ≤ 1 := by
    rw [div_le_one ht0]
    have h1 : ((r : ℝ) + 1) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hrM
    exact le_trans h1 (Nat.floor_le ht0.le)
  have := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_one] at this
  linarith

/-- The counting identity behind the layer cake. -/
theorem sum_indicator_eq_floor {t v : ℝ} (ht : 1 ≤ t) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∑ r ∈ Finset.range ⌊t⌋₊, (if ((r : ℝ) + 1) / t ≤ v then (1 : ℝ) else 0)
      = (⌊t * v⌋₊ : ℝ) := by
  classical
  have ht0 : (0 : ℝ) < t := by linarith
  have htv : (0 : ℝ) ≤ t * v := by positivity
  have hfilter : (Finset.range ⌊t⌋₊).filter (fun r : ℕ => ((r : ℝ) + 1) / t ≤ v)
      = Finset.range ⌊t * v⌋₊ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hle⟩
      have h1 : ((r : ℝ) + 1) ≤ t * v := by
        rw [div_le_iff₀ ht0] at hle
        linarith [hle]
      have h2 : ((r + 1 : ℕ) : ℝ) ≤ t * v := by push_cast; linarith
      have := Nat.le_floor h2
      omega
    · intro hr
      have hle : ((r + 1 : ℕ) : ℝ) ≤ t * v := by
        have : (r + 1 : ℕ) ≤ ⌊t * v⌋₊ := by omega
        have h := Nat.floor_le htv
        have h2 : ((r + 1 : ℕ) : ℝ) ≤ (⌊t * v⌋₊ : ℝ) := by exact_mod_cast this
        linarith
      have hmono : ⌊t * v⌋₊ ≤ ⌊t⌋₊ := by
        refine Nat.floor_le_floor ?_
        nlinarith
      constructor
      · omega
      · rw [div_le_iff₀ ht0]
        push_cast at hle
        linarith
  rw [Finset.sum_boole, hfilter, Finset.card_range]

theorem intervalIntegrable_indicatorLayer (a : ℝ) :
    IntervalIntegrable (fun v : ℝ => if a ≤ v then layerWeight v else 0) volume 0 1 := by
  have hfun : (fun v : ℝ => if a ≤ v then layerWeight v else 0)
      = Set.indicator (Set.Ici a) layerWeight := by
    funext v
    rw [Set.indicator_apply]
    simp [Set.mem_Ici]
  rw [hfun]
  exact ⟨(intervalIntegrable_layerWeight (le_refl (0 : ℝ)) zero_le_one).1.indicator
      measurableSet_Ici,
    (intervalIntegrable_layerWeight (le_refl (0 : ℝ)) zero_le_one).2.indicator measurableSet_Ici⟩

theorem integral_indicatorLayer {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ v in (0 : ℝ)..1, (if a ≤ v then layerWeight v else 0)) = 1 - Real.sqrt a := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := a) (c := (1 : ℝ)) (f := fun v : ℝ => if a ≤ v then layerWeight v else 0)
    ((intervalIntegrable_indicatorLayer a).mono_set
      (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.2 (Or.inl ⟨ha.le, ha1⟩))))
    ((intervalIntegrable_indicatorLayer a).mono_set
      (Set.uIcc_subset_uIcc_right (Set.mem_uIcc.2 (Or.inl ⟨ha.le, ha1⟩))))
  have hhead : (∫ v in (0 : ℝ)..a, (if a ≤ v then layerWeight v else 0)) = 0 := by
    have hz : (∫ v in (0 : ℝ)..a, (if a ≤ v then layerWeight v else 0))
        = ∫ _v in (0 : ℝ)..a, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hnull : volume ({a} : Set ℝ) = 0 := Real.volume_singleton
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with v hv hmem
      have hva : v ≠ a := by simpa using hv
      have hlt : v < a := by
        rcases Set.mem_uIoc.1 hmem with h | h
        · exact lt_of_le_of_ne h.2 hva
        · exact absurd h.1 (not_lt.2 (le_of_lt (lt_of_le_of_lt h.2 (by linarith))))
      rw [if_neg (not_le.2 hlt)]
    rw [hz]
    simp
  have htail : (∫ v in a..(1 : ℝ), (if a ≤ v then layerWeight v else 0))
      = ∫ v in a..(1 : ℝ), layerWeight v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hav : a ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.1, h.2]
    rw [if_pos hav]
  rw [hhead, htail, integral_layerWeight ha] at hsplit
  linarith [hsplit]

/-- **Equation (5), first half.**  The progression sum is the layer-cake integral of the counting
function. -/
theorem integral_floor_layerWeight {t : ℝ} (ht : 1 ≤ t) :
    (∫ v in (0 : ℝ)..1, (⌊t * v⌋₊ : ℝ) * layerWeight v) = rieszProgressionSum t := by
  classical
  have ht0 : (0 : ℝ) < t := by linarith
  have hcongr : (∫ v in (0 : ℝ)..1, (⌊t * v⌋₊ : ℝ) * layerWeight v)
      = ∫ v in (0 : ℝ)..1, ∑ r ∈ Finset.range ⌊t⌋₊,
          (if ((r : ℝ) + 1) / t ≤ v then layerWeight v else 0) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    have hv1 : v ≤ 1 := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.2
      · linarith [h.1]
    rw [← sum_indicator_eq_floor ht hv0 hv1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hcase : ((r : ℝ) + 1) / t ≤ v
    · rw [if_pos hcase, if_pos hcase, one_mul]
    · rw [if_neg hcase, if_neg hcase, zero_mul]
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hrM : r + 1 ≤ ⌊t⌋₊ := Finset.mem_range.1 hr
    have hapos : (0 : ℝ) < ((r : ℝ) + 1) / t := by positivity
    have hale : ((r : ℝ) + 1) / t ≤ 1 := by
      rw [div_le_one ht0]
      have h1 : ((r : ℝ) + 1) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hrM
      exact le_trans h1 (Nat.floor_le ht0.le)
    exact integral_indicatorLayer hapos hale
  · intro r _
    exact intervalIntegrable_indicatorLayer _

/-! ## The bounds -/

theorem intervalIntegrable_polar (t : ℝ) :
    IntervalIntegrable (fun v : ℝ => t * v * layerWeight v) volume 0 1 := by
  have hrpow : IntervalIntegrable (fun v : ℝ => t / 2 * v ^ (1 / 2 : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  refine hrpow.congr fun v hv => ?_
  have hv0 : 0 < v := by
    have := hv.1
    simpa using this
  rw [layerWeight_eq_rpow hv0.le]
  have hkey : v * v ^ (-(1 / 2) : ℝ) = v ^ (1 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one v]
    rw [← Real.rpow_add hv0]
    norm_num
  rw [← hkey]
  ring

theorem integral_polar_layerWeight (t : ℝ) :
    (∫ v in (0 : ℝ)..1, t * v * layerWeight v) = t / 3 := by
  have hcongr : (∫ v in (0 : ℝ)..1, t * v * layerWeight v)
      = ∫ v in (0 : ℝ)..1, t / 2 * v ^ (1 / 2 : ℝ) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    rw [layerWeight_eq_rpow hv0]
    rcases eq_or_lt_of_le hv0 with h | h
    · rw [← h, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
      ring
    · have hkey : v * v ^ (-(1 / 2) : ℝ) = v ^ (1 / 2 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one v]
        rw [← Real.rpow_add h]
        norm_num
      rw [← hkey]
      ring
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num))]
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 from by ring, Real.one_rpow, Real.zero_rpow (by norm_num)]
  ring

theorem intervalIntegrable_floorLayer {t : ℝ} (ht : 1 ≤ t) :
    IntervalIntegrable (fun v : ℝ => (⌊t * v⌋₊ : ℝ) * layerWeight v) volume 0 1 := by
  classical
  have ht0 : (0 : ℝ) < t := by linarith
  have hsum : IntervalIntegrable (fun v : ℝ => ∑ r ∈ Finset.range ⌊t⌋₊,
      (if ((r : ℝ) + 1) / t ≤ v then layerWeight v else 0)) volume 0 1 := by
    have h := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (Finset.range ⌊t⌋₊)
      (f := fun r : ℕ => fun v : ℝ => if ((r : ℝ) + 1) / t ≤ v then layerWeight v else 0)
      (fun r _ => intervalIntegrable_indicatorLayer _)
    have hfun : (∑ i ∈ Finset.range ⌊t⌋₊,
        fun v : ℝ => if ((i : ℝ) + 1) / t ≤ v then layerWeight v else 0)
        = fun v : ℝ => ∑ r ∈ Finset.range ⌊t⌋₊,
          (if ((r : ℝ) + 1) / t ≤ v then layerWeight v else 0) := by
      funext v
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  refine hsum.congr fun v hv => ?_
  have hv0 : 0 ≤ v := le_of_lt (by simpa using hv.1)
  have hv1 : v ≤ 1 := by simpa using hv.2
  rw [← sum_indicator_eq_floor ht hv0 hv1, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun r _ => ?_).symm
  by_cases hcase : ((r : ℝ) + 1) / t ≤ v
  · rw [if_pos hcase, if_pos hcase, one_mul]
  · rw [if_neg hcase, if_neg hcase, zero_mul]

/-- **Equation (5), second half.**  The defect is the layer-cake integral of the fractional
part. -/
theorem rieszQuadratureDefect_eq {t : ℝ} (ht : 1 ≤ t) :
    rieszQuadratureDefect t
      = ∫ v in (0 : ℝ)..1, (t * v - (⌊t * v⌋₊ : ℝ)) * layerWeight v := by
  have hsub : (∫ v in (0 : ℝ)..1, (t * v - (⌊t * v⌋₊ : ℝ)) * layerWeight v)
      = (∫ v in (0 : ℝ)..1, t * v * layerWeight v)
        - ∫ v in (0 : ℝ)..1, (⌊t * v⌋₊ : ℝ) * layerWeight v := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_polar t)
      (intervalIntegrable_floorLayer ht)]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  rw [hsub, integral_polar_layerWeight t, integral_floor_layerWeight ht,
    rieszQuadratureDefect]

/-- **Equation (6), lower bound.** -/
theorem rieszQuadratureDefect_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ rieszQuadratureDefect t := by
  rw [rieszQuadratureDefect_eq ht]
  refine intervalIntegral.integral_nonneg zero_le_one fun v hv => ?_
  have hfl : ((⌊t * v⌋₊ : ℕ) : ℝ) ≤ t * v := Nat.floor_le (by nlinarith [hv.1, hv.2])
  have := layerWeight_nonneg v
  nlinarith [hfl, this]

/-- **Equation (6), upper bound by the total layer mass.** -/
theorem rieszQuadratureDefect_le_one {t : ℝ} (ht : 1 ≤ t) : rieszQuadratureDefect t ≤ 1 := by
  have hint : IntervalIntegrable (fun v : ℝ => (t * v - (⌊t * v⌋₊ : ℝ)) * layerWeight v)
      volume 0 1 := by
    refine ((intervalIntegrable_polar t).sub (intervalIntegrable_floorLayer ht)).congr ?_
    intro v _
    ring
  have hmono : (∫ v in (0 : ℝ)..1, (t * v - (⌊t * v⌋₊ : ℝ)) * layerWeight v)
      ≤ ∫ v in (0 : ℝ)..1, layerWeight v := by
    refine intervalIntegral.integral_mono_on zero_le_one hint
      (intervalIntegrable_layerWeight (le_refl (0 : ℝ)) zero_le_one) fun v hv => ?_
    have hfl : t * v - 1 < ((⌊t * v⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (t * v)
      linarith
    have hw := layerWeight_nonneg v
    nlinarith [hfl, hw]
  rw [integral_layerWeight_unit] at hmono
  rw [rieszQuadratureDefect_eq ht]
  exact hmono

/-- **Equation (6), upper bound by the polar continuum.** -/
theorem rieszQuadratureDefect_le_third {t : ℝ} (ht : 1 ≤ t) :
    rieszQuadratureDefect t ≤ t / 3 := by
  have := rieszProgressionSum_nonneg ht
  rw [rieszQuadratureDefect]
  linarith

/-! ## The sharp cutoff bound -/

theorem unitRieszLogProfile_eq_progression (v : ℝ) :
    unitRieszLogProfile v = 3 * rieszProgressionSum (Real.exp v) / Real.exp v := by
  have hx : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hsx : (0 : ℝ) < Real.sqrt (Real.exp v) := Real.sqrt_pos.mpr hx
  have hsplit : rieszProgressionSum (Real.exp v)
      = (⌊Real.exp v⌋₊ : ℝ)
        - unitRieszSqrtPrefixMass ⌊Real.exp v⌋₊ / Real.sqrt (Real.exp v) := by
    rw [rieszProgressionSum, unitRieszSqrtPrefixMass, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.sqrt_div (by positivity)]
  rw [unitRieszLogProfile_eq_div v, hsplit]
  field_simp

/-- **The sharp cutoff bound.**  `1 - W(t) = 3 eta(t)/t <= 3/t`, i.e. the aperture profile is
within `3 e^{-v}` of one. -/
theorem one_sub_unitRieszLogProfile_le {v : ℝ} (hv : 0 ≤ v) :
    1 - unitRieszLogProfile v ≤ 3 * Real.exp (-v) := by
  have hx1 : (1 : ℝ) ≤ Real.exp v := Real.one_le_exp hv
  have hx : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hdef := rieszQuadratureDefect_le_one hx1
  rw [rieszQuadratureDefect] at hdef
  have hgoal : 1 - 3 * rieszProgressionSum (Real.exp v) / Real.exp v ≤ 3 / Real.exp v := by
    have h1 : (1 : ℝ) - 3 * rieszProgressionSum (Real.exp v) / Real.exp v
        = (Real.exp v - 3 * rieszProgressionSum (Real.exp v)) / Real.exp v := by
      field_simp
    rw [h1, div_le_div_iff_of_pos_right hx]
    linarith [hdef]
  rw [unitRieszLogProfile_eq_progression v, Real.exp_neg, ← div_eq_mul_inv]
  exact hgoal

end GaloisForLFunctions.RHTower

end
