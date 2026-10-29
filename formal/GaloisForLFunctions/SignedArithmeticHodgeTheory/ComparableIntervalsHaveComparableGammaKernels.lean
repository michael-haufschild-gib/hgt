import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaExteriorSubsets

/-!+# Uniform Gamma kernel comparison on bounded intervals

Bounded changes of distance, with bounded distance ratio, change the Gamma
density by a fixed factor. For adjacent comparable intervals, the integrated
boundary defect replaces the false pointwise comparison at their common
endpoint. Both estimates pay the actual rectangle by its far-end conductance.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open ArithmeticCastelnuovoSeveri.MeanZeroIntervals

/-- A common comparison cost for interval pairs and separated exterior rows. -/
def stoppingGammaKernelConstant : ℝ := 32 * Real.exp 2

theorem stoppingGammaKernelConstant_pos : 0 < stoppingGammaKernelConstant := by
  unfold stoppingGammaKernelConstant
  positivity

private theorem one_sub_pow_le_nat_mul {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
  have hp (k : ℕ) : r ^ k ≤ 1 := by
    induction k with
    | zero => simp only [pow_zero, le_refl]
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih hr0).trans (by simpa only [one_mul] using hr1)
  induction n with
  | zero => simp only [pow_zero, sub_self, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right (hp n) (sub_nonneg.mpr hr1)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [ih, h]

/-- The Gamma density has a uniform comparison under a bounded relative and additive displacement. -/
theorem archLevyDensity_le_seven_exp {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hr : t ≤ 7 * s) (hd : t - s ≤ 2) :
    archLevyDensity s ≤ (7 * Real.exp 1) * archLevyDensity t := by
  have ht : 0 < t := hs.trans_le hst
  have hds : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hs]))
  have hdt : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hpow := one_sub_pow_le_nat_mul (Real.exp_pos (-2 * s)).le
    (Real.exp_le_one_iff.mpr (by linarith only [hs])) 7
  have he : Real.exp (-2 * t) ≥ Real.exp (-2 * s) ^ 7 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hr]
  have hden : 1 - Real.exp (-2 * t) ≤ 7 * (1 - Real.exp (-2 * s)) := by
    norm_num only [Nat.cast_ofNat] at hpow
    linarith only [he, hpow]
  have hnum : Real.exp (-s / 2) ≤ Real.exp 1 * Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hd]
  unfold archLevyDensity
  rw [← mul_div_assoc, div_le_div_iff₀ hds hdt]
  calc
    _ ≤ (Real.exp 1 * Real.exp (-t / 2)) * (7 * (1 - Real.exp (-2 * s))) :=
      mul_le_mul hnum hden hdt.le (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
    _ = _ := by ring

/-- On distances at most two, the Gamma conductance has a fixed inverse-distance floor. -/
theorem one_le_two_exp_mul_distance_density {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    1 ≤ 2 * Real.exp 1 * t * archLevyDensity t := by
  have hden : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hd : 1 - Real.exp (-2 * t) ≤ 2 * t := by
    have h := Real.add_one_le_exp (-2 * t)
    linarith only [h]
  have hn : 1 ≤ Real.exp 1 * Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith only [ht2])
  unfold archLevyDensity
  rw [← mul_div_assoc, le_div_iff₀ hden, one_mul]
  calc
    _ ≤ 2 * t := hd
    _ ≤ (2 * t) * (Real.exp 1 * Real.exp (-t / 2)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * t)
    _ = _ := by ring

private theorem seven_exp_le_stopping : 7 * Real.exp 1 ≤ stoppingGammaKernelConstant := by
  have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  unfold stoppingGammaKernelConstant
  nlinarith only [he, Real.exp_pos 2]

/-- Separated short intervals with a width-scale gap have uniformly comparable endpoint kernels. -/
theorem gammaIntervalKernel_le_stopping_of_gap {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hu : b - a ≤ 1) (hv : d - c ≤ 1)
    (hgu : b - a ≤ 3 * (c - b)) (hgv : d - c ≤ 3 * (c - b)) :
    gammaIntervalKernel a b c d ≤
      ENNReal.ofReal (stoppingGammaKernelConstant *
        ((b - a) * (d - c) * archLevyDensity (d - a))) := by
  have hg : 0 < c - b := sub_pos.mpr hbc
  have hf : 0 < d - a := by linarith only [hab, hbc, hcd]
  have hk := archLevyDensity_le_seven_exp hg
    (by linarith only [hab, hcd]) (by linarith only [hgu, hgv])
    (by linarith only [hu, hv])
  have hcost : archLevyDensity (c - b) ≤
      stoppingGammaKernelConstant * archLevyDensity (d - a) :=
    hk.trans (mul_le_mul_of_nonneg_right seven_exp_le_stopping (archLevyDensity_pos hf).le)
  refine (gammaIntervalKernel_le_near hab hbc hcd).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_left hcost
    (mul_nonneg (sub_pos.mpr hab).le (sub_pos.mpr hcd).le)
  nlinarith only [h]

/-- Comparable touching intervals retain a finite averaged-kernel bound. -/
theorem gammaIntervalKernel_le_stopping_of_touching {a b d : ℝ}
    (hab : a < b) (hbd : b < d) (hu : b - a ≤ 1) (hv : d - b ≤ 1)
    (huv : b - a ≤ 3 * (d - b)) (hvu : d - b ≤ 3 * (b - a)) :
    gammaIntervalKernel a b b d ≤
      ENNReal.ofReal (stoppingGammaKernelConstant *
        ((b - a) * (d - b) * archLevyDensity (d - a))) := by
  have hu0 : 0 < b - a := sub_pos.mpr hab
  have hv0 : 0 < d - b := sub_pos.mpr hbd
  have hf : 0 < d - a := by linarith only [hab, hbd]
  have hfar : 0 ≤ archLevyDensity (d - a) := (archLevyDensity_pos hf).le
  have hsub : Ioo b d ⊆ (Ioo a b)ᶜ := by
    intro y hy hy'
    exact (not_lt_of_ge hy.1.le) hy'.2
  have hbound := (gammaIntervalKernel_le_defect_add_width hab (Or.inl le_rfl)).trans
    (add_le_add (gamma_interval_exterior_subset_defect_le hab hu hsub) le_rfl)
  have hdensity := archLevyDensity_le_seven_exp hu0
    (by linarith only [hbd]) (by linarith only [hvu, hu0])
    (by linarith only [hv])
  have hfloor := one_le_two_exp_mul_distance_density hf (by linarith only [hu, hv])
  have hwidth : d - a ≤ 4 * (d - b) := by linarith only [huv]
  have hp : 1 ≤ 8 * Real.exp 1 * (d - b) * archLevyDensity (d - a) := by
    have hm := mul_le_mul_of_nonneg_right hwidth
      (mul_nonneg (by positivity : 0 ≤ 2 * Real.exp 1) hfar)
    nlinarith only [hfloor, hm]
  have hehalf : Real.exp (1 / 2) * Real.exp 1 ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by norm_num)
  have heone : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hboundary : Real.exp (1 / 2) * (b - a) ≤
      (8 * Real.exp 2) * ((b - a) * (d - b) * archLevyDensity (d - a)) := by
    have hm := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (Real.exp_pos (1 / 2)).le hu0.le)
    have he := mul_le_mul_of_nonneg_right hehalf
      (by positivity : 0 ≤ 8 * ((b - a) * (d - b) * archLevyDensity (d - a)))
    nlinarith only [hm, he]
  have hregular : (b - a) * (d - b) * archLevyDensity (b - a) ≤
      (7 * Real.exp 2) * ((b - a) * (d - b) * archLevyDensity (d - a)) := by
    have h := mul_le_mul_of_nonneg_left hdensity (mul_nonneg hu0.le hv0.le)
    have he := mul_le_mul_of_nonneg_right heone
      (by positivity : 0 ≤ 7 * ((b - a) * (d - b) * archLevyDensity (d - a)))
    nlinarith only [h, he]
  rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hu0.le)
    (mul_nonneg (mul_nonneg hu0.le hv0.le) (archLevyDensity_pos hu0).le)] at hbound
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hnonneg : 0 ≤ Real.exp 2 * ((b - a) * (d - b) * archLevyDensity (d - a)) := by positivity
  unfold stoppingGammaKernelConstant
  nlinarith only [hboundary, hregular, hnonneg]

/-- A width-scale exterior gap makes every actual row comparable to its far-end charge. -/
theorem gammaKernel_le_stopping_far_of_gap {a b x y : ℝ}
    (hx : x ∈ Ioo a b) (hw : b - a ≤ 1)
    (hgap : b + (b - a) / 3 ≤ y ∨ y + (b - a) / 3 ≤ a) :
    ENNReal.ofReal (archLevyDensity |y - x|) ≤
      ENNReal.ofReal stoppingGammaKernelConstant * gammaFarCharge a b y := by
  have hab : a < b := hx.1.trans hx.2
  rcases hgap with hr | hl
  · have hyb : b < y := by linarith only [hab, hr]
    have hs : 0 < y - x := by linarith only [hx.2, hyb]
    have ht : 0 < y - a := by linarith only [hab, hyb]
    have hyn : y ∉ Ioo a b := fun h => (not_lt_of_ge hyb.le) h.2
    rw [abs_of_pos hs, gammaFarCharge, if_neg hyn, max_eq_left (by linarith only [hab, hyb]),
      ← ENNReal.ofReal_mul stoppingGammaKernelConstant_pos.le]
    apply ENNReal.ofReal_le_ofReal
    have h := archLevyDensity_le_seven_exp hs
      (by linarith only [hx.1]) (by linarith only [hr, hx.2, hab])
      (by linarith only [hx.1, hx.2, hw])
    exact h.trans (mul_le_mul_of_nonneg_right seven_exp_le_stopping (archLevyDensity_pos ht).le)
  · have hya : y < a := by linarith only [hab, hl]
    have hs : 0 < x - y := by linarith only [hx.1, hya]
    have ht : 0 < b - y := by linarith only [hab, hya]
    have hyn : y ∉ Ioo a b := fun h => (not_lt_of_ge hya.le) h.1
    rw [abs_of_neg (by linarith only [hs] : y - x < 0), neg_sub,
      gammaFarCharge, if_neg hyn, max_eq_right (by linarith only [hab, hya]),
      ← ENNReal.ofReal_mul stoppingGammaKernelConstant_pos.le]
    apply ENNReal.ofReal_le_ofReal
    have h := archLevyDensity_le_seven_exp hs
      (by linarith only [hx.2]) (by linarith only [hl, hx.1, hab])
      (by linarith only [hx.1, hx.2, hw])
    exact h.trans (mul_le_mul_of_nonneg_right seven_exp_le_stopping (archLevyDensity_pos ht).le)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.archLevyDensity_le_seven_exp
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.gammaIntervalKernel_le_stopping_of_gap
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.gammaIntervalKernel_le_stopping_of_touching
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.gammaKernel_le_stopping_far_of_gap
