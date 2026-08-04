import GaloisForLFunctions.RHTower.SelfDualFixedSectorVariation

noncomputable section

open Complex Filter Set Metric

namespace GaloisForLFunctions.RHTower

def polynomialCompleted (t : ℕ × ℕ) (z : ℂ) : ℂ :=
  z ^ t.1 * ((z - 1) * (z + 1)) ^ t.2

private theorem analyticOrderAt_sub_self (a : ℂ) :
    analyticOrderAt (fun z : ℂ => z - a) a = 1 := by
  have h : AnalyticAt ℂ (fun z : ℂ => z - a) a :=
    analyticAt_id.sub analyticAt_const
  exact h.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by simp)

private theorem analyticOrderAt_sub_self_pow (a : ℂ) (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (z - a) ^ n) a = (n : ℕ∞) := by
  have h : AnalyticAt ℂ (fun z : ℂ => z - a) a :=
    analyticAt_id.sub analyticAt_const
  change analyticOrderAt ((fun z : ℂ => z - a) ^ n) a = _
  rw [analyticOrderAt_pow h, analyticOrderAt_sub_self, nsmul_eq_mul, mul_one]

theorem polynomialCompleted_order_zero (n k : ℕ) :
    analyticOrderAt (polynomialCompleted (n, k)) 0 = (n : ℕ∞) := by
  have hz : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0 := analyticAt_id.pow n
  have hzOrder : analyticOrderAt (fun z : ℂ => z ^ n) 0 = (n : ℕ∞) := by
    change analyticOrderAt ((id : ℂ → ℂ) ^ n) 0 = _
    rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id, nsmul_eq_mul, mul_one]
  have hquad : AnalyticAt ℂ (fun z : ℂ => (z - 1) * (z + 1)) 0 := by fun_prop
  have hquad0 : analyticOrderAt (fun z : ℂ => (z - 1) * (z + 1)) 0 = 0 :=
    hquad.analyticOrderAt_eq_zero.mpr (by norm_num)
  change analyticOrderAt (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) 0 = _
  rw [show (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) =
      (fun z : ℂ => z ^ n) * (fun z : ℂ => (z - 1) * (z + 1)) ^ k by
        funext z; rfl]
  rw [analyticOrderAt_mul hz (hquad.pow k), hzOrder,
    analyticOrderAt_pow hquad, hquad0]
  simp

theorem polynomialCompleted_order_one (n k : ℕ) :
    analyticOrderAt (polynomialCompleted (n, k)) 1 = (k : ℕ∞) := by
  have hz : AnalyticAt ℂ (fun z : ℂ => z ^ n) 1 := analyticAt_id.pow n
  have hminus : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
  have hplus : AnalyticAt ℂ (fun z : ℂ => z + 1) 1 := by fun_prop
  have hz0 : analyticOrderAt (fun z : ℂ => z ^ n) 1 = 0 :=
    hz.analyticOrderAt_eq_zero.mpr (by simp)
  have hplus0 : analyticOrderAt (fun z : ℂ => z + 1) 1 = 0 :=
    hplus.analyticOrderAt_eq_zero.mpr (by norm_num)
  change analyticOrderAt (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) 1 = _
  rw [show (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) =
      (fun z : ℂ => z ^ n) * (fun z : ℂ => (z - 1) * (z + 1)) ^ k by
        funext z; rfl,
    show (fun z : ℂ => (z - 1) * (z + 1)) =
      (fun z : ℂ => z - 1) * (fun z : ℂ => z + 1) by funext z; rfl]
  rw [analyticOrderAt_mul hz ((hminus.mul hplus).pow k), hz0,
    analyticOrderAt_pow (hminus.mul hplus), analyticOrderAt_mul hminus hplus,
    show analyticOrderAt (fun z : ℂ => z - 1) 1 = 1 by
      simpa using analyticOrderAt_sub_self (1 : ℂ),
    hplus0]
  simp

theorem polynomialCompleted_order_neg_one (n k : ℕ) :
    analyticOrderAt (polynomialCompleted (n, k)) (-1) = (k : ℕ∞) := by
  have hz : AnalyticAt ℂ (fun z : ℂ => z ^ n) (-1) := analyticAt_id.pow n
  have hminus : AnalyticAt ℂ (fun z : ℂ => z - 1) (-1) := by fun_prop
  have hplus : AnalyticAt ℂ (fun z : ℂ => z + 1) (-1) := by fun_prop
  have hz0 : analyticOrderAt (fun z : ℂ => z ^ n) (-1) = 0 :=
    hz.analyticOrderAt_eq_zero.mpr (by simp)
  have hminus0 : analyticOrderAt (fun z : ℂ => z - 1) (-1) = 0 :=
    hminus.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hplus1 : analyticOrderAt (fun z : ℂ => z + 1) (-1) = 1 := by
    convert analyticOrderAt_sub_self (-1 : ℂ) using 1 <;> ring_nf
  change analyticOrderAt (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) (-1) = _
  rw [show (fun z : ℂ => z ^ n * ((z - 1) * (z + 1)) ^ k) =
      (fun z : ℂ => z ^ n) * (fun z : ℂ => (z - 1) * (z + 1)) ^ k by
        funext z; rfl,
    show (fun z : ℂ => (z - 1) * (z + 1)) =
      (fun z : ℂ => z - 1) * (fun z : ℂ => z + 1) by funext z; rfl]
  rw [analyticOrderAt_mul hz ((hminus.mul hplus).pow k), hz0,
    analyticOrderAt_pow (hminus.mul hplus), analyticOrderAt_mul hminus hplus,
    hminus0, hplus1]
  simp

def polynomialSelfDualFamily : CompletedSelfDualAnalyticFamily (ℕ × ℕ) where
  completed := polynomialCompleted
  center := 0
  radius := 1
  radius_nonneg := by norm_num
  analytic := by
    intro t z _
    exact (analyticAt_id.pow t.1).mul
      (((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.add analyticAt_const)).pow t.2)
  nontrivial := by
    intro t
    refine ⟨2, ?_⟩
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (mul_ne_zero (by norm_num) (by norm_num)))
  rootNumber := fun t => (-1 : ℂ) ^ t.1
  rootNumber_ne_zero := by intro t; exact pow_ne_zero _ (by norm_num)
  functionalEquation := by
    intro t z
    simp only [polynomialCompleted]
    rw [show 2 * ((0 : ℝ) : ℂ) - z = -z by norm_num]
    change (-z) ^ t.1 * ((-z - 1) * (-z + 1)) ^ t.2 =
      (-1 : ℂ) ^ t.1 * (z ^ t.1 * ((z - 1) * (z + 1)) ^ t.2)
    rw [neg_pow]
    have hq : (-z - 1) * (-z + 1) = (z - 1) * (z + 1) := by ring
    rw [hq]
    ring

def polynomialWindowMultiplicity (n k : ℕ) : ℝ →₀ ℕ :=
  Finsupp.single 0 n + Finsupp.single 1 k + Finsupp.single (-1) k

theorem polynomialSelfDualFamily_realWindowMultiplicity (n k : ℕ) :
    polynomialSelfDualFamily.realWindowMultiplicity (n, k) =
      polynomialWindowMultiplicity n k := by
  ext x
  by_cases hx0 : x = 0
  · subst x
    rw [polynomialSelfDualFamily.realWindowMultiplicity_apply_of_mem]
    · have h := congrArg ENat.toNat (polynomialCompleted_order_zero n k)
      simpa [polynomialSelfDualFamily, polynomialWindowMultiplicity] using h
    · simp [polynomialSelfDualFamily]
  by_cases hx1 : x = 1
  · subst x
    rw [polynomialSelfDualFamily.realWindowMultiplicity_apply_of_mem]
    · have h := congrArg ENat.toNat (polynomialCompleted_order_one n k)
      have hne : (1 : ℝ) ≠ -1 := by norm_num
      simpa [polynomialSelfDualFamily, polynomialWindowMultiplicity, hne] using h
    · simp [polynomialSelfDualFamily]
  by_cases hxneg1 : x = -1
  · subst x
    rw [polynomialSelfDualFamily.realWindowMultiplicity_apply_of_mem]
    · have h := congrArg ENat.toNat (polynomialCompleted_order_neg_one n k)
      have hne : (-1 : ℝ) ≠ 1 := by norm_num
      simpa [polynomialSelfDualFamily, polynomialWindowMultiplicity, hne] using h
    · simp [polynomialSelfDualFamily]
  have hx0c : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1c : (x : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hx1
  have hxneg1c : (x : ℂ) + 1 ≠ 0 := by
    have hre : x + 1 ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    exact_mod_cast hre
  have hvalue : polynomialCompleted (n, k) (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ hx0c)
      (pow_ne_zero _ (mul_ne_zero hx1c hxneg1c))
  have horder : analyticOrderAt (polynomialCompleted (n, k)) (x : ℂ) = 0 :=
    (polynomialSelfDualFamily.analytic (n, k) (x : ℂ) (Set.mem_univ _))
      |>.analyticOrderAt_eq_zero.mpr hvalue
  have horderF :
      analyticOrderAt (polynomialSelfDualFamily.completed (n, k)) (x : ℂ) = 0 := by
    simpa [polynomialSelfDualFamily] using horder
  by_cases hxball : x ∈ Metric.closedBall polynomialSelfDualFamily.center
      polynomialSelfDualFamily.radius
  · rw [polynomialSelfDualFamily.realWindowMultiplicity_apply_of_mem (n, k) x hxball,
      horderF]
    simp [polynomialWindowMultiplicity, hx0, hx1, hxneg1]
  · rw [polynomialSelfDualFamily.realWindowMultiplicity_apply_of_not_mem (n, k) x hxball]
    simp [polynomialWindowMultiplicity, hx0, hx1, hxneg1]

theorem polynomialSelfDualFamily_analyticRank (n k : ℕ) :
    polynomialSelfDualFamily.toSelfDualRealZeroFamily.analyticRank (n, k) = n := by
  rw [polynomialSelfDualFamily.analyticRank_eq_orderAt_center]
  change (analyticOrderAt (polynomialCompleted (n, k)) 0).toNat = n
  rw [polynomialCompleted_order_zero]
  simp

theorem polynomialSelfDualFamily_defectRank (n k : ℕ) :
    polynomialSelfDualFamily.toSelfDualRealZeroFamily.defectRank (n, k) = n + 2 * k := by
  change fixedSectorDefectRank (polynomialSelfDualFamily.realWindowMultiplicity (n, k)) = _
  rw [polynomialSelfDualFamily_realWindowMultiplicity]
  simp [fixedSectorDefectRank, polynomialWindowMultiplicity, Finsupp.sum_add_index']
  omega

theorem polynomialSelfDualFamily_upperOffCentralMultiplicity (n k : ℕ) :
    polynomialSelfDualFamily.toSelfDualRealZeroFamily.upperOffCentralMultiplicity (n, k) = k := by
  have h := polynomialSelfDualFamily.toSelfDualRealZeroFamily
    |>.defectRank_eq_analyticRank_add_twice_upper (n, k)
  rw [polynomialSelfDualFamily_defectRank, polynomialSelfDualFamily_analyticRank] at h
  omega

theorem polynomialSelfDualFamily_centralKZeroRankInt (n k : ℕ) :
    polynomialSelfDualFamily.centralKZeroRankInt (n, k) =
      if n = 0 then 0 else 1 := by
  rw [polynomialSelfDualFamily.centralKZeroRankInt_eq_supportIndicator,
    polynomialSelfDualFamily_analyticRank]

theorem polynomialSelfDualFamily_fixedSectorDefectVariation
    (n₀ k₀ n₁ k₁ : ℕ) :
    polynomialSelfDualFamily.fixedSectorDefectVariation (n₀, k₀) (n₁, k₁) =
      ((n₁ + 2 * k₁ : ℕ) : ℤ) - ((n₀ + 2 * k₀ : ℕ) : ℤ) := by
  rw [CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation,
    polynomialSelfDualFamily_defectRank, polynomialSelfDualFamily_defectRank]

theorem polynomialSelfDualFamily_analyticRankVariation
    (n₀ k₀ n₁ k₁ : ℕ) :
    polynomialSelfDualFamily.analyticRankVariation (n₀, k₀) (n₁, k₁) =
      (n₁ : ℤ) - (n₀ : ℤ) := by
  rw [CompletedSelfDualAnalyticFamily.analyticRankVariation,
    polynomialSelfDualFamily_analyticRank, polynomialSelfDualFamily_analyticRank]

theorem polynomialSelfDualFamily_upperOffCentralMultiplicityVariation
    (n₀ k₀ n₁ k₁ : ℕ) :
    polynomialSelfDualFamily.upperOffCentralMultiplicityVariation (n₀, k₀) (n₁, k₁) =
      (k₁ : ℤ) - (k₀ : ℤ) := by
  rw [CompletedSelfDualAnalyticFamily.upperOffCentralMultiplicityVariation,
    polynomialSelfDualFamily_upperOffCentralMultiplicity,
    polynomialSelfDualFamily_upperOffCentralMultiplicity]

theorem polynomialSelfDualFamily_centralKZeroVariation
    (n₀ k₀ n₁ k₁ : ℕ) :
    polynomialSelfDualFamily.centralKZeroVariation (n₀, k₀) (n₁, k₁) =
      (if n₁ = 0 then 0 else 1) - (if n₀ = 0 then 0 else 1) := by
  rw [CompletedSelfDualAnalyticFamily.centralKZeroVariation,
    polynomialSelfDualFamily_centralKZeroRankInt,
    polynomialSelfDualFamily_centralKZeroRankInt]

end GaloisForLFunctions.RHTower
