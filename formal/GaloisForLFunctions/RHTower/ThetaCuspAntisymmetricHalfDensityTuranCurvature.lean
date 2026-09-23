import GaloisForLFunctions.RHTower.ThetaCuspContinuousHalfDensityResidualTail
import GaloisForLFunctions.RHTower.PrimeArchThetaReflectedBudgetTailTransfer
import GaloisForLFunctions.RHTower.PrimeArchThetaHalfDensityDampedTail

open Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

def thetaCuspAtomMoment (k n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ k * thetaCuspSourceTerm x n

theorem integrableOn_natPow_mul_thetaCuspSourceTerm
    (k : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x ^ k * thetaCuspSourceTerm x n) (Ioi 0) := by
  have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    k thetaCuspSeedPolynomial hn
  apply h.congr
  filter_upwards with x
  rw [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom n) x]

theorem thetaCuspAtomMoment_pos (k : ℕ) {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspAtomMoment k n := by
  let f : ℝ → ℝ := fun x => x ^ k * thetaCuspSourceTerm x n
  have hfcont : Continuous f := by
    dsimp [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa [f] using integrableOn_natPow_mul_thetaCuspSourceTerm k hn
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le k)
      (thetaCuspSourceTerm_nonneg_of_pos hx n)
  unfold thetaCuspAtomMoment
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  exact ne_of_gt (mul_pos (by positivity)
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos (by norm_num) hn))

theorem thetaCuspAtomOddMoment_series {n : ℕ} (hn : 0 < n) :
    (∑' j : ℕ,
      thetaCuspAtomMoment (2 * j + 1) n /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) =
      Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun j x =>
    2 * ((x / 2) ^ (2 * j + 1) /
      (Nat.factorial (2 * j + 1) : ℝ)) * thetaCuspSourceTerm x n
  let G : ℝ → ℝ := fun x =>
    2 * (Real.sinh (x / 2) * thetaCuspSourceTerm x n)
  have hFmeas : ∀ j, AEStronglyMeasurable (F j) μ := by
    intro j
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F j))).aestronglyMeasurable
  have hFnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro j
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (pow_nonneg (div_nonneg hx.le (by norm_num)) _)
        (by positivity)))
      (thetaCuspSourceTerm_nonneg_of_pos hx n)
  have hsum : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (G x) := by
    filter_upwards with x
    have h := (Real.hasSum_sinh (x / 2)).mul_left
      (2 * thetaCuspSourceTerm x n)
    simpa [F, G, mul_assoc, mul_comm, mul_left_comm] using h
  have hG : Integrable G μ := by
    exact (integrableOn_sinh_half_mul_thetaCuspSourceTerm hn).const_mul 2
  have hswap := integral_tsum_of_nonneg_hasSum μ F G hFmeas hFnonneg hsum hG
  have hterm (j : ℕ) :
      (∫ x, F j x ∂μ) =
        thetaCuspAtomMoment (2 * j + 1) n /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ)) := by
    change (∫ x : ℝ in Ioi 0,
      2 * ((x / 2) ^ (2 * j + 1) /
        (Nat.factorial (2 * j + 1) : ℝ)) * thetaCuspSourceTerm x n) = _
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (1 / ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) *
            (x ^ (2 * j + 1) * thetaCuspSourceTerm x n) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [thetaCusp_two_mul_oddTaylorTerm_eq]
        ring
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        unfold thetaCuspAtomMoment
        ring
  calc
    (∑' j : ℕ,
        thetaCuspAtomMoment (2 * j + 1) n /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j + 1) : ℝ))) =
        ∑' j : ℕ, ∫ x, F j x ∂μ := by
      apply tsum_congr
      intro j
      exact (hterm j).symm
    _ = ∫ x, G x ∂μ := hswap.symm
    _ = 2 * ∫ x : ℝ in Ioi 0,
        Real.sinh (x / 2) * thetaCuspSourceTerm x n := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := two_mul_integral_sinh_half_mul_thetaCuspSourceTerm_eq_orientation hn

theorem thetaCuspAtomEvenMoment_series {n : ℕ} (hn : 0 < n) :
    2 * (∑' j : ℕ,
      thetaCuspAtomMoment (2 * j) n /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) =
      (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ (2 : ℕ)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun j x =>
    2 * ((x / 2) ^ (2 * j) /
      (Nat.factorial (2 * j) : ℝ)) * thetaCuspSourceTerm x n
  let G : ℝ → ℝ := fun x =>
    2 * (Real.cosh (x / 2) * thetaCuspSourceTerm x n)
  have hFmeas : ∀ j, AEStronglyMeasurable (F j) μ := by
    intro j
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F j))).aestronglyMeasurable
  have hFnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro j
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (pow_nonneg (div_nonneg hx.le (by norm_num)) _)
        (by positivity)))
      (thetaCuspSourceTerm_nonneg_of_pos hx n)
  have hsum : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (G x) := by
    filter_upwards with x
    have h := (Real.hasSum_cosh (x / 2)).mul_left
      (2 * thetaCuspSourceTerm x n)
    simpa [F, G, mul_assoc, mul_comm, mul_left_comm] using h
  have hG : Integrable G μ := by
    exact (integrableOn_cosh_half_mul_thetaCuspSourceTerm hn).const_mul 2
  have hswap := integral_tsum_of_nonneg_hasSum μ F G hFmeas hFnonneg hsum hG
  have hterm (j : ℕ) :
      (∫ x, F j x ∂μ) =
        2 * thetaCuspAtomMoment (2 * j) n /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ)) := by
    change (∫ x : ℝ in Ioi 0,
      2 * ((x / 2) ^ (2 * j) /
        (Nat.factorial (2 * j) : ℝ)) * thetaCuspSourceTerm x n) = _
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (2 / ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) *
            (x ^ (2 * j) * thetaCuspSourceTerm x n) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [thetaCusp_two_mul_evenTaylorTerm_eq]
        ring
      _ = _ := by
        rw [MeasureTheory.integral_const_mul]
        unfold thetaCuspAtomMoment
        ring
  calc
    2 * (∑' j : ℕ,
        thetaCuspAtomMoment (2 * j) n /
          ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) =
        ∑' j : ℕ, 2 *
          (thetaCuspAtomMoment (2 * j) n /
            ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) := by
      rw [tsum_mul_left]
    _ = ∑' j : ℕ, ∫ x, F j x ∂μ := by
      apply tsum_congr
      intro j
      rw [hterm]
      ring
    _ = ∫ x, G x ∂μ := hswap.symm
    _ = 2 * ∫ x : ℝ in Ioi 0,
        Real.cosh (x / 2) * thetaCuspSourceTerm x n := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget hn

def thetaCuspCoshTiltOrientationExpectation (n : ℕ) : ℝ :=
  (∫ x : ℝ in Ioi 0,
      Real.tanh (x / 2) *
        (Real.cosh (x / 2) * thetaCuspSourceTerm x n)) /
    ∫ x : ℝ in Ioi 0,
      Real.cosh (x / 2) * thetaCuspSourceTerm x n

theorem thetaCuspCoshTiltOrientationExpectation_eq
    {n : ℕ} (hn : 0 < n) :
    thetaCuspCoshTiltOrientationExpectation n =
      1 / (4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1) := by
  have hdenpos : 0 < 4 * Real.pi * (n : ℝ) ^ (2 : ℕ) - 1 := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three, sq_nonneg ((n : ℝ) - 1)]
  have hcoshpos : 0 < ∫ x : ℝ in Ioi 0,
      Real.cosh (x / 2) * thetaCuspSourceTerm x n := by
    have h := two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget hn
    have hexp := Real.exp_pos (-Real.pi * (n : ℝ) ^ (2 : ℕ))
    nlinarith
  have hnum : (∫ x : ℝ in Ioi 0,
      Real.tanh (x / 2) *
        (Real.cosh (x / 2) * thetaCuspSourceTerm x n)) =
      ∫ x : ℝ in Ioi 0,
        Real.sinh (x / 2) * thetaCuspSourceTerm x n := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos _)]
  have hodd := two_mul_integral_sinh_half_mul_thetaCuspSourceTerm_eq_orientation hn
  have heven := two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget hn
  unfold thetaCuspCoshTiltOrientationExpectation
  rw [hnum]
  field_simp [hcoshpos.ne', hdenpos.ne']
  nlinarith

/-! ## Exact first-atom even tails -/

def thetaCuspFirstAtomEvenWeight (j : ℕ) : ℝ :=
  2 * thetaCuspAtomMoment (2 * j) 1 /
    ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))

def thetaCuspFirstAtomEvenSeriesBudget : ℝ :=
  ∑' j : ℕ, thetaCuspFirstAtomEvenWeight j

def thetaCuspFirstAtomEvenTail (r : ℕ) : ℝ :=
  ∑' j : ℕ, thetaCuspFirstAtomEvenWeight (j + r)

theorem thetaCuspAtomMoment_one_eq_totalMoment (k : ℕ) :
    thetaCuspAtomMoment k 1 = thetaCuspTotalMoment k := by
  rw [thetaCuspTotalMoment_eq_integral_Ioi]
  rfl

theorem thetaCuspFirstAtomEvenWeight_eq_rawEvenMoment (j : ℕ) :
    thetaCuspFirstAtomEvenWeight j =
      thetaCuspAtomRawEvenMoment j 1 /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ)) := by
  rw [thetaCuspFirstAtomEvenWeight, thetaCuspAtomRawEvenMoment]
  rfl

theorem thetaCuspFirstAtomEvenWeight_pos (j : ℕ) :
    0 < thetaCuspFirstAtomEvenWeight j := by
  rw [thetaCuspFirstAtomEvenWeight]
  exact div_pos (mul_pos (by norm_num)
      (thetaCuspAtomMoment_pos (2 * j) (by norm_num)))
    (mul_pos (by positivity) (by positivity))

theorem summable_thetaCuspFirstAtomEvenWeight :
    Summable thetaCuspFirstAtomEvenWeight := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun j x =>
    2 * ((x / 2) ^ (2 * j) /
      (Nat.factorial (2 * j) : ℝ)) * thetaCuspSourceTerm x 1
  let G : ℝ → ℝ := fun x =>
    2 * (Real.cosh (x / 2) * thetaCuspSourceTerm x 1)
  have hFmeas : ∀ j, AEStronglyMeasurable (F j) μ := by
    intro j
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F j))).aestronglyMeasurable
  have hFnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ F j x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro j
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (pow_nonneg (div_nonneg hx.le (by norm_num)) _)
        (by positivity)))
      (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsum : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (G x) := by
    filter_upwards with x
    have h := (Real.hasSum_cosh (x / 2)).mul_left
      (2 * thetaCuspSourceTerm x 1)
    simpa [F, G, mul_assoc, mul_comm, mul_left_comm] using h
  have hG : Integrable G μ := by
    exact (integrableOn_cosh_half_mul_thetaCuspSourceTerm
      (n := 1) (by norm_num)).const_mul 2
  have hint := summable_integral_of_nonneg_hasSum μ F G
    hFmeas hFnonneg hsum hG
  refine hint.congr ?_
  intro j
  change (∫ x : ℝ in Ioi 0,
      2 * ((x / 2) ^ (2 * j) /
        (Nat.factorial (2 * j) : ℝ)) * thetaCuspSourceTerm x 1) =
    thetaCuspFirstAtomEvenWeight j
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (2 / ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) *
          (x ^ (2 * j) * thetaCuspSourceTerm x 1) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaCusp_two_mul_evenTaylorTerm_eq]
      ring
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      unfold thetaCuspFirstAtomEvenWeight thetaCuspAtomMoment
      ring

theorem thetaCuspFirstAtomEvenSeriesBudget_eq :
    thetaCuspFirstAtomEvenSeriesBudget =
      (4 * Real.pi - 1) * Real.exp (-Real.pi) := by
  have h := thetaCuspAtomEvenMoment_series (n := 1) (by norm_num)
  norm_num only [Nat.cast_one, one_pow] at h
  unfold thetaCuspFirstAtomEvenSeriesBudget thetaCuspFirstAtomEvenWeight
  calc
    (∑' j : ℕ, 2 * thetaCuspAtomMoment (2 * j) 1 /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) =
      2 * (∑' j : ℕ, thetaCuspAtomMoment (2 * j) 1 /
        ((4 : ℝ) ^ j * (Nat.factorial (2 * j) : ℝ))) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro j
          ring
    _ = _ := by simpa only [mul_one] using h

theorem thetaCuspFirstAtomEvenTail_split (r : ℕ) :
    (∑ j ∈ Finset.range r, thetaCuspFirstAtomEvenWeight j) +
        thetaCuspFirstAtomEvenTail r = thetaCuspFirstAtomEvenSeriesBudget := by
  simpa [thetaCuspFirstAtomEvenTail, thetaCuspFirstAtomEvenSeriesBudget,
    Nat.add_comm] using
      (summable_thetaCuspFirstAtomEvenWeight.sum_add_tsum_nat_add r)

theorem thetaCuspFirstAtomEvenTail_recurrence (r : ℕ) :
    thetaCuspFirstAtomEvenTail r =
      thetaCuspFirstAtomEvenWeight r + thetaCuspFirstAtomEvenTail (r + 1) := by
  have hs : Summable (fun j => thetaCuspFirstAtomEvenWeight (j + r)) :=
    (summable_nat_add_iff r).2 summable_thetaCuspFirstAtomEvenWeight
  have h := hs.tsum_eq_zero_add
  simpa [thetaCuspFirstAtomEvenTail, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

theorem thetaCuspFirstAtomEvenTail_nonneg (r : ℕ) :
    0 ≤ thetaCuspFirstAtomEvenTail r := by
  rw [thetaCuspFirstAtomEvenTail]
  exact tsum_nonneg fun j => (thetaCuspFirstAtomEvenWeight_pos _).le

theorem thetaCuspFirstAtomEvenWeight_zero :
    thetaCuspFirstAtomEvenWeight 0 = thetaCuspAtomRawEvenMoment 0 1 := by
  rw [thetaCuspFirstAtomEvenWeight_eq_rawEvenMoment]
  norm_num

theorem thetaCuspFirstAtomEvenWeight_one :
    thetaCuspFirstAtomEvenWeight 1 = thetaCuspAtomRawEvenMoment 1 1 / 8 := by
  rw [thetaCuspFirstAtomEvenWeight_eq_rawEvenMoment]
  norm_num

theorem thetaCuspFirstAtomEvenWeight_two :
    thetaCuspFirstAtomEvenWeight 2 = thetaCuspAtomRawEvenMoment 2 1 / 384 := by
  rw [thetaCuspFirstAtomEvenWeight_eq_rawEvenMoment]
  norm_num

theorem thetaCuspFirstAtomTail_one_identity :
    thetaCuspAtomRawEvenMoment 0 1 + thetaCuspHigherHalfDensityBudget =
      1 / 2 - thetaCuspFirstAtomEvenTail 1 := by
  have h := thetaCuspFirstAtomEvenTail_split 1
  rw [thetaCuspFirstAtomEvenSeriesBudget_eq] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [thetaCuspHigherHalfDensityBudget,
    ← thetaCuspFirstAtomEvenWeight_zero]
  linarith

theorem thetaCuspFirstAtomTail_two_pair_identity :
    thetaCuspFirstAtomHalfDensityPairBudget + thetaCuspHigherHalfDensityBudget =
      1 / 2 - thetaCuspFirstAtomEvenTail 2 := by
  have h := thetaCuspFirstAtomEvenTail_split 2
  rw [thetaCuspFirstAtomEvenSeriesBudget_eq] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h
  rw [thetaCuspFirstAtomEvenWeight_zero,
    thetaCuspFirstAtomEvenWeight_one] at h
  change (thetaCuspAtomRawEvenMoment 0 1 +
      thetaCuspAtomRawEvenMoment 1 1 / 8) +
      (1 / 2 - (4 * Real.pi - 1) * Real.exp (-Real.pi)) = _
  linarith

theorem thetaCuspFirstAtomPair_eq_budget_sub_tail_two :
    thetaCuspFirstAtomHalfDensityPairBudget =
      (4 * Real.pi - 1) * Real.exp (-Real.pi) -
        thetaCuspFirstAtomEvenTail 2 := by
  have h := thetaCuspFirstAtomEvenTail_split 2
  rw [thetaCuspFirstAtomEvenSeriesBudget_eq] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h
  rw [thetaCuspFirstAtomEvenWeight_zero,
    thetaCuspFirstAtomEvenWeight_one] at h
  change thetaCuspAtomRawEvenMoment 0 1 +
      thetaCuspAtomRawEvenMoment 1 1 / 8 = _
  linarith

theorem thetaCuspFirstAtomEvenTail_one_lower :
    thetaCuspAtomRawEvenMoment 1 1 / 8 +
        thetaCuspAtomRawEvenMoment 2 1 / 384 ≤
      thetaCuspFirstAtomEvenTail 1 := by
  rw [thetaCuspFirstAtomEvenTail_recurrence 1,
    thetaCuspFirstAtomEvenTail_recurrence 2,
    thetaCuspFirstAtomEvenWeight_one,
    thetaCuspFirstAtomEvenWeight_two]
  nlinarith [thetaCuspFirstAtomEvenTail_nonneg 3]

theorem thetaCuspFirstAtomUpperGate_iff_positiveTail :
    (16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
        thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) ↔
    (8 * thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) +
        16 * thetaCuspAtomRawEvenMoment 2 1 *
          thetaCuspFirstAtomEvenTail 1) := by
  rw [thetaCuspFirstAtomTail_one_identity]
  constructor <;> intro h <;> nlinarith

theorem thetaCuspFirstAtomUpperGate_of_finite_reduction
    (hfinite :
      8 * thetaCuspAtomRawEvenMoment 2 1 ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) +
          2 * thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 2 1 +
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) / 24) :
    16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
        thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) := by
  rw [thetaCuspFirstAtomUpperGate_iff_positiveTail]
  have htail := thetaCuspFirstAtomEvenTail_one_lower
  have ha2 := thetaCuspAtomRawEvenMoment_nonneg 2 1
  have hmul := mul_le_mul_of_nonneg_left htail
    (mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) ha2)
  nlinarith

theorem thetaCuspFirstAtomLowerGate_tail_form_iff :
    (14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
        thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
      9 * thetaCuspFirstAtomHalfDensityPairBudget *
        thetaCuspAtomRawEvenMoment 1 1 * thetaCuspAtomRawEvenMoment 3 1) ↔
    (14 * (1 / 2 - thetaCuspFirstAtomEvenTail 2) *
        thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
      9 * ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
          thetaCuspFirstAtomEvenTail 2) *
        thetaCuspAtomRawEvenMoment 1 1 * thetaCuspAtomRawEvenMoment 3 1) := by
  constructor
  · intro h
    calc
      14 * (1 / 2 - thetaCuspFirstAtomEvenTail 2) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) =
        14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) := by
            rw [thetaCuspFirstAtomTail_two_pair_identity]
      _ ≤ 9 * thetaCuspFirstAtomHalfDensityPairBudget *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1 := h
      _ = 9 * ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
          thetaCuspFirstAtomEvenTail 2) *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1 := by
              rw [thetaCuspFirstAtomPair_eq_budget_sub_tail_two]
  · intro h
    calc
      14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) =
        14 * (1 / 2 - thetaCuspFirstAtomEvenTail 2) *
          thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) := by
            rw [thetaCuspFirstAtomTail_two_pair_identity]
      _ ≤ 9 * ((4 * Real.pi - 1) * Real.exp (-Real.pi) -
          thetaCuspFirstAtomEvenTail 2) *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1 := h
      _ = 9 * thetaCuspFirstAtomHalfDensityPairBudget *
          thetaCuspAtomRawEvenMoment 1 1 *
            thetaCuspAtomRawEvenMoment 3 1 := by
              rw [thetaCuspFirstAtomPair_eq_budget_sub_tail_two]

/-! ## Half-line slope curvature -/

def thetaCuspSlopeQuotient (x : ℝ) : ℝ :=
  thetaCuspFirstLogPotentialSlope x / x

def thetaCuspFullSlopeCurvature (x : ℝ) : ℝ :=
  thetaCuspFirstAtomBoundaryLogSlope / x ^ (2 : ℕ) +
    thetaCuspRegularSlopeCurvature x

theorem thetaCuspSlopeQuotient_eq_boundary_add_regular
    {x : ℝ} (hx : x ≠ 0) :
    thetaCuspSlopeQuotient x =
      -thetaCuspFirstAtomBoundaryLogSlope / x +
        thetaCuspRegularSlopeQuotient x := by
  unfold thetaCuspSlopeQuotient thetaCuspRegularSlopeQuotient
  rw [thetaCuspFirstLogPotentialSlope_zero]
  field_simp [hx]
  ring

theorem hasDerivAt_thetaCuspSlopeQuotient
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspSlopeQuotient
      (thetaCuspFullSlopeCurvature x) x := by
  have hslope := hasDerivAt_two_thetaCuspBornWittenSuperpotential
    (n := 1) (by norm_num) hx.le
  have hquot := hslope.div (hasDerivAt_id x) hx.ne'
  change HasDerivAt
    (fun y : ℝ => (2 * thetaCuspBornWittenSuperpotential 1 y) / y)
    (thetaCuspFullSlopeCurvature x) x
  exact hquot.congr_deriv (by
    have hzero := thetaCuspFirstLogPotentialSlope_zero
    change 2 * thetaCuspBornWittenSuperpotential 1 0 =
      -thetaCuspFirstAtomBoundaryLogSlope at hzero
    unfold thetaCuspFullSlopeCurvature thetaCuspRegularSlopeCurvature
      thetaCuspRegularCurvatureNumerator thetaCuspFirstLogPotentialSlope
    rw [hzero]
    simp only [id_eq]
    field_simp [hx.ne']
    ring)

theorem intervalIntegral_thetaCuspFullSlopeCurvature
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t) =
      thetaCuspSlopeQuotient v - thetaCuspSlopeQuotient u := by
  have hpos : ∀ t ∈ uIcc u v, 0 < t := by
    intro t ht
    have hmin : 0 < min u v := lt_min hu hv
    exact hmin.trans_le ht.1
  have hderiv : ∀ t ∈ uIcc u v,
      HasDerivAt thetaCuspSlopeQuotient
        (thetaCuspFullSlopeCurvature t) t := by
    intro t ht
    exact hasDerivAt_thetaCuspSlopeQuotient (hpos t ht)
  have hcont : ContinuousOn thetaCuspFullSlopeCurvature (uIcc u v) := by
    intro t ht
    have ht0 := (hpos t ht).ne'
    have hcurv : ContinuousAt (thetaCuspBornWittenLogCurvature 1) t :=
      (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hslope : ContinuousAt
        (fun x : ℝ => 2 * thetaCuspBornWittenSuperpotential 1 x) t :=
      (hasDerivAt_two_thetaCuspBornWittenSuperpotential
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hden : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ)) t := continuousAt_id.pow 2
    have hden0 : t ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 ht0
    unfold thetaCuspFullSlopeCurvature thetaCuspRegularSlopeCurvature
      thetaCuspRegularCurvatureNumerator thetaCuspFirstLogPotentialSlope
    exact ((continuousAt_const.div hden hden0).add
      (((continuousAt_id.mul hcurv).sub
        (hslope.sub continuousAt_const)).div hden hden0)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable

theorem thetaCuspFullSlopeCurvature_split (x : ℝ) :
    thetaCuspFullSlopeCurvature x =
      thetaCuspFirstAtomBoundaryLogSlope / x ^ (2 : ℕ) +
        thetaCuspRegularSlopeCurvature x := rfl

def thetaCuspTuranDefect (m : ℕ) : ℝ :=
  thetaCuspTotalMoment (2 * m) ^ (2 : ℕ) -
    ((2 * m - 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) *
      thetaCuspTotalMoment (2 * m - 2) *
        thetaCuspTotalMoment (2 * m + 2)

def thetaCuspSlopeCurvatureTuranIntegral (m : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    ∫ v : ℝ in Ioi 0,
      u ^ (2 * m) * v ^ (2 * m) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)

def thetaCuspTuranDefectIndex (k : ℕ) : ℝ :=
  thetaCuspTotalMoment (k + 1) ^ (2 : ℕ) -
    (k : ℝ) / (k + 2 : ℝ) * thetaCuspTotalMoment (k - 1) *
      thetaCuspTotalMoment (k + 3)

def thetaCuspSlopeCurvatureTuranIntegralIndex (k : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    ∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)

private theorem thetaCuspSlopeCurvatureTuran_inner
    {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    (∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) =
      u ^ (k + 1) * thetaCuspSourceTerm u 1 *
          ((k + 2 : ℕ) : ℝ) * thetaCuspTotalMoment (k + 1) -
        u ^ (k + 3) * thetaCuspSourceTerm u 1 *
          (k : ℝ) * thetaCuspTotalMoment (k - 1) -
        (u ^ k * thetaCuspFirstLogPotentialSlope u *
            thetaCuspSourceTerm u 1) * thetaCuspTotalMoment (k + 3) +
        (u ^ (k + 2) * thetaCuspFirstLogPotentialSlope u *
            thetaCuspSourceTerm u 1) * thetaCuspTotalMoment (k + 1) := by
  let A : ℝ := u ^ (k + 1) * thetaCuspSourceTerm u 1
  let B : ℝ := u ^ (k + 3) * thetaCuspSourceTerm u 1
  let C : ℝ := u ^ k * thetaCuspFirstLogPotentialSlope u *
    thetaCuspSourceTerm u 1
  let D : ℝ := u ^ (k + 2) * thetaCuspFirstLogPotentialSlope u *
    thetaCuspSourceTerm u 1
  let fA : ℝ → ℝ := fun v =>
    v ^ (k + 2) * thetaCuspFirstLogPotentialSlope v *
      thetaCuspSourceTerm v 1
  let fB : ℝ → ℝ := fun v =>
    v ^ k * thetaCuspFirstLogPotentialSlope v * thetaCuspSourceTerm v 1
  let fC : ℝ → ℝ := fun v => v ^ (k + 3) * thetaCuspSourceTerm v 1
  let fD : ℝ → ℝ := fun v => v ^ (k + 1) * thetaCuspSourceTerm v 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source (k + 2)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using
      integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using
      integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hvalA : (∫ v : ℝ in Ioi 0, fA v) =
      ((k + 2 : ℕ) : ℝ) * thetaCuspTotalMoment (k + 1) := by
    unfold fA
    rw [thetaCuspSourcePotentialSlope_moment_eq (show 1 ≤ k + 2 by omega)]
    rw [show k + 2 - 1 = k + 1 by omega]
  have hvalB : (∫ v : ℝ in Ioi 0, fB v) =
      (k : ℝ) * thetaCuspTotalMoment (k - 1) := by
    simpa only [fB] using thetaCuspSourcePotentialSlope_moment_eq hk
  have hvalC : (∫ v : ℝ in Ioi 0, fC v) =
      thetaCuspTotalMoment (k + 3) := by
    simpa only [fC] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 3)).symm
  have hvalD : (∫ v : ℝ in Ioi 0, fD v) =
      thetaCuspTotalMoment (k + 1) := by
    simpa only [fD] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 1)).symm
  have hpoint : ∀ᵐ v ∂volume.restrict (Ioi 0),
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t) =
        ((A * fA v - B * fB v) - C * fC v) + D * fD v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [intervalIntegral_thetaCuspFullSlopeCurvature hu hv]
    unfold thetaCuspSlopeQuotient A B C D fA fB fC fD
    simp only [pow_succ]
    field_simp [hu.ne', hv.ne']
    ring
  have hAint : IntegrableOn (fun v => A * fA v) (Ioi 0) := hfA.const_mul A
  have hBint : IntegrableOn (fun v => B * fB v) (Ioi 0) := hfB.const_mul B
  have hCint : IntegrableOn (fun v => C * fC v) (Ioi 0) := hfC.const_mul C
  have hDint : IntegrableOn (fun v => D * fD v) (Ioi 0) := hfD.const_mul D
  have hABint : IntegrableOn (fun v => A * fA v - B * fB v) (Ioi 0) :=
    hAint.sub hBint
  have hABCint : IntegrableOn
      (fun v => (A * fA v - B * fB v) - C * fC v) (Ioi 0) :=
    hABint.sub hCint
  have hlin :
      (∫ v : ℝ in Ioi 0, ((A * fA v - B * fB v) - C * fC v) + D * fD v) =
        (A * (∫ v : ℝ in Ioi 0, fA v) -
          B * (∫ v : ℝ in Ioi 0, fB v)) -
          C * (∫ v : ℝ in Ioi 0, fC v) +
          D * (∫ v : ℝ in Ioi 0, fD v) := by
    calc
      _ = (∫ v : ℝ in Ioi 0, (A * fA v - B * fB v) - C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            exact MeasureTheory.integral_add hABCint hDint
      _ = ((∫ v : ℝ in Ioi 0, A * fA v - B * fB v) -
          ∫ v : ℝ in Ioi 0, C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            rw [MeasureTheory.integral_sub hABint hCint]
      _ = (((∫ v : ℝ in Ioi 0, A * fA v) -
          ∫ v : ℝ in Ioi 0, B * fB v) -
          ∫ v : ℝ in Ioi 0, C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            rw [MeasureTheory.integral_sub hAint hBint]
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc
    (∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) =
      ∫ v : ℝ in Ioi 0,
        ((A * fA v - B * fB v) - C * fC v) + D * fD v :=
          integral_congr_ae hpoint
    _ = (A * (∫ v : ℝ in Ioi 0, fA v) -
          B * (∫ v : ℝ in Ioi 0, fB v)) -
          C * (∫ v : ℝ in Ioi 0, fC v) +
          D * (∫ v : ℝ in Ioi 0, fD v) := hlin
    _ = _ := by
      simp only [hvalA, hvalB, hvalC, hvalD]
      unfold A B C D
      ring

theorem thetaCuspSlopeCurvatureTuranIntegralIndex_eq
    {k : ℕ} (hk : 1 ≤ k) :
    thetaCuspSlopeCurvatureTuranIntegralIndex k =
      2 * ((k + 2 : ℕ) : ℝ) * thetaCuspTuranDefectIndex k := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ) * thetaCuspTotalMoment (k + 1)
  let B : ℝ := (k : ℝ) * thetaCuspTotalMoment (k - 1)
  let C : ℝ := thetaCuspTotalMoment (k + 3)
  let D : ℝ := thetaCuspTotalMoment (k + 1)
  let fA : ℝ → ℝ := fun u => u ^ (k + 1) * thetaCuspSourceTerm u 1
  let fB : ℝ → ℝ := fun u => u ^ (k + 3) * thetaCuspSourceTerm u 1
  let fC : ℝ → ℝ := fun u =>
    u ^ k * thetaCuspFirstLogPotentialSlope u * thetaCuspSourceTerm u 1
  let fD : ℝ → ℝ := fun u =>
    u ^ (k + 2) * thetaCuspFirstLogPotentialSlope u * thetaCuspSourceTerm u 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using
      integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using
      integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source (k + 2)
  have hvalA : (∫ u : ℝ in Ioi 0, fA u) = thetaCuspTotalMoment (k + 1) := by
    simpa only [fA] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 1)).symm
  have hvalB : (∫ u : ℝ in Ioi 0, fB u) = thetaCuspTotalMoment (k + 3) := by
    simpa only [fB] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 3)).symm
  have hvalC : (∫ u : ℝ in Ioi 0, fC u) =
      (k : ℝ) * thetaCuspTotalMoment (k - 1) := by
    simpa only [fC] using thetaCuspSourcePotentialSlope_moment_eq hk
  have hvalD : (∫ u : ℝ in Ioi 0, fD u) =
      ((k + 2 : ℕ) : ℝ) * thetaCuspTotalMoment (k + 1) := by
    unfold fD
    rw [thetaCuspSourcePotentialSlope_moment_eq (show 1 ≤ k + 2 by omega)]
    rw [show k + 2 - 1 = k + 1 by omega]
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi 0),
      (∫ v : ℝ in Ioi 0,
        u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) =
        ((fA u * A - fB u * B) - fC u * C) + fD u * D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    rw [thetaCuspSlopeCurvatureTuran_inner hk hu]
    unfold A B C D fA fB fC fD
    ring
  have hAint : IntegrableOn (fun u => fA u * A) (Ioi 0) := hfA.mul_const A
  have hBint : IntegrableOn (fun u => fB u * B) (Ioi 0) := hfB.mul_const B
  have hCint : IntegrableOn (fun u => fC u * C) (Ioi 0) := hfC.mul_const C
  have hDint : IntegrableOn (fun u => fD u * D) (Ioi 0) := hfD.mul_const D
  have hABint : IntegrableOn (fun u => fA u * A - fB u * B) (Ioi 0) :=
    hAint.sub hBint
  have hABCint : IntegrableOn
      (fun u => (fA u * A - fB u * B) - fC u * C) (Ioi 0) :=
    hABint.sub hCint
  have hlin :
      (∫ u : ℝ in Ioi 0, ((fA u * A - fB u * B) - fC u * C) + fD u * D) =
        ((∫ u : ℝ in Ioi 0, fA u) * A -
          (∫ u : ℝ in Ioi 0, fB u) * B) -
          (∫ u : ℝ in Ioi 0, fC u) * C +
          (∫ u : ℝ in Ioi 0, fD u) * D := by
    calc
      _ = (∫ u : ℝ in Ioi 0, (fA u * A - fB u * B) - fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            exact MeasureTheory.integral_add hABCint hDint
      _ = ((∫ u : ℝ in Ioi 0, fA u * A - fB u * B) -
          ∫ u : ℝ in Ioi 0, fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            rw [MeasureTheory.integral_sub hABint hCint]
      _ = (((∫ u : ℝ in Ioi 0, fA u * A) -
          ∫ u : ℝ in Ioi 0, fB u * B) -
          ∫ u : ℝ in Ioi 0, fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            rw [MeasureTheory.integral_sub hAint hBint]
      _ = _ := by
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const,
          MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
  rw [thetaCuspSlopeCurvatureTuranIntegralIndex]
  calc
    (∫ u : ℝ in Ioi 0,
      ∫ v : ℝ in Ioi 0,
        u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) =
      ∫ u : ℝ in Ioi 0,
        ((fA u * A - fB u * B) - fC u * C) + fD u * D :=
          integral_congr_ae hpoint
    _ = ((∫ u : ℝ in Ioi 0, fA u) * A -
          (∫ u : ℝ in Ioi 0, fB u) * B) -
          (∫ u : ℝ in Ioi 0, fC u) * C +
          (∫ u : ℝ in Ioi 0, fD u) * D := hlin
    _ = 2 * ((k + 2 : ℕ) : ℝ) * thetaCuspTuranDefectIndex k := by
      simp only [hvalA, hvalB, hvalC, hvalD]
      unfold A B C D thetaCuspTuranDefectIndex
      have hk2 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      field_simp [hk2]
      ring

theorem thetaCuspSlopeCurvatureTuranIntegral_eq
    {m : ℕ} (hm : 1 ≤ m) :
    thetaCuspSlopeCurvatureTuranIntegral m =
      2 * ((2 * m + 1 : ℕ) : ℝ) * thetaCuspTuranDefect m := by
  let k : ℕ := 2 * m - 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkm : k + 1 = 2 * m := by dsimp [k]; omega
  have hindex := thetaCuspSlopeCurvatureTuranIntegralIndex_eq hk
  have hint : thetaCuspSlopeCurvatureTuranIntegral m =
      thetaCuspSlopeCurvatureTuranIntegralIndex k := by
    unfold thetaCuspSlopeCurvatureTuranIntegral
      thetaCuspSlopeCurvatureTuranIntegralIndex
    rw [hkm]
  have hdef : thetaCuspTuranDefectIndex k = thetaCuspTuranDefect m := by
    unfold thetaCuspTuranDefectIndex thetaCuspTuranDefect
    rw [hkm]
    have hk2 : k + 2 = 2 * m + 1 := by omega
    have hkm1 : k - 1 = 2 * m - 2 := by dsimp [k]; omega
    have hkm3 : k + 3 = 2 * m + 2 := by omega
    rw [hkm1, hkm3]
    rw [show k = 2 * m - 1 by rfl]
    norm_num only [Nat.cast_sub (show 1 ≤ 2 * m by omega), Nat.cast_one,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hint, hindex, hdef]
  congr 2
  exact_mod_cast (show k + 2 = 2 * m + 1 by omega)

def thetaCuspBoundaryPoleCurvature (x : ℝ) : ℝ :=
  thetaCuspFirstAtomBoundaryLogSlope / x ^ (2 : ℕ)

def thetaCuspBoundaryPoleTuranIntegralIndex (k : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    ∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)

theorem intervalIntegral_thetaCuspBoundaryPoleCurvature
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t) =
      thetaCuspFirstAtomBoundaryLogSlope * (1 / u - 1 / v) := by
  let F : ℝ → ℝ := fun x => -thetaCuspFirstAtomBoundaryLogSlope / x
  have hpos : ∀ t ∈ uIcc u v, 0 < t := by
    intro t ht
    exact (lt_min hu hv).trans_le ht.1
  have hderiv : ∀ t ∈ uIcc u v,
      HasDerivAt F (thetaCuspBoundaryPoleCurvature t) t := by
    intro t ht
    have ht0 := (hpos t ht).ne'
    have h := (hasDerivAt_const t (-thetaCuspFirstAtomBoundaryLogSlope)).div
      (hasDerivAt_id t) ht0
    exact h.congr_deriv (by
      unfold thetaCuspBoundaryPoleCurvature
      simp only [id_eq, zero_mul]
      field_simp [ht0]
      ring)
  have hcont : ContinuousOn thetaCuspBoundaryPoleCurvature (uIcc u v) := by
    intro t ht
    unfold thetaCuspBoundaryPoleCurvature
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (hpos t ht).ne')).continuousWithinAt
  calc
    (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t) = F v - F u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    _ = _ := by
      unfold F
      field_simp [hu.ne', hv.ne']
      ring

private theorem thetaCuspBoundaryPoleTuran_inner
    (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) =
      thetaCuspFirstAtomBoundaryLogSlope *
        (u ^ k * thetaCuspSourceTerm u 1 * thetaCuspTotalMoment (k + 3) -
          u ^ (k + 1) * thetaCuspSourceTerm u 1 * thetaCuspTotalMoment (k + 2) -
          u ^ (k + 2) * thetaCuspSourceTerm u 1 * thetaCuspTotalMoment (k + 1) +
          u ^ (k + 3) * thetaCuspSourceTerm u 1 * thetaCuspTotalMoment k) := by
  let s : ℝ := thetaCuspFirstAtomBoundaryLogSlope
  let A : ℝ := s * u ^ k * thetaCuspSourceTerm u 1
  let B : ℝ := s * u ^ (k + 1) * thetaCuspSourceTerm u 1
  let C : ℝ := s * u ^ (k + 2) * thetaCuspSourceTerm u 1
  let D : ℝ := s * u ^ (k + 3) * thetaCuspSourceTerm u 1
  let fA : ℝ → ℝ := fun v => v ^ (k + 3) * thetaCuspSourceTerm v 1
  let fB : ℝ → ℝ := fun v => v ^ (k + 2) * thetaCuspSourceTerm v 1
  let fC : ℝ → ℝ := fun v => v ^ (k + 1) * thetaCuspSourceTerm v 1
  let fD : ℝ → ℝ := fun v => v ^ k * thetaCuspSourceTerm v 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 2)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hvalA : (∫ v : ℝ in Ioi 0, fA v) = thetaCuspTotalMoment (k + 3) := by
    simpa only [fA] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 3)).symm
  have hvalB : (∫ v : ℝ in Ioi 0, fB v) = thetaCuspTotalMoment (k + 2) := by
    simpa only [fB] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 2)).symm
  have hvalC : (∫ v : ℝ in Ioi 0, fC v) = thetaCuspTotalMoment (k + 1) := by
    simpa only [fC] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 1)).symm
  have hvalD : (∫ v : ℝ in Ioi 0, fD v) = thetaCuspTotalMoment k := by
    simpa only [fD] using (thetaCuspTotalMoment_eq_integral_Ioi k).symm
  have hpoint : ∀ᵐ v ∂volume.restrict (Ioi 0),
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t) =
        ((A * fA v - B * fB v) - C * fC v) + D * fD v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [intervalIntegral_thetaCuspBoundaryPoleCurvature hu hv]
    unfold A B C D fA fB fC fD s
    simp only [pow_succ]
    field_simp [hu.ne', hv.ne']
    ring
  have hAint : IntegrableOn (fun v => A * fA v) (Ioi 0) := hfA.const_mul A
  have hBint : IntegrableOn (fun v => B * fB v) (Ioi 0) := hfB.const_mul B
  have hCint : IntegrableOn (fun v => C * fC v) (Ioi 0) := hfC.const_mul C
  have hDint : IntegrableOn (fun v => D * fD v) (Ioi 0) := hfD.const_mul D
  have hABint : IntegrableOn (fun v => A * fA v - B * fB v) (Ioi 0) :=
    hAint.sub hBint
  have hABCint : IntegrableOn
      (fun v => (A * fA v - B * fB v) - C * fC v) (Ioi 0) :=
    hABint.sub hCint
  have hlin :
      (∫ v : ℝ in Ioi 0, ((A * fA v - B * fB v) - C * fC v) + D * fD v) =
        ((A * (∫ v : ℝ in Ioi 0, fA v) -
          B * (∫ v : ℝ in Ioi 0, fB v)) -
          C * (∫ v : ℝ in Ioi 0, fC v)) +
          D * (∫ v : ℝ in Ioi 0, fD v) := by
    calc
      _ = (∫ v : ℝ in Ioi 0, (A * fA v - B * fB v) - C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            exact MeasureTheory.integral_add hABCint hDint
      _ = ((∫ v : ℝ in Ioi 0, A * fA v - B * fB v) -
          ∫ v : ℝ in Ioi 0, C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            rw [MeasureTheory.integral_sub hABint hCint]
      _ = (((∫ v : ℝ in Ioi 0, A * fA v) -
          ∫ v : ℝ in Ioi 0, B * fB v) -
          ∫ v : ℝ in Ioi 0, C * fC v) +
          ∫ v : ℝ in Ioi 0, D * fD v := by
            rw [MeasureTheory.integral_sub hAint hBint]
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc
    (∫ v : ℝ in Ioi 0,
      u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) =
      ∫ v : ℝ in Ioi 0,
        ((A * fA v - B * fB v) - C * fC v) + D * fD v :=
          integral_congr_ae hpoint
    _ = ((A * (∫ v : ℝ in Ioi 0, fA v) -
          B * (∫ v : ℝ in Ioi 0, fB v)) -
          C * (∫ v : ℝ in Ioi 0, fC v)) +
          D * (∫ v : ℝ in Ioi 0, fD v) := hlin
    _ = _ := by
      simp only [hvalA, hvalB, hvalC, hvalD]
      unfold A B C D s
      ring

theorem thetaCuspBoundaryPoleTuranIntegralIndex_eq (k : ℕ) :
    thetaCuspBoundaryPoleTuranIntegralIndex k =
      2 * thetaCuspFirstAtomBoundaryLogSlope *
        (thetaCuspTotalMoment k * thetaCuspTotalMoment (k + 3) -
          thetaCuspTotalMoment (k + 1) * thetaCuspTotalMoment (k + 2)) := by
  let A : ℝ := thetaCuspTotalMoment (k + 3)
  let B : ℝ := thetaCuspTotalMoment (k + 2)
  let C : ℝ := thetaCuspTotalMoment (k + 1)
  let D : ℝ := thetaCuspTotalMoment k
  let s : ℝ := thetaCuspFirstAtomBoundaryLogSlope
  let fA : ℝ → ℝ := fun u => u ^ k * thetaCuspSourceTerm u 1
  let fB : ℝ → ℝ := fun u => u ^ (k + 1) * thetaCuspSourceTerm u 1
  let fC : ℝ → ℝ := fun u => u ^ (k + 2) * thetaCuspSourceTerm u 1
  let fD : ℝ → ℝ := fun u => u ^ (k + 3) * thetaCuspSourceTerm u 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 2)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hvalA : (∫ u : ℝ in Ioi 0, fA u) = thetaCuspTotalMoment k := by
    simpa only [fA] using (thetaCuspTotalMoment_eq_integral_Ioi k).symm
  have hvalB : (∫ u : ℝ in Ioi 0, fB u) = thetaCuspTotalMoment (k + 1) := by
    simpa only [fB] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 1)).symm
  have hvalC : (∫ u : ℝ in Ioi 0, fC u) = thetaCuspTotalMoment (k + 2) := by
    simpa only [fC] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 2)).symm
  have hvalD : (∫ u : ℝ in Ioi 0, fD u) = thetaCuspTotalMoment (k + 3) := by
    simpa only [fD] using (thetaCuspTotalMoment_eq_integral_Ioi (k + 3)).symm
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi 0),
      (∫ v : ℝ in Ioi 0,
        u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) =
        s * (((fA u * A - fB u * B) - fC u * C) + fD u * D) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    rw [thetaCuspBoundaryPoleTuran_inner k hu]
  have hAint : IntegrableOn (fun u => fA u * A) (Ioi 0) := hfA.mul_const A
  have hBint : IntegrableOn (fun u => fB u * B) (Ioi 0) := hfB.mul_const B
  have hCint : IntegrableOn (fun u => fC u * C) (Ioi 0) := hfC.mul_const C
  have hDint : IntegrableOn (fun u => fD u * D) (Ioi 0) := hfD.mul_const D
  have hABint : IntegrableOn (fun u => fA u * A - fB u * B) (Ioi 0) :=
    hAint.sub hBint
  have hABCint : IntegrableOn
      (fun u => (fA u * A - fB u * B) - fC u * C) (Ioi 0) :=
    hABint.sub hCint
  have hlin :
      (∫ u : ℝ in Ioi 0, ((fA u * A - fB u * B) - fC u * C) + fD u * D) =
        (((∫ u : ℝ in Ioi 0, fA u) * A -
          (∫ u : ℝ in Ioi 0, fB u) * B) -
          (∫ u : ℝ in Ioi 0, fC u) * C) +
          (∫ u : ℝ in Ioi 0, fD u) * D := by
    calc
      _ = (∫ u : ℝ in Ioi 0, (fA u * A - fB u * B) - fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            exact MeasureTheory.integral_add hABCint hDint
      _ = ((∫ u : ℝ in Ioi 0, fA u * A - fB u * B) -
          ∫ u : ℝ in Ioi 0, fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            rw [MeasureTheory.integral_sub hABint hCint]
      _ = (((∫ u : ℝ in Ioi 0, fA u * A) -
          ∫ u : ℝ in Ioi 0, fB u * B) -
          ∫ u : ℝ in Ioi 0, fC u * C) +
          ∫ u : ℝ in Ioi 0, fD u * D := by
            rw [MeasureTheory.integral_sub hAint hBint]
      _ = _ := by
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const,
          MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
  rw [thetaCuspBoundaryPoleTuranIntegralIndex]
  calc
    (∫ u : ℝ in Ioi 0,
      ∫ v : ℝ in Ioi 0,
        u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
            (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) =
      ∫ u : ℝ in Ioi 0,
        s * (((fA u * A - fB u * B) - fC u * C) + fD u * D) :=
          integral_congr_ae hpoint
    _ = s * ∫ u : ℝ in Ioi 0,
        ((fA u * A - fB u * B) - fC u * C) + fD u * D := by
          rw [MeasureTheory.integral_const_mul]
    _ = s * ((((∫ u : ℝ in Ioi 0, fA u) * A -
          (∫ u : ℝ in Ioi 0, fB u) * B) -
          (∫ u : ℝ in Ioi 0, fC u) * C) +
          (∫ u : ℝ in Ioi 0, fD u) * D) := congrArg (fun z : ℝ => s * z) hlin
    _ = _ := by
      simp only [hvalA, hvalB, hvalC, hvalD]
      unfold A B C D s
      ring

theorem thetaCuspBoundaryPoleKernel_nonneg
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ (v ^ (2 : ℕ) - u ^ (2 : ℕ)) * (1 / u - 1 / v) := by
  have hrewrite :
      (v ^ (2 : ℕ) - u ^ (2 : ℕ)) * (1 / u - 1 / v) =
        (v - u) ^ (2 : ℕ) * (v + u) / (u * v) := by
    field_simp [hu.ne', hv.ne']
    ring
  rw [hrewrite]
  positivity

theorem thetaCuspBoundaryPoleTuranIntegrand_nonneg
    (k : ℕ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
      thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
        (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t) := by
  rw [intervalIntegral_thetaCuspBoundaryPoleCurvature hu hv]
  have hkernel := thetaCuspBoundaryPoleKernel_nonneg hu hv
  have hsu := thetaCuspSourceTerm_nonneg_of_pos hu 1
  have hsv := thetaCuspSourceTerm_nonneg_of_pos hv 1
  have hs := thetaCuspFirstAtomBoundaryLogSlope_pos.le
  calc
    u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1 *
          (thetaCuspFirstAtomBoundaryLogSlope * (1 / u - 1 / v)) =
      (u ^ (k + 1) * v ^ (k + 1) * thetaCuspSourceTerm u 1 *
          thetaCuspSourceTerm v 1 * thetaCuspFirstAtomBoundaryLogSlope) *
        ((v ^ (2 : ℕ) - u ^ (2 : ℕ)) * (1 / u - 1 / v)) := by ring
    _ ≥ 0 := mul_nonneg (by positivity) hkernel

theorem thetaCuspBoundaryPoleTuranIntegralIndex_nonneg (k : ℕ) :
    0 ≤ thetaCuspBoundaryPoleTuranIntegralIndex k := by
  unfold thetaCuspBoundaryPoleTuranIntegralIndex
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro u hu
  change 0 < u at hu
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro v hv
  change 0 < v at hv
  exact thetaCuspBoundaryPoleTuranIntegrand_nonneg k hu hv

theorem thetaCuspTotalMoment_cross_nonneg (k : ℕ) :
    0 ≤ thetaCuspTotalMoment k * thetaCuspTotalMoment (k + 3) -
      thetaCuspTotalMoment (k + 1) * thetaCuspTotalMoment (k + 2) := by
  have hI := thetaCuspBoundaryPoleTuranIntegralIndex_nonneg k
  rw [thetaCuspBoundaryPoleTuranIntegralIndex_eq] at hI
  nlinarith [thetaCuspFirstAtomBoundaryLogSlope_pos]

def thetaCuspTuranKernelIndex (k : ℕ) (u v : ℝ) : ℝ :=
  u ^ (k + 1) * v ^ (k + 1) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
    thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1

def thetaCuspRegularSlopeCurvatureTuranIntegralIndex (k : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    ∫ v : ℝ in Ioi 0,
      thetaCuspTuranKernelIndex k u v *
        (∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t)

theorem intervalIntegral_thetaCuspRegularSlopeCurvature
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t) =
      thetaCuspRegularSlopeQuotient v - thetaCuspRegularSlopeQuotient u := by
  have hpos : ∀ t ∈ uIcc u v, 0 < t := by
    intro t ht
    exact (lt_min hu hv).trans_le ht.1
  have hderiv : ∀ t ∈ uIcc u v,
      HasDerivAt thetaCuspRegularSlopeQuotient
        (thetaCuspRegularSlopeCurvature t) t := by
    intro t ht
    exact hasDerivAt_thetaCuspRegularSlopeQuotient (hpos t ht)
  have hcont : ContinuousOn thetaCuspRegularSlopeCurvature (uIcc u v) := by
    intro t ht
    have ht0 := (hpos t ht).ne'
    have hcurv : ContinuousAt (thetaCuspBornWittenLogCurvature 1) t :=
      (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hslope : ContinuousAt thetaCuspFirstLogPotentialSlope t :=
      (hasDerivAt_two_thetaCuspBornWittenSuperpotential
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hden : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ)) t := continuousAt_id.pow 2
    unfold thetaCuspRegularSlopeCurvature thetaCuspRegularCurvatureNumerator
    exact (((continuousAt_id.mul hcurv).sub
      (hslope.sub continuousAt_const)).div hden
        (pow_ne_zero 2 ht0)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable

theorem intervalIntegral_thetaCuspRegularSlopeCurvature_eq_full_sub_pole
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t) =
      (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t) -
        (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t) := by
  rw [intervalIntegral_thetaCuspRegularSlopeCurvature hu hv,
    intervalIntegral_thetaCuspFullSlopeCurvature hu hv,
    intervalIntegral_thetaCuspBoundaryPoleCurvature hu hv,
    thetaCuspSlopeQuotient_eq_boundary_add_regular hv.ne',
    thetaCuspSlopeQuotient_eq_boundary_add_regular hu.ne']
  ring

private theorem integrableOn_thetaCuspFullTuranInner
    (k : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun v : ℝ =>
      thetaCuspTuranKernelIndex k u v *
        (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) (Ioi 0) := by
  let A : ℝ := u ^ (k + 1) * thetaCuspSourceTerm u 1
  let B : ℝ := u ^ (k + 3) * thetaCuspSourceTerm u 1
  let C : ℝ := u ^ k * thetaCuspFirstLogPotentialSlope u *
    thetaCuspSourceTerm u 1
  let D : ℝ := u ^ (k + 2) * thetaCuspFirstLogPotentialSlope u *
    thetaCuspSourceTerm u 1
  let fA : ℝ → ℝ := fun v =>
    v ^ (k + 2) * thetaCuspFirstLogPotentialSlope v * thetaCuspSourceTerm v 1
  let fB : ℝ → ℝ := fun v =>
    v ^ k * thetaCuspFirstLogPotentialSlope v * thetaCuspSourceTerm v 1
  let fC : ℝ → ℝ := fun v => v ^ (k + 3) * thetaCuspSourceTerm v 1
  let fD : ℝ → ℝ := fun v => v ^ (k + 1) * thetaCuspSourceTerm v 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source (k + 2)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hAint : IntegrableOn (fun v => A * fA v) (Ioi 0) := hfA.const_mul A
  have hBint : IntegrableOn (fun v => B * fB v) (Ioi 0) := hfB.const_mul B
  have hCint : IntegrableOn (fun v => C * fC v) (Ioi 0) := hfC.const_mul C
  have hDint : IntegrableOn (fun v => D * fD v) (Ioi 0) := hfD.const_mul D
  have hsum : IntegrableOn
      (fun v => ((A * fA v - B * fB v) - C * fC v) + D * fD v) (Ioi 0) :=
    ((hAint.sub hBint).sub hCint).add hDint
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change 0 < v at hv
  rw [intervalIntegral_thetaCuspFullSlopeCurvature hu hv]
  unfold thetaCuspTuranKernelIndex thetaCuspSlopeQuotient A B C D fA fB fC fD
  simp only [pow_succ]
  field_simp [hu.ne', hv.ne']
  ring

private theorem integrableOn_thetaCuspBoundaryPoleTuranInner
    (k : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun v : ℝ =>
      thetaCuspTuranKernelIndex k u v *
        (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) (Ioi 0) := by
  let s : ℝ := thetaCuspFirstAtomBoundaryLogSlope
  let A : ℝ := s * u ^ k * thetaCuspSourceTerm u 1
  let B : ℝ := s * u ^ (k + 1) * thetaCuspSourceTerm u 1
  let C : ℝ := s * u ^ (k + 2) * thetaCuspSourceTerm u 1
  let D : ℝ := s * u ^ (k + 3) * thetaCuspSourceTerm u 1
  let fA : ℝ → ℝ := fun v => v ^ (k + 3) * thetaCuspSourceTerm v 1
  let fB : ℝ → ℝ := fun v => v ^ (k + 2) * thetaCuspSourceTerm v 1
  let fC : ℝ → ℝ := fun v => v ^ (k + 1) * thetaCuspSourceTerm v 1
  let fD : ℝ → ℝ := fun v => v ^ k * thetaCuspSourceTerm v 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 2)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hAint : IntegrableOn (fun v => A * fA v) (Ioi 0) := hfA.const_mul A
  have hBint : IntegrableOn (fun v => B * fB v) (Ioi 0) := hfB.const_mul B
  have hCint : IntegrableOn (fun v => C * fC v) (Ioi 0) := hfC.const_mul C
  have hDint : IntegrableOn (fun v => D * fD v) (Ioi 0) := hfD.const_mul D
  have hsum : IntegrableOn
      (fun v => ((A * fA v - B * fB v) - C * fC v) + D * fD v) (Ioi 0) :=
    ((hAint.sub hBint).sub hCint).add hDint
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change 0 < v at hv
  rw [intervalIntegral_thetaCuspBoundaryPoleCurvature hu hv]
  unfold thetaCuspTuranKernelIndex A B C D fA fB fC fD s
  simp only [pow_succ]
  field_simp [hu.ne', hv.ne']
  ring

private theorem integrableOn_thetaCuspFullTuranOuter
    {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun u : ℝ =>
      ∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) (Ioi 0) := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ) * thetaCuspTotalMoment (k + 1)
  let B : ℝ := (k : ℝ) * thetaCuspTotalMoment (k - 1)
  let C : ℝ := thetaCuspTotalMoment (k + 3)
  let D : ℝ := thetaCuspTotalMoment (k + 1)
  let fA : ℝ → ℝ := fun u => u ^ (k + 1) * thetaCuspSourceTerm u 1
  let fB : ℝ → ℝ := fun u => u ^ (k + 3) * thetaCuspSourceTerm u 1
  let fC : ℝ → ℝ := fun u =>
    u ^ k * thetaCuspFirstLogPotentialSlope u * thetaCuspSourceTerm u 1
  let fD : ℝ → ℝ := fun u =>
    u ^ (k + 2) * thetaCuspFirstLogPotentialSlope u * thetaCuspSourceTerm u 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source k
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using
      integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source (k + 2)
  have hAint : IntegrableOn (fun u => fA u * A) (Ioi 0) := hfA.mul_const A
  have hBint : IntegrableOn (fun u => fB u * B) (Ioi 0) := hfB.mul_const B
  have hCint : IntegrableOn (fun u => fC u * C) (Ioi 0) := hfC.mul_const C
  have hDint : IntegrableOn (fun u => fD u * D) (Ioi 0) := hfD.mul_const D
  have hsum : IntegrableOn
      (fun u => ((fA u * A - fB u * B) - fC u * C) + fD u * D) (Ioi 0) :=
    ((hAint.sub hBint).sub hCint).add hDint
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change 0 < u at hu
  unfold thetaCuspTuranKernelIndex
  rw [thetaCuspSlopeCurvatureTuran_inner hk hu]
  unfold A B C D fA fB fC fD
  ring

private theorem integrableOn_thetaCuspBoundaryPoleTuranOuter (k : ℕ) :
    IntegrableOn (fun u : ℝ =>
      ∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) (Ioi 0) := by
  let A : ℝ := thetaCuspTotalMoment (k + 3)
  let B : ℝ := thetaCuspTotalMoment (k + 2)
  let C : ℝ := thetaCuspTotalMoment (k + 1)
  let D : ℝ := thetaCuspTotalMoment k
  let s : ℝ := thetaCuspFirstAtomBoundaryLogSlope
  let fA : ℝ → ℝ := fun u => u ^ k * thetaCuspSourceTerm u 1
  let fB : ℝ → ℝ := fun u => u ^ (k + 1) * thetaCuspSourceTerm u 1
  let fC : ℝ → ℝ := fun u => u ^ (k + 2) * thetaCuspSourceTerm u 1
  let fD : ℝ → ℝ := fun u => u ^ (k + 3) * thetaCuspSourceTerm u 1
  have hfA : IntegrableOn fA (Ioi 0) := by
    simpa only [fA] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hfB : IntegrableOn fB (Ioi 0) := by
    simpa only [fB] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 1)
  have hfC : IntegrableOn fC (Ioi 0) := by
    simpa only [fC] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 2)
  have hfD : IntegrableOn fD (Ioi 0) := by
    simpa only [fD] using integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k + 3)
  have hAint : IntegrableOn (fun u => fA u * A) (Ioi 0) := hfA.mul_const A
  have hBint : IntegrableOn (fun u => fB u * B) (Ioi 0) := hfB.mul_const B
  have hCint : IntegrableOn (fun u => fC u * C) (Ioi 0) := hfC.mul_const C
  have hDint : IntegrableOn (fun u => fD u * D) (Ioi 0) := hfD.mul_const D
  have hsum0 : IntegrableOn
      (fun u => ((fA u * A - fB u * B) - fC u * C) + fD u * D) (Ioi 0) :=
    ((hAint.sub hBint).sub hCint).add hDint
  have hsum : IntegrableOn
      (fun u => s * (((fA u * A - fB u * B) - fC u * C) + fD u * D))
        (Ioi 0) := hsum0.const_mul s
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change 0 < u at hu
  unfold thetaCuspTuranKernelIndex
  rw [thetaCuspBoundaryPoleTuran_inner k hu]

theorem thetaCuspRegularTuranIntegralIndex_eq_full_sub_pole
    {k : ℕ} (hk : 1 ≤ k) :
    thetaCuspRegularSlopeCurvatureTuranIntegralIndex k =
      thetaCuspSlopeCurvatureTuranIntegralIndex k -
        thetaCuspBoundaryPoleTuranIntegralIndex k := by
  have hinner : ∀ u : ℝ, 0 < u →
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t)) =
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) -
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) := by
    intro u hu
    have hfull := integrableOn_thetaCuspFullTuranInner k hu
    have hpole := integrableOn_thetaCuspBoundaryPoleTuranInner k hu
    rw [← MeasureTheory.integral_sub hfull hpole]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [intervalIntegral_thetaCuspRegularSlopeCurvature_eq_full_sub_pole hu hv]
    ring
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi 0),
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t)) =
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspFullSlopeCurvature t)) -
      (∫ v : ℝ in Ioi 0,
        thetaCuspTuranKernelIndex k u v *
          (∫ t : ℝ in u..v, thetaCuspBoundaryPoleCurvature t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hinner u hu
  have hfull := integrableOn_thetaCuspFullTuranOuter hk
  have hpole := integrableOn_thetaCuspBoundaryPoleTuranOuter k
  unfold thetaCuspRegularSlopeCurvatureTuranIntegralIndex
  rw [integral_congr_ae hpoint, MeasureTheory.integral_sub hfull hpole]
  unfold thetaCuspSlopeCurvatureTuranIntegralIndex
    thetaCuspBoundaryPoleTuranIntegralIndex thetaCuspTuranKernelIndex
  rfl

def thetaCuspBoundaryPoleContribution (m : ℕ) : ℝ :=
  thetaCuspFirstAtomBoundaryLogSlope / ((2 * m + 1 : ℕ) : ℝ) *
    (thetaCuspTotalMoment (2 * m - 1) * thetaCuspTotalMoment (2 * m + 2) -
      thetaCuspTotalMoment (2 * m) * thetaCuspTotalMoment (2 * m + 1))

def thetaCuspRegularCurvatureContribution (m : ℕ) : ℝ :=
  thetaCuspRegularSlopeCurvatureTuranIntegralIndex (2 * m - 1) /
    (2 * ((2 * m + 1 : ℕ) : ℝ))

theorem thetaCuspBoundaryPoleContribution_succ_nonneg (m : ℕ) :
    0 ≤ thetaCuspBoundaryPoleContribution (m + 1) := by
  let k : ℕ := 2 * m + 1
  have hcross := thetaCuspTotalMoment_cross_nonneg k
  have hk0 : k = 2 * (m + 1) - 1 := by dsimp [k]; omega
  have hk1 : k + 1 = 2 * (m + 1) := by dsimp [k]; omega
  have hk2 : k + 2 = 2 * (m + 1) + 1 := by dsimp [k]; omega
  have hk3 : k + 3 = 2 * (m + 1) + 2 := by dsimp [k]; omega
  rw [hk1, hk2, hk3, hk0] at hcross
  unfold thetaCuspBoundaryPoleContribution
  exact mul_nonneg
    (div_nonneg thetaCuspFirstAtomBoundaryLogSlope_pos.le (by positivity)) hcross

theorem thetaCuspTuranDefect_succ_eq_boundary_add_regular (m : ℕ) :
    thetaCuspTuranDefect (m + 1) =
      thetaCuspBoundaryPoleContribution (m + 1) +
        thetaCuspRegularCurvatureContribution (m + 1) := by
  let n : ℕ := m + 1
  let k : ℕ := 2 * m + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hreg := thetaCuspRegularTuranIntegralIndex_eq_full_sub_pole hk
  rw [thetaCuspSlopeCurvatureTuranIntegralIndex_eq hk,
    thetaCuspBoundaryPoleTuranIntegralIndex_eq] at hreg
  have hk0 : k = 2 * n - 1 := by dsimp [k, n]; omega
  have hk1 : k + 1 = 2 * n := by dsimp [k, n]; omega
  have hk2 : k + 2 = 2 * n + 1 := by dsimp [k, n]; omega
  have hk3 : k + 3 = 2 * n + 2 := by dsimp [k, n]; omega
  have hdef : thetaCuspTuranDefectIndex k = thetaCuspTuranDefect n := by
    unfold thetaCuspTuranDefectIndex thetaCuspTuranDefect
    rw [hk1]
    have hkm1 : k - 1 = 2 * n - 2 := by dsimp [k, n]; omega
    rw [hkm1, hk3, hk0]
    norm_num only [Nat.cast_sub (show 1 ≤ 2 * n by dsimp [n]; omega),
      Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hdef, hk2, hk3, hk1, hk0] at hreg
  change thetaCuspTuranDefect n =
    thetaCuspBoundaryPoleContribution n + thetaCuspRegularCurvatureContribution n
  unfold thetaCuspBoundaryPoleContribution thetaCuspRegularCurvatureContribution
  have hden : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  field_simp [hden.ne']
  nlinarith [hreg]

/-! ## Positive crossing windows -/

def thetaCuspMomentDensity (k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * thetaCuspSourceTerm x 1

def thetaCuspTuranCrossingWindow (m : ℕ) (t : ℝ) : ℝ :=
  thetaCuspLowerMoment (2 * m) t * thetaCuspUpperTailMoment (2 * m + 2) t -
    thetaCuspLowerMoment (2 * m + 2) t * thetaCuspUpperTailMoment (2 * m) t

theorem continuous_thetaCuspMomentDensity (k : ℕ) :
    Continuous (thetaCuspMomentDensity k) := by
  unfold thetaCuspMomentDensity
  exact (continuous_id.pow k).mul continuous_thetaCuspSourceTerm_one

theorem thetaCuspUpperTailMoment_eq_integral_Ioi
    (k : ℕ) {t : ℝ} (_ht : 0 < t) :
    thetaCuspUpperTailMoment k t =
      ∫ x : ℝ in Ioi t, thetaCuspMomentDensity k x := by
  unfold thetaCuspUpperTailMoment thetaCuspMomentDensity
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici : Ioi t =ᵐ[volume] Ici t)]

theorem thetaCuspLowerMoment_eq_intervalIntegral
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    thetaCuspLowerMoment k t =
      ∫ x : ℝ in 0..t, thetaCuspMomentDensity k x := by
  have hfull : IntegrableOn (thetaCuspMomentDensity k) (Ioi 0) := by
    unfold thetaCuspMomentDensity
    exact integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hlow : IntegrableOn (thetaCuspMomentDensity k) (Ioc 0 t) :=
    hfull.mono_set (by intro x hx; exact hx.1)
  have hupp : IntegrableOn (thetaCuspMomentDensity k) (Ioi t) :=
    hfull.mono_set (by intro x hx; exact ht.trans hx)
  have hdis : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := by
    rw [Set.disjoint_left]
    intro x hxlow hxupp
    exact (not_lt_of_ge hxlow.2) hxupp
  have hunion : Ioc (0 : ℝ) t ∪ Ioi t = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact ht.trans hx
    · intro hx
      by_cases hxt : x ≤ t
      · exact Or.inl ⟨hx, hxt⟩
      · exact Or.inr (lt_of_not_ge hxt)
  have hsplit := MeasureTheory.setIntegral_union hdis measurableSet_Ioi hlow hupp
  rw [hunion] at hsplit
  unfold thetaCuspLowerMoment
  rw [thetaCuspTotalMoment_eq_integral_Ioi,
    thetaCuspUpperTailMoment_eq_integral_Ioi k ht,
    intervalIntegral.integral_of_le ht.le]
  unfold thetaCuspMomentDensity at hsplit ⊢
  linarith

theorem hasDerivAt_thetaCuspLowerMoment
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspLowerMoment k) (thetaCuspMomentDensity k t) t := by
  have hcont := continuous_thetaCuspMomentDensity k
  have hinterval := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 t)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  apply hinterval.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact thetaCuspLowerMoment_eq_intervalIntegral k hu

theorem hasDerivAt_thetaCuspUpperTailMoment
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspUpperTailMoment k) (-thetaCuspMomentDensity k t) t := by
  have hraw := (hasDerivAt_const t (thetaCuspTotalMoment k)).sub
    (hasDerivAt_thetaCuspLowerMoment k ht)
  have heq : thetaCuspUpperTailMoment k =ᶠ[𝓝 t]
      ((fun _ : ℝ => thetaCuspTotalMoment k) - thetaCuspLowerMoment k) := by
    filter_upwards with u
    unfold thetaCuspLowerMoment
    change thetaCuspUpperTailMoment k u =
      thetaCuspTotalMoment k -
        (thetaCuspTotalMoment k - thetaCuspUpperTailMoment k u)
    ring
  simpa only [zero_sub] using hraw.congr_of_eventuallyEq heq

theorem thetaCuspTuranCrossingWindow_derivative
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspTuranCrossingWindow m)
      (t ^ (2 * m) * thetaCuspSourceTerm t 1 *
        (thetaCuspTotalMoment (2 * m + 2) -
          t ^ (2 : ℕ) * thetaCuspTotalMoment (2 * m))) t := by
  have hLp := hasDerivAt_thetaCuspLowerMoment (2 * m) ht
  have hUp := hasDerivAt_thetaCuspUpperTailMoment (2 * m) ht
  have hLp2 := hasDerivAt_thetaCuspLowerMoment (2 * m + 2) ht
  have hUp2 := hasDerivAt_thetaCuspUpperTailMoment (2 * m + 2) ht
  have hraw := (hLp.mul hUp2).sub (hLp2.mul hUp)
  unfold thetaCuspTuranCrossingWindow
  refine hraw.congr_deriv ?_
  unfold thetaCuspMomentDensity thetaCuspLowerMoment
  rw [show t ^ (2 * m + 2) = t ^ (2 * m) * t ^ (2 : ℕ) by rw [pow_add]]
  ring

def thetaCuspTuranCrossingIntegral (m : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioc 0 t,
    ∫ v : ℝ in Ioi t,
      u ^ (2 * m) * v ^ (2 * m) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1

theorem thetaCuspLowerMoment_eq_integral_Ioc
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    thetaCuspLowerMoment k t =
      ∫ x : ℝ in Ioc 0 t, thetaCuspMomentDensity k x := by
  rw [thetaCuspLowerMoment_eq_intervalIntegral k ht,
    intervalIntegral.integral_of_le ht.le]

theorem thetaCuspTuranCrossingIntegral_eq_window
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    thetaCuspTuranCrossingIntegral m t =
      thetaCuspTuranCrossingWindow m t := by
  let p : ℕ := 2 * m
  let fp : ℝ → ℝ := thetaCuspMomentDensity p
  let fp2 : ℝ → ℝ := thetaCuspMomentDensity (p + 2)
  let Up : ℝ := thetaCuspUpperTailMoment p t
  let Up2 : ℝ := thetaCuspUpperTailMoment (p + 2) t
  have hfpFull : IntegrableOn fp (Ioi 0) := by
    dsimp [fp, thetaCuspMomentDensity]
    exact integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi p
  have hfp2Full : IntegrableOn fp2 (Ioi 0) := by
    dsimp [fp2, thetaCuspMomentDensity]
    exact integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (p + 2)
  have hfpLow : IntegrableOn fp (Ioc 0 t) :=
    hfpFull.mono_set (by intro x hx; exact hx.1)
  have hfp2Low : IntegrableOn fp2 (Ioc 0 t) :=
    hfp2Full.mono_set (by intro x hx; exact hx.1)
  have hfpUp : IntegrableOn fp (Ioi t) :=
    hfpFull.mono_set (by intro x hx; exact ht.trans hx)
  have hfp2Up : IntegrableOn fp2 (Ioi t) :=
    hfp2Full.mono_set (by intro x hx; exact ht.trans hx)
  have hUp : (∫ v : ℝ in Ioi t, fp v) = Up := by
    dsimp [Up, fp]
    exact (thetaCuspUpperTailMoment_eq_integral_Ioi p ht).symm
  have hUp2 : (∫ v : ℝ in Ioi t, fp2 v) = Up2 := by
    dsimp [Up2, fp2]
    exact (thetaCuspUpperTailMoment_eq_integral_Ioi (p + 2) ht).symm
  have hinner : ∀ u : ℝ,
      (∫ v : ℝ in Ioi t,
        u ^ p * v ^ p * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
          thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1) =
        fp u * Up2 - fp2 u * Up := by
    intro u
    have hAint : IntegrableOn (fun v => fp u * fp2 v) (Ioi t) :=
      hfp2Up.const_mul (fp u)
    have hBint : IntegrableOn (fun v => fp2 u * fp v) (Ioi t) :=
      hfpUp.const_mul (fp2 u)
    calc
      _ = ∫ v : ℝ in Ioi t, fp u * fp2 v - fp2 u * fp v := by
        apply integral_congr_ae
        filter_upwards with v
        dsimp [fp, fp2, thetaCuspMomentDensity]
        rw [show v ^ (p + 2) = v ^ p * v ^ (2 : ℕ) by rw [pow_add],
          show u ^ (p + 2) = u ^ p * u ^ (2 : ℕ) by rw [pow_add]]
        ring
      _ = (∫ v : ℝ in Ioi t, fp u * fp2 v) -
          ∫ v : ℝ in Ioi t, fp2 u * fp v := by
            exact MeasureTheory.integral_sub hAint hBint
      _ = fp u * (∫ v : ℝ in Ioi t, fp2 v) -
          fp2 u * (∫ v : ℝ in Ioi t, fp v) := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = _ := by rw [hUp, hUp2]
  have hAint : IntegrableOn (fun u => fp u * Up2) (Ioc 0 t) :=
    hfpLow.mul_const Up2
  have hBint : IntegrableOn (fun u => fp2 u * Up) (Ioc 0 t) :=
    hfp2Low.mul_const Up
  have hLp : (∫ u : ℝ in Ioc 0 t, fp u) = thetaCuspLowerMoment p t := by
    dsimp [fp]
    exact (thetaCuspLowerMoment_eq_integral_Ioc p ht).symm
  have hLp2 : (∫ u : ℝ in Ioc 0 t, fp2 u) =
      thetaCuspLowerMoment (p + 2) t := by
    dsimp [fp2]
    exact (thetaCuspLowerMoment_eq_integral_Ioc (p + 2) ht).symm
  unfold thetaCuspTuranCrossingIntegral
  change (∫ u : ℝ in Ioc 0 t,
    ∫ v : ℝ in Ioi t,
      u ^ p * v ^ p * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
        thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1) = _
  calc
    _ = ∫ u : ℝ in Ioc 0 t, fp u * Up2 - fp2 u * Up := by
      apply integral_congr_ae
      filter_upwards with u
      exact hinner u
    _ = (∫ u : ℝ in Ioc 0 t, fp u * Up2) -
        ∫ u : ℝ in Ioc 0 t, fp2 u * Up := by
          exact MeasureTheory.integral_sub hAint hBint
    _ = (∫ u : ℝ in Ioc 0 t, fp u) * Up2 -
        (∫ u : ℝ in Ioc 0 t, fp2 u) * Up := by
          rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
    _ = _ := by
      rw [hLp, hLp2]
      unfold thetaCuspTuranCrossingWindow Up Up2 p
      rfl

private def thetaCuspTuranCrossingInner (m : ℕ) (t u : ℝ) : ℝ :=
  ∫ v : ℝ in Ioi t,
    u ^ (2 * m) * v ^ (2 * m) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
      thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1

private theorem thetaCuspTuranCrossingInner_eq
    (m : ℕ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    thetaCuspTuranCrossingInner m t u =
      thetaCuspMomentDensity (2 * m) u *
          thetaCuspUpperTailMoment (2 * m + 2) t -
        thetaCuspMomentDensity (2 * m + 2) u *
          thetaCuspUpperTailMoment (2 * m) t := by
  let p : ℕ := 2 * m
  let fp : ℝ → ℝ := thetaCuspMomentDensity p
  let fp2 : ℝ → ℝ := thetaCuspMomentDensity (p + 2)
  have hfp : IntegrableOn fp (Ioi t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi p).mono_set
      (by intro x hx; exact ht.trans hx)
  have hfp2 : IntegrableOn fp2 (Ioi t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (p + 2)).mono_set
      (by intro x hx; exact ht.trans hx)
  have hAint : IntegrableOn (fun v => fp u * fp2 v) (Ioi t) :=
    hfp2.const_mul (fp u)
  have hBint : IntegrableOn (fun v => fp2 u * fp v) (Ioi t) :=
    hfp.const_mul (fp2 u)
  unfold thetaCuspTuranCrossingInner
  change (∫ v : ℝ in Ioi t,
    u ^ p * v ^ p * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
      thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1) = _
  calc
    _ = ∫ v : ℝ in Ioi t, fp u * fp2 v - fp2 u * fp v := by
      apply integral_congr_ae
      filter_upwards with v
      dsimp [fp, fp2, thetaCuspMomentDensity]
      rw [show v ^ (p + 2) = v ^ p * v ^ (2 : ℕ) by rw [pow_add],
        show u ^ (p + 2) = u ^ p * u ^ (2 : ℕ) by rw [pow_add]]
      ring
    _ = (∫ v : ℝ in Ioi t, fp u * fp2 v) -
        ∫ v : ℝ in Ioi t, fp2 u * fp v :=
          MeasureTheory.integral_sub hAint hBint
    _ = fp u * (∫ v : ℝ in Ioi t, fp2 v) -
        fp2 u * (∫ v : ℝ in Ioi t, fp v) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [← thetaCuspUpperTailMoment_eq_integral_Ioi p ht,
        ← thetaCuspUpperTailMoment_eq_integral_Ioi (p + 2) ht]

private theorem thetaCuspTuranCrossingInner_pos
    (m : ℕ) {t u : ℝ} (ht : 0 < t) (hu : u ∈ Ioc (0 : ℝ) t) :
    0 < thetaCuspTuranCrossingInner m t u := by
  let g : ℝ → ℝ := fun v =>
    u ^ (2 * m) * v ^ (2 * m) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
      thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1
  have hgint : IntegrableOn g (Ioi t) := by
    let fp : ℝ → ℝ := thetaCuspMomentDensity (2 * m)
    let fp2 : ℝ → ℝ := thetaCuspMomentDensity (2 * m + 2)
    have hfp : IntegrableOn fp (Ioi t) :=
      (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * m)).mono_set
        (by intro x hx; exact ht.trans hx)
    have hfp2 : IntegrableOn fp2 (Ioi t) :=
      (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * m + 2)).mono_set
        (by intro x hx; exact ht.trans hx)
    have hsep : IntegrableOn (fun v => fp u * fp2 v - fp2 u * fp v) (Ioi t) :=
      (hfp2.const_mul (fp u)).sub (hfp.const_mul (fp2 u))
    apply hsep.congr
    filter_upwards with v
    dsimp [g, fp, fp2, thetaCuspMomentDensity]
    rw [show v ^ (2 * m + 2) = v ^ (2 * m) * v ^ (2 : ℕ) by rw [pow_add],
      show u ^ (2 * m + 2) = u ^ (2 * m) * u ^ (2 : ℕ) by rw [pow_add]]
    ring
  have hgpos : ∀ v ∈ Ioi t, 0 < g v := by
    intro v hv
    have hv0 : 0 < v := ht.trans hv
    have huv : u < v := hu.2.trans_lt hv
    have hsq : 0 < v ^ (2 : ℕ) - u ^ (2 : ℕ) := by
      have hfac : 0 < (v - u) * (v + u) :=
        mul_pos (sub_pos.mpr huv) (add_pos hv0 hu.1)
      nlinarith
    dsimp [g]
    have hsu : 0 < thetaCuspSourceTerm u 1 :=
      thetaCuspSourceTerm_pos_of_pos_of_nat_pos (n := 1) hu.1 (by norm_num)
    have hsv : 0 < thetaCuspSourceTerm v 1 :=
      thetaCuspSourceTerm_pos_of_pos_of_nat_pos (n := 1) hv0 (by norm_num)
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (pow_pos hu.1 (2 * m)) (pow_pos hv0 (2 * m))) hsq) hsu) hsv
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioi t)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (hgpos v hv).le
  unfold thetaCuspTuranCrossingInner
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hgnn hgint).2
  have hsupp : Function.support g ∩ Ioi t = Ioi t := by
    ext v
    constructor
    · exact fun hv => hv.2
    · intro hv
      exact ⟨ne_of_gt (hgpos v hv), hv⟩
  rw [hsupp]
  exact isOpen_Ioi.measure_pos volume ⟨t + 1, by simp⟩

theorem thetaCuspTuranCrossingWindow_pos
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspTuranCrossingWindow m t := by
  let F : ℝ → ℝ := thetaCuspTuranCrossingInner m t
  let fp : ℝ → ℝ := thetaCuspMomentDensity (2 * m)
  let fp2 : ℝ → ℝ := thetaCuspMomentDensity (2 * m + 2)
  let Up : ℝ := thetaCuspUpperTailMoment (2 * m) t
  let Up2 : ℝ := thetaCuspUpperTailMoment (2 * m + 2) t
  have hfp : IntegrableOn fp (Ioc 0 t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * m)).mono_set
      (by intro x hx; exact hx.1)
  have hfp2 : IntegrableOn fp2 (Ioc 0 t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (2 * m + 2)).mono_set
      (by intro x hx; exact hx.1)
  have hsep : IntegrableOn (fun u => fp u * Up2 - fp2 u * Up) (Ioc 0 t) :=
    (hfp.mul_const Up2).sub (hfp2.mul_const Up)
  have hFint : IntegrableOn F (Ioc 0 t) := by
    apply hsep.congr
    filter_upwards with u
    exact (thetaCuspTuranCrossingInner_eq m ht u).symm
  have hFpos : ∀ u ∈ Ioc (0 : ℝ) t, 0 < F u := by
    intro u hu
    exact thetaCuspTuranCrossingInner_pos m ht hu
  have hFnn : 0 ≤ᵐ[volume.restrict (Ioc 0 t)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hFpos u hu).le
  rw [← thetaCuspTuranCrossingIntegral_eq_window m ht]
  unfold thetaCuspTuranCrossingIntegral
  change 0 < ∫ u : ℝ in Ioc 0 t, F u
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hFnn hFint).2
  have hsupp : Function.support F ∩ Ioc 0 t = Ioc 0 t := by
    ext u
    constructor
    · exact fun hu => hu.2
    · intro hu
      exact ⟨ne_of_gt (hFpos u hu), hu⟩
  rw [hsupp, Real.volume_Ioc]
  simp [ht]

def thetaCuspTuranCrossingPeak (m : ℕ) : ℝ :=
  Real.sqrt (thetaCuspTotalMoment (2 * m + 2) /
    thetaCuspTotalMoment (2 * m))

theorem thetaCuspTuranCrossingPeak_pos (m : ℕ) :
    0 < thetaCuspTuranCrossingPeak m := by
  unfold thetaCuspTuranCrossingPeak
  exact Real.sqrt_pos.2
    (div_pos (thetaCuspTotalMoment_pos (2 * m + 2))
      (thetaCuspTotalMoment_pos (2 * m)))

theorem thetaCuspTuranCrossingPeak_sq (m : ℕ) :
    thetaCuspTuranCrossingPeak m ^ (2 : ℕ) =
      thetaCuspTotalMoment (2 * m + 2) /
        thetaCuspTotalMoment (2 * m) := by
  unfold thetaCuspTuranCrossingPeak
  exact Real.sq_sqrt (div_nonneg
    (thetaCuspTotalMoment_pos (2 * m + 2)).le
    (thetaCuspTotalMoment_pos (2 * m)).le)

private theorem thetaCuspTuranCrossingBracket_pos_before_peak
    (m : ℕ) {t : ℝ} (ht : 0 < t)
    (htau : t < thetaCuspTuranCrossingPeak m) :
    0 < thetaCuspTotalMoment (2 * m + 2) -
      t ^ (2 : ℕ) * thetaCuspTotalMoment (2 * m) := by
  have hpeak := thetaCuspTuranCrossingPeak_pos m
  have hsquare : t ^ (2 : ℕ) < thetaCuspTuranCrossingPeak m ^ (2 : ℕ) := by
    have hfac : 0 < (thetaCuspTuranCrossingPeak m - t) *
        (thetaCuspTuranCrossingPeak m + t) :=
      mul_pos (sub_pos.mpr htau) (add_pos hpeak ht)
    nlinarith
  rw [thetaCuspTuranCrossingPeak_sq] at hsquare
  have hM := thetaCuspTotalMoment_pos (2 * m)
  have hmul := mul_lt_mul_of_pos_right hsquare hM
  field_simp [hM.ne'] at hmul
  nlinarith

private theorem thetaCuspTuranCrossingBracket_neg_after_peak
    (m : ℕ) {t : ℝ} (htau : thetaCuspTuranCrossingPeak m < t) :
    thetaCuspTotalMoment (2 * m + 2) -
      t ^ (2 : ℕ) * thetaCuspTotalMoment (2 * m) < 0 := by
  have hpeak := thetaCuspTuranCrossingPeak_pos m
  have ht : 0 < t := hpeak.trans htau
  have hsquare : thetaCuspTuranCrossingPeak m ^ (2 : ℕ) < t ^ (2 : ℕ) := by
    have hfac : 0 < (t - thetaCuspTuranCrossingPeak m) *
        (t + thetaCuspTuranCrossingPeak m) :=
      mul_pos (sub_pos.mpr htau) (add_pos ht hpeak)
    nlinarith
  rw [thetaCuspTuranCrossingPeak_sq] at hsquare
  have hM := thetaCuspTotalMoment_pos (2 * m)
  have hmul := mul_lt_mul_of_pos_right hsquare hM
  field_simp [hM.ne'] at hmul
  nlinarith

theorem thetaCuspTuranCrossingWindow_deriv_pos_before_peak
    (m : ℕ) {t : ℝ} (ht : 0 < t)
    (htau : t < thetaCuspTuranCrossingPeak m) :
    0 < deriv (thetaCuspTuranCrossingWindow m) t := by
  rw [(thetaCuspTuranCrossingWindow_derivative m ht).deriv]
  have hsource : 0 < thetaCuspSourceTerm t 1 :=
    thetaCuspSourceTerm_pos_of_pos_of_nat_pos (n := 1) ht (by norm_num)
  exact mul_pos (mul_pos (pow_pos ht (2 * m)) hsource)
    (thetaCuspTuranCrossingBracket_pos_before_peak m ht htau)

theorem thetaCuspTuranCrossingWindow_deriv_neg_after_peak
    (m : ℕ) {t : ℝ} (htau : thetaCuspTuranCrossingPeak m < t) :
    deriv (thetaCuspTuranCrossingWindow m) t < 0 := by
  have ht := (thetaCuspTuranCrossingPeak_pos m).trans htau
  rw [(thetaCuspTuranCrossingWindow_derivative m ht).deriv]
  have hsource : 0 < thetaCuspSourceTerm t 1 :=
    thetaCuspSourceTerm_pos_of_pos_of_nat_pos (n := 1) ht (by norm_num)
  exact mul_neg_of_pos_of_neg (mul_pos (pow_pos ht (2 * m)) hsource)
    (thetaCuspTuranCrossingBracket_neg_after_peak m htau)

theorem thetaCuspTuranCrossingWindow_strictMonoOn_before_peak (m : ℕ) :
    StrictMonoOn (thetaCuspTuranCrossingWindow m)
      (Ioo 0 (thetaCuspTuranCrossingPeak m)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (thetaCuspTuranCrossingPeak m))
  · intro t ht
    exact (thetaCuspTuranCrossingWindow_derivative m ht.1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact thetaCuspTuranCrossingWindow_deriv_pos_before_peak m ht.1 ht.2

theorem thetaCuspTuranCrossingWindow_strictAntiOn_after_peak (m : ℕ) :
    StrictAntiOn (thetaCuspTuranCrossingWindow m)
      (Ioi (thetaCuspTuranCrossingPeak m)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (thetaCuspTuranCrossingPeak m))
  · intro t ht
    have ht0 := (thetaCuspTuranCrossingPeak_pos m).trans ht
    exact (thetaCuspTuranCrossingWindow_derivative m ht0).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact thetaCuspTuranCrossingWindow_deriv_neg_after_peak m ht

theorem thetaCuspTuranCrossingPeak_one_le_two :
    thetaCuspTuranCrossingPeak 1 ≤ thetaCuspTuranCrossingPeak 2 := by
  have hcs := thetaCuspTotalMoment_cauchySchwarz 1 3
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at hcs ⊢
  unfold thetaCuspTuranCrossingPeak
  apply Real.sqrt_le_sqrt
  have hM2 := thetaCuspTotalMoment_pos 2
  have hM4 := thetaCuspTotalMoment_pos 4
  apply (div_le_div_iff₀ hM2 hM4).2
  nlinarith

/-! ## Exact low-gate reformulation -/

theorem thetaCuspAtomRawEvenMoment_one_eq_two_mul_total (j : ℕ) :
    thetaCuspAtomRawEvenMoment j 1 =
      2 * thetaCuspTotalMoment (2 * j) := by
  rw [thetaCuspAtomRawEvenMoment, thetaCuspTotalMoment_eq_integral_Ioi]

def thetaCuspReflectedBudgetInflation : ℝ :=
  (thetaCuspFirstAtomHalfDensityPairBudget + thetaCuspHigherHalfDensityBudget) /
    thetaCuspFirstAtomHalfDensityPairBudget

theorem thetaCuspFirstAtomUpperGate_iff_turanMargin :
    (16 * (thetaCuspAtomRawEvenMoment 0 1 +
          thetaCuspHigherHalfDensityBudget) *
        thetaCuspAtomRawEvenMoment 2 1 ≤
      45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) ↔
    ((1 / 45 + 16 * thetaCuspHigherHalfDensityBudget /
          (45 * thetaCuspAtomRawEvenMoment 0 1)) *
        thetaCuspTotalMoment 0 * thetaCuspTotalMoment 4 ≤
      thetaCuspTuranDefect 1) := by
  have h0 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 0
  have h1 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 1
  have h2 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 2
  norm_num only [Nat.reduceMul] at h0 h1 h2
  rw [h0, h1, h2]
  unfold thetaCuspTuranDefect
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_one,
    Nat.cast_ofNat]
  have hM0 := thetaCuspTotalMoment_pos 0
  constructor <;> intro h
  · field_simp [hM0.ne']
    field_simp [hM0.ne'] at h
    nlinarith
  · field_simp [hM0.ne'] at h ⊢
    nlinarith

theorem thetaCuspFirstAtomLowerGate_iff_turanMargin :
    (14 * (thetaCuspFirstAtomHalfDensityPairBudget +
          thetaCuspHigherHalfDensityBudget) *
        thetaCuspAtomRawEvenMoment 2 1 ^ (2 : ℕ) ≤
      9 * thetaCuspFirstAtomHalfDensityPairBudget *
        thetaCuspAtomRawEvenMoment 1 1 * thetaCuspAtomRawEvenMoment 3 1) ↔
    (thetaCuspTuranDefect 2 ≤
      (1 - 14 * thetaCuspReflectedBudgetInflation / 15) *
        thetaCuspTotalMoment 4 ^ (2 : ℕ)) := by
  have h1 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 1
  have h2 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 2
  have h3 := thetaCuspAtomRawEvenMoment_one_eq_two_mul_total 3
  norm_num only [Nat.reduceMul] at h1 h2 h3
  rw [h1, h2, h3]
  unfold thetaCuspTuranDefect thetaCuspReflectedBudgetInflation
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat]
  have hW := thetaCuspFirstAtomHalfDensityPairBudget_pos
  constructor <;> intro h
  · field_simp [hW.ne']
    field_simp [hW.ne'] at h
    nlinarith
  · field_simp [hW.ne'] at h ⊢
    nlinarith

theorem thetaCuspHigherBudget_div_pairBudget_lt_uniformLoss :
    thetaCuspHigherHalfDensityBudget /
        thetaCuspFirstAtomHalfDensityPairBudget < 8 / 2997 := by
  have hH := thetaCuspHigherHalfDensityBudget_le_uniformLoss_mul_firstAtomZero
  have ha0 : 0 < thetaCuspAtomRawEvenMoment 0 1 :=
    thetaCuspAtomRawEvenMoment_pos_of_nat_pos (n := 1) 0 (by norm_num)
  have ha1 : 0 < thetaCuspAtomRawEvenMoment 1 1 :=
    thetaCuspAtomRawEvenMoment_pos_of_nat_pos (n := 1) 1 (by norm_num)
  have hW := thetaCuspFirstAtomHalfDensityPairBudget_pos
  have ha0W : thetaCuspAtomRawEvenMoment 0 1 <
      thetaCuspFirstAtomHalfDensityPairBudget := by
    unfold thetaCuspFirstAtomHalfDensityPairBudget
    nlinarith
  have hc : (0 : ℝ) < 8 / 2997 := by norm_num
  have hstrict : thetaCuspHigherHalfDensityBudget <
      (8 / 2997 : ℝ) * thetaCuspFirstAtomHalfDensityPairBudget :=
    hH.trans_lt (mul_lt_mul_of_pos_left ha0W hc)
  exact (div_lt_iff₀ hW).2 hstrict

theorem thetaCuspReflectedBudgetInflation_lt_fifteen_fourteen :
    thetaCuspReflectedBudgetInflation < 15 / 14 := by
  have hratio := thetaCuspHigherBudget_div_pairBudget_lt_uniformLoss
  have hW := thetaCuspFirstAtomHalfDensityPairBudget_pos
  unfold thetaCuspReflectedBudgetInflation
  rw [add_div]
  field_simp [hW.ne'] at hratio ⊢
  nlinarith

theorem thetaCuspLowerGate_marginCoefficient_pos :
    0 < 1 - 14 * thetaCuspReflectedBudgetInflation / 15 := by
  nlinarith [thetaCuspReflectedBudgetInflation_lt_fifteen_fourteen]

theorem thetaCuspFirstAtomUpperTuranMargin_iff_regularContribution :
    ((1 / 45 + 16 * thetaCuspHigherHalfDensityBudget /
          (45 * thetaCuspAtomRawEvenMoment 0 1)) *
        thetaCuspTotalMoment 0 * thetaCuspTotalMoment 4 ≤
      thetaCuspTuranDefect 1) ↔
    ((1 / 45 + 16 * thetaCuspHigherHalfDensityBudget /
          (45 * thetaCuspAtomRawEvenMoment 0 1)) *
        thetaCuspTotalMoment 0 * thetaCuspTotalMoment 4 -
          thetaCuspBoundaryPoleContribution 1 ≤
      thetaCuspRegularCurvatureContribution 1) := by
  rw [thetaCuspTuranDefect_succ_eq_boundary_add_regular 0]
  norm_num only [Nat.zero_add]
  constructor <;> intro h <;> linarith

theorem thetaCuspFirstAtomLowerTuranMargin_iff_regularContribution :
    (thetaCuspTuranDefect 2 ≤
      (1 - 14 * thetaCuspReflectedBudgetInflation / 15) *
        thetaCuspTotalMoment 4 ^ (2 : ℕ)) ↔
    (thetaCuspRegularCurvatureContribution 2 ≤
      (1 - 14 * thetaCuspReflectedBudgetInflation / 15) *
          thetaCuspTotalMoment 4 ^ (2 : ℕ) -
        thetaCuspBoundaryPoleContribution 2) := by
  rw [thetaCuspTuranDefect_succ_eq_boundary_add_regular 1]
  norm_num only [Nat.reduceAdd]
  constructor <;> intro h <;> linarith

/-! ## Absolute Fubini for the one-seam representation -/

private theorem integrableOn_natPow_mul_abs_regularSlopeQuotient_source
    {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspSourceTerm x 1 *
        |thetaCuspRegularSlopeQuotient x|) (Ioi 0) := by
  let f : ℝ → ℝ := fun x =>
    x ^ (k - 1) *
      (thetaCuspFirstLogPotentialSlope x - thetaCuspFirstLogPotentialSlope 0) *
        thetaCuspSourceTerm x 1
  have hA : IntegrableOn (fun x : ℝ =>
      x ^ (k - 1) * thetaCuspFirstLogPotentialSlope x *
        thetaCuspSourceTerm x 1) (Ioi 0) :=
    integrableOn_natPow_mul_thetaCuspFirstLogPotentialSlope_source (k - 1)
  have hB0 : IntegrableOn (fun x : ℝ =>
      x ^ (k - 1) * thetaCuspSourceTerm x 1) (Ioi 0) :=
    integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (k - 1)
  have hB : IntegrableOn (fun x : ℝ =>
      thetaCuspFirstLogPotentialSlope 0 *
        (x ^ (k - 1) * thetaCuspSourceTerm x 1)) (Ioi 0) :=
    hB0.const_mul _
  have hf : IntegrableOn f (Ioi 0) := by
    have hsub := hA.sub hB
    apply hsub.congr
    filter_upwards with x
    unfold f
    simp only [Pi.sub_apply]
    ring
  apply hf.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  rw [Real.norm_eq_abs]
  unfold f thetaCuspRegularSlopeQuotient
  rw [abs_div, abs_of_pos hx, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg hx.le (k - 1)),
    abs_of_nonneg (thetaCuspSourceTerm_nonneg_of_pos hx 1)]
  rw [show k = k - 1 + 1 by omega, pow_succ]
  field_simp [hx.ne']
  rw [show k - 1 + 1 - 1 = k - 1 by omega]
  ring

private def thetaCuspRegularFubiniProfile (k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * thetaCuspSourceTerm x 1 *
    (|thetaCuspRegularSlopeQuotient x| +
      (1 + 2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|))

private theorem integrableOn_thetaCuspRegularFubiniProfile
    {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (thetaCuspRegularFubiniProfile k) (Ioi 0) := by
  let C : ℝ :=
    1 + 2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|
  have hR := integrableOn_natPow_mul_abs_regularSlopeQuotient_source hk
  have hM := integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi k
  have hMC : IntegrableOn (fun x : ℝ =>
      (x ^ k * thetaCuspSourceTerm x 1) * C) (Ioi 0) :=
    hM.mul_const C
  apply (hR.add hMC).congr
  filter_upwards with x
  unfold thetaCuspRegularFubiniProfile C
  simp only [Pi.add_apply]
  ring

private theorem intervalIntegrable_thetaCuspRegularSlopeCurvature
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable thetaCuspRegularSlopeCurvature volume u v := by
  have hpos : ∀ t ∈ uIcc u v, 0 < t := by
    intro t ht
    exact (lt_min hu hv).trans_le ht.1
  have hcont : ContinuousOn thetaCuspRegularSlopeCurvature (uIcc u v) := by
    intro t ht
    have ht0 := (hpos t ht).ne'
    have hcurv : ContinuousAt (thetaCuspBornWittenLogCurvature 1) t :=
      (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hslope : ContinuousAt thetaCuspFirstLogPotentialSlope t :=
      (hasDerivAt_two_thetaCuspBornWittenSuperpotential
        (n := 1) (by norm_num) (hpos t ht).le).continuousAt
    have hden : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ)) t := continuousAt_id.pow 2
    unfold thetaCuspRegularSlopeCurvature thetaCuspRegularCurvatureNumerator
    exact (((continuousAt_id.mul hcurv).sub
      (hslope.sub continuousAt_const)).div hden
        (pow_ne_zero 2 ht0)).continuousWithinAt
  exact hcont.intervalIntegrable

private theorem intervalIntegral_abs_thetaCuspRegularSlopeCurvature_before
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hvc : v ≤ thetaCuspRegularCurvatureSeam) :
    (∫ t : ℝ in u..v, |thetaCuspRegularSlopeCurvature t|) =
      thetaCuspRegularSlopeQuotient u - thetaCuspRegularSlopeQuotient v := by
  calc
    (∫ t : ℝ in u..v, |thetaCuspRegularSlopeCurvature t|) =
        ∫ t : ℝ in u..v, -thetaCuspRegularSlopeCurvature t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      have ht0 : 0 < t := hu.trans_le ht.1
      have htc : t ≤ thetaCuspRegularCurvatureSeam := ht.2.trans hvc
      have hnonpos : thetaCuspRegularSlopeCurvature t ≤ 0 := by
        rcases htc.eq_or_lt with h | h
        · rw [h, thetaCuspRegularSlopeCurvature_signLaw.2.1]
        · exact (thetaCuspRegularSlopeCurvature_signLaw.1 t ht0 h).le
      change |thetaCuspRegularSlopeCurvature t| =
        -thetaCuspRegularSlopeCurvature t
      rw [abs_of_nonpos hnonpos]
    _ = -(∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t) :=
      intervalIntegral.integral_neg
    _ = _ := by
      rw [intervalIntegral_thetaCuspRegularSlopeCurvature hu
        (hu.trans_le huv)]
      ring

private theorem intervalIntegral_abs_thetaCuspRegularSlopeCurvature_after
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hcu : thetaCuspRegularCurvatureSeam ≤ u) :
    (∫ t : ℝ in u..v, |thetaCuspRegularSlopeCurvature t|) =
      thetaCuspRegularSlopeQuotient v - thetaCuspRegularSlopeQuotient u := by
  calc
    (∫ t : ℝ in u..v, |thetaCuspRegularSlopeCurvature t|) =
        ∫ t : ℝ in u..v, thetaCuspRegularSlopeCurvature t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      have hct : thetaCuspRegularCurvatureSeam ≤ t := hcu.trans ht.1
      have hnonneg : 0 ≤ thetaCuspRegularSlopeCurvature t := by
        rcases hct.eq_or_lt with h | h
        · rw [← h, thetaCuspRegularSlopeCurvature_signLaw.2.1]
        · exact (thetaCuspRegularSlopeCurvature_signLaw.2.2 t h).le
      change |thetaCuspRegularSlopeCurvature t| =
        thetaCuspRegularSlopeCurvature t
      rw [abs_of_nonneg hnonneg]
    _ = _ := intervalIntegral_thetaCuspRegularSlopeCurvature hu
      (hu.trans_le huv)

private theorem intervalIntegral_abs_thetaCuspRegularSlopeCurvature_le
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ t : ℝ in u..v, |thetaCuspRegularSlopeCurvature t|) ≤
      |thetaCuspRegularSlopeQuotient u| +
        |thetaCuspRegularSlopeQuotient v| +
          2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam| := by
  let c : ℝ := thetaCuspRegularCurvatureSeam
  by_cases hvc : v ≤ c
  · rw [intervalIntegral_abs_thetaCuspRegularSlopeCurvature_before hu huv hvc]
    have huabs := le_abs_self (thetaCuspRegularSlopeQuotient u)
    have hvabs := neg_le_abs (thetaCuspRegularSlopeQuotient v)
    have hcabs : 0 ≤ 2 * |thetaCuspRegularSlopeQuotient c| := by positivity
    dsimp [c] at hcabs ⊢
    linarith
  by_cases hcu : c ≤ u
  · rw [intervalIntegral_abs_thetaCuspRegularSlopeCurvature_after hu huv hcu]
    have hvabs := le_abs_self (thetaCuspRegularSlopeQuotient v)
    have huabs := neg_le_abs (thetaCuspRegularSlopeQuotient u)
    have hcabs : 0 ≤ 2 * |thetaCuspRegularSlopeQuotient c| := by positivity
    dsimp [c] at hcabs ⊢
    linarith
  · have huc : u < c := lt_of_not_ge hcu
    have hcv : c < v := lt_of_not_ge hvc
    have hc0 : 0 < c := thetaCuspRegularCurvatureSeam_spec.1
    have hIuc := intervalIntegrable_thetaCuspRegularSlopeCurvature hu hc0
    have hIcv := intervalIntegrable_thetaCuspRegularSlopeCurvature hc0
      (hc0.trans hcv)
    have habsadd := intervalIntegral.integral_add_adjacent_intervals
      hIuc.norm hIcv.norm
    simp only [Real.norm_eq_abs] at habsadd
    rw [intervalIntegral_abs_thetaCuspRegularSlopeCurvature_before
        hu huc.le le_rfl,
      intervalIntegral_abs_thetaCuspRegularSlopeCurvature_after
        hc0 hcv.le le_rfl] at habsadd
    rw [← habsadd]
    have huabs := le_abs_self (thetaCuspRegularSlopeQuotient u)
    have hvabs := le_abs_self (thetaCuspRegularSlopeQuotient v)
    have hcabs := neg_le_abs (thetaCuspRegularSlopeQuotient c)
    dsimp [c] at huabs hvabs hcabs ⊢
    linarith

private def thetaCuspTuranCrossKernel (m : ℕ) (u v : ℝ) : ℝ :=
  u ^ (2 * m) * v ^ (2 * m) * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) *
    thetaCuspSourceTerm u 1 * thetaCuspSourceTerm v 1

private theorem abs_thetaCuspTuranCrossKernel_mul_endpoint_le_profile
    {m : ℕ} {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    |thetaCuspTuranCrossKernel m u v| *
        (|thetaCuspRegularSlopeQuotient u| +
          |thetaCuspRegularSlopeQuotient v| +
            2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|) ≤
      thetaCuspRegularFubiniProfile (2 * m) u *
          thetaCuspRegularFubiniProfile (2 * m + 2) v +
        thetaCuspRegularFubiniProfile (2 * m + 2) u *
          thetaCuspRegularFubiniProfile (2 * m) v := by
  let ru : ℝ := |thetaCuspRegularSlopeQuotient u|
  let rv : ℝ := |thetaCuspRegularSlopeQuotient v|
  let C : ℝ := 2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|
  let D : ℝ := 1 + C
  let A : ℝ := u ^ (2 * m) * thetaCuspSourceTerm u 1
  let B : ℝ := v ^ (2 * m) * thetaCuspSourceTerm v 1
  have hsu : 0 ≤ thetaCuspSourceTerm u 1 :=
    thetaCuspSourceTerm_nonneg_of_pos hu 1
  have hsv : 0 ≤ thetaCuspSourceTerm v 1 :=
    thetaCuspSourceTerm_nonneg_of_pos hv 1
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg hu.le _) hsu
  have hB : 0 ≤ B := mul_nonneg (pow_nonneg hv.le _) hsv
  have hru : 0 ≤ ru := abs_nonneg _
  have hrv : 0 ≤ rv := abs_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hfactor : ru + rv + C ≤ (ru + D) * (rv + D) := by
    have hrr : 0 ≤ ru * rv := mul_nonneg hru hrv
    have hDr : 0 ≤ (D - 1) * (ru + rv) :=
      mul_nonneg (sub_nonneg.mpr hD) (add_nonneg hru hrv)
    have hDC : C ≤ D ^ (2 : ℕ) := by
      dsimp [D]
      nlinarith [sq_nonneg C]
    nlinarith
  have hsquare : 0 ≤ v ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hdiff : v ^ (2 : ℕ) - u ^ (2 : ℕ) ≤ v ^ (2 : ℕ) + u ^ (2 : ℕ) := by
    nlinarith [sq_nonneg u]
  have hkernel : |thetaCuspTuranCrossKernel m u v| =
      A * B * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) := by
    unfold thetaCuspTuranCrossKernel A B
    rw [abs_of_nonneg]
    · ring
    · positivity
  have hmain : A * B * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) * (ru + rv + C) ≤
      A * B * (v ^ (2 : ℕ) + u ^ (2 : ℕ)) * ((ru + D) * (rv + D)) := by
    gcongr
  rw [hkernel]
  change A * B * (v ^ (2 : ℕ) - u ^ (2 : ℕ)) * (ru + rv + C) ≤ _
  calc
    _ ≤ A * B * (v ^ (2 : ℕ) + u ^ (2 : ℕ)) * ((ru + D) * (rv + D)) := hmain
    _ = _ := by
      dsimp [D, C]
      unfold thetaCuspRegularFubiniProfile A B ru rv
      rw [show u ^ (2 * m + 2) = u ^ (2 * m) * u ^ (2 : ℕ) by rw [pow_add],
        show v ^ (2 * m + 2) = v ^ (2 * m) * v ^ (2 : ℕ) by rw [pow_add]]
      ring

private def thetaCuspTuranFubiniSet : Set ((ℝ × ℝ) × ℝ) :=
  {z | 0 < z.1.1 ∧ z.1.1 < z.2 ∧ z.2 < z.1.2}

private def thetaCuspTuranFubiniIntegrand
    (m : ℕ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  thetaCuspTuranFubiniSet.indicator
    (fun q => thetaCuspTuranCrossKernel m q.1.1 q.1.2 *
      thetaCuspRegularSlopeCurvature q.2) z

private theorem aestronglyMeasurable_thetaCuspTuranFubiniIntegrand
    (m : ℕ) {μ : Measure ((ℝ × ℝ) × ℝ)} :
    AEStronglyMeasurable (thetaCuspTuranFubiniIntegrand m) μ := by
  have hS : MeasurableSet thetaCuspTuranFubiniSet := by
    unfold thetaCuspTuranFubiniSet
    measurability
  let base : ((ℝ × ℝ) × ℝ) → ℝ := fun q =>
    thetaCuspTuranCrossKernel m q.1.1 q.1.2 *
      thetaCuspRegularSlopeCurvature q.2
  have hbase : ContinuousOn base thetaCuspTuranFubiniSet := by
    intro z hz
    have ht0 : 0 < z.2 := hz.1.trans hz.2.1
    have hcurv : ContinuousAt (thetaCuspBornWittenLogCurvature 1) z.2 :=
      (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) ht0.le).continuousAt
    have hslope : ContinuousAt thetaCuspFirstLogPotentialSlope z.2 :=
      (hasDerivAt_two_thetaCuspBornWittenSuperpotential
        (n := 1) (by norm_num) ht0.le).continuousAt
    have hden : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ)) z.2 :=
      continuousAt_id.pow 2
    have hE : ContinuousAt thetaCuspRegularSlopeCurvature z.2 := by
      unfold thetaCuspRegularSlopeCurvature thetaCuspRegularCurvatureNumerator
      exact ((continuousAt_id.mul hcurv).sub
        (hslope.sub continuousAt_const)).div hden (pow_ne_zero 2 ht0.ne')
    have hK : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          thetaCuspTuranCrossKernel m q.1.1 q.1.2) z := by
      unfold thetaCuspTuranCrossKernel
      have hucoord : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => q.1.1) z :=
        continuousAt_fst.comp continuousAt_fst
      have hvcoord : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => q.1.2) z :=
        continuousAt_snd.comp continuousAt_fst
      have hsu : ContinuousAt
          (fun q : (ℝ × ℝ) × ℝ => thetaCuspSourceTerm q.1.1 1) z :=
        continuous_thetaCuspSourceTerm_one.continuousAt.comp hucoord
      have hsv : ContinuousAt
          (fun q : (ℝ × ℝ) × ℝ => thetaCuspSourceTerm q.1.2 1) z :=
        continuous_thetaCuspSourceTerm_one.continuousAt.comp hvcoord
      exact ((((hucoord.pow (2 * m)).mul (hvcoord.pow (2 * m))).mul
        ((hvcoord.pow 2).sub (hucoord.pow 2))).mul hsu).mul hsv
    exact (hK.mul (hE.comp continuousAt_snd)).continuousWithinAt
  have h1 : AEStronglyMeasurable base (μ.restrict thetaCuspTuranFubiniSet) :=
    hbase.aestronglyMeasurable hS
  have h2 : AEStronglyMeasurable
      (thetaCuspTuranFubiniSet.indicator (h1.mk base)) μ :=
    (h1.stronglyMeasurable_mk.indicator hS).aestronglyMeasurable
  unfold thetaCuspTuranFubiniIntegrand
  apply h2.congr
  apply ae_of_ae_restrict_of_ae_restrict_compl thetaCuspTuranFubiniSet
  · exact Filter.EventuallyEq.indicator h1.ae_eq_mk.symm
  · exact ae_restrict_of_forall_mem hS.compl (fun x hx => by
      simp [Set.indicator_of_notMem hx])

private theorem integrable_thetaCuspTuranFubiniIntegrand
    {m : ℕ} (hm : 1 ≤ m) :
    Integrable (thetaCuspTuranFubiniIntegrand m)
      (((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))).prod volume) := by
  let μuv : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  let H : ℝ × ℝ → ℝ := fun z =>
    thetaCuspRegularFubiniProfile (2 * m) z.1 *
        thetaCuspRegularFubiniProfile (2 * m + 2) z.2 +
      thetaCuspRegularFubiniProfile (2 * m + 2) z.1 *
        thetaCuspRegularFubiniProfile (2 * m) z.2
  have hp : 1 ≤ 2 * m := by omega
  have hp2 : 1 ≤ 2 * m + 2 := by omega
  have hgP := integrableOn_thetaCuspRegularFubiniProfile hp
  have hgP2 := integrableOn_thetaCuspRegularFubiniProfile hp2
  have hHprod : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
    exact (hgP.mul_prod hgP2).add (hgP2.mul_prod hgP)
  have hH : Integrable H μuv := by
    rw [MeasureTheory.Measure.prod_restrict] at hHprod
    exact hHprod
  have hmeas : AEStronglyMeasurable (thetaCuspTuranFubiniIntegrand m)
      (μuv.prod volume) :=
    aestronglyMeasurable_thetaCuspTuranFubiniIntegrand m
  apply (MeasureTheory.integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      with z hz
    rcases hz with ⟨hu, hv⟩
    change 0 < z.1 at hu
    change 0 < z.2 at hv
    by_cases huv : z.1 < z.2
    · have hE := intervalIntegrable_thetaCuspRegularSlopeCurvature hu hv
      have hEoo : IntegrableOn thetaCuspRegularSlopeCurvature (Ioo z.1 z.2) :=
        hE.1.mono_set Ioo_subset_Ioc_self
      have hbase : IntegrableOn (fun t : ℝ =>
          thetaCuspTuranCrossKernel m z.1 z.2 *
            thetaCuspRegularSlopeCurvature t) (Ioo z.1 z.2) :=
        hEoo.const_mul _
      rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioo] at hbase
      apply hbase.congr
      filter_upwards with t
      simp only [thetaCuspTuranFubiniIntegrand, thetaCuspTuranFubiniSet,
        Set.indicator, mem_setOf_eq, mem_Ioo]
      simp [hu]
    · have hzero : (fun y : ℝ => thetaCuspTuranFubiniIntegrand m (z, y)) =
          fun _ : ℝ => 0 := by
        funext t
        unfold thetaCuspTuranFubiniIntegrand
        rw [Set.indicator_of_notMem]
        intro h
        exact huv (h.2.1.trans h.2.2)
      rw [hzero]
      exact integrable_zero ℝ ℝ volume
  · apply hH.mono'
      (hmeas.norm.integral_prod_right')
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      with z hz
    rcases hz with ⟨hu, hv⟩
    change 0 < z.1 at hu
    change 0 < z.2 at hv
    by_cases huv : z.1 < z.2
    · have hnormPoint : (fun t : ℝ =>
          ‖thetaCuspTuranFubiniIntegrand m (z, t)‖) =
        (Ioo z.1 z.2).indicator (fun t : ℝ =>
          |thetaCuspTuranCrossKernel m z.1 z.2| *
            |thetaCuspRegularSlopeCurvature t|) := by
        funext t
        unfold thetaCuspTuranFubiniIntegrand
        by_cases ht : t ∈ Ioo z.1 z.2
        · have hmem : (z, t) ∈ thetaCuspTuranFubiniSet :=
            ⟨hu, ht.1, ht.2⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht,
            Real.norm_eq_abs, abs_mul]
        · have hnot : (z, t) ∉ thetaCuspTuranFubiniSet := by
            intro h
            exact ht ⟨h.2.1, h.2.2⟩
          rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem ht, norm_zero]
      rw [hnormPoint, MeasureTheory.integral_indicator measurableSet_Ioo,
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le huv.le]
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg huv.le
        (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))),
        intervalIntegral.integral_const_mul]
      have habs := intervalIntegral_abs_thetaCuspRegularSlopeCurvature_le
        hu huv.le
      have hmul := mul_le_mul_of_nonneg_left habs
        (abs_nonneg (thetaCuspTuranCrossKernel m z.1 z.2))
      exact hmul.trans
        (abs_thetaCuspTuranCrossKernel_mul_endpoint_le_profile hu hv huv.le)
    · have hzero : (fun y : ℝ => thetaCuspTuranFubiniIntegrand m (z, y)) =
          fun _ : ℝ => 0 := by
        funext t
        unfold thetaCuspTuranFubiniIntegrand
        rw [Set.indicator_of_notMem]
        intro h
        exact huv (h.2.1.trans h.2.2)
      rw [show (fun t : ℝ => ‖thetaCuspTuranFubiniIntegrand m (z, t)‖) =
          fun _ : ℝ => 0 by
        funext t
        rw [congrFun hzero t, norm_zero]]
      simp only [integral_zero, Real.norm_eq_abs, abs_zero]
      unfold H thetaCuspRegularFubiniProfile
      have hsu := thetaCuspSourceTerm_nonneg_of_pos hu 1
      have hsv := thetaCuspSourceTerm_nonneg_of_pos hv 1
      have hbrU : 0 ≤ |thetaCuspRegularSlopeQuotient z.1| +
          (1 + 2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|) := by
        positivity
      have hbrV : 0 ≤ |thetaCuspRegularSlopeQuotient z.2| +
          (1 + 2 * |thetaCuspRegularSlopeQuotient thetaCuspRegularCurvatureSeam|) := by
        positivity
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg hu.le _) hsu) hbrU)
          (mul_nonneg (mul_nonneg (pow_nonneg hv.le _) hsv) hbrV))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg hu.le _) hsu) hbrU)
          (mul_nonneg (mul_nonneg (pow_nonneg hv.le _) hsv) hbrV))

private def thetaCuspTuranUpperCone : Set (ℝ × ℝ) :=
  {z | z.1 < z.2}

private def thetaCuspRegularTuranPairIntegrand
    (m : ℕ) (z : ℝ × ℝ) : ℝ :=
  thetaCuspTuranCrossKernel m z.1 z.2 *
    (∫ t : ℝ in z.1..z.2, thetaCuspRegularSlopeCurvature t)

private theorem measurableSet_thetaCuspTuranUpperCone :
    MeasurableSet thetaCuspTuranUpperCone := by
  unfold thetaCuspTuranUpperCone
  measurability

private theorem integral_thetaCuspTuranFubiniIntegrand_section
    (m : ℕ) {u v : ℝ} (hu : 0 < u) :
    (∫ t : ℝ, thetaCuspTuranFubiniIntegrand m ((u, v), t)) =
      thetaCuspTuranUpperCone.indicator
        (thetaCuspRegularTuranPairIntegrand m) (u, v) := by
  by_cases huv : u < v
  · have hsection : (fun t : ℝ =>
        thetaCuspTuranFubiniIntegrand m ((u, v), t)) =
      (Ioo u v).indicator (fun t : ℝ =>
        thetaCuspTuranCrossKernel m u v *
          thetaCuspRegularSlopeCurvature t) := by
      funext t
      simp only [thetaCuspTuranFubiniIntegrand, thetaCuspTuranFubiniSet,
        Set.indicator, mem_setOf_eq, mem_Ioo]
      simp [hu]
    rw [hsection, MeasureTheory.integral_indicator measurableSet_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le huv.le,
      intervalIntegral.integral_const_mul]
    simp [thetaCuspTuranUpperCone, thetaCuspRegularTuranPairIntegrand, huv]
  · have hsection : (fun t : ℝ =>
        thetaCuspTuranFubiniIntegrand m ((u, v), t)) = fun _ : ℝ => 0 := by
      funext t
      unfold thetaCuspTuranFubiniIntegrand
      rw [Set.indicator_of_notMem]
      intro h
      exact huv (h.2.1.trans h.2.2)
    rw [hsection, integral_zero]
    rw [Set.indicator_of_notMem]
    exact huv

private theorem thetaCuspRegularTuranPairIntegrand_swap
    (m : ℕ) (z : ℝ × ℝ) :
    thetaCuspRegularTuranPairIntegrand m z.swap =
      thetaCuspRegularTuranPairIntegrand m z := by
  rcases z with ⟨u, v⟩
  simp only [Prod.swap_prod_mk]
  unfold thetaCuspRegularTuranPairIntegrand thetaCuspTuranCrossKernel
  rw [intervalIntegral.integral_symm]
  ring

private theorem thetaCuspRegularTuranPairIntegrand_eq_upper_add_swap
    (m : ℕ) (z : ℝ × ℝ) :
    thetaCuspRegularTuranPairIntegrand m z =
      thetaCuspTuranUpperCone.indicator
          (thetaCuspRegularTuranPairIntegrand m) z +
        (thetaCuspTuranUpperCone.indicator
          (thetaCuspRegularTuranPairIntegrand m)) z.swap := by
  rcases lt_trichotomy z.1 z.2 with h | h | h
  · have hmem : z ∈ thetaCuspTuranUpperCone := h
    have hnmem : z.swap ∉ thetaCuspTuranUpperCone := not_lt_of_ge h.le
    rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnmem, add_zero]
  · have hzero : thetaCuspRegularTuranPairIntegrand m z = 0 := by
      unfold thetaCuspRegularTuranPairIntegrand thetaCuspTuranCrossKernel
      rw [h]
      ring
    have hnmem : z ∉ thetaCuspTuranUpperCone := by simp [thetaCuspTuranUpperCone, h]
    have hswapnmem : z.swap ∉ thetaCuspTuranUpperCone := by
      simp [thetaCuspTuranUpperCone, h]
    rw [Set.indicator_of_notMem hnmem,
      Set.indicator_of_notMem hswapnmem, hzero, zero_add]
  · have hnmem : z ∉ thetaCuspTuranUpperCone := not_lt_of_ge h.le
    have hswapmem : z.swap ∈ thetaCuspTuranUpperCone := h
    rw [Set.indicator_of_notMem hnmem, zero_add,
      Set.indicator_of_mem hswapmem,
      thetaCuspRegularTuranPairIntegrand_swap]

private theorem two_mul_integral_thetaCuspTuranFubiniIntegrand_eq_regular
    {m : ℕ} (hm : 1 ≤ m) :
    2 * (∫ z : ℝ × ℝ,
        (∫ t : ℝ, thetaCuspTuranFubiniIntegrand m (z, t))
          ∂((volume.prod volume).restrict
            (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) =
      thetaCuspRegularSlopeCurvatureTuranIntegralIndex (2 * m - 1) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let μuv : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  let U : ℝ × ℝ → ℝ :=
    thetaCuspTuranUpperCone.indicator
      (thetaCuspRegularTuranPairIntegrand m)
  let J : ℝ × ℝ → ℝ := thetaCuspRegularTuranPairIntegrand m
  have hF := integrable_thetaCuspTuranFubiniIntegrand hm
  have hUuv : Integrable U μuv := by
    have hinner := hF.integral_prod_left
    apply hinner.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      with z hz
    exact integral_thetaCuspTuranFubiniIntegrand_section m hz.1
  have hU : Integrable U (μ.prod μ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hUuv
  have hUswap : Integrable (fun z : ℝ × ℝ => U z.swap) (μ.prod μ) := hU.swap
  have hJ : Integrable J (μ.prod μ) := by
    apply (hU.add hUswap).congr
    filter_upwards with z
    exact (thetaCuspRegularTuranPairIntegrand_eq_upper_add_swap m z).symm
  have hswap : (∫ z : ℝ × ℝ, U z.swap ∂μ.prod μ) =
      ∫ z : ℝ × ℝ, U z ∂μ.prod μ := by
    simpa only [μ] using
      (MeasureTheory.integral_prod_swap (μ := μ) (ν := μ) U)
  have hfull : (∫ z : ℝ × ℝ, J z ∂μ.prod μ) =
      2 * ∫ z : ℝ × ℝ, U z ∂μ.prod μ := by
    have hpoint : J = U + fun z : ℝ × ℝ => U z.swap := by
      funext z
      exact thetaCuspRegularTuranPairIntegrand_eq_upper_add_swap m z
    rw [hpoint]
    change (∫ z : ℝ × ℝ, U z + U z.swap ∂μ.prod μ) = _
    rw [MeasureTheory.integral_add hU hUswap, hswap]
    ring
  have hJ' : Integrable (Function.uncurry
      (fun u : ℝ => fun v : ℝ => J (u, v))) (μ.prod μ) := by
    change Integrable J (μ.prod μ)
    exact hJ
  have hiter := MeasureTheory.integral_integral hJ'
  have hk : 2 * m - 1 + 1 = 2 * m := by omega
  change 2 * (∫ z : ℝ × ℝ, ∫ t : ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂volume ∂μuv) = _
  have hinnerEq : (∫ z : ℝ × ℝ, ∫ t : ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂volume ∂μuv) =
      ∫ z : ℝ × ℝ, U z ∂μ.prod μ := by
    rw [MeasureTheory.Measure.prod_restrict]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      with z hz
    exact integral_thetaCuspTuranFubiniIntegrand_section m hz.1
  rw [hinnerEq, ← hfull, ← hiter]
  unfold thetaCuspRegularSlopeCurvatureTuranIntegralIndex J
    thetaCuspRegularTuranPairIntegrand thetaCuspTuranCrossKernel μ
    thetaCuspTuranKernelIndex
  rw [hk]

private theorem integral_pair_thetaCuspTuranFubiniIntegrand_eq_crossing
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ × ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t)
        ∂((volume.prod volume).restrict
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) =
      thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t := by
  let p : ℕ := 2 * m
  let fp : ℝ → ℝ := thetaCuspMomentDensity p
  let fp2 : ℝ → ℝ := thetaCuspMomentDensity (p + 2)
  let A : Set (ℝ × ℝ) := Ioo (0 : ℝ) t ×ˢ Ioi t
  let base : ℝ × ℝ → ℝ := fun z =>
    thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossKernel m z.1 z.2
  have hfpLow : IntegrableOn fp (Ioo (0 : ℝ) t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi p).mono_set
      (by intro x hx; exact hx.1)
  have hfp2Low : IntegrableOn fp2 (Ioo (0 : ℝ) t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (p + 2)).mono_set
      (by intro x hx; exact hx.1)
  have hfpUp : IntegrableOn fp (Ioi t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi p).mono_set
      (by intro x hx; exact ht.trans hx)
  have hfp2Up : IntegrableOn fp2 (Ioi t) :=
    (integrableOn_natPow_mul_thetaCuspSourceTerm_Ioi (p + 2)).mono_set
      (by intro x hx; exact ht.trans hx)
  have hsep : Integrable (fun z : ℝ × ℝ =>
      fp z.1 * fp2 z.2 - fp2 z.1 * fp z.2)
      ((volume.restrict (Ioo (0 : ℝ) t)).prod
        (volume.restrict (Ioi t))) :=
    (hfpLow.mul_prod hfp2Up).sub (hfp2Low.mul_prod hfpUp)
  have hcross : Integrable (fun z : ℝ × ℝ =>
      thetaCuspTuranCrossKernel m z.1 z.2)
      ((volume.restrict (Ioo (0 : ℝ) t)).prod
        (volume.restrict (Ioi t))) := by
    apply hsep.congr
    filter_upwards with z
    unfold thetaCuspTuranCrossKernel fp fp2 thetaCuspMomentDensity p
    rw [show z.1 ^ (2 * m + 2) = z.1 ^ (2 * m) * z.1 ^ (2 : ℕ) by rw [pow_add],
      show z.2 ^ (2 * m + 2) = z.2 ^ (2 * m) * z.2 ^ (2 : ℕ) by rw [pow_add]]
    ring
  have hbase : Integrable base
      ((volume.restrict (Ioo (0 : ℝ) t)).prod
        (volume.restrict (Ioi t))) := hcross.const_mul _
  have hbase' : Integrable (Function.uncurry
      (fun u : ℝ => fun v : ℝ => base (u, v)))
      ((volume.restrict (Ioo (0 : ℝ) t)).prod
        (volume.restrict (Ioi t))) := by
    change Integrable base
      ((volume.restrict (Ioo (0 : ℝ) t)).prod
        (volume.restrict (Ioi t)))
    exact hbase
  have hiter := MeasureTheory.integral_integral hbase'
  rw [MeasureTheory.Measure.prod_restrict] at hiter
  have hactive : (fun z : ℝ × ℝ =>
      thetaCuspTuranFubiniIntegrand m (z, t)) = A.indicator base := by
    funext z
    simp only [thetaCuspTuranFubiniIntegrand, thetaCuspTuranFubiniSet,
      A, base, Set.indicator, mem_prod, mem_Ioo, mem_Ioi, mem_setOf_eq]
    by_cases hz : 0 < z.1 ∧ z.1 < t ∧ t < z.2
    · rw [if_pos hz, if_pos ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩]
      ring
    · rw [if_neg hz]
      have hnot : ¬((0 < z.1 ∧ z.1 < t) ∧ t < z.2) := by
        simpa only [and_assoc] using hz
      rw [if_neg hnot]
  have hpositiveIndicator :
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
          (fun z : ℝ × ℝ => thetaCuspTuranFubiniIntegrand m (z, t)) =
        fun z : ℝ × ℝ => thetaCuspTuranFubiniIntegrand m (z, t) := by
    funext z
    by_cases hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      unfold thetaCuspTuranFubiniIntegrand
      rw [Set.indicator_of_notMem]
      intro h
      exact hz ⟨h.1, ht.trans h.2.2⟩
  calc
    (∫ z : ℝ × ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t)
        ∂((volume.prod volume).restrict
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) =
        ∫ z : ℝ × ℝ, thetaCuspTuranFubiniIntegrand m (z, t)
          ∂volume.prod volume := by
      rw [← MeasureTheory.integral_indicator
        (measurableSet_Ioi.prod measurableSet_Ioi), hpositiveIndicator]
    _ = ∫ z : ℝ × ℝ in A, base z ∂volume.prod volume := by
      rw [hactive, MeasureTheory.integral_indicator
        (show MeasurableSet A by
          exact measurableSet_Ioo.prod measurableSet_Ioi)]
    _ = ∫ u : ℝ in Ioo 0 t,
        ∫ v : ℝ in Ioi t, base (u, v) := hiter.symm
    _ = thetaCuspRegularSlopeCurvature t *
        (∫ u : ℝ in Ioo 0 t,
          ∫ v : ℝ in Ioi t, thetaCuspTuranCrossKernel m u v) := by
      unfold base
      simp_rw [MeasureTheory.integral_const_mul]
    _ = thetaCuspRegularSlopeCurvature t *
        (∫ u : ℝ in Ioc 0 t,
          ∫ v : ℝ in Ioi t, thetaCuspTuranCrossKernel m u v) := by
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      unfold thetaCuspTuranCrossingIntegral thetaCuspTuranCrossKernel
      rfl

private theorem integral_thetaCuspTuranFubiniIntegrand_swap_eq_crossing
    (m : ℕ) :
    (∫ t : ℝ,
      ∫ z : ℝ × ℝ,
        thetaCuspTuranFubiniIntegrand m (z, t)
          ∂((volume.prod volume).restrict
            (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) =
      ∫ t : ℝ in Ioi 0,
        thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 < t
  · simp only [Set.indicator, mem_Ioi]
    rw [if_pos ht,
      integral_pair_thetaCuspTuranFubiniIntegrand_eq_crossing m ht]
  · simp only [Set.indicator, mem_Ioi]
    rw [if_neg ht]
    apply integral_eq_zero_of_ae
    filter_upwards with z
    change thetaCuspTuranFubiniIntegrand m (z, t) = 0
    unfold thetaCuspTuranFubiniIntegrand
    rw [Set.indicator_of_notMem]
    intro h
    exact ht (h.1.trans h.2.1)

theorem thetaCuspRegularCurvatureContribution_eq_crossingIntegral
    {m : ℕ} (hm : 1 ≤ m) :
    thetaCuspRegularCurvatureContribution m =
      1 / ((2 * m + 1 : ℕ) : ℝ) *
        ∫ t : ℝ in Ioi 0,
          thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t := by
  let μuv : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  have hF := integrable_thetaCuspTuranFubiniIntegrand hm
  have hF' : Integrable (Function.uncurry
      (fun z : ℝ × ℝ => fun t : ℝ =>
        thetaCuspTuranFubiniIntegrand m (z, t))) (μuv.prod volume) := by
    change Integrable (thetaCuspTuranFubiniIntegrand m) (μuv.prod volume)
    exact hF
  have hswap := MeasureTheory.integral_integral_swap hF'
  have hleft := two_mul_integral_thetaCuspTuranFubiniIntegrand_eq_regular hm
  have hright := integral_thetaCuspTuranFubiniIntegrand_swap_eq_crossing m
  change (∫ z : ℝ × ℝ, ∫ t : ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂volume ∂μuv) =
    (∫ t : ℝ, ∫ z : ℝ × ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂μuv ∂volume) at hswap
  change 2 * (∫ z : ℝ × ℝ, ∫ t : ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂volume ∂μuv) =
    thetaCuspRegularSlopeCurvatureTuranIntegralIndex (2 * m - 1) at hleft
  change (∫ t : ℝ, ∫ z : ℝ × ℝ,
      thetaCuspTuranFubiniIntegrand m (z, t) ∂μuv ∂volume) =
    ∫ t : ℝ in Ioi 0,
      thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t at hright
  unfold thetaCuspRegularCurvatureContribution
  have hden : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [← hleft, hswap, hright]
  field_simp [hden.ne']

private theorem integrableOn_thetaCuspRegularSlopeCurvature_mul_crossingIntegral
    {m : ℕ} (hm : 1 ≤ m) :
    IntegrableOn (fun t : ℝ =>
      thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t)
      (Ioi 0) := by
  let μuv : Measure (ℝ × ℝ) :=
    (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  let g : ℝ → ℝ := fun t =>
    thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t
  have hF := integrable_thetaCuspTuranFubiniIntegrand hm
  have hF' : Integrable (Function.uncurry
      (fun z : ℝ × ℝ => fun t : ℝ =>
        thetaCuspTuranFubiniIntegrand m (z, t))) (μuv.prod volume) := by
    change Integrable (thetaCuspTuranFubiniIntegrand m) (μuv.prod volume)
    exact hF
  have hout : Integrable (fun t : ℝ =>
      ∫ z : ℝ × ℝ, thetaCuspTuranFubiniIntegrand m (z, t) ∂μuv) volume :=
    hF'.integral_prod_right
  have hind : Integrable ((Ioi (0 : ℝ)).indicator g) volume := by
    apply hout.congr
    filter_upwards with t
    by_cases ht : 0 < t
    · simp only [Set.indicator, mem_Ioi]
      rw [if_pos ht]
      exact integral_pair_thetaCuspTuranFubiniIntegrand_eq_crossing m ht
    · simp only [Set.indicator, mem_Ioi]
      rw [if_neg ht]
      apply integral_eq_zero_of_ae
      filter_upwards with z
      change thetaCuspTuranFubiniIntegrand m (z, t) = 0
      unfold thetaCuspTuranFubiniIntegrand
      rw [Set.indicator_of_notMem]
      intro h
      exact ht (h.1.trans h.2.1)
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).1 hind

theorem thetaCuspRegularCrossingIntegrand_nonneg_after_seam
    (m : ℕ) {t : ℝ} (ht : thetaCuspRegularCurvatureSeam ≤ t) :
    0 ≤ thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t := by
  have ht0 : 0 < t := thetaCuspRegularCurvatureSeam_spec.1.trans_le ht
  have hcurv : 0 ≤ thetaCuspRegularSlopeCurvature t := by
    rcases ht.eq_or_lt with h | h
    · rw [← h, thetaCuspRegularSlopeCurvature_signLaw.2.1]
    · exact (thetaCuspRegularSlopeCurvature_signLaw.2.2 t h).le
  have hcross : 0 < thetaCuspTuranCrossingIntegral m t := by
    rw [thetaCuspTuranCrossingIntegral_eq_window m ht0]
    exact thetaCuspTuranCrossingWindow_pos m ht0
  exact mul_nonneg hcurv hcross.le

theorem thetaCuspRegularCrossingIntegrand_negated_nonneg_before_seam
    (m : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) thetaCuspRegularCurvatureSeam) :
    0 ≤ (-thetaCuspRegularSlopeCurvature t) *
      thetaCuspTuranCrossingIntegral m t := by
  rcases ht.2.eq_or_lt with h | h
  · rw [h, thetaCuspRegularSlopeCurvature_signLaw.2.1, neg_zero, zero_mul]
  · have hcurv := thetaCuspRegularSlopeCurvature_signLaw.1 t ht.1 h
    have hcross : 0 < thetaCuspTuranCrossingIntegral m t := by
      rw [thetaCuspTuranCrossingIntegral_eq_window m ht.1]
      exact thetaCuspTuranCrossingWindow_pos m ht.1
    exact mul_nonneg (neg_nonneg.mpr hcurv.le)
      hcross.le

theorem thetaCuspRegularCurvatureContribution_seam_balance
    {m : ℕ} (hm : 1 ≤ m) :
    ((2 * m + 1 : ℕ) : ℝ) * thetaCuspRegularCurvatureContribution m =
      (∫ t : ℝ in Ioi thetaCuspRegularCurvatureSeam,
        thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t) -
      ∫ t : ℝ in Ioc 0 thetaCuspRegularCurvatureSeam,
        (-thetaCuspRegularSlopeCurvature t) * thetaCuspTuranCrossingIntegral m t := by
  let g : ℝ → ℝ := fun t =>
    thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t
  let h : ℝ → ℝ := fun t =>
    (-thetaCuspRegularSlopeCurvature t) * thetaCuspTuranCrossingIntegral m t
  let c : ℝ := thetaCuspRegularCurvatureSeam
  have hc : 0 < c := thetaCuspRegularCurvatureSeam_spec.1
  have hg : IntegrableOn g (Ioi 0) :=
    integrableOn_thetaCuspRegularSlopeCurvature_mul_crossingIntegral hm
  have hgL : IntegrableOn g (Ioc 0 c) :=
    hg.mono_set (by intro t ht; exact ht.1)
  have hgR : IntegrableOn g (Ioi c) :=
    hg.mono_set (by intro t ht; exact hc.trans ht)
  have hdis : Disjoint (Ioc (0 : ℝ) c) (Ioi c) := by
    rw [Set.disjoint_left]
    intro t htL htR
    exact (not_lt_of_ge htL.2) htR
  have hunion : Ioc (0 : ℝ) c ∪ Ioi c = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact hc.trans ht
    · intro ht
      by_cases htc : t ≤ c
      · exact Or.inl ⟨ht, htc⟩
      · exact Or.inr (lt_of_not_ge htc)
  have hsplit := MeasureTheory.setIntegral_union hdis measurableSet_Ioi hgL hgR
  rw [hunion] at hsplit
  have hL : (∫ t : ℝ in Ioc 0 c, g t) =
      -(∫ t : ℝ in Ioc 0 c, h t) := by
    calc
      (∫ t : ℝ in Ioc 0 c, g t) = ∫ t : ℝ in Ioc 0 c, -h t := by
        apply integral_congr_ae
        filter_upwards with t
        unfold g h
        ring
      _ = _ := by
        exact MeasureTheory.integral_neg
          (μ := volume.restrict (Ioc 0 c)) h
  have hrepr := thetaCuspRegularCurvatureContribution_eq_crossingIntegral hm
  have hden : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [hrepr]
  field_simp [hden.ne']
  have hresult : (∫ t : ℝ in Ioi 0, g t) =
      (∫ t : ℝ in Ioi c, g t) - ∫ t : ℝ in Ioc 0 c, h t := by
    rw [hsplit, hL]
    ring
  simpa only [g, h, c, neg_mul] using hresult

theorem thetaCuspRegularCurvatureContribution_seam_masses_nonneg
    (m : ℕ) :
    0 ≤ (∫ t : ℝ in Ioi thetaCuspRegularCurvatureSeam,
      thetaCuspRegularSlopeCurvature t * thetaCuspTuranCrossingIntegral m t) ∧
    0 ≤ ∫ t : ℝ in Ioc 0 thetaCuspRegularCurvatureSeam,
      (-thetaCuspRegularSlopeCurvature t) * thetaCuspTuranCrossingIntegral m t := by
  constructor
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact thetaCuspRegularCrossingIntegrand_nonneg_after_seam m ht.le
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact thetaCuspRegularCrossingIntegrand_negated_nonneg_before_seam m ht


end RHTower
