import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLogScheduleCriterion

/-!
# Boundary exterior obstruction to the base-two logarithmic schedule

At `s = 6/11`, the Cayley coordinate is `-8/3`.  The negative-half central-binomial weights grow
at least by two after their first step.  Hence the base-two logarithmic Cayley schedule makes the
pole-factor approximants grow at least linearly in the Dirichlet cutoff.  Local boundedness of the
scheduled products would force `N * ‖D_N(6/11)‖` to remain bounded, contradicting the exact prime
jump `(1/2) p^(-6/11)`.

Thus escaping one fixed exterior-point ceiling is insufficient.  A viable logarithmic schedule
must be slow enough uniformly as the test point approaches the boundary `Re s = 1/2`.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

def boundaryExteriorWeight (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (2 / 3 : ℝ) ^ k

def boundaryNegHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * boundaryExteriorWeight k

def boundaryHalfExteriorTerm (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-8 / 3 : ℝ) ^ k

def boundaryHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, boundaryHalfExteriorTerm k

@[simp] theorem boundaryExteriorWeight_zero : boundaryExteriorWeight 0 = 1 := by
  simp [boundaryExteriorWeight]

theorem boundaryExteriorWeight_pos (k : ℕ) : 0 < boundaryExteriorWeight k := by
  unfold boundaryExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k) (pow_pos (by norm_num) k)

theorem boundaryExteriorWeight_growth (k : ℕ) :
    (5 / 4 : ℝ) * boundaryExteriorWeight k ≤ boundaryExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [boundaryExteriorWeight, boundaryExteriorWeight, pow_succ]
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hCgrowth : 2 * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) := by
    nlinarith
  have hbase : (5 / 4 : ℝ) * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) * (2 / 3 : ℝ) := by
    nlinarith
  calc
    (5 / 4 : ℝ) * ((Nat.centralBinom k : ℝ) * (2 / 3 : ℝ) ^ k) =
        ((5 / 4 : ℝ) * (Nat.centralBinom k : ℝ)) * (2 / 3 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (2 / 3 : ℝ)) * (2 / 3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg (by norm_num) k)
    _ = (Nat.centralBinom (k + 1) : ℝ) * ((2 / 3 : ℝ) ^ k * (2 / 3 : ℝ)) := by
      ring

theorem boundaryExteriorWeight_growth_two {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) * boundaryExteriorWeight k ≤ boundaryExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [boundaryExteriorWeight, boundaryExteriorWeight, pow_succ]
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hbase : (2 : ℝ) * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) * (2 / 3 : ℝ) := by
    nlinarith
  calc
    (2 : ℝ) * ((Nat.centralBinom k : ℝ) * (2 / 3 : ℝ) ^ k) =
        (2 * (Nat.centralBinom k : ℝ)) * (2 / 3 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (2 / 3 : ℝ)) * (2 / 3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg (by norm_num) k)
    _ = (Nat.centralBinom (k + 1) : ℝ) * ((2 / 3 : ℝ) ^ k * (2 / 3 : ℝ)) := by
      ring

theorem boundaryExteriorWeight_ge_two_pow {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) ≤ boundaryExteriorWeight k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [boundaryExteriorWeight, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
      change (2 : ℝ) ^ k ≤ boundaryExteriorWeight (k + 1)
      calc
        (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        _ ≤ boundaryExteriorWeight k * 2 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = 2 * boundaryExteriorWeight k := by ring
        _ ≤ boundaryExteriorWeight (k + 1) := boundaryExteriorWeight_growth_two hk

theorem boundaryNegHalfExteriorSum_bounds (m : ℕ) :
    ((boundaryExteriorWeight (2 * m)) / 5 ≤ boundaryNegHalfExteriorSum (2 * m + 1) ∧
      boundaryNegHalfExteriorSum (2 * m + 1) ≤ boundaryExteriorWeight (2 * m)) ∧
    (-boundaryExteriorWeight (2 * m + 1) ≤ boundaryNegHalfExteriorSum (2 * m + 2) ∧
      boundaryNegHalfExteriorSum (2 * m + 2) ≤
        -boundaryExteriorWeight (2 * m + 1) / 5) := by
  induction m with
  | zero =>
      norm_num [boundaryNegHalfExteriorSum, boundaryExteriorWeight, Nat.centralBinom,
        Nat.choose, Finset.sum_range_succ]
  | succ m ih =>
      rcases ih with ⟨hodd, heven⟩
      have hg1 := boundaryExteriorWeight_growth (2 * m + 1)
      have hg2 := boundaryExteriorWeight_growth (2 * m + 2)
      have hp1 := boundaryExteriorWeight_pos (2 * m + 1)
      have hp2 := boundaryExteriorWeight_pos (2 * m + 2)
      have hp3 := boundaryExteriorWeight_pos (2 * m + 3)
      have hsodd : boundaryNegHalfExteriorSum (2 * (m + 1) + 1) =
          boundaryNegHalfExteriorSum (2 * m + 2) + boundaryExteriorWeight (2 * m + 2) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          boundaryNegHalfExteriorSum, Finset.sum_range_succ]
        have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
          rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
          norm_num
        rw [he, one_mul]
        rfl
      have hseven : boundaryNegHalfExteriorSum (2 * (m + 1) + 2) =
          boundaryNegHalfExteriorSum (2 * (m + 1) + 1) -
            boundaryExteriorWeight (2 * m + 3) := by
        rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
          boundaryNegHalfExteriorSum, Finset.sum_range_succ]
        have ho : (-1 : ℝ) ^ (2 * (m + 1) + 1) = -1 := by
          rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl, pow_add, pow_mul]
          norm_num
        rw [ho, neg_one_mul]
        unfold boundaryNegHalfExteriorSum
        congr 2
      have hnewodd :
          boundaryExteriorWeight (2 * (m + 1)) / 5 ≤
              boundaryNegHalfExteriorSum (2 * (m + 1) + 1) ∧
            boundaryNegHalfExteriorSum (2 * (m + 1) + 1) ≤
              boundaryExteriorWeight (2 * (m + 1)) := by
        rw [hsodd]
        simp only [Nat.mul_add, Nat.mul_one]
        constructor <;> linarith
      have hneweven :
          -boundaryExteriorWeight (2 * (m + 1) + 1) ≤
              boundaryNegHalfExteriorSum (2 * (m + 1) + 2) ∧
            boundaryNegHalfExteriorSum (2 * (m + 1) + 2) ≤
              -boundaryExteriorWeight (2 * (m + 1) + 1) / 5 := by
        rw [hseven]
        rcases hnewodd with ⟨hnewoddlo, hnewoddhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hnewoddlo hnewoddhi ⊢
        constructor <;> linarith
      exact ⟨hnewodd, hneweven⟩


theorem boundaryHalfExteriorTerm_neg {k : ℕ} (hk : 1 ≤ k) :
    boundaryHalfExteriorTerm k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [boundaryHalfExteriorTerm]
  | succ k hk ih =>
      have hrec := choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : boundaryHalfExteriorTerm (k + 1) =
          boundaryHalfExteriorTerm k * ((8 / 3 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold boundaryHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih (div_pos (mul_pos (by norm_num) hkpos) hk1)

theorem boundaryHalfExteriorSum_le_neg_quarter {N : ℕ} (hN : 2 ≤ N) :
    boundaryHalfExteriorSum N ≤ -1 / 4 := by
  induction N, hN using Nat.le_induction with
  | base =>
      norm_num [boundaryHalfExteriorSum, boundaryHalfExteriorTerm,
        Ring.choose_zero_right, Ring.choose_one_right, Finset.sum_range_succ]
  | succ N hN ih =>
      rw [boundaryHalfExteriorSum, Finset.sum_range_succ, ← boundaryHalfExteriorSum]
      calc
        boundaryHalfExteriorSum N + boundaryHalfExteriorTerm N ≤ boundaryHalfExteriorSum N :=
          add_le_of_nonpos_right
            (le_of_lt (boundaryHalfExteriorTerm_neg (le_trans one_le_two hN)))
        _ ≤ -1 / 4 := ih

private theorem binomialPartialSum_eq_sum_choose_complex (a z : ℂ) (N : ℕ) :
    (binomialSeries ℂ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp


private theorem boundary_binomialPartialSum_eq_sum_choose_real (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_boundary_binomialPartialSum_ofReal (a z : ℝ) (N : ℕ) :
    (binomialSeries ℂ (a : ℂ)).partialSum N (z : ℂ) =
      ((binomialSeries ℝ a).partialSum N z : ℂ) := by
  rw [binomialPartialSum_eq_sum_choose_complex,
    boundary_binomialPartialSum_eq_sum_choose_real]
  push_cast
  rfl

theorem complex_boundaryHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-8 / 3 : ℂ) =
      (boundaryHalfExteriorSum N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show (-8 / 3 : ℂ) = ((-8 / 3 : ℝ) : ℂ) by norm_num,
    complex_boundary_binomialPartialSum_ofReal,
    boundary_binomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_boundaryNegHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (8 / 3 : ℂ) =
      (boundaryNegHalfExteriorSum N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (8 / 3 : ℂ) = ((8 / 3 : ℝ) : ℂ) by norm_num,
    complex_boundary_binomialPartialSum_ofReal,
    boundary_binomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold boundaryNegHalfExteriorSum boundaryExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * (8 / 3 : ℝ) ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * (8 / 3 : ℝ) ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * (8 / 3 : ℝ)) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k * (2 / 3 : ℝ) ^ k := by
      norm_num
  ring

def boundaryExteriorPoint : ℂ := (6 / 11 : ℂ)

@[simp] theorem poleFactorCayley_boundaryExteriorPoint :
    poleFactorCayley boundaryExteriorPoint = (-8 / 3 : ℂ) := by
  norm_num [boundaryExteriorPoint, poleFactorCayley,
    GaloisForLFunctions.HTGeometry.cayleyRight]

theorem boundaryExteriorPoint_mem_rightHalf : boundaryExteriorPoint ∈ rightHalf := by
  rw [mem_rightHalf]
  norm_num [boundaryExteriorPoint]

theorem norm_boundaryHalfExteriorPartialSum_ge_quarter {N : ℕ} (hN : 2 ≤ N) :
    (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-8 / 3 : ℂ)‖ := by
  rw [complex_boundaryHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hsum := boundaryHalfExteriorSum_le_neg_quarter hN
  rw [abs_of_nonpos (le_trans hsum (by norm_num))]
  linarith

theorem norm_boundaryNegHalfExteriorPartialSum_odd_ge (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (2 * m - 1) / 5 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 1) (8 / 3 : ℂ)‖ := by
  rw [complex_boundaryNegHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (boundaryNegHalfExteriorSum_bounds m).1
  have hgeom := boundaryExteriorWeight_ge_two_pow (show 1 ≤ 2 * m by omega)
  have hnonneg : 0 ≤ boundaryNegHalfExteriorSum (2 * m + 1) := by
    linarith [boundaryExteriorWeight_pos (2 * m)]
  rw [abs_of_nonneg hnonneg]
  exact le_trans (div_le_div_of_nonneg_right hgeom (by norm_num)) hbounds.1

theorem norm_boundaryNegHalfExteriorPartialSum_even_ge (m : ℕ) :
    (2 : ℝ) ^ (2 * m) / 5 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 2) (8 / 3 : ℂ)‖ := by
  rw [complex_boundaryNegHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (boundaryNegHalfExteriorSum_bounds m).2
  have hgeom := boundaryExteriorWeight_ge_two_pow (show 1 ≤ 2 * m + 1 by omega)
  have hnonpos : boundaryNegHalfExteriorSum (2 * m + 2) ≤ 0 := by
    linarith [boundaryExteriorWeight_pos (2 * m + 1)]
  rw [abs_of_nonpos hnonpos]
  have hweight : (2 : ℝ) ^ (2 * m) / 5 ≤
      boundaryExteriorWeight (2 * m + 1) / 5 :=
    div_le_div_of_nonneg_right hgeom (by norm_num)
  linarith [hbounds.2]

theorem norm_poleFactorSqrtApprox_boundaryExteriorPoint_odd_ge
    (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (2 * m - 1) / 20 ≤
      ‖poleFactorSqrtApprox (2 * m + 1) boundaryExteriorPoint‖ := by
  have hhalf := norm_boundaryHalfExteriorPartialSum_ge_quarter
    (show 2 ≤ 2 * m + 1 by omega)
  have hneg := norm_boundaryNegHalfExteriorPartialSum_odd_ge m hm
  have hhalf' : (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum (2 * m + 1) (-(8 / 3) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (2 : ℝ) ^ (2 * m - 1) / 5 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 1) (8 / 3 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_boundaryExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul]
  calc
    (2 : ℝ) ^ (2 * m - 1) / 20 =
        (1 / 4 : ℝ) * ((2 : ℝ) ^ (2 * m - 1) / 5) := by ring
    _ ≤ _ := mul_le_mul hhalf' hneg' (by positivity) (by positivity)

theorem norm_poleFactorSqrtApprox_boundaryExteriorPoint_even_ge (m : ℕ) :
    (2 : ℝ) ^ (2 * m) / 20 ≤
      ‖poleFactorSqrtApprox (2 * m + 2) boundaryExteriorPoint‖ := by
  have hhalf := norm_boundaryHalfExteriorPartialSum_ge_quarter
    (show 2 ≤ 2 * m + 2 by omega)
  have hneg := norm_boundaryNegHalfExteriorPartialSum_even_ge m
  have hhalf' : (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum (2 * m + 2) (-(8 / 3) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (2 : ℝ) ^ (2 * m) / 5 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 2) (8 / 3 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_boundaryExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul]
  calc
    (2 : ℝ) ^ (2 * m) / 20 =
        (1 / 4 : ℝ) * ((2 : ℝ) ^ (2 * m) / 5) := by ring
    _ ≤ _ := mul_le_mul hhalf' hneg' (by positivity) (by positivity)

theorem norm_poleFactorSqrtApprox_boundaryExteriorPoint_geometric
    {N : ℕ} (hN : 3 ≤ N) :
    (2 : ℝ) ^ (N - 2) / 20 ≤
      ‖poleFactorSqrtApprox N boundaryExteriorPoint‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    rw [show 2 * (k + 1) - 2 = 2 * k by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega]
    exact norm_poleFactorSqrtApprox_boundaryExteriorPoint_even_ge k
  · have hm1 : 1 ≤ m := by omega
    have hexp : 2 * m + 1 - 2 = 2 * m - 1 := by omega
    rw [hexp]
    exact norm_poleFactorSqrtApprox_boundaryExteriorPoint_odd_ge m hm1

theorem norm_logarithmicCayleyPoleFactor_boundaryExteriorPoint_ge_linear (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) / 20 ≤
      ‖poleFactorSqrtApprox (logarithmicCayleySchedule N) boundaryExteriorPoint‖ := by
  have hg := norm_poleFactorSqrtApprox_boundaryExteriorPoint_geometric
    (logarithmicCayleySchedule_ge_three N)
  have hdegree : logarithmicCayleySchedule N - 2 = (Nat.log 2 (N + 1)).succ := by
    simp [logarithmicCayleySchedule]
  rw [hdegree] at hg
  have hnat := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 1)
  have hreal : ((N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (N + 1)).succ := by
    exact_mod_cast hnat.le
  exact le_trans (div_le_div_of_nonneg_right hreal (by norm_num)) hg

theorem norm_squarefreeConvolutionHalf_term_prime_boundaryExteriorPoint
    (p : ℕ) (hp : p.Prime) :
    ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ =
      (1 / 2 : ℝ) / (p : ℝ) ^ (6 / 11 : ℝ) := by
  rw [LSeries.norm_term_eq, if_neg hp.ne_zero,
    squarefreeConvolutionHalf_apply_prime hp]
  norm_num [boundaryExteriorPoint]

theorem prime_mul_norm_term_boundaryExteriorPoint
    (p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ =
      (1 / 2 : ℝ) * (p : ℝ) ^ (5 / 11 : ℝ) := by
  rw [norm_squarefreeConvolutionHalf_term_prime_boundaryExteriorPoint p hp]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    (p : ℝ) * ((1 / 2 : ℝ) / (p : ℝ) ^ (6 / 11 : ℝ)) =
        (1 / 2 : ℝ) * ((p : ℝ) ^ (1 : ℝ) / (p : ℝ) ^ (6 / 11 : ℝ)) := by
      rw [Real.rpow_one]
      ring
    _ = (1 / 2 : ℝ) * (p : ℝ) ^ ((1 : ℝ) - (6 / 11 : ℝ)) := by
      rw [Real.rpow_sub hp0]
    _ = (1 / 2 : ℝ) * (p : ℝ) ^ (5 / 11 : ℝ) := by norm_num

theorem not_logarithmicCayleySchedule_locallyBounded :
    ¬ PoleClearedFirstTraceScheduledLocallyBounded logarithmicCayleySchedule := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 boundaryExteriorPoint hcenter)
  let K : ℝ := 20 * C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpartial (N : ℕ) :
      ((N + 1 : ℕ) : ℝ) *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ K := by
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hC N boundaryExteriorPoint hcenter
    have hprod :
        ‖poleFactorSqrtApprox (logarithmicCayleySchedule N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
          C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ := by
      rw [poleClearedFirstTraceScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hfactor := norm_logarithmicCayleyPoleFactor_boundaryExteriorPoint_ge_linear N
    have hscaled :
        (((N + 1 : ℕ) : ℝ) / 20) *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
          C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      le_trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)) hprod
    dsimp [K]
    nlinarith
  have htermUpper (p : ℕ) :
      (p : ℝ) * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
        2 * K := by
    have hsucc := squarefreeHalfDirichletPartialSum_succ p boundaryExteriorPoint
    have htermEq :
        LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p =
          squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint -
            squarefreeHalfDirichletPartialSum p boundaryExteriorPoint := by
      rw [hsucc]
      ring
    have htri :
        ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
          ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
            ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ := by
      rw [htermEq]
      exact norm_sub_le _ _
    have hpnext :
        (p : ℝ) * ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ ≤ K := by
      have hpcast : (p : ℝ) ≤ ((p + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : p ≤ p + 2)
      exact le_trans (mul_le_mul_of_nonneg_right hpcast (norm_nonneg _)) (hpartial (p + 1))
    have hpthis :
        (p : ℝ) * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ ≤ K := by
      have hpcast : (p : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ p
      exact le_trans (mul_le_mul_of_nonneg_right hpcast (norm_nonneg _)) (hpartial p)
    calc
      (p : ℝ) * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
          (p : ℝ) *
            (‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
              ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖) :=
        mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg p)
      _ = (p : ℝ) * ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
          (p : ℝ) * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ := by ring
      _ ≤ K + K := add_le_add hpnext hpthis
      _ = 2 * K := by ring
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (5 / 11 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hdiverge : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) ^ (5 / 11 : ℝ))
      atTop atTop := hpower.const_mul_atTop (by norm_num)
  have heventually : ∀ᶠ n : ℕ in atTop,
      2 * K < (1 / 2 : ℝ) * (n : ℝ) ^ (5 / 11 : ℝ) :=
    hdiverge.eventually_gt_atTop (2 * K)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hlarge := hN p hpN
  have heq := prime_mul_norm_term_boundaryExteriorPoint p hp
  have hupper := htermUpper p
  rw [heq] at hupper
  linarith


end

end RHTower
