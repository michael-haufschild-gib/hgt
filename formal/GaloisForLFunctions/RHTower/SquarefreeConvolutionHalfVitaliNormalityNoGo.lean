import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfVitaliCriterion
import GaloisForLFunctions.HTGeometry.ArcsineCentralBinomial
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The synchronized Cayley--Dirichlet normality obstruction

At the fixed point `s = 4/7`, the rational Cayley square-root approximants grow at least like
`(5/4)^N / 20`.  Local boundedness of the explicit source approximants would therefore force the
canonical squarefree-half Dirichlet partial sums to decay geometrically.  Successive partial sums
differ by the exact prime term, whose coefficient is `1/2` and whose norm decays only
polynomially.  Infinitely many primes give a contradiction.

This closes the local-boundedness hypothesis used by the first-rung Vitali bridge for its exact
same-index truncation.  It does not rule out a differently synchronized or regularized source
sequence.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

def cayleyExteriorWeight (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (5 / 8 : ℝ) ^ k

def cayleyNegHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * cayleyExteriorWeight k

def cayleyHalfExteriorTerm (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-5 / 2 : ℝ) ^ k

def cayleyHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, cayleyHalfExteriorTerm k

@[simp] theorem cayleyExteriorWeight_zero : cayleyExteriorWeight 0 = 1 := by
  simp [cayleyExteriorWeight]

theorem cayleyExteriorWeight_pos (k : ℕ) : 0 < cayleyExteriorWeight k := by
  unfold cayleyExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k) (pow_pos (by norm_num) k)

theorem cayleyExteriorWeight_growth (k : ℕ) :
    (5 / 4 : ℝ) * cayleyExteriorWeight k ≤ cayleyExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [cayleyExteriorWeight, cayleyExteriorWeight, pow_succ]
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hCgrowth : 2 * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) := by
    nlinarith
  have hbase : (5 / 4 : ℝ) * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) * (5 / 8 : ℝ) := by
    nlinarith
  calc
    (5 / 4 : ℝ) * ((Nat.centralBinom k : ℝ) * (5 / 8 : ℝ) ^ k) =
        ((5 / 4 : ℝ) * (Nat.centralBinom k : ℝ)) * (5 / 8 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (5 / 8 : ℝ)) * (5 / 8 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg (by norm_num) k)
    _ = (Nat.centralBinom (k + 1) : ℝ) * ((5 / 8 : ℝ) ^ k * (5 / 8 : ℝ)) := by
      ring

theorem cayleyExteriorWeight_ge_geometric (k : ℕ) :
    (5 / 4 : ℝ) ^ k ≤ cayleyExteriorWeight k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc
        (5 / 4 : ℝ) ^ k * (5 / 4 : ℝ) ≤
            cayleyExteriorWeight k * (5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (5 / 4 : ℝ) * cayleyExteriorWeight k := by ring
        _ ≤ cayleyExteriorWeight (k + 1) := cayleyExteriorWeight_growth k

theorem cayleyNegHalfExteriorSum_bounds (m : ℕ) :
    ((cayleyExteriorWeight (2 * m)) / 5 ≤ cayleyNegHalfExteriorSum (2 * m + 1) ∧
      cayleyNegHalfExteriorSum (2 * m + 1) ≤ cayleyExteriorWeight (2 * m)) ∧
    (-cayleyExteriorWeight (2 * m + 1) ≤ cayleyNegHalfExteriorSum (2 * m + 2) ∧
      cayleyNegHalfExteriorSum (2 * m + 2) ≤
        -cayleyExteriorWeight (2 * m + 1) / 5) := by
  induction m with
  | zero =>
      norm_num [cayleyNegHalfExteriorSum, cayleyExteriorWeight, Nat.centralBinom,
        Nat.choose, Finset.sum_range_succ]
  | succ m ih =>
      rcases ih with ⟨hodd, heven⟩
      have hg1 := cayleyExteriorWeight_growth (2 * m + 1)
      have hg2 := cayleyExteriorWeight_growth (2 * m + 2)
      have hp1 := cayleyExteriorWeight_pos (2 * m + 1)
      have hp2 := cayleyExteriorWeight_pos (2 * m + 2)
      have hp3 := cayleyExteriorWeight_pos (2 * m + 3)
      have hsodd : cayleyNegHalfExteriorSum (2 * (m + 1) + 1) =
          cayleyNegHalfExteriorSum (2 * m + 2) + cayleyExteriorWeight (2 * m + 2) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          cayleyNegHalfExteriorSum, Finset.sum_range_succ]
        have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
          rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
          norm_num
        rw [he, one_mul]
        rfl
      have hseven : cayleyNegHalfExteriorSum (2 * (m + 1) + 2) =
          cayleyNegHalfExteriorSum (2 * (m + 1) + 1) -
            cayleyExteriorWeight (2 * m + 3) := by
        rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
          cayleyNegHalfExteriorSum, Finset.sum_range_succ]
        have ho : (-1 : ℝ) ^ (2 * (m + 1) + 1) = -1 := by
          rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl, pow_add, pow_mul]
          norm_num
        rw [ho, neg_one_mul]
        unfold cayleyNegHalfExteriorSum
        congr 2
      have hnewodd :
          cayleyExteriorWeight (2 * (m + 1)) / 5 ≤
              cayleyNegHalfExteriorSum (2 * (m + 1) + 1) ∧
            cayleyNegHalfExteriorSum (2 * (m + 1) + 1) ≤
              cayleyExteriorWeight (2 * (m + 1)) := by
        rw [hsodd]
        simp only [Nat.mul_add, Nat.mul_one]
        constructor <;> linarith
      have hneweven :
          -cayleyExteriorWeight (2 * (m + 1) + 1) ≤
              cayleyNegHalfExteriorSum (2 * (m + 1) + 2) ∧
            cayleyNegHalfExteriorSum (2 * (m + 1) + 2) ≤
              -cayleyExteriorWeight (2 * (m + 1) + 1) / 5 := by
        rw [hseven]
        rcases hnewodd with ⟨hnewoddlo, hnewoddhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hnewoddlo hnewoddhi ⊢
        constructor <;> linarith
      exact ⟨hnewodd, hneweven⟩

theorem cayleyHalfExteriorTerm_neg {k : ℕ} (hk : 1 ≤ k) :
    cayleyHalfExteriorTerm k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [cayleyHalfExteriorTerm]
  | succ k hk ih =>
      have hrec := choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : cayleyHalfExteriorTerm (k + 1) =
          cayleyHalfExteriorTerm k * ((5 / 2 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold cayleyHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih (div_pos (mul_pos (by norm_num) hkpos) hk1)

theorem cayleyHalfExteriorSum_le_neg_quarter {N : ℕ} (hN : 2 ≤ N) :
    cayleyHalfExteriorSum N ≤ -1 / 4 := by
  induction N, hN using Nat.le_induction with
  | base =>
      norm_num [cayleyHalfExteriorSum, cayleyHalfExteriorTerm,
        Ring.choose_zero_right, Ring.choose_one_right, Finset.sum_range_succ]
  | succ N hN ih =>
      rw [cayleyHalfExteriorSum, Finset.sum_range_succ, ← cayleyHalfExteriorSum]
      calc
        cayleyHalfExteriorSum N + cayleyHalfExteriorTerm N ≤ cayleyHalfExteriorSum N :=
          add_le_of_nonpos_right
            (le_of_lt (cayleyHalfExteriorTerm_neg (le_trans one_le_two hN)))
        _ ≤ -1 / 4 := ih

private theorem binomialPartialSum_eq_sum_choose_complex (a z : ℂ) (N : ℕ) :
    (binomialSeries ℂ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

private theorem binomialPartialSum_eq_sum_choose_real (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_binomialPartialSum_ofReal (a z : ℝ) (N : ℕ) :
    (binomialSeries ℂ (a : ℂ)).partialSum N (z : ℂ) =
      ((binomialSeries ℝ a).partialSum N z : ℂ) := by
  rw [binomialPartialSum_eq_sum_choose_complex,
    binomialPartialSum_eq_sum_choose_real]
  push_cast
  rfl

theorem complex_halfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-5 / 2 : ℂ) =
      (cayleyHalfExteriorSum N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show (-5 / 2 : ℂ) = ((-5 / 2 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    binomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_negHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (5 / 2 : ℂ) =
      (cayleyNegHalfExteriorSum N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    binomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold cayleyNegHalfExteriorSum cayleyExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * (5 / 2 : ℝ) ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * (5 / 2 : ℝ) ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * (5 / 2 : ℝ)) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k * (5 / 8 : ℝ) ^ k := by
      norm_num
  ring

/-- Fixed exterior-disk point used to test the source approximants. -/
def cayleyExteriorPoint : ℂ := (4 / 7 : ℂ)

@[simp] theorem poleFactorCayley_cayleyExteriorPoint :
    poleFactorCayley cayleyExteriorPoint = (-5 / 2 : ℂ) := by
  norm_num [cayleyExteriorPoint, poleFactorCayley,
    GaloisForLFunctions.HTGeometry.cayleyRight]

theorem cayleyExteriorPoint_mem_rightHalf : cayleyExteriorPoint ∈ rightHalf := by
  rw [mem_rightHalf]
  norm_num [cayleyExteriorPoint]

theorem norm_halfExteriorPartialSum_ge_quarter {N : ℕ} (hN : 2 ≤ N) :
    (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-5 / 2 : ℂ)‖ := by
  rw [complex_halfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hsum := cayleyHalfExteriorSum_le_neg_quarter hN
  rw [abs_of_nonpos (le_trans hsum (by norm_num))]
  linarith

theorem norm_negHalfExteriorPartialSum_odd_ge (m : ℕ) :
    (5 / 4 : ℝ) ^ (2 * m) / 5 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 1) (5 / 2 : ℂ)‖ := by
  rw [complex_negHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (cayleyNegHalfExteriorSum_bounds m).1
  have hgeom := cayleyExteriorWeight_ge_geometric (2 * m)
  have hnonneg : 0 ≤ cayleyNegHalfExteriorSum (2 * m + 1) := by
    linarith [cayleyExteriorWeight_pos (2 * m)]
  rw [abs_of_nonneg hnonneg]
  exact le_trans (div_le_div_of_nonneg_right hgeom (by norm_num)) hbounds.1

theorem norm_negHalfExteriorPartialSum_even_ge (m : ℕ) :
    (5 / 4 : ℝ) ^ (2 * m + 1) / 5 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 2) (5 / 2 : ℂ)‖ := by
  rw [complex_negHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (cayleyNegHalfExteriorSum_bounds m).2
  have hgeom := cayleyExteriorWeight_ge_geometric (2 * m + 1)
  have hnonpos : cayleyNegHalfExteriorSum (2 * m + 2) ≤ 0 := by
    linarith [cayleyExteriorWeight_pos (2 * m + 1)]
  rw [abs_of_nonpos hnonpos]
  have hweight : (5 / 4 : ℝ) ^ (2 * m + 1) / 5 ≤
      cayleyExteriorWeight (2 * m + 1) / 5 :=
    div_le_div_of_nonneg_right hgeom (by norm_num)
  linarith [hbounds.2]

theorem norm_poleFactorSqrtApprox_cayleyExteriorPoint_odd_ge (m : ℕ) (hm : 1 ≤ m) :
    (5 / 4 : ℝ) ^ (2 * m) / 20 ≤
      ‖poleFactorSqrtApprox (2 * m + 1) cayleyExteriorPoint‖ := by
  have hhalf := norm_halfExteriorPartialSum_ge_quarter
    (show 2 ≤ 2 * m + 1 by omega)
  have hneg := norm_negHalfExteriorPartialSum_odd_ge m
  have hhalf' : (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum (2 * m + 1) (-(5 / 2) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (5 / 4 : ℝ) ^ (2 * m) / 5 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 1) (5 / 2 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_cayleyExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul]
  calc
    (5 / 4 : ℝ) ^ (2 * m) / 20 =
        (1 / 4 : ℝ) * ((5 / 4 : ℝ) ^ (2 * m) / 5) := by ring
    _ ≤ _ := mul_le_mul hhalf' hneg' (by positivity) (by positivity)

theorem norm_poleFactorSqrtApprox_cayleyExteriorPoint_even_ge (m : ℕ) :
    (5 / 4 : ℝ) ^ (2 * m + 1) / 20 ≤
      ‖poleFactorSqrtApprox (2 * m + 2) cayleyExteriorPoint‖ := by
  have hhalf := norm_halfExteriorPartialSum_ge_quarter
    (show 2 ≤ 2 * m + 2 by omega)
  have hneg := norm_negHalfExteriorPartialSum_even_ge m
  have hhalf' : (1 / 4 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum (2 * m + 2) (-(5 / 2) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (5 / 4 : ℝ) ^ (2 * m + 1) / 5 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 2) (5 / 2 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_cayleyExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul]
  calc
    (5 / 4 : ℝ) ^ (2 * m + 1) / 20 =
        (1 / 4 : ℝ) * ((5 / 4 : ℝ) ^ (2 * m + 1) / 5) := by ring
    _ ≤ _ := mul_le_mul hhalf' hneg' (by positivity) (by positivity)

theorem squarefreeHalfDirichletPartialSum_succ (N : ℕ) (s : ℂ) :
    squarefreeHalfDirichletPartialSum (N + 1) s =
      squarefreeHalfDirichletPartialSum N s +
        LSeries.term squarefreeConvolutionHalf s N := by
  simp [squarefreeHalfDirichletPartialSum, Finset.sum_range_succ]

theorem norm_squarefreeConvolutionHalf_term_prime (p : ℕ) (hp : p.Prime) :
    ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ =
      (1 / 2 : ℝ) / (p : ℝ) ^ (4 / 7 : ℝ) := by
  rw [LSeries.norm_term_eq, if_neg hp.ne_zero,
    squarefreeConvolutionHalf_apply_prime hp]
  norm_num [cayleyExteriorPoint]

theorem inv_two_mul_natCast_le_norm_squarefreeConvolutionHalf_term_prime
    (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) / (2 * p) ≤
      ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ := by
  rw [norm_squarefreeConvolutionHalf_term_prime p hp]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (4 / 7 : ℝ) ≤ p := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hp1 (show (4 / 7 : ℝ) ≤ 1 by norm_num)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow0 : 0 < (p : ℝ) ^ (4 / 7 : ℝ) := Real.rpow_pos_of_pos hp0 _
  rw [one_div, one_div, mul_inv, show (2 : ℝ)⁻¹ = 1 / 2 by ring]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hp0 hpow0).2 hpow) (by norm_num)

theorem geometric_mul_norm_squarefreeHalfDirichletPartialSum_le_of_source_bound
    {N e : ℕ} {C : ℝ}
    (hr : (5 / 4 : ℝ) ^ e / 20 ≤
      ‖poleFactorSqrtApprox N cayleyExteriorPoint‖)
    (hsource : ‖poleClearedFirstTraceSourceApprox N cayleyExteriorPoint‖ ≤ C) :
    (5 / 4 : ℝ) ^ e *
        ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
      20 * C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ := by
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero cayleyExteriorPoint)
  have hprod :
      ‖poleFactorSqrtApprox N cayleyExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
        C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ := by
    rw [poleClearedFirstTraceSourceApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hscaled :
      ((5 / 4 : ℝ) ^ e / 20) *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
        C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ :=
    le_trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)) hprod
  nlinarith

/-- The synchronized Cayley--Dirichlet truncations are not locally bounded on `rightHalf`. -/
theorem not_poleClearedFirstTraceSourceLocallyBounded :
    ¬ PoleClearedFirstTraceSourceLocallyBounded := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc cayleyExteriorPoint cayleyExteriorPoint_mem_rightHalf
  have hcenter : cayleyExteriorPoint ∈ ball cayleyExteriorPoint R := mem_ball_self hR
  have hCnonneg : 0 ≤ C :=
    le_trans (norm_nonneg _) (hC 0 cayleyExteriorPoint hcenter)
  let K : ℝ := 20 * C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hodd (m : ℕ) (hm : 1 ≤ m) :
      (5 / 4 : ℝ) ^ (2 * m) *
          ‖squarefreeHalfDirichletPartialSum (2 * m + 1) cayleyExteriorPoint‖ ≤ K := by
    dsimp [K]
    exact geometric_mul_norm_squarefreeHalfDirichletPartialSum_le_of_source_bound
      (norm_poleFactorSqrtApprox_cayleyExteriorPoint_odd_ge m hm)
      (hC (2 * m + 1) cayleyExteriorPoint hcenter)
  have heven (m : ℕ) :
      (5 / 4 : ℝ) ^ (2 * m + 1) *
          ‖squarefreeHalfDirichletPartialSum (2 * m + 2) cayleyExteriorPoint‖ ≤ K := by
    dsimp [K]
    exact geometric_mul_norm_squarefreeHalfDirichletPartialSum_le_of_source_bound
      (norm_poleFactorSqrtApprox_cayleyExteriorPoint_even_ge m)
      (hC (2 * m + 2) cayleyExteriorPoint hcenter)
  have hterm (m : ℕ) (hm : 1 ≤ m) :
      (5 / 4 : ℝ) ^ (2 * m + 1) *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint (2 * m + 1)‖ ≤
        (9 / 4 : ℝ) * K := by
    have hsucc := squarefreeHalfDirichletPartialSum_succ
      (2 * m + 1) cayleyExteriorPoint
    have htermEq :
        LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint (2 * m + 1) =
          squarefreeHalfDirichletPartialSum (2 * m + 2) cayleyExteriorPoint -
            squarefreeHalfDirichletPartialSum (2 * m + 1) cayleyExteriorPoint := by
      rw [hsucc]
      ring
    have htri :
        ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint (2 * m + 1)‖ ≤
          ‖squarefreeHalfDirichletPartialSum (2 * m + 2) cayleyExteriorPoint‖ +
            ‖squarefreeHalfDirichletPartialSum (2 * m + 1) cayleyExteriorPoint‖ := by
      rw [htermEq]
      exact norm_sub_le _ _
    calc
      (5 / 4 : ℝ) ^ (2 * m + 1) *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint (2 * m + 1)‖ ≤
          (5 / 4 : ℝ) ^ (2 * m + 1) *
            (‖squarefreeHalfDirichletPartialSum (2 * m + 2) cayleyExteriorPoint‖ +
              ‖squarefreeHalfDirichletPartialSum (2 * m + 1) cayleyExteriorPoint‖) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg (by norm_num) _)
      _ = (5 / 4 : ℝ) ^ (2 * m + 1) *
            ‖squarefreeHalfDirichletPartialSum (2 * m + 2) cayleyExteriorPoint‖ +
          (5 / 4 : ℝ) * ((5 / 4 : ℝ) ^ (2 * m) *
            ‖squarefreeHalfDirichletPartialSum (2 * m + 1) cayleyExteriorPoint‖) := by
        rw [show 2 * m + 1 = 2 * m + 1 by rfl, pow_succ]
        ring
      _ ≤ K + (5 / 4 : ℝ) * K :=
        add_le_add (heven m) (mul_le_mul_of_nonneg_left (hodd m hm) (by norm_num))
      _ = (9 / 4 : ℝ) * K := by ring
  have hdiverge : Tendsto (fun n : ℕ => (5 / 4 : ℝ) ^ n / n) atTop atTop :=
    GaloisForLFunctions.tendsto_const_pow_div_natCast_atTop (by norm_num)
  have heventually : ∀ᶠ n : ℕ in atTop,
      2 * ((9 / 4 : ℝ) * K) < (5 / 4 : ℝ) ^ n / n :=
    hdiverge.eventually_gt_atTop (2 * ((9 / 4 : ℝ) * K))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hpN' : N ≤ p := (le_max_left N 3).trans hpN
  have hp3 : 3 ≤ p := (le_max_right N 3).trans hpN
  have hpne2 : p ≠ 2 := by omega
  obtain ⟨m, hpm⟩ := hp.odd_of_ne_two hpne2
  have hm : 1 ≤ m := by omega
  have hupper :
      (5 / 4 : ℝ) ^ p *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ ≤
        (9 / 4 : ℝ) * K := by
    simpa only [hpm] using hterm m hm
  have hlowerTerm :=
    inv_two_mul_natCast_le_norm_squarefreeConvolutionHalf_term_prime p hp
  have hlower :
      (5 / 4 : ℝ) ^ p / (2 * (p : ℝ)) ≤
        (5 / 4 : ℝ) ^ p *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ := by
    calc
      (5 / 4 : ℝ) ^ p / (2 * (p : ℝ)) =
          (5 / 4 : ℝ) ^ p * (1 / (2 * (p : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlowerTerm (pow_nonneg (by norm_num) p)
  have hstrict :
      (9 / 4 : ℝ) * K < (5 / 4 : ℝ) ^ p / (2 * (p : ℝ)) := by
    have hlarge := hN p hpN'
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [show (5 / 4 : ℝ) ^ p / (2 * (p : ℝ)) =
      ((5 / 4 : ℝ) ^ p / (p : ℝ)) / 2 by ring]
    linarith
  linarith

end

end RHTower
