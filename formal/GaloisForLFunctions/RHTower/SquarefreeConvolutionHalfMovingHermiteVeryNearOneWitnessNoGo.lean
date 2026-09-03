import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteNearOneWitnessNoGo

/-!
# A very-near-one witness closes Hermite depths through slope `3/8`

At `s=20/21`, the shifted pole Cayley coordinate is `-11/10`.  Explicit alternating-binomial
bounds show the finite Cayley square-root factor has norm at least one once its cutoff is at least
`271`: the central-binomial weights have eventual ratio at least `21/20`, while the other
binomial factor is bounded away from zero.

For the moving Hermite counterterm, use the radius-`3/8` Cauchy circle about `6/11`.  The witness
gap is `94/231`, hence the Taylor ratio is `752/693`; after undoing the exponential dress,

`|c_{N,K}(20/21)| ≤ 12 N (752/693)^(K+1) exp(-(59/1848)N)`.

The rational inequality `752/693 ≤ exp(1/12)` makes this tend to zero whenever `K ≤ 3N/8`,
with residual exponential rate `5/7392`.  Local boundedness would instead require the counterterm
to be unbounded at the same point.  Thus every surviving canonical point-Hermite schedule must
exceed slope `3/8` infinitely often.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def twentyTwentyFirstExteriorWeight (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (11 / 40 : ℝ) ^ k

def twentyTwentyFirstNegHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * twentyTwentyFirstExteriorWeight k

def twentyTwentyFirstHalfExteriorTerm (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-11 / 10 : ℝ) ^ k

def twentyTwentyFirstHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, twentyTwentyFirstHalfExteriorTerm k

theorem twentyTwentyFirstExteriorWeight_pos (k : ℕ) :
    0 < twentyTwentyFirstExteriorWeight k := by
  unfold twentyTwentyFirstExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k) (pow_pos (by norm_num) k)

theorem twentyTwentyFirstExteriorWeight_growth {k : ℕ} (hk : 10 ≤ k) :
    (21 / 20 : ℝ) * twentyTwentyFirstExteriorWeight k ≤
      twentyTwentyFirstExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hCgrowth : (21 / 20 : ℝ) * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) * (11 / 40 : ℝ) := by
    have hkreal : (10 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [twentyTwentyFirstExteriorWeight, twentyTwentyFirstExteriorWeight, pow_succ]
  calc
    (21 / 20 : ℝ) *
        ((Nat.centralBinom k : ℝ) * (11 / 40 : ℝ) ^ k) =
      ((21 / 20 : ℝ) * (Nat.centralBinom k : ℝ)) *
        (11 / 40 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (11 / 40 : ℝ)) *
        (11 / 40 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right hCgrowth (pow_nonneg (by norm_num) k)
    _ = (Nat.centralBinom (k + 1) : ℝ) *
        ((11 / 40 : ℝ) ^ k * (11 / 40 : ℝ)) := by ring

theorem twentyTwentyFirstExteriorWeight_ge_geometric {k : ℕ} (hk : 10 ≤ k) :
    (2 / 5 : ℝ) * (21 / 20 : ℝ) ^ (k - 10) ≤
      twentyTwentyFirstExteriorWeight k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [twentyTwentyFirstExteriorWeight, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
      rw [show k + 1 - 10 = (k - 10) + 1 by omega, pow_succ]
      calc
        (2 / 5 : ℝ) * ((21 / 20 : ℝ) ^ (k - 10) * (21 / 20 : ℝ)) =
            ((2 / 5 : ℝ) * (21 / 20 : ℝ) ^ (k - 10)) *
              (21 / 20 : ℝ) := by ring
        _ ≤ twentyTwentyFirstExteriorWeight k * (21 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (21 / 20 : ℝ) * twentyTwentyFirstExteriorWeight k := by ring
        _ ≤ twentyTwentyFirstExteriorWeight (k + 1) :=
          twentyTwentyFirstExteriorWeight_growth hk

theorem twentyTwentyFirstHalfExteriorTerm_neg {k : ℕ} (hk : 1 ≤ k) :
    twentyTwentyFirstHalfExteriorTerm k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [twentyTwentyFirstHalfExteriorTerm]
  | succ k hk ih =>
      have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : twentyTwentyFirstHalfExteriorTerm (k + 1) =
          twentyTwentyFirstHalfExteriorTerm k *
            ((11 / 10 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold twentyTwentyFirstHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih
        (div_pos (mul_pos (by norm_num) hkpos) hk1)

theorem twentyTwentyFirstHalfExteriorTerm_succ (k : ℕ) :
    twentyTwentyFirstHalfExteriorTerm (k + 1) =
      twentyTwentyFirstHalfExteriorTerm k *
        ((11 / 10 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
      Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hk1)]
    simpa [mul_comm] using hrec
  unfold twentyTwentyFirstHalfExteriorTerm
  rw [hchoose, pow_succ]
  ring

theorem twentyTwentyFirstHalfExteriorSum_eleven_le_neg_one_div_hundred :
    twentyTwentyFirstHalfExteriorSum 11 ≤ (-1 / 100 : ℝ) := by
  rw [show twentyTwentyFirstHalfExteriorSum 11 =
      twentyTwentyFirstHalfExteriorTerm 0 + twentyTwentyFirstHalfExteriorTerm 1 +
      twentyTwentyFirstHalfExteriorTerm 2 + twentyTwentyFirstHalfExteriorTerm 3 +
      twentyTwentyFirstHalfExteriorTerm 4 + twentyTwentyFirstHalfExteriorTerm 5 +
      twentyTwentyFirstHalfExteriorTerm 6 + twentyTwentyFirstHalfExteriorTerm 7 +
      twentyTwentyFirstHalfExteriorTerm 8 + twentyTwentyFirstHalfExteriorTerm 9 +
      twentyTwentyFirstHalfExteriorTerm 10 by
    norm_num [twentyTwentyFirstHalfExteriorSum, Finset.sum_range_succ]]
  rw [twentyTwentyFirstHalfExteriorTerm_succ 9,
    twentyTwentyFirstHalfExteriorTerm_succ 8,
    twentyTwentyFirstHalfExteriorTerm_succ 7,
    twentyTwentyFirstHalfExteriorTerm_succ 6,
    twentyTwentyFirstHalfExteriorTerm_succ 5,
    twentyTwentyFirstHalfExteriorTerm_succ 4,
    twentyTwentyFirstHalfExteriorTerm_succ 3,
    twentyTwentyFirstHalfExteriorTerm_succ 2,
    twentyTwentyFirstHalfExteriorTerm_succ 1,
    twentyTwentyFirstHalfExteriorTerm_succ 0]
  norm_num [twentyTwentyFirstHalfExteriorTerm]

private theorem twentyTwentyFirstNegHalfExteriorSum_base :
    ((twentyTwentyFirstExteriorWeight 28) / 21 ≤
        twentyTwentyFirstNegHalfExteriorSum 29 ∧
      twentyTwentyFirstNegHalfExteriorSum 29 ≤ twentyTwentyFirstExteriorWeight 28) ∧
    (-twentyTwentyFirstExteriorWeight 29 ≤ twentyTwentyFirstNegHalfExteriorSum 30 ∧
      twentyTwentyFirstNegHalfExteriorSum 30 ≤
        -twentyTwentyFirstExteriorWeight 29 / 21) := by
  norm_num [twentyTwentyFirstNegHalfExteriorSum, twentyTwentyFirstExteriorWeight,
    Nat.centralBinom, Nat.choose, Finset.sum_range_succ]

theorem twentyTwentyFirstHalfExteriorSum_le_neg_one_div_hundred
    {N : ℕ} (hN : 11 ≤ N) :
    twentyTwentyFirstHalfExteriorSum N ≤ (-1 / 100 : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => exact twentyTwentyFirstHalfExteriorSum_eleven_le_neg_one_div_hundred
  | succ N hN ih =>
      rw [twentyTwentyFirstHalfExteriorSum, Finset.sum_range_succ,
        ← twentyTwentyFirstHalfExteriorSum]
      exact (add_le_of_nonpos_right
        (le_of_lt (twentyTwentyFirstHalfExteriorTerm_neg (by omega)))).trans ih

theorem twentyTwentyFirstNegHalfExteriorSum_bounds {m : ℕ} (hm : 14 ≤ m) :
    ((twentyTwentyFirstExteriorWeight (2 * m)) / 21 ≤
        twentyTwentyFirstNegHalfExteriorSum (2 * m + 1) ∧
      twentyTwentyFirstNegHalfExteriorSum (2 * m + 1) ≤
        twentyTwentyFirstExteriorWeight (2 * m)) ∧
    (-twentyTwentyFirstExteriorWeight (2 * m + 1) ≤
        twentyTwentyFirstNegHalfExteriorSum (2 * m + 2) ∧
      twentyTwentyFirstNegHalfExteriorSum (2 * m + 2) ≤
        -twentyTwentyFirstExteriorWeight (2 * m + 1) / 21) := by
  induction m, hm using Nat.le_induction with
  | base => exact twentyTwentyFirstNegHalfExteriorSum_base
  | succ m hm ih =>
      rcases ih with ⟨hodd, heven⟩
      have hg1 := twentyTwentyFirstExteriorWeight_growth
        (show 10 ≤ 2 * m + 1 by omega)
      have hg2 := twentyTwentyFirstExteriorWeight_growth
        (show 10 ≤ 2 * m + 2 by omega)
      have hp1 := twentyTwentyFirstExteriorWeight_pos (2 * m + 1)
      have hp2 := twentyTwentyFirstExteriorWeight_pos (2 * m + 2)
      have hp3 := twentyTwentyFirstExteriorWeight_pos (2 * m + 3)
      have hsodd : twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 1) =
          twentyTwentyFirstNegHalfExteriorSum (2 * m + 2) +
            twentyTwentyFirstExteriorWeight (2 * m + 2) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          twentyTwentyFirstNegHalfExteriorSum, Finset.sum_range_succ]
        have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
          rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
          norm_num
        rw [he, one_mul]
        rfl
      have hseven : twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 2) =
          twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 1) -
            twentyTwentyFirstExteriorWeight (2 * m + 3) := by
        rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
          twentyTwentyFirstNegHalfExteriorSum, Finset.sum_range_succ]
        have ho : (-1 : ℝ) ^ (2 * (m + 1) + 1) = -1 := by
          rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl,
            pow_add, pow_mul]
          norm_num
        rw [ho, neg_one_mul]
        unfold twentyTwentyFirstNegHalfExteriorSum
        congr 2
      have hnewodd :
          twentyTwentyFirstExteriorWeight (2 * (m + 1)) / 21 ≤
              twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 1) ∧
            twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 1) ≤
              twentyTwentyFirstExteriorWeight (2 * (m + 1)) := by
        rw [hsodd]
        rcases heven with ⟨hevenlo, hevenhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hevenlo hevenhi ⊢
        constructor <;> nlinarith
      have hneweven :
          -twentyTwentyFirstExteriorWeight (2 * (m + 1) + 1) ≤
              twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 2) ∧
            twentyTwentyFirstNegHalfExteriorSum (2 * (m + 1) + 2) ≤
              -twentyTwentyFirstExteriorWeight (2 * (m + 1) + 1) / 21 := by
        rw [hseven]
        rcases hnewodd with ⟨hnewoddlo, hnewoddhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hnewoddlo hnewoddhi ⊢
        constructor <;> nlinarith
      exact ⟨hnewodd, hneweven⟩

private theorem twentyTwentyFirstBinomialPartialSum_eq_sum_choose_real
    (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_twentyTwentyFirstHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-11 / 10 : ℂ) =
      (twentyTwentyFirstHalfExteriorSum N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show (-11 / 10 : ℂ) = ((-11 / 10 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    twentyTwentyFirstBinomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_twentyTwentyFirstNegHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (11 / 10 : ℂ) =
      (twentyTwentyFirstNegHalfExteriorSum N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    twentyTwentyFirstBinomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold twentyTwentyFirstNegHalfExteriorSum twentyTwentyFirstExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [GaloisForLFunctions.choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * (11 / 10 : ℝ) ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * (11 / 10 : ℝ) ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * (11 / 10 : ℝ)) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          (11 / 40 : ℝ) ^ k := by norm_num
  ring

/-- Very-near-one interior witness; its pole Cayley coordinate is `-11/10`. -/
def hermiteVeryNearOneExteriorPoint : ℂ := (20 / 21 : ℂ)

@[simp] theorem poleFactorCayley_hermiteVeryNearOneExteriorPoint :
    poleFactorCayley hermiteVeryNearOneExteriorPoint = (-11 / 10 : ℂ) := by
  norm_num [hermiteVeryNearOneExteriorPoint, poleFactorCayley,
    GaloisForLFunctions.HTGeometry.cayleyRight]

theorem hermiteVeryNearOneExteriorPoint_mem_rightHalf :
    hermiteVeryNearOneExteriorPoint ∈ rightHalf := by
  rw [mem_rightHalf]
  norm_num [hermiteVeryNearOneExteriorPoint]

theorem norm_twentyTwentyFirstHalfExteriorPartialSum_ge_one_div_hundred
    {N : ℕ} (hN : 11 ≤ N) :
    (1 / 100 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-11 / 10 : ℂ)‖ := by
  rw [complex_twentyTwentyFirstHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hsum := twentyTwentyFirstHalfExteriorSum_le_neg_one_div_hundred hN
  rw [abs_of_nonpos (hsum.trans (by norm_num))]
  linarith

theorem norm_twentyTwentyFirstNegHalfExteriorPartialSum_odd_ge
    (m : ℕ) (hm : 14 ≤ m) :
    (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 10) ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum
        (2 * m + 1) (11 / 10 : ℂ)‖ := by
  rw [complex_twentyTwentyFirstNegHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (twentyTwentyFirstNegHalfExteriorSum_bounds hm).1
  have hgeom := twentyTwentyFirstExteriorWeight_ge_geometric
    (show 10 ≤ 2 * m by omega)
  have hnonneg : 0 ≤ twentyTwentyFirstNegHalfExteriorSum (2 * m + 1) := by
    linarith [twentyTwentyFirstExteriorWeight_pos (2 * m)]
  rw [abs_of_nonneg hnonneg]
  calc
    (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 10) =
        ((2 / 5 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 10)) / 21 := by ring
    _ ≤ twentyTwentyFirstExteriorWeight (2 * m) / 21 :=
      div_le_div_of_nonneg_right hgeom (by norm_num)
    _ ≤ _ := hbounds.1

theorem norm_twentyTwentyFirstNegHalfExteriorPartialSum_even_ge
    (m : ℕ) (hm : 14 ≤ m) :
    (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 9) ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum
        (2 * m + 2) (11 / 10 : ℂ)‖ := by
  rw [complex_twentyTwentyFirstNegHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (twentyTwentyFirstNegHalfExteriorSum_bounds hm).2
  have hgeom := twentyTwentyFirstExteriorWeight_ge_geometric
    (show 10 ≤ 2 * m + 1 by omega)
  have hnonpos : twentyTwentyFirstNegHalfExteriorSum (2 * m + 2) ≤ 0 := by
    linarith [twentyTwentyFirstExteriorWeight_pos (2 * m + 1)]
  rw [abs_of_nonpos hnonpos]
  calc
    (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 9) =
        ((2 / 5 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 9)) / 21 := by ring
    _ ≤ twentyTwentyFirstExteriorWeight (2 * m + 1) / 21 :=
      div_le_div_of_nonneg_right hgeom (by norm_num)
    _ ≤ _ := by linarith [hbounds.2]

theorem norm_poleFactorSqrtApprox_hermiteVeryNearOneExteriorPoint_geometric
    {N : ℕ} (hN : 29 ≤ N) :
    (21 / 20 : ℝ) ^ (N - 11) / 5250 ≤
      ‖poleFactorSqrtApprox N hermiteVeryNearOneExteriorPoint‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm : 15 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    have hhalf : (1 / 100 : ℝ) ≤
        ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum
          (2 * (k + 1)) (-(11 / 10) : ℂ)‖ := by
      simpa only [neg_div] using
        norm_twentyTwentyFirstHalfExteriorPartialSum_ge_one_div_hundred
          (show 11 ≤ 2 * (k + 1) by omega)
    have hneg : (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * k - 9) ≤
        ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum
          (2 * k + 2) (11 / 10 : ℂ)‖ := by
      simpa only [neg_div] using
        norm_twentyTwentyFirstNegHalfExteriorPartialSum_even_ge k (by omega)
    rw [poleFactorSqrtApprox, poleFactorCayley_hermiteVeryNearOneExteriorPoint]
    norm_num only [neg_neg]
    rw [norm_mul]
    rw [show 2 * (k + 1) - 11 = 2 * k - 9 by omega]
    calc
      (21 / 20 : ℝ) ^ (2 * k - 9) / 5250 =
          (1 / 100 : ℝ) *
            ((2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * k - 9)) := by ring
      _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)
  · have hm : 14 ≤ m := by omega
    have hhalf : (1 / 100 : ℝ) ≤
        ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum
          (2 * m + 1) (-(11 / 10) : ℂ)‖ := by
      simpa only [neg_div] using
        norm_twentyTwentyFirstHalfExteriorPartialSum_ge_one_div_hundred
          (show 11 ≤ 2 * m + 1 by omega)
    have hneg : (2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 10) ≤
        ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum
          (2 * m + 1) (11 / 10 : ℂ)‖ := by
      simpa only [neg_div] using
        norm_twentyTwentyFirstNegHalfExteriorPartialSum_odd_ge m hm
    rw [poleFactorSqrtApprox, poleFactorCayley_hermiteVeryNearOneExteriorPoint]
    norm_num only [neg_neg]
    rw [norm_mul]
    rw [show 2 * m + 1 - 11 = 2 * m - 10 by omega]
    calc
      (21 / 20 : ℝ) ^ (2 * m - 10) / 5250 =
          (1 / 100 : ℝ) *
            ((2 / 105 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 10)) := by ring
      _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)

theorem one_le_norm_poleFactorSqrtApprox_hermiteVeryNearOneExteriorPoint
    {N : ℕ} (hN : 271 ≤ N) :
    1 ≤ ‖poleFactorSqrtApprox N hermiteVeryNearOneExteriorPoint‖ := by
  have hgeom := norm_poleFactorSqrtApprox_hermiteVeryNearOneExteriorPoint_geometric
    (show 29 ≤ N by omega)
  have hq20 : (2 : ℝ) ≤ (21 / 20 : ℝ) ^ 20 := by norm_num
  have hq260 : (2 : ℝ) ^ 13 ≤ (21 / 20 : ℝ) ^ 260 := by
    rw [show 260 = 20 * 13 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hq20 13
  have hpow : (21 / 20 : ℝ) ^ 260 ≤ (21 / 20 : ℝ) ^ (N - 11) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (1 : ℝ) ≤ (2 : ℝ) ^ 13 / 5250 := by norm_num
    _ ≤ (21 / 20 : ℝ) ^ 260 / 5250 :=
      div_le_div_of_nonneg_right hq260 (by norm_num)
    _ ≤ (21 / 20 : ℝ) ^ (N - 11) / 5250 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ ≤ _ := hgeom

theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteVeryNearOneExteriorPoint :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint‖ ≤ C := by
  simpa [hermiteVeryNearOneExteriorPoint] using
    (not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
      (sigma := (20 / 21 : ℝ)) (by norm_num) (by norm_num))

theorem counterterm_not_eventually_bounded_at_hermiteVeryNearOneExteriorPoint_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N hermiteVeryNearOneExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc hermiteVeryNearOneExteriorPoint hermiteVeryNearOneExteriorPoint_mem_rightHalf
  have hcenter : hermiteVeryNearOneExteriorPoint ∈ ball hermiteVeryNearOneExteriorPoint R :=
    mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        hermiteVeryNearOneExteriorPoint‖ ≤ C :=
    fun N => hC N hermiteVeryNearOneExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 271))
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteVeryNearOneExteriorPoint
  let Q : ℝ := C * ‖squarefreeCarlemanHalfDet hermiteVeryNearOneExteriorPoint‖
  refine ⟨Q + B, max N₀ M₀, fun N hN => ?_⟩
  have hNkappa : 271 ≤ kappa N := hN₀ N ((le_max_left N₀ M₀).trans hN)
  have hNM : M₀ ≤ N := (le_max_right N₀ M₀).trans hN
  have honeFactor : (1 : ℝ) ≤
      ‖poleFactorSqrtApprox (kappa N) hermiteVeryNearOneExteriorPoint‖ :=
    one_le_norm_poleFactorSqrtApprox_hermiteVeryNearOneExteriorPoint hNkappa
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet hermiteVeryNearOneExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero hermiteVeryNearOneExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) hermiteVeryNearOneExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
            counterterm N hermiteVeryNearOneExteriorPoint‖ ≤ Q := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hcorrected :
      ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
        counterterm N hermiteVeryNearOneExteriorPoint‖ ≤ Q := by
    calc
      _ = 1 * ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
          counterterm N hermiteVeryNearOneExteriorPoint‖ := by ring
      _ ≤ ‖poleFactorSqrtApprox (kappa N) hermiteVeryNearOneExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
            counterterm N hermiteVeryNearOneExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right honeFactor (norm_nonneg _)
      _ ≤ Q := hprod
  calc
    ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
          counterterm N hermiteVeryNearOneExteriorPoint) -
            counterterm N hermiteVeryNearOneExteriorPoint‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N hermiteVeryNearOneExteriorPoint +
          counterterm N hermiteVeryNearOneExteriorPoint‖ +
        ‖counterterm N hermiteVeryNearOneExteriorPoint‖ := norm_sub_le _ _
    _ ≤ Q + B := add_le_add hcorrected (hB N hNM)

theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteVeryNearOneExteriorPoint
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm :
      Tendsto (fun N => counterterm N hermiteVeryNearOneExteriorPoint) atTop (nhds 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  apply
    (counterterm_not_eventually_bounded_at_hermiteVeryNearOneExteriorPoint_of_cofinal_locallyBounded
      hkappa hloc)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

private theorem norm_boundaryPositiveExponentialDress_on_veryNearOneSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (3 / 8 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ)) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (3 / 8 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ 3 / 8 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((3 / 8 : ℝ) * (N : ℝ)) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ 3 / 8 :=
      (le_abs_self _).trans hreal
    have hrexp :
        (((N : ℂ) * (w - boundaryExteriorPoint)).re) =
          (N : ℝ) * (w.re - (6 / 11 : ℝ)) := by
      simp [boundaryExteriorPoint]
    rw [hrexp]
    have hN : (0 : ℝ) ≤ N := by positivity
    nlinarith
  rw [boundaryPositiveExponentialDress, norm_mul]
  exact mul_le_mul hsep (norm_squarefreeHalfDirichletPartialSum_le_nat N hwre)
    (norm_nonneg _) (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_veryNearOneCircle_le
    (j N : ℕ) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) /
        (3 / 8 : ℝ) ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s
        (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num)
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_veryNearOneSphere_le N hw)

private theorem norm_hermiteVeryNearOneExterior_gap :
    ‖hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint‖ = (94 / 231 : ℝ) := by
  norm_num [hermiteVeryNearOneExteriorPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_hermiteVeryNearOneExteriorPoint_le
    (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K hermiteVeryNearOneExteriorPoint‖ ≤
      12 * ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
        (752 / 693 : ℝ) ^ (K + 1) := by
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ ≤
      ∑ j ∈ Finset.range (K + 1),
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
          (752 / 693 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc :=
        norm_iteratedDeriv_boundaryPositiveExponentialDress_veryNearOneCircle_le j N
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
        norm_hermiteVeryNearOneExterior_gap]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (94 / 231 : ℝ) ^ j ≤
          (((j.factorial : ℝ) *
              ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) /
            (3 / 8 : ℝ) ^ j) / (j.factorial : ℝ)) *
              (94 / 231 : ℝ) ^ j := by
            gcongr
        _ = ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
            (752 / 693 : ℝ) ^ j := by
          rw [show (94 / 231 : ℝ) = (3 / 8 : ℝ) * (752 / 693 : ℝ) by norm_num,
            mul_pow]
          field_simp
    _ = ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
        (∑ j ∈ Finset.range (K + 1), (752 / 693 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
        (12 * (752 / 693 : ℝ) ^ (K + 1)) := by
      gcongr
      rw [geom_sum_eq (by norm_num : (752 / 693 : ℝ) ≠ 1)]
      rw [show (752 / 693 : ℝ) - 1 = 59 / 693 by norm_num,
        div_le_iff₀ (by norm_num : (0 : ℝ) < 59 / 693)]
      have hp : (0 : ℝ) ≤ (752 / 693 : ℝ) ^ (K + 1) := by positivity
      nlinarith
    _ = 12 * ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
        (752 / 693 : ℝ) ^ (K + 1) := by ring

theorem norm_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_le
    (N K : ℕ) :
    ‖boundaryHermiteJetCounterterm N K hermiteVeryNearOneExteriorPoint‖ ≤
      12 * (N : ℝ) * (752 / 693 : ℝ) ^ (K + 1) *
        Real.exp (-(59 / 1848 : ℝ) * (N : ℝ)) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly :=
    norm_boundaryHermiteJetPolynomial_hermiteVeryNearOneExteriorPoint_le N K
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - hermiteVeryNearOneExteriorPoint.re)) =
        Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) := by
    congr 1
    norm_num [hermiteVeryNearOneExteriorPoint]
    ring
  rw [hexp]
  calc
    Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K hermiteVeryNearOneExteriorPoint‖ ≤
      Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
        (12 * ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
          (752 / 693 : ℝ) ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = 12 * (N : ℝ) * (752 / 693 : ℝ) ^ (K + 1) *
        Real.exp (-(59 / 1848 : ℝ) * (N : ℝ)) := by
      rw [show Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
          (12 * ((N : ℝ) * Real.exp ((3 / 8 : ℝ) * (N : ℝ))) *
            (752 / 693 : ℝ) ^ (K + 1)) =
        12 * (N : ℝ) * (752 / 693 : ℝ) ^ (K + 1) *
          (Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
            Real.exp ((3 / 8 : ℝ) * (N : ℝ))) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem tendsto_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_of_eventually_depth_le_three_div_eight
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ 3 * (N : ℝ) / 8) :
    Tendsto (fun N =>
      boundaryHermiteJetCounterterm N (depth N) hermiteVeryNearOneExteriorPoint)
      atTop (nhds 0) := by
  have hbaseExp : (752 / 693 : ℝ) ≤ Real.exp (1 / 12 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 / 12 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hmajor : Tendsto
      (fun N : ℕ => 14 * (N : ℝ) *
        Real.exp (-(5 / 7392 : ℝ) * (N : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
      (5 / 7392 : ℝ) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using
      h.const_mul 14
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hpow : (752 / 693 : ℝ) ^ depth N ≤
      Real.exp ((1 / 12 : ℝ) * (depth N : ℝ)) := by
    calc
      (752 / 693 : ℝ) ^ depth N ≤
          (Real.exp (1 / 12 : ℝ)) ^ depth N :=
        pow_le_pow_left₀ (by norm_num) hbaseExp _
      _ = Real.exp ((1 / 12 : ℝ) * (depth N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdepthScaled :
      (1 / 12 : ℝ) * (depth N : ℝ) ≤ (1 / 32 : ℝ) * (N : ℝ) := by
    nlinarith [hdepthN]
  have hexpDepth : Real.exp ((1 / 12 : ℝ) * (depth N : ℝ)) ≤
      Real.exp ((1 / 32 : ℝ) * (N : ℝ)) :=
    Real.exp_le_exp.mpr hdepthScaled
  have hcounter :=
    norm_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_le N (depth N)
  calc
    ‖boundaryHermiteJetCounterterm N (depth N) hermiteVeryNearOneExteriorPoint‖ ≤
      12 * (N : ℝ) * (752 / 693 : ℝ) ^ (depth N + 1) *
        Real.exp (-(59 / 1848 : ℝ) * (N : ℝ)) := hcounter
    _ = (12 * (752 / 693 : ℝ)) * (N : ℝ) *
        ((752 / 693 : ℝ) ^ depth N *
          Real.exp (-(59 / 1848 : ℝ) * (N : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ 14 * (N : ℝ) *
        (Real.exp ((1 / 32 : ℝ) * (N : ℝ)) *
          Real.exp (-(59 / 1848 : ℝ) * (N : ℝ))) := by
      have hprefactor : (12 : ℝ) * (752 / 693 : ℝ) ≤ 14 := by norm_num
      gcongr
      exact hpow.trans hexpDepth
    _ = 14 * (N : ℝ) *
        Real.exp (-(5 / 7392 : ℝ) * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Very-near-one witness closes every canonical Hermite schedule eventually below slope `3/8`. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_three_div_eight
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ 3 * (N : ℝ) / 8)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact
    no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteVeryNearOneExteriorPoint
      hkappa
      (tendsto_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_of_eventually_depth_le_three_div_eight
        hdepth)

end

end RHTower
