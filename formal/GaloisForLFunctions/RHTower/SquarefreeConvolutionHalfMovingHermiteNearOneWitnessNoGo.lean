import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteArithmeticHighDepthNoGo

/-!
# A near-one interior witness closes Hermite depths through slope `1/3`

At `s=10/11`, the shifted pole Cayley coordinate is `-6/5`.  Explicit alternating-binomial
bounds show the finite Cayley square-root factor has norm at least one once its cutoff is at least
`264`: the growing central-binomial weights have eventual ratio at least `21/20`, while the other
binomial factor is bounded away from zero.

For the moving Hermite counterterm, use the radius-`1/3` Cauchy circle about `6/11`.  The witness
gap is `4/11`, hence the Taylor ratio is `12/11`; after undoing the exponential dress,

`|c_{N,K}(10/11)| ≤ 11 N (12/11)^(K+1) exp(-N/33)`.

The rational inequality `12/11 ≤ exp(9/100)` makes this tend to zero whenever `K ≤ N/3`,
with residual exponential rate `1/3300`.  Local boundedness would instead require the counterterm
to be unbounded at the same point.  Thus every surviving canonical point-Hermite schedule must
exceed slope `1/3` infinitely often.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def tenEleventhExteriorWeight (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (3 / 10 : ℝ) ^ k

def tenEleventhNegHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * tenEleventhExteriorWeight k

def tenEleventhHalfExteriorTerm (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-6 / 5 : ℝ) ^ k

def tenEleventhHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, tenEleventhHalfExteriorTerm k

theorem tenEleventhExteriorWeight_pos (k : ℕ) :
    0 < tenEleventhExteriorWeight k := by
  unfold tenEleventhExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k) (pow_pos (by norm_num) k)

theorem tenEleventhExteriorWeight_growth {k : ℕ} (hk : 3 ≤ k) :
    (21 / 20 : ℝ) * tenEleventhExteriorWeight k ≤
      tenEleventhExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hCgrowth : (21 / 20 : ℝ) * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) * (3 / 10 : ℝ) := by
    have hkreal : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [tenEleventhExteriorWeight, tenEleventhExteriorWeight, pow_succ]
  calc
    (21 / 20 : ℝ) *
        ((Nat.centralBinom k : ℝ) * (3 / 10 : ℝ) ^ k) =
      ((21 / 20 : ℝ) * (Nat.centralBinom k : ℝ)) *
        (3 / 10 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (3 / 10 : ℝ)) *
        (3 / 10 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right hCgrowth (pow_nonneg (by norm_num) k)
    _ = (Nat.centralBinom (k + 1) : ℝ) *
        ((3 / 10 : ℝ) ^ k * (3 / 10 : ℝ)) := by ring

theorem tenEleventhExteriorWeight_ge_geometric {k : ℕ} (hk : 3 ≤ k) :
    (1 / 2 : ℝ) * (21 / 20 : ℝ) ^ (k - 3) ≤
      tenEleventhExteriorWeight k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [tenEleventhExteriorWeight, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
      rw [show k + 1 - 3 = (k - 3) + 1 by omega, pow_succ]
      calc
        (1 / 2 : ℝ) * ((21 / 20 : ℝ) ^ (k - 3) * (21 / 20 : ℝ)) =
            ((1 / 2 : ℝ) * (21 / 20 : ℝ) ^ (k - 3)) *
              (21 / 20 : ℝ) := by ring
        _ ≤ tenEleventhExteriorWeight k * (21 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (21 / 20 : ℝ) * tenEleventhExteriorWeight k := by ring
        _ ≤ tenEleventhExteriorWeight (k + 1) :=
          tenEleventhExteriorWeight_growth hk

theorem tenEleventhHalfExteriorTerm_neg {k : ℕ} (hk : 1 ≤ k) :
    tenEleventhHalfExteriorTerm k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [tenEleventhHalfExteriorTerm]
  | succ k hk ih =>
      have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : tenEleventhHalfExteriorTerm (k + 1) =
          tenEleventhHalfExteriorTerm k *
            ((6 / 5 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold tenEleventhHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih
        (div_pos (mul_pos (by norm_num) hkpos) hk1)

theorem tenEleventhHalfExteriorTerm_succ (k : ℕ) :
    tenEleventhHalfExteriorTerm (k + 1) =
      tenEleventhHalfExteriorTerm k *
        ((6 / 5 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
      Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hk1)]
    simpa [mul_comm] using hrec
  unfold tenEleventhHalfExteriorTerm
  rw [hchoose, pow_succ]
  ring

theorem tenEleventhHalfExteriorSum_six_le_neg_one_div_hundred :
    tenEleventhHalfExteriorSum 6 ≤ (-1 / 100 : ℝ) := by
  rw [show tenEleventhHalfExteriorSum 6 =
      tenEleventhHalfExteriorTerm 0 + tenEleventhHalfExteriorTerm 1 +
      tenEleventhHalfExteriorTerm 2 + tenEleventhHalfExteriorTerm 3 +
      tenEleventhHalfExteriorTerm 4 + tenEleventhHalfExteriorTerm 5 by
    norm_num [tenEleventhHalfExteriorSum, Finset.sum_range_succ]]
  rw [tenEleventhHalfExteriorTerm_succ 4, tenEleventhHalfExteriorTerm_succ 3,
    tenEleventhHalfExteriorTerm_succ 2, tenEleventhHalfExteriorTerm_succ 1,
    tenEleventhHalfExteriorTerm_succ 0]
  norm_num [tenEleventhHalfExteriorTerm]

private theorem tenEleventhNegHalfExteriorSum_base :
    ((tenEleventhExteriorWeight 14) / 21 ≤ tenEleventhNegHalfExteriorSum 15 ∧
      tenEleventhNegHalfExteriorSum 15 ≤ tenEleventhExteriorWeight 14) ∧
    (-tenEleventhExteriorWeight 15 ≤ tenEleventhNegHalfExteriorSum 16 ∧
      tenEleventhNegHalfExteriorSum 16 ≤ -tenEleventhExteriorWeight 15 / 21) := by
  norm_num [tenEleventhNegHalfExteriorSum, tenEleventhExteriorWeight,
    Nat.centralBinom, Nat.choose, Finset.sum_range_succ]

theorem tenEleventhHalfExteriorSum_le_neg_one_div_hundred
    {N : ℕ} (hN : 6 ≤ N) :
    tenEleventhHalfExteriorSum N ≤ (-1 / 100 : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => exact tenEleventhHalfExteriorSum_six_le_neg_one_div_hundred
  | succ N hN ih =>
      rw [tenEleventhHalfExteriorSum, Finset.sum_range_succ,
        ← tenEleventhHalfExteriorSum]
      exact (add_le_of_nonpos_right
        (le_of_lt (tenEleventhHalfExteriorTerm_neg (by omega)))).trans ih

theorem tenEleventhNegHalfExteriorSum_bounds {m : ℕ} (hm : 7 ≤ m) :
    ((tenEleventhExteriorWeight (2 * m)) / 21 ≤
        tenEleventhNegHalfExteriorSum (2 * m + 1) ∧
      tenEleventhNegHalfExteriorSum (2 * m + 1) ≤
        tenEleventhExteriorWeight (2 * m)) ∧
    (-tenEleventhExteriorWeight (2 * m + 1) ≤
        tenEleventhNegHalfExteriorSum (2 * m + 2) ∧
      tenEleventhNegHalfExteriorSum (2 * m + 2) ≤
        -tenEleventhExteriorWeight (2 * m + 1) / 21) := by
  induction m, hm using Nat.le_induction with
  | base => exact tenEleventhNegHalfExteriorSum_base
  | succ m hm ih =>
      rcases ih with ⟨hodd, heven⟩
      have hg1 := tenEleventhExteriorWeight_growth
        (show 3 ≤ 2 * m + 1 by omega)
      have hg2 := tenEleventhExteriorWeight_growth
        (show 3 ≤ 2 * m + 2 by omega)
      have hp1 := tenEleventhExteriorWeight_pos (2 * m + 1)
      have hp2 := tenEleventhExteriorWeight_pos (2 * m + 2)
      have hp3 := tenEleventhExteriorWeight_pos (2 * m + 3)
      have hsodd : tenEleventhNegHalfExteriorSum (2 * (m + 1) + 1) =
          tenEleventhNegHalfExteriorSum (2 * m + 2) +
            tenEleventhExteriorWeight (2 * m + 2) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          tenEleventhNegHalfExteriorSum, Finset.sum_range_succ]
        have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
          rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
          norm_num
        rw [he, one_mul]
        rfl
      have hseven : tenEleventhNegHalfExteriorSum (2 * (m + 1) + 2) =
          tenEleventhNegHalfExteriorSum (2 * (m + 1) + 1) -
            tenEleventhExteriorWeight (2 * m + 3) := by
        rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
          tenEleventhNegHalfExteriorSum, Finset.sum_range_succ]
        have ho : (-1 : ℝ) ^ (2 * (m + 1) + 1) = -1 := by
          rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl,
            pow_add, pow_mul]
          norm_num
        rw [ho, neg_one_mul]
        unfold tenEleventhNegHalfExteriorSum
        congr 2
      have hnewodd :
          tenEleventhExteriorWeight (2 * (m + 1)) / 21 ≤
              tenEleventhNegHalfExteriorSum (2 * (m + 1) + 1) ∧
            tenEleventhNegHalfExteriorSum (2 * (m + 1) + 1) ≤
              tenEleventhExteriorWeight (2 * (m + 1)) := by
        rw [hsodd]
        rcases heven with ⟨hevenlo, hevenhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hevenlo hevenhi ⊢
        constructor <;> nlinarith
      have hneweven :
          -tenEleventhExteriorWeight (2 * (m + 1) + 1) ≤
              tenEleventhNegHalfExteriorSum (2 * (m + 1) + 2) ∧
            tenEleventhNegHalfExteriorSum (2 * (m + 1) + 2) ≤
              -tenEleventhExteriorWeight (2 * (m + 1) + 1) / 21 := by
        rw [hseven]
        rcases hnewodd with ⟨hnewoddlo, hnewoddhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hnewoddlo hnewoddhi ⊢
        constructor <;> nlinarith
      exact ⟨hnewodd, hneweven⟩

private theorem tenEleventhBinomialPartialSum_eq_sum_choose_real
    (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_tenEleventhHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-6 / 5 : ℂ) =
      (tenEleventhHalfExteriorSum N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show (-6 / 5 : ℂ) = ((-6 / 5 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    tenEleventhBinomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_tenEleventhNegHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (6 / 5 : ℂ) =
      (tenEleventhNegHalfExteriorSum N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (6 / 5 : ℂ) = ((6 / 5 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    tenEleventhBinomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold tenEleventhNegHalfExteriorSum tenEleventhExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [GaloisForLFunctions.choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * (6 / 5 : ℝ) ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * (6 / 5 : ℝ) ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * (6 / 5 : ℝ)) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          (3 / 10 : ℝ) ^ k := by norm_num
  ring

/-- Near-one interior witness; its pole Cayley coordinate is `-6/5`. -/
def hermiteNearOneExteriorPoint : ℂ := (10 / 11 : ℂ)

@[simp] theorem poleFactorCayley_hermiteNearOneExteriorPoint :
    poleFactorCayley hermiteNearOneExteriorPoint = (-6 / 5 : ℂ) := by
  norm_num [hermiteNearOneExteriorPoint, poleFactorCayley,
    GaloisForLFunctions.HTGeometry.cayleyRight]

theorem hermiteNearOneExteriorPoint_mem_rightHalf :
    hermiteNearOneExteriorPoint ∈ rightHalf := by
  rw [mem_rightHalf]
  norm_num [hermiteNearOneExteriorPoint]

theorem norm_tenEleventhHalfExteriorPartialSum_ge_one_div_hundred
    {N : ℕ} (hN : 6 ≤ N) :
    (1 / 100 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-6 / 5 : ℂ)‖ := by
  rw [complex_tenEleventhHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hsum := tenEleventhHalfExteriorSum_le_neg_one_div_hundred hN
  rw [abs_of_nonpos (hsum.trans (by norm_num))]
  linarith

theorem norm_tenEleventhNegHalfExteriorPartialSum_odd_ge
    (m : ℕ) (hm : 7 ≤ m) :
    (21 / 20 : ℝ) ^ (2 * m - 3) / 42 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum
        (2 * m + 1) (6 / 5 : ℂ)‖ := by
  rw [complex_tenEleventhNegHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (tenEleventhNegHalfExteriorSum_bounds hm).1
  have hgeom := tenEleventhExteriorWeight_ge_geometric
    (show 3 ≤ 2 * m by omega)
  have hnonneg : 0 ≤ tenEleventhNegHalfExteriorSum (2 * m + 1) := by
    linarith [tenEleventhExteriorWeight_pos (2 * m)]
  rw [abs_of_nonneg hnonneg]
  calc
    (21 / 20 : ℝ) ^ (2 * m - 3) / 42 =
        ((1 / 2 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 3)) / 21 := by ring
    _ ≤ tenEleventhExteriorWeight (2 * m) / 21 :=
      div_le_div_of_nonneg_right hgeom (by norm_num)
    _ ≤ _ := hbounds.1

theorem norm_tenEleventhNegHalfExteriorPartialSum_even_ge
    (m : ℕ) (hm : 7 ≤ m) :
    (21 / 20 : ℝ) ^ (2 * m - 2) / 42 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum
        (2 * m + 2) (6 / 5 : ℂ)‖ := by
  rw [complex_tenEleventhNegHalfExteriorPartialSum_eq,
    Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (tenEleventhNegHalfExteriorSum_bounds hm).2
  have hgeom := tenEleventhExteriorWeight_ge_geometric
    (show 3 ≤ 2 * m + 1 by omega)
  have hnonpos : tenEleventhNegHalfExteriorSum (2 * m + 2) ≤ 0 := by
    linarith [tenEleventhExteriorWeight_pos (2 * m + 1)]
  rw [abs_of_nonpos hnonpos]
  calc
    (21 / 20 : ℝ) ^ (2 * m - 2) / 42 =
        ((1 / 2 : ℝ) * (21 / 20 : ℝ) ^ (2 * m - 2)) / 21 := by ring
    _ ≤ tenEleventhExteriorWeight (2 * m + 1) / 21 :=
      div_le_div_of_nonneg_right hgeom (by norm_num)
    _ ≤ _ := by linarith [hbounds.2]

theorem norm_poleFactorSqrtApprox_hermiteNearOneExteriorPoint_geometric
    {N : ℕ} (hN : 15 ≤ N) :
    (21 / 20 : ℝ) ^ (N - 4) / 4200 ≤
      ‖poleFactorSqrtApprox N hermiteNearOneExteriorPoint‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm : 7 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    have hhalf : (1 / 100 : ℝ) ≤
        ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum
          (2 * (k + 1)) (-(6 / 5) : ℂ)‖ := by
      simpa only [neg_div] using
        norm_tenEleventhHalfExteriorPartialSum_ge_one_div_hundred
          (show 6 ≤ 2 * (k + 1) by omega)
    have hneg : (21 / 20 : ℝ) ^ (2 * k - 2) / 42 ≤
        ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum
          (2 * k + 2) (6 / 5 : ℂ)‖ := by
      simpa only [neg_div] using
        norm_tenEleventhNegHalfExteriorPartialSum_even_ge k (by omega)
    rw [poleFactorSqrtApprox, poleFactorCayley_hermiteNearOneExteriorPoint]
    norm_num only [neg_neg]
    rw [norm_mul]
    rw [show 2 * (k + 1) - 4 = 2 * k - 2 by omega]
    calc
      (21 / 20 : ℝ) ^ (2 * k - 2) / 4200 =
          (1 / 100 : ℝ) * ((21 / 20 : ℝ) ^ (2 * k - 2) / 42) := by ring
      _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)
  · have hm : 7 ≤ m := by omega
    have hhalf : (1 / 100 : ℝ) ≤
        ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum
          (2 * m + 1) (-(6 / 5) : ℂ)‖ := by
      simpa only [neg_div] using
        norm_tenEleventhHalfExteriorPartialSum_ge_one_div_hundred
          (show 6 ≤ 2 * m + 1 by omega)
    have hneg : (21 / 20 : ℝ) ^ (2 * m - 3) / 42 ≤
        ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum
          (2 * m + 1) (6 / 5 : ℂ)‖ := by
      simpa only [neg_div] using
        norm_tenEleventhNegHalfExteriorPartialSum_odd_ge m hm
    rw [poleFactorSqrtApprox, poleFactorCayley_hermiteNearOneExteriorPoint]
    norm_num only [neg_neg]
    rw [norm_mul]
    rw [show 2 * m + 1 - 4 = 2 * m - 3 by omega]
    calc
      (21 / 20 : ℝ) ^ (2 * m - 3) / 4200 =
          (1 / 100 : ℝ) * ((21 / 20 : ℝ) ^ (2 * m - 3) / 42) := by ring
      _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)

theorem one_le_norm_poleFactorSqrtApprox_hermiteNearOneExteriorPoint
    {N : ℕ} (hN : 264 ≤ N) :
    1 ≤ ‖poleFactorSqrtApprox N hermiteNearOneExteriorPoint‖ := by
  have hgeom := norm_poleFactorSqrtApprox_hermiteNearOneExteriorPoint_geometric
    (show 15 ≤ N by omega)
  have hq20 : (2 : ℝ) ≤ (21 / 20 : ℝ) ^ 20 := by norm_num
  have hq260 : (2 : ℝ) ^ 13 ≤ (21 / 20 : ℝ) ^ 260 := by
    rw [show 260 = 20 * 13 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hq20 13
  have hpow : (21 / 20 : ℝ) ^ 260 ≤ (21 / 20 : ℝ) ^ (N - 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (1 : ℝ) ≤ (2 : ℝ) ^ 13 / 4200 := by norm_num
    _ ≤ (21 / 20 : ℝ) ^ 260 / 4200 :=
      div_le_div_of_nonneg_right hq260 (by norm_num)
    _ ≤ (21 / 20 : ℝ) ^ (N - 4) / 4200 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ ≤ _ := hgeom

theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteNearOneExteriorPoint :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint‖ ≤ C := by
  simpa [hermiteNearOneExteriorPoint] using
    (not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
      (sigma := (10 / 11 : ℝ)) (by norm_num) (by norm_num))

theorem counterterm_not_eventually_bounded_at_hermiteNearOneExteriorPoint_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N hermiteNearOneExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc hermiteNearOneExteriorPoint hermiteNearOneExteriorPoint_mem_rightHalf
  have hcenter : hermiteNearOneExteriorPoint ∈ ball hermiteNearOneExteriorPoint R :=
    mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        hermiteNearOneExteriorPoint‖ ≤ C :=
    fun N => hC N hermiteNearOneExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 264))
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteNearOneExteriorPoint
  let Q : ℝ := C * ‖squarefreeCarlemanHalfDet hermiteNearOneExteriorPoint‖
  refine ⟨Q + B, max N₀ M₀, fun N hN => ?_⟩
  have hNkappa : 264 ≤ kappa N := hN₀ N ((le_max_left N₀ M₀).trans hN)
  have hNM : M₀ ≤ N := (le_max_right N₀ M₀).trans hN
  have honeFactor : (1 : ℝ) ≤
      ‖poleFactorSqrtApprox (kappa N) hermiteNearOneExteriorPoint‖ :=
    one_le_norm_poleFactorSqrtApprox_hermiteNearOneExteriorPoint hNkappa
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet hermiteNearOneExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero hermiteNearOneExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) hermiteNearOneExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
            counterterm N hermiteNearOneExteriorPoint‖ ≤ Q := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hcorrected :
      ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
        counterterm N hermiteNearOneExteriorPoint‖ ≤ Q := by
    calc
      _ = 1 * ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
          counterterm N hermiteNearOneExteriorPoint‖ := by ring
      _ ≤ ‖poleFactorSqrtApprox (kappa N) hermiteNearOneExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
            counterterm N hermiteNearOneExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right honeFactor (norm_nonneg _)
      _ ≤ Q := hprod
  calc
    ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
          counterterm N hermiteNearOneExteriorPoint) -
            counterterm N hermiteNearOneExteriorPoint‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N hermiteNearOneExteriorPoint +
          counterterm N hermiteNearOneExteriorPoint‖ +
        ‖counterterm N hermiteNearOneExteriorPoint‖ := norm_sub_le _ _
    _ ≤ Q + B := add_le_add hcorrected (hB N hNM)

theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteNearOneExteriorPoint
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm :
      Tendsto (fun N => counterterm N hermiteNearOneExteriorPoint) atTop (nhds 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  apply
    (counterterm_not_eventually_bounded_at_hermiteNearOneExteriorPoint_of_cofinal_locallyBounded
      hkappa hloc)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

private theorem norm_boundaryPositiveExponentialDress_on_nearOneSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (1 / 3 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((N : ℝ) / 3) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (1 / 3 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ 1 / 3 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((N : ℝ) / 3) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ 1 / 3 :=
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

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_nearOneCircle_le
    (j N : ℕ) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) /
        (1 / 3 : ℝ) ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s
        (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num)
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_nearOneSphere_le N hw)

private theorem norm_hermiteNearOneExterior_gap :
    ‖hermiteNearOneExteriorPoint - boundaryExteriorPoint‖ = (4 / 11 : ℝ) := by
  norm_num [hermiteNearOneExteriorPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_hermiteNearOneExteriorPoint_le
    (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K hermiteNearOneExteriorPoint‖ ≤
      11 * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
        (12 / 11 : ℝ) ^ (K + 1) := by
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ ≤
      ∑ j ∈ Finset.range (K + 1),
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp ((N : ℝ) / 3)) * (12 / 11 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := norm_iteratedDeriv_boundaryPositiveExponentialDress_nearOneCircle_le j N
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
        norm_hermiteNearOneExterior_gap]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (4 / 11 : ℝ) ^ j ≤
          (((j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) /
            (1 / 3 : ℝ) ^ j) / (j.factorial : ℝ)) *
              (4 / 11 : ℝ) ^ j := by
            gcongr
        _ = ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
            (12 / 11 : ℝ) ^ j := by
          rw [show (4 / 11 : ℝ) = (1 / 3 : ℝ) * (12 / 11 : ℝ) by norm_num,
            mul_pow]
          field_simp
    _ = ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
        (∑ j ∈ Finset.range (K + 1), (12 / 11 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
        (11 * (12 / 11 : ℝ) ^ (K + 1)) := by
      gcongr
      rw [geom_sum_eq (by norm_num : (12 / 11 : ℝ) ≠ 1)]
      have hp : (0 : ℝ) ≤ (12 / 11 : ℝ) ^ (K + 1) := by positivity
      norm_num at *
      nlinarith
    _ = 11 * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
        (12 / 11 : ℝ) ^ (K + 1) := by ring

theorem norm_boundaryHermiteJetCounterterm_hermiteNearOneExteriorPoint_le
    (N K : ℕ) :
    ‖boundaryHermiteJetCounterterm N K hermiteNearOneExteriorPoint‖ ≤
      11 * (N : ℝ) * (12 / 11 : ℝ) ^ (K + 1) *
        Real.exp (-(1 / 33 : ℝ) * (N : ℝ)) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly :=
    norm_boundaryHermiteJetPolynomial_hermiteNearOneExteriorPoint_le N K
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - hermiteNearOneExteriorPoint.re)) =
        Real.exp (-(4 / 11 : ℝ) * (N : ℝ)) := by
    congr 1
    norm_num [hermiteNearOneExteriorPoint]
    ring
  rw [hexp]
  calc
    Real.exp (-(4 / 11 : ℝ) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K hermiteNearOneExteriorPoint‖ ≤
      Real.exp (-(4 / 11 : ℝ) * (N : ℝ)) *
        (11 * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
          (12 / 11 : ℝ) ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = 11 * (N : ℝ) * (12 / 11 : ℝ) ^ (K + 1) *
        Real.exp (-(1 / 33 : ℝ) * (N : ℝ)) := by
      rw [show Real.exp (-(4 / 11 : ℝ) * (N : ℝ)) *
          (11 * ((N : ℝ) * Real.exp ((N : ℝ) / 3)) *
            (12 / 11 : ℝ) ^ (K + 1)) =
        11 * (N : ℝ) * (12 / 11 : ℝ) ^ (K + 1) *
          (Real.exp (-(4 / 11 : ℝ) * (N : ℝ)) *
            Real.exp ((N : ℝ) / 3)) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem tendsto_boundaryHermiteJetCounterterm_hermiteNearOneExteriorPoint_of_eventually_depth_le_one_div_three
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 3) :
    Tendsto (fun N =>
      boundaryHermiteJetCounterterm N (depth N) hermiteNearOneExteriorPoint)
      atTop (nhds 0) := by
  have hbaseExp : (12 / 11 : ℝ) ≤ Real.exp (9 / 100 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (x := (9 / 100 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hmajor : Tendsto
      (fun N : ℕ => 12 * (N : ℝ) *
        Real.exp (-(1 / 3300 : ℝ) * (N : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
      (1 / 3300 : ℝ) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using
      h.const_mul 12
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hpow : (12 / 11 : ℝ) ^ depth N ≤
      Real.exp ((9 / 100 : ℝ) * (depth N : ℝ)) := by
    calc
      (12 / 11 : ℝ) ^ depth N ≤
          (Real.exp (9 / 100 : ℝ)) ^ depth N :=
        pow_le_pow_left₀ (by norm_num) hbaseExp _
      _ = Real.exp ((9 / 100 : ℝ) * (depth N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdepthScaled :
      (9 / 100 : ℝ) * (depth N : ℝ) ≤ (3 / 100 : ℝ) * (N : ℝ) := by
    nlinarith [hdepthN]
  have hexpDepth : Real.exp ((9 / 100 : ℝ) * (depth N : ℝ)) ≤
      Real.exp ((3 / 100 : ℝ) * (N : ℝ)) :=
    Real.exp_le_exp.mpr hdepthScaled
  have hcounter :=
    norm_boundaryHermiteJetCounterterm_hermiteNearOneExteriorPoint_le N (depth N)
  calc
    ‖boundaryHermiteJetCounterterm N (depth N) hermiteNearOneExteriorPoint‖ ≤
      11 * (N : ℝ) * (12 / 11 : ℝ) ^ (depth N + 1) *
        Real.exp (-(1 / 33 : ℝ) * (N : ℝ)) := hcounter
    _ = 12 * (N : ℝ) *
        ((12 / 11 : ℝ) ^ depth N *
          Real.exp (-(1 / 33 : ℝ) * (N : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ 12 * (N : ℝ) *
        (Real.exp ((3 / 100 : ℝ) * (N : ℝ)) *
          Real.exp (-(1 / 33 : ℝ) * (N : ℝ))) := by
      gcongr
      exact hpow.trans hexpDepth
    _ = 12 * (N : ℝ) *
        Real.exp (-(1 / 3300 : ℝ) * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Near-one witness closes every canonical Hermite schedule eventually below slope `1/3`. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_one_div_three
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 3)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact
    no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteNearOneExteriorPoint
      hkappa
      (tendsto_boundaryHermiteJetCounterterm_hermiteNearOneExteriorPoint_of_eventually_depth_le_one_div_three
        hdepth)

end

end RHTower
