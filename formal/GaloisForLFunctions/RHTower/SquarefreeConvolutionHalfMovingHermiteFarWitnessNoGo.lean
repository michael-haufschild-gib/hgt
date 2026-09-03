import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteNoGo

/-!
# A farther interior witness closes Hermite depths through slope `1/15`

The point `s=2/3` has Cayley coordinate `-2`.  At this rational coordinate, both binomial factors
of the Cayley square-root approximant have explicit alternating real sums.  Their weights grow at
least geometrically, giving a uniform lower bound on the Cayley factor at all sufficiently large
degrees.  Consequently local boundedness of a corrected full approximant still forces its
counterterm to be unbounded at `2/3`.

For the moving Hermite counterterm, Cauchy's estimate on the radius-`1/22` circle around `6/11`
gives the pointwise envelope

`N * 3^(K+1) * exp(-5N/66)`.

Since `3 < exp(11/10)`, this tends to zero whenever `K <= N/15`, contradicting the required
unboundedness.  Thus any surviving point-Hermite schedule must exceed slope `1/15` infinitely
often.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def twoThirdExteriorWeight (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) * (1 / 2 : ℝ) ^ k

def twoThirdNegHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * twoThirdExteriorWeight k

def twoThirdHalfExteriorTerm (k : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) k * (-2 : ℝ) ^ k

def twoThirdHalfExteriorSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, twoThirdHalfExteriorTerm k

@[simp] theorem twoThirdExteriorWeight_zero : twoThirdExteriorWeight 0 = 1 := by
  simp [twoThirdExteriorWeight]

theorem twoThirdExteriorWeight_pos (k : ℕ) : 0 < twoThirdExteriorWeight k := by
  unfold twoThirdExteriorWeight
  exact mul_pos (by exact_mod_cast Nat.centralBinom_pos k) (pow_pos (by norm_num) k)

theorem twoThirdExteriorWeight_growth {k : ℕ} (hk : 1 ≤ k) :
    (3 / 2 : ℝ) * twoThirdExteriorWeight k ≤ twoThirdExteriorWeight (k + 1) := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hCpos : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos k
  have hCgrowth : 3 * (Nat.centralBinom k : ℝ) ≤
      (Nat.centralBinom (k + 1) : ℝ) := by
    nlinarith
  rw [twoThirdExteriorWeight, twoThirdExteriorWeight, pow_succ]
  calc
    (3 / 2 : ℝ) * ((Nat.centralBinom k : ℝ) * (1 / 2 : ℝ) ^ k) =
        ((3 / 2 : ℝ) * (Nat.centralBinom k : ℝ)) * (1 / 2 : ℝ) ^ k := by ring
    _ ≤ ((Nat.centralBinom (k + 1) : ℝ) * (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) k)
      nlinarith
    _ = (Nat.centralBinom (k + 1) : ℝ) *
        ((1 / 2 : ℝ) ^ k * (1 / 2 : ℝ)) := by ring

theorem twoThirdExteriorWeight_ge_geometric {k : ℕ} (hk : 1 ≤ k) :
    (3 / 2 : ℝ) ^ (k - 1) ≤ twoThirdExteriorWeight k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [twoThirdExteriorWeight, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
      change (3 / 2 : ℝ) ^ k ≤ twoThirdExteriorWeight (k + 1)
      calc
        (3 / 2 : ℝ) ^ k = (3 / 2 : ℝ) ^ (k - 1) * (3 / 2 : ℝ) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        _ ≤
            twoThirdExteriorWeight k * (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (3 / 2 : ℝ) * twoThirdExteriorWeight k := by ring
        _ ≤ twoThirdExteriorWeight (k + 1) := twoThirdExteriorWeight_growth hk

theorem twoThirdNegHalfExteriorSum_bounds {m : ℕ} (hm : 1 ≤ m) :
    ((twoThirdExteriorWeight (2 * m)) / 3 ≤ twoThirdNegHalfExteriorSum (2 * m + 1) ∧
      twoThirdNegHalfExteriorSum (2 * m + 1) ≤ twoThirdExteriorWeight (2 * m)) ∧
    (-twoThirdExteriorWeight (2 * m + 1) ≤ twoThirdNegHalfExteriorSum (2 * m + 2) ∧
      twoThirdNegHalfExteriorSum (2 * m + 2) ≤
        -twoThirdExteriorWeight (2 * m + 1) / 3) := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num [twoThirdNegHalfExteriorSum, twoThirdExteriorWeight, Nat.centralBinom,
        Nat.choose, Finset.sum_range_succ]
  | succ m hm ih =>
      rcases ih with ⟨hodd, heven⟩
      have hg1 := twoThirdExteriorWeight_growth (show 1 ≤ 2 * m + 1 by omega)
      have hg2 := twoThirdExteriorWeight_growth (show 1 ≤ 2 * m + 2 by omega)
      have hp1 := twoThirdExteriorWeight_pos (2 * m + 1)
      have hp2 := twoThirdExteriorWeight_pos (2 * m + 2)
      have hp3 := twoThirdExteriorWeight_pos (2 * m + 3)
      have hsodd : twoThirdNegHalfExteriorSum (2 * (m + 1) + 1) =
          twoThirdNegHalfExteriorSum (2 * m + 2) + twoThirdExteriorWeight (2 * m + 2) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          twoThirdNegHalfExteriorSum, Finset.sum_range_succ]
        have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
          rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
          norm_num
        rw [he, one_mul]
        rfl
      have hseven : twoThirdNegHalfExteriorSum (2 * (m + 1) + 2) =
          twoThirdNegHalfExteriorSum (2 * (m + 1) + 1) -
            twoThirdExteriorWeight (2 * m + 3) := by
        rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
          twoThirdNegHalfExteriorSum, Finset.sum_range_succ]
        have ho : (-1 : ℝ) ^ (2 * (m + 1) + 1) = -1 := by
          rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl, pow_add, pow_mul]
          norm_num
        rw [ho, neg_one_mul]
        unfold twoThirdNegHalfExteriorSum
        congr 2
      have hnewodd :
          twoThirdExteriorWeight (2 * (m + 1)) / 3 ≤
              twoThirdNegHalfExteriorSum (2 * (m + 1) + 1) ∧
            twoThirdNegHalfExteriorSum (2 * (m + 1) + 1) ≤
              twoThirdExteriorWeight (2 * (m + 1)) := by
        rw [hsodd]
        simp only [Nat.mul_add, Nat.mul_one]
        constructor <;> nlinarith
      have hneweven :
          -twoThirdExteriorWeight (2 * (m + 1) + 1) ≤
              twoThirdNegHalfExteriorSum (2 * (m + 1) + 2) ∧
            twoThirdNegHalfExteriorSum (2 * (m + 1) + 2) ≤
              -twoThirdExteriorWeight (2 * (m + 1) + 1) / 3 := by
        rw [hseven]
        rcases hnewodd with ⟨hnewoddlo, hnewoddhi⟩
        simp only [Nat.mul_add, Nat.mul_one] at hnewoddlo hnewoddhi ⊢
        constructor <;> nlinarith
      exact ⟨hnewodd, hneweven⟩

theorem twoThirdHalfExteriorTerm_neg {k : ℕ} (hk : 1 ≤ k) :
    twoThirdHalfExteriorTerm k < 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [twoThirdHalfExteriorTerm]
  | succ k hk ih =>
      have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by linarith
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
          Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
        rw [eq_div_iff (ne_of_gt hk1)]
        simpa [mul_comm] using hrec
      have hterm : twoThirdHalfExteriorTerm (k + 1) =
          twoThirdHalfExteriorTerm k *
            ((2 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
        unfold twoThirdHalfExteriorTerm
        rw [hchoose, pow_succ]
        ring
      rw [hterm]
      exact mul_neg_of_neg_of_pos ih (div_pos (mul_pos (by norm_num) hkpos) hk1)

theorem twoThirdHalfExteriorSum_le_neg_half {N : ℕ} (hN : 3 ≤ N) :
    twoThirdHalfExteriorSum N ≤ -1 / 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
      have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) 1
      norm_num [Ring.choose_one_right] at hrec
      norm_num [twoThirdHalfExteriorSum, twoThirdHalfExteriorTerm,
        Ring.choose_zero_right, Ring.choose_one_right, Finset.sum_range_succ]
      linarith
  | succ N hN ih =>
      rw [twoThirdHalfExteriorSum, Finset.sum_range_succ, ← twoThirdHalfExteriorSum]
      exact (add_le_of_nonpos_right
        (le_of_lt (twoThirdHalfExteriorTerm_neg (by omega)))).trans ih

private theorem twoThirdBinomialPartialSum_eq_sum_choose_real (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z =
      ∑ k ∈ Finset.range N, Ring.choose a k * z ^ k := by
  rw [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_apply, smul_eq_mul]
  simp

theorem complex_twoThirdHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-2 : ℂ) =
      (twoThirdHalfExteriorSum N : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    twoThirdBinomialPartialSum_eq_sum_choose_real]
  rfl

theorem complex_twoThirdNegHalfExteriorPartialSum_eq (N : ℕ) :
    (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (2 : ℂ) =
      (twoThirdNegHalfExteriorSum N : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    complex_binomialPartialSum_ofReal,
    twoThirdBinomialPartialSum_eq_sum_choose_real]
  congr 1
  unfold twoThirdNegHalfExteriorSum twoThirdExteriorWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [GaloisForLFunctions.choose_neg_half]
  calc
    (-1 : ℝ) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k * (2 : ℝ) ^ k =
        (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k := by ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k *
          ((4 : ℝ)⁻¹ * 2) ^ k := by
      rw [← inv_pow, mul_pow]
      ring
    _ = (Nat.centralBinom k : ℝ) * (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
      norm_num
  ring

/-- Farther rational interior witness, with Cayley coordinate exactly `-2`. -/
def hermiteFarExteriorPoint : ℂ := (2 / 3 : ℂ)

@[simp] theorem poleFactorCayley_hermiteFarExteriorPoint :
    poleFactorCayley hermiteFarExteriorPoint = (-2 : ℂ) := by
  norm_num [hermiteFarExteriorPoint, poleFactorCayley,
    GaloisForLFunctions.HTGeometry.cayleyRight]

theorem hermiteFarExteriorPoint_mem_rightHalf : hermiteFarExteriorPoint ∈ rightHalf := by
  rw [mem_rightHalf]
  norm_num [hermiteFarExteriorPoint]

theorem norm_twoThirdHalfExteriorPartialSum_ge_half {N : ℕ} (hN : 3 ≤ N) :
    (1 / 2 : ℝ) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-2 : ℂ)‖ := by
  rw [complex_twoThirdHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hsum := twoThirdHalfExteriorSum_le_neg_half hN
  rw [abs_of_nonpos (hsum.trans (by norm_num))]
  linarith

theorem norm_twoThirdNegHalfExteriorPartialSum_odd_ge (m : ℕ) (hm : 1 ≤ m) :
    (3 / 2 : ℝ) ^ (2 * m - 1) / 3 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 1) (2 : ℂ)‖ := by
  rw [complex_twoThirdNegHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (twoThirdNegHalfExteriorSum_bounds hm).1
  have hgeom := twoThirdExteriorWeight_ge_geometric (show 1 ≤ 2 * m by omega)
  have hnonneg : 0 ≤ twoThirdNegHalfExteriorSum (2 * m + 1) := by
    linarith [twoThirdExteriorWeight_pos (2 * m)]
  rw [abs_of_nonneg hnonneg]
  exact (div_le_div_of_nonneg_right hgeom (by norm_num)).trans hbounds.1

theorem norm_twoThirdNegHalfExteriorPartialSum_even_ge (m : ℕ) (hm : 1 ≤ m) :
    (3 / 2 : ℝ) ^ (2 * m) / 3 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum (2 * m + 2) (2 : ℂ)‖ := by
  rw [complex_twoThirdNegHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hbounds := (twoThirdNegHalfExteriorSum_bounds hm).2
  have hgeom := twoThirdExteriorWeight_ge_geometric (show 1 ≤ 2 * m + 1 by omega)
  have hnonpos : twoThirdNegHalfExteriorSum (2 * m + 2) ≤ 0 := by
    linarith [twoThirdExteriorWeight_pos (2 * m + 1)]
  rw [abs_of_nonpos hnonpos]
  have hweight : (3 / 2 : ℝ) ^ (2 * m) / 3 ≤
      twoThirdExteriorWeight (2 * m + 1) / 3 :=
    div_le_div_of_nonneg_right hgeom (by norm_num)
  linarith [hbounds.2]

theorem norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_odd_ge
    (m : ℕ) (hm : 1 ≤ m) :
    (3 / 2 : ℝ) ^ (2 * m - 1) / 6 ≤
      ‖poleFactorSqrtApprox (2 * m + 1) hermiteFarExteriorPoint‖ := by
  have hhalf := norm_twoThirdHalfExteriorPartialSum_ge_half
    (show 3 ≤ 2 * m + 1 by omega)
  have hneg : (3 / 2 : ℝ) ^ (2 * m - 1) / 3 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 1) (2 : ℂ)‖ := by
    simpa only [neg_div] using norm_twoThirdNegHalfExteriorPartialSum_odd_ge m hm
  rw [poleFactorSqrtApprox, poleFactorCayley_hermiteFarExteriorPoint]
  norm_num only [neg_neg]
  rw [norm_mul]
  calc
    (3 / 2 : ℝ) ^ (2 * m - 1) / 6 =
        (1 / 2 : ℝ) * ((3 / 2 : ℝ) ^ (2 * m - 1) / 3) := by ring
    _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)

theorem norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_even_ge (m : ℕ) (hm : 1 ≤ m) :
    (3 / 2 : ℝ) ^ (2 * m) / 6 ≤
      ‖poleFactorSqrtApprox (2 * m + 2) hermiteFarExteriorPoint‖ := by
  have hhalf := norm_twoThirdHalfExteriorPartialSum_ge_half
    (show 3 ≤ 2 * m + 2 by omega)
  have hneg : (3 / 2 : ℝ) ^ (2 * m) / 3 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum (2 * m + 2) (2 : ℂ)‖ := by
    simpa only [neg_div] using norm_twoThirdNegHalfExteriorPartialSum_even_ge m hm
  rw [poleFactorSqrtApprox, poleFactorCayley_hermiteFarExteriorPoint]
  norm_num only [neg_neg]
  rw [norm_mul]
  calc
    (3 / 2 : ℝ) ^ (2 * m) / 6 =
        (1 / 2 : ℝ) * ((3 / 2 : ℝ) ^ (2 * m) / 3) := by ring
    _ ≤ _ := mul_le_mul hhalf hneg (by positivity) (by positivity)

theorem norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_geometric
    {N : ℕ} (hN : 3 ≤ N) :
    (3 / 2 : ℝ) ^ (N - 2) / 6 ≤
      ‖poleFactorSqrtApprox N hermiteFarExteriorPoint‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    rw [show 2 * (k + 1) - 2 = 2 * k by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega]
    exact norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_even_ge k (by omega)
  · have hm1 : 1 ≤ m := by omega
    rw [show 2 * m + 1 - 2 = 2 * m - 1 by omega]
    exact norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_odd_ge m hm1

theorem one_le_norm_poleFactorSqrtApprox_hermiteFarExteriorPoint
    {N : ℕ} (hN : 8 ≤ N) :
    1 ≤ ‖poleFactorSqrtApprox N hermiteFarExteriorPoint‖ := by
  have hgeom := norm_poleFactorSqrtApprox_hermiteFarExteriorPoint_geometric
    (show 3 ≤ N by omega)
  have hpow : (3 / 2 : ℝ) ^ 6 ≤ (3 / 2 : ℝ) ^ (N - 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    (1 : ℝ) ≤ (3 / 2 : ℝ) ^ 6 / 6 := by norm_num
    _ ≤ (3 / 2 : ℝ) ^ (N - 2) / 6 :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    _ ≤ _ := hgeom

theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteFarExteriorPoint :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint‖ ≤ C := by
  simpa [hermiteFarExteriorPoint] using
    (not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
      (sigma := (2 / 3 : ℝ)) (by norm_num) (by norm_num))

theorem counterterm_not_eventually_bounded_at_hermiteFarExteriorPoint_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N hermiteFarExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc hermiteFarExteriorPoint hermiteFarExteriorPoint_mem_rightHalf
  have hcenter : hermiteFarExteriorPoint ∈ ball hermiteFarExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        hermiteFarExteriorPoint‖ ≤ C :=
    fun N => hC N hermiteFarExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 8))
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_hermiteFarExteriorPoint
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet hermiteFarExteriorPoint‖
  refine ⟨K + B, max N₀ M₀, fun N hN => ?_⟩
  have hNkappa : 8 ≤ kappa N := hN₀ N ((le_max_left N₀ M₀).trans hN)
  have hNM : M₀ ≤ N := (le_max_right N₀ M₀).trans hN
  have honeFactor : (1 : ℝ) ≤
      ‖poleFactorSqrtApprox (kappa N) hermiteFarExteriorPoint‖ :=
    one_le_norm_poleFactorSqrtApprox_hermiteFarExteriorPoint hNkappa
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet hermiteFarExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero hermiteFarExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) hermiteFarExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
            counterterm N hermiteFarExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hcorrected :
      ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
        counterterm N hermiteFarExteriorPoint‖ ≤ K := by
    calc
      _ = 1 * ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
          counterterm N hermiteFarExteriorPoint‖ := by ring
      _ ≤ ‖poleFactorSqrtApprox (kappa N) hermiteFarExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
            counterterm N hermiteFarExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right honeFactor (norm_nonneg _)
      _ ≤ K := hprod
  calc
    ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
          counterterm N hermiteFarExteriorPoint) -
            counterterm N hermiteFarExteriorPoint‖ := by ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N hermiteFarExteriorPoint +
          counterterm N hermiteFarExteriorPoint‖ +
        ‖counterterm N hermiteFarExteriorPoint‖ := norm_sub_le _ _
    _ ≤ K + B := add_le_add hcorrected (hB N hNM)

theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteFarExteriorPoint
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm :
      Tendsto (fun N => counterterm N hermiteFarExteriorPoint) atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  apply (counterterm_not_eventually_bounded_at_hermiteFarExteriorPoint_of_cofinal_locallyBounded
    hkappa hloc)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

private theorem norm_boundaryPositiveExponentialDress_on_wideSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (1 / 22 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((N : ℝ) / 22) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (1 / 22 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ 1 / 22 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((N : ℝ) / 22) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ 1 / 22 :=
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

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_wideCircle_le
    (j N : ℕ) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 22)) /
        (1 / 22 : ℝ) ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num)
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_wideSphere_le N hw)

private theorem norm_hermiteFarExterior_gap :
    ‖hermiteFarExteriorPoint - boundaryExteriorPoint‖ = (4 / 33 : ℝ) := by
  norm_num [hermiteFarExteriorPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_hermiteFarExteriorPoint_le (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K hermiteFarExteriorPoint‖ ≤
      ((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ (K + 1) := by
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteFarExteriorPoint - boundaryExteriorPoint) ^ j‖ ≤
        ∑ j ∈ Finset.range (K + 1),
          ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
              (j.factorial : ℂ) *
            (hermiteFarExteriorPoint - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := norm_iteratedDeriv_boundaryPositiveExponentialDress_wideCircle_le j N
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      have hbase : (8 / 3 : ℝ) ^ j ≤ 3 ^ j :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) j
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, norm_hermiteFarExterior_gap]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (4 / 33 : ℝ) ^ j ≤
            (((j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 22)) /
              (1 / 22 : ℝ) ^ j) / (j.factorial : ℝ)) * (4 / 33 : ℝ) ^ j := by
          gcongr
        _ = ((N : ℝ) * Real.exp ((N : ℝ) / 22)) * (8 / 3 : ℝ) ^ j := by
          rw [show (4 / 33 : ℝ) = (1 / 22 : ℝ) * (8 / 3 : ℝ) by norm_num,
            mul_pow]
          field_simp
        _ ≤ ((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ j :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((N : ℝ) * Real.exp ((N : ℝ) / 22)) *
        (∑ j ∈ Finset.range (K + 1), (3 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ (K + 1) := by
      gcongr
      rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1)]
      have hp : (0 : ℝ) ≤ 3 ^ (K + 1) := by positivity
      nlinarith

theorem norm_boundaryHermiteJetCounterterm_hermiteFarExteriorPoint_le (N K : ℕ) :
    ‖boundaryHermiteJetCounterterm N K hermiteFarExteriorPoint‖ ≤
      (N : ℝ) * 3 ^ (K + 1) * Real.exp (-(5 / 66 : ℝ) * (N : ℝ)) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly := norm_boundaryHermiteJetPolynomial_hermiteFarExteriorPoint_le N K
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - hermiteFarExteriorPoint.re)) =
        Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) := by
    congr 1
    norm_num [hermiteFarExteriorPoint]
    ring
  rw [hexp]
  calc
    Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K hermiteFarExteriorPoint‖ ≤
      Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) *
        (((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = (N : ℝ) * 3 ^ (K + 1) * Real.exp (-(5 / 66 : ℝ) * (N : ℝ)) := by
      have hexpCombine :
          Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) * Real.exp ((N : ℝ) / 22) =
            Real.exp (-(5 / 66 : ℝ) * (N : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) *
          (((N : ℝ) * Real.exp ((N : ℝ) / 22)) * 3 ^ (K + 1)) =
          (N : ℝ) * 3 ^ (K + 1) *
            (Real.exp (-(4 / 33 : ℝ) * (N : ℝ)) * Real.exp ((N : ℝ) / 22)) by ring,
        hexpCombine]

theorem tendsto_boundaryHermiteJetCounterterm_hermiteFarExteriorPoint_of_eventually_depth_le_one_div_15
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 15) :
    Tendsto (fun N => boundaryHermiteJetCounterterm N (depth N) hermiteFarExteriorPoint)
      atTop (𝓝 0) := by
  have hthreeexp : (3 : ℝ) ≤ Real.exp (11 / 10 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (x := (11 / 10 : ℝ)) (by norm_num) 6
    norm_num at h ⊢
    linarith
  have hmajor : Tendsto
      (fun N : ℕ => 3 * (N : ℝ) * Real.exp (-(2 / 825 : ℝ) * (N : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 / 825 : ℝ)
      (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero, zero_mul, mul_assoc, mul_left_comm,
      mul_comm] using h.const_mul 3
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hpow : (3 : ℝ) ^ depth N ≤
      Real.exp ((11 / 10 : ℝ) * (depth N : ℝ)) := by
    calc
      (3 : ℝ) ^ depth N ≤ (Real.exp (11 / 10 : ℝ)) ^ depth N :=
        pow_le_pow_left₀ (by norm_num) hthreeexp _
      _ = Real.exp ((11 / 10 : ℝ) * (depth N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdepthScaled :
      (11 / 10 : ℝ) * (depth N : ℝ) ≤ 11 * (N : ℝ) / 150 := by
    nlinarith [hdepthN]
  have hexpDepth : Real.exp ((11 / 10 : ℝ) * (depth N : ℝ)) ≤
      Real.exp (11 * (N : ℝ) / 150) := Real.exp_le_exp.mpr hdepthScaled
  have hcounter :=
    norm_boundaryHermiteJetCounterterm_hermiteFarExteriorPoint_le N (depth N)
  calc
    ‖boundaryHermiteJetCounterterm N (depth N) hermiteFarExteriorPoint‖ ≤
        (N : ℝ) * 3 ^ (depth N + 1) *
          Real.exp (-(5 / 66 : ℝ) * (N : ℝ)) := hcounter
    _ = 3 * (N : ℝ) *
        ((3 : ℝ) ^ depth N * Real.exp (-(5 / 66 : ℝ) * (N : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ 3 * (N : ℝ) *
        (Real.exp (11 * (N : ℝ) / 150) *
          Real.exp (-(5 / 66 : ℝ) * (N : ℝ))) := by
      gcongr
      exact hpow.trans hexpDepth
    _ = 3 * (N : ℝ) * Real.exp (-(2 / 825 : ℝ) * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Main far-witness closure: a successful Hermite schedule must exceed slope `1/15`
infinitely often. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_one_div_15
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 15)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteFarExteriorPoint
    hkappa
      (tendsto_boundaryHermiteJetCounterterm_hermiteFarExteriorPoint_of_eventually_depth_le_one_div_15
        hdepth)

end

end RHTower
