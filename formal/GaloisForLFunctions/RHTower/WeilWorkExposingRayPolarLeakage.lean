import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction
import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion

/-!
# The full repair budget of far polar corrections

Although the actual far-polar tests have uniformly vanishing integer atom traces and eventually
negative archimedean energy, their weighted absolute trace budget grows like `X * exp X`.
This measures the independent-atom repair budget, not the minimum energy of arbitrary repairs.
-/

open Real Finset Filter Topology Set
noncomputable section
namespace RHTower.ExposingRayPolarLeakage

local notation "R" => flatBumpCorr (17 / 50) (17 / 1000)

/-- Complete integer trace budget in the normalization used by atom repair. -/
def budget (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * (X + 17 / 50))⌋₊,
    (Real.log n + boxConst) * |atomCoeff (farPolarTest X) n|

private theorem weight_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ Real.log n + boxConst :=
  add_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) boxConst_nonneg

/-- Both translated correlation windows are retained. -/
theorem trace_eq {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : 2 ≤ n) :
    atomCoeff (farPolarTest X) n =
      farPolarCoeff X ^ 2 / 2 * R (Real.log n - 2 * X) -
        2 * farPolarCoeff X * R (Real.log n - X) := by
  have h := integral_normSq_paperFT_mul_cos_eq (contDiff_farPolarTest X)
    (tsupport_farPolarTest hX) (Real.log n)
  rw [integral_normSq_farPolarTest_mul_cos_log hX hn] at h
  change 2 * π * _ = π * atomCoeff (farPolarTest X) n at h
  nlinarith [Real.pi_pos]

private theorem corr_lower {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1 / 4) : 1 / 4 ≤ R y := by
  have h0 := flatBumpCorr_zero_ge (b := (17 / 50 : ℝ)) (d := 17 / 1000)
    (by norm_num) (by norm_num)
  have h1 := flatBumpCorr_sub_le (b := (17 / 50 : ℝ)) (d := 17 / 1000)
    (by norm_num) (by norm_num) hy
  linarith

private theorem coeff_lower {X : ℝ} (hX : 0 ≤ X) :
    Real.exp (-(X / 2)) ≤ farPolarCoeff X := by
  have hc := Real.cosh_pos (X / 2)
  have he : Real.exp (-(X / 2)) ≤ Real.exp (X / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp : Real.exp (-(X / 2)) * Real.exp (X / 2) = 1 := by
    rw [← Real.exp_add]; simp
  rw [farPolarCoeff, le_div_iff₀ hc, Real.cosh_eq]
  nlinarith [Real.exp_pos (-(X / 2))]

private theorem coeff_sq_lower {X : ℝ} (hX : 0 ≤ X) :
    Real.exp (-X) ≤ farPolarCoeff X ^ 2 := by
  have hc := coeff_lower hX
  have he : Real.exp (-(X / 2)) ^ 2 = Real.exp (-X) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  nlinarith [Real.exp_pos (-(X / 2))]

/-- Uniform smallness of all integer coefficients does not control the repair budget. -/
theorem trace_abs_le {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : 2 ≤ n) :
    |atomCoeff (farPolarTest X) n| ≤ 2 * farPolarCoeff X + farPolarCoeff X ^ 2 / 2 := by
  rw [trace_eq hX hn]
  have hc := farPolarCoeff_nonneg X
  have hp := fejerCorr_nonneg (Real.log n - 2 * X)
  have hq := fejerCorr_nonneg (Real.log n - X)
  have hp1 := fejerCorr_le_one (Real.log n - 2 * X)
  have hq1 := fejerCorr_le_one (Real.log n - X)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (farPolarCoeff X)]

/-- Actual polar admissibility, with the explicit support aperture. -/
theorem polar {X : ℝ} (hX : 0 ≤ X) : IsPolarTest (X + 17 / 50) (farPolarTest X) :=
  ⟨by linarith, contDiff_farPolarTest X, tsupport_farPolarTest hX,
    paperFT_farPolarTest_half_I X, paperFT_farPolarTest_neg_half_I X⟩

/-- A fixed negative energy persists while the full trace tends uniformly to zero. -/
theorem negative_energy_and_uniform_trace :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      IsPolarTest (X + 17 / 50) (farPolarTest X) ∧
      archEnergy (farPolarTest X) ≤ -δ ∧
      ∀ n : ℕ, 2 ≤ n → |atomCoeff (farPolarTest X) n| ≤ ε := by
  have hneg : archEnergy fejerTest < 0 := integral_normSq_paperFT_fejerTest_mul_arch_neg
  refine ⟨-archEnergy fejerTest / 2, by linarith, ?_⟩
  intro ε hε
  have he : Tendsto (fun X => (2 * farPolarCoeff X + farPolarCoeff X ^ 2) *
      fejerArchAbsEnergy) atTop (𝓝 0) := by
    simpa using ((tendsto_farPolarCoeff.const_mul 2).add
      (tendsto_farPolarCoeff.pow 2)).mul_const fejerArchAbsEnergy
  have ht : Tendsto (fun X => 2 * farPolarCoeff X + farPolarCoeff X ^ 2 / 2)
      atTop (𝓝 0) := by
    simpa using (tendsto_farPolarCoeff.const_mul 2).add
      ((tendsto_farPolarCoeff.pow 2).div_const 2)
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    he.eventually (gt_mem_nhds (show 0 < -archEnergy fejerTest / 2 by linarith)),
    ht.eventually (gt_mem_nhds hε)] with X hX he ht
  refine ⟨polar hX, ?_, fun n hn => (trace_abs_le hX hn).trans ht.le⟩
  have h := integral_arch_farPolarTest_le hX
  change archEnergy (farPolarTest X) ≤ archEnergy fejerTest + _ at h
  linarith

private theorem window_count {X : ℝ} (hX : 4 ≤ X) :
    Real.exp (2 * X) / 8 ≤
      ((Finset.Ioc ⌊Real.exp (2 * X)⌋₊ ⌊(5 / 4) * Real.exp (2 * X)⌋₊).card : ℝ) := by
  have ht := Real.exp_pos (2 * X)
  have hbig : 8 ≤ Real.exp (2 * X) := by linarith [Real.add_one_le_exp (2 * X)]
  have hle : ⌊Real.exp (2 * X)⌋₊ ≤ ⌊(5 / 4) * Real.exp (2 * X)⌋₊ :=
    Nat.floor_mono (by nlinarith)
  rw [Nat.card_Ioc, Nat.cast_sub hle]
  have hlow := Nat.floor_le ht.le
  have hupp := Nat.lt_floor_add_one ((5 / 4) * Real.exp (2 * X))
  linarith

private theorem window_log {X : ℝ} {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊Real.exp (2 * X)⌋₊ ⌊(5 / 4) * Real.exp (2 * X)⌋₊) :
    2 * X < Real.log n ∧ Real.log n ≤ 2 * X + 1 / 4 := by
  obtain ⟨hnl, hnu⟩ := Finset.mem_Ioc.mp hn
  have hl : Real.exp (2 * X) < n := Nat.lt_of_floor_lt hnl
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hl
  have hu : (n : ℝ) ≤ (5 / 4) * Real.exp (2 * X) :=
    (Nat.cast_le.mpr hnu).trans (Nat.floor_le (by positivity))
  refine ⟨(Real.lt_log_iff_exp_lt hn0).mpr hl, ?_⟩
  apply (Real.log_le_iff_le_exp hn0).mpr
  calc (n : ℝ) ≤ (5 / 4) * Real.exp (2 * X) := hu
    _ ≤ Real.exp (1 / 4) * Real.exp (2 * X) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (1 / 4 : ℝ)]
    _ = Real.exp (2 * X + 1 / 4) := by rw [← Real.exp_add]; congr 1; ring

/-- The second correlation window alone costs at least `X exp(X)/32`. -/
theorem budget_lower {X : ℝ} (hX : 4 ≤ X) :
    X * Real.exp X / 32 ≤ budget X := by
  have hX0 : 0 ≤ X := by linarith
  let S := Finset.Ioc ⌊Real.exp (2 * X)⌋₊ ⌊(5 / 4) * Real.exp (2 * X)⌋₊
  let T := Finset.Icc 2 ⌊Real.exp (2 * (X + 17 / 50))⌋₊
  have hST : S ⊆ T := by
    intro n hn
    have hl := window_log hn
    have hn0 : 0 < (n : ℝ) := (Real.exp_pos _).trans
      (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn).1)
    have hn2 : 2 ≤ n := by
      have hne : Real.exp (2 * X) < (n : ℝ) := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn).1
      have : (2 : ℝ) < n := by linarith [Real.add_one_le_exp (2 * X)]
      exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
    refine Finset.mem_Icc.mpr ⟨hn2, Nat.le_floor ?_⟩
    apply (Real.log_le_iff_le_exp hn0).mp
    linarith [hl.2]
  have hterm : ∀ n ∈ S, X * Real.exp (-X) / 4 ≤
      (Real.log n + boxConst) * |atomCoeff (farPolarTest X) n| := by
    intro n hn
    have hl := window_log hn
    have hn2 := (Finset.mem_Icc.mp (hST hn)).1
    have hz : R (Real.log n - X) = 0 := fejerCorr_eq_zero (by
      rw [abs_of_nonneg (by linarith)]; linarith)
    have hc := corr_lower (show 0 ≤ Real.log n - 2 * X by linarith)
      (show Real.log n - 2 * X ≤ 1 / 4 by linarith)
    have ha : Real.exp (-X) / 8 ≤ atomCoeff (farPolarTest X) n := by
      rw [trace_eq hX0 hn2, hz, mul_zero, sub_zero]
      have hs := coeff_sq_lower hX0
      nlinarith [Real.exp_pos (-X)]
    have ha' : Real.exp (-X) / 8 ≤ |atomCoeff (farPolarTest X) n| :=
      ha.trans (le_abs_self _)
    have hw : 2 * X ≤ Real.log n + boxConst := by linarith [boxConst_nonneg]
    have hp := mul_le_mul hw ha' (by positivity) (weight_nonneg hn2)
    nlinarith
  calc X * Real.exp X / 32 = (Real.exp (2 * X) / 8) * (X * Real.exp (-X) / 4) := by
        have he : Real.exp (2 * X) * Real.exp (-X) = Real.exp X := by
          rw [← Real.exp_add]; congr 1; ring
        nlinarith [he]
    _ ≤ (S.card : ℝ) * (X * Real.exp (-X) / 4) :=
      mul_le_mul_of_nonneg_right (window_count hX) (by positivity)
    _ = ∑ n ∈ S, X * Real.exp (-X) / 4 := by simp
    _ ≤ ∑ n ∈ S, (Real.log n + boxConst) * |atomCoeff (farPolarTest X) n| :=
      Finset.sum_le_sum hterm
    _ ≤ budget X := Finset.sum_le_sum_of_subset_of_nonneg hST (by
      intro n hn _; exact mul_nonneg (weight_nonneg (Finset.mem_Icc.mp hn).1) (abs_nonneg _))


private theorem sum_corr_le {Y : ℝ} (hY : 0 ≤ Y) (M : ℕ) :
    ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * R (Real.log n - Y) ≤
      (Y + 1 + boxConst) * Real.exp (Y + 1) := by
  let S := Finset.Icc 2 M
  let T := Finset.Icc 2 ⌊Real.exp (Y + 1)⌋₊
  let B := Y + 1 + boxConst
  have hB : 0 ≤ B := by dsimp [B]; linarith [boxConst_nonneg]
  have heq : ∑ n ∈ S ∩ T, (Real.log n + boxConst) * R (Real.log n - Y) =
      ∑ n ∈ S, (Real.log n + boxConst) * R (Real.log n - Y) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hnot
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnt : n ∉ T := by intro ht; exact hnot (Finset.mem_inter.mpr ⟨hn, ht⟩)
    have hlarge : ⌊Real.exp (Y + 1)⌋₊ < n := by
      have : ¬n ≤ ⌊Real.exp (Y + 1)⌋₊ := by
        intro h; exact hnt (Finset.mem_Icc.mpr ⟨hn2, h⟩)
      omega
    have he : Real.exp (Y + 1) < (n : ℝ) := Nat.lt_of_floor_lt hlarge
    have hn0 : 0 < (n : ℝ) := (Real.exp_pos _).trans he
    have hl := (Real.lt_log_iff_exp_lt hn0).mpr he
    rw [fejerCorr_eq_zero (y := Real.log n - Y) (by
      rw [abs_of_nonneg (by linarith)]; linarith), mul_zero]
  have hterm : ∀ n ∈ S ∩ T, (Real.log n + boxConst) * R (Real.log n - Y) ≤ B := by
    intro n hn
    have ht := Finset.mem_Icc.mp (Finset.mem_inter.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnl : (n : ℝ) ≤ Real.exp (Y + 1) :=
      (Nat.cast_le.mpr ht.2).trans (Nat.floor_le (Real.exp_pos _).le)
    have hl := (Real.log_le_iff_le_exp hn0).mpr hnl
    have hw := weight_nonneg ht.1
    have hc := fejerCorr_le_one (Real.log n - Y)
    have hp := mul_le_mul_of_nonneg_left hc hw
    dsimp [B]; nlinarith
  have hcard : ((S ∩ T).card : ℝ) ≤ Real.exp (Y + 1) := by
    have hc : T.card ≤ ⌊Real.exp (Y + 1)⌋₊ := by
      dsimp [T]; rw [Nat.card_Icc]; omega
    exact (Nat.cast_le.mpr ((Finset.card_le_card Finset.inter_subset_right).trans hc)).trans
      (Nat.floor_le (Real.exp_pos _).le)
  calc _ = ∑ n ∈ S ∩ T, (Real.log n + boxConst) * R (Real.log n - Y) := heq.symm
    _ ≤ ∑ n ∈ S ∩ T, B := Finset.sum_le_sum hterm
    _ = ((S ∩ T).card : ℝ) * B := by simp
    _ ≤ Real.exp (Y + 1) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by dsimp [B]; ring

private theorem coeff_sq_upper (X : ℝ) : farPolarCoeff X ^ 2 ≤ 4 * Real.exp (-X) := by
  have hc := farPolarCoeff_le X
  have hc0 := farPolarCoeff_nonneg X
  have he : Real.exp (-(X / 2)) ^ 2 = Real.exp (-X) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  nlinarith [sq_nonneg (2 * Real.exp (-(X / 2)) - farPolarCoeff X)]

/-- Matching upper scale for the entire trace, including both distant windows. -/
theorem budget_upper {X : ℝ} (hX : 4 ≤ X) :
    budget X ≤ 6 * Real.exp 1 * (3 + boxConst) * X * Real.exp X := by
  have hX0 : 0 ≤ X := by linarith
  let M := ⌊Real.exp (2 * (X + 17 / 50))⌋₊
  let H := 2 * X + 1 + boxConst
  have hH : 0 ≤ H := by dsimp [H]; linarith [boxConst_nonneg]
  have hs1 : ∑ n ∈ Finset.Icc 2 M, (Real.log n + boxConst) * R (Real.log n - X) ≤
      H * Real.exp (X + 1) :=
    (sum_corr_le hX0 M).trans (mul_le_mul_of_nonneg_right (by dsimp [H]; linarith)
      (Real.exp_pos _).le)
  have hs2 := sum_corr_le (show 0 ≤ 2 * X by positivity) M
  have hbase : budget X ≤
      2 * farPolarCoeff X * (H * Real.exp (X + 1)) +
      (farPolarCoeff X ^ 2 / 2) * (H * Real.exp (2 * X + 1)) := by
    calc
      budget X ≤ ∑ n ∈ Finset.Icc 2 M,
          (2 * farPolarCoeff X * ((Real.log n + boxConst) * R (Real.log n - X)) +
          (farPolarCoeff X ^ 2 / 2) * ((Real.log n + boxConst) * R (Real.log n - 2 * X))) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn2 := (Finset.mem_Icc.mp hn).1
        have hp : |atomCoeff (farPolarTest X) n| ≤
            farPolarCoeff X ^ 2 / 2 * R (Real.log n - 2 * X) +
              2 * farPolarCoeff X * R (Real.log n - X) := by
          rw [trace_eq hX0 hn2]
          exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (by
            exact mul_nonneg (by positivity) (fejerCorr_nonneg _)), abs_of_nonneg (by
            exact mul_nonneg (mul_nonneg (by norm_num) (farPolarCoeff_nonneg X))
              (fejerCorr_nonneg _))])
        have hw := mul_le_mul_of_nonneg_left hp (weight_nonneg hn2)
        nlinarith
      _ = 2 * farPolarCoeff X * (∑ n ∈ Finset.Icc 2 M,
          (Real.log n + boxConst) * R (Real.log n - X)) +
          (farPolarCoeff X ^ 2 / 2) * (∑ n ∈ Finset.Icc 2 M,
          (Real.log n + boxConst) * R (Real.log n - 2 * X)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hs1 (by
        exact mul_nonneg (by norm_num) (farPolarCoeff_nonneg X)))
        (mul_le_mul_of_nonneg_left hs2 (by positivity))
  have he1 : Real.exp (-(X / 2)) * Real.exp (X + 1) = Real.exp 1 * Real.exp (X / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-X) * Real.exp (2 * X + 1) = Real.exp 1 * Real.exp X := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hhalf : Real.exp (X / 2) ≤ Real.exp X := Real.exp_le_exp.mpr (by linarith)
  have hH' : H ≤ (3 + boxConst) * X := by
    dsimp [H]
    have := mul_nonneg boxConst_nonneg (show 0 ≤ X - 1 by linarith)
    nlinarith
  calc budget X ≤ _ := hbase
    _ ≤ (4 * Real.exp (-(X / 2))) * (H * Real.exp (X + 1)) +
        (2 * Real.exp (-X)) * (H * Real.exp (2 * X + 1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by linarith [farPolarCoeff_le X]) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by linarith [coeff_sq_upper X]) (by positivity)
    _ = 4 * H * Real.exp 1 * Real.exp (X / 2) + 2 * H * Real.exp 1 * Real.exp X := by
      calc _ = 4 * H * (Real.exp (-(X / 2)) * Real.exp (X + 1)) +
          2 * H * (Real.exp (-X) * Real.exp (2 * X + 1)) := by ring
        _ = _ := by rw [he1, he2]; ring
    _ ≤ 6 * H * Real.exp 1 * Real.exp X := by
      have := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4 * H * Real.exp 1 by positivity)
      nlinarith
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hH' (show 0 ≤ 6 * Real.exp 1 * Real.exp X by positivity)
      nlinarith

/-- Sharp exponential scale of the literal complete repair budget. -/
theorem budget_bounds (X : ℝ) (hX : 4 ≤ X) :
    X * Real.exp X / 32 ≤ budget X ∧
      budget X ≤ 6 * Real.exp 1 * (3 + boxConst) * X * Real.exp X :=
  ⟨budget_lower hX, budget_upper hX⟩


/-- Full independent-atom budget for matching the literal truncated exposing ray. -/
def matchingBudget (X : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (max N ⌊Real.exp (2 * (X + 17 / 50))⌋₊),
    (Real.log n + boxConst) *
      |2 * π * atomCoeff (farPolarTest X) n - exposingWeightTrunc N n|

/-- No exposing cutoff can absorb the divergent far-polar leakage in the box norm. -/
theorem matchingBudget_lower (X : ℝ) (hX : 4 ≤ X) (N : ℕ) :
    π / 16 * X * Real.exp X - (∑' n : ℕ, exposingMajorant n) ≤ matchingBudget X N := by
  let M := ⌊Real.exp (2 * (X + 17 / 50))⌋₊
  let S := Finset.Icc 2 (max N M)
  have hsub : Finset.Icc 2 M ⊆ S := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (le_max_right _ _)⟩
  have hnorm : budget X ≤ ∑ n ∈ S, (Real.log n + boxConst) *
      |atomCoeff (farPolarTest X) n| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ =>
      mul_nonneg (weight_nonneg (Finset.mem_Icc.mp hn).1) (abs_nonneg _))
  have ht : ∑ n ∈ S, (Real.log n + boxConst) * |exposingWeightTrunc N n| ≤
      ∑' n : ℕ, exposingMajorant n := by
    calc _ ≤ ∑ n ∈ S, exposingMajorant n := by
          apply Finset.sum_le_sum
          intro n hn
          have hn2 := (Finset.mem_Icc.mp hn).1
          by_cases hnN : n ≤ N
          · simp only [exposingWeightTrunc, exposingMajorant, if_pos hn2, if_pos hnN]
            exact le_rfl
          · simp only [exposingWeightTrunc, exposingMajorant, if_pos hn2, if_neg hnN,
              abs_zero, mul_zero]
            exact mul_nonneg (weight_nonneg hn2) (abs_nonneg _)
      _ ≤ _ := summable_exposingMajorant.sum_le_tsum S (fun n _ => exposingMajorant_nonneg n)
  have hs : 2 * π * (∑ n ∈ S, (Real.log n + boxConst) *
      |atomCoeff (farPolarTest X) n|) ≤ matchingBudget X N +
        ∑ n ∈ S, (Real.log n + boxConst) * |exposingWeightTrunc N n| := by
    rw [Finset.mul_sum]
    change _ ≤ (∑ n ∈ S, _) + _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have ha : 2 * π * |atomCoeff (farPolarTest X) n| ≤
        |2 * π * atomCoeff (farPolarTest X) n - exposingWeightTrunc N n| +
          |exposingWeightTrunc N n| := by
      have h := abs_add_le (2 * π * atomCoeff (farPolarTest X) n - exposingWeightTrunc N n)
        (exposingWeightTrunc N n)
      rw [sub_add_cancel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π)] at h
      exact h
    have := mul_le_mul_of_nonneg_left ha (weight_nonneg hn2)
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * π by positivity)
  have hl := mul_le_mul_of_nonneg_left (budget_lower hX) (show 0 ≤ 2 * π by positivity)
  nlinarith

end RHTower.ExposingRayPolarLeakage
