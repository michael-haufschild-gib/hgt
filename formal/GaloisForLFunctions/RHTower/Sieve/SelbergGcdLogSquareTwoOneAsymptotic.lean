import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPowerAsymptotic

/-!
# The square-gcd-log `(2,1)` Selberg asymptotic

The short Barban--Vehov energy contains one mixed moment not covered by the origin-based family:

`Σ μ(m)μ(n)(m,n)/(mn) · log(m,n)^2 · log(N/m)^2 · log(N/n)`.

The all-order Euler-jet identity splits it into three correction orders.  Absolute summability and
the exact principal `(2,1)` asymptotic show that only correction order zero survives, with leading
coefficient `1/6`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Literal square-gcd-log Selberg monomial with complementary-log powers `(2,1)`. -/
def selbergOriginalGcdLogSquareTwoOneMonomial (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ 2 *
      (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 * Real.log ((N : ℝ) / (n : ℝ)))

/-- The symmetric `(1,2)` orientation of the mixed square-gcd-log monomial. -/
def selbergOriginalGcdLogSquareOneTwoMonomial (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ 2 *
      (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)) ^ 2)

theorem selbergOriginalGcdLogSquareOneTwoMonomial_eq_twoOne (N : ℕ) :
    selbergOriginalGcdLogSquareOneTwoMonomial N =
      selbergOriginalGcdLogSquareTwoOneMonomial N := by
  rw [selbergOriginalGcdLogSquareOneTwoMonomial,
    selbergOriginalGcdLogSquareTwoOneMonomial, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [selbergOriginalCoeff_comm, Nat.gcd_comm]
  ring

/-- Exact three-order correction split of the mixed square-gcd-log monomial. -/
theorem selbergOriginalGcdLogSquareTwoOneMonomial_eq_correction_sum (N : ℕ) :
    selbergOriginalGcdLogSquareTwoOneMonomial N =
      ∑ l ∈ Finset.range 3, ((2 : ℕ).choose l : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N := by
  rw [selbergOriginalGcdLogSquareTwoOneMonomial]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ 2 *
          (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
            Real.log ((N : ℝ) / (n : ℝ)))) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∑ l ∈ Finset.range 3,
          ((2 : ℕ).choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (2 - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [selbergOriginalCoeff_mul_log_gcd_pow_eq_correction_convolution_principal]
      rw [Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ l ∈ Finset.range 3,
        ∑ n ∈ Finset.Icc 1 N,
          ((2 : ℕ).choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (2 - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
    _ = ∑ l ∈ Finset.range 3, ∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N,
          ((2 : ℕ).choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (2 - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / (n : ℝ))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      calc
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ((2 : ℕ).choose l : ℝ) *
              bivariateDirichletConvolution
                (selbergEulerCorrectionLogPowerCoeff l)
                (selbergGcdLogPowerPrincipalCoeff (2 - l)) m n *
              (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
                Real.log ((N : ℝ) / (n : ℝ)))) =
          ((2 : ℕ).choose l : ℝ) *
            (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              bivariateDirichletConvolution
                (selbergEulerCorrectionLogPowerCoeff l)
                (selbergGcdLogPowerPrincipalCoeff (2 - l)) m n *
              (Real.log ((N : ℝ) / (m : ℝ)) ^ 2 *
                Real.log ((N : ℝ) / (n : ℝ)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
        _ = _ := by
          apply congrArg (fun x : ℝ => ((2 : ℕ).choose l : ℝ) * x)
          rw [sum_Icc_bivariateDirichletConvolution_mul
            (selbergEulerCorrectionLogPowerCoeff l)
            (selbergGcdLogPowerPrincipalCoeff (2 - l)) _ N N]
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          apply congrArg (fun x : ℝ => selbergEulerCorrectionLogPowerCoeff l d e * x)
          simpa using
            (selbergGcdLogPowerPrincipalCoeff_weighted_logPower_eq_scaledModel
              (2 - l) 2 1 d e N (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1)

/-- One normalized correction order in the mixed square-gcd-log decomposition. -/
def selbergGcdLogSquareTwoOneCorrectionScaledTerm
    (l N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2 *
      (selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 mn.1 mn.2 N /
        Real.log N ^ 4)
  else 0

theorem tsum_selbergGcdLogSquareTwoOneCorrectionScaledTerm (l N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergGcdLogSquareTwoOneCorrectionScaledTerm l N mn) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogPowerCoeff l d e *
          (selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N /
            Real.log N ^ 4) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp [selbergGcdLogSquareTwoOneCorrectionScaledTerm, hd, he]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergGcdLogSquareTwoOneCorrectionScaledTerm, if_neg hmn]

private theorem exists_abs_selbergGcdLogPowerPrincipalScaledModel_two_sub_two_one_le
    (l : ℕ) (hl : l ≤ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ A B : ℕ, 0 < A → 0 < B →
      |selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 A B N| ≤
        M * Real.log N ^ (4 - l) := by
  interval_cases l
  · simpa using exists_abs_selbergGcdLogPowerPrincipalScaledModel_two_two_one_le
  · obtain ⟨M, hM, hbound⟩ := exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le 1 0
    refine ⟨M, hM, ?_⟩
    filter_upwards [hbound] with N hN A B hA hB
    simpa [selbergGcdLogPowerPrincipalScaledModel,
      selbergGcdLogPrincipalScaledLogPowerModel] using hN A B hA hB
  · obtain ⟨M, hM, hbound⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le 1 0
    refine ⟨M, hM, ?_⟩
    filter_upwards [hbound] with N hN A B hA hB
    simpa [selbergGcdLogPowerPrincipalScaledModel,
      selbergPrincipalScaledLogPowerModel] using hN A B hA hB

private theorem tendsto_log_nat_pow_atTop {l : ℕ} (hl : 0 < l) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ l) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨r, rfl⟩ : ∃ r, l = r + 1 := ⟨l - 1, by omega⟩
  refine Filter.tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  rw [pow_succ]
  simpa [mul_comm] using
    (le_mul_of_one_le_right (le_trans zero_le_one hN) (one_le_pow₀ hN))

theorem exists_eventually_norm_selbergGcdLogSquareTwoOneCorrectionScaledTerm_le
    (l : ℕ) (hl : l ≤ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
      ‖selbergGcdLogSquareTwoOneCorrectionScaledTerm l N mn‖ ≤
        D * |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| := by
  obtain ⟨M, hM, hMbound⟩ :=
    exists_abs_selbergGcdLogPowerPrincipalScaledModel_two_sub_two_one_le l hl
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨M / Real.log (2 : ℝ) ^ l, div_nonneg hM (pow_nonneg hlogTwo.le l), ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2 mn
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have hpowTwoLe : Real.log (2 : ℝ) ^ l ≤ Real.log (N : ℝ) ^ l :=
    pow_le_pow_left₀ hlogTwo.le hlogTwoLe l
  rw [selbergGcdLogSquareTwoOneCorrectionScaledTerm]
  split_ifs with hmem
  · obtain ⟨hm, hn⟩ := hmem
    have hmpos : 0 < mn.1 := (Finset.mem_Icc.mp hm).1
    have hnpos : 0 < mn.2 := (Finset.mem_Icc.mp hn).1
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (pow_pos hlogpos 4)]
    have hmodel := hN mn.1 mn.2 hmpos hnpos
    have hexp : 4 = (4 - l) + l := by omega
    have hratio :
        |selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 mn.1 mn.2 N| /
            Real.log N ^ 4 ≤ M / Real.log (2 : ℝ) ^ l := by
      calc
        |selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 mn.1 mn.2 N| /
              Real.log N ^ 4 ≤
            (M * Real.log N ^ (4 - l)) / Real.log N ^ 4 :=
          div_le_div_of_nonneg_right hmodel (pow_nonneg hlogpos.le _)
        _ = M / Real.log N ^ l := by
          rw [hexp, pow_add]
          field_simp
          congr 2
          omega
        _ ≤ M / Real.log (2 : ℝ) ^ l := by
          rw [div_le_div_iff₀ (pow_pos hlogpos l) (pow_pos hlogTwo l)]
          exact mul_le_mul_of_nonneg_left hpowTwoLe hM
    calc
      |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| *
          (|selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 mn.1 mn.2 N| /
            Real.log N ^ 4) ≤
        |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| *
          (M / Real.log (2 : ℝ) ^ l) :=
        mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
      _ = (M / Real.log (2 : ℝ) ^ l) *
          |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| := mul_comm _ _
  · simp
    exact mul_nonneg (div_nonneg hM (pow_nonneg hlogTwo.le l)) (abs_nonneg _)

theorem tendsto_selbergGcdLogSquareTwoOneCorrectionScaledTerm
    (l : ℕ) (hl : l ≤ 2) (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergGcdLogSquareTwoOneCorrectionScaledTerm l N mn)
      atTop (nhds (if l = 0 then
        (1 / 6 : ℝ) * selbergEulerCorrectionCoeff mn.1 mn.2 else 0)) := by
  rcases mn with ⟨d, e⟩
  rcases d.eq_zero_or_pos with rfl | hd
  · have hzero : selbergEulerCorrectionCoeff 0 e = 0 := by
      simp [selbergEulerCorrectionCoeff]
    simp [selbergGcdLogSquareTwoOneCorrectionScaledTerm, hzero]
  rcases e.eq_zero_or_pos with rfl | he
  · have hzero : selbergEulerCorrectionCoeff d 0 = 0 := by
      simp [selbergEulerCorrectionCoeff]
    simp [selbergGcdLogSquareTwoOneCorrectionScaledTerm, hzero]
  by_cases hl0 : l = 0
  · subst l
    simp only [if_true]
    have hmain :=
      (tendsto_selbergGcdLogPowerPrincipalScaledModel_two_two_one_div_log_four hd he).const_mul
        (selbergEulerCorrectionCoeff d e)
    simpa only [selbergEulerCorrectionLogPowerCoeff_zero, mul_comm] using
      hmain.congr' (by
        filter_upwards [eventually_ge_atTop (max d e)] with N hN
        have hmem : d ∈ Finset.Icc 1 N ∧ e ∈ Finset.Icc 1 N :=
          ⟨Finset.mem_Icc.mpr ⟨hd, (le_max_left d e).trans hN⟩,
            Finset.mem_Icc.mpr ⟨he, (le_max_right d e).trans hN⟩⟩
        rw [selbergGcdLogSquareTwoOneCorrectionScaledTerm, if_pos hmem]
        simp [selbergEulerCorrectionLogPowerCoeff_zero])
  · rw [if_neg hl0]
    obtain ⟨M, hM, hMbound⟩ :=
      exists_abs_selbergGcdLogPowerPrincipalScaledModel_two_sub_two_one_le l hl
    have hlogPow := tendsto_log_nat_pow_atTop (Nat.pos_of_ne_zero hl0)
    have hmaj : Tendsto (fun N : ℕ =>
        (|selbergEulerCorrectionLogPowerCoeff l d e| * M) /
          Real.log N ^ l) atTop (nhds 0) :=
      hlogPow.const_div_atTop (|selbergEulerCorrectionLogPowerCoeff l d e| * M)
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hMbound, eventually_ge_atTop (max (max d e) 2)] with N hN hNlarge
    have hdN : d ≤ N := (le_max_left d e).trans
      ((le_max_left (max d e) 2).trans hNlarge)
    have heN : e ≤ N := (le_max_right d e).trans
      ((le_max_left (max d e) 2).trans hNlarge)
    have hN2 : 2 ≤ N := (le_max_right (max d e) 2).trans hNlarge
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    rw [selbergGcdLogSquareTwoOneCorrectionScaledTerm,
      if_pos ⟨Finset.mem_Icc.mpr ⟨hd, hdN⟩, Finset.mem_Icc.mpr ⟨he, heN⟩⟩,
      Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (pow_pos hlogpos 4)]
    have hmodel := hN d e hd he
    have hexp : 4 = (4 - l) + l := by omega
    calc
      |selbergEulerCorrectionLogPowerCoeff l d e| *
          (|selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N| /
            Real.log N ^ 4) ≤
        |selbergEulerCorrectionLogPowerCoeff l d e| *
          ((M * Real.log N ^ (4 - l)) / Real.log N ^ 4) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hmodel (pow_nonneg hlogpos.le _)) (abs_nonneg _)
      _ = (|selbergEulerCorrectionLogPowerCoeff l d e| * M) /
          Real.log N ^ l := by
        rw [hexp, pow_add]
        field_simp
        congr 2
        omega

theorem tendsto_tsum_selbergGcdLogSquareTwoOneCorrectionScaledTerm
    (l : ℕ) (hl : l ≤ 2) :
    Tendsto (fun N : ℕ =>
      ∑' mn : ℕ × ℕ, selbergGcdLogSquareTwoOneCorrectionScaledTerm l N mn)
      atTop (nhds (if l = 0 then (1 / 6 : ℝ) else 0)) := by
  obtain ⟨D, _hD, hdomEventually⟩ :=
    exists_eventually_norm_selbergGcdLogSquareTwoOneCorrectionScaledTerm_le l hl
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      D * |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2|) :=
    (summable_abs_selbergEulerCorrectionLogPowerCoeff l).mul_left D
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    (tendsto_selbergGcdLogSquareTwoOneCorrectionScaledTerm l hl) hdomEventually
  by_cases hl0 : l = 0
  · subst l
    simp only [if_true] at hconv ⊢
    rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff, mul_one] at hconv
    exact hconv
  · simp only [if_neg hl0] at hconv ⊢
    simpa using hconv

/-- **The mixed square-gcd-log Selberg moment has leading coefficient `1/6`.** -/
theorem tendsto_selbergOriginalGcdLogSquareTwoOneMonomial_div_log_four :
    Tendsto (fun N : ℕ =>
      selbergOriginalGcdLogSquareTwoOneMonomial N / Real.log N ^ 4)
      atTop (nhds (1 / 6 : ℝ)) := by
  have hterms : ∀ l ∈ Finset.range 3,
      Tendsto (fun N : ℕ => ((2 : ℕ).choose l : ℝ) *
        ∑' mn : ℕ × ℕ, selbergGcdLogSquareTwoOneCorrectionScaledTerm l N mn)
        atTop (nhds (((2 : ℕ).choose l : ℝ) *
          (if l = 0 then (1 / 6 : ℝ) else 0))) := by
    intro l hl
    have hlt : l < 3 := Finset.mem_range.mp hl
    exact (tendsto_tsum_selbergGcdLogSquareTwoOneCorrectionScaledTerm l
      (by omega)).const_mul _
  have hsum := tendsto_finsetSum (Finset.range 3) hterms
  have hlimit :
      (∑ l ∈ Finset.range 3, ((2 : ℕ).choose l : ℝ) *
        (if l = 0 then (1 / 6 : ℝ) else 0)) = 1 / 6 := by
    rw [Finset.sum_eq_single 0]
    · norm_num
    · intro l _ hl0
      simp [hl0]
    · simp
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  rw [selbergOriginalGcdLogSquareTwoOneMonomial_eq_correction_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [tsum_selbergGcdLogSquareTwoOneCorrectionScaledTerm]
  calc
    ((2 : ℕ).choose l : ℝ) *
        (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            (selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N /
              Real.log N ^ 4)) =
      ((2 : ℕ).choose l : ℝ) *
        ((∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N) /
          Real.log N ^ 4) := by
      apply congrArg (fun x : ℝ => ((2 : ℕ).choose l : ℝ) * x)
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (((2 : ℕ).choose l : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (2 - l) 2 1 d e N) /
        Real.log N ^ 4 := by ring

/-- The symmetric mixed square-gcd-log moment has the same leading coefficient. -/
theorem tendsto_selbergOriginalGcdLogSquareOneTwoMonomial_div_log_four :
    Tendsto (fun N : ℕ =>
      selbergOriginalGcdLogSquareOneTwoMonomial N / Real.log N ^ 4)
      atTop (nhds (1 / 6 : ℝ)) := by
  simpa only [selbergOriginalGcdLogSquareOneTwoMonomial_eq_twoOne] using
    tendsto_selbergOriginalGcdLogSquareTwoOneMonomial_div_log_four

end

end RHTower.Sieve
