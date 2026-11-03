import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicSpectrum
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Moment gaps for regional logarithmic jumps

Finite Legendre projections turn the harmonic spectrum into a lower bound on
the orthogonal complement of low polynomial moments. Polynomial density closes
the estimate for continuously differentiable tests.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)

/-- The symmetric regional logarithmic pairing on `[-1,1]`. -/
def regionalLogPair (F G : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (F p.1 - F p.2) * (G p.1 - G p.2) / (2 * |p.1 - p.2|) ∂((ν).prod ν)

/-- The regional logarithmic Dirichlet energy. -/
def regionalLogEnergy (F : ℝ → ℝ) : ℝ := regionalLogPair F F

theorem regionalLogEnergy_nonneg (F : ℝ → ℝ) : 0 ≤ regionalLogEnergy F := by
  apply integral_nonneg
  intro p
  exact div_nonneg (mul_self_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))

theorem regionalLogPair_comm (F G : ℝ → ℝ) : regionalLogPair F G = regionalLogPair G F := by
  unfold regionalLogPair
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by dsimp only; ring

private theorem integrable_regional_square_of_bounded {H : ℝ × ℝ → ℝ} {C : ℝ}
    (hH : Measurable H)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |H (x, y)| ≤ C) :
    Integrable H ((ν).prod ν) := by
  rw [Measure.prod_restrict]
  have hfin : (volume.prod volume) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
  refine Measure.integrableOn_of_bounded (M := C) hfin hH.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [Real.norm_eq_abs]
  exact hbound p.1 hp.1 p.2 hp.2

private theorem regional_lipschitz {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |F x - F y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (-1 : ℝ) 1) isCompact_Icc
  refine ⟨K, K.coe_nonneg, fun x hx y hy => ?_⟩
  simpa only [Real.dist_eq] using hK.dist_le_mul x hx y hy

private theorem regional_value_bound {F : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hFL : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |F x - F y| ≤ K * |x - y|) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |F x| ≤ |F 0| + K := by
  have h := hFL x hx 0 (by norm_num)
  have hx1 : |x| ≤ 1 := abs_le.mpr hx
  have ht := abs_add_le (F x - F 0) (F 0)
  rw [sub_add_cancel] at ht
  rw [sub_zero] at h
  have hm := mul_le_mul_of_nonneg_left hx1 hK
  linarith only [h, ht, hm]

private theorem regional_row_bound {F G : ℝ → ℝ} {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hFL : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |F x - F y| ≤ K * |x - y|)
    (hGL : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |G x - G y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |F x * (G x - G y) / (|x - y|)| ≤ (|F 0| + K) * L := by
  by_cases he : x = y
  · subst y
    simp only [sub_self, mul_zero, abs_zero, zero_div]
    exact mul_nonneg (add_nonneg (abs_nonneg _) hK) hL
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
  rw [abs_div, abs_abs, abs_mul, div_le_iff₀ hd]
  have h := mul_le_mul (regional_value_bound hK hFL hx) (hGL x hx y hy)
    (abs_nonneg _) (add_nonneg (abs_nonneg _) hK)
  nlinarith only [h]

private theorem regional_rows_integrable {F G : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    Integrable (fun p : ℝ × ℝ => F p.1 * (G p.1 - G p.2) / |p.1 - p.2|) ((ν).prod ν) ∧
    Integrable (fun p : ℝ × ℝ => F p.2 * (G p.2 - G p.1) / |p.1 - p.2|) ((ν).prod ν) := by
  obtain ⟨K, hK, hFL⟩ := regional_lipschitz hF
  obtain ⟨L, hL, hGL⟩ := regional_lipschitz hG
  have hFc := hF.continuous
  have hGc := hG.continuous
  constructor
  · apply integrable_regional_square_of_bounded (C := (|F 0| + K) * L)
    · fun_prop
    · intro x hx y hy
      exact regional_row_bound hK hL hFL hGL hx hy
  · apply integrable_regional_square_of_bounded (C := (|F 0| + K) * L)
    · fun_prop
    · intro x hx y hy
      rw [abs_sub_comm x y]
      exact regional_row_bound hK hL hFL hGL hy hx

/-- Local Lipschitz bounds remove the diagonal singularity of the pairing. -/
theorem regionalLogPair_integrable {F G : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    Integrable (fun p : ℝ × ℝ =>
      (F p.1 - F p.2) * (G p.1 - G p.2) / (2 * |p.1 - p.2|)) ((ν).prod ν) := by
  obtain ⟨hA, hB⟩ := regional_rows_integrable hF hG
  refine ((hA.add hB).div_const 2).congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp
  ring

/-- The regional pairing represents the logarithmic operator; swapping coordinates identifies its two rows. -/
theorem regionalLogPair_eq_integral {F G : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    regionalLogPair F G = ∫ x in Icc (-1 : ℝ) 1, F x * regionalLogOperator G x := by
  let A : ℝ × ℝ → ℝ := fun p => F p.1 * (G p.1 - G p.2) / |p.1 - p.2|
  let B : ℝ × ℝ → ℝ := fun p => F p.2 * (G p.2 - G p.1) / |p.1 - p.2|
  obtain ⟨hAi, hBi⟩ := regional_rows_integrable hF hG
  have hA : Integrable A ((ν).prod ν) := hAi
  have hB : Integrable B ((ν).prod ν) := hBi
  have hswap : (∫ p, B p ∂((ν).prod ν)) = ∫ p, A p ∂((ν).prod ν) := by
    rw [integral_prod _ hB, integral_prod _ hA]
    have he : ∀ x y, B (x, y) = A (y, x) := fun x y => by
      dsimp [A, B]
      rw [abs_sub_comm x y]
    simp_rw [he]
    exact (integral_integral_swap hA).symm
  have hpair : regionalLogPair F G = ∫ p, A p ∂((ν).prod ν) := by
    have he : (fun p : ℝ × ℝ =>
        (F p.1 - F p.2) * (G p.1 - G p.2) / (2 * |p.1 - p.2|)) =
        fun p => (A p + B p) / 2 := by
      funext p
      dsimp [A, B]
      ring
    rw [regionalLogPair, he, integral_div, integral_add hA hB, hswap]
    ring
  rw [hpair, integral_prod _ hA]
  have he (x : ℝ) : (∫ y, A (x, y) ∂ν) =
      F x * ∫ y, (G x - G y) / |x - y| ∂ν := by
    dsimp [A]
    simp_rw [mul_div_assoc]
    exact integral_const_mul _ _
  simp_rw [he]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [regionalLogOperator_eq_integral (hG.differentiable (by norm_num)) hx,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- Removing a finite polynomial projection leaves an exact nonnegative remainder. -/
theorem regionalLogEnergy_sub {F P : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hP : ContDiff ℝ 1 P) :
    regionalLogEnergy (fun x => F x - P x) =
      regionalLogEnergy F + regionalLogEnergy P - 2 * regionalLogPair F P := by
  have hFF := regionalLogPair_integrable hF hF
  have hPP := regionalLogPair_integrable hP hP
  have hFP := regionalLogPair_integrable hF hP
  unfold regionalLogEnergy regionalLogPair
  have he : (fun p : ℝ × ℝ =>
      ((F p.1 - P p.1) - (F p.2 - P p.2)) *
        ((F p.1 - P p.1) - (F p.2 - P p.2)) / (2 * |p.1 - p.2|)) =
      fun p =>
        ((F p.1 - F p.2) * (F p.1 - F p.2) / (2 * |p.1 - p.2|) +
          (P p.1 - P p.2) * (P p.1 - P p.2) / (2 * |p.1 - p.2|)) -
        2 * ((F p.1 - F p.2) * (P p.1 - P p.2) / (2 * |p.1 - p.2|)) := by
    funext p
    ring
  have hiSum : Integrable (fun p : ℝ × ℝ =>
      (F p.1 - F p.2) * (F p.1 - F p.2) / (2 * |p.1 - p.2|) +
      (P p.1 - P p.2) * (P p.1 - P p.2) / (2 * |p.1 - p.2|)) ((ν).prod ν) :=
    hFF.add hPP
  rw [he, integral_sub hiSum (hFP.const_mul 2),
    integral_add hFF hPP, integral_const_mul]

/-- The ordinary square-integral moment paired with one Legendre function. -/
def regionalLegendreMoment (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Icc (-1 : ℝ) 1, F x * legP n x

private theorem legendre_norm_pos (n : ℕ) : 0 < 2 / (2 * (n : ℝ) + 1) := by
  positivity

private theorem integral_legP_mul (n k : ℕ) :
    (∫ x in Icc (-1 : ℝ) 1, legP n x * legP k x) =
      if n = k then 2 / (2 * (n : ℝ) + 1) else 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  by_cases h : n = k
  · subst k
    rw [if_pos rfl]
    simpa only [pow_two] using legP_sq_integral n
  · rw [if_neg h]
    exact legP_orthog h

private theorem integral_mul_legendreSum {F : ℝ → ℝ} (hF : Continuous F)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, F x * regionalLegendreSum s a x) =
      ∑ n ∈ s, a n * regionalLegendreMoment F n := by
  have hi (n : ℕ) : Integrable (fun x => a n * (F x * legP n x)) ν :=
    (continuous_const.mul (hF.mul (continuous_legP n))).integrableOn_Icc
  unfold regionalLegendreSum regionalLegendreMoment
  simp_rw [Finset.mul_sum, show ∀ n x, F x * (a n * legP n x) =
    a n * (F x * legP n x) by intros; ring]
  rw [integral_finsetSum s (fun n _ => hi n)]
  simp_rw [integral_const_mul]

theorem regionalLegendreMoment_sum (s : Finset ℕ) (a : ℕ → ℝ) (k : ℕ) :
    regionalLegendreMoment (regionalLegendreSum s a) k =
      if k ∈ s then a k * (2 / (2 * (k : ℝ) + 1)) else 0 := by
  classical
  have hi (n : ℕ) : Integrable (fun x => a n * (legP n x * legP k x)) ν :=
    (continuous_const.mul ((continuous_legP n).mul (continuous_legP k))).integrableOn_Icc
  unfold regionalLegendreMoment regionalLegendreSum
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum s (fun n _ => hi n)]
  simp_rw [integral_const_mul, integral_legP_mul]
  simp

private theorem integral_sq_legendreSum (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, regionalLegendreSum s a x ^ 2) =
      ∑ n ∈ s, a n ^ 2 * (2 / (2 * (n : ℝ) + 1)) := by
  simp only [pow_two]
  rw [integral_mul_legendreSum (contDiff_regionalLegendreSum s a).continuous]
  apply Finset.sum_congr rfl
  intro n hn
  rw [regionalLegendreMoment_sum, if_pos hn]
  ring

private theorem pair_legendreSum {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    regionalLogPair F (regionalLegendreSum s a) =
      ∑ n ∈ s, regionalLogEigenvalue n * a n * regionalLegendreMoment F n := by
  rw [regionalLogPair_eq_integral hF (contDiff_regionalLegendreSum s a)]
  simp_rw [regionalLogOperator_legendreSum]
  have he : (fun x => F x * ∑ n ∈ s, a n * regionalLogEigenvalue n * legP n x) =
      fun x => F x * regionalLegendreSum s (fun n => regionalLogEigenvalue n * a n) x := by
    funext x
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he, integral_mul_legendreSum hF.continuous]

theorem regionalLogEnergy_legendreSum (s : Finset ℕ) (a : ℕ → ℝ) :
    regionalLogEnergy (regionalLegendreSum s a) =
      ∑ n ∈ s, regionalLogEigenvalue n * a n ^ 2 * (2 / (2 * (n : ℝ) + 1)) := by
  rw [regionalLogEnergy, pair_legendreSum (contDiff_regionalLegendreSum s a)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [regionalLegendreMoment_sum, if_pos hn]
  ring

/-- Bessel's inequality for logarithmic energy, with its exact harmonic weights. -/
theorem regionalLogEnergy_ge_finite_moments {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (s : Finset ℕ) :
    (∑ n ∈ s, regionalLogEigenvalue n * regionalLegendreMoment F n ^ 2 /
      (2 / (2 * (n : ℝ) + 1))) ≤ regionalLogEnergy F := by
  let a (n : ℕ) := regionalLegendreMoment F n / (2 / (2 * (n : ℝ) + 1))
  let P := regionalLegendreSum s a
  have hP : ContDiff ℝ 1 P := contDiff_regionalLegendreSum s a
  have hpair : regionalLogPair F P = regionalLogEnergy P := by
    rw [pair_legendreSum hF, regionalLogEnergy_legendreSum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a]
    field_simp [(legendre_norm_pos n).ne']
  have hE : regionalLogEnergy P = ∑ n ∈ s,
      regionalLogEigenvalue n * regionalLegendreMoment F n ^ 2 /
        (2 / (2 * (n : ℝ) + 1)) := by
    rw [regionalLogEnergy_legendreSum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a]
    field_simp [(legendre_norm_pos n).ne']
  have hrem := regionalLogEnergy_nonneg (fun x => F x - P x)
  rw [regionalLogEnergy_sub hF hP, hpair, hE] at hrem
  linarith only [hrem]

private theorem integral_sq_sub_legendreSum {F : ℝ → ℝ} (hF : Continuous F)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, (F x - regionalLegendreSum s a x) ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
        ∑ n ∈ s, (2 * a n * regionalLegendreMoment F n -
          a n ^ 2 * (2 / (2 * (n : ℝ) + 1))) := by
  have hP := (contDiff_regionalLegendreSum s a).continuous
  have hFF : Integrable (fun x => F x ^ 2) ν := (hF.pow 2).integrableOn_Icc
  have hPP : Integrable (fun x => regionalLegendreSum s a x ^ 2) ν :=
    (hP.pow 2).integrableOn_Icc
  have hFP : Integrable (fun x => F x * regionalLegendreSum s a x) ν :=
    (hF.mul hP).integrableOn_Icc
  have he : (fun x => (F x - regionalLegendreSum s a x) ^ 2) =
      fun x => (F x ^ 2 + regionalLegendreSum s a x ^ 2) -
        2 * (F x * regionalLegendreSum s a x) := by funext x; ring
  have hiSum : Integrable (fun x => F x ^ 2 + regionalLegendreSum s a x ^ 2) ν :=
    hFF.add hPP
  rw [he, integral_sub hiSum (hFP.const_mul 2), integral_add hFF hPP,
    integral_const_mul, integral_sq_legendreSum, integral_mul_legendreSum hF]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ n ∈ s, 2 * a n * regionalLegendreMoment F n) =
      2 * ∑ n ∈ s, a n * regionalLegendreMoment F n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

private theorem polynomial_mass_captured {F : ℝ → ℝ} (hF : Continuous F)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) -
      (∫ x in Icc (-1 : ℝ) 1, (F x - regionalLegendreSum s a x) ^ 2) ≤
        ∑ n ∈ s, regionalLegendreMoment F n ^ 2 / (2 / (2 * (n : ℝ) + 1)) := by
  rw [integral_sq_sub_legendreSum hF]
  simp only [sub_sub_cancel]
  apply Finset.sum_le_sum
  intro n _
  rw [le_div_iff₀ (legendre_norm_pos n)]
  nlinarith only [sq_nonneg
    (a n * (2 / (2 * (n : ℝ) + 1)) - regionalLegendreMoment F n)]

private theorem finite_moment_gap {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (m : ℕ)
    (hm : ∀ n < m, regionalLegendreMoment F n = 0) (s : Finset ℕ) :
    regionalLogEigenvalue m *
      (∑ n ∈ s, regionalLegendreMoment F n ^ 2 / (2 / (2 * (n : ℝ) + 1))) ≤
        regionalLogEnergy F := by
  apply le_trans _ (regionalLogEnergy_ge_finite_moments hF s)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : n < m
  · rw [hm n hn]
    simp
  · have hmn := regionalLogEigenvalue_monotone (Nat.le_of_not_gt hn)
    have hpos : 0 ≤ regionalLegendreMoment F n ^ 2 / (2 / (2 * (n : ℝ) + 1)) :=
      div_nonneg (sq_nonneg _) (legendre_norm_pos n).le
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hmn hpos

/-- Vanishing low Legendre moments gives the exact harmonic regional spectral gap. -/
theorem regionalLogEnergy_moment_gap {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (m : ℕ)
    (hm : ∀ n < m, regionalLegendreMoment F n = 0) :
    regionalLogEigenvalue m * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) ≤
      regionalLogEnergy F := by
  have hEig := regionalLogEigenvalue_nonneg m
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min 1 (ε / (2 * (regionalLogEigenvalue m + 1)))
  have hdpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith only [hEig]))
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hδε : 2 * (regionalLogEigenvalue m + 1) * δ ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε / (2 * (regionalLogEigenvalue m + 1)))
    have he := (le_div_iff₀ (show 0 < 2 * (regionalLogEigenvalue m + 1) by
      linarith only [hEig])).mp h
    nlinarith only [he]
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1 : ℝ) 1 F
    hF.continuous.continuousOn δ hdpos
  obtain ⟨a, ha⟩ := polynomial_eval_eq_legP_sum p
  let P := regionalLegendreSum a.support (fun n => a n)
  have hP := (contDiff_regionalLegendreSum a.support (fun n => a n)).continuous
  have herr : (∫ x in Icc (-1 : ℝ) 1, (F x - P x) ^ 2) ≤ 2 * δ ^ 2 := by
    have hb : ∀ x ∈ Icc (-1 : ℝ) 1, (F x - P x) ^ 2 ≤ δ ^ 2 := by
      intro x hx
      have h := (hp x hx).le
      rw [ha x, abs_sub_comm] at h
      have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
      simpa only [sq_abs, P, regionalLegendreSum] using hs
    have hi : Integrable (fun x => (F x - P x) ^ 2) ν :=
      ((hF.continuous.sub hP).pow 2).integrableOn_Icc
    have hc : Integrable (fun _ : ℝ => δ ^ 2) ν := continuous_const.integrableOn_Icc
    have h := integral_mono_ae hi hc (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hb x hx)
    norm_num [integral_const, smul_eq_mul, Measure.real, Real.volume_Icc] at h
    exact h
  have hcap := polynomial_mass_captured hF.continuous a.support (fun n => a n)
  have hgap := finite_moment_gap hF m hm a.support
  have hcapEig := mul_le_mul_of_nonneg_left hcap hEig
  have herrEig := mul_le_mul_of_nonneg_left herr hEig
  have hsmall : 2 * regionalLogEigenvalue m * δ ^ 2 ≤ ε := by
    have hs : δ ^ 2 ≤ δ := by nlinarith only [hdpos, hd1]
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * regionalLogEigenvalue m by positivity)
    nlinarith only [h, hδε, hdpos]
  change _ ≤ _ + ε
  dsimp [P] at herrEig
  nlinarith only [hcapEig, hgap, herrEig, hsmall]

private theorem integral_odd_unit_eq_zero (f : ℝ → ℝ)
    (ho : ∀ x, f (-x) = -f x) : (∫ x in Icc (-1 : ℝ) 1, f x) = 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hn := intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 1)
  have he : (fun x => f (-x)) = fun x => -f x := funext ho
  rw [he, intervalIntegral.integral_neg] at hn
  simp only [neg_neg] at hn
  linarith only [hn]

private theorem regionalLegendreMoment_even_of_odd {F : ℝ → ℝ}
    (ho : ∀ x, F (-x) = -F x) {n : ℕ} (hn : (-1 : ℝ) ^ n = 1) :
    regionalLegendreMoment F n = 0 := by
  apply integral_odd_unit_eq_zero
  intro x
  rw [ho, legP_neg, hn, one_mul, neg_mul]

/-- On odd tests, first and third moments are the only constraints below degree five. -/
theorem regionalLogEnergy_odd_two_moment_gap {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x in Icc (-1 : ℝ) 1, F x * x) = 0)
    (h3 : (∫ x in Icc (-1 : ℝ) 1, F x * x ^ 3) = 0) :
    (137 / 30 : ℝ) * (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) ≤ regionalLogEnergy F := by
  have hP3 : regionalLegendreMoment F 3 = 0 := by
    have hi1 : Integrable (fun x => F x * x) ν :=
      (hF.continuous.mul continuous_id).integrableOn_Icc
    have hi3 : Integrable (fun x => F x * x ^ 3) ν :=
      (hF.continuous.mul (continuous_pow 3)).integrableOn_Icc
    have he : (fun x => F x * legP 3 x) = fun x =>
        (5 / 2 : ℝ) * (F x * x ^ 3) - (3 / 2 : ℝ) * (F x * x) := by
      funext x
      simp only [legP]
      norm_num
      ring
    rw [regionalLegendreMoment, he,
      integral_sub (hi3.const_mul (5 / 2)) (hi1.const_mul (3 / 2)),
      integral_const_mul, integral_const_mul, h1, h3]
    ring
  have hm : ∀ n < 5, regionalLegendreMoment F n = 0 := by
    intro n hn
    interval_cases n
    · exact regionalLegendreMoment_even_of_odd ho (by norm_num)
    · simpa only [regionalLegendreMoment, legP_one] using h1
    · exact regionalLegendreMoment_even_of_odd ho (by norm_num)
    · exact hP3
    · exact regionalLegendreMoment_even_of_odd ho (by norm_num)
  have hgap := regionalLogEnergy_moment_gap hF 5 hm
  norm_num [regionalLogEigenvalue, Finset.sum_range_succ] at hgap
  exact hgap

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_moment_gap

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_odd_two_moment_gap
