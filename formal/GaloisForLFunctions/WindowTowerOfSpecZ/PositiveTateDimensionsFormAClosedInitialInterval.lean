import GaloisForLFunctions.WindowTowerOfSpecZ.PositivePrimeMultipliersLowerTateDimension
import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowBartaCriterion
import GaloisForLFunctions.WindowTowerOfSpecZ.TheReflectionCentralizerOfTheWindowAlgebra
import GaloisForLFunctions.WindowTowerOfSpecZ.NoTatePositivityIsUniform
import Mathlib.Topology.Order.Monotone

/-!
# Positive Tate dimensions form a closed initial interval

Finite prime multipliers give downward closure and a strict interior floor.
Continuity closes the endpoint. The two-vertex graph bounds it above once
ratio two fits, while a constant Barta weight supplies a positive dimension.
-/

noncomputable section

open Finset MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open ArithmeticDegenerationTheory CohomologyOfWindowsOfSpecZ

theorem continuous_jordanTotient (n : ℕ) : Continuous (fun k : ℝ => jordanTotient k n) := by
  unfold jordanTotient
  apply continuous_finsetSum
  intro d hd
  exact continuous_const.mul (Real.continuous_const_rpow
    (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'))

theorem continuous_tateFunction {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    Continuous (tateFunction A H) := by
  have he : tateFunction A H = fun k => ∑ n ∈ Finset.Icc 1 (windowLevel A),
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) :=
    funext (tateFunction_eq hH)
  rw [he]
  apply continuous_finsetSum
  intro n _
  exact ((continuous_jordanTotient n).div_const _).mul_const _

/-- The nonnegative dimensions for which every test in the aperture is positive. -/
def tatePositiveDimensions (A : ℝ) : Set ℝ :=
  {k | 0 ≤ k ∧ ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k}

/-- Enlarging the containing aperture does not change the form of a fixed test. -/
theorem tateFunction_of_aperture_le {A B : ℝ} (hAB : A ≤ B)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) (k : ℝ) :
    tateFunction B H k = tateFunction A H k := by
  unfold tateFunction
  rw [windowRepFun_of_le hAB (jordanFun k) (mem_windowSupported_of_isWindowTest hH)]

theorem tatePositiveDimensions_antitone : Antitone tatePositiveDimensions := by
  intro A B hAB k hk
  refine ⟨hk.1, fun H hH => ?_⟩
  have hh := hk.2 H (hH.mono hAB)
  rwa [tateFunction_of_aperture_le hAB hH k] at hh

theorem zero_mem_tatePositiveDimensions (A : ℝ) : 0 ∈ tatePositiveDimensions A := by
  refine ⟨le_rfl, fun H hH => ?_⟩
  rw [tateFunction_zero hH]
  exact integral_nonneg fun u => sq_nonneg (H u)

/-- At and before the first prime, every nonidentity correlation vanishes. -/
theorem tateFunction_eq_norm_beforeFirstPrime {A : ℝ} (hA : A ≤ Real.log 2)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) (k : ℝ) :
    tateFunction A H k = ∫ u, H u ^ 2 := by
  rw [tateFunction_eq_norm_add_correlations hH k]
  have hz : (∑ n ∈ Finset.Icc 2 (windowLevel A), jordanTotient k n / Real.sqrt n *
      ∫ u, H u * H (u + Real.log n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hln : A ≤ Real.log n := hA.trans (Real.log_le_log (by norm_num) hn2)
    rw [← integral_windowShift_mul hH.vanish,
      windowShift_eq_zero_of_length_le hH.continuous hH.vanish hln]
    simp only [Pi.zero_apply, zero_mul, integral_zero, mul_zero]
  rw [hz, add_zero]

theorem tatePositiveDimensions_beforeFirstPrime {A : ℝ} (hA : A ≤ Real.log 2) :
    tatePositiveDimensions A = Set.Ici 0 := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    refine ⟨hk, fun H hH => ?_⟩
    rw [tateFunction_eq_norm_beforeFirstPrime hA hH k]
    exact integral_nonneg fun u => sq_nonneg (H u)

theorem isClosed_tatePositiveDimensions (A : ℝ) : IsClosed (tatePositiveDimensions A) := by
  have he : tatePositiveDimensions A = Set.Ici 0 ∩
      ⋂ (H : ℝ → ℝ) (hH : IsWindowTest A H), {k | 0 ≤ tateFunction A H k} := by
    ext k
    simp only [tatePositiveDimensions, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_Ici, Set.mem_iInter]
  rw [he]
  exact isClosed_Ici.inter (isClosed_iInter fun H =>
    isClosed_iInter fun hH => isClosed_le continuous_const (continuous_tateFunction hH))

private theorem tateFunction_nonneg_of_coefficient_sum_le_one {A k : ℝ} (hk : 0 ≤ k)
    (hc : (∑ n ∈ Finset.Icc 2 (windowLevel A), jordanTotient k n / Real.sqrt n) ≤ 1)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) : 0 ≤ tateFunction A H k := by
  have ha : ∀ n, 0 ≤ (jordanTotient k n / Real.sqrt n) / 2 := fun n =>
    div_nonneg (div_nonneg (jordanTotient_nonneg hk n) (Real.sqrt_nonneg _)) (by norm_num)
  have hg (u : ℝ) : windowGate A (fun _ => (1 : ℝ)) u ≤ 1 := by
    unfold windowGate
    by_cases hu : u ∈ Set.Icc (-A) 0
    · simpa only [Set.indicator_of_mem hu] using (le_rfl : (1 : ℝ) ≤ 1)
    · simpa only [Set.indicator_of_notMem hu] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hbal : ∀ u ∈ Set.Icc (-A) 0,
      ∑ n ∈ Finset.Icc 2 (windowLevel A), ((jordanTotient k n / Real.sqrt n) / 2) *
        (windowGate A (fun _ => 1) (u + Real.log n) +
          windowGate A (fun _ => 1) (u - Real.log n)) ≤ 1 := by
    intro u _
    calc
      _ ≤ ∑ n ∈ Finset.Icc 2 (windowLevel A),
          ((jordanTotient k n / Real.sqrt n) / 2) * (1 + 1) := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (add_le_add (hg _) (hg _)) (ha n)
      _ = ∑ n ∈ Finset.Icc 2 (windowLevel A), jordanTotient k n / Real.sqrt n := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ 1 := hc
  have hh := arith_form_nonneg_of_balanced hH measurable_const
    (h := fun _ => (1 : ℝ)) (C := 1) (fun _ => le_rfl) (fun _ => le_rfl)
    (Finset.Icc 2 (windowLevel A)) ha hbal (fun _ => 1) (fun _ => by norm_num)
  simp only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), mul_one] at hh
  rwa [← tateFunction_eq_norm_add_correlations hH k] at hh

/-- Every fixed aperture carries a positive Tate dimension. -/
theorem exists_pos_mem_tatePositiveDimensions (A : ℝ) :
    ∃ k : ℝ, 0 < k ∧ k ∈ tatePositiveDimensions A := by
  let f : ℝ → ℝ := fun k =>
    ∑ n ∈ Finset.Icc 2 (windowLevel A), jordanTotient k n / Real.sqrt n
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro n _
    exact (continuous_jordanTotient n).div_const _
  have hf0 : f 0 = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn1 : n ≠ 1 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [← jordanFun_apply, jordanFun_zero, ArithmeticFunction.one_apply, if_neg hn1, zero_div]
  have hnb : {k : ℝ | f k < 1} ∈ 𝓝 0 :=
    (isOpen_lt hf continuous_const).mem_nhds (by change f 0 < 1; rw [hf0]; norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnb
  have hk : 0 < δ / 2 := half_pos hδ
  have hfk : f (δ / 2) < 1 := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hk]
    linarith only [hδ])
  exact ⟨δ / 2, hk, hk.le, fun H hH =>
    tateFunction_nonneg_of_coefficient_sum_le_one hk.le hfk.le hH⟩

private theorem rationalHeckeForm_pair (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℝ) :
    rationalHeckeForm N c {1, 2} (fun r => if r = 1 then 1 else -1) = 2 - c 2 := by
  classical
  have hedge (n : ℕ) (hn : 2 ≤ n) :
      (∑ r ∈ ({1, 2} : Finset ℚ), ∑ s ∈ ({1, 2} : Finset ℚ),
        if (s : ℝ) = n * r then
          (if r = 1 then (1 : ℝ) else -1) * (if s = 1 then 1 else -1) else 0) =
        if n = 2 then -1 else 0 := by
    by_cases hn2 : n = 2
    · subst n
      norm_num
    · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : (1 : ℝ) ≠ n := by linarith only [hnR]
      have h12 : (1 : ℝ) ≠ n * 2 := by linarith only [hnR]
      have h22 : (2 : ℝ) ≠ n * 2 := by linarith only [hnR]
      have h2 : (2 : ℝ) ≠ n := by exact_mod_cast Ne.symm hn2
      norm_num [h1, h12, h22, h2, hn2]
  have hs : (∑ n ∈ Finset.Icc 2 N, c n *
      ∑ r ∈ ({1, 2} : Finset ℚ), ∑ s ∈ ({1, 2} : Finset ℚ),
        if (s : ℝ) = n * r then
          (if r = 1 then (1 : ℝ) else -1) * (if s = 1 then 1 else -1) else 0) = -c 2 := by
    rw [Finset.sum_congr rfl (fun n hn => congrArg (c n * ·) (hedge n (Finset.mem_Icc.mp hn).1))]
    rw [Finset.sum_eq_single_of_mem 2 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
    · simp
    · intro n _ hn
      rw [if_neg hn, mul_zero]
  unfold rationalHeckeForm
  rw [hs]
  norm_num [sub_eq_add_neg]

/-- The two-vertex graph bounds every positive dimension once ratio two fits. -/
theorem tate_rpow_two_le_of_nonneg {A k : ℝ} (hA : Real.log 2 < A)
    (hp : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) :
    (2 : ℝ) ^ k ≤ 1 + 2 * Real.sqrt 2 := by
  have hN : 2 ≤ windowLevel A := by
    apply (Nat.le_floor_iff (Real.exp_pos A).le).mpr
    have hh := Real.exp_le_exp.mpr hA.le
    rwa [Real.exp_log (by norm_num)] at hh
  have hpos : ∀ r ∈ ({1, 2} : Finset ℚ), 0 < r := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> norm_num
  have hs : ∀ r ∈ ({1, 2} : Finset ℚ), ∀ s ∈ ({1, 2} : Finset ℚ),
      Real.log s - Real.log r < A := by
    intro r hr s hs
    have hr1 : (1 : ℝ) ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num
    have hs2 : (s : ℝ) ≤ 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> norm_num
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hpos s hs
    have hrl := Real.log_nonneg hr1
    have hsl := Real.log_le_log hs0 hs2
    linarith only [hA, hrl, hsl]
  have hh := (tateFunction_nonneg_iff_rationalHeckePositive A k).mp hp {1, 2} hpos hs
    (fun r => if r = 1 then 1 else -1)
  rw [rationalHeckeForm_pair _ hN] at hh
  have hJ : jordanTotient k 2 = (2 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_two k (a := 1) le_rfl
  rw [hJ] at hh
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : ((2 : ℝ) ^ k - 1) / Real.sqrt 2 ≤ 2 := by linarith only [hh]
  have hb := (div_le_iff₀ hsqrt).mp hc
  linarith only [hb]

theorem tate_dimension_le_firstPrimeHorizon {A k : ℝ} (hA : Real.log 2 < A)
    (hp : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ tateFunction A H k) :
    k ≤ Real.log (1 + 2 * Real.sqrt 2) / Real.log 2 := by
  have hl := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) k)
    (tate_rpow_two_le_of_nonneg hA hp)
  rw [Real.log_rpow (by norm_num)] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hl

/-- Above the first prime, positive Tate dimensions form a compact initial
interval with positive endpoint. Every smaller nonnegative dimension has a
uniform positive floor. -/
theorem exists_exact_tateHorizon {A : ℝ} (hA : Real.log 2 < A) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ Real.log (1 + 2 * Real.sqrt 2) / Real.log 2 ∧
      tatePositiveDimensions A = Set.Icc 0 κ ∧
      ∀ k : ℝ, 0 ≤ k → k < κ → ∃ ε : ℝ, 0 < ε ∧
        ∀ H : ℝ → ℝ, IsWindowTest A H → ε * (∫ u, H u ^ 2) ≤ tateFunction A H k := by
  let S := tatePositiveDimensions A
  have hne : S.Nonempty := ⟨0, zero_mem_tatePositiveDimensions A⟩
  have hb : BddAbove S := ⟨Real.log (1 + 2 * Real.sqrt 2) / Real.log 2,
    fun k hk => tate_dimension_le_firstPrimeHorizon hA hk.2⟩
  have hsup : sSup S ∈ S := (isClosed_tatePositiveDimensions A).csSup_mem hne hb
  obtain ⟨k0, hk0, hk0S⟩ := exists_pos_mem_tatePositiveDimensions A
  have hκ : 0 < sSup S := hk0.trans_le (le_csSup hb hk0S)
  refine ⟨sSup S, hκ, tate_dimension_le_firstPrimeHorizon hA hsup.2, ?_, ?_⟩
  · ext k
    constructor
    · intro hk
      exact ⟨hk.1, le_csSup hb hk⟩
    · intro hk
      exact ⟨hk.1, tateFunction_nonneg_of_dimension_le hk.1 hk.2 hsup.2⟩
  · intro k hk hkκ
    exact exists_tateFunction_uniform_floor_of_dimension_lt hk hkκ hsup.2

/-- The entire positive interval shrinks to dimension zero along the tower. -/
theorem tatePositiveDimensions_shrink_to_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ k ∈ tatePositiveDimensions A, k < ε := by
  obtain ⟨A₀, H, hH, hneg⟩ := exists_tateFunction_neg hε
  refine ⟨A₀, fun A hA k hk => ?_⟩
  by_contra hkle
  have hpos := tateFunction_nonneg_of_dimension_le hε.le (le_of_not_gt hkle) hk.2
  have hh := hpos H (hH.mono hA)
  rw [tateFunction_of_aperture_le hA hH ε] at hh
  exact (not_lt_of_ge hh) hneg

#print axioms isClosed_tatePositiveDimensions
#print axioms exists_pos_mem_tatePositiveDimensions
#print axioms exists_exact_tateHorizon
#print axioms tatePositiveDimensions_beforeFirstPrime
#print axioms tatePositiveDimensions_shrink_to_zero

end GaloisForLFunctions.WindowTowerOfSpecZ
