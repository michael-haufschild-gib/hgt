import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeAbs
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeMonotonicity
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Fixed height beyond which every Route-T binary shell meets the depth threshold. -/
def inghamRouteTUniformZeroFreeBase : ℕ :=
  2 ^ (routeTBandDepthRootThreshold ^ 10)

/-- Half the smaller of the compact and high-height Route-T zero-free widths. -/
def inghamRouteTUniformZeroFreeWidth (A delta K : ℝ) : ℝ :=
  min delta (routeTZeroFreeWidth A K) / 2

theorem inghamRouteTUniformZeroFreeBase_large :
    100000 ≤ inghamRouteTUniformZeroFreeBase := by
  have hq : 17 ≤ routeTBandDepthRootThreshold ^ 10 := by
    calc
      17 ≤ 2 ^ (10 : ℕ) := by norm_num
      _ ≤ routeTBandDepthRootThreshold ^ 10 :=
        Nat.pow_le_pow_left routeTBandDepthRootThreshold_pos 10
  calc
    100000 ≤ 2 ^ (17 : ℕ) := by norm_num
    _ ≤ 2 ^ (routeTBandDepthRootThreshold ^ 10) :=
      Nat.pow_le_pow_right (by norm_num) hq

theorem inghamRouteTUniformZeroFreeBase_depth :
    routeTBandDepthRootThreshold ^ 10 ≤
      routeTBinaryHeight (inghamRouteTUniformZeroFreeBase : ℝ) := by
  rw [inghamRouteTUniformZeroFreeBase, routeTBinaryHeight, Nat.ceil_natCast,
    Nat.clog_pow 2 (routeTBandDepthRootThreshold ^ 10) (by norm_num)]

theorem inghamRouteTUniformZeroFreeWidth_pos
    {A delta K : ℝ} (hdelta : 0 < delta) :
    0 < inghamRouteTUniformZeroFreeWidth A delta K := by
  unfold inghamRouteTUniformZeroFreeWidth
  exact div_pos (lt_min hdelta (routeTZeroFreeWidth_pos A K)) (by norm_num)

/-- The Route-T zero-free region made uniform over every ordinate up to `K`: compactness handles
the fixed initial box, and antitonicity evaluates every higher ordinate at the common top height. -/
theorem exists_zeta_uniform_routeT_zero_free :
    ∃ A delta : ℝ, 0 < delta ∧
      ∀ (s : ℂ) (K : ℝ),
        (inghamRouteTUniformZeroFreeBase : ℝ) ≤ K →
        |s.im| ≤ K →
        1 - inghamRouteTUniformZeroFreeWidth A delta K ≤ s.re →
        s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨A, hroute⟩ := exists_routeT_zero_free_region_abs
  obtain ⟨delta, hdelta, hbox⟩ :=
    exists_zero_free_box (inghamRouteTUniformZeroFreeBase : ℝ)
  refine ⟨A, delta, hdelta, ?_⟩
  intro s K hK him hre hs1
  rcases le_or_gt 1 s.re with hre1 | hre1
  · exact riemannZeta_ne_zero_of_one_le_re hre1
  by_cases hhigh : (inghamRouteTUniformZeroFreeBase : ℝ) ≤ |s.im|
  · have hbase100 : (100000 : ℝ) ≤ inghamRouteTUniformZeroFreeBase := by
      exact_mod_cast inghamRouteTUniformZeroFreeBase_large
    have h100 : (100000 : ℝ) ≤ |s.im| := hbase100.trans hhigh
    have hdepth : routeTBandDepthRootThreshold ^ 10 ≤
        routeTBinaryHeight |s.im| :=
      inghamRouteTUniformZeroFreeBase_depth.trans
        (routeTBinaryHeight_mono hhigh)
    have hedge_lt_top :
        inghamRouteTUniformZeroFreeWidth A delta K < routeTZeroFreeWidth A K := by
      have hmin := min_le_right delta (routeTZeroFreeWidth A K)
      have hwidth := routeTZeroFreeWidth_pos A K
      unfold inghamRouteTUniformZeroFreeWidth
      nlinarith
    have hmono : routeTZeroFreeWidth A K ≤ routeTZeroFreeWidth A |s.im| :=
      routeTZeroFreeWidth_antitone (A := A) (by
        have hpi : Real.pi < 4 := Real.pi_lt_four
        linarith) him
    have hedge : 1 - routeTZeroFreeWidth A |s.im| < s.re := by
      linarith
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I :=
      (Complex.re_add_im s).symm
    rw [hsplit]
    exact hroute s.re s.im h100 hdepth hre1.le hedge
  · have hedge_lt_delta :
        inghamRouteTUniformZeroFreeWidth A delta K < delta := by
      have hmin := min_le_left delta (routeTZeroFreeWidth A K)
      unfold inghamRouteTUniformZeroFreeWidth
      nlinarith
    exact hbox s (by linarith) hre1.le (le_of_not_ge hhigh) hs1

/-- Above the common Route-T edge, the actual Littlewood zero count vanishes uniformly throughout
the full truncated rectangle. -/
theorem exists_zetaLittlewoodZeroCountAbove_eq_zero_routeT_edge :
    ∃ A delta : ℝ, 0 < delta ∧
      ∀ {sigma : ℝ} {X : ℕ},
        inghamRouteTUniformZeroFreeBase ≤ X →
        1 - inghamRouteTUniformZeroFreeWidth A delta (X : ℝ) ≤ sigma →
        zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma = 0 := by
  obtain ⟨A, delta, hdelta, hzf⟩ := exists_zeta_uniform_routeT_zero_free
  refine ⟨A, delta, hdelta, ?_⟩
  intro sigma X hX hsigma
  unfold zetaLittlewoodZeroCountAbove
  apply Finset.sum_eq_zero
  intro w hw
  have hwf := Finset.mem_filter.mp hw
  have hwmem := mem_zetaResidueUnitClosedRectangleZeros.mp hwf.1
  have hwK := Complex.mem_reProdIm.mp hwmem.1
  have hXR : (inghamRouteTUniformZeroFreeBase : ℝ) ≤ X := by
    exact_mod_cast hX
  have hT : 0 ≤ (X : ℝ) - 2 := by
    have hbase : 100000 ≤ X := inghamRouteTUniformZeroFreeBase_large.trans hX
    have hX2 : (2 : ℕ) ≤ X := by omega
    have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    linarith
  have hwim : w.im ∈ Set.uIcc (-((X : ℝ) - 2)) ((X : ℝ) - 2) := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add,
      add_zero, sub_zero] using hwK.2
  rw [Set.uIcc_of_le (neg_le_self hT)] at hwim
  have himX : |w.im| ≤ (X : ℝ) := (abs_le.2 hwim).trans (by linarith)
  have hw1 : w ≠ 1 := by
    intro heq
    rw [heq, zetaResidueUnit_one] at hwmem
    norm_num at hwmem
  have hzeta : riemannZeta w ≠ 0 :=
    hzf w (X : ℝ) hXR himX (hsigma.trans hwf.2) hw1
  exact False.elim (((zetaResidueUnit_ne_zero_iff hw1).2 hzeta) hwmem.2)

/-- The common-height width is exactly the Route-T contour displacement after shifting the contour
parameter down by one. -/
theorem inghamRouteTUniformZeroFreeWidth_eq_contourShift
    (A delta T : ℝ) :
    inghamRouteTUniformZeroFreeWidth A delta (T + 1) =
      routeTContourShift A delta T := by
  unfold inghamRouteTUniformZeroFreeWidth routeTContourShift
  unfold routeTZeroFreeWidth routeTInverseDelta routeTInverseHeight
  rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  rw [min_comm]
  congr 1
  · ring

/-- The explicit `log(T)^(-9/10)/(log log T)^2` Route-T envelope is eventually a genuine common
zero-free edge for the whole Littlewood rectangle. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_eq_zero_routeT_envelope :
    ∃ A : ℝ,
      ∀ᶠ X : ℕ in Filter.atTop,
        ∀ {sigma : ℝ},
          1 - routeTContourShiftEnvelope A ((X : ℝ) - 1) ≤ sigma →
          zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
            ((X : ℝ) - 2) sigma = 0 := by
  obtain ⟨A, delta, hdelta, hcount⟩ :=
    exists_zetaLittlewoodZeroCountAbove_eq_zero_routeT_edge
  refine ⟨A, ?_⟩
  have hshiftReal := eventually_routeTContourShiftEnvelope_le (A := A) hdelta
  have htend : Filter.Tendsto (fun X : ℕ => (X : ℝ) - 1)
      Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ)
        tendsto_natCast_atTop_atTop
  have hshiftNat :
      ∀ᶠ X : ℕ in Filter.atTop,
        routeTContourShiftEnvelope A ((X : ℝ) - 1) ≤
          routeTContourShift A delta ((X : ℝ) - 1) :=
    htend.eventually hshiftReal
  filter_upwards [hshiftNat,
    Filter.eventually_ge_atTop inghamRouteTUniformZeroFreeBase] with X hshift hX
  intro sigma hsigma
  apply hcount hX
  have hedge : routeTContourShiftEnvelope A ((X : ℝ) - 1) ≤
      inghamRouteTUniformZeroFreeWidth A delta (X : ℝ) := by
    calc
      routeTContourShiftEnvelope A ((X : ℝ) - 1) ≤
          routeTContourShift A delta ((X : ℝ) - 1) := hshift
      _ = inghamRouteTUniformZeroFreeWidth A delta (((X : ℝ) - 1) + 1) :=
        (inghamRouteTUniformZeroFreeWidth_eq_contourShift
          A delta ((X : ℝ) - 1)).symm
      _ = inghamRouteTUniformZeroFreeWidth A delta (X : ℝ) := by ring_nf
  linarith

end

end RHTower.Sieve
