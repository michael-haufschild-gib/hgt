import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import GaloisForLFunctions.RHTower.XiPositivePairedDiagonalSectorCollapse
import GaloisForLFunctions.RHTower.PrimeArchExtendedHausdorffSourceBand
import GaloisForLFunctions.RHTower.PrimeArchCoefficientSignCone
import GaloisForLFunctions.RHTower.PrimeArchExplicitCircleStateReflection
import GaloisForLFunctions.RHTower.PrimeArchMomentTwentyThreeClosure

/-!
# Prime--Gamma positive-paired diagonal on an exterior overlap band

The reciprocal-square radius `1/150`, fourth-trace orientation control, and unconditional
positivity of normalized source moments through index twenty-two together force strict Route-Q
diagonal positivity on `701/100 < Re z ≤ 261/25`, `0 < Im z < 1/2`.  The proof compares the exact
first moment term with a closed linear-weight majorant for the entire remaining tail.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem xiShiftAbsoluteMass_one_eq_hermitianMass :
    xiShiftAbsoluteMass 1 = xiReciprocalSquareHermitianMass := by
  rw [xiShiftAbsoluteMass, xiReciprocalSquareHermitianMass]

/-- Fourth-trace orientation control bounds full second absolute mass relative to its holomorphic
source trace. -/
theorem xiShiftAbsoluteMass_one_le_seventyFour_over_seventyThree_source :
    xiShiftAbsoluteMass 1 ≤
      (74 / 73 : ℝ) * normalizedPrimeArchMoment 1 := by
  have horientation :
      xiThermalOrientationEnergy ≤
        (1 / 147 : ℝ) * xiThermalSecondMoment := by
    rw [xiThermalOrientationEnergy, xiThermalSecondMoment, ← tsum_mul_left]
    exact summable_xiThermalOrientationTerm.tsum_le_tsum
      (fun q => xiThermalOrientationTerm_le_one_over_oneHundredFortySeven_node_sq q)
      (summable_xiThermalNode_sq.mul_left (1 / 147 : ℝ))
  have hmass := xiReciprocalSquareHermitianMass_eq_secondMoment_add_orientation
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  rw [xiShiftAbsoluteMass_one_eq_hermitianMass]
  nlinarith

/-- Every moment after the first is controlled relative to the positive first moment. -/
theorem abs_normalizedPrimeArchMoment_one_add_le_sourceRadius
    (n : ℕ) :
    |normalizedPrimeArchMoment (1 + n)| ≤
      (74 / 73 : ℝ) * (1 / 150 : ℝ) ^ n *
        normalizedPrimeArchMoment 1 := by
  calc
    |normalizedPrimeArchMoment (1 + n)| ≤
        (1 / 150 : ℝ) ^ n * xiShiftAbsoluteMass 1 :=
      abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 1 n
    _ ≤ (1 / 150 : ℝ) ^ n *
        ((74 / 73 : ℝ) * normalizedPrimeArchMoment 1) := by
      exact mul_le_mul_of_nonneg_left
        xiShiftAbsoluteMass_one_le_seventyFour_over_seventyThree_source
        (pow_nonneg (by norm_num) n)
    _ = (74 / 73 : ℝ) * (1 / 150 : ℝ) ^ n *
        normalizedPrimeArchMoment 1 := by ring

/-- The improved reciprocal-square radius extends absolute moment-series convergence from radius
`41/2` to radius `150`. -/
theorem summable_primeArchCircleMomentSeries_of_norm_lt_oneHundredFifty
    {w : ℂ} (hw : ‖w‖ < 150) :
    Summable (fun n : ℕ =>
      (normalizedPrimeArchMoment n : ℂ) * w ^ n) := by
  let ratio : ℝ := ‖w‖ * (1 / 150)
  have hratio0 : 0 ≤ ratio := mul_nonneg (norm_nonneg w) (by norm_num)
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    nlinarith [norm_nonneg w]
  have hmajor : Summable (fun n : ℕ =>
      ratio ^ n * xiShiftAbsoluteMass 0) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_right _
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hm := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 n
  simp only [Nat.zero_add] at hm
  calc
    |normalizedPrimeArchMoment n| * ‖w‖ ^ n ≤
        ((1 / 150 : ℝ) ^ n * xiShiftAbsoluteMass 0) * ‖w‖ ^ n := by
      gcongr
    _ = ratio ^ n * xiShiftAbsoluteMass 0 := by
      dsimp only [ratio]
      rw [mul_pow]
      ring

/-- The improved atom radius extends the exact circle-resolvent identity to its natural disk of
radius `150`. -/
theorem primeArchCircleMomentResolvent_eq_atomicResolvent_of_norm_lt_oneHundredFifty
    {w : ℂ} (hw : ‖w‖ < 150) :
    primeArchCircleMomentResolvent w = primeArchCircleAtomicResolvent w := by
  let lam : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  have hlam : Summable (fun q => ‖lam q‖) := by
    simpa only [lam] using summable_xiZeroCopyReciprocalSquare.norm
  let ratio : ℝ := ‖w‖ * (1 / 150)
  have hratio0 : 0 ≤ ratio := mul_nonneg (norm_nonneg w) (by norm_num)
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    nlinarith [norm_nonneg w]
  have hgeom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hboundTerm : ∀ (n : ℕ) (q : XiZeroCopy),
      ‖w ^ n * lam q ^ (n + 1)‖ ≤ ratio ^ n * ‖lam q‖ := by
    intro n q
    rw [norm_mul, norm_pow, norm_pow, pow_succ]
    have hlamPow : ‖lam q‖ ^ n ≤ (1 / 150 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (by simpa only [lam] using
          (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le) n
    calc
      ‖w‖ ^ n * (‖lam q‖ ^ n * ‖lam q‖) ≤
          ‖w‖ ^ n * ((1 / 150 : ℝ) ^ n * ‖lam q‖) := by
        gcongr
      _ = ratio ^ n * ‖lam q‖ := by
        rw [mul_pow]
        ring
  have hnorm : Summable (fun p : ℕ × XiZeroCopy =>
      ratio ^ p.1 * ‖lam p.2‖) := by
    rw [summable_prod_of_nonneg
      (fun p => mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))]
    constructor
    · intro n
      exact hlam.mul_left (ratio ^ n)
    · apply Summable.of_nonneg_of_le
          (fun n => tsum_nonneg fun _ =>
            mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))
          (fun _ => le_rfl)
      exact (hgeom.mul_right (∑' q : XiZeroCopy, ‖lam q‖)).congr
        (fun n => by rw [← tsum_mul_left])
  have huncurry : Summable (Function.uncurry
      (fun (n : ℕ) (q : XiZeroCopy) => w ^ n * lam q ^ (n + 1))) := by
    apply Summable.of_norm_bounded hnorm
    intro p
    exact hboundTerm p.1 p.2
  rw [primeArchCircleMomentResolvent]
  have hstep : ∀ n : ℕ,
      (normalizedPrimeArchMoment n : ℂ) * w ^ n =
        ∑' q : XiZeroCopy, w ^ n * lam q ^ (n + 1) := by
    intro n
    have hm : (normalizedPrimeArchMoment n : ℂ) =
        xiCentralReciprocalMoment n := by
      rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
      apply Complex.ext
      · simp
      · simp [xiCentralReciprocalMoment_im_eq_zero]
    rw [hm, ← tsum_xiZeroCopyReciprocalSquare_pow n, ← tsum_mul_right]
    apply tsum_congr
    intro q
    dsimp [lam]
    ring
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr
  intro q
  have hwlam : ‖w * lam q‖ < 1 := by
    rw [norm_mul]
    have hq := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
    dsimp only [lam]
    nlinarith [norm_nonneg w]
  change (∑' n : ℕ, w ^ n * lam q ^ (n + 1)) =
    lam q / (1 - lam q * w)
  calc
    (∑' n : ℕ, w ^ n * lam q ^ (n + 1)) =
        lam q * ∑' n : ℕ, (w * lam q) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow, pow_succ]
      ring
    _ = lam q / (1 - lam q * w) := by
      rw [tsum_geometric_of_norm_lt_one hwlam, div_eq_mul_inv]
      congr 2
      ring

/-- The current unconditional source-moment block, in one range statement. -/
theorem normalizedPrimeArchMoment_pos_of_lt_twentyThree
    (n : ℕ) (hn : n < 23) :
    0 < normalizedPrimeArchMoment n := by
  by_cases h18 : n ≤ 18
  · exact normalizedPrimeArchMoment_pos_of_le_eighteen n h18
  by_cases h19 : n = 19
  · simpa [h19] using normalizedPrimeArchMoment_nineteen_pos
  by_cases h20 : n = 20
  · simpa [h20] using normalizedPrimeArchMoment_twenty_pos
  by_cases h21 : n = 21
  · simpa [h21] using normalizedPrimeArchMoment_twentyOne_pos
  have h22 : n = 22 := by omega
  simpa [h22] using normalizedPrimeArchMoment_twentyTwo_pos

/-- The closed twenty-third source moment extends the finite positive prefix by one index. -/
private theorem normalizedPrimeArchMoment_pos_of_lt_twentyFour
    (n : ℕ) (hn : n < 24) :
    0 < normalizedPrimeArchMoment n := by
  by_cases h23 : n = 23
  · simpa [h23] using normalizedPrimeArchMoment_twentyThree_pos
  · exact normalizedPrimeArchMoment_pos_of_lt_twentyThree n (by omega)

/-- Polar form of the imaginary part of an integral complex power. -/
private theorem pow_im_eq_norm_mul_sin_arg (z : ℂ) (n : ℕ) :
    (z ^ n).im = ‖z‖ ^ n * Real.sin (n * z.arg) := by
  have hcomplex : z ^ n =
      ((‖z‖ ^ n : ℝ) : ℂ) *
        Complex.exp (((n * z.arg : ℝ) : ℂ) * Complex.I) := by
    calc
      z ^ n =
          (((‖z‖ : ℝ) : ℂ) *
            Complex.exp ((z.arg : ℂ) * Complex.I)) ^ n := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = (((‖z‖ : ℝ) : ℂ) ^ n) *
          Complex.exp ((z.arg : ℂ) * Complex.I) ^ n := by rw [mul_pow]
      _ = (((‖z‖ : ℝ) : ℂ) ^ n) *
          Complex.exp ((n : ℂ) * ((z.arg : ℂ) * Complex.I)) := by
        rw [← Complex.exp_nat_mul]
      _ = ((‖z‖ ^ n : ℝ) : ℂ) *
          Complex.exp (((n * z.arg : ℝ) : ℂ) * Complex.I) := by
        congr 1
        · norm_num
        · push_cast
          ring_nf
  rw [hcomplex, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num

/-- A narrow first-quadrant argument keeps the first twenty-two even powers in the upper half
plane. -/
private theorem pow_two_mul_im_nonneg_of_exteriorBand
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (n : ℕ) (hn : n ≤ 22) :
    0 ≤ (z ^ (2 * n)).im := by
  have hre : 0 < z.re := by linarith
  have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim.le
  have harg : |z.arg| ≤ (50 / 701 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hre (by
      rw [abs_of_pos hzim]
      nlinarith)
  have hargUpper : z.arg ≤ (50 / 701 : ℝ) := le_trans (le_abs_self _) harg
  have hnR : (n : ℝ) ≤ 22 := by exact_mod_cast hn
  have hangle : ((2 * n : ℕ) : ℝ) * z.arg ≤ Real.pi := by
    have hpi : (2200 / 701 : ℝ) < Real.pi := by
      nlinarith [Real.pi_gt_d20]
    have hmul := mul_le_mul_of_nonneg_left hargUpper
      (show (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) by positivity)
    norm_num at hmul
    push_cast
    nlinarith
  rw [pow_im_eq_norm_mul_sin_arg]
  exact mul_nonneg (pow_nonneg (norm_nonneg z) _)
    (Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg (by positivity) harg0, hangle⟩)

/-- Above the former overlap edge, the narrower argument cone keeps the added twenty-third
even power in the upper half-plane as well. -/
private theorem pow_two_mul_im_nonneg_of_orderTwentyThreeExteriorOverlap
    (z : ℂ) (hzre : (207 / 20 : ℝ) < z.re)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (n : ℕ) (hn : n ≤ 23) :
    0 ≤ (z ^ (2 * n)).im := by
  have hre : 0 < z.re := by linarith
  have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim.le
  have harg : |z.arg| ≤ (10 / 207 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hre (by
      rw [abs_of_pos hzim]
      nlinarith)
  have hargUpper : z.arg ≤ (10 / 207 : ℝ) := le_trans (le_abs_self _) harg
  have hnR : (n : ℝ) ≤ 23 := by exact_mod_cast hn
  have hangle : ((2 * n : ℕ) : ℝ) * z.arg ≤ Real.pi := by
    have hpi : (460 / 207 : ℝ) < Real.pi := by
      nlinarith [Real.pi_gt_d20]
    have hmul := mul_le_mul_of_nonneg_left hargUpper
      (show (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) by positivity)
    norm_num at hmul
    push_cast
    nlinarith
  rw [pow_im_eq_norm_mul_sin_arg]
  exact mul_nonneg (pow_nonneg (norm_nonneg z) _)
    (Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg (by positivity) harg0, hangle⟩)

/-- Geometric-series bound for drift of a complex power from the positive real axis. -/
private theorem norm_pow_sub_re_pow_le_q
    (z : ℂ) (hre : 0 ≤ z.re) (n : ℕ) :
    ‖z ^ (n + 1) - ((z.re : ℂ)) ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * |z.im| * (z.re + |z.im|) ^ n := by
  have hgeom := geom_sum₂_mul z ((z.re : ℂ)) (n + 1)
  rw [← hgeom, norm_mul]
  have hdiff : z - (z.re : ℂ) = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hnormdiff : ‖z - (z.re : ℂ)‖ = |z.im| := by
    rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormdiff]
  have hbound :
      ‖∑ i ∈ Finset.range (n + 1),
          z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ ≤
        ((n : ℝ) + 1) * (z.re + |z.im|) ^ n := by
    have hM : 0 ≤ z.re + |z.im| := by positivity
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            ‖z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (n + 1),
          (z.re + |z.im|) ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hre]
        have hz : ‖z‖ ≤ z.re + |z.im| := by
          have h := Complex.norm_le_abs_re_add_abs_im z
          rwa [abs_of_nonneg hre] at h
        have hre' : z.re ≤ z.re + |z.im| := by
          linarith [abs_nonneg z.im]
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc
          ‖z‖ ^ i * z.re ^ (n + 1 - 1 - i) ≤
              (z.re + |z.im|) ^ i *
                (z.re + |z.im|) ^ (n + 1 - 1 - i) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz i)
              (pow_le_pow_left₀ hre hre' _) (pow_nonneg hre _)
              (pow_nonneg hM i)
          _ = (z.re + |z.im|) ^ (i + (n + 1 - 1 - i)) :=
            (pow_add _ _ _).symm
          _ = (z.re + |z.im|) ^ n := by
            congr 1
            simpa using Nat.add_sub_cancel' hin
      _ = ((n : ℝ) + 1) * (z.re + |z.im|) ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ * |z.im| ≤
        ((n : ℝ) + 1) * (z.re + |z.im|) ^ n * |z.im| :=
      mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = ((n : ℝ) + 1) * |z.im| * (z.re + |z.im|) ^ n := by ring

/-- Imaginary-power Lipschitz bound around the positive real axis. -/
private theorem abs_im_pow_le_two_mul
    (z : ℂ) (hre : 0 ≤ z.re) (n : ℕ) (hn : 1 ≤ n) :
    |(z ^ (2 * n)).im| ≤
      (2 * n : ℝ) * (z.re + |z.im|) ^ (2 * n - 1) * |z.im| := by
  have hbound := norm_pow_sub_re_pow_le_q z hre (2 * n - 1)
  have hexp : 2 * n - 1 + 1 = 2 * n := by omega
  have him :
      (z ^ (2 * n) - ((z.re : ℂ)) ^ (2 * n)).im =
        (z ^ (2 * n)).im := by
    rw [Complex.sub_im]
    have himReal : (((z.re : ℂ)) ^ (2 * n)).im = 0 := by
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_im _
    rw [himReal, sub_zero]
  rw [hexp] at hbound
  calc
    |(z ^ (2 * n)).im| =
        |(z ^ (2 * n) - ((z.re : ℂ)) ^ (2 * n)).im| := by rw [him]
    _ ≤ ‖z ^ (2 * n) - ((z.re : ℂ)) ^ (2 * n)‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ((((2 * n - 1 : ℕ) : ℝ) + 1) * |z.im| *
        (z.re + |z.im|) ^ (2 * n - 1)) := hbound
    _ = (2 * n : ℝ) * (z.re + |z.im|) ^ (2 * n - 1) * |z.im| := by
      have hn2 : 1 ≤ 2 * n := by omega
      rw [Nat.cast_sub hn2]
      push_cast
      ring

private def linearWeightedTail (N : ℕ) (x : ℝ) : ℝ :=
  x ^ (N - 1) * (N * (1 - x)⁻¹ + x / (1 - x) ^ (2 : ℕ))

/-- Exact linear-weight tail, avoiding the fixed-ratio loss in the coarse geometric majorant. -/
private theorem hasSum_nat_add_mul_pow_exact
    (N : ℕ)
    {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => ((N + k : ℕ) : ℝ) * x ^ (N - 1 + k))
      (linearWeightedTail N x) := by
  have hnorm : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have hgeom : HasSum (fun k : ℕ => x ^ k) (1 - x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hlinear : HasSum (fun k : ℕ => (k : ℝ) * x ^ k)
      (x / (1 - x) ^ (2 : ℕ)) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsum := (hgeom.mul_left (N : ℝ)).add hlinear
  have hscaled := hsum.mul_left (x ^ (N - 1))
  apply hscaled.congr_fun
  intro k
  rw [pow_add]
  push_cast
  ring

/-- Exact tail at `x` is bounded by the exact tail at any larger contraction `r`. -/
private theorem tsum_nat_add_mul_pow_le_exact_at
    (N : ℕ)
    {x r : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, ((N + k : ℕ) : ℝ) * x ^ (N - 1 + k)) ≤
      linearWeightedTail N r := by
  have hrAbs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hsum := hasSum_nat_add_mul_pow_exact N hrAbs
  have hpoint : ∀ k : ℕ,
      ((N + k : ℕ) : ℝ) * x ^ (N - 1 + k) ≤
        ((N + k : ℕ) : ℝ) * r ^ (N - 1 + k) := by
    intro k
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx0 hxr (N - 1 + k)) (Nat.cast_nonneg _)
  have hleft : Summable (fun k : ℕ =>
      ((N + k : ℕ) : ℝ) * x ^ (N - 1 + k)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
      hpoint hsum.summable
  rw [← hsum.tsum_eq]
  exact Summable.tsum_le_tsum hpoint hleft hsum.summable

/-- Relative moment decay and the power Lipschitz estimate give a summable majorant with one
dimensionless ratio. -/
private theorem abs_primeArchMomentTerm_one_add_im_le
    (z : ℂ) (hre : 0 ≤ z.re) (j : ℕ) :
    |(((normalizedPrimeArchMoment (1 + j) : ℂ) *
        z ^ (2 * (1 + j))).im)| ≤
      ((74 / 73 : ℝ) * 2 * |z.im| * (z.re + |z.im|) *
        normalizedPrimeArchMoment 1) *
        (((1 + j : ℕ) : ℝ) *
          (((z.re + |z.im|) ^ (2 : ℕ) / 150) ^ j)) := by
  have hm := abs_normalizedPrimeArchMoment_one_add_le_sourceRadius j
  have hp := abs_im_pow_le_two_mul z hre (1 + j) (by omega)
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
  calc
    |normalizedPrimeArchMoment (1 + j)| * |(z ^ (2 * (1 + j))).im| ≤
        ((74 / 73 : ℝ) * (1 / 150 : ℝ) ^ j *
          normalizedPrimeArchMoment 1) *
          ((2 : ℝ) * ((1 + j : ℕ) : ℝ) *
            (z.re + |z.im|) ^ (2 * (1 + j) - 1) * |z.im|) := by
      exact mul_le_mul hm hp (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) j))
          normalizedPrimeArchMoment_one_pos.le)
    _ = ((74 / 73 : ℝ) * 2 * |z.im| * (z.re + |z.im|) *
          normalizedPrimeArchMoment 1) *
          (((1 + j : ℕ) : ℝ) *
            (((z.re + |z.im|) ^ (2 : ℕ) / 150) ^ j)) := by
      rw [show 2 * (1 + j) - 1 = 1 + 2 * j by omega,
        pow_add, pow_one, pow_mul]
      have hxpow :
          (((z.re + |z.im|) ^ (2 : ℕ) / 150) ^ j) =
            (1 / 150 : ℝ) ^ j * ((z.re + |z.im|) ^ (2 : ℕ)) ^ j := by
        rw [show (z.re + |z.im|) ^ (2 : ℕ) / 150 =
          (1 / 150 : ℝ) * (z.re + |z.im|) ^ (2 : ℕ) by ring, mul_pow]
      rw [hxpow]
      push_cast
      ring

private theorem norm_sq_lt_oneHundredFifty_of_exteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 207 / 20)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    ‖z ^ (2 : ℕ)‖ < 150 := by
  have hre : 0 ≤ z.re := by linarith
  have hnormz : ‖z‖ < 217 / 20 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans_lt (by
      rw [abs_of_nonneg hre, abs_of_pos hzim]
      linarith)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

private theorem norm_sq_lt_oneHundredFifty_of_extendedExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 261 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    ‖z ^ (2 : ℕ)‖ < 150 := by
  have hre : 0 ≤ z.re := by linarith
  have hnormz : ‖z‖ < 547 / 50 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans_lt (by
      rw [abs_of_nonneg hre, abs_of_pos hzim]
      linarith)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

private theorem norm_sq_lt_oneHundredFifty_of_orderTwentyThreeExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 1047 / 100)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    ‖z ^ (2 : ℕ)‖ < 150 := by
  have hre : 0 ≤ z.re := by linarith
  have hnormz : ‖z‖ < 1097 / 100 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans_lt (by
      rw [abs_of_nonneg hre, abs_of_pos hzim]
      linarith)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

/-- Exact-tail positivity core. The only quantitative input is domination of the natural
linear-weight tail at one contraction ratio; no frozen geometric relaxation remains. -/
private theorem im_primeArchCircleMomentResolvent_sq_pos_of_linearWeightedTail
    (z : ℂ) (hzre : 0 < z.re) (hzim : 0 < z.im)
    (N : ℕ) (hN : 1 < N)
    (hmoment : ∀ n : ℕ, n < N → 0 ≤ normalizedPrimeArchMoment n)
    (hpower : ∀ n : ℕ, n < N → 0 ≤ (z ^ (2 * n)).im)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hratio : (z.re + |z.im|) ^ (2 : ℕ) / 150 ≤ r)
    (hscalar :
      (74 / 73 : ℝ) * (z.re + |z.im|) *
          linearWeightedTail N r < z.re) :
    0 < (primeArchCircleMomentResolvent (z ^ (2 : ℕ))).im := by
  have hre : 0 ≤ z.re := by linarith
  have hm1 : 0 < normalizedPrimeArchMoment 1 :=
    normalizedPrimeArchMoment_one_pos
  let a : ℝ := z.re + |z.im|
  let x : ℝ := a ^ (2 : ℕ) / 150
  let B : ℝ :=
    (74 / 73) * 2 * |z.im| * a * normalizedPrimeArchMoment 1
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxr : x ≤ r := by
    simpa only [x, a] using hratio
  have hx1 : x < 1 := hxr.trans_lt hr1
  have hxAbs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hnormza : ‖z‖ ≤ a := by
    dsimp only [a]
    have h := Complex.norm_le_abs_re_add_abs_im z
    rwa [abs_of_nonneg hre] at h
  have haSq : a ^ (2 : ℕ) < 150 := by
    dsimp only [x] at hx1
    nlinarith
  have hw : ‖z ^ (2 : ℕ)‖ < 150 := by
    rw [norm_pow]
    nlinarith [sq_nonneg (a - ‖z‖), norm_nonneg z]
  let f : ℕ → ℂ := fun n =>
    (normalizedPrimeArchMoment n : ℂ) * z ^ (2 * n)
  have hsum : Summable f := by
    have h :=
      summable_primeArchCircleMomentSeries_of_norm_lt_oneHundredFifty
        (w := z ^ (2 : ℕ)) hw
    simpa only [f, ← pow_mul] using h
  have hprefixTerm : ∀ n ∈ Finset.range N, 0 ≤ (f n).im := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    have hm := hmoment n hnlt
    have hp := hpower n hnlt
    dsimp only [f]
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hm hp
  have hfirst :
      (f 1).im =
        2 * z.re * z.im * normalizedPrimeArchMoment 1 := by
    dsimp only [f]
    norm_num [pow_two, Complex.mul_im]
    ring
  have hprefix :
      2 * z.re * z.im * normalizedPrimeArchMoment 1 ≤
        ∑ n ∈ Finset.range N, (f n).im := by
    rw [← hfirst]
    exact Finset.single_le_sum hprefixTerm (Finset.mem_range.mpr hN)
  have htail : Summable (fun k : ℕ => f (k + N)) :=
    (summable_nat_add_iff N).2 hsum
  have htailIm : Summable (fun k : ℕ => (f (k + N)).im) :=
    Complex.imCLM.summable htail
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (by norm_num)) (abs_nonneg _)) ha0)
      hm1.le
  have hweight := (hasSum_nat_add_mul_pow_exact N hxAbs).summable
  have htailTerm : ∀ k : ℕ,
      |(f (k + N)).im| ≤
        B * (((N + k : ℕ) : ℝ) * x ^ (N - 1 + k)) := by
    intro k
    have h := abs_primeArchMomentTerm_one_add_im_le z hre (N - 1 + k)
    dsimp only [f, B, x, a]
    simpa only [show k + N = 1 + (N - 1 + k) by omega,
      show 1 + (N - 1 + k) = N + k by omega] using h
  have htailAbsLe :
      (∑' k : ℕ, |(f (k + N)).im|) ≤
        B * linearWeightedTail N r := by
    calc
      (∑' k : ℕ, |(f (k + N)).im|) ≤
          ∑' k : ℕ, B * (((N + k : ℕ) : ℝ) * x ^ (N - 1 + k)) :=
        Summable.tsum_le_tsum htailTerm htailIm.abs (hweight.mul_left B)
      _ = B * ∑' k : ℕ, ((N + k : ℕ) : ℝ) * x ^ (N - 1 + k) := by
        rw [tsum_mul_left]
      _ ≤ B * linearWeightedTail N r :=
        mul_le_mul_of_nonneg_left
          (tsum_nat_add_mul_pow_le_exact_at N hx0 hxr hr0 hr1) hB0
  have htailBound :
      B * linearWeightedTail N r <
        2 * z.re * z.im * normalizedPrimeArchMoment 1 := by
    calc
      B * linearWeightedTail N r =
          (2 * z.im * normalizedPrimeArchMoment 1) *
            ((74 / 73 : ℝ) * a * linearWeightedTail N r) := by
        dsimp only [B]
        rw [abs_of_pos hzim]
        ring
      _ < (2 * z.im * normalizedPrimeArchMoment 1) * z.re :=
        mul_lt_mul_of_pos_left (by simpa only [a] using hscalar) (by positivity)
      _ = 2 * z.re * z.im * normalizedPrimeArchMoment 1 := by ring
  have htailAbsSmall :
      (∑' k : ℕ, |(f (k + N)).im|) <
        2 * z.re * z.im * normalizedPrimeArchMoment 1 :=
    htailAbsLe.trans_lt htailBound
  have htailLower :
      -(∑' k : ℕ, |(f (k + N)).im|) ≤
        ∑' k : ℕ, (f (k + N)).im := by
    have h := Summable.tsum_le_tsum
      (fun k => neg_abs_le ((f (k + N)).im))
      htailIm.abs.neg htailIm
    rw [tsum_neg] at h
    exact h
  have hsplit := hsum.sum_add_tsum_nat_add N
  rw [primeArchCircleMomentResolvent]
  rw [show (fun n : ℕ =>
      (normalizedPrimeArchMoment n : ℂ) * (z ^ (2 : ℕ)) ^ n) = f by
    funext n
    dsimp only [f]
    rw [← pow_mul]]
  rw [← hsplit, Complex.add_im, Complex.im_sum, Complex.im_tsum htail]
  linarith

/-- Twenty-two positive moments dominate the remaining moment tail throughout an explicit
exterior overlap band. -/
theorem im_primeArchCircleMomentResolvent_sq_pos_of_exteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 207 / 20)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    0 < (primeArchCircleMomentResolvent (z ^ (2 : ℕ))).im := by
  have haUpper : z.re + |z.im| < (217 / 20 : ℝ) := by
    rw [abs_of_pos hzim]
    linarith
  have ha0 : (0 : ℝ) ≤ z.re + |z.im| := by positivity
  have hratio : (z.re + |z.im|) ^ (2 : ℕ) / 150 ≤ (157 / 200 : ℝ) := by
    nlinarith [sq_nonneg ((z.re + |z.im|) - 217 / 20)]
  have htailCoefficient :
      0 < (74 / 73 : ℝ) * linearWeightedTail 23 (157 / 200) := by
    simp only [linearWeightedTail]
    positivity
  have hscalar :
      (74 / 73 : ℝ) * (z.re + |z.im|) *
          linearWeightedTail 23 (157 / 200) < z.re := by
    calc
      (74 / 73 : ℝ) * (z.re + |z.im|) *
            linearWeightedTail 23 (157 / 200) =
          ((74 / 73 : ℝ) * linearWeightedTail 23 (157 / 200)) *
              (z.re + |z.im|) := by ring
      _ < ((74 / 73 : ℝ) * linearWeightedTail 23 (157 / 200)) *
              (217 / 20 : ℝ) :=
        mul_lt_mul_of_pos_left haUpper htailCoefficient
      _ < 701 / 100 := by norm_num [linearWeightedTail]
      _ < z.re := hzre
  exact im_primeArchCircleMomentResolvent_sq_pos_of_linearWeightedTail
    z (by linarith) hzim 23 (by norm_num)
    (fun n hn => (normalizedPrimeArchMoment_pos_of_lt_twentyThree n hn).le)
    (fun n hn => pow_two_mul_im_nonneg_of_exteriorBand
      z hzre hzim hzimUpper n (by omega))
    (by norm_num) (by norm_num) hratio hscalar

/-- Exact tail summation enlarges unconditional moment-resolvent positivity from upper edge
`207/20` to `261/25`. The lower edge, which controls the first twenty-two arguments, is
unchanged. -/
theorem im_primeArchCircleMomentResolvent_sq_pos_of_extendedExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 261 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    0 < (primeArchCircleMomentResolvent (z ^ (2 : ℕ))).im := by
  by_cases hold : z.re ≤ 207 / 20
  · exact im_primeArchCircleMomentResolvent_sq_pos_of_exteriorOverlap
      z hzre hold hzim hzimUpper
  · have holdStrict : (207 / 20 : ℝ) < z.re := lt_of_not_ge hold
    have hre : (0 : ℝ) ≤ z.re := by linarith
    have ha0 : (0 : ℝ) ≤ z.re + |z.im| := by positivity
    have haUpper : z.re + |z.im| < (547 / 50 : ℝ) := by
      rw [abs_of_pos hzim]
      linarith
    have hratio : (z.re + |z.im|) ^ (2 : ℕ) / 150 ≤ (399 / 500 : ℝ) := by
      nlinarith [sq_nonneg ((z.re + |z.im|) - 547 / 50)]
    have htailCoefficient :
        0 < (74 / 73 : ℝ) * linearWeightedTail 23 (399 / 500) := by
      simp only [linearWeightedTail]
      positivity
    have hscalar :
        (74 / 73 : ℝ) * (z.re + |z.im|) *
            linearWeightedTail 23 (399 / 500) < z.re := by
      calc
        (74 / 73 : ℝ) * (z.re + |z.im|) *
              linearWeightedTail 23 (399 / 500) =
            ((74 / 73 : ℝ) * linearWeightedTail 23 (399 / 500)) *
                (z.re + |z.im|) := by ring
        _ < ((74 / 73 : ℝ) * linearWeightedTail 23 (399 / 500)) *
                (547 / 50 : ℝ) :=
          mul_lt_mul_of_pos_left haUpper htailCoefficient
        _ < 207 / 20 := by norm_num [linearWeightedTail]
        _ < z.re := holdStrict
    exact im_primeArchCircleMomentResolvent_sq_pos_of_linearWeightedTail
      z (by linarith) hzim 23 (by norm_num)
      (fun n hn => (normalizedPrimeArchMoment_pos_of_lt_twentyThree n hn).le)
      (fun n hn => pow_two_mul_im_nonneg_of_exteriorBand
        z hzre hzim hzimUpper n (by omega))
      (by norm_num) (by norm_num) hratio hscalar

/-- The closed moment of index twenty-three enlarges the exact-tail exterior overlap band to
`701/100 < Re z ≤ 1047/100`.  The new part uses a stricter argument cone to preserve every
prefix term through order twenty-three. -/
theorem im_primeArchCircleMomentResolvent_sq_pos_of_orderTwentyThreeExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 1047 / 100)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2) :
    0 < (primeArchCircleMomentResolvent (z ^ (2 : ℕ))).im := by
  by_cases hold : z.re ≤ 261 / 25
  · exact im_primeArchCircleMomentResolvent_sq_pos_of_extendedExteriorOverlap
      z hzre hold hzim hzimUpper
  · have holdStrict : (261 / 25 : ℝ) < z.re := lt_of_not_ge hold
    have h207 : (207 / 20 : ℝ) < z.re := by linarith
    have hre : (0 : ℝ) ≤ z.re := by linarith
    have ha0 : (0 : ℝ) ≤ z.re + |z.im| := by positivity
    have haUpper : z.re + |z.im| < (1097 / 100 : ℝ) := by
      rw [abs_of_pos hzim]
      linarith
    have hratio : (z.re + |z.im|) ^ (2 : ℕ) / 150 ≤ (803 / 1000 : ℝ) := by
      nlinarith [sq_nonneg ((z.re + |z.im|) - 1097 / 100)]
    have htailCoefficient :
        0 < (74 / 73 : ℝ) * linearWeightedTail 24 (803 / 1000) := by
      simp only [linearWeightedTail]
      positivity
    have hscalar :
        (74 / 73 : ℝ) * (z.re + |z.im|) *
            linearWeightedTail 24 (803 / 1000) < z.re := by
      calc
        (74 / 73 : ℝ) * (z.re + |z.im|) *
              linearWeightedTail 24 (803 / 1000) =
            ((74 / 73 : ℝ) * linearWeightedTail 24 (803 / 1000)) *
                (z.re + |z.im|) := by ring
        _ < ((74 / 73 : ℝ) * linearWeightedTail 24 (803 / 1000)) *
                (1097 / 100 : ℝ) :=
          mul_lt_mul_of_pos_left haUpper htailCoefficient
        _ < 207 / 20 := by norm_num [linearWeightedTail]
        _ < z.re := h207
    exact im_primeArchCircleMomentResolvent_sq_pos_of_linearWeightedTail
      z (by linarith) hzim 24 (by norm_num)
      (fun n hn => (normalizedPrimeArchMoment_pos_of_lt_twentyFour n hn).le)
      (fun n hn => pow_two_mul_im_nonneg_of_orderTwentyThreeExteriorOverlap
        z h207 hzim hzimUpper n (by omega))
      (by norm_num) (by norm_num) hratio hscalar

/-- The circle atomic resolvent at `z²` is exactly the reciprocal-square resolvent sum at `z`. -/
theorem primeArchCircleAtomicResolvent_sq_eq_reciprocalSquare_tsum (z : ℂ) :
    primeArchCircleAtomicResolvent (z ^ (2 : ℕ)) =
      ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  rw [primeArchCircleAtomicResolvent]
  apply tsum_congr
  intro q
  rw [xiReciprocalSquareResolventTerm]
  congr 1
  ring

/-- The analytically continued prime--Gamma reciprocal-square trace is strictly sector-positive
throughout the explicit exterior overlap band. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_pos_of_exteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 207 / 20)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hw := norm_sq_lt_oneHundredFifty_of_exteriorOverlap
    z hzre hzreUpper hzim hzimUpper
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzim hzimUpper hzeta,
    ← primeArchCircleAtomicResolvent_sq_eq_reciprocalSquare_tsum,
    ← primeArchCircleMomentResolvent_eq_atomicResolvent_of_norm_lt_oneHundredFifty hw]
  exact im_primeArchCircleMomentResolvent_sq_pos_of_exteriorOverlap
    z hzre hzreUpper hzim hzimUpper

/-- Exact tail summation propagates the enlarged overlap band to the continued prime--Gamma
reciprocal-square trace. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_pos_of_extendedExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 261 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hw := norm_sq_lt_oneHundredFifty_of_extendedExteriorOverlap
    z hzre hzreUpper hzim hzimUpper
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzim hzimUpper hzeta,
    ← primeArchCircleAtomicResolvent_sq_eq_reciprocalSquare_tsum,
    ← primeArchCircleMomentResolvent_eq_atomicResolvent_of_norm_lt_oneHundredFifty hw]
  exact im_primeArchCircleMomentResolvent_sq_pos_of_extendedExteriorOverlap
    z hzre hzreUpper hzim hzimUpper

/-- The moment-twenty-three exterior-overlap positivity transfers to the continued
prime--Gamma reciprocal-square trace. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_pos_of_orderTwentyThreeExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 1047 / 100)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hw := norm_sq_lt_oneHundredFifty_of_orderTwentyThreeExteriorOverlap
    z hzre hzreUpper hzim hzimUpper
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzim hzimUpper hzeta,
    ← primeArchCircleAtomicResolvent_sq_eq_reciprocalSquare_tsum,
    ← primeArchCircleMomentResolvent_eq_atomicResolvent_of_norm_lt_oneHundredFifty hw]
  exact im_primeArchCircleMomentResolvent_sq_pos_of_orderTwentyThreeExteriorOverlap
    z hzre hzreUpper hzim hzimUpper

/-- Route Q is strictly positive, not merely nonnegative, on the explicit exterior overlap band
`701/100 < Re z ≤ 207/20`. -/
theorem ccmPositivePairedReducedKernel_self_pos_of_exteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 207 / 20)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < ccmPositivePairedReducedKernel z z := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  exact mul_pos
    (mul_pos (by norm_num) (div_pos (by linarith) hzim))
    (continuedPrimeArchReciprocalSquareTrace_im_pos_of_exteriorOverlap
      z hzre hzreUpper hzim hzimUpper hzeta)

/-- Route Q is strictly positive on the exact-tail exterior overlap band
`701/100 < Re z ≤ 261/25`. -/
theorem ccmPositivePairedReducedKernel_self_pos_of_extendedExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 261 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < ccmPositivePairedReducedKernel z z := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  exact mul_pos
    (mul_pos (by norm_num) (div_pos (by linarith) hzim))
    (continuedPrimeArchReciprocalSquareTrace_im_pos_of_extendedExteriorOverlap
      z hzre hzreUpper hzim hzimUpper hzeta)

/-- Route Q is strictly positive on the moment-twenty-three exterior overlap band
`701/100 < Re z ≤ 1047/100`. -/
theorem ccmPositivePairedReducedKernel_self_pos_of_orderTwentyThreeExteriorOverlap
    (z : ℂ) (hzre : (701 / 100 : ℝ) < z.re)
    (hzreUpper : z.re ≤ 1047 / 100)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < ccmPositivePairedReducedKernel z z := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  exact mul_pos
    (mul_pos (by norm_num) (div_pos (by linarith) hzim))
    (continuedPrimeArchReciprocalSquareTrace_im_pos_of_orderTwentyThreeExteriorOverlap
      z hzre hzreUpper hzim hzimUpper hzeta)

/-- Closed source-only statement of strict Route-Q positivity on the exterior overlap band. -/
def PrimeArchPositivePairedDiagonalExteriorOverlap : Prop :=
  ∀ z : ℂ,
    (701 / 100 : ℝ) < z.re → z.re ≤ 207 / 20 →
    0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 < ccmPositivePairedReducedKernel z z

/-- The prime--Gamma source unconditionally satisfies strict Route-Q positivity on the explicit
exterior overlap band. -/
theorem primeArchPositivePairedDiagonalExteriorOverlap :
    PrimeArchPositivePairedDiagonalExteriorOverlap := by
  intro z hzre hzreUpper hzim hzimUpper hzeta
  exact ccmPositivePairedReducedKernel_self_pos_of_exteriorOverlap
    z hzre hzreUpper hzim hzimUpper hzeta

/-- Closed source-only statement of strict Route-Q positivity on the exact-tail overlap band. -/
def PrimeArchPositivePairedDiagonalExtendedExteriorOverlap : Prop :=
  ∀ z : ℂ,
    (701 / 100 : ℝ) < z.re → z.re ≤ 261 / 25 →
    0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 < ccmPositivePairedReducedKernel z z

/-- The prime--Gamma source unconditionally satisfies strict Route-Q positivity on the enlarged
exact-tail exterior overlap band. -/
theorem primeArchPositivePairedDiagonalExtendedExteriorOverlap :
    PrimeArchPositivePairedDiagonalExtendedExteriorOverlap := by
  intro z hzre hzreUpper hzim hzimUpper hzeta
  exact ccmPositivePairedReducedKernel_self_pos_of_extendedExteriorOverlap
    z hzre hzreUpper hzim hzimUpper hzeta

/-- Closed source-only statement of strict Route-Q positivity through the twenty-third moment
overlap band. -/
def PrimeArchPositivePairedDiagonalOrderTwentyThreeExteriorOverlap : Prop :=
  ∀ z : ℂ,
    (701 / 100 : ℝ) < z.re → z.re ≤ 1047 / 100 →
    0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 < ccmPositivePairedReducedKernel z z

/-- The prime--Gamma source unconditionally satisfies strict Route-Q positivity through the
closed twenty-third source moment. -/
theorem primeArchPositivePairedDiagonalOrderTwentyThreeExteriorOverlap :
    PrimeArchPositivePairedDiagonalOrderTwentyThreeExteriorOverlap := by
  intro z hzre hzreUpper hzim hzimUpper hzeta
  exact ccmPositivePairedReducedKernel_self_pos_of_orderTwentyThreeExteriorOverlap
    z hzre hzreUpper hzim hzimUpper hzeta

end

end RHTower
