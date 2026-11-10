import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.MovingPhaseBranch
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The factorial logarithm profile of the Liouville transition

The coefficients `(-iπ)^k/k!` have total mass `-2`. Their shifted
prime logarithms separate the quadratic residue scale from the
spectral profile on `Re w>-1`.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The nonconstant exponential coefficients, indexed from zero. -/
def exponentialPhaseCoefficient (n : ℕ) : ℂ :=
  (-(Real.pi : ℂ) * I) ^ (n + 1) / ((n + 1).factorial : ℂ)

/-- Factorial sum of shifted logarithms on the right of its first branch point. -/
def quadraticResidueScalingLog (w : ℂ) : ℂ :=
  ∑' n : ℕ, exponentialPhaseCoefficient n * Complex.log (w + ((n + 1 : ℕ) : ℂ))

/-- The full spectral profile of the quadratic residue scale. -/
def quadraticResidueScalingProfile (w : ℂ) : ℂ :=
  riemannZeta 2 * Complex.exp (-quadraticResidueScalingLog w)


private theorem hasSum_complex_exponential (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  simpa only [Complex.exp_eq_exp_ℂ, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z)

theorem exponentialPhaseCoefficient_zero : exponentialPhaseCoefficient 0 = -(Real.pi : ℂ) * I := by
  simp only [exponentialPhaseCoefficient, zero_add, Nat.factorial_one, Nat.cast_one, pow_one, div_one]

theorem norm_exponentialPhaseCoefficient (n : ℕ) :
    ‖exponentialPhaseCoefficient n‖ = Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [exponentialPhaseCoefficient, norm_div, norm_pow, norm_mul, norm_neg, norm_I,
    mul_one, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_natCast]

theorem summable_norm_exponentialPhaseCoefficient :
    Summable (fun n : ℕ => ‖exponentialPhaseCoefficient n‖) := by
  simpa only [norm_exponentialPhaseCoefficient] using
    (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial Real.pi)

theorem summable_exponentialPhaseCoefficient : Summable exponentialPhaseCoefficient :=
  Summable.of_norm summable_norm_exponentialPhaseCoefficient

/-- The coefficient mass is exactly minus two, fixing the residue exponent. -/
theorem tsum_exponentialPhaseCoefficient : (∑' n : ℕ, exponentialPhaseCoefficient n) = -2 := by
  have hh := hasSum_complex_exponential (-(Real.pi : ℂ) * I)
  have hs := hh.summable.sum_add_tsum_nat_add 1
  rw [hh.tsum_eq] at hs
  have he : (1 : ℂ) + (∑' n : ℕ, exponentialPhaseCoefficient n) = -1 := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      exponentialPhaseCoefficient, hh.tsum_eq, neg_mul, Complex.exp_neg_pi_mul_I] using hs
  linear_combination he

private theorem norm_exponentialPhaseCoefficient_mul_index (n : ℕ) :
    ‖exponentialPhaseCoefficient n‖ * (n + 1 : ℝ) =
      Real.pi * (Real.pi ^ n / (n.factorial : ℝ)) := by
  rw [norm_exponentialPhaseCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hn, hf]

/-- Linear growth of the logarithm is harmless under factorial weights. -/
theorem summable_exponentialPhaseCoefficient_weight (C : ℝ) :
    Summable (fun n : ℕ => ‖exponentialPhaseCoefficient n‖ * (C + (n + 1 : ℝ))) := by
  have hs := (summable_norm_exponentialPhaseCoefficient.mul_left C).add
    ((Real.summable_pow_div_factorial Real.pi).mul_left Real.pi)
  refine hs.congr (fun n => ?_)
  rw [← norm_exponentialPhaseCoefficient_mul_index]
  ring

theorem norm_log_le_linear {z : ℂ} {η M : ℝ} (hη : 0 < η)
    (hl : η ≤ z.re) (hu : ‖z‖ ≤ M) (hM : 0 ≤ M) :
    ‖Complex.log z‖ ≤ |Real.log η| + M + Real.pi := by
  have hηz : η ≤ ‖z‖ := hl.trans (Complex.re_le_norm z)
  have hlogl := Real.log_le_log hη hηz
  have hlogu : Real.log ‖z‖ ≤ M := (Real.log_le_self (norm_nonneg z)).trans hu
  have ha : |Real.log ‖z‖| ≤ |Real.log η| + M := by
    rw [abs_le]
    constructor
    · linarith only [neg_abs_le (Real.log η), hlogl, hM]
    · linarith only [hlogu, abs_nonneg (Real.log η)]
  rw [Complex.log]
  calc
    ‖(Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * I‖ ≤
        ‖(Real.log ‖z‖ : ℂ)‖ + ‖(z.arg : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by simp
    _ ≤ |Real.log η| + M + Real.pi := add_le_add ha (Complex.abs_arg_le_pi z)

/-- Every factorial logarithm tail has a normally convergent holomorphic region. -/
private theorem factorialLogTail_normal_bound (j : ℕ) {w : ℂ}
    (hw : -(j + 1 : ℝ) < w.re) :
    ∃ r : ℝ, 0 < r ∧ ∃ b : ℕ → ℝ, Summable b ∧
      ∀ n : ℕ, ∀ z ∈ Metric.ball w r,
        ‖exponentialPhaseCoefficient (n + j) *
          Complex.log (z + ((n + j + 1 : ℕ) : ℂ))‖ ≤ b n ∧
        0 < (z + ((n + j + 1 : ℕ) : ℂ)).re := by
  let r := (w.re + (j + 1 : ℝ)) / 2
  have hr : 0 < r := by dsimp [r]; linarith only [hw]
  let C := |Real.log r| + ‖w‖ + r + Real.pi
  let b : ℕ → ℝ := fun n => ‖exponentialPhaseCoefficient (n + j)‖ *
    (C + ((n + j : ℕ) + 1 : ℝ))
  have hb : Summable b := by
    exact (summable_nat_add_iff j).mpr (summable_exponentialPhaseCoefficient_weight C)
  refine ⟨r, hr, b, hb, ?_⟩
  intro n z hz
  have hzn : ‖z - w‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hRe := Complex.re_le_norm (w - z)
  rw [norm_sub_rev] at hRe
  simp only [Complex.sub_re] at hRe
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : r ≤ (z + ((n + j + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one]
    dsimp [r] at hzn ⊢
    linarith only [hRe, hzn, hn]
  have hzbound : ‖z‖ ≤ ‖w‖ + r := by
    calc
      ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + r := by linarith only [hzn]
  have hu : ‖z + ((n + j + 1 : ℕ) : ℂ)‖ ≤ ‖w‖ + r + (n + j + 1 : ℕ) := by
    calc
      _ ≤ ‖z‖ + ‖((n + j + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + (n + j + 1 : ℕ) := by rw [Complex.norm_natCast]
      _ ≤ _ := add_le_add hzbound le_rfl
  have hlog := norm_log_le_linear hr hl hu (by positivity)
  refine ⟨?_, hr.trans_le hl⟩
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hlog (norm_nonneg _)).trans_eq
  dsimp [b, C]
  push_cast
  ring

private theorem summable_factorialLogTail (j : ℕ) {w : ℂ} (hw : -(j + 1 : ℝ) < w.re) :
    Summable (fun n : ℕ => exponentialPhaseCoefficient (n + j) *
      Complex.log (w + ((n + j + 1 : ℕ) : ℂ))) := by
  obtain ⟨r, hr, b, hb, hbound⟩ := factorialLogTail_normal_bound j hw
  exact Summable.of_norm_bounded hb (fun n => (hbound n w (Metric.mem_ball_self hr)).1)

private theorem analyticAt_factorialLogTail (j : ℕ) {w : ℂ} (hw : -(j + 1 : ℝ) < w.re) :
    AnalyticAt ℂ (fun z => ∑' n : ℕ, exponentialPhaseCoefficient (n + j) *
      Complex.log (z + ((n + j + 1 : ℕ) : ℂ))) w := by
  obtain ⟨r, hr, b, hb, hbound⟩ := factorialLogTail_normal_bound j hw
  have hd : DifferentiableOn ℂ (fun z => ∑' n : ℕ, exponentialPhaseCoefficient (n + j) *
      Complex.log (z + ((n + j + 1 : ℕ) : ℂ))) (Metric.ball w r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hb (fun n => ?_) Metric.isOpen_ball
      (fun n z hz => (hbound n z hz).1)
    intro z hz
    have hslit : z + ((n + j + 1 : ℕ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hbound n z hz).2)
    exact (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).clog hslit)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-- The analytic unit after the first logarithmic branch of the scaling profile is removed. -/
def quadraticResidueScalingBranchUnit (w : ℂ) : ℂ :=
  riemannZeta 2 * Complex.exp (-(∑' n : ℕ, exponentialPhaseCoefficient (n + 1) *
    Complex.log (w + ((n + 1 + 1 : ℕ) : ℂ))))

theorem analyticOnNhd_quadraticResidueScalingLog :
    AnalyticOnNhd ℂ quadraticResidueScalingLog {w | -1 < w.re} := by
  intro w hw
  change -1 < w.re at hw
  change AnalyticAt ℂ (fun z => ∑' n : ℕ, exponentialPhaseCoefficient n *
    Complex.log (z + ((n + 1 : ℕ) : ℂ))) w
  simpa only [Nat.add_zero] using analyticAt_factorialLogTail 0 (w := w)
    (by simpa only [Nat.cast_zero, zero_add] using hw)

theorem analyticOnNhd_quadraticResidueScalingProfile :
    AnalyticOnNhd ℂ quadraticResidueScalingProfile {w | -1 < w.re} := by
  intro w hw
  exact analyticAt_const.mul (analyticOnNhd_quadraticResidueScalingLog w hw).neg.cexp

private theorem zeta_two_ne_zero : riemannZeta (2 : ℂ) ≠ 0 := by
  rw [← exp_canonicalEulerLogZeta_eq_riemannZeta (s := (2 : ℂ)) (by norm_num)]
  exact Complex.exp_ne_zero _

theorem quadraticResidueScalingProfile_ne_zero (w : ℂ) : quadraticResidueScalingProfile w ≠ 0 :=
  mul_ne_zero zeta_two_ne_zero (Complex.exp_ne_zero _)

theorem analyticAt_quadraticResidueScalingBranchUnit :
    AnalyticAt ℂ quadraticResidueScalingBranchUnit (-1) := by
  exact analyticAt_const.mul (analyticAt_factorialLogTail 1 (w := (-1 : ℂ)) (by norm_num)).neg.cexp

theorem quadraticResidueScalingBranchUnit_ne_zero (w : ℂ) : quadraticResidueScalingBranchUnit w ≠ 0 :=
  mul_ne_zero zeta_two_ne_zero (Complex.exp_ne_zero _)

/-- The first branch exponent of the limiting profile is exactly `iπ`. -/
theorem quadraticResidueScalingProfile_factorization {w : ℂ} (hw : -1 < w.re) :
    quadraticResidueScalingProfile w = quadraticResidueScalingBranchUnit w *
      Complex.exp ((Real.pi : ℂ) * I * Complex.log (w + 1)) := by
  have hs := summable_factorialLogTail 0 (w := w) (by
    simpa only [Nat.cast_zero, zero_add] using hw)
  simp only [Nat.add_zero] at hs
  have he := hs.tsum_eq_zero_add
  change quadraticResidueScalingLog w =
    exponentialPhaseCoefficient 0 * Complex.log (w + ((0 + 1 : ℕ) : ℂ)) +
      (∑' n : ℕ, exponentialPhaseCoefficient (n + 1) *
        Complex.log (w + ((n + 1 + 1 : ℕ) : ℂ))) at he
  rw [quadraticResidueScalingProfile, he, exponentialPhaseCoefficient_zero,
    show ((0 + 1 : ℕ) : ℂ) = 1 by norm_num, neg_add, Complex.exp_add,
    quadraticResidueScalingBranchUnit]
  rw [show -(-(Real.pi : ℂ) * I * Complex.log (w + 1)) =
    (Real.pi : ℂ) * I * Complex.log (w + 1) by ring]
  ring

/-- Quadratic residue order conceals a profile which is not a polynomial of any degree. -/
theorem quadraticResidueScalingProfile_not_polynomial :
    ¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, -1 < w.re → quadraticResidueScalingProfile w = P.eval w := by
  rintro ⟨P, hP⟩
  apply oscillatoryLogBranch_no_continuous_extension
    analyticAt_quadraticResidueScalingBranchUnit.continuousAt
    (quadraticResidueScalingBranchUnit_ne_zero (-1)) P.continuous.continuousAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hw : -1 < ((-1 : ℂ) + (x : ℂ)).re := by
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hx]
  rw [← hP _ hw, quadraticResidueScalingProfile_factorization hw,
    show (-1 : ℂ) + (x : ℂ) + 1 = (x : ℂ) by ring]


/-- A branch-fixed total version of the renormalized prime logarithm. -/
def regularizedPrimeLog (s : ℂ) : ℂ :=
  if 1 < s.re then coronaPrimeZeta s + Complex.log (s - 1) else primeLogRegularPart s

theorem regularizedPrimeLog_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    regularizedPrimeLog s = coronaPrimeZeta s + Complex.log (s - 1) := if_pos hs

theorem regularizedPrimeLog_one : regularizedPrimeLog 1 = -hullRem 1 (twist 0) := by
  rw [regularizedPrimeLog, if_neg (by norm_num), primeLogRegularPart_one]

/-- The pole subtraction genuinely extends analytically through one. -/
theorem analyticAt_regularizedPrimeLog_one : AnalyticAt ℂ regularizedPrimeLog 1 := by
  obtain ⟨r, hr, _, he⟩ := exists_primeLogRegularPart_germ
  apply analyticAt_primeLogRegularPart_one.congr
  filter_upwards [Metric.ball_mem_nhds (1 : ℂ) hr] with s hs
  unfold regularizedPrimeLog
  split_ifs with h
  · exact (he s hs h).symm
  · rfl

theorem analyticAt_regularizedPrimeLog_right {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ regularizedPrimeLog s := by
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ coronaPrimeZeta {z | 1 < z.re} :=
    fun z hz => (differentiableAt_coronaPrimeZeta hz).differentiableWithinAt
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (z - 1)) s :=
    (analyticAt_id.sub analyticAt_const).clog (Complex.mem_slitPlane_iff.mpr (Or.inl (by
      change 0 < (s - 1).re
      simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs)))
  apply ((hd.analyticAt (ho.mem_nhds hs)).add hlog).congr
  filter_upwards [ho.mem_nhds hs] with z hz
  exact (regularizedPrimeLog_of_re_gt_one hz).symm

private theorem norm_coronaPrimeZeta_le {b : ℝ} (hb : 1 < b) {s : ℂ} (hs : b ≤ s.re) :
    ‖coronaPrimeZeta s‖ ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-b) := by
  have hsum := summable_primes_rpow (show -b < -1 by linarith only [hb])
  have hsn := summable_norm_coronaPrimeEigenvalue (hb.trans_le hs)
  unfold coronaPrimeZeta
  refine (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum (fun p => ?_) hsn hsum)
  rw [norm_coronaPrimeEigenvalue]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (neg_le_neg hs)

/-- Uniform linear growth in the shift index suffices for the factorial limit. -/
theorem regularizedPrimeLog_scaled_bound {η M : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ w : ℂ,
      η ≤ w.re + 1 → ‖w‖ ≤ M → ∀ n : ℕ,
        ‖regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ)))‖ ≤ C + (n + 1 : ℝ) := by
  let C₀ := ‖regularizedPrimeLog 1‖ + 1
  have hlocal : ∀ᶠ s in 𝓝 (1 : ℂ), ‖regularizedPrimeLog s‖ < C₀ :=
    analyticAt_regularizedPrimeLog_one.continuousAt.norm.tendsto.eventually
      (gt_mem_nhds (by dsimp [C₀]; linarith only [norm_nonneg (regularizedPrimeLog 1)]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  let d := η * ε / (M + 1)
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hMp : 0 < M + 1 := by linarith only [hM]
  have hd : 0 < d := by dsimp [d]; positivity
  let B := (∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + d))) + |Real.log d| + M + Real.pi
  let C := max C₀ B
  have hC₀ : C₀ ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 0 ≤ C := (by dsimp [C₀]; positivity : 0 ≤ C₀).trans hC₀
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 w hw hwM n
  let k : ℝ := n + 1
  have hk : 1 ≤ k := by
    dsimp [k]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hn]
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  by_cases htzero : t = 0
  · subst t
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    change ‖regularizedPrimeLog 1‖ ≤ C + k
    dsimp [C₀] at hC₀
    linarith only [hC₀, hk0]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
  let δ : ℂ := (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ))
  have hδre : δ.re = t * (w.re + k) := by
    simp only [δ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re, k]
  have hkw : η * k ≤ w.re + k := by
    have hp := mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr hk)
    nlinarith only [hp, hw]
  have hMk : M + k ≤ (M + 1) * k := by
    have hp := mul_nonneg hM0 (sub_nonneg.mpr hk)
    nlinarith only [hp]
  have harg : ‖w + ((n + 1 : ℕ) : ℂ)‖ ≤ M + k := by
    calc
      _ ≤ ‖w‖ + ‖((n + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + k := by rw [Complex.norm_natCast]; simp only [Nat.cast_add, Nat.cast_one, k]
      _ ≤ _ := add_le_add hwM le_rfl
  have hδn : ‖δ‖ ≤ t * (M + k) := by
    dsimp only [δ]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left harg ht
  have hδM : ‖δ‖ ≤ M + k := by
    apply hδn.trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (add_nonneg hM0 hk0)
  have hsector : η * ‖δ‖ ≤ (M + 1) * δ.re := by
    calc
      _ ≤ η * (t * (M + k)) := mul_le_mul_of_nonneg_left hδn hη.le
      _ ≤ η * (t * ((M + 1) * k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMk ht) hη.le
      _ = ((M + 1) * t) * (η * k) := by ring
      _ ≤ ((M + 1) * t) * (w.re + k) :=
        mul_le_mul_of_nonneg_left hkw (mul_nonneg hMp.le ht)
      _ = _ := by rw [hδre]; ring
  have hδpos : 0 < δ.re := by
    rw [hδre]
    exact mul_pos htp ((mul_pos hη (lt_of_lt_of_le zero_lt_one hk)).trans_le hkw)
  have hs : 1 < (1 + δ).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hδpos]
  change ‖regularizedPrimeLog (1 + δ)‖ ≤ C + k
  by_cases hsmall : ‖δ‖ < ε
  · have hh := hball (show 1 + δ ∈ Metric.ball (1 : ℂ) ε by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hsmall)
    exact hh.le.trans (hC₀.trans (le_add_of_nonneg_right hk0))
  have hdre : d ≤ δ.re := by
    apply (div_le_iff₀ hMp).mpr
    calc
      η * ε ≤ η * ‖δ‖ := mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) hη.le
      _ ≤ (M + 1) * δ.re := hsector
      _ = δ.re * (M + 1) := by ring
  have hP : ‖coronaPrimeZeta (1 + δ)‖ ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + d)) :=
    norm_coronaPrimeZeta_le (by linarith only [hd]) (by
      simp only [Complex.add_re, Complex.one_re]
      linarith only [hdre])
  have hlog := norm_log_le_linear hd hdre hδM (add_nonneg hM0 hk0)
  rw [regularizedPrimeLog_of_re_gt_one hs, add_sub_cancel_left]
  calc
    _ ≤ ‖coronaPrimeZeta (1 + δ)‖ + ‖Complex.log δ‖ := norm_add_le _ _
    _ ≤ (∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + d))) +
        (|Real.log d| + (M + k) + Real.pi) := add_le_add hP hlog
    _ ≤ C + k := by dsimp [B] at hBC; linarith only [hBC]


private def exponentialPhaseShiftTerm (t : ℝ) (s : ℂ) (p : Nat.Primes) (n : ℕ) : ℂ :=
  exponentialPhaseCoefficient n *
    Complex.exp (-(s + ((n + 1 : ℕ) : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))

private theorem norm_exponentialPhaseShiftTerm_le {t : ℝ} (ht : 0 ≤ t) (s : ℂ)
    (p : Nat.Primes) (n : ℕ) :
    ‖exponentialPhaseShiftTerm t s p n‖ ≤
      (p : ℝ) ^ (-(s.re + t)) * ‖exponentialPhaseCoefficient n‖ := by
  rw [exponentialPhaseShiftTerm, norm_mul, norm_exponentialPrime_damping]
  apply (mul_le_mul_of_nonneg_left ?_ (norm_nonneg (exponentialPhaseCoefficient n))).trans_eq (mul_comm _ _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one, Complex.one_re]
  nlinarith only [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ht]

private theorem summable_exponentialPhaseShiftTerm {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 1 < s.re + t) :
    Summable (fun pn : Nat.Primes × ℕ => exponentialPhaseShiftTerm t s pn.1 pn.2) := by
  have hp := summable_primes_rpow (show -(s.re + t) < -1 by linarith only [hs])
  have hb := Summable.mul_of_nonneg hp summable_norm_exponentialPhaseCoefficient
    (fun p => by positivity) (fun n => norm_nonneg _)
  exact Summable.of_norm_bounded hb (fun pn => norm_exponentialPhaseShiftTerm_le ht s pn.1 pn.2)

private theorem hasSum_complex_exp_sub_one (z : ℂ) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1).factorial : ℂ)) (Complex.exp z - 1) := by
  have hh := hasSum_complex_exponential z
  have hs := hh.summable.sum_add_tsum_nat_add 1
  rw [hh.tsum_eq] at hs
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hs
  have ht : Summable (fun n : ℕ => z ^ (n + 1) / ((n + 1).factorial : ℂ)) :=
    (summable_nat_add_iff 1).mpr hh.summable
  have he : (∑' n : ℕ, z ^ (n + 1) / ((n + 1).factorial : ℂ)) = Complex.exp z - 1 := by
    linear_combination hs
  rw [← he]
  exact ht.hasSum

private theorem exponentialPhaseShiftTerm_eq (t : ℝ) (s : ℂ) (p : Nat.Primes) (n : ℕ) :
    exponentialPhaseShiftTerm t s p n =
      ((-(Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))) ^ (n + 1) /
        ((n + 1).factorial : ℂ)) * Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  rw [exponentialPhaseShiftTerm, exponentialPhaseCoefficient,
    show -(s + ((n + 1 : ℕ) : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
      ((n + 1 : ℕ) : ℂ) * (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) +
        (-s * (Real.log (p : ℝ) : ℂ)) by ring,
    Complex.exp_add, Complex.exp_nat_mul, mul_pow]
  ring

private theorem tsum_exponentialPhaseShiftTerm (t : ℝ) (s : ℂ) (p : Nat.Primes) :
    (∑' n : ℕ, exponentialPhaseShiftTerm t s p n) =
      (exponentialPrimePhase p (t : ℂ) - 1) * Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  have hh := (hasSum_complex_exp_sub_one
    (-(Real.pi : ℂ) * I * Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)))).mul_right
      (Complex.exp (-s * (Real.log (p : ℝ) : ℂ)))
  rw [tsum_congr (fun n => exponentialPhaseShiftTerm_eq t s p n)]
  exact hh.tsum_eq

/-- Absolute Fubini expansion of the actual first-prime deformation. -/
theorem deformationPrimeSum_exponentialPhase_shifted {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 1 < s.re + t) :
    deformationPrimeSum (exponentialPhaseGauge t) s =
      ∑' n : ℕ, exponentialPhaseCoefficient n * coronaPrimeZeta (s + ((n + 1 : ℕ) : ℂ) * (t : ℂ)) := by
  have hp := summable_exponentialPhaseShiftTerm ht hs
  calc
    _ = ∑' p : Nat.Primes, ∑' n : ℕ, exponentialPhaseShiftTerm t s p n := by
      unfold deformationPrimeSum
      apply tsum_congr
      intro p
      rw [tsum_exponentialPhaseShiftTerm, ← exponentialPrimePhase_eq_twist,
        ← prime_cexp_decay p s]
      simp only [primeFrequency, neg_mul]
    _ = ∑' n : ℕ, ∑' p : Nat.Primes, exponentialPhaseShiftTerm t s p n :=
      (Summable.tsum_comm (f := fun p n => exponentialPhaseShiftTerm t s p n) hp).symm
    _ = _ := by
      apply tsum_congr
      intro n
      unfold exponentialPhaseShiftTerm
      rw [tsum_mul_left]
      congr 1
      unfold coronaPrimeZeta
      apply tsum_congr
      intro p
      rw [coronaPrimeEigenvalue, ← prime_cexp_decay]
      simp only [primeFrequency, neg_mul]

/-- The regular part remaining after all shifted prime logarithms are subtracted. -/
def scaledPrimeLogRemainder (t : ℝ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, exponentialPhaseCoefficient n *
    regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ)))

theorem scaledPrimeLogRemainder_zero (w : ℂ) :
    scaledPrimeLogRemainder 0 w = 2 * hullRem 1 (twist 0) := by
  simp only [scaledPrimeLogRemainder, Complex.ofReal_zero, zero_mul, add_zero,
    regularizedPrimeLog_one, tsum_mul_right, tsum_exponentialPhaseCoefficient]
  ring

/-- Compact spectral sets admit a jointly continuous renormalized prime sum through `t=0`. -/
theorem continuousOn_scaledPrimeLogRemainder {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -1 < w.re}) :
    ContinuousOn (fun q : ℝ × ℂ => scaledPrimeLogRemainder q.1 q.2) (Icc 0 1 ×ˢ K) := by
  by_cases hK0 : K = ∅
  · subst K
    simp
  have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK0
  obtain ⟨m, hm, hmin⟩ := hK.exists_isMinOn (f := fun w : ℂ => w.re + 1) hne
    ((Complex.continuous_re.add continuous_const).continuousOn)
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn (f := fun w : ℂ => ‖w‖) hne continuous_norm.continuousOn
  have hmBound : ∀ w ∈ K, m.re + 1 ≤ w.re + 1 := hmin
  have hbBound : ∀ w ∈ K, ‖w‖ ≤ ‖b‖ := hmax
  let η := min (m.re + 1) 1
  let M := max 1 ‖b‖
  have hmre : -1 < m.re := hhalf hm
  have hη : 0 < η := lt_min (by linarith only [hmre]) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hM : 1 ≤ M := le_max_left _ _
  have hηw (w : ℂ) (hw : w ∈ K) : η ≤ w.re + 1 :=
    (min_le_left _ _).trans (hmBound w hw)
  have hMw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ M :=
    (hbBound w hw).trans (le_max_right _ _)
  obtain ⟨C, _, hbound⟩ := regularizedPrimeLog_scaled_bound hη hη1 hM
  change ContinuousOn (fun q : ℝ × ℂ => ∑' n : ℕ, exponentialPhaseCoefficient n *
    regularizedPrimeLog (1 + (q.1 : ℂ) * (q.2 + ((n + 1 : ℕ) : ℂ)))) (Icc 0 1 ×ˢ K)
  refine continuousOn_tsum (fun n q hq => ?_)
    (summable_exponentialPhaseCoefficient_weight C) (fun n q hq => ?_)
  · have hmap : ContinuousAt (fun v : ℝ × ℂ =>
        1 + (v.1 : ℂ) * (v.2 + ((n + 1 : ℕ) : ℂ))) q := by fun_prop
    have hE : ContinuousAt regularizedPrimeLog
        (1 + (q.1 : ℂ) * (q.2 + ((n + 1 : ℕ) : ℂ))) := by
      by_cases ht0 : q.1 = 0
      · simpa only [ht0, Complex.ofReal_zero, zero_mul, add_zero] using
          analyticAt_regularizedPrimeLog_one.continuousAt
      · apply (analyticAt_regularizedPrimeLog_right ?_).continuousAt
        have ht : 0 < q.1 := lt_of_le_of_ne hq.1.1 (Ne.symm ht0)
        have hw : -1 < q.2.re := hhalf hq.2
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hp : 0 < q.1 * (q.2.re + (n + 1 : ℝ)) :=
          mul_pos ht (by linarith only [hw, hn])
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.natCast_re, Nat.cast_add, Nat.cast_one]
        linarith only [hp]
    exact ((hE.comp (g := regularizedPrimeLog)
      (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * (v.2 + ((n + 1 : ℕ) : ℂ))) hmap).const_mul
        (exponentialPhaseCoefficient n)).continuousWithinAt
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hbound q.1 hq.1.1 hq.1.2 q.2 (hηw q.2 hq.2) (hMw q.2 hq.2) n) (norm_nonneg _)

theorem nhdsGT_zero_le_Icc {a : ℝ} (ha : 0 < a) :
    (𝓝[>] (0 : ℝ)) ≤ 𝓝[Icc (0 : ℝ) a] 0 := by
  change (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 ⊓ 𝓟 (Icc (0 : ℝ) a)
  refine le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr ?_)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ha)] with t ht hta
  exact ⟨ht.le, hta.le⟩

/-- The renormalized shifted-prime sum has its exact locally uniform boundary value. -/
theorem tendstoUniformlyOn_scaledPrimeLogRemainder {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -1 < w.re}) :
    TendstoUniformlyOn scaledPrimeLogRemainder (fun _ => 2 * hullRem 1 (twist 0))
      (𝓝[>] (0 : ℝ)) K := by
  have hc := continuousOn_scaledPrimeLogRemainder hK hhalf
  have hu : TendstoUniformlyOn scaledPrimeLogRemainder (scaledPrimeLogRemainder 0)
      (𝓝[Icc (0 : ℝ) 1] 0) K :=
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn
      ⟨le_rfl, zero_le_one⟩
  have hu' : TendstoUniformlyOn scaledPrimeLogRemainder (scaledPrimeLogRemainder 0)
      (𝓝[>] (0 : ℝ)) K := fun V hV => Filter.Eventually.filter_mono (nhdsGT_zero_le_Icc zero_lt_one) (hu V hV)
  have hzero : scaledPrimeLogRemainder 0 = fun _ => 2 * hullRem 1 (twist 0) :=
    funext scaledPrimeLogRemainder_zero
  rwa [hzero] at hu'


private theorem liouville_localRem_pair (p : Nat.Primes) :
    localRem 1 (twist 0) p + localRem 1 (twist (exponentialPhaseGauge 0)) p =
      -Complex.log (1 - (p : ℂ) ^ (-(2 : ℂ))) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  let q : ℝ := (p : ℝ)⁻¹
  have hq : 0 < q := inv_pos.mpr hp
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← one_div, div_lt_iff₀ hp, one_mul]
    exact hp1
  have hd : (p : ℂ) ^ (-(1 : ℂ)) = (q : ℂ) := by
    rw [Complex.cpow_neg_one]
    simp only [q, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hd2 : (p : ℂ) ^ (-(2 : ℂ)) = (q : ℂ) * (q : ℂ) := by
    rw [show -(2 : ℂ) = -(1 : ℂ) + -(1 : ℂ) by ring,
      Complex.cpow_add _ _ (by exact_mod_cast p.2.ne_zero), hd]
  have hm : 0 < 1 - q := sub_pos.mpr hq1
  have hplus : 0 < 1 + q := by linarith only [hq]
  have hlog : Complex.log (1 - (q : ℂ)) + Complex.log (1 + (q : ℂ)) =
      Complex.log (1 - (q : ℂ) * (q : ℂ)) := by
    have he := congrArg Complex.ofReal (Real.log_mul hm.ne' hplus.ne')
    rw [Complex.ofReal_log (mul_pos hm hplus).le, Complex.ofReal_add,
      Complex.ofReal_log hm.le, Complex.ofReal_log hplus.le, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one,
      show (1 - (q : ℂ)) * (1 + (q : ℂ)) = 1 - (q : ℂ) * (q : ℂ) by ring] at he
    exact he.symm
  have ht : twist (exponentialPhaseGauge 0) p = -1 := by
    rw [← exponentialPrimePhase_eq_twist, Complex.ofReal_zero, exponentialPrimePhase_zero]
  simp only [localRem, eulerVar, powCoeff, twist_trivial, ht, mul_one, mul_neg_one,
    sub_neg_eq_add, hd, hd2]
  linear_combination -hlog

/-- Prime squares supply exactly the factor `ζ(2)` in the endpoint profile. -/
theorem exp_liouville_hullRem_pair :
    Complex.exp (hullRem 1 (twist 0) + hullRem 1 (twist (exponentialPhaseGauge 0))) =
      riemannZeta 2 := by
  have h0 := summable_localRem (s := (1 : ℂ)) (norm_twist_prime 0) (by norm_num)
  have hL := summable_localRem (s := (1 : ℂ)) (norm_twist_prime (exponentialPhaseGauge 0)) (by norm_num)
  have he : hullRem 1 (twist 0) + hullRem 1 (twist (exponentialPhaseGauge 0)) =
      canonicalEulerLogZeta 2 := by
    rw [hullRem, hullRem, ← h0.tsum_add hL,
      canonicalEulerLogZeta_eq_primeLog (s := (2 : ℂ)) (by norm_num)]
    exact tsum_congr liouville_localRem_pair
  rw [he, exp_canonicalEulerLogZeta_eq_riemannZeta (s := (2 : ℂ)) (by norm_num)]

private theorem continuous_exponentialPhase_eulerVar (p : Nat.Primes) :
    Continuous (fun q : ℝ × ℂ => eulerVar q.2 (twist (exponentialPhaseGauge q.1)) p) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpow : Continuous (fun s : ℂ => (p : ℂ) ^ (-s)) := by
    have hd : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) := fun s =>
      (differentiableAt_id.neg).const_cpow (Or.inl hp)
    exact hd.continuous
  have hphase : Continuous (fun q : ℝ × ℂ => exponentialPrimePhase p (q.1 : ℂ)) :=
    (differentiable_exponentialPrimePhase p).continuous.comp
      (Complex.continuous_ofReal.comp continuous_fst)
  have he : (fun q : ℝ × ℂ => eulerVar q.2 (twist (exponentialPhaseGauge q.1)) p) =
      fun q : ℝ × ℂ => (p : ℂ) ^ (-q.2) * exponentialPrimePhase p (q.1 : ℂ) := by
    funext q
    rw [eulerVar, powCoeff, exponentialPrimePhase_eq_twist]
  rw [he]
  exact (hpow.comp continuous_snd).mul hphase

private theorem continuousAt_exponentialPhase_localRem (p : Nat.Primes) {q : ℝ × ℂ}
    (hs : 1 / 2 < q.2.re) :
    ContinuousAt (fun v : ℝ × ℂ => localRem v.2 (twist (exponentialPhaseGauge v.1)) p) q := by
  have he := (continuous_exponentialPhase_eulerVar p).continuousAt (x := q)
  have hslit : 1 - eulerVar q.2 (twist (exponentialPhaseGauge q.1)) p ∈ Complex.slitPlane :=
    one_sub_mem_slitPlane ((norm_eulerVar_le (norm_twist_prime (exponentialPhaseGauge q.1)) p.2 hs).trans_lt
      (by norm_num))
  exact ((continuousAt_const.sub he).clog hslit).neg.sub he

/-- Higher prime powers remain jointly continuous for real phase parameters throughout `Re s>1/2`. -/
theorem continuousAt_exponentialPhase_hullRem (t : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ContinuousAt (fun q : ℝ × ℂ => hullRem q.2 (twist (exponentialPhaseGauge q.1))) (t, s) := by
  let c := (1 / 2 + s.re) / 2
  have hc : 1 / 2 < c := by dsimp [c]; linarith only [hs]
  have hcs : c < s.re := by dsimp [c]; linarith only [hs]
  let S : Set (ℝ × ℂ) := {q | c < q.2.re}
  have ho : IsOpen S := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)
  have hb := (summable_primes_rpow (show -(2 * c) < -1 by linarith only [hc])).mul_left 2
  have hcont : ContinuousOn
      (fun q : ℝ × ℂ => ∑' p : Nat.Primes, localRem q.2 (twist (exponentialPhaseGauge q.1)) p) S := by
    refine continuousOn_tsum (fun p q hq => ?_) hb (fun p q hq => ?_)
    · exact (continuousAt_exponentialPhase_localRem p (hc.trans hq)).continuousWithinAt
    · apply (norm_localRem_le (norm_twist_prime (exponentialPhaseGauge q.1)) p.2 (hc.trans hq)).trans
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
      have hqc : c < q.2.re := hq
      linarith only [hqc]
  exact hcont.continuousAt (ho.mem_nhds hcs)

/-- The quadratic scale with the divergent prime logarithm removed. -/
def normalizedExponentialPhaseProfile (t : ℝ) (w : ℂ) : ℂ :=
  zetaResidueFactor (1 + (t : ℂ) * w) * Complex.exp
    (-quadraticResidueScalingLog w + scaledPrimeLogRemainder t w +
      hullRem (1 + (t : ℂ) * w) (twist (exponentialPhaseGauge t)) -
        hullRem (1 + (t : ℂ) * w) (twist 0))

theorem normalizedExponentialPhaseProfile_zero (w : ℂ) :
    normalizedExponentialPhaseProfile 0 w = quadraticResidueScalingProfile w := by
  rw [normalizedExponentialPhaseProfile, Complex.ofReal_zero, zero_mul, add_zero,
    zetaResidueFactor_one, one_mul, scaledPrimeLogRemainder_zero]
  rw [show -quadraticResidueScalingLog w + 2 * hullRem 1 (twist 0) +
      hullRem 1 (twist (exponentialPhaseGauge 0)) - hullRem 1 (twist 0) =
      (hullRem 1 (twist 0) + hullRem 1 (twist (exponentialPhaseGauge 0))) +
        -quadraticResidueScalingLog w by ring,
    Complex.exp_add, exp_liouville_hullRem_pair, quadraticResidueScalingProfile]

/-- A compact spectral set has a common real parameter interval of continuous normalized values. -/
theorem exists_continuousOn_normalizedExponentialPhaseProfile {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -1 < w.re}) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      (∀ t ∈ Icc 0 a, ∀ w ∈ K, 1 / 2 < (1 + (t : ℂ) * w).re) ∧
      ContinuousOn (fun q : ℝ × ℂ => normalizedExponentialPhaseProfile q.1 q.2) (Icc 0 a ×ˢ K) := by
  by_cases hK0 : K = ∅
  · subst K
    refine ⟨1, zero_lt_one, le_rfl, ?_, ?_⟩
    · intro t ht w hw
      exact False.elim hw
    · simp
  have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK0
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn (f := fun w : ℂ => ‖w‖) hne continuous_norm.continuousOn
  have hbBound : ∀ w ∈ K, ‖w‖ ≤ ‖b‖ := hmax
  let B := max 1 ‖b‖
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ B := (hbBound w hw).trans (le_max_right _ _)
  let a := 1 / (4 * (B + 1))
  have hden : 0 < 4 * (B + 1) := by linarith only [hB]
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hden).mpr
    linarith only [hB]
  have hclear : a * (4 * (B + 1)) = 1 := by
    dsimp [a]
    exact div_mul_cancel₀ 1 hden.ne'
  have haB : a * B < 1 / 2 := by nlinarith only [hclear, ha]
  have hspectral (t : ℝ) (ht : t ∈ Icc 0 a) (w : ℂ) (hw : w ∈ K) :
      1 / 2 < (1 + (t : ℂ) * w).re := by
    have hn : ‖(t : ℂ) * w‖ < 1 / 2 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ((mul_le_mul_of_nonneg_left (hBw w hw) ht.1).trans
        (mul_le_mul_of_nonneg_right ht.2 hB0)).trans_lt haB
    have hre := Complex.re_le_norm (-((t : ℂ) * w))
    rw [Complex.neg_re, norm_neg] at hre
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hre, hn]
  have hscaled : ContinuousOn (fun q : ℝ × ℂ => scaledPrimeLogRemainder q.1 q.2) (Icc 0 a ×ˢ K) :=
    (continuousOn_scaledPrimeLogRemainder hK hhalf).mono
      (fun q hq => ⟨⟨hq.1.1, hq.1.2.trans ha1⟩, hq.2⟩)
  refine ⟨a, ha, ha1, hspectral, ?_⟩
  intro q hq
  have hs := hspectral q.1 hq.1 q.2 hq.2
  have hm : ContinuousAt (fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) q := by fun_prop
  have hp : ContinuousAt (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) q := by fun_prop
  have hZ := differentiable_zetaResidueFactor.continuous.continuousAt.comp
    (g := zetaResidueFactor) (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) hm
  have hL := (analyticOnNhd_quadraticResidueScalingLog q.2 (hhalf hq.2)).continuousAt.comp
    (g := quadraticResidueScalingLog) (f := fun v : ℝ × ℂ => v.2) continuous_snd.continuousAt
  have hH := (continuousAt_exponentialPhase_hullRem q.1 hs).comp
    (g := fun v : ℝ × ℂ => hullRem v.2 (twist (exponentialPhaseGauge v.1)))
    (f := fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) hp
  have h0 := (analyticOnNhd_hullRem (norm_twist_prime 0) _ hs).continuousAt.comp
    (g := fun s : ℂ => hullRem s (twist 0)) (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) hm
  exact hZ.continuousWithinAt.mul
    (((hL.continuousWithinAt.neg.add (hscaled q hq)).add hH.continuousWithinAt).sub
      h0.continuousWithinAt).cexp

/-- The continuously renormalized profile tends uniformly to its exact endpoint value. -/
theorem tendstoUniformlyOn_normalizedExponentialPhaseProfile {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -1 < w.re}) :
    TendstoUniformlyOn normalizedExponentialPhaseProfile quadraticResidueScalingProfile
      (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨a, ha, _, _, hc⟩ := exists_continuousOn_normalizedExponentialPhaseProfile hK hhalf
  have hu : TendstoUniformlyOn normalizedExponentialPhaseProfile (normalizedExponentialPhaseProfile 0)
      (𝓝[Icc (0 : ℝ) a] 0) K :=
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn
      ⟨le_rfl, ha.le⟩
  have hu' : TendstoUniformlyOn normalizedExponentialPhaseProfile (normalizedExponentialPhaseProfile 0)
      (𝓝[>] (0 : ℝ)) K := fun V hV =>
    Filter.Eventually.filter_mono (nhdsGT_zero_le_Icc ha) (hu V hV)
  have hzero : normalizedExponentialPhaseProfile 0 = quadraticResidueScalingProfile :=
    funext normalizedExponentialPhaseProfile_zero
  rwa [hzero] at hu'


private theorem summable_scaledPrimeLogRemainder {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -1 < w.re) :
    Summable (fun n : ℕ => exponentialPhaseCoefficient n *
      regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ)))) := by
  let η := min (w.re + 1) 1
  let M := max 1 ‖w‖
  have hη : 0 < η := lt_min (by linarith only [hw]) zero_lt_one
  obtain ⟨C, _, hb⟩ := regularizedPrimeLog_scaled_bound (η := η) (M := M) hη (min_le_right _ _) (le_max_left _ _)
  apply Summable.of_norm_bounded (summable_exponentialPhaseCoefficient_weight C)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hb t ht ht1 w (min_le_left _ _) (le_max_right _ _) n) (norm_nonneg _)

private theorem scaling_prime_halfplane {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : -1 < w.re) :
    1 < (1 + (t : ℂ) * w).re + t := by
  have hp : 0 < t * (w.re + 1) := mul_pos ht (by linarith only [hw])
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith only [hp]

/-- Exact cancellation of the shifted prime logarithmic divergence. -/
theorem deformationPrimeSum_exponentialPhase_scaled {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -1 < w.re) :
    deformationPrimeSum (exponentialPhaseGauge t) (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) - quadraticResidueScalingLog w + scaledPrimeLogRemainder t w := by
  have hE := summable_scaledPrimeLogRemainder ht.le ht1 hw
  have hL : Summable (fun n : ℕ => exponentialPhaseCoefficient n *
      Complex.log (w + ((n + 1 : ℕ) : ℂ))) := by
    simpa only [Nat.add_zero] using summable_factorialLogTail 0 (w := w)
      (by simpa only [Nat.cast_zero, zero_add] using hw)
  have hconst := summable_exponentialPhaseCoefficient.mul_right (Real.log t : ℂ)
  rw [deformationPrimeSum_exponentialPhase_shifted ht.le (scaling_prime_halfplane ht hw)]
  calc
    _ = ∑' n : ℕ, ((exponentialPhaseCoefficient n *
        regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ))) -
          exponentialPhaseCoefficient n * Complex.log (w + ((n + 1 : ℕ) : ℂ))) -
            exponentialPhaseCoefficient n * (Real.log t : ℂ)) := by
      apply tsum_congr
      intro n
      have hRe : 0 < (w + ((n + 1 : ℕ) : ℂ)).re := by
        simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [hw, hn]
      have hne : w + ((n + 1 : ℕ) : ℂ) ≠ 0 := by
        intro hz
        rw [hz, Complex.zero_re] at hRe
        exact lt_irrefl 0 hRe
      have hz : 1 < (1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ))).re := by
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.natCast_re, Nat.cast_add, Nat.cast_one] at hRe ⊢
        nlinarith only [mul_pos ht hRe]
      have he := regularizedPrimeLog_of_re_gt_one hz
      rw [add_sub_cancel_left, Complex.log_ofReal_mul ht hne] at he
      rw [show 1 + (t : ℂ) * w + ((n + 1 : ℕ) : ℂ) * (t : ℂ) =
        1 + (t : ℂ) * (w + ((n + 1 : ℕ) : ℂ)) by ring]
      linear_combination -(exponentialPhaseCoefficient n) * he
    _ = scaledPrimeLogRemainder t w - quadraticResidueScalingLog w -
        (∑' n : ℕ, exponentialPhaseCoefficient n) * (Real.log t : ℂ) := by
      rw [(hE.sub hL).tsum_sub hconst, hE.tsum_sub hL, tsum_mul_right]
      rfl
    _ = _ := by rw [tsum_exponentialPhaseCoefficient]; ring

/-- The continuous profile is exactly the actual pole regularization divided by `t²`. -/
theorem jointGaugeRegularization_exponentialPhase_normalized {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -1 < w.re) (hh : 1 / 2 < (1 + (t : ℂ) * w).re) :
    jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2 =
      normalizedExponentialPhaseProfile t w := by
  have he : deformationExponent (exponentialPhaseGauge t) (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) + (-quadraticResidueScalingLog w + scaledPrimeLogRemainder t w +
        hullRem (1 + (t : ℂ) * w) (twist (exponentialPhaseGauge t)) -
          hullRem (1 + (t : ℂ) * w) (twist 0)) := by
    rw [deformationExponent, deformationPrimeSum_exponentialPhase_scaled ht ht1 hw]
    ring
  have hexp : Complex.exp (2 * (Real.log t : ℂ)) = (t : ℂ) ^ 2 := by
    simp only [two_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht, pow_two]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [jointGaugeRegularization, jointExponent_exponentialPhase_eq (scaling_prime_halfplane ht hw) hh,
    he, Complex.exp_add, hexp, normalizedExponentialPhaseProfile]
  field_simp [htC]

/-- The actual pole regularization has the exact nonpolynomial quadratic scaling limit. -/
theorem tendstoLocallyUniformlyOn_exponentialPhase_quadratic :
    TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ =>
        jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
      quadraticResidueScalingProfile (𝓝[>] (0 : ℝ)) {w : ℂ | -1 < w.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro K hhalf hK
  have hu := tendstoUniformlyOn_normalizedExponentialPhaseProfile hK hhalf
  obtain ⟨a, ha, ha1, hspectral, _⟩ := exists_continuousOn_normalizedExponentialPhaseProfile hK hhalf
  intro V hV
  filter_upwards [hu V hV, self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ha)] with t hlim ht hta
  change 0 < t at ht
  intro w hw
  rw [jointGaugeRegularization_exponentialPhase_normalized ht (hta.le.trans ha1) (hhalf hw)
    (hspectral t ⟨ht.le, hta.le⟩ w hw)]
  exact hlim w hw

/-- The nonzero pole residue vanishes with exact quadratic order. -/
theorem tendsto_exponentialPhase_residue_quadratic :
    Tendsto (fun t : ℝ => jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (quadraticResidueScalingProfile 0)) := by
  have hsub : ({0} : Set ℂ) ⊆ {w | -1 < w.re} := by
    intro w hw
    have hw0 : w = 0 := Set.mem_singleton_iff.mp hw
    rw [hw0]
    norm_num
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mp
      tendstoLocallyUniformlyOn_exponentialPhase_quadratic ({0} : Set ℂ) hsub isCompact_singleton
  have hzero := tendstoUniformlyOn_singleton_iff_tendsto.mp hu
  simpa only [mul_zero, add_zero] using hzero

theorem exponentialPhase_quadratic_residue_coefficient_ne_zero : quadraticResidueScalingProfile 0 ≠ 0 :=
  quadraticResidueScalingProfile_ne_zero 0

theorem tendsto_exponentialPhase_residue_zero :
    Tendsto (fun t : ℝ => jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hbase : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hh := hbase.pow 2
    simpa only [Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hh
  have hp : Tendsto (fun t : ℝ =>
      (jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1) / (t : ℂ) ^ 2) * (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_exponentialPhase_residue_quadratic.mul ht
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)))

#print axioms tsum_exponentialPhaseCoefficient
#print axioms analyticOnNhd_quadraticResidueScalingProfile
#print axioms quadraticResidueScalingProfile_not_polynomial
#print axioms regularizedPrimeLog_scaled_bound
#print axioms deformationPrimeSum_exponentialPhase_shifted
#print axioms tendstoUniformlyOn_scaledPrimeLogRemainder
#print axioms exp_liouville_hullRem_pair
#print axioms tendstoUniformlyOn_normalizedExponentialPhaseProfile
#print axioms tendstoLocallyUniformlyOn_exponentialPhase_quadratic
#print axioms tendsto_exponentialPhase_residue_quadratic
#print axioms exponentialPhase_quadratic_residue_coefficient_ne_zero
#print axioms tendsto_exponentialPhase_residue_zero

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
