import GaloisForLFunctions.ArithmeticCriticalityTheory.ThetaConvolutionGauges
import GaloisForLFunctions.ArithmeticCriticalityTheory.SignedSuperpositionInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateReflectedCollarDefect

/-!
# Odd theta convolutions fail at infinity: no folded supersolution outside the span

Let `φ ∈ C²_c(ℝ)` be odd, `M = Φ ∗ φ` its theta convolution and `ω_φ = M/Φ` the convolution gauge.
`M` is odd; on the cone `M ≥ 0` on `(0, ∞)` the folded generator differs from the two-sided one by the
reflected collar, so, with `A_φ = 0` by oddness,

    𝓛_N ω_φ − Φ cosh(x/2) ω_φ = Φ(x) [ B_φ sinh(x/2) − 2 C_φ(x) ],
    C_φ(x) = ∫ ω(t) M(t − x)⁺ dt + Σ Λ(n) n^{−1/2} M(log n − x)⁺,

`B_φ = ∫ φ(b) sinh(b/2) db` (`foldedDefect_convGauge`). The collar dominates the signed prime sum
`Σ Λ(n) n^{−1/2} M(log n − x)`, and the superposition `M = ∫ φ(b) Φ(· − b) db` turns that sum into
`∫ φ(b) P(x + b) db` with `P(y) = Σ Λ(n) n^{−1/2} Φ(y − log n)`, which the theta harmonic identity
evaluates as `cosh(y/2)` up to the universal constant `K`. Hence for `x` beyond the support of `φ`

    C_φ(x) ≥ B_φ sinh(x/2) − K ∫|φ|,      𝓛_N ω_φ − Φ cosh(x/2) ω_φ ≤ −Φ(x) [ B_φ sinh(x/2) − 2K ∫|φ| ].

The decisive coefficient is again the pole moment, `B_φ = 2 ∫ M(x) sinh(x/2) dx > 0` on the nonzero
cone. No prime number theorem enters: the convolution class is exactly the class on which the prime
sum is a superposition of the harmonic identity. This makes exact, on the continuous span of the
translates, the asymptotics of the reflected prime mass of a general odd profile: twice the source,
up to a bounded error.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.ThetaSourceWard

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The folded generator on the odd nonnegative cone -/

/-- For `ω` odd and nonnegative on `(0, ∞)`, the folded shift generator is the two-sided one minus
the reflected collar, at every point and every shift. -/
theorem foldedShiftGenerator_eq_twoSided_sub_reflectedCollar {ω : ℝ → ℝ}
    (hodd : ∀ x, ω (-x) = -ω x) (hnn : ∀ y, 0 < y → 0 ≤ ω y) (t x : ℝ) :
    foldedShiftGenerator ω t x = twoSidedShiftGenerator ω t x - reflectedCollarShift ω t x := by
  unfold foldedShiftGenerator twoSidedShiftGenerator reflectedCollarShift
  by_cases ht : t ≤ x
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - t)]
    have h0 : max (ω (t - x)) 0 = 0 := by
      rcases eq_or_lt_of_le ht with h | h
      · have hz : ω 0 = 0 := by linarith [hodd 0, neg_zero (G := ℝ) ▸ hodd 0]
        rw [h, sub_self, hz, max_self]
      · rw [show t - x = -(x - t) by ring, hodd]
        exact max_eq_right (by linarith [hnn (x - t) (by linarith)])
    rw [h0]
    ring
  · replace ht := not_le.mp ht
    rw [abs_of_neg (by linarith : x - t < 0), max_eq_left (hnn (t - x) (by linarith)),
      show -(x - t) = t - x by ring, show x - t = -(t - x) by ring, hodd, riemannKernelReal_neg']
    ring

/-! ### Oddness of the convolution gauge -/

/-- The cosh coefficient of an odd `φ` vanishes. -/
theorem convCoshCoefficient_eq_zero_of_odd {φ : ℝ → ℝ} (hodd : ∀ b, φ (-b) = -φ b) :
    convCoshCoefficient φ = 0 := by
  have h := integral_neg_eq_self (fun b => φ b * Real.cosh (b / 2)) volume
  unfold convCoshCoefficient
  have e : (fun b => φ (-b) * Real.cosh (-b / 2)) = fun b => -(φ b * Real.cosh (b / 2)) :=
    funext fun b => by rw [hodd, neg_div, Real.cosh_neg]; ring
  simp only [e, integral_neg] at h
  linarith

theorem thetaConv_neg_of_odd {φ : ℝ → ℝ} (hodd : ∀ b, φ (-b) = -φ b) (x : ℝ) :
    thetaConv φ (-x) = -thetaConv φ x := by
  have h := integral_neg_eq_self (fun b => φ b * riemannKernelReal (-x - b)) volume
  unfold thetaConv
  rw [← h, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [hodd, show -x - -b = -(x - b) by ring, riemannKernelReal_neg']
  ring

theorem convGauge_neg_of_odd {φ : ℝ → ℝ} (hodd : ∀ b, φ (-b) = -φ b) (x : ℝ) :
    convGauge φ (-x) = -convGauge φ x := by
  unfold convGauge
  rw [thetaConv_neg_of_odd hodd, riemannKernelReal_neg', neg_div]

theorem reflectedCollarShift_convGauge (φ : ℝ → ℝ) (t x : ℝ) :
    reflectedCollarShift (convGauge φ) t x = 2 * riemannKernelReal x * max (thetaConv φ (t - x)) 0 := by
  unfold reflectedCollarShift
  rw [mul_assoc (2 * riemannKernelReal x), mul_max_of_nonneg _ _ (riemannKernelReal_pos (t - x)).le,
    mul_zero, riemannKernelReal_mul_convGauge]

/-- The reflected collar mass of the convolution gauge, in test coordinates. -/
def convCollarMass (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0) +
    ∑' n : ℕ, vonMangoldtAtom n * max (thetaConv φ (Real.log n - x)) 0

/-! ### The prime sum of a theta convolution -/

theorem atom_mul_riemannKernelReal_add_sub_le {R x b : ℝ} (hb : |b| ≤ R) (n : ℕ) :
    vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n) ≤
      2 * (riemannKernelReal 0 / riemannKernelReal (|x| + R)) *
        (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) := by
  have hxb : |x + b| ≤ |x| + R := (abs_add_le x b).trans (by linarith)
  have h := riemannKernelReal_add_add_sub_le hxb n
  have hp := riemannKernelReal_pos (x + b + Real.log n)
  have hk : riemannKernelReal (x + b - Real.log n) ≤
      2 * (riemannKernelReal 0 / riemannKernelReal (|x| + R)) *
        riemannKernelReal (|x| + R - Real.log n) := by linarith
  have := mul_le_mul_of_nonneg_left hk (vonMangoldtAtom_nonneg n)
  linarith

/-- The harmonic identity on the half line: `|P(y) − cosh(y/2)| ≤ K` for `y ≥ 0`, with
`P(y) = Σ Λ(n) n^{−1/2} Φ(y − log n)`. -/
theorem abs_leftPrimeShift_sub_cosh_le {y : ℝ} (hy : 0 ≤ y) :
    |leftPrimeShift y - Real.cosh (y / 2)| ≤ collarExcessConstant := by
  have hP : leftPrimeShift y = primeKernelSum y - rightPrimeShift y := by
    rw [primeKernelSum_eq_add]
    ring
  rw [hP, theta_harmonic_identity]
  have hQ1 := rightPrimeShift_le_zero_point hy
  have hQ2 := rightPrimeShift_nonneg y
  have hA := abs_le.mp (abs_integral_symArchTerm_le y)
  have hA0 := abs_integral_symArchTerm_le 0
  have hm : 0 ≤ gammaSourceBoundMass := by
    linarith [abs_nonneg (∫ u in Ioi (0 : ℝ), symArchTerm 0 u)]
  have hc : |2 * archConstantReal * riemannKernelReal y| ≤
      2 * |archConstantReal| * riemannKernelReal 0 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_pos (riemannKernelReal_pos y)]
    exact mul_le_mul_of_nonneg_left (riemannKernelReal_le_zero_point y) (by positivity)
  have hc' := abs_le.mp hc
  unfold collarExcessConstant
  rw [abs_le]
  constructor <;> linarith [hA.1, hA.2, hc'.1, hc'.2]

theorem atom_thetaConv_log_sub_eq (φ : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    vonMangoldtAtom n * thetaConv φ (Real.log n - x) =
      ∫ b, vonMangoldtAtom n * (φ b * riemannKernelReal (x + b - Real.log n)) := by
  unfold thetaConv
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [show Real.log n - x - b = -(x + b - Real.log n) by ring, riemannKernelReal_neg']

section OddCone

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
include hφ hφc

theorem exists_abs_thetaConv_le_exp_eight :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |thetaConv φ y| ≤ C * Real.exp (-(8 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  refine ⟨C, hC0, fun y => ?_⟩
  rw [← riemannKernelReal_mul_convGauge]
  exact (hC y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    linarith [abs_nonneg y])) hC0)

theorem summable_atom_thetaConv_log_sub (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * thetaConv φ (Real.log n - x) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le_exp_eight hφ hφc
  refine Summable.of_norm_bounded ((summable_atom_mul_exp_neg_eight_log.mul_left
    (C * Real.exp (8 * |x|)))) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  have h1 := hC (Real.log n - x)
  have h2 := exp_neg_eight_mul_abs_sub_log_le x n
  rw [abs_sub_comm] at h1
  have h3 : |thetaConv φ (Real.log n - x)| ≤
      C * Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n)) := by
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hC0
  nlinarith [mul_le_mul_of_nonneg_left h3 (vonMangoldtAtom_nonneg n)]

theorem summable_atom_max_thetaConv_log_sub (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * max (thetaConv φ (Real.log n - x)) 0 := by
  refine (summable_atom_thetaConv_log_sub hφ hφc x).norm.of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (le_max_right _ _)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (vonMangoldtAtom_nonneg n)

/-- The collar dominates the signed prime sum: `Σ Λ(n) n^{−1/2} M(log n − x) ≤ C_φ(x)`. -/
theorem tsum_atom_thetaConv_log_sub_le_convCollarMass (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * thetaConv φ (Real.log n - x)) ≤ convCollarMass φ x := by
  unfold convCollarMass
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0 :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _)
  have h2 := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (le_max_left _ _) (vonMangoldtAtom_nonneg n))
    (summable_atom_thetaConv_log_sub hφ hφc x) (summable_atom_max_thetaConv_log_sub hφ hφc x)
  linarith

/-- **The prime sum of a theta convolution is a superposition of harmonic sums.**
`Σ Λ(n) n^{−1/2} M(log n − x) = ∫ φ(b) P(x + b) db`. -/
theorem tsum_atom_thetaConv_log_sub_eq (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * thetaConv φ (Real.log n - x)) =
      ∫ b, φ b * leftPrimeShift (x + b) := by
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (riemannKernelReal 0 / riemannKernelReal (|x| + R)) := ⟨_, rfl⟩
  set F : ℕ → ℝ → ℝ := fun n b =>
    vonMangoldtAtom n * (φ b * riemannKernelReal (x + b - Real.log n)) with hF_def
  have hFint : ∀ n, Integrable (F n) := fun n =>
    (continuous_const.mul (hφ.continuous.mul (continuous_riemannKernelReal.comp
      ((continuous_const.add continuous_id).sub continuous_const)))).integrable_of_hasCompactSupport
      (hφc.mul_right.mul_left)
  have hbound : ∀ n b, |F n b| ≤
      K * (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) * |φ b| := fun n b => by
    by_cases hb : |b| ≤ R
    · have h := atom_mul_riemannKernelReal_add_sub_le (x := x) hb n
      rw [← hK] at h
      simp only [hF_def]
      rw [show vonMangoldtAtom n * (φ b * riemannKernelReal (x + b - Real.log n)) =
        φ b * (vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n)) by ring, abs_mul,
        abs_of_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le)]
      nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (φ b))]
    · simp only [hF_def]
      rw [hsupp b (not_le.mp hb)]
      simp
  have hsum : Summable fun n => ∫ b, ‖F n b‖ := by
    have hmaj : Summable fun n : ℕ =>
        K * (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) * ∫ b, |φ b| :=
      ((summable_atom_mul_kernel_sub (|x| + R)).mul_left K).mul_right _
    refine hmaj.of_nonneg_of_le (fun n => integral_nonneg fun b => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    exact integral_mono (hFint n).norm (hφi.const_mul _) fun b => by
      simpa [Real.norm_eq_abs] using hbound n b
  have h1 : (∑' n : ℕ, vonMangoldtAtom n * thetaConv φ (Real.log n - x)) = ∑' n, ∫ b, F n b :=
    tsum_congr fun n => atom_thetaConv_log_sub_eq φ x n
  rw [h1, integral_tsum_of_summable_integral_norm hFint hsum]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [hF_def]
  unfold leftPrimeShift
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem integrable_mul_leftPrimeShift_add (x : ℝ) :
    Integrable fun b => φ b * leftPrimeShift (x + b) := by
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (riemannKernelReal 0 / riemannKernelReal (|x| + R)) := ⟨_, rfl⟩
  set S := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)
  have hterm : ∀ n b, |φ b * (vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n))| ≤
      K * (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) * |φ b| := fun n b => by
    by_cases hb : |b| ≤ R
    · have h := atom_mul_riemannKernelReal_add_sub_le (x := x) hb n
      rw [← hK] at h
      rw [abs_mul, abs_of_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le)]
      nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (φ b))]
    · rw [hsupp b (not_le.mp hb)]
      simp
  have hmeas : AEStronglyMeasurable (fun b => φ b * leftPrimeShift (x + b)) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun N b => φ b *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n))
      atTop (fun N => ?_) (Eventually.of_forall fun b => ?_)
    · exact (hφ.continuous.mul (continuous_finsetSum _ fun n _ => continuous_const.mul
        (continuous_riemannKernelReal.comp ((continuous_const.add continuous_id).sub
          continuous_const)))).aestronglyMeasurable
    · exact ((summable_primeShift_left (x + b)).hasSum.tendsto_sum_nat).const_mul _
  refine (hφi.const_mul (K * S)).mono' hmeas (Eventually.of_forall fun b => ?_)
  rw [Real.norm_eq_abs]
  unfold leftPrimeShift
  rw [← tsum_mul_left]
  have hB : Summable fun n : ℕ =>
      K * (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) * |φ b| :=
    ((summable_atom_mul_kernel_sub (|x| + R)).mul_left K).mul_right _
  have hnorm : Summable fun n : ℕ =>
      ‖φ b * (vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n))‖ :=
    hB.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by rw [Real.norm_eq_abs]; exact hterm n b
  calc |∑' n : ℕ, φ b * (vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n))|
      ≤ ∑' n : ℕ, ‖φ b * (vonMangoldtAtom n * riemannKernelReal (x + b - Real.log n))‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, K * (vonMangoldtAtom n * riemannKernelReal (|x| + R - Real.log n)) * |φ b| :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hterm n b) hnorm hB
    _ = K * S * |φ b| := by rw [tsum_mul_right, tsum_mul_left]

/-- **Two-sided evaluation of the prime sum.** Beyond the support radius `R` of `φ`,
`Σ Λ(n) n^{−1/2} M(log n − x) ≥ A_φ cosh(x/2) + B_φ sinh(x/2) − K ∫|φ|`. -/
theorem exists_tsum_atom_thetaConv_log_sub_ge :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R ≤ x →
      convCoshCoefficient φ * Real.cosh (x / 2) + convSinhCoefficient φ * Real.sinh (x / 2) -
          collarExcessConstant * ∫ b, |φ b| ≤
        ∑' n : ℕ, vonMangoldtAtom n * thetaConv φ (Real.log n - x) := by
  obtain ⟨R, hR0, hsupp⟩ := exists_support_radius hφc
  refine ⟨R, by linarith, fun x hx => ?_⟩
  rw [tsum_atom_thetaConv_log_sub_eq hφ hφc x]
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  have hc : Integrable fun b => φ b * Real.cosh ((x + b) / 2) :=
    (hφ.continuous.mul (Real.continuous_cosh.comp ((continuous_const.add continuous_id).div_const
      2))).integrable_of_hasCompactSupport hφc.mul_right
  have hcb : Integrable fun b => φ b * Real.cosh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hsb : Integrable fun b => φ b * Real.sinh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hcosh : (∫ b, φ b * Real.cosh ((x + b) / 2)) =
      convCoshCoefficient φ * Real.cosh (x / 2) + convSinhCoefficient φ * Real.sinh (x / 2) := by
    have e : (fun b => φ b * Real.cosh ((x + b) / 2)) = fun b =>
        Real.cosh (x / 2) * (φ b * Real.cosh (b / 2)) + Real.sinh (x / 2) * (φ b * Real.sinh (b / 2)) :=
      funext fun b => by rw [show (x + b) / 2 = x / 2 + b / 2 by ring, Real.cosh_add]; ring
    rw [e, integral_add (hcb.const_mul _) (hsb.const_mul _), integral_const_mul, integral_const_mul]
    unfold convCoshCoefficient convSinhCoefficient
    ring
  have hle : ∀ b, φ b * Real.cosh ((x + b) / 2) - collarExcessConstant * |φ b| ≤
      φ b * leftPrimeShift (x + b) := fun b => by
    by_cases hb : |b| ≤ R
    · have hy : 0 ≤ x + b := by linarith [neg_abs_le b]
      have h2 : |φ b * (leftPrimeShift (x + b) - Real.cosh ((x + b) / 2))| ≤
          |φ b| * collarExcessConstant := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_leftPrimeShift_sub_cosh_le hy) (abs_nonneg _)
      have := (abs_le.mp h2).1
      nlinarith
    · rw [hsupp b (not_le.mp hb)]
      simp
  calc convCoshCoefficient φ * Real.cosh (x / 2) + convSinhCoefficient φ * Real.sinh (x / 2) -
        collarExcessConstant * ∫ b, |φ b|
      = ∫ b, (φ b * Real.cosh ((x + b) / 2) - collarExcessConstant * |φ b|) := by
        rw [integral_sub hc (hφi.const_mul _), integral_const_mul, hcosh]
    _ ≤ ∫ b, φ b * leftPrimeShift (x + b) :=
        integral_mono (hc.sub (hφi.const_mul _)) (integrable_mul_leftPrimeShift_add hφ hφc x) hle

/-- Fubini against the theta convolution: `∫ (Φ ∗ φ) h = ∫ φ(b) ∫ Φ(x − b) h(x) dx db` for continuous
`h` of growth at most `e^{8|x|}`. -/
theorem integral_thetaConv_mul_eq {h : ℝ → ℝ} {H : ℝ} (hhc : Continuous h) (hH0 : 0 ≤ H)
    (hhb : ∀ x, |h x| ≤ H * Real.exp (8 * |x|)) :
    (∫ x, thetaConv φ x * h x) = ∫ b, φ b * ∫ x, riemannKernelReal (x - b) * h x := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  have hprod : Integrable (Function.uncurry fun x b => φ b * (riemannKernelReal (x - b) * h x))
      (volume.prod volume) := by
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (C₀ * Real.exp (24 * R) * H * Real.exp (-(8 * |p.1|))) * |φ p.2|) (volume.prod volume) :=
      (integrable_exp_neg_eight_mul_abs.const_mul (C₀ * Real.exp (24 * R) * H)).mul_prod hφi
    refine hmaj.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hφ.continuous.comp continuous_snd).mul
        ((continuous_riemannKernelReal.comp (continuous_fst.sub continuous_snd)).mul
          (hhc.comp continuous_fst))).aestronglyMeasurable
    · show ‖φ p.2 * (riemannKernelReal (p.1 - p.2) * h p.1)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
      by_cases hb : |p.2| ≤ R
      · have h2 := exp_neg_mul_abs_sub_le 24 p.1 p.2 (by norm_num)
        have h3 : Real.exp (24 * |p.2|) ≤ Real.exp (24 * R) := Real.exp_le_exp.mpr (by linarith)
        have hk : riemannKernelReal (p.1 - p.2) ≤
            C₀ * Real.exp (24 * R) * Real.exp (-(24 * |p.1|)) := by
          refine (hC (p.1 - p.2)).trans ?_
          calc C₀ * Real.exp (-(24 * |p.1 - p.2|))
              ≤ C₀ * (Real.exp (24 * |p.2|) * Real.exp (-(24 * |p.1|))) :=
                mul_le_mul_of_nonneg_left h2 hC₀
            _ ≤ C₀ * (Real.exp (24 * R) * Real.exp (-(24 * |p.1|))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) hC₀
            _ = _ := by ring
        have he : Real.exp (-(24 * |p.1|)) * Real.exp (8 * |p.1|) ≤ Real.exp (-(8 * |p.1|)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith [abs_nonneg p.1])
        have hkh : riemannKernelReal (p.1 - p.2) * |h p.1| ≤
            C₀ * Real.exp (24 * R) * H * Real.exp (-(8 * |p.1|)) :=
          calc riemannKernelReal (p.1 - p.2) * |h p.1|
              ≤ (C₀ * Real.exp (24 * R) * Real.exp (-(24 * |p.1|))) * (H * Real.exp (8 * |p.1|)) :=
                mul_le_mul hk (hhb p.1) (abs_nonneg _) (by positivity)
            _ = C₀ * Real.exp (24 * R) * H * (Real.exp (-(24 * |p.1|)) * Real.exp (8 * |p.1|)) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hkh (abs_nonneg (φ p.2))]
      · rw [hsupp p.2 (not_le.mp hb)]
        simp
  have hconv : (fun x => thetaConv φ x * h x) =
      fun x => ∫ b, φ b * (riemannKernelReal (x - b) * h x) := funext fun x => by
    unfold thetaConv
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => by ring)
  rw [hconv, integral_integral_swap hprod]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  exact integral_const_mul _ _

/-- The pole moment of the theta convolution: `∫ (Φ ∗ φ)(x) sinh(x/2) dx = B_φ/2`. -/
theorem integral_thetaConv_mul_sinh_half :
    (∫ x, thetaConv φ x * Real.sinh (x / 2)) = convSinhCoefficient φ / 2 := by
  rw [integral_thetaConv_mul_eq hφ hφc (h := fun x => Real.sinh (x / 2))
    (Real.continuous_sinh.comp (continuous_id.div_const 2)) zero_le_one fun x => by
      rw [one_mul]
      exact (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)]
  have e : (fun b => φ b * ∫ x, riemannKernelReal (x - b) * Real.sinh (x / 2)) =
      fun b => (1 / 2) * (φ b * Real.sinh (b / 2)) :=
    funext fun b => by rw [integral_riemannKernelReal_sub_mul_sinh_half]; ring
  rw [e, integral_const_mul]
  unfold convSinhCoefficient
  ring

variable (hodd : ∀ b, φ (-b) = -φ b) (hnn : ∀ y, 0 < y → 0 ≤ thetaConv φ y)
include hodd hnn

omit hφ hφc in
theorem max_thetaConv_sub_eq_zero {x t : ℝ} (ht : t ≤ x) : max (thetaConv φ (t - x)) 0 = 0 := by
  rcases eq_or_lt_of_le ht with h | h
  · have hz : thetaConv φ 0 = 0 := by
      have := thetaConv_neg_of_odd hodd 0
      rw [neg_zero] at this
      linarith
    rw [h, sub_self, hz, max_self]
  · rw [show t - x = -(x - t) by ring, thetaConv_neg_of_odd hodd]
    exact max_eq_right (by linarith [hnn (x - t) (by linarith)])

theorem integrableOn_archLevy_max_thetaConv {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * max (thetaConv φ (t - x)) 0) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le_exp_eight hφ hφc
  have hmaj : IntegrableOn (fun t => archLevyDensity x * C * Real.exp (-(8 * |t - x|))) (Ioi 0) :=
    ((integrable_exp_neg_eight_mul_abs.comp_sub_right x).const_mul _).integrableOn
  have hcont : Continuous fun t => thetaConv φ t :=
    (contDiff_thetaConv hφ hφc).continuous
  refine hmaj.mono' ((measurable_archLevyDensity.mul
    ((hcont.comp (continuous_id.sub continuous_const)).max continuous_const).measurable).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
  by_cases htx : t ≤ x
  · rw [max_thetaConv_sub_eq_zero hodd hnn htx, abs_zero, mul_zero]
    have := archLevyDensity_pos hx
    positivity
  · replace htx := not_le.mp htx
    have hA : archLevyDensity t ≤ archLevyDensity x :=
      strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hx) (mem_Ioi.mpr ht0) htx.le
    have hm : |max (thetaConv φ (t - x)) 0| ≤ C * Real.exp (-(8 * |t - x|)) := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact (max_le (le_abs_self _) (abs_nonneg _)).trans (hC _)
    calc archLevyDensity t * |max (thetaConv φ (t - x)) 0|
        ≤ archLevyDensity x * (C * Real.exp (-(8 * |t - x|))) :=
          mul_le_mul hA hm (abs_nonneg _) (archLevyDensity_pos hx).le
      _ = _ := by ring

/-- **The folded generator of an odd convolution gauge** on the cone `M ≥ 0`:
`𝓛_N ω_φ = 𝓛_D ω_φ − 2Φ(x) C_φ(x)` for `x > 0`. -/
theorem foldedGenerator_convGauge {x : ℝ} (hx : 0 < x) :
    foldedGenerator (convGauge φ) x =
      twoSidedGenerator (convGauge φ) x - 2 * riemannKernelReal x * convCollarMass φ x := by
  have hpt : ∀ t, foldedShiftGenerator (convGauge φ) t x = twoSidedShiftGenerator (convGauge φ) t x -
      2 * riemannKernelReal x * max (thetaConv φ (t - x)) 0 := fun t => by
    rw [foldedShiftGenerator_eq_twoSided_sub_reflectedCollar (convGauge_neg_of_odd hodd)
      (fun y hy => div_nonneg (hnn y hy) (riemannKernelReal_pos y).le),
      reflectedCollarShift_convGauge]
  have hA := integrableOn_archLevy_twoSidedShiftGenerator_convGauge hφ hφc x
  have hC := integrableOn_archLevy_max_thetaConv hφ hφc hodd hnn hx
  have hP := summable_atom_twoSidedShiftGenerator_convGauge hφ hφc x
  have hQ := summable_atom_max_thetaConv_log_sub hφ hφc x
  have e1 : (fun t => archLevyDensity t * foldedShiftGenerator (convGauge φ) t x) = fun t =>
      archLevyDensity t * twoSidedShiftGenerator (convGauge φ) t x -
        (2 * riemannKernelReal x) * (archLevyDensity t * max (thetaConv φ (t - x)) 0) :=
    funext fun t => by rw [hpt]; ring
  have e2 : (fun n : ℕ => vonMangoldtAtom n * foldedShiftGenerator (convGauge φ) (Real.log n) x) =
      fun n => vonMangoldtAtom n * twoSidedShiftGenerator (convGauge φ) (Real.log n) x -
        (2 * riemannKernelReal x) * (vonMangoldtAtom n * max (thetaConv φ (Real.log n - x)) 0) :=
    funext fun n => by rw [hpt]; ring
  unfold foldedGenerator twoSidedGenerator convCollarMass
  rw [e1, e2, integral_sub hA (hC.const_mul _), integral_const_mul, hP.tsum_sub (hQ.mul_left _),
    tsum_mul_left]
  ring

/-- **Folded defect of an odd convolution gauge.**
`𝓛_N ω_φ − Φ cosh(x/2) ω_φ = Φ(x) [B_φ sinh(x/2) − 2 C_φ(x)]` for `x > 0`. -/
theorem foldedDefect_convGauge {x : ℝ} (hx : 0 < x) :
    foldedGenerator (convGauge φ) x - riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x =
      riemannKernelReal x * (convSinhCoefficient φ * Real.sinh (x / 2) - 2 * convCollarMass φ x) := by
  rw [foldedGenerator_convGauge hφ hφc hodd hnn hx]
  have h := twoSidedGenerator_convGauge_sub_potential hφ hφc x
  rw [convSource_eq hφ hφc, convCoshCoefficient_eq_zero_of_odd hodd] at h
  linear_combination h

/-- The pole moment is positive on the nonzero cone: `M ≥ 0` on `(0, ∞)` and `M(x₀) > 0` give
`B_φ = 2 ∫ M(x) sinh(x/2) dx > 0`. -/
theorem convSinhCoefficient_pos {x₀ : ℝ} (hx₀ : 0 < x₀) (hM : 0 < thetaConv φ x₀) :
    0 < convSinhCoefficient φ := by
  set f : ℝ → ℝ := fun x => thetaConv φ x * Real.sinh (x / 2) with hf
  have hcont : Continuous f := (contDiff_thetaConv hφ hφc).continuous.mul
    (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hnn' : 0 ≤ f := fun y => by
    rcases lt_trichotomy y 0 with hy | hy | hy
    · have h1 := hnn (-y) (by linarith)
      rw [thetaConv_neg_of_odd hodd] at h1
      have h2 : Real.sinh (y / 2) < 0 := Real.sinh_neg_iff.mpr (by linarith)
      show 0 ≤ thetaConv φ y * Real.sinh (y / 2)
      nlinarith
    · show 0 ≤ thetaConv φ y * Real.sinh (y / 2)
      rw [hy, zero_div, Real.sinh_zero, mul_zero]
    · exact mul_nonneg (hnn y hy) (Real.sinh_nonneg_iff.mpr (by linarith))
  have hfi : Integrable f := by
    obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
    refine (integrable_exp_neg_eight_mul_abs.const_mul C).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    show ‖thetaConv φ x * Real.sinh (x / 2)‖ ≤ C * Real.exp (-(8 * |x|))
    rw [Real.norm_eq_abs, abs_mul, ← riemannKernelReal_mul_convGauge]
    have hs : |Real.sinh (x / 2)| ≤ Real.exp (8 * |x|) :=
      (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
    have he : Real.exp (-(24 * |x|)) * Real.exp (8 * |x|) ≤ Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
    calc |riemannKernelReal x * convGauge φ x| * |Real.sinh (x / 2)|
        ≤ (C * Real.exp (-(24 * |x|))) * Real.exp (8 * |x|) :=
          mul_le_mul (hC x) hs (abs_nonneg _) (by positivity)
      _ = C * (Real.exp (-(24 * |x|)) * Real.exp (8 * |x|)) := by ring
      _ ≤ C * Real.exp (-(8 * |x|)) := mul_le_mul_of_nonneg_left he hC0
  have hpos : 0 < ∫ x, f x := by
    rw [integral_pos_iff_support_of_nonneg hnn' hfi]
    have hopen : IsOpen (Function.support f) := isOpen_ne_fun hcont continuous_const
    exact hopen.measure_pos volume
      ⟨x₀, (mul_pos hM (Real.sinh_pos_iff.mpr (by linarith))).ne'⟩
  have h := integral_thetaConv_mul_sinh_half hφ hφc
  rw [← hf] at h
  linarith

/-- **Quantitative infinity failure.** Beyond the support radius of `φ`, for `x > 0`,
`𝓛_N ω_φ − Φ cosh(x/2) ω_φ ≤ −Φ(x) [B_φ sinh(x/2) − 2K ∫|φ|]`. -/
theorem exists_foldedDefect_convGauge_le :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R ≤ x → 0 < x →
      foldedGenerator (convGauge φ) x - riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x ≤
        -(riemannKernelReal x * (convSinhCoefficient φ * Real.sinh (x / 2) -
          2 * collarExcessConstant * ∫ b, |φ b|)) := by
  obtain ⟨R, hR0, hge⟩ := exists_tsum_atom_thetaConv_log_sub_ge hφ hφc
  refine ⟨R, hR0, fun x hx hx0 => ?_⟩
  rw [foldedDefect_convGauge hφ hφc hodd hnn hx0]
  have h1 := hge x hx
  rw [convCoshCoefficient_eq_zero_of_odd hodd, zero_mul, zero_add] at h1
  have h2 := tsum_atom_thetaConv_log_sub_le_convCollarMass hφ hφc x
  have hΦ := riemannKernelReal_pos x
  nlinarith [mul_le_mul_of_nonneg_left (le_trans h1 h2) hΦ.le]

/-- **Odd theta convolutions fail at infinity.** If `φ ∈ C²_c` is odd, `M = Φ ∗ φ ≥ 0` on `(0, ∞)`
and `M(x₀) > 0` for some `x₀ > 0`, the convolution gauge is a strict folded subsolution on a half line
`[X, ∞)`. -/
theorem exists_infinity_window_convGauge_foldedGenerator_lt_potential {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hM : 0 < thetaConv φ x₀) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
      foldedGenerator (convGauge φ) x <
        riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x := by
  have hB := convSinhCoefficient_pos hφ hφc hodd hnn hx₀ hM
  obtain ⟨R, hR0, hd⟩ := exists_foldedDefect_convGauge_le hφ hφc hodd hnn
  set B := convSinhCoefficient φ
  set D := abs (2 * collarExcessConstant * ∫ b, |φ b|)
  refine ⟨max (R + 1) (2 * (D + 1) / B), lt_of_lt_of_le (by linarith) (le_max_left _ _),
    fun x hX => ?_⟩
  have hx1 : R + 1 ≤ x := le_trans (le_max_left _ _) hX
  have hx0 : 0 < x := by linarith
  have hx2 : 2 * (D + 1) / B ≤ x := le_trans (le_max_right _ _) hX
  have h1 : 2 * (D + 1) ≤ x * B := by rwa [div_le_iff₀ hB] at hx2
  have hsinh : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hsinh hB.le
  have hD : 2 * collarExcessConstant * ∫ b, |φ b| ≤ D := le_abs_self _
  have hgap : 0 < B * Real.sinh (x / 2) - 2 * collarExcessConstant * ∫ b, |φ b| := by nlinarith
  have hdx := hd x (by linarith) hx0
  have : 0 < riemannKernelReal x * (B * Real.sinh (x / 2) - 2 * collarExcessConstant * ∫ b, |φ b|) :=
    mul_pos (riemannKernelReal_pos x) hgap
  linarith

end OddCone

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
