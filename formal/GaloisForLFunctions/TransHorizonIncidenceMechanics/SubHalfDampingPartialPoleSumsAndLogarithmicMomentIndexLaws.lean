import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SmallDampingMoebiusAndLiouvilleCancellationLaws
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DoubleZeroKernelsAndLogarithmicSmoothPowerAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheLogarithmicEnergyOfThePartialPoleSums
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Sub-Half-Damping Partial Pole Sums, Signed Logarithmic Rate Transfer, and All-Order Pole-Vanishing Index Laws

This file resolves the sub-half-damping sign and pole-moment structure of trans-horizon receiver
mechanics across three coupled directions:

1. **The Sub-Half-Damped Partial-Pole-Sum Energy Law (`0 < ε < 1`) and Individual Kernels Beyond
   `CriticalWiener` (§1):**
   For every `0 < ε < 1`, the smooth power `q_ε(d) = d^{-ε}` has centred prefix
   `A_{q_ε}(n) = Z_ε n^{1 - ε} + R_ε(n)` where `Z_ε = Re ζ(1 - ε) / (1 - ε) < 0` (`subHalfZetaCoeff_neg`)
   and `|R_ε(n)| ≤ K_ε (√n)^{1 - ε}` (`abs_subHalfRemainder_le`).
   For any kernel `k`, the convolution `k ⋆ q_ε` has centred prefix
   `A_{k ⋆ q_ε}(n) = Z_ε n^{1 - ε} S_{k,ε}(n) + Σ_{j ≤ n} k(j) R_{ε,j}(n) + m_{q_ε} A_k(n)`,
   where `S_{k,ε}(n) = Σ_{j ≤ n} k(j) j^{-(1 - ε)}` are the partial pole sums at the pole abscissa
   `1 - ε`, and each dilated remainder `R_{ε,j}` has pronic norm `O(j^{-1/2})`
   (`pronicNorm_subHalfDilationRemainder_le`).
   Consequently, both on `CriticalWiener` (`abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le`)
   and for general individual kernels with bounded remainder/self-receiver norms
   (`abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le_of_bounds`), the receiver norm
   `√E_T(k ⋆ q_ε)` agrees up to a uniform constant with `|Z_ε| √L_{T,ε}(k)`, where
   `L_{T,ε}(k) = Σ_{n ≤ T} (n^{1 - ε} S_{k,ε}(n))² / (n(n + 1))`.
   Furthermore, via Möbius inversion `k_{s,ε}(j) = (s ⋆ μ)(j) j^{-ε}`, we construct explicit classes
   of individual kernels outside `CriticalWiener` whose convolution `k_{s,ε} ⋆ d^{-ε} = s(d) d^{-ε}`
   is `ReceiverBounded` (`receiverBounded_dirichletConv_moebiusInvertedKernel_of_bounded_partialSums`,
   `receiverBounded_dirichletConv_moebiusInvertedKernel_of_partialSum_rpow`), and prove that
   `k = μ(d) d^{-ε}` repairs `d^{-ε}` with zero receiver energy while failing both `CriticalWiener`
   and absolute summability at the pole abscissa `1 - ε` (`not_summable_abs_pmPowerDamped_abscissa`,
   `not_criticalWiener_pmPowerDamped`).

2. **Signed Logarithmic Rate Transfer and Complete Vertical-Line Boundary Energy Equivalence (§2):**
   Via the Selberg–von Mangoldt identity `-μ(n) log n = (μ ⋆ Λ)(n)` (`neg_logWeight_moebiusReal_eq_dirichletConv`),
   a linear tail bound `|Σ_{e ≤ x} s(e) log e| ≤ M_log x` for `x ≥ D ≥ 1` transfers by Abel summation
   against `1 / log e` to the undamped tail `|Σ_{D < e ≤ x} s(e)| ≤ (2 M_log / log(D + 1)) x`
   (`abs_sum_Ioc_le_of_logWeight_linear`), yielding the logarithmic hyperbola bound with explicit
   `(log(D + 1))⁻¹` gain:
   `|A_{s,ε}(n)| ≤ 6 D^{1 - ε} + (26 / (ε log(D + 1))) M_log n D^{-ε}`
   (`abs_weightCenteredPrefix_dampedSign_le_of_logWeight_linear_pos`).
   A power-saving bound `|Σ_{e ≤ N} s(e) log e| ≤ C (N + 1)^β` (`β < 1`, `β < 2ε`) at a single damping `ε`
   pays `dampedSignWeight s ε` (`receiverBounded_dampedSign_of_logWeight_partialSum_rpow`), and for
   `c ∈ DampedClass K (1 / 2)` the receiver energy is two-sidedly equivalent to the uniform vertical-line
   boundary energy `∫_ℝ |ζ(σ + it)(C(σ + it) - m)/(σ + it)|² dt` on `1/2 < σ < 3/4`
   (`lineEnergy_le_four_pi_mul_of_weightPronicEnergy_le`, `receiverBounded_iff_exists_lineEnergy_le`).

3. **All-Order Logarithmic Pole Moments, Binomial Leibniz Law, and Index Additivity (§3):**
   For `poleLogMoment k J ε m = Σ_{j ≤ J} k(j) (log j)^m j^{-(1 - ε)}`, Dirichlet convolution obeys
   the exact binomial Leibniz formula
   `poleLogMoment (k₁ ⋆ k₂) (J₁ J₂) ε m = Σ_{i ≤ m} C(m, i) poleLogMoment k₁ J₁ ε i · poleLogMoment k₂ J₂ ε (m - i)`
   (`poleLogMoment_dirichletConv`).
   Hence the order of vanishing at the pole abscissa `1 - ε` is additive under Dirichlet convolution
   (`poleLogMoment_dirichletConv_eq_zero_of_lt`, `poleLogMoment_dirichletConv_add`), and the `r`-fold
   iterated Fermi kernel `(δ_1 - 2^{1 - ε} δ_2)^{⋆ r}` has exact pole vanishing order `r` with
   non-vanishing `r`-th logarithmic moment `r! (-log 2)^r` (`poleLogMoment_iteratedFermiKernel_eq`,
   `poleLogMoment_iteratedFermiKernel_ne_zero`).
-/

open Finset Filter Topology Complex MeasureTheory
open GaloisForLFunctions.BezoutValuationIncidence
open _root_.RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Sub-Half-Damped Partial-Pole-Sum Energy Law (`0 < ε < 1`) and Individual Kernels Beyond `CriticalWiener` -/

/-- The leading pole-drift coefficient `Z_ε = Re ζ(1 - ε) / (1 - ε)` of the smooth power `d^{-ε}`
for `0 < ε < 1`. -/
def subHalfZetaCoeff (ε : ℝ) : ℝ :=
  (riemannZeta ((1 - ε : ℝ) : ℂ)).re / (1 - ε)

/-- For `0 < ε < 1`, `ζ(1 - ε) < 0` on the real critical strip, so `Z_ε < 0`. -/
theorem subHalfZetaCoeff_neg {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    subHalfZetaCoeff ε < 0 := by
  unfold subHalfZetaCoeff
  obtain ⟨x, hx, hzx⟩ :=
    RHTower.riemannZeta_real_strip_neg (σ := 1 - ε) (by linarith) (by linarith)
  have hneg : (riemannZeta ((1 - ε : ℝ) : ℂ)).re < 0 := by
    rw [hzx, Complex.ofReal_re]
    exact hx
  exact div_neg_of_neg_of_pos hneg (by linarith)

theorem subHalfZetaCoeff_ne_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    subHalfZetaCoeff ε ≠ 0 :=
  (subHalfZetaCoeff_neg hε hε1).ne

/-- At zero oscillation frequency `t = 0`, `oscillatingSmoothPower ε 0` is the smooth power
`dampedSignWeight unitSign ε`. -/
theorem oscillatingSmoothPower_zero {ε : ℝ} (hε : 0 < ε) :
    oscillatingSmoothPower ε 0 = dampedSignWeight unitSign ε := by
  funext d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [oscillatingSmoothPower, dampedSignWeight, unitSign,
      Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
  · simp [oscillatingSmoothPower, dampedSignWeight, unitSign]

theorem oscillationExponent_zero (ε : ℝ) :
    oscillationExponent ε 0 = ((1 - ε : ℝ) : ℂ) := by
  simp [oscillationExponent]

/-- The remainder `R_ε(N) = A_{q_ε}(N) - Z_ε N^{1 - ε}` of the smooth power `q_ε(d) = d^{-ε}`. -/
def subHalfRemainder (ε : ℝ) (N : ℕ) : ℝ :=
  weightCenteredPrefix (dampedSignWeight unitSign ε)
    (∑' d : ℕ, dampedSignWeight unitSign ε d / d) N -
    subHalfZetaCoeff ε * (N : ℝ) ^ (1 - ε)

theorem subHalfRemainder_zero {ε : ℝ} (hε1 : ε < 1) :
    subHalfRemainder ε 0 = 0 := by
  simp [subHalfRemainder, weightCenteredPrefix_zero,
    Real.zero_rpow (show (1 : ℝ) - ε ≠ 0 by linarith)]

/-- **The sub-half-damped smooth power prefix asymptotic.** For `0 < ε < 1` and every `n : ℕ`,
`|A_{q_ε}(n) - Z_ε n^{1 - ε}| ≤ K_ε (√n)^{1 - ε}`, where `K_ε = floorSumRate (1 - ε)`. -/
theorem abs_subHalfRemainder_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    |subHalfRemainder ε n| ≤
      floorSumRate ((1 - ε : ℝ) : ℂ) * Real.sqrt n ^ (1 - ε) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [subHalfRemainder_zero hε1]
    simp [Real.zero_rpow (show (1 : ℝ) - ε ≠ 0 by linarith)]
  have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 0 hn
  rw [oscillatingSmoothPower_zero hε, oscillationExponent_zero] at h
  have hpow : (((n : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ)) = (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  have hterm : (riemannZeta ((1 - ε : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((1 - ε : ℝ) : ℂ) /
      ((1 - ε : ℝ) : ℂ)).re = subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) := by
    rw [hpow, mul_div_right_comm, Complex.re_mul_ofReal, Complex.div_ofReal_re, subHalfZetaCoeff]
  rwa [hterm] at h

/-- The partial pole sums `S_{k,ε}(n) = Σ_{j ≤ n} k(j) j^{-(1 - ε)}` at the pole abscissa `1 - ε`. -/
def subHalfPartialPoleSum (ε : ℝ) (k : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, k j * (j : ℝ) ^ (-(1 - ε))

theorem subHalfPartialPoleSum_eq_poleValue (ε : ℝ) (k : ℕ → ℝ) (n : ℕ) :
    subHalfPartialPoleSum ε k n = poleValue k n ε := rfl

/-- The pronic pole-sum energy `L_{T,ε}(k) = Σ_{n ≤ T} (n^{1 - ε} S_{k,ε}(n))² / (n(n + 1))`. -/
def subHalfPoleSumEnergy (ε : ℝ) (k : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem subHalfPoleSumEnergy_nonneg (ε : ℝ) (k : ℕ → ℝ) (T : ℕ) :
    0 ≤ subHalfPoleSumEnergy ε k T :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

/-- The dilated remainder `R_{ε,j}(n) = R_ε(⌊n/j⌋) - Z_ε ((n/j)^{1 - ε} - ⌊n/j⌋^{1 - ε})`. -/
def subHalfDilationRemainder (ε : ℝ) (n j : ℕ) : ℝ :=
  subHalfRemainder ε (n / j) -
    subHalfZetaCoeff ε * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) - ((n / j : ℕ) : ℝ) ^ (1 - ε))

/-- **Exact convolution prefix identity at damping `ε`.** For every kernel `k` and cutoff `n`,
`A_{k ⋆ q_ε}(n) = Z_ε n^{1 - ε} S_{k,ε}(n) + Σ_{j ≤ n} k(j) R_{ε,j}(n) + m_{q_ε} A_k(n)`. -/
theorem weightCenteredPrefix_dirichletConv_unit_subHalf (ε : ℝ) (k : ℕ → ℝ) (mk : ℝ) (n : ℕ) :
    weightCenteredPrefix (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (mk * ∑' d : ℕ, dampedSignWeight unitSign ε d / d) n =
      subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n +
        ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
          (∑' d : ℕ, dampedSignWeight unitSign ε d / d) * weightCenteredPrefix k mk n := by
  rw [weightCenteredPrefix_dirichletConv, subHalfPartialPoleSum, mul_sum, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp only [subHalfDilationRemainder, subHalfRemainder]
  ring

/-- Fractional-part inequality for `u ↦ u^{1 - ε}` (`0 ≤ ε ≤ 1`): for `1 ≤ a ≤ b` with `b - a ≤ 1`,
`0 ≤ b^{1 - ε} - a^{1 - ε} ≤ 1`. -/
theorem rpow_one_sub_sub_le_one {ε a b : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hba : b - a ≤ 1) :
    0 ≤ b ^ (1 - ε) - a ^ (1 - ε) ∧ b ^ (1 - ε) - a ^ (1 - ε) ≤ 1 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := by linarith
  refine ⟨sub_nonneg.mpr (Real.rpow_le_rpow ha0.le hab (by linarith)), ?_⟩
  have hdiv1 : 1 ≤ b / a := (one_le_div ha0).mpr hab
  have hpow : (b / a) ^ (1 - ε) ≤ b / a := by
    have h := Real.rpow_le_rpow_of_exponent_le hdiv1 (show 1 - ε ≤ 1 by linarith)
    rwa [Real.rpow_one] at h
  have hmul : b ^ (1 - ε) ≤ a ^ (1 - ε) * (b / a) := by
    have heq : b ^ (1 - ε) = a ^ (1 - ε) * (b / a) ^ (1 - ε) := by
      rw [← Real.mul_rpow ha0.le (div_nonneg hb0 ha0.le), mul_div_cancel₀ _ ha0.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg ha0.le _)
  have ha_pow : a ^ (1 - ε) / a = a ^ (-ε) := by
    rw [← Real.rpow_sub_one ha0.ne']
    congr 1; ring
  have ha_le : a ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
  have hfactor : a ^ (1 - ε) * (b / a) - a ^ (1 - ε) = (a ^ (1 - ε) / a) * (b - a) := by
    have : a ≠ 0 := ha0.ne'
    field_simp
  calc b ^ (1 - ε) - a ^ (1 - ε)
      ≤ a ^ (1 - ε) * (b / a) - a ^ (1 - ε) := sub_le_sub_right hmul _
    _ = (a ^ (1 - ε) / a) * (b - a) := hfactor
    _ = a ^ (-ε) * (b - a) := by rw [ha_pow]
    _ ≤ 1 * 1 := mul_le_mul ha_le hba (by linarith) zero_le_one
    _ = 1 := mul_one 1

/-- **Each dilated remainder at damping `0 < ε < 1` has pronic norm `O(j^{-1/2})`.**
Specifically, because `|R_{ε,j}(n)| ≤ C_ε (n/j)^{(1 - ε)/2}` for `n ≥ j` and
`((n/j)^{(1 - ε)/2})² / (n(n + 1)) ≤ j^{-(1 - ε)} n^{-(1 + ε)}`, summing over `n ≥ j` yields
`(1 + 1/ε) j^{-(1 - ε)} j^{-ε} = (1 + 1/ε) j^{-1}`. -/
theorem pronicNorm_subHalfDilationRemainder_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {j : ℕ} (hj : 1 ≤ j) (T : ℕ) :
    pronicNorm (fun n => if j ≤ n then subHalfDilationRemainder ε n j else 0) T ≤
      Real.sqrt (1 + 1 / ε) *
        (floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set C := floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε| with hC
  have hrate0 : 0 ≤ floorSumRate ((1 - ε : ℝ) : ℂ) := by
    have h := abs_subHalfRemainder_le hε hε1 1
    rw [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hC0 : 0 ≤ C := add_nonneg hrate0 (abs_nonneg _)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hpt : ∀ n : ℕ, j ≤ n →
      |subHalfDilationRemainder ε n j| ≤ C * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    intro n hjn
    have hN1 : 1 ≤ n / j := (Nat.le_div_iff_mul_le hj).mpr (by omega)
    have hNR : (1 : ℝ) ≤ ((n / j : ℕ) : ℝ) := by exact_mod_cast hN1
    have hle : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / j := Nat.cast_div_le
    have hlt : (n : ℝ) / j - ((n / j : ℕ) : ℝ) ≤ 1 := by
      have := (abs_le.mp (abs_natDiv_sub_div_le n j hj)).1
      linarith
    have hw1 : 1 ≤ Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
      Real.one_le_rpow (Real.one_le_sqrt.mpr (hNR.trans hle)) (by linarith)
    have hR := abs_subHalfRemainder_le hε hε1 (n / j)
    have hRw : Real.sqrt ((n / j : ℕ) : ℝ) ^ (1 - ε) ≤ Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hle) (by linarith)
    have hrm : (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) = ((n : ℝ) / j) ^ (1 - ε) := by
      rw [Real.div_rpow (Nat.cast_nonneg n) hj0.le, Real.rpow_neg hj0.le, div_eq_mul_inv]
    have hfr := rpow_one_sub_sub_le_one hε.le hε1.le hNR hle hlt
    rw [subHalfDilationRemainder, hrm]
    calc |subHalfRemainder ε (n / j) -
          subHalfZetaCoeff ε * (((n : ℝ) / j) ^ (1 - ε) - ((n / j : ℕ) : ℝ) ^ (1 - ε))|
        ≤ |subHalfRemainder ε (n / j)| +
            |subHalfZetaCoeff ε| * |((n : ℝ) / j) ^ (1 - ε) - ((n / j : ℕ) : ℝ) ^ (1 - ε)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ floorSumRate ((1 - ε : ℝ) : ℂ) * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) +
            |subHalfZetaCoeff ε| * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
          rw [abs_of_nonneg hfr.1]
          refine add_le_add (hR.trans (mul_le_mul_of_nonneg_left hRw hrate0))
            (mul_le_mul_of_nonneg_left (hfr.2.trans hw1) (abs_nonneg _))
      _ = C * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by rw [hC]; ring
  have hsum : ∑ n ∈ Icc 1 T, (if j ≤ n then subHalfDilationRemainder ε n j else 0) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (1 + 1 / ε) * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have hfil : ∑ n ∈ Icc 1 T, (if j ≤ n then subHalfDilationRemainder ε n j else 0) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc j T, subHalfDilationRemainder ε n j ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [← sum_filter_add_sum_filter_not (Icc 1 T) (fun n => j ≤ n)]
      have h1 : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ j ≤ n),
          (if j ≤ n then subHalfDilationRemainder ε n j else 0) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) = 0 :=
        sum_eq_zero fun n hn => by rw [if_neg (mem_filter.mp hn).2]; simp
      have h2 : (Icc 1 T).filter (fun n => j ≤ n) = Icc j T := by
        ext n; simp only [mem_filter, mem_Icc]; omega
      rw [h1, add_zero, h2]
      exact sum_congr rfl fun n hn => by rw [if_pos (mem_Icc.mp hn).1]
    rw [hfil]
    have hjε : 0 ≤ (j : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg hj0.le _
    calc ∑ n ∈ Icc j T, subHalfDilationRemainder ε n j ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc j T, C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) := by
          refine sum_le_sum fun n hn => ?_
          have hjn := (mem_Icc.mp hn).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hj.trans hjn
          have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
          have hW : (Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 =
              (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
              ← Real.rpow_mul (div_nonneg hn0.le hj0.le),
              show (1 / 2 : ℝ) * ((1 - ε) * (2 : ℕ)) = 1 - ε by push_cast; ring,
              Real.div_rpow hn0.le hj0.le, Real.rpow_neg hj0.le, div_eq_mul_inv]
          have hsq : subHalfDilationRemainder ε n j ^ 2 ≤
              C ^ 2 * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε))) := by
            rw [← hW, ← mul_pow, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hpt n hjn) 2
          have hn_pow : (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) = (n : ℝ) ^ (1 - ε) := by
            rw [← mul_assoc, ← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']
            congr 1; ring
          rw [div_le_iff₀ hpr]
          calc subHalfDilationRemainder ε n j ^ 2
              ≤ C ^ 2 * ((n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε))) := hsq
            _ = C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) := by
                rw [← hn_pow]; ring
            _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) *
                  ((n : ℝ) * ((n : ℝ) + 1)) := by gcongr; linarith
      _ = C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * ∑ n ∈ Icc j T, (n : ℝ) ^ (-(1 + ε)) := by
          rw [mul_sum]
      _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * ((1 + 1 / ε) * (j : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_one_sub_le hε hj T)
            (mul_nonneg (sq_nonneg C) hjε)
      _ = (1 + 1 / ε) * C ^ 2 * ((j : ℝ) ^ (-(1 - ε)) * (j : ℝ) ^ (-ε)) := by ring
      _ = (1 + 1 / ε) * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
          congr 1
          rw [← Real.rpow_add hj0, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
          congr 1; push_cast; ring
  rw [pronicNorm]
  have h1ε : 0 ≤ 1 + 1 / ε := by positivity
  calc Real.sqrt (∑ n ∈ Icc 1 T, (if j ≤ n then subHalfDilationRemainder ε n j else 0) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)))
      ≤ Real.sqrt ((1 + 1 / ε) * C ^ 2 * ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (1 + 1 / ε) * C * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul (mul_nonneg h1ε (sq_nonneg C)), Real.sqrt_mul h1ε, Real.sqrt_sq hC0,
          Real.sqrt_sq (Real.rpow_nonneg hj0.le _)]

/-- **Universal Individual-Kernel Partial-Pole-Sum Comparison (`0 < ε < 1`, without `CriticalWiener`).**
For *any* kernel `k : ℕ → ℝ` (not assumed to lie in `CriticalWiener`), if the dilated-remainder
sum has pronic norm at most `B_rem` and `A_k` has pronic norm at most `B_self` at cutoff `T`, then
`|√E_T(k ⋆ d^{-ε}) - |Z_ε| √L_{T,ε}(k)| ≤ B_rem + |m_{q_ε}| B_self`. -/
theorem abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le_of_bounds
    {ε : ℝ} {k : ℕ → ℝ} {mk B_rem B_self : ℝ} {T : ℕ}
    (hrem : pronicNorm (fun n => ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j) T ≤ B_rem)
    (hself : pronicNorm (weightCenteredPrefix k mk) T ≤ B_self) :
    |Real.sqrt (weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (mk * ∑' d : ℕ, dampedSignWeight unitSign ε d / d) T) -
      |subHalfZetaCoeff ε| * Real.sqrt (subHalfPoleSumEnergy ε k T)| ≤
      B_rem + |∑' d : ℕ, dampedSignWeight unitSign ε d / d| * B_self := by
  set mq := ∑' d : ℕ, dampedSignWeight unitSign ε d / d
  rw [weightPronicEnergy_eq_sq_pronicNorm, Real.sqrt_sq (pronicNorm_nonneg _ _)]
  have hrep : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) (mk * mq) n =
        subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n +
          (∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
            mq * weightCenteredPrefix k mk n) := by
    intro n _
    rw [weightCenteredPrefix_dirichletConv_unit_subHalf ε k mk n]
    ring
  have hρ : pronicNorm (fun n => ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
      mq * weightCenteredPrefix k mk n) T ≤ B_rem + |mq| * B_self := by
    refine (pronicNorm_add_le _ _ T).trans (add_le_add hrem ?_)
    rw [pronicNorm_smul]
    exact mul_le_mul_of_nonneg_left hself (abs_nonneg _)
  have hmain : pronicNorm (fun n => subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) *
      subHalfPartialPoleSum ε k n) T =
      |subHalfZetaCoeff ε| * Real.sqrt (subHalfPoleSumEnergy ε k T) := by
    rw [pronicNorm, subHalfPoleSumEnergy]
    have h : ∑ n ∈ Icc 1 T,
        (subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) =
        |subHalfZetaCoeff ε| ^ 2 * ∑ n ∈ Icc 1 T,
          ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [sq_abs]
      ring
    rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  have h1 := pronicNorm_add_le
    (fun n => subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n)
    (fun n => ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
      mq * weightCenteredPrefix k mk n) T
  rw [← pronicNorm_congr hrep] at h1
  have h2 : pronicNorm
      (fun n => subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) T ≤
      pronicNorm (weightCenteredPrefix
        (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) (mk * mq)) T +
      pronicNorm (fun n => ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
        mq * weightCenteredPrefix k mk n) T := by
    have h := pronicNorm_add_le (weightCenteredPrefix
        (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) (mk * mq))
      (fun n => (-1) * (∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j +
        mq * weightCenteredPrefix k mk n)) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
    refine le_of_eq_of_le (pronicNorm_congr fun n hn => ?_) h
    rw [hrep n hn]
    ring
  rw [hmain] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **The Sub-Half-Damped Receiver Is the Pronic Energy of the Partial Pole Sums (`0 < ε < 1`).**
For every kernel `k` in `CriticalWiener` (`Σ_j |k(j)| j^{-1/2} < ∞`) and every `0 < ε < 1`, there is
`B ≥ 0` such that at every cutoff `T`,
`|√E_T(k ⋆ d^{-ε}) - |Z_ε| √L_{T,ε}(k)| ≤ B`. -/
theorem abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ∃ B : ℝ, ∀ T : ℕ,
      |Real.sqrt (weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
          (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d) T) -
        |subHalfZetaCoeff ε| * Real.sqrt (subHalfPoleSumEnergy ε k T)| ≤ B := by
  have hW : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := hk
  set G := ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))
  set mq := ∑' d : ℕ, dampedSignWeight unitSign ε d / d
  set mk := ∑' j : ℕ, k j / j
  set C := floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|
  have hrate0 : 0 ≤ floorSumRate ((1 - ε : ℝ) : ℂ) := by
    have h := abs_subHalfRemainder_le hε hε1 1
    rw [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hC0 : 0 ≤ C := add_nonneg hrate0 (abs_nonneg _)
  refine ⟨Real.sqrt (1 + 1 / ε) * C * G + |mq| * ((Real.sqrt 2 + 1) * G), fun T => ?_⟩
  have hq := summable_unit_weight hε
  have hmean : ∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d = mk * mq :=
    (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hq.hasSum hk.summable_abs_div
      hq.abs).tsum_eq
  rw [hmean]
  refine abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le_of_bounds ?_
    (pronicNorm_weightCenteredPrefix_le_critical hk T)
  have hcongr : pronicNorm (fun n => ∑ j ∈ Icc 1 n, k j * subHalfDilationRemainder ε n j) T =
      pronicNorm (fun n => ∑ j ∈ Icc 1 T,
        k j * (if j ≤ n then subHalfDilationRemainder ε n j else 0)) T := by
    refine pronicNorm_congr fun n hn => ?_
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    congr 1
    have hnT := (mem_Icc.mp hn).2
    ext j; simp only [mem_filter, mem_Icc]; omega
  rw [hcongr]
  refine (pronicNorm_sum_le (Icc 1 T)
    (fun j n => k j * (if j ≤ n then subHalfDilationRemainder ε n j else 0)) T).trans ?_
  calc ∑ j ∈ Icc 1 T, pronicNorm
        (fun n => k j * (if j ≤ n then subHalfDilationRemainder ε n j else 0)) T
      = ∑ j ∈ Icc 1 T, |k j| *
          pronicNorm (fun n => if j ≤ n then subHalfDilationRemainder ε n j else 0) T :=
        sum_congr rfl fun j _ => pronicNorm_smul _ _ _
    _ ≤ ∑ j ∈ Icc 1 T, |k j| * (Real.sqrt (1 + 1 / ε) * C * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (pronicNorm_subHalfDilationRemainder_le hε hε1 (mem_Icc.mp hj).1 T) (abs_nonneg _)
    _ = Real.sqrt (1 + 1 / ε) * C * ∑ j ∈ Icc 1 T, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ Real.sqrt (1 + 1 / ε) * C * G :=
        mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun j _ => by positivity) (by positivity)

theorem weightPronicEnergy_nonneg' (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    0 ≤ weightPronicEnergy c m T := by
  rw [weightPronicEnergy]
  exact sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

/-- **Two-sided criterion for `k ⋆ d^{-ε}` on `CriticalWiener` (`0 < ε < 1`).**
For `k ∈ CriticalWiener` and `0 < ε < 1`, the receiver of `k ⋆ d^{-ε}` is bounded if and only if
the pronic energy series `Σ_n (n^{1 - ε} S_{k,ε}(n))² / (n(n + 1))` of the partial pole sums is
summable. -/
theorem receiverBounded_dirichletConv_unit_subHalf_iff_summable_partialPoleSum
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
      Summable (fun n : ℕ =>
        ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
  obtain ⟨B, hB⟩ := abs_sqrt_weightPronicEnergy_dirichletConv_unit_subHalf_sub_le hε hε1 hk
  set c := RHTower.dirichletConv k (dampedSignWeight unitSign ε)
  set m := ∑' d : ℕ, c d / d
  set Z := |subHalfZetaCoeff ε|
  have hZ : 0 < Z := abs_pos.mpr (subHalfZetaCoeff_ne_zero hε hε1)
  constructor
  · rintro ⟨E, hE⟩
    have hE0 : 0 ≤ E := (weightPronicEnergy_nonneg' c m 0).trans (hE 0)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    set M := (Real.sqrt E + B) / Z
    have hM0 : 0 ≤ M := by positivity
    refine summable_of_sum_range_le
      (fun n => div_nonneg (sq_nonneg _) (by positivity)) (c := M ^ 2) fun N => ?_
    have hsub' : ∑ n ∈ range N,
        ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        subHalfPoleSumEnergy ε k N := by
      rw [subHalfPoleSumEnergy]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · rw [sum_range_eq_add_Ico _ hN]
        have h0 : (((0 : ℕ) : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k 0) ^ 2 /
            (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) + 1)) = 0 := by simp
        rw [h0, zero_add]
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
          fun _ _ _ => div_nonneg (sq_nonneg _) (by positivity)
        simp only [mem_Ico, mem_Icc] at hn ⊢; omega
    have hL : Real.sqrt (subHalfPoleSumEnergy ε k N) ≤ M := by
      have h1 := (abs_le.mp (hB N)).1
      have h2 := Real.sqrt_le_sqrt (hE N)
      rw [le_div_iff₀ hZ]; linarith
    calc ∑ n ∈ range N,
          ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ subHalfPoleSumEnergy ε k N := hsub'
      _ = Real.sqrt (subHalfPoleSumEnergy ε k N) ^ 2 :=
          (Real.sq_sqrt (subHalfPoleSumEnergy_nonneg ε k N)).symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL 2
  · intro hsum
    set L := ∑' n : ℕ,
      ((n : ℝ) ^ (1 - ε) * subHalfPartialPoleSum ε k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    refine ⟨(Z * Real.sqrt L + B) ^ 2, fun T => ?_⟩
    have hLT : subHalfPoleSumEnergy ε k T ≤ L :=
      hsum.sum_le_tsum (Icc 1 T) fun _ _ => div_nonneg (sq_nonneg _) (by positivity)
    have h1 := (abs_le.mp (hB T)).2
    have h2 : Z * Real.sqrt (subHalfPoleSumEnergy ε k T) ≤ Z * Real.sqrt L :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLT) hZ.le
    have hsqrt : Real.sqrt (weightPronicEnergy c m T) ≤ Z * Real.sqrt L + B := by linarith
    calc weightPronicEnergy c m T
        = Real.sqrt (weightPronicEnergy c m T) ^ 2 :=
          (Real.sq_sqrt (weightPronicEnergy_nonneg' c m T)).symm
      _ ≤ (Z * Real.sqrt L + B) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2

/-! ### Individual Kernels Beyond `CriticalWiener` via Möbius Inversion -/

theorem dirichletConv_comm' (a b : ℕ → ℝ) :
    RHTower.dirichletConv a b = RHTower.dirichletConv b a := by
  funext n
  rw [dirichletConv_eq_toAF_mul, dirichletConv_eq_toAF_mul, mul_comm]

theorem dirichletConv_assoc' (a b c : ℕ → ℝ) :
    RHTower.dirichletConv (RHTower.dirichletConv a b) c =
      RHTower.dirichletConv a (RHTower.dirichletConv b c) := by
  funext n
  rw [dirichletConv_eq_toAF_mul, toAF_dirichletConv, mul_assoc,
    ← toAF_dirichletConv, ← dirichletConv_eq_toAF_mul]

theorem dirichletConv_unitMass_right_of_pos (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    RHTower.dirichletConv f unitMass n = f n := by
  have h1 : toAF unitMass = 1 := by
    ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [toAF]
    · simp [toAF, hm, unitMass, ArithmeticFunction.one_apply]
  rw [dirichletConv_eq_toAF_mul, h1, mul_one]
  simp [toAF, hn.ne']

theorem dirichletConv_moebiusReal_unitSign :
    RHTower.dirichletConv moebiusReal unitSign = unitMass := by
  have h := dirichletConv_pmPowerDamped_unitSign 0
  have h1 : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d; simp [pmPowerDampedRealWeight]
  have h2 : dampedSignWeight unitSign 0 = unitSign := by
    funext d; simp [dampedSignWeight]
  rwa [h1, h2] at h

theorem dirichletConv_unitSign_moebiusReal :
    RHTower.dirichletConv unitSign moebiusReal = unitMass := by
  rw [dirichletConv_comm', dirichletConv_moebiusReal_unitSign]

/-- The Möbius-inverted kernel `k_{s,ε}(j) = (s ⋆ μ)(j) j^{-ε}` associated to an arithmetic signal
`s : ℕ → ℝ` at damping `ε`. -/
def moebiusInvertedKernel (s : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ :=
  dampedSignWeight (RHTower.dirichletConv s moebiusReal) ε

/-- **Dirichlet convolution of `moebiusInvertedKernel s ε` with `d^{-ε}` recovers `s(d) d^{-ε}`.**
This provides an explicit constructor of individual kernels `k` for which `k ⋆ d^{-ε}` has a known
receiver behavior regardless of whether `k` belongs to `CriticalWiener`. -/
theorem dirichletConv_moebiusInvertedKernel_unit {s : ℕ → ℝ} (hs0 : s 0 = 0) (ε : ℝ) :
    RHTower.dirichletConv (moebiusInvertedKernel s ε) (dampedSignWeight unitSign ε) =
      dampedSignWeight s ε := by
  funext d
  rw [moebiusInvertedKernel, ← dampedSignWeight_dirichletConv]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [RHTower.dirichletConv, dampedSignWeight, hs0]
  have hconv : RHTower.dirichletConv (RHTower.dirichletConv s moebiusReal) unitSign d = s d := by
    rw [dirichletConv_assoc', dirichletConv_moebiusReal_unitSign]
    exact dirichletConv_unitMass_right_of_pos s hd
  rw [dampedSignWeight, hconv, dampedSignWeight]

/-- **Individual kernels with bounded-partial-sum target `s` pay `k ⋆ d^{-ε}` (`0 < ε`).**
Even when `moebiusInvertedKernel s ε` lies outside `CriticalWiener`, if `s` has bounded partial sums
then `moebiusInvertedKernel s ε ⋆ d^{-ε} = dampedSignWeight s ε` has a bounded receiver. -/
theorem receiverBounded_dirichletConv_moebiusInvertedKernel_of_bounded_partialSums
    {s : ℕ → ℝ} (hs0 : s 0 = 0) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hS : ∀ N, |∑ d ∈ range N, s d| ≤ B) :
    ReceiverBounded
      (RHTower.dirichletConv (moebiusInvertedKernel s ε) (dampedSignWeight unitSign ε)) := by
  rw [dirichletConv_moebiusInvertedKernel_unit hs0 ε]
  exact exists_weightPronicEnergy_dampedSign_le hB hε hS

/-- **Individual kernels with power-saving target `|Σ_{e ≤ N} s(e)| ≤ C (N + 1)^β` (`β < 1`, `β < 2ε`)
pay `k ⋆ d^{-ε}`.** -/
theorem receiverBounded_dirichletConv_moebiusInvertedKernel_of_partialSum_rpow
    {s : ℕ → ℝ} (hs0 : s 0 = 0) {C β ε : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβε : β / 2 < ε) (hs1 : ∀ d, |s d| ≤ 1)
    (hS : ∀ N : ℕ, |∑ e ∈ Icc 1 N, s e| ≤ C * ((N : ℝ) + 1) ^ β) :
    ReceiverBounded
      (RHTower.dirichletConv (moebiusInvertedKernel s ε) (dampedSignWeight unitSign ε)) := by
  rw [dirichletConv_moebiusInvertedKernel_unit hs0 ε]
  exact receiverBounded_dampedSign_of_partialSum_rpow hs1 hβ0 hβ1 hC hS hβε

/-- **The Möbius kernel `k(j) = μ(j) j^{-ε}` is not absolutely summable at the pole abscissa `1 - ε`.**
Indeed, `|k(j)| j^{-(1 - ε)} = |μ(j)| / j ≥ o(j) / j`, whose dyadic blocks `Ioc n (2n)` stay bounded
below by a positive constant (`eventually_oddSqfWeight_drift`). -/
theorem not_summable_abs_pmPowerDamped_abscissa (ε : ℝ) :
    ¬ Summable (fun j : ℕ => |pmPowerDampedRealWeight ε j| * (j : ℝ) ^ (-(1 - ε))) := by
  intro hsum
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_oddSqfWeight_drift (ε := 1 / 2) (by norm_num))
  have hcauchy := summable_iff_vanishing_norm.mp hsum
  set δ := RHTower.Sieve.squarefreeDensity / 3 * (2 : ℝ) ^ (-(1 + (1 / 2 : ℝ)))
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hδ : 0 < δ := by
    simp only [δ]; positivity
  obtain ⟨S, hS⟩ := hcauchy δ hδ
  set n := max (max N₀ 1) (S.sup id + 1)
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hdisj : Disjoint (Ioc n (2 * n)) S := by
    rw [disjoint_left]
    intro j hj hjS
    rw [mem_Ioc] at hj
    have hjle : j ≤ S.sup id := le_sup (f := id) hjS
    have hSn : S.sup id + 1 ≤ n := le_max_right (max N₀ 1) (S.sup id + 1)
    omega
  have hlt := hS (Ioc n (2 * n)) hdisj
  rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))] at hlt
  have hle : δ ≤ ∑ j ∈ Ioc n (2 * n), |pmPowerDampedRealWeight ε j| * (j : ℝ) ^ (-(1 - ε)) := by
    have hdrift := hN₀ n hnN₀
    have hterm : ∀ j ∈ Ioc n (2 * n),
        (n : ℝ) * (oddSqfWeight (1 / 2) j / (j : ℝ)) ≤
          (n : ℝ) ^ (1 - (1 / 2 : ℝ)) *
            (|pmPowerDampedRealWeight ε j| * (j : ℝ) ^ (-(1 - ε))) := by
      intro j hj
      rw [mem_Ioc] at hj
      have hj1 : 1 ≤ j := by omega
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hnj : (n : ℝ) ≤ j := by exact_mod_cast hj.1.le
      have hpow_j : (j : ℝ) ^ (-ε) * (j : ℝ) ^ (-(1 - ε)) = (j : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hj0, show -ε + -(1 - ε) = -1 by ring]
      have hpow_n : (n : ℝ) * (j : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
        have hj_le : (j : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hn0 hnj (by norm_num)
        have h1 : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) =
            (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_one]
        calc (n : ℝ) * (j : ℝ) ^ (-(1 / 2 : ℝ))
            ≤ (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hj_le hn0.le
          _ = (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
              rw [h1, ← Real.rpow_add hn0, ← sub_eq_add_neg]
      have hmu : oddSqfAF j ≤ |moebiusReal j| := by
        rw [oddSqfAF_apply]
        split_ifs with h
        · rw [moebiusReal]
          have hsq : (((ArithmeticFunction.moebius j : ℤ) : ℝ)) ^ 2 = 1 := by
            exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree h.2
          have h1 : |((ArithmeticFunction.moebius j : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          nlinarith [sq_abs (((ArithmeticFunction.moebius j : ℤ) : ℝ)),
            abs_nonneg (((ArithmeticFunction.moebius j : ℤ) : ℝ))]
        · exact abs_nonneg _
      rw [oddSqfWeight, dampedSignWeight, pmPowerDampedRealWeight, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hj0.le _),
        mul_assoc |moebiusReal j|, hpow_j, Real.rpow_neg_one, ← div_eq_mul_inv]
      calc (n : ℝ) * (oddSqfAF j * (j : ℝ) ^ (-(1 / 2 : ℝ)) / (j : ℝ))
          = ((n : ℝ) * (j : ℝ) ^ (-(1 / 2 : ℝ))) * (oddSqfAF j / (j : ℝ)) := by ring
        _ ≤ (n : ℝ) ^ (1 - (1 / 2 : ℝ)) * (|moebiusReal j| / (j : ℝ)) :=
            mul_le_mul hpow_n (div_le_div_of_nonneg_right hmu hj0.le)
              (div_nonneg (by rw [oddSqfAF_apply]; split_ifs <;> norm_num) hj0.le)
              (Real.rpow_nonneg hn0.le _)
    have hsum_le : (n : ℝ) * ∑ j ∈ Ioc n (2 * n), oddSqfWeight (1 / 2) j / (j : ℝ) ≤
        (n : ℝ) ^ (1 - (1 / 2 : ℝ)) *
          ∑ j ∈ Ioc n (2 * n), |pmPowerDampedRealWeight ε j| * (j : ℝ) ^ (-(1 - ε)) := by
      rw [mul_sum, mul_sum]
      exact sum_le_sum hterm
    have hcomb := hdrift.trans hsum_le
    have hn_rpow : 0 < (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := Real.rpow_pos_of_pos hn0 _
    exact le_of_mul_le_mul_left (by linarith) hn_rpow
  linarith

/-- **For `0 < ε ≤ 1/2`, `pmPowerDampedRealWeight ε` (`μ(d) d^{-ε}`) lies outside `CriticalWiener`,
yet `pmPowerDampedRealWeight ε ⋆ d^{-ε} = δ_1` has zero receiver energy at every cutoff `T`.** -/
theorem not_criticalWiener_pmPowerDamped {ε : ℝ} (hε2 : ε ≤ 1 / 2) :
    ¬ CriticalWiener (pmPowerDampedRealWeight ε) := by
  intro hk
  apply not_summable_abs_pmPowerDamped_abscissa ε
  refine hk.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg j) _)) fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [pmPowerDampedRealWeight, moebiusReal]
  · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)

theorem receiverBounded_dirichletConv_pmPowerDamped_unit (ε : ℝ) :
    ReceiverBounded
      (RHTower.dirichletConv (pmPowerDampedRealWeight ε) (dampedSignWeight unitSign ε)) := by
  rw [dirichletConv_pmPowerDamped_unitSign]
  refine ⟨0, fun T => ?_⟩
  have hmean : (∑' d : ℕ, unitMass d / (d : ℝ)) = 1 := by
    rw [tsum_eq_single 1]
    · simp [unitMass]
    · intro d hd
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp
      · simp [unitMass, hd]
  rw [hmean, weightPronicEnergy]
  refine le_of_eq (sum_eq_zero fun n hn => ?_)
  have hn1 := (mem_Icc.mp hn).1
  have hpref : weightCenteredPrefix unitMass 1 n = 0 := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
      sum_eq_single 1]
    · simp [unitMass]
    · intro d _ hd1; simp [unitMass, hd1]
    · intro h1; exfalso; exact h1 (mem_Icc.mpr ⟨le_rfl, hn1⟩)
  rw [hpref, sq, zero_mul, zero_div]

/-! ## §2. Signed Logarithmic Rate Transfer and Complete Vertical-Line Boundary Energy Equivalence -/

/-- `log n = (1 ⋆ Λ)(n)` as a Dirichlet convolution with `unitSign`. -/
theorem logWeight_unitSign_eq_dirichletConv_vonMangoldt :
    logWeight unitSign =
      RHTower.dirichletConv (fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ)) unitSign := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logWeight, unitSign, RHTower.dirichletConv]
  · rw [logWeight, unitSign, one_mul, ← ArithmeticFunction.vonMangoldt_sum,
      RHTower.dirichletConv]
    refine sum_congr rfl fun d _ => ?_
    simp [unitSign]

/-- Möbius inversion of `log = 1 ⋆ Λ`: `(log 1 ⋆ μ)(n) = Λ(n)`. -/
theorem dirichletConv_logWeight_unitSign_moebiusReal :
    RHTower.dirichletConv (logWeight unitSign) moebiusReal =
      fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ) := by
  rw [logWeight_unitSign_eq_dirichletConv_vonMangoldt, dirichletConv_assoc',
    dirichletConv_unitSign_moebiusReal]
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RHTower.dirichletConv]
  · exact dirichletConv_unitMass_right_of_pos _ hn

/-- **Selberg–von Mangoldt identity for `moebiusReal`.**
Pointwise on `ℕ`, `-μ(n) log n = (μ ⋆ Λ)(n)`: differentiating `μ ⋆ 1 = δ_1` with `logWeight`
and inverting `1` by `μ` expresses the signed logarithmic Möbius weight as `μ ⋆ Λ`. -/
theorem neg_logWeight_moebiusReal_eq_dirichletConv (n : ℕ) :
    -logWeight moebiusReal n =
      RHTower.dirichletConv moebiusReal
        (fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ)) n := by
  have h0 : ∀ m : ℕ, logWeight unitMass m = 0 := fun m => by
    rcases eq_or_ne m 1 with rfl | hm
    · simp [logWeight, unitMass]
    · simp [logWeight, unitMass, hm]
  have hleib : ∀ m : ℕ,
      RHTower.dirichletConv (logWeight moebiusReal) unitSign m +
        RHTower.dirichletConv moebiusReal (logWeight unitSign) m = 0 := fun m => by
    rw [← logWeight_dirichletConv, dirichletConv_moebiusReal_unitSign, h0]
  have hconv : RHTower.dirichletConv
      (fun m => RHTower.dirichletConv (logWeight moebiusReal) unitSign m +
        RHTower.dirichletConv moebiusReal (logWeight unitSign) m) moebiusReal n = 0 := by
    rw [RHTower.dirichletConv]
    exact sum_eq_zero fun d _ => by rw [hleib d, zero_mul]
  have hadd : RHTower.dirichletConv
      (fun m => RHTower.dirichletConv (logWeight moebiusReal) unitSign m +
        RHTower.dirichletConv moebiusReal (logWeight unitSign) m) moebiusReal n =
      RHTower.dirichletConv (RHTower.dirichletConv (logWeight moebiusReal) unitSign) moebiusReal n +
        RHTower.dirichletConv (RHTower.dirichletConv moebiusReal (logWeight unitSign))
          moebiusReal n := by
    simp only [RHTower.dirichletConv, add_mul, sum_add_distrib]
  rw [hadd, dirichletConv_assoc', dirichletConv_unitSign_moebiusReal,
    dirichletConv_assoc', dirichletConv_logWeight_unitSign_moebiusReal] at hconv
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logWeight, RHTower.dirichletConv]
  · have h1 := dirichletConv_unitMass_right_of_pos (logWeight moebiusReal) hn
    linarith

/-- **Abel transfer from signed logarithmic partial sums to undamped block sums.**
If `|Σ_{e ≤ x} s(e) log e| ≤ M_log x` for `x ≥ D ≥ 1`, then on every interval `(D, X]` (`D ≤ X`),
`|Σ_{D < d ≤ X} s(d)| ≤ (2 M_log / log(D + 1)) X`. -/
theorem abs_sum_Ioc_le_of_logWeight_linear {s : ℕ → ℝ} {M_log : ℝ} {D X : ℕ}
    (hD : 1 ≤ D) (hDX : D ≤ X) (hM : 0 ≤ M_log)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e * Real.log e| ≤ M_log * x) :
    |∑ d ∈ Ioc D X, s d| ≤ (2 * M_log / Real.log ((D : ℝ) + 1)) * X := by
  set w : ℕ → ℝ := fun d => 1 / Real.log ((max d (D + 1) : ℕ) : ℝ)
  have hlogD1 : 0 < Real.log ((D : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < D + 1 by omega))
  have hw0 : ∀ d, 0 ≤ w d := fun d => by
    dsimp [w]
    have h2 : (1 : ℝ) < ((max d (D + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < max d (D + 1) by omega)
    exact div_nonneg zero_le_one (Real.log_pos h2).le
  have hwa : ∀ d, D < d → w (d + 1) ≤ w d := fun d hd => by
    dsimp [w]
    rw [max_eq_left (by omega : D + 1 ≤ d + 1), max_eq_left (by omega : D + 1 ≤ d)]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
    exact one_div_le_one_div_of_le hlogd
      (Real.log_le_log hd0 (by exact_mod_cast Nat.le_succ d))
  have heq : ∑ d ∈ Ioc D X, s d = ∑ d ∈ Ioc D X, (s d * Real.log d) * w d := by
    refine sum_congr rfl fun d hd => ?_
    rw [mem_Ioc] at hd
    dsimp [w]
    rw [max_eq_left (by omega : D + 1 ≤ d)]
    have hlogd : Real.log (d : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < d by omega))).ne'
    field_simp
  rw [heq]
  have hab := abs_sum_Ioc_mul_le_of_linear (s := fun e => s e * Real.log e) (w := w)
    hDX (fun x hx _ => hS x hx) hw0 hwa
  have hwD1 : w (D + 1) = 1 / Real.log ((D : ℝ) + 1) := by
    dsimp [w]; rw [max_self, Nat.cast_add, Nat.cast_one]
  have hsum_w : ∑ d ∈ Ioc D X, w d ≤ ((X - D : ℕ) : ℝ) * w (D + 1) := by
    calc ∑ d ∈ Ioc D X, w d
        ≤ ∑ _d ∈ Ioc D X, w (D + 1) := sum_le_sum fun d hd => by
          rw [mem_Ioc] at hd
          dsimp [w]
          rw [max_eq_left (by omega : D + 1 ≤ d), max_self, Nat.cast_add, Nat.cast_one]
          exact one_div_le_one_div_of_le hlogD1
            (Real.log_le_log (by positivity) (by exact_mod_cast (show D + 1 ≤ d by omega)))
      _ = ((X - D : ℕ) : ℝ) * w (D + 1) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hDX_cast : 2 * (D : ℝ) * w (D + 1) + ((X - D : ℕ) : ℝ) * w (D + 1) ≤
      2 * (X : ℝ) * w (D + 1) := by
    rw [Nat.cast_sub hDX]
    have hw_nonneg : 0 ≤ w (D + 1) := hw0 (D + 1)
    have hDXR : (D : ℝ) ≤ X := by exact_mod_cast hDX
    nlinarith
  calc |∑ d ∈ Ioc D X, (s d * Real.log d) * w d|
      ≤ M_log * (2 * D * w (D + 1) + ∑ d ∈ Ioc D X, w d) := hab
    _ ≤ M_log * (2 * D * w (D + 1) + ((X - D : ℕ) : ℝ) * w (D + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hM
    _ ≤ M_log * (2 * (X : ℝ) * w (D + 1)) :=
        mul_le_mul_of_nonneg_left hDX_cast hM
    _ = (2 * M_log / Real.log ((D : ℝ) + 1)) * X := by
        rw [hwD1]; ring

/-- **Signed-logarithmic hyperbola rate transfer with `(log(D + 1))⁻¹` gain (`0 < ε ≤ 1/2`).**
If `|s(d)| ≤ 1` and the signed logarithmic partial sums satisfy
`|Σ_{e ≤ x} s(e) log e| ≤ M_log x` for all `x ≥ D ≥ 1`, then for `1 ≤ D ≤ n` and `0 < ε ≤ 1/2`,
`|A_{s,ε}(n)| ≤ 6 D^{1 - ε} + (26 / (ε log(D + 1))) M_log n D^{-ε}`. -/
theorem abs_weightCenteredPrefix_dampedSign_le_of_logWeight_linear_pos
    {s : ℕ → ℝ} {M_log ε : ℝ} (hM : 0 ≤ M_log) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hs1 : ∀ d, |s d| ≤ 1) {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e * Real.log e| ≤ M_log * x) :
    |weightCenteredPrefix (dampedSignWeight s ε) (∑' d : ℕ, dampedSignWeight s ε d / d) n| ≤
      6 * (D : ℝ) ^ (1 - ε) +
        26 / (ε * Real.log ((D : ℝ) + 1)) * M_log * n * (D : ℝ) ^ (-ε) := by
  set s₂ : ℕ → ℝ := fun d => if D < d then s d else 0
  have hs₂1 : ∀ d, |s₂ d| ≤ 1 := fun d => by
    dsimp [s₂]; split_ifs <;> [exact hs1 d; norm_num]
  have hlogD1 : 0 < Real.log ((D : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < D + 1 by omega))
  set L := 2 * M_log / Real.log ((D : ℝ) + 1)
  have hL0 : 0 ≤ L := div_nonneg (by linarith) hlogD1.le
  have hS₂ : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s₂ e| ≤ L * x := by
    intro x hx
    have heq : ∑ e ∈ Icc 1 x, s₂ e = ∑ e ∈ Ioc D x, s e := by
      dsimp [s₂]
      rw [← sum_filter]
      congr 1
      ext e; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
    rw [heq]
    exact abs_sum_Ioc_le_of_logWeight_linear hD hx hM hS
  have hA₂ := abs_weightCenteredPrefix_dampedSign_le_of_linear_pos hL0 hε hε2 hs₂1 hD hDn hS₂
  set c := dampedSignWeight s ε
  set c₂ := dampedSignWeight s₂ ε
  have hsum := summable_dampedSignWeight_div_of_abs_le_one hε hs1
  have hsum₂ := summable_dampedSignWeight_div_of_abs_le_one hε hs₂1
  have hmean_diff : (∑' d : ℕ, c d / d) - (∑' d : ℕ, c₂ d / d) =
      ∑ d ∈ Icc 1 D, c d / d := by
    rw [← hsum.tsum_sub hsum₂]
    have hfin : (fun d : ℕ => c d / d - c₂ d / d) =
        fun d : ℕ => if d ∈ Icc 1 D then c d / d else 0 := by
      funext d
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [c, c₂, dampedSignWeight]
      · by_cases hdD : d ≤ D
        · have hmem : d ∈ Icc 1 D := mem_Icc.mpr ⟨hd, hdD⟩
          have hnot : ¬ D < d := by omega
          simp [hmem, c, c₂, s₂, dampedSignWeight, hnot]
        · have hmem : d ∉ Icc 1 D := fun h => hdD (mem_Icc.mp h).2
          have hlt : D < d := by omega
          simp [hmem, c, c₂, s₂, dampedSignWeight, hlt]
    rw [hfin, tsum_eq_sum (s := Icc 1 D) (fun d hd => if_neg hd)]
    exact sum_congr rfl fun d hd => if_pos hd
  have hfloor_diff : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) -
      ∑ d ∈ Icc 1 n, c₂ d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) := by
    rw [← sum_sub_distrib]
    have hsub : Icc 1 D ⊆ Icc 1 n := fun d hd =>
      mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hDn⟩
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun d hd => ?_
      have hnot : ¬ D < d := not_lt.mpr (mem_Icc.mp hd).2
      simp [c, c₂, s₂, dampedSignWeight, hnot]
    · intro d hd hnot
      have hlt : D < d := by
        rw [mem_Icc] at hd hnot; omega
      simp [c, c₂, s₂, dampedSignWeight, hlt]
  have hdecomp : weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      (∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        weightCenteredPrefix c₂ (∑' d : ℕ, c₂ d / d) n := by
    rw [weightCenteredPrefix, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
      sum_Icc_sum_divisors_eq_floor]
    linear_combination hfloor_diff - (n : ℝ) * hmean_diff
  have ha : |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| ≤
      3 * (D : ℝ) ^ (1 - ε) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D, |c d * ((n / d : ℕ) : ℝ) - n * (c d / d)| ≤ (d : ℝ) ^ (-ε) := by
      intro d hd
      rw [mem_Icc] at hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
      have hc : |c d| ≤ (d : ℝ) ^ (-ε) := by
        rw [show c d = s d * (d : ℝ) ^ (-ε) from rfl, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
      have heq : c d * ((n / d : ℕ) : ℝ) - n * (c d / d) =
          c d * (((n / d : ℕ) : ℝ) - n / d) := by field_simp
      rw [heq, abs_mul]
      have hfr : |((n / d : ℕ) : ℝ) - n / d| ≤ 1 := abs_natDiv_sub_div_le n d hd.1
      exact (mul_le_mul hc hfr (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans
        (le_of_eq (mul_one _))
    exact (sum_le_sum hterm).trans (sum_Icc_rpow_neg_le_three hε hε2 hD)
  rw [hdecomp]
  calc |(∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d) +
        weightCenteredPrefix c₂ (∑' d : ℕ, c₂ d / d) n|
      ≤ |∑ d ∈ Icc 1 D, c d * ((n / d : ℕ) : ℝ) - n * ∑ d ∈ Icc 1 D, c d / d| +
          |weightCenteredPrefix c₂ (∑' d : ℕ, c₂ d / d) n| := abs_add_le _ _
    _ ≤ 3 * (D : ℝ) ^ (1 - ε) + (3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε)) :=
        add_le_add ha hA₂
    _ = 6 * (D : ℝ) ^ (1 - ε) +
          26 / (ε * Real.log ((D : ℝ) + 1)) * M_log * n * (D : ℝ) ^ (-ε) := by
        dsimp [L]; ring

/-- Specialization of `abs_weightCenteredPrefix_dampedSign_le_of_logWeight_linear_pos` to the actual
Möbius row `pmPowerDampedRealWeight ε` (`μ(d) d^{-ε}`). -/
theorem abs_weightCenteredPrefix_pmPowerDamped_le_of_logWeight_linear_pos
    {M_log ε : ℝ} (hM : 0 ≤ M_log) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e * Real.log e| ≤ M_log * x) :
    |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
      6 * (D : ℝ) ^ (1 - ε) +
        26 / (ε * Real.log ((D : ℝ) + 1)) * M_log * n * (D : ℝ) ^ (-ε) := by
  rw [pmPowerDampedRealWeight_eq_dampedSignWeight, dampedDensity_eq_tsum hε]
  exact abs_weightCenteredPrefix_dampedSign_le_of_logWeight_linear_pos
    hM hε hε2 (fun d => abs_moebiusReal_le_one' d) hD hDn hS

/-- **Power-saving signed logarithmic sums pay `dampedSignWeight s ε` (`β < 1`, `β < 2ε`).**
If `|s(d)| ≤ 1` and `|Σ_{e ≤ N} s(e) log e| ≤ C (N + 1)^β` for all `N` with `0 ≤ β < 1` and
`β / 2 < ε`, then `dampedSignWeight s ε` is `ReceiverBounded`. -/
theorem receiverBounded_dampedSign_of_logWeight_partialSum_rpow
    {s : ℕ → ℝ} {C β ε : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβε : β / 2 < ε) (hs1 : ∀ d, |s d| ≤ 1)
    (hS : ∀ N : ℕ, |∑ e ∈ Icc 1 N, s e * Real.log e| ≤ C * ((N : ℝ) + 1) ^ β) :
    ReceiverBounded (dampedSignWeight s ε) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C' := 1 + C / Real.log 2
  have hC' : 0 ≤ C' := by positivity
  refine receiverBounded_dampedSign_of_partialSum_rpow hs1 hβ0 hβ1 hC' (fun N => ?_) hβε
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  · have hsplit : ∑ e ∈ Icc 1 N, s e = s 1 + ∑ e ∈ Ioc 1 N, s e := by
      have hset : Icc 1 N = insert 1 (Ioc 1 N) := by
        ext e; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
      rw [hset, sum_insert (by simp)]
    set w : ℕ → ℝ := fun d => 1 / Real.log ((max d 2 : ℕ) : ℝ)
    have hw0 : ∀ d, 0 ≤ w d := fun d => by
      dsimp [w]
      have h2 : (1 : ℝ) < ((max d 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < max d 2 by omega)
      exact div_nonneg zero_le_one (Real.log_pos h2).le
    have hwa : ∀ d, 1 < d → w (d + 1) ≤ w d := fun d hd => by
      dsimp [w]
      rw [max_eq_left (by omega : 2 ≤ d + 1), max_eq_left (by omega : 2 ≤ d)]
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hlogd : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hd)
      exact one_div_le_one_div_of_le hlogd
        (Real.log_le_log hd0 (by exact_mod_cast Nat.le_succ d))
    have heq : ∑ d ∈ Ioc 1 N, s d = ∑ d ∈ Ioc 1 N, (s d * Real.log d) * w d := by
      refine sum_congr rfl fun d hd => ?_
      rw [mem_Ioc] at hd
      dsimp [w]
      rw [max_eq_left (by omega : 2 ≤ d)]
      have hlogd : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hd.1)).ne'
      field_simp
    have htel : ∀ M : ℕ, 1 ≤ M → w (M + 1) + ∑ d ∈ Ioc 1 M, (w d - w (d + 1)) = w 2 := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [sum_Ioc_succ_top hM]
        linarith
    have hIoc : |∑ d ∈ Ioc 1 N, s d| ≤ (C / Real.log 2) * ((N : ℝ) + 1) ^ β := by
      rw [heq, sum_Ioc_mul_eq_partialSums (fun e => s e * Real.log e) w hN]
      have h1_zero : ∑ e ∈ Icc 1 1, s e * Real.log e = 0 := by simp
      rw [h1_zero, zero_mul, sub_zero]
      set B_N := C * ((N : ℝ) + 1) ^ β
      have hBN0 : 0 ≤ B_N := by positivity
      have hS_le : ∀ d : ℕ, d ≤ N → |∑ e ∈ Icc 1 d, s e * Real.log e| ≤ B_N := fun d hd =>
        (hS d).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hd 1) hβ0) hC)
      have hterm1 : |(∑ e ∈ Icc 1 N, s e * Real.log e) * w (N + 1)| ≤ B_N * w (N + 1) := by
        rw [abs_mul, abs_of_nonneg (hw0 (N + 1))]
        exact mul_le_mul_of_nonneg_right (hS_le N le_rfl) (hw0 (N + 1))
      have hterm2 : |∑ d ∈ Ioc 1 N, (∑ e ∈ Icc 1 d, s e * Real.log e) * (w d - w (d + 1))| ≤
          B_N * ∑ d ∈ Ioc 1 N, (w d - w (d + 1)) := by
        rw [mul_sum]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
        rw [mem_Ioc] at hd
        have hwd : 0 ≤ w d - w (d + 1) := sub_nonneg.mpr (hwa d hd.1)
        rw [abs_mul, abs_of_nonneg hwd]
        exact mul_le_mul_of_nonneg_right (hS_le d hd.2) hwd
      have hw2 : w 2 = 1 / Real.log 2 := by dsimp [w]; norm_num
      calc |(∑ e ∈ Icc 1 N, s e * Real.log e) * w (N + 1) +
            ∑ d ∈ Ioc 1 N, (∑ e ∈ Icc 1 d, s e * Real.log e) * (w d - w (d + 1))|
          ≤ |(∑ e ∈ Icc 1 N, s e * Real.log e) * w (N + 1)| +
              |∑ d ∈ Ioc 1 N, (∑ e ∈ Icc 1 d, s e * Real.log e) * (w d - w (d + 1))| :=
            abs_add_le _ _
        _ ≤ B_N * w (N + 1) + B_N * ∑ d ∈ Ioc 1 N, (w d - w (d + 1)) := add_le_add hterm1 hterm2
        _ = B_N * (w (N + 1) + ∑ d ∈ Ioc 1 N, (w d - w (d + 1))) := by ring
        _ = B_N * (1 / Real.log 2) := by rw [htel N hN, hw2]
        _ = (C / Real.log 2) * ((N : ℝ) + 1) ^ β := by dsimp [B_N]; ring
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ β :=
      Real.one_le_rpow (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hβ0
    rw [hsplit]
    calc |s 1 + ∑ e ∈ Ioc 1 N, s e|
        ≤ |s 1| + |∑ e ∈ Ioc 1 N, s e| := abs_add_le _ _
      _ ≤ 1 + (C / Real.log 2) * ((N : ℝ) + 1) ^ β := add_le_add (hs1 1) hIoc
      _ ≤ ((N : ℝ) + 1) ^ β + (C / Real.log 2) * ((N : ℝ) + 1) ^ β := by linarith
      _ = C' * ((N : ℝ) + 1) ^ β := by dsimp [C']; ring

/-- **A power-saving bound on the Selberg–von Mangoldt sums `Σ_{e ≤ N} (μ ⋆ Λ)(e)` at a single
damping `ε > β / 2` (`0 ≤ β < 1`) pays both the Möbius and Liouville receivers at damping `ε`.** -/
theorem receiverBounded_moebius_and_liouville_of_vonMangoldtConv_partialSum_rpow
    {C β ε : ℝ} (hC : 0 ≤ C) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβε : β / 2 < ε)
    (hS : ∀ N : ℕ,
      |∑ e ∈ Icc 1 N, RHTower.dirichletConv moebiusReal
        (fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ)) e| ≤ C * ((N : ℝ) + 1) ^ β) :
    ReceiverBounded (pmPowerDampedRealWeight ε) ∧
      ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) := by
  have hε : 0 < ε := by linarith
  have hmu : ReceiverBounded (pmPowerDampedRealWeight ε) := by
    rw [pmPowerDampedRealWeight_eq_dampedSignWeight]
    refine receiverBounded_dampedSign_of_logWeight_partialSum_rpow
      hC hβ0 hβ1 hβε (fun d => abs_moebiusReal_le_one' d) fun N => ?_
    have heq : ∑ e ∈ Icc 1 N, moebiusReal e * Real.log e =
        -∑ e ∈ Icc 1 N, RHTower.dirichletConv moebiusReal
          (fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ)) e := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun e _ => by
        rw [← neg_logWeight_moebiusReal_eq_dirichletConv, neg_neg, logWeight]
    rw [heq, abs_neg]
    exact hS N
  exact ⟨hmu, (receiverBounded_moebius_iff_liouville hε).mp hmu⟩

/-- **A paid receiver caps the vertical-line boundary energy on `1/2 < σ < 1`.**
For `c ∈ DampedClass K (1 / 2)`, if the receiver energy is bounded by `E` at every horizon `T`, then
on every vertical line `1/2 < σ < 1`,
`∫_ℝ ‖ζ(σ + it)(C(σ + it) - m)/(σ + it)‖² dt ≤ 4π E`. -/
theorem lineEnergy_le_four_pi_mul_of_weightPronicEnergy_le
    {K E : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c)
    (hE : ∀ T : ℕ, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
      (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
        ((σ : ℂ) + t * I)‖ ^ 2 ≤ 4 * Real.pi * E := by
  have hcell := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero c _) hσ.le hE
  rw [sum_sq_mul_mellinCell_eq_lineEnergy hc hσ hσ1] at hcell
  have hσ0 : 0 < σ := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at hcell
  have hle : σ * ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
      (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
        ((σ : ℂ) + t * I)‖ ^ 2 ≤ σ * (4 * Real.pi * E) := by
    linarith
  exact le_of_mul_le_mul_left hle hσ0

/-- **Two-Sided Equivalence Between `ReceiverBounded` and Uniform Vertical-Line Boundary Energy.**
For `c ∈ DampedClass K (1 / 2)`, the discrete pronic receiver is bounded if and only if the
vertical-line boundary energies `∫_ℝ ‖ζ(σ + it)(C(σ + it) - m)/(σ + it)‖² dt` are uniformly bounded
across `1/2 < σ < 3/4`. -/
theorem receiverBounded_iff_exists_lineEnergy_le
    {K : ℝ} {c : ℕ → ℝ} (hc : DampedClass K (1 / 2) c) :
    ReceiverBounded c ↔
      ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 →
        ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
          (weightDirichletSeries c ((σ : ℂ) + t * I) - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) /
            ((σ : ℂ) + t * I)‖ ^ 2 ≤ M := by
  constructor
  · rintro ⟨E, hE⟩
    exact ⟨4 * Real.pi * E, fun σ hσ hσ34 =>
      lineEnergy_le_four_pi_mul_of_weightPronicEnergy_le hc hE hσ (by linarith)⟩
  · rintro ⟨M, hM⟩
    exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hc hM⟩

/-! ## §3. All-Order Logarithmic Pole Moments, Binomial Leibniz Law, and Index Additivity -/

theorem logPowWeight_add (f : ℕ → ℝ) (r m : ℕ) :
    logPowWeight (logPowWeight f r) m = logPowWeight f (r + m) := by
  funext n; simp only [logPowWeight, pow_add]; ring

theorem logPowWeight_support {f : ℕ → ℝ} {J : ℕ} (hf : ∀ j, J < j → f j = 0) (m : ℕ) :
    ∀ j, J < j → logPowWeight f m j = 0 := fun j hj => by
  simp [logPowWeight, hf j hj]

/-- **All-order binomial Leibniz identity for `logPowWeight` under Dirichlet convolution.**
`(a ⋆ b)(n) (log n)^m = Σ_{i ≤ m} C(m, i) ((a (log ·)^i) ⋆ (b (log ·)^{m - i}))(n)`. -/
theorem logPowWeight_dirichletConv (a b : ℕ → ℝ) (m n : ℕ) :
    logPowWeight (RHTower.dirichletConv a b) m n =
      ∑ i ∈ range (m + 1),
        (m.choose i : ℝ) *
          RHTower.dirichletConv (logPowWeight a i) (logPowWeight b (m - i)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logPowWeight, RHTower.dirichletConv]
  simp only [logPowWeight, RHTower.dirichletConv, sum_mul]
  have hterm : ∀ d ∈ n.divisors,
      a d * b (n / d) * (Real.log n) ^ m =
        ∑ i ∈ range (m + 1),
          (m.choose i : ℝ) * (a d * (Real.log d) ^ i * (b (n / d) * (Real.log (n / d : ℕ)) ^ (m - i))) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
    have hq0 : (0 : ℝ) < (n / d : ℕ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1)
        (Nat.pos_of_mem_divisors hd)
    have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    have hlog : Real.log (n : ℝ) = Real.log d + Real.log ((n / d : ℕ) : ℝ) := by
      rw [← hmul, Real.log_mul hd0.ne' hq0.ne']
    rw [hlog, add_pow, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum]

/-- The `m`-th logarithmic pole moment of a finite kernel `k` supported on `[1, J]` at the pole
abscissa `1 - ε`:
`poleLogMoment k J ε m = Σ_{j ≤ J} k(j) (log j)^m j^{-(1 - ε)} = (-1)^m K^{(m)}(1 - ε)`. -/
def poleLogMoment (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 J, k j * (Real.log j) ^ m * (j : ℝ) ^ (-(1 - ε))

theorem poleLogMoment_eq_poleValue_logPowWeight (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) (m : ℕ) :
    poleLogMoment k J ε m = poleValue (logPowWeight k m) J ε := rfl

@[simp]
theorem poleLogMoment_zero (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    poleLogMoment k J ε 0 = poleValue k J ε := by
  rw [poleLogMoment_eq_poleValue_logPowWeight, logPowWeight_zero]

@[simp]
theorem poleLogMoment_one (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    poleLogMoment k J ε 1 = poleSlope k J ε := by
  simp [poleLogMoment, poleSlope]

theorem poleLogMoment_logPowWeight (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) (r m : ℕ) :
    poleLogMoment (logPowWeight k r) J ε m = poleLogMoment k J ε (r + m) := by
  rw [poleLogMoment_eq_poleValue_logPowWeight, logPowWeight_add,
    ← poleLogMoment_eq_poleValue_logPowWeight]

/-- Support of a Dirichlet convolution of two finitely supported kernels: if `f₁` vanishes above `J₁`
and `f₂` vanishes above `J₂`, then `f₁ ⋆ f₂` vanishes above `J₁ * J₂`. -/
theorem dirichletConv_support_mul {f₁ f₂ : ℕ → ℝ} {J₁ J₂ : ℕ}
    (hf₁ : ∀ j, J₁ < j → f₁ j = 0) (hf₂ : ∀ j, J₂ < j → f₂ j = 0) :
    ∀ n, J₁ * J₂ < n → RHTower.dirichletConv f₁ f₂ n = 0 := by
  intro n hn
  rw [RHTower.dirichletConv]
  refine sum_eq_zero fun d hd => ?_
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  by_cases hdJ : J₁ < d
  · rw [hf₁ d hdJ, zero_mul]
  · have hqJ : J₂ < n / d := by
      by_contra hle
      push Not at hdJ hle
      have : d * (n / d) ≤ J₁ * J₂ := Nat.mul_le_mul hdJ hle
      omega
    rw [hf₂ (n / d) hqJ, mul_zero]

/-- Multiplicativity of `poleValue` under Dirichlet convolution of finitely supported kernels:
`poleValue (f₁ ⋆ f₂) (J₁ * J₂) ε = poleValue f₁ J₁ ε * poleValue f₂ J₂ ε`. -/
theorem poleValue_dirichletConv {f₁ f₂ : ℕ → ℝ} {J₁ J₂ : ℕ}
    (hf₁ : ∀ j, J₁ < j → f₁ j = 0) (hf₂ : ∀ j, J₂ < j → f₂ j = 0) (ε : ℝ) :
    poleValue (RHTower.dirichletConv f₁ f₂) (J₁ * J₂) ε =
      poleValue f₁ J₁ ε * poleValue f₂ J₂ ε := by
  simp only [poleValue, sum_mul_sum, ← sum_product']
  have hmaps : ∀ p ∈ Icc 1 J₁ ×ˢ Icc 1 J₂, p.1 * p.2 ∈ Icc 1 (J₁ * J₂) := by
    intro p hp
    rw [mem_product, mem_Icc, mem_Icc] at hp
    rw [mem_Icc]
    exact ⟨Nat.mul_pos hp.1.1 hp.2.1, Nat.mul_le_mul hp.1.2 hp.2.2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun n hn => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hn_ne : n ≠ 0 := by omega
  rw [RHTower.dirichletConv, sum_mul]
  have hbij : ∑ p ∈ (Icc 1 J₁ ×ˢ Icc 1 J₂).filter (fun p => p.1 * p.2 = n),
      f₁ p.1 * (p.1 : ℝ) ^ (-(1 - ε)) * (f₂ p.2 * (p.2 : ℝ) ^ (-(1 - ε))) =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ J₁ ∧ n / d ≤ J₂),
        f₁ d * f₂ (n / d) * (n : ℝ) ^ (-(1 - ε)) := by
    refine sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisors] at hp ⊢
      have hdvd : p.1 ∣ n := ⟨p.2, hp.2.symm⟩
      have hdiv : n / p.1 = p.2 := by
        rw [← hp.2, Nat.mul_div_right p.2 hp.1.1.1]
      exact ⟨⟨hdvd, hn_ne⟩, hp.1.1.2, hdiv.symm ▸ hp.1.2.2⟩
    · intro p₁ hp₁ p₂ hp₂ h1
      simp only [mem_filter, mem_product, mem_Icc] at hp₁ hp₂
      ext
      · exact h1
      · have hp₁0 : 0 < p₁.1 := hp₁.1.1.1
        apply Nat.eq_of_mul_eq_mul_left hp₁0
        rw [hp₁.2, h1, hp₂.2]
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      refine ⟨(d, n / d), ?_, rfl⟩
      simp only [mem_filter, mem_product, mem_Icc]
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd.1)
      have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn1 hd.1.1) hd1
      exact ⟨⟨⟨hd1, hd.2.1⟩, ⟨hq1, hd.2.2⟩⟩, Nat.mul_div_cancel' hd.1.1⟩
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc] at hp
      have hdiv : n / p.1 = p.2 := by rw [← hp.2, Nat.mul_div_right p.2 hp.1.1.1]
      have hp10 : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg p.1
      have hp20 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg p.2
      have hpow : (n : ℝ) ^ (-(1 - ε)) = (p.1 : ℝ) ^ (-(1 - ε)) * (p.2 : ℝ) ^ (-(1 - ε)) := by
        rw [← hp.2, Nat.cast_mul, Real.mul_rpow hp10 hp20]
      rw [hdiv, hpow]
      ring
  rw [hbij]
  refine (sum_subset (filter_subset _ _) fun d hd hnot => ?_).symm
  rw [mem_filter] at hnot
  push Not at hnot
  have hcond := hnot hd
  by_cases hdJ : d ≤ J₁
  · have hqJ : J₂ < n / d := hcond hdJ
    rw [hf₂ (n / d) hqJ, mul_zero, zero_mul]
  · rw [hf₁ d (not_le.mp hdJ), zero_mul, zero_mul]

/-- **All-order Binomial Leibniz Law for `poleLogMoment` under Dirichlet Convolution.**
For `k₁` supported on `[1, J₁]` and `k₂` supported on `[1, J₂]`,
`poleLogMoment (k₁ ⋆ k₂) (J₁ * J₂) ε m = Σ_{i ≤ m} C(m, i) poleLogMoment k₁ J₁ ε i · poleLogMoment k₂ J₂ ε (m - i)`. -/
theorem poleLogMoment_dirichletConv {k₁ k₂ : ℕ → ℝ} {J₁ J₂ : ℕ}
    (hk₁ : ∀ j, J₁ < j → k₁ j = 0) (hk₂ : ∀ j, J₂ < j → k₂ j = 0) (ε : ℝ) (m : ℕ) :
    poleLogMoment (RHTower.dirichletConv k₁ k₂) (J₁ * J₂) ε m =
      ∑ i ∈ range (m + 1),
        (m.choose i : ℝ) * poleLogMoment k₁ J₁ ε i * poleLogMoment k₂ J₂ ε (m - i) := by
  rw [poleLogMoment_eq_poleValue_logPowWeight, poleValue]
  have hterm : ∀ j ∈ Icc 1 (J₁ * J₂),
      logPowWeight (RHTower.dirichletConv k₁ k₂) m j * (j : ℝ) ^ (-(1 - ε)) =
        ∑ i ∈ range (m + 1),
          (m.choose i : ℝ) *
            (RHTower.dirichletConv (logPowWeight k₁ i) (logPowWeight k₂ (m - i)) j *
              (j : ℝ) ^ (-(1 - ε))) := by
    intro j _
    rw [logPowWeight_dirichletConv, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum, ← poleValue,
    poleValue_dirichletConv (logPowWeight_support hk₁ i) (logPowWeight_support hk₂ (m - i)) ε,
    ← poleLogMoment_eq_poleValue_logPowWeight, ← poleLogMoment_eq_poleValue_logPowWeight, mul_assoc]

/-- **Pole-Vanishing Index Additivity (Lower Moments Vanish).**
If `k₁` vanishes to order `r₁` at `1 - ε` (`∀ i < r₁, poleLogMoment k₁ J₁ ε i = 0`) and `k₂`
vanishes to order `r₂` (`∀ j < r₂, poleLogMoment k₂ J₂ ε j = 0`), then `k₁ ⋆ k₂` vanishes to
order `r₁ + r₂`: `∀ m < r₁ + r₂, poleLogMoment (k₁ ⋆ k₂) (J₁ * J₂) ε m = 0`. -/
theorem poleLogMoment_dirichletConv_eq_zero_of_lt {k₁ k₂ : ℕ → ℝ} {J₁ J₂ r₁ r₂ : ℕ}
    (hk₁ : ∀ j, J₁ < j → k₁ j = 0) (hk₂ : ∀ j, J₂ < j → k₂ j = 0) {ε : ℝ}
    (h1 : ∀ i < r₁, poleLogMoment k₁ J₁ ε i = 0)
    (h2 : ∀ j < r₂, poleLogMoment k₂ J₂ ε j = 0)
    {m : ℕ} (hm : m < r₁ + r₂) :
    poleLogMoment (RHTower.dirichletConv k₁ k₂) (J₁ * J₂) ε m = 0 := by
  rw [poleLogMoment_dirichletConv hk₁ hk₂ ε m]
  refine sum_eq_zero fun i hi => ?_
  rw [mem_range] at hi
  by_cases hi1 : i < r₁
  · rw [h1 i hi1, mul_zero, zero_mul]
  · have hi2 : m - i < r₂ := by omega
    rw [h2 (m - i) hi2, mul_zero]

/-- **Pole-Vanishing Index Additivity (Leading Moment Formula).**
If `k₁` vanishes to order `r₁` and `k₂` vanishes to order `r₂` at `1 - ε`, then at order `r₁ + r₂`:
`poleLogMoment (k₁ ⋆ k₂) (J₁ * J₂) ε (r₁ + r₂) = C(r₁ + r₂, r₁) · poleLogMoment k₁ J₁ ε r₁ · poleLogMoment k₂ J₂ ε r₂`. -/
theorem poleLogMoment_dirichletConv_add {k₁ k₂ : ℕ → ℝ} {J₁ J₂ r₁ r₂ : ℕ}
    (hk₁ : ∀ j, J₁ < j → k₁ j = 0) (hk₂ : ∀ j, J₂ < j → k₂ j = 0) {ε : ℝ}
    (h1 : ∀ i < r₁, poleLogMoment k₁ J₁ ε i = 0)
    (h2 : ∀ j < r₂, poleLogMoment k₂ J₂ ε j = 0) :
    poleLogMoment (RHTower.dirichletConv k₁ k₂) (J₁ * J₂) ε (r₁ + r₂) =
      ((r₁ + r₂).choose r₁ : ℝ) *
        poleLogMoment k₁ J₁ ε r₁ * poleLogMoment k₂ J₂ ε r₂ := by
  rw [poleLogMoment_dirichletConv hk₁ hk₂ ε (r₁ + r₂),
    sum_eq_single r₁]
  · rw [Nat.add_sub_cancel_left]
  · intro i hi hne
    rw [mem_range] at hi
    by_cases hi1 : i < r₁
    · rw [h1 i hi1, mul_zero, zero_mul]
    · have hi2 : r₁ + r₂ - i < r₂ := by omega
      rw [h2 (r₁ + r₂ - i) hi2, mul_zero]
  · intro hnot
    exfalso
    exact hnot (mem_range.mpr (by omega))

/-- **Exact Additivity of Pole Vanishing Order:** if `k₁` has exact vanishing order `r₁` and `k₂`
has exact vanishing order `r₂`, then `k₁ ⋆ k₂` has exact vanishing order `r₁ + r₂`. -/
theorem poleLogMoment_dirichletConv_ne_zero {k₁ k₂ : ℕ → ℝ} {J₁ J₂ r₁ r₂ : ℕ}
    (hk₁ : ∀ j, J₁ < j → k₁ j = 0) (hk₂ : ∀ j, J₂ < j → k₂ j = 0) {ε : ℝ}
    (h1 : ∀ i < r₁, poleLogMoment k₁ J₁ ε i = 0)
    (h2 : ∀ j < r₂, poleLogMoment k₂ J₂ ε j = 0)
    (h1_ne : poleLogMoment k₁ J₁ ε r₁ ≠ 0)
    (h2_ne : poleLogMoment k₂ J₂ ε r₂ ≠ 0) :
    poleLogMoment (RHTower.dirichletConv k₁ k₂) (J₁ * J₂) ε (r₁ + r₂) ≠ 0 := by
  rw [poleLogMoment_dirichletConv_add hk₁ hk₂ h1 h2]
  have hch : ((r₁ + r₂).choose r₁ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right r₁ r₂)).ne'
  exact mul_ne_zero (mul_ne_zero hch h1_ne) h2_ne

/-! ### The All-Order Iterated Fermi Kernel Hierarchy `(δ_1 - 2^{1 - ε} δ_2)^{⋆ r}` -/

/-- The `r`-fold iterated Fermi kernel `(δ_1 - 2^{1 - ε} δ_2)^{⋆ r}`. -/
def iteratedFermiKernel (ε : ℝ) : ℕ → ℕ → ℝ
  | 0 => unitMass
  | r + 1 => RHTower.dirichletConv (iteratedFermiKernel ε r) (fermiKernel ε)

@[simp]
theorem iteratedFermiKernel_zero (ε : ℝ) :
    iteratedFermiKernel ε 0 = unitMass := rfl

@[simp]
theorem iteratedFermiKernel_succ (ε : ℝ) (r : ℕ) :
    iteratedFermiKernel ε (r + 1) =
      RHTower.dirichletConv (iteratedFermiKernel ε r) (fermiKernel ε) := rfl

theorem iteratedFermiKernel_support (ε : ℝ) :
    ∀ r j : ℕ, 2 ^ r < j → iteratedFermiKernel ε r j = 0
  | 0, j, hj => by
    simp [unitMass, show j ≠ 1 by omega]
  | r + 1, j, hj => by
    rw [iteratedFermiKernel_succ]
    rw [pow_succ] at hj
    exact dirichletConv_support_mul (iteratedFermiKernel_support ε r)
      (fermiKernel_support ε) j hj

/-- All logarithmic moments of `iteratedFermiKernel ε r` below order `r` vanish, and the `r`-th
logarithmic moment equals `r! (-log 2)^r`. -/
theorem poleLogMoment_iteratedFermiKernel (ε : ℝ) :
    ∀ r : ℕ,
      (∀ m < r, poleLogMoment (iteratedFermiKernel ε r) (2 ^ r) ε m = 0) ∧
        poleLogMoment (iteratedFermiKernel ε r) (2 ^ r) ε r =
          (r.factorial : ℝ) * (-Real.log 2) ^ r
  | 0 => by
    refine ⟨fun m hm => by omega, ?_⟩
    simp [poleLogMoment, unitMass]
  | r + 1 => by
    obtain ⟨ih_lt, ih_eq⟩ := poleLogMoment_iteratedFermiKernel ε r
    have hf0 : ∀ j < 1, poleLogMoment (fermiKernel ε) 2 ε j = 0 := by
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [poleLogMoment_zero]
      exact poleValue_fermiKernel ε
    have hf1 : poleLogMoment (fermiKernel ε) 2 ε 1 = -Real.log 2 := by
      rw [poleLogMoment_one]
      exact poleSlope_fermiKernel ε
    refine ⟨fun m hm => ?_, ?_⟩
    · rw [iteratedFermiKernel_succ, pow_succ]
      exact poleLogMoment_dirichletConv_eq_zero_of_lt
        (iteratedFermiKernel_support ε r) (fermiKernel_support ε) ih_lt hf0 hm
    · rw [iteratedFermiKernel_succ, pow_succ,
        poleLogMoment_dirichletConv_add (iteratedFermiKernel_support ε r)
          (fermiKernel_support ε) ih_lt hf0,
        ih_eq, hf1, Nat.choose_succ_self_right, Nat.factorial_succ, pow_succ]
      push_cast
      ring

theorem poleLogMoment_iteratedFermiKernel_eq_zero_of_lt (ε : ℝ) {r m : ℕ} (hm : m < r) :
    poleLogMoment (iteratedFermiKernel ε r) (2 ^ r) ε m = 0 :=
  (poleLogMoment_iteratedFermiKernel ε r).1 m hm

theorem poleLogMoment_iteratedFermiKernel_eq (ε : ℝ) (r : ℕ) :
    poleLogMoment (iteratedFermiKernel ε r) (2 ^ r) ε r =
      (r.factorial : ℝ) * (-Real.log 2) ^ r :=
  (poleLogMoment_iteratedFermiKernel ε r).2

/-- **The `r`-th iterated Fermi kernel `(δ_1 - 2^{1 - ε} δ_2)^{⋆ r}` has exact pole vanishing order
`r`: its `r`-th logarithmic pole moment is strictly non-zero.** -/
theorem poleLogMoment_iteratedFermiKernel_ne_zero (ε : ℝ) (r : ℕ) :
    poleLogMoment (iteratedFermiKernel ε r) (2 ^ r) ε r ≠ 0 := by
  rw [poleLogMoment_iteratedFermiKernel_eq]
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  have hlog : -Real.log 2 ≠ 0 := neg_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  exact mul_ne_zero hfac (pow_ne_zero r hlog)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
