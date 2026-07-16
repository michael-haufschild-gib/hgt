import GaloisForLFunctions.HTGeometry.CentralBinomialDiagonalKernel
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Half-order asymptotic for a central-binomial geometric convolution

The diagonal square-root kernel coefficient is a convolution of two normalized central-binomial
sequences.  This file proves its sharp `n⁻¹/²` asymptotic by dominated convergence.
-/

open Filter Topology
open scoped BigOperators Nat Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every finite Wallis product is at least one. -/
lemma one_le_Wallis_W (n : ℕ) : 1 ≤ Real.Wallis.W n := by
  induction n with
  | zero => simp [Real.Wallis.W]
  | succ n ih =>
      rw [Real.Wallis.W_succ]
      have hden : 0 < ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by positivity
      have hfactor : 1 ≤
          (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1) *
            ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) := by
        rw [div_mul_div_comm]
        exact (one_le_div hden).2 (by nlinarith)
      exact ih.trans (le_mul_of_one_le_right (Real.Wallis.W_pos n).le hfactor)

/-- Global Wallis envelope for the normalized central-binomial coefficient. -/
lemma normalizedCentralBinom_sq_le_inv_succ (n : ℕ) :
    normalizedCentralBinom n ^ 2 ≤ 1 / (n + 1 : ℝ) := by
  have hid := wallis_mul_normalizedCentralBinom_sq n
  have hfirst : normalizedCentralBinom n ^ 2 ≤
      Real.Wallis.W n * normalizedCentralBinom n ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) (one_le_Wallis_W n)
  rw [hid] at hfirst
  calc
    normalizedCentralBinom n ^ 2 ≤ 1 / (2 * n + 1 : ℝ) := hfirst
    _ ≤ 1 / (n + 1 : ℝ) := by
      gcongr
      exact_mod_cast (show n ≤ 2 * n by omega)

/-- Uniform square-root envelope: `sqrt(n+1) c_n ≤ 1`. -/
lemma sqrt_succ_mul_normalizedCentralBinom_le_one (n : ℕ) :
    Real.sqrt (n + 1 : ℝ) * normalizedCentralBinom n ≤ 1 := by
  have hc := normalizedCentralBinom_sq_le_inv_succ n
  have hsqrt : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsq : (Real.sqrt (n + 1 : ℝ) * normalizedCentralBinom n) ^ 2 ≤ 1 := by
    rw [mul_pow, hsqrt]
    have hpos : 0 < (n + 1 : ℝ) := by positivity
    simpa [mul_comm] using (le_div_iff₀ hpos).mp hc
  have hnonneg : 0 ≤ Real.sqrt (n + 1 : ℝ) * normalizedCentralBinom n :=
    mul_nonneg (Real.sqrt_nonneg _) (normalizedCentralBinom_nonneg n)
  nlinarith [sq_nonneg
    (Real.sqrt (n + 1 : ℝ) * normalizedCentralBinom n + 1)]

/-- The normalized central-binomial coefficient itself lies in `[0,1]`. -/
lemma normalizedCentralBinom_le_one (n : ℕ) : normalizedCentralBinom n ≤ 1 := by
  rw [normalizedCentralBinom]
  exact (div_le_one (by positivity : (0 : ℝ) < 4 ^ n)).2 (by
    exact_mod_cast Nat.centralBinom_le_four_pow n)

/-- A fixed backward shift does not change the half-order central-binomial limit. -/
lemma tendsto_sqrtNat_mul_normalizedCentralBinom_sub (j : ℕ) :
    Tendsto
      (fun n : ℕ => Real.sqrt n * normalizedCentralBinom (n - j))
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + (j : ℝ)))
      atTop (nhds 1) := tendsto_natCast_div_add_atTop (j : ℝ)
  have hinv := hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hfrac : Tendsto (fun n : ℕ => ((n + j : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have hinv' : Tendsto (fun n : ℕ =>
        ((n : ℝ) / ((n : ℝ) + (j : ℝ)))⁻¹) atTop (nhds 1) := by
      simpa only [inv_one] using hinv
    apply hinv'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Nat.cast_add]
    field_simp [hn0]
  have hsqrtFrac : Tendsto
      (fun n : ℕ => Real.sqrt (((n + j : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds 1) := by
    simpa using hfrac.sqrt
  have hratio : Tendsto
      (fun n : ℕ => Real.sqrt (n + j : ℝ) / Real.sqrt (n : ℝ))
      atTop (nhds 1) := by
    apply hsqrtFrac.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.sqrt_div (by positivity : 0 ≤ ((n + j : ℕ) : ℝ))]
    simp only [Nat.cast_add]
  have hproduct := hratio.mul tendsto_sqrtNat_mul_normalizedCentralBinom
  have hplus : Tendsto
      (fun n : ℕ => Real.sqrt (n + j : ℝ) * normalizedCentralBinom n)
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
    have hproduct' : Tendsto
        (fun n : ℕ =>
          (Real.sqrt (n + j : ℝ) / Real.sqrt (n : ℝ)) *
            (Real.sqrt n * normalizedCentralBinom n))
        atTop (nhds (1 / Real.sqrt Real.pi)) := by
      simpa only [one_mul] using hproduct
    apply hproduct'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    field_simp [hsqrt0]
  have hshift := hplus.comp (tendsto_sub_atTop_nat j)
  apply hshift.congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  simp only [Function.comp_apply]
  rw [← Nat.cast_add, Nat.sub_add_cancel hn]

/-- The shifted half-order factor has a pointwise envelope depending only on the removed index. -/
lemma sqrtNat_mul_shifted_normalizedCentralBinom_le
    {n j : ℕ} (hj : j ≤ n) :
    Real.sqrt n * normalizedCentralBinom (n - j) ≤ Real.sqrt (j + 1 : ℝ) := by
  have hnat : n ≤ (j + 1) * (n - j + 1) := by
    calc
      n = (n - j) + j := (Nat.sub_add_cancel hj).symm
      _ ≤ (n - j) + j + (j * (n - j) + 1) := Nat.le_add_right _ _
      _ = (j + 1) * (n - j + 1) := by ring
  have hcast : (n : ℝ) ≤
      (j + 1 : ℝ) * (((n - j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hsqrt : Real.sqrt (n : ℝ) ≤
      Real.sqrt (j + 1 : ℝ) * Real.sqrt (((n - j + 1 : ℕ) : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (j + 1 : ℝ))]
    exact Real.sqrt_le_sqrt hcast
  calc
    Real.sqrt n * normalizedCentralBinom (n - j) ≤
        (Real.sqrt (j + 1 : ℝ) *
          Real.sqrt (((n - j + 1 : ℕ) : ℝ))) *
          normalizedCentralBinom (n - j) :=
      mul_le_mul_of_nonneg_right hsqrt (normalizedCentralBinom_nonneg _)
    _ = Real.sqrt (j + 1 : ℝ) *
        (Real.sqrt (((n - j + 1 : ℕ) : ℝ)) *
          normalizedCentralBinom (n - j)) := by ring
    _ ≤ Real.sqrt (j + 1 : ℝ) * 1 := by
      have hcb : Real.sqrt (((n - j + 1 : ℕ) : ℝ)) *
          normalizedCentralBinom (n - j) ≤ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          sqrt_succ_mul_normalizedCentralBinom_le_one (n - j)
      exact mul_le_mul_of_nonneg_left hcb (Real.sqrt_nonneg _)
    _ = Real.sqrt (j + 1 : ℝ) := mul_one _

/-- The normalized geometric convolution appearing after division by the leading radius. -/
def normalizedCentralBinomialGeometricConvolution (q : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    normalizedCentralBinom j * q ^ j * normalizedCentralBinom (n - j)

/-- **Sharp half-order convolution asymptotic.** -/
theorem tendsto_sqrtNat_mul_normalizedCentralBinomialGeometricConvolution
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto
      (fun n : ℕ => Real.sqrt n * normalizedCentralBinomialGeometricConvolution q n)
      atTop
      (nhds ((1 / Real.sqrt Real.pi) * ((1 - q) ^ (-1 / 2 : ℝ)))) := by
  let F : ℕ → ℕ → ℝ := fun n j =>
    if j ≤ n then
      normalizedCentralBinom j * q ^ j *
        (Real.sqrt n * normalizedCentralBinom (n - j))
    else 0
  let G : ℕ → ℝ := fun j =>
    normalizedCentralBinom j * q ^ j * (1 / Real.sqrt Real.pi)
  let bound : ℕ → ℝ := fun j =>
    Real.sqrt (j + 1 : ℝ) * normalizedCentralBinom j * q ^ j
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hlinear : Summable (fun j : ℕ => (j + 1 : ℝ) * q ^ j) := by
    have hnat := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hqnorm
    have hgeo := summable_geometric_of_norm_lt_one hqnorm
    simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hnat.add hgeo
  have hbound : Summable bound := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (normalizedCentralBinom_nonneg j))
        (pow_nonneg hq0 j))
      (fun j => ?_) hlinear
    have hsqrt : Real.sqrt (j + 1 : ℝ) ≤ (j + 1 : ℝ) := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ (j + 1 : ℝ))
      have hj1 : 1 ≤ (j + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      nlinarith [Real.sqrt_nonneg (j + 1 : ℝ)]
    calc
      bound j ≤ (j + 1 : ℝ) * normalizedCentralBinom j * q ^ j := by
        dsimp only [bound]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsqrt (normalizedCentralBinom_nonneg j))
          (pow_nonneg hq0 j)
      _ ≤ (j + 1 : ℝ) * 1 * q ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (normalizedCentralBinom_le_one j) (by positivity))
          (pow_nonneg hq0 j)
      _ = (j + 1 : ℝ) * q ^ j := by ring
  have hpoint (j : ℕ) : Tendsto (fun n => F n j) atTop (nhds (G j)) := by
    have hshift := tendsto_sqrtNat_mul_normalizedCentralBinom_sub j
    have hmul : Tendsto
        (fun n : ℕ =>
          (normalizedCentralBinom j * q ^ j) *
            (Real.sqrt n * normalizedCentralBinom (n - j)))
        atTop (nhds (G j)) := by
      simpa only [G] using tendsto_const_nhds.mul hshift
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    simp only [F, if_pos hn]
  have hdominated : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, ‖F n j‖ ≤ bound j := by
    filter_upwards with n
    intro j
    by_cases hj : j ≤ n
    · have hshift := sqrtNat_mul_shifted_normalizedCentralBinom_le hj
      simp only [F, if_pos hj, Real.norm_eq_abs]
      rw [abs_of_nonneg]
      · dsimp only [bound]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hshift
            (mul_nonneg (normalizedCentralBinom_nonneg j) (pow_nonneg hq0 j)))
      · exact mul_nonneg
          (mul_nonneg (normalizedCentralBinom_nonneg j) (pow_nonneg hq0 j))
          (mul_nonneg (Real.sqrt_nonneg _) (normalizedCentralBinom_nonneg _))
    · simp only [F, if_neg hj, norm_zero]
      exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (normalizedCentralBinom_nonneg j))
        (pow_nonneg hq0 j)
  have hlimit := tendsto_tsum_of_dominated_convergence hbound hpoint hdominated
  have htsum (n : ℕ) :
      (∑' j : ℕ, F n j) =
        Real.sqrt n * normalizedCentralBinomialGeometricConvolution q n := by
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · rw [normalizedCentralBinomialGeometricConvolution, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      simp only [F, if_pos hjn]
      ring
    · intro j hj
      have hjn : ¬ j ≤ n := by
        intro hle
        exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [F, hjn]
  have hGsum : (∑' j : ℕ, G j) =
      (1 / Real.sqrt Real.pi) * ((1 - q) ^ (-1 / 2 : ℝ)) := by
    have hgf := normalizedCentralBinom_gf hq0 hq1
    have hscaled := hgf.mul_left (1 / Real.sqrt Real.pi)
    have hscaledG : HasSum G
        ((1 / Real.sqrt Real.pi) * ((1 - q) ^ (-1 / 2 : ℝ))) := by
      simpa only [G, one_div, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact hscaledG.tsum_eq
  rw [hGsum] at hlimit
  apply hlimit.congr'
  exact Eventually.of_forall htsum

/-- Factoring the leading characteristic radius reduces the diagonal kernel coefficient to the
normalized geometric convolution. -/
theorem centralBinomialDiagonalKernelCoefficient_eq_pow_mul_convolution
    {B D : ℝ} (hB : B ≠ 0) (n : ℕ) :
    centralBinomialDiagonalKernelCoefficient B D n =
      (B ^ 2) ^ n *
        normalizedCentralBinomialGeometricConvolution (D ^ 2 / B ^ 2) n := by
  rw [centralBinomialDiagonalKernelCoefficient,
    normalizedCentralBinomialGeometricConvolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : (B ^ 2) ^ n = (B ^ 2) ^ k * (B ^ 2) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [div_pow, hpow]
  field_simp [hB]

/-- **Sharp diagonal-kernel coefficient asymptotic.**  The exact leading exponential radius is
`B²`; after removing it, the coefficient has the universal half-order limit determined by the
transverse ratio `D²/B²`. -/
theorem tendsto_sqrtNat_mul_centralBinomialDiagonalKernelCoefficient_div_pow
    {B D : ℝ} (hB : 0 < B) (hD : |D| < B) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt n * centralBinomialDiagonalKernelCoefficient B D n / (B ^ 2) ^ n)
      atTop
      (nhds ((1 / Real.sqrt Real.pi) *
        ((1 - D ^ 2 / B ^ 2) ^ (-1 / 2 : ℝ)))) := by
  have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
  have hDinterval := abs_lt.mp hD
  have hDsq : D ^ 2 < B ^ 2 := by nlinarith
  have hq0 : 0 ≤ D ^ 2 / B ^ 2 := div_nonneg (sq_nonneg D) hBsq.le
  have hq1 : D ^ 2 / B ^ 2 < 1 := (div_lt_one hBsq).2 hDsq
  have hlimit :=
    tendsto_sqrtNat_mul_normalizedCentralBinomialGeometricConvolution hq0 hq1
  apply hlimit.congr'
  filter_upwards with n
  rw [centralBinomialDiagonalKernelCoefficient_eq_pow_mul_convolution hB.ne' n]
  field_simp [(pow_pos hBsq n).ne']

end

end GaloisForLFunctions.HTGeometry
