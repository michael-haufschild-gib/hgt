import GaloisForLFunctions.RHTower.SmoothAFEReflectedTruncatedGaussianTransfer
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound



open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- The complete character-weighted reflected-primal Gaussian carrier. -/
def steinhausFullReflectedPrimalCarrier (d tau : ℝ) (N : ℕ) (ω : SteinhausModel.Omega) : ℂ :=
  zetaChi (rightDisplacedLinePt d tau) *
    steinhausFullGaussianCofactor (rightDisplacedLinePt d tau) N ω

/-- The full carrier uses exactly the original reflected-AFE coefficients. -/
theorem steinhausFullReflectedPrimalCarrier_eq_tsum (d tau : ℝ) (N : ℕ)
    (ω : SteinhausModel.Omega) :
    steinhausFullReflectedPrimalCarrier d tau N ω =
      ∑' n : ℕ, smoothAFEZetaRightReflectedPrimalCoefficient d tau N n * SteinhausModel.X (n + 1) ω := by
  unfold steinhausFullReflectedPrimalCarrier steinhausFullGaussianCofactor
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [smoothAFEZetaRightReflectedPrimalCoefficient, Nat.cast_add, Nat.cast_one]
  ring

/-- The finite positive-index carrier is the literal truncation of the same Gaussian source. -/
theorem reflectedPrimalWindowCarrier_eq_chi_mul_truncated (d tau : ℝ) (N L : ℕ)
    (ω : SteinhausModel.Omega) :
    (∑ n ∈ Icc 1 L, smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N n *
      SteinhausModel.X n ω) =
      zetaChi (rightDisplacedLinePt d tau) *
        truncatedFullGaussianCofactor (rightDisplacedLinePt d tau) N L ω := by
  rw [truncatedFullGaussianCofactor_eq_Icc, mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ (mem_Icc.mp hn).1, one_mul]
  ring

/-- At square smoothing scale and cubic polynomial cutoff, the omitted actual reflected
primal tail is smaller than every prescribed power, uniformly in phase and height above
that scale. This is a deterministic tail bound, with no rare-event subtraction. -/
theorem exists_fullReflectedPrimal_cubic_tail_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ tau : ℝ, ((n ^ 2 : ℕ) : ℝ) ≤ tau →
      ∀ ω : SteinhausModel.Omega,
      ‖steinhausFullReflectedPrimalCarrier d tau (n ^ 2) ω -
        ∑ m ∈ Icc 1 (n ^ 3),
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 (n ^ 2) m *
            SteinhausModel.X m ω‖ ≤ C * (n : ℝ) ^ (-q) := by
  let A : ℝ := q + d + 2
  have hA : 0 < A := by dsimp only [A]; linarith
  have hden : 0 < A - (1 / 2 + d) := by dsimp only [A]; linarith
  obtain ⟨K, hK, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  obtain ⟨C, hC, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  refine ⟨C * K / (A - (1 / 2 + d)), by positivity, ?_⟩
  intro n hn tau htau ω
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ 2 : ℕ) : ℝ) := by positivity
  have hNmax : ((n ^ 2 : ℕ) : ℝ) ≤ max 1 |tau| :=
    htau.trans ((le_abs_self _).trans (le_max_right _ _))
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ C / (((n ^ 2 : ℕ) : ℝ) ^ d) :=
    (hchi tau).trans (div_le_div_of_nonneg_left hC (by positivity)
      (Real.rpow_le_rpow hN.le hNmax hd.le))
  have hsA : (rightDisplacedLinePt d tau).re < A := by
    rw [rightDisplacedLinePt_re]
    linarith
  have htrunc := htail (rightDisplacedLinePt d tau) ((n ^ 2 : ℕ) : ℝ) hN hsA (n ^ 3) (by have hpos : 0 < n ^ 3 := pow_pos hn 3; omega) ω
  change ‖steinhausFullGaussianCofactor (rightDisplacedLinePt d tau) ((n ^ 2 : ℕ) : ℝ) ω -
    truncatedFullGaussianCofactor (rightDisplacedLinePt d tau) ((n ^ 2 : ℕ) : ℝ) (n ^ 3) ω‖ ≤ _ at htrunc
  rw [rightDisplacedLinePt_re] at htrunc
  have hpower : (((n ^ 2 : ℕ) : ℝ) ^ (-d)) * (((n ^ 2 : ℕ) : ℝ) ^ A) *
      (((n ^ 3 : ℕ) : ℝ) ^ (1 / 2 + d - A)) = (n : ℝ) ^ (-q - 1 / 2) := by
    simp only [Nat.cast_pow]
    rw [← Real.rpow_natCast_mul hnR.le, ← Real.rpow_natCast_mul hnR.le,
      ← Real.rpow_natCast_mul hnR.le, ← Real.rpow_add hnR, ← Real.rpow_add hnR]
    congr 1
    dsimp only [A]
    norm_num
    ring
  rw [reflectedPrimalWindowCarrier_eq_chi_mul_truncated, steinhausFullReflectedPrimalCarrier,
    ← mul_sub, norm_mul]
  calc
    _ ≤ (C / (((n ^ 2 : ℕ) : ℝ) ^ d)) *
        (K * (((n ^ 2 : ℕ) : ℝ) ^ A) *
          ((((n ^ 3 : ℕ) : ℝ) ^ (1 / 2 + d - A)) / (A - (1 / 2 + d)))) :=
      mul_le_mul hchiN htrunc (norm_nonneg _) (by positivity)
    _ = (C * K / (A - (1 / 2 + d))) *
        ((((n ^ 2 : ℕ) : ℝ) ^ (-d)) * (((n ^ 2 : ℕ) : ℝ) ^ A) *
          (((n ^ 3 : ℕ) : ℝ) ^ (1 / 2 + d - A))) := by
      rw [Real.rpow_neg hN.le]
      ring
    _ = (C * K / (A - (1 / 2 + d))) * (n : ℝ) ^ (-q - 1 / 2) := by rw [hpower]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)) (by positivity)

end RHTower
