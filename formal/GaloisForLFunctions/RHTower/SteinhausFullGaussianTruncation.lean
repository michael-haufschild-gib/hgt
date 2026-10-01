import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorModes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology Finset
noncomputable section
namespace RHTower

/-- The literal positive-index Gaussian cofactor truncated after L terms. -/
def truncatedFullGaussianCofactor (s : ℂ) (R : ℝ) (L : ℕ) (ω : SteinhausModel.Omega) : ℂ :=
  ∑ n ∈ range L, SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
    smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)

/-- Reindex the literal finite cofactor in the arithmetic interval convention. -/
theorem truncatedFullGaussianCofactor_eq_Icc (s : ℂ) (R : ℝ) (L : ℕ)
    (ω : SteinhausModel.Omega) :
    truncatedFullGaussianCofactor s R L ω =
      ∑ n ∈ Icc 1 L, SteinhausModel.X n ω * (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / R) := by
  unfold truncatedFullGaussianCofactor
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  apply sum_congr rfl
  intro n _
  rw [Nat.add_comm]

/-- The actual truncations converge to the full Gaussian cofactor uniformly in all phases
and in every bounded positive range of smoothing scales. -/
theorem eventually_truncatedFullGaussianCofactor_uniform_error
    (s : ℂ) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ R : ℝ, 0 < R → R ≤ U → ∀ ω : SteinhausModel.Omega,
      ‖truncatedFullGaussianCofactor s R L ω - steinhausFullGaussianCofactor s R ω‖ < ε := by
  let A : ℝ := |s.re| + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hsA : s.re < A := by dsimp only [A]; linarith [le_abs_self s.re]
  obtain ⟨C, hC, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_head_le hA
  have hpow : Tendsto (fun L : ℕ => (L : ℝ) ^ (s.re - A)) atTop (𝓝 0) := by
    simpa only [show -(A - s.re) = s.re - A by ring, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hsA)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop)
  have hlim : Tendsto (fun L : ℕ =>
      C * U ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re))) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using (hpow.div_const (A - s.re)).const_mul (C * U ^ A)
  filter_upwards [hlim.eventually (Iio_mem_nhds hε), eventually_ge_atTop 1] with L hL hL1
  intro R hR hRU ω
  rw [norm_sub_rev]
  calc
    _ ≤ C * R ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) := htail s R hR hsA L hL1 ω
    _ ≤ C * U ^ A * ((L : ℝ) ^ (s.re - A) / (A - s.re)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRU hA.le) hC)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sub_pos.mpr hsA).le)
    _ < ε := hL

/-- Apply the exact coherent normalization to a literal finite cofactor. -/
def relativeTruncatedFullGaussianCofactorMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ)
    (R : ℝ) (L : ℕ) (ω : SteinhausModel.Omega) : Fin J → ℂ :=
  fun j => A⁻¹ * ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) *
    (truncatedFullGaussianCofactor (s j) R L ω * (R : ℂ) ^ (-s j)))

/-- Coherent normalized finite channels approximate their full Gaussian responses uniformly
in phase and every bounded real scale interval away from zero. -/
theorem eventually_relativeTruncatedFullGaussianCofactorMode_uniform_error
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 ≤ (s j).re)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ R : ℝ, 1 ≤ R → R ≤ U → ∀ ω : SteinhausModel.Omega,
      ‖relativeTruncatedFullGaussianCofactorMode s t A R L ω -
        relativeFullGaussianCofactorMode s t A R ω‖ < ε := by
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hlimits : ∀ᶠ L : ℕ in atTop, ∀ j : Fin J, ∀ R : ℝ, 0 < R → R ≤ U →
      ∀ ω : SteinhausModel.Omega,
        ‖truncatedFullGaussianCofactor (s j) R L ω - steinhausFullGaussianCofactor (s j) R ω‖ <
          ε * ‖A‖ :=
    Filter.eventually_all.mpr (fun j =>
      eventually_truncatedFullGaussianCofactor_uniform_error (s j) U (mul_pos hε hAnorm))
  filter_upwards [hlimits] with L hL
  intro R hR hRU ω
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have htwist : ‖(R : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR0]
    simp
  apply (pi_norm_lt_iff hε).mpr
  intro j
  have hd := hL j R hR0 hRU ω
  have heq : relativeTruncatedFullGaussianCofactorMode s t A R L ω j -
      relativeFullGaussianCofactorMode s t A R ω j =
      A⁻¹ * ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) *
        ((truncatedFullGaussianCofactor (s j) R L ω - steinhausFullGaussianCofactor (s j) R ω) *
          (R : ℂ) ^ (-s j))) := by
    simp only [relativeTruncatedFullGaussianCofactorMode, relativeFullGaussianCofactorMode,
      fullGaussianCofactorNodeVector, Pi.smul_apply, smul_eq_mul]
    ring
  change ‖relativeTruncatedFullGaussianCofactorMode s t A R L ω j -
    relativeFullGaussianCofactorMode s t A R ω j‖ < ε
  rw [heq, norm_mul, norm_mul, norm_mul, norm_inv, htwist, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hR0, Complex.neg_re]
  calc
    _ ≤ ‖A‖⁻¹ * ‖truncatedFullGaussianCofactor (s j) R L ω -
        steinhausFullGaussianCofactor (s j) R ω‖ :=
      mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hR
          (neg_nonpos.mpr (hs j)))) (inv_nonneg.mpr hAnorm.le)
    _ < ‖A‖⁻¹ * (ε * ‖A‖) := mul_lt_mul_of_pos_left hd (inv_pos.mpr hAnorm)
    _ = ε := by field_simp [hAnorm.ne']

end RHTower
