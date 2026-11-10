import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherLatticeError

/-!
# Physical-scale remainders for every Gaussian moment

The normalized moment of order `r` has complete lattice error
`O(b^(2r-1) t^(2r) X^(1-σ-2r))`. The constant depends only on `r` and `σ`.
-/

open Complex MeasureTheory Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The continuous pole of the normalized Gaussian moment of order `r`. -/
def gaussianHigherMomentPole (r : ℕ) (s ε : ℂ) (t : ℝ) : ℂ :=
  (ε / (t : ℂ)) ^ r * ((1 / 2 : ℂ) * Complex.Gamma ((((2 * r : ℕ) : ℂ) - s + 1) / 2) *
    ε ^ (-(((2 * r : ℕ) : ℂ) - s + 1) / 2))

/-- The dimensionless constant in the damping-power remainder. -/
def gaussianHigherMomentLatticeConstant (r : ℕ) (σ : ℝ) : ℝ :=
  4 ^ r * |((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ) *
    gaussianMellinJetConstant (2 * r) ((2 * r : ℕ) - σ)

theorem gaussianHigherMomentLatticeConstant_nonneg (r : ℕ) {σ : ℝ}
    (hσ : σ < 1) : 0 ≤ gaussianHigherMomentLatticeConstant r σ := by
  have h := gaussianMellinJetConstant_nonneg (2 * r)
    (show ((2 * r : ℕ) : ℝ) - 1 < (2 * r : ℕ) - σ by linarith)
  unfold gaussianHigherMomentLatticeConstant
  positivity

/-- Higher moment normalization preserves the full high-order lattice saving. -/
theorem norm_tsum_gaussianHigherMoment_sub_pole_le (r : ℕ) (hr : r ≠ 0)
    {σ t : ℝ} {ε : ℂ} (hσ : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) ^ r * (∑' n : ℕ,
        gaussianMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t‖ ≤
      gaussianHigherMomentLatticeConstant r σ * b ^ (2 * r - 1) * t ^ (2 * r) *
        ε.re ^ (((2 * r : ℕ) + σ - 1) / 2) := by
  let w : ℂ := ((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)
  have hwre : w.re = ((2 * r : ℕ) : ℝ) - σ := by simp [w]
  have hw : ((2 * r : ℕ) : ℝ) - 1 < w.re := by rw [hwre]; linarith
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have him : |w.im| ≤ t := by simp [w, abs_of_pos ht0]
  have hV := gaussianMellinJetVariation_le (2 * r) hw hε ht him hsector
  rw [hwre, show (((2 * r : ℕ) : ℝ) - ((2 * r : ℕ) - σ) - 1) / 2 =
    (σ - 1) / 2 by ring] at hV
  have hC := gaussianMellinJetConstant_nonneg (2 * r) hw
  rw [hwre] at hC
  have hbase := norm_tsum_gaussianMellinWeight_sub_main_higher_le r hr hw hε hb
  have hscale : ‖(ε / (t : ℂ)) ^ r‖ ≤ (4 * ε.re) ^ r := by
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr hsector
  have hright : 0 ≤ b ^ (2 * r - 1) * |((bernoulli (2 * r) : ℚ) : ℝ)| /
      ((2 * r).factorial : ℝ) := by positivity
  have hcombined := mul_le_mul hscale
    (hbase.trans (mul_le_mul_of_nonneg_left hV hright)) (norm_nonneg _) (by positivity)
  rw [← norm_mul] at hcombined
  have heq : (ε / (t : ℂ)) ^ r *
      ((∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) * ε ^ (-(w + 1) / 2))) =
      (ε / (t : ℂ)) ^ r * (∑' n : ℕ, gaussianMellinWeight w ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t := by
    unfold gaussianHigherMomentPole
    dsimp only [w]
    ring
  rw [heq] at hcombined
  apply hcombined.trans_eq
  have hpow : ε.re ^ r * ε.re ^ ((σ - 1) / 2) =
      ε.re ^ (((2 * r : ℕ) + σ - 1) / 2) := by
    rw [← Real.rpow_natCast ε.re r, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  rw [mul_pow]
  unfold gaussianHigherMomentLatticeConstant
  calc
    _ = (4 ^ r * |((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ) *
        gaussianMellinJetConstant (2 * r) ((2 * r : ℕ) - σ)) *
        b ^ (2 * r - 1) * t ^ (2 * r) * (ε.re ^ r * ε.re ^ ((σ - 1) / 2)) := by ring
    _ = _ := by rw [hpow]

private theorem damping_power_eq_physical_scale {α X : ℝ} (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q : ℝ) : α ^ q = (2 : ℝ) ^ q * X ^ (-2 * q) := by
  have ha : α = 2 / X ^ 2 := (eq_div_iff (pow_ne_zero 2 hX.ne')).mpr hscale
  have hp : (X ^ 2) ^ q = X ^ (2 * q) := by
    rw [← Real.rpow_two X, ← Real.rpow_mul hX.le]
  rw [ha, Real.div_rpow (by norm_num) (sq_nonneg X), hp,
    show -2 * q = -(2 * q) by ring, Real.rpow_neg hX.le, div_eq_mul_inv]

/-- Every fixed moment order yields an additional power saving in the physical scale. -/
theorem norm_tsum_gaussianHigherMoment_sub_pole_physical_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) ^ r * (∑' n : ℕ,
        gaussianMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε (b * (n + 1))) -
      (b : ℂ)⁻¹ * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t‖ ≤
      (gaussianHigherMomentLatticeConstant r σ *
        (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
        b ^ (2 * r - 1) * t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) := by
  apply (norm_tsum_gaussianHigherMoment_sub_pole_le r hr hσ ht hε hsector hb).trans_eq
  rw [damping_power_eq_physical_scale hX hscale,
    show -2 * (((2 * r : ℕ) + σ - 1) / 2) = 1 - σ - (2 * r : ℕ) by ring]
  ring

#print axioms norm_tsum_gaussianHigherMoment_sub_pole_le
#print axioms norm_tsum_gaussianHigherMoment_sub_pole_physical_le

end GaloisForLFunctions.ExceptionalLayerTheory
