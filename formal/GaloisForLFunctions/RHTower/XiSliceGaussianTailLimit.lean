import GaloisForLFunctions.RHTower.XiSliceGaussianTailComparison
import GaloisForLFunctions.RHTower.XiDyadicBandReciprocalPhaseAmplification
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# A Gaussian limit for the actual distant Xi divisor

Remove all zero copies within distance `R` of a real center. Riemann--von Mangoldt gives
enough mass in the next dyadic band to make the normalized fourth moment vanish. The critical
strip aligns the quadratic sum with the positive reciprocal-square mass. The remaining
product, rescaled by the square root of that mass, therefore tends to `exp(z²)` uniformly on
every fixed complex disc, without a zero-spacing or critical-line assumption.
-/

open Filter Topology Complex
namespace RHTower
noncomputable section

private theorem norm_square_sub_norm_square (z : ℂ) :
    ‖z ^ 2 - ((‖z‖ ^ 2 : ℝ) : ℂ)‖ = 2 * |z.im| * ‖z‖ := by
  have h : z ^ 2 - ((‖z‖ ^ 2 : ℝ) : ℂ) = z * ((2 * z.im : ℝ) * I) := by
    rw [Complex.sq_norm]
    apply Complex.ext <;> simp only [pow_two, sub_re, sub_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, mul_one, add_zero,
      sub_zero, normSq_apply] <;> ring
  rw [h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one, abs_mul]
  norm_num
  ring

private theorem norm_inv_square_sub_norm (z : ℂ) :
    ‖(z ^ 2)⁻¹ - ((‖(z ^ 2)⁻¹‖ : ℝ) : ℂ)‖ =
      (2 * |z.im| / ‖z‖) * ‖(z ^ 2)⁻¹‖ := by
  rw [← inv_pow, norm_pow, norm_square_sub_norm_square, inv_im, abs_div, abs_neg,
    abs_of_nonneg (Complex.normSq_nonneg _), ← Complex.sq_norm, norm_inv]
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem norm_inv_square_phase_le (z : ℂ) {R : ℝ}
    (hR : 0 < R) (hd : R ≤ ‖z‖) (hi : 2 * |z.im| ≤ 1) :
    ‖(z ^ 2)⁻¹ - ((‖(z ^ 2)⁻¹‖ : ℝ) : ℂ)‖ ≤ ‖(z ^ 2)⁻¹‖ / R := by
  rw [norm_inv_square_sub_norm, div_eq_mul_inv]
  have hd0 : 0 < ‖z‖ := hR.trans_le hd
  have hcoef : 2 * |z.im| / ‖z‖ ≤ R⁻¹ :=
    (div_le_div_of_nonneg_right hi hd0.le).trans (by
      simpa only [one_div] using one_div_le_one_div_of_le hR hd)
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((z ^ 2)⁻¹))

/-- All multiplicity copies within distance `R` of the real slice center. -/
def xiSliceGaussianRadiusHead (t R : ℝ) : Finset XiZeroCopy := by
  classical
  exact ((finite_xiZeroCopy_norm_le (|R| + |t|)).toFinset).filter
    (fun q => ‖xiSpectralPoint q - (t : ℂ)‖ ≤ R)

theorem mem_xiSliceGaussianRadiusHead (t R : ℝ) (q : XiZeroCopy) :
    q ∈ xiSliceGaussianRadiusHead t R ↔ ‖xiSpectralPoint q - (t : ℂ)‖ ≤ R := by
  classical
  rw [xiSliceGaussianRadiusHead, Finset.mem_filter, Set.Finite.mem_toFinset]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  calc
    ‖xiSpectralPoint q‖ = ‖(xiSpectralPoint q - (t : ℂ)) + (t : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖xiSpectralPoint q - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
    _ ≤ |R| + |t| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (h.trans (le_abs_self R)) le_rfl

private theorem gaussianSpectral_im_abs_le_half (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  nlinarith only [xiSpectralPoint_im_sq_lt_quarter q,
    sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]

private theorem gaussianBand_distance_bounds (t : ℝ) {R : ℝ}
    (hR : 2 * |t| + 1 ≤ R) {q : XiZeroCopy} (hq : q ∈ xiCopiesBand (2 * R) (4 * R)) :
    R < ‖xiSpectralPoint q - (t : ℂ)‖ ∧ ‖xiSpectralPoint q - (t : ℂ)‖ ≤ 5 * R := by
  have hmem := mem_xiCopiesBand.mp hq
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have hlow : |(q.1 : ℂ).im| ≤ ‖xiSpectralPoint q - (t : ℂ)‖ + |t| := by
    calc
      |(q.1 : ℂ).im| = |((xiSpectralPoint q - (t : ℂ)).re) + t| := by
        rw [Complex.sub_re, Complex.ofReal_re, sub_add_cancel, hre]
      _ ≤ |(xiSpectralPoint q - (t : ℂ)).re| + |t| := abs_add_le _ _
      _ ≤ ‖xiSpectralPoint q - (t : ℂ)‖ + |t| :=
        add_le_add (Complex.abs_re_le_norm _) le_rfl
  constructor
  · linarith only [hmem.1, hlow, hR, abs_nonneg t]
  · calc
      ‖xiSpectralPoint q - (t : ℂ)‖ ≤ ‖xiSpectralPoint q‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
      _ ≤ (|(xiSpectralPoint q).re| + |(xiSpectralPoint q).im|) + |t| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (Complex.norm_le_abs_re_add_abs_im _) le_rfl
      _ ≤ 5 * R := by rw [hre]; linarith only [hmem.2, gaussianSpectral_im_abs_le_half q, hR, abs_nonneg t]

private theorem eventually_gaussianBand_card :
    ∀ᶠ R : ℝ in atTop, R ≤ ((xiCopiesBand (2 * R) (4 * R)).card : ℝ) := by
  have htwo : Tendsto (fun R : ℝ => 2 * R) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (max b 0)] with R hR
    linarith only [le_max_left b 0, le_max_right b 0, hR]
  filter_upwards [htwo.eventually eventually_card_xiCopiesBand_mul_two_lower,
    (Real.tendsto_log_atTop.comp htwo).eventually_ge_atTop (2 * Real.pi),
    eventually_ge_atTop (1 : ℝ)] with R hcard hlog hR
  have hcount : (1 / (4 * Real.pi)) * ((2 * R) * Real.log (2 * R)) ≤
      ((xiCopiesBand (2 * R) (4 * R)).card : ℝ) := by
    simpa only [show 2 * (2 * R) = 4 * R by ring] using hcard
  refine le_trans ?_ hcount
  calc
    R = (1 / (4 * Real.pi)) * ((2 * R) * (2 * Real.pi)) := by field_simp; ring
    _ ≤ (1 / (4 * Real.pi)) * ((2 * R) * Real.log (2 * R)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by positivity)

/-- Actual zero counting prevents the far-tail reciprocal mass from collapsing. -/
theorem eventually_xiSliceGaussianTailMass_lower (t : ℝ) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      1 / (25 * R) ≤ xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) := by
  classical
  filter_upwards [eventually_gaussianBand_card,
    eventually_ge_atTop (2 * |t| + 1)] with R hcard hR
  have hR0 : 0 < R := by linarith only [hR, abs_nonneg t]
  let H := xiSliceGaussianRadiusHead t R
  let S := xiCopiesBand (2 * R) (4 * R)
  have hout : ∀ q ∈ S, q ∉ H := by
    intro q hq
    change ¬ q ∈ xiSliceGaussianRadiusHead t R
    rw [mem_xiSliceGaussianRadiusHead]
    exact not_le.mpr (gaussianBand_distance_bounds t hR hq).1
  have hterm : ∀ q ∈ S, 1 / (25 * R ^ 2) ≤ ‖xiSliceGaussianReciprocal t q‖ := by
    intro q hq
    obtain ⟨hd0, hd1⟩ := gaussianBand_distance_bounds t hR hq
    have hd : 0 < ‖xiSpectralPoint q - (t : ℂ)‖ := hR0.trans hd0
    rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
    calc
      ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 ≤ (5 * R) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd1 2
      _ = 25 * R ^ 2 := by ring
  have hsum : (∑ q ∈ S, ‖xiSliceGaussianReciprocal t q‖) ≤ xiSliceGaussianTailMass t H := by
    rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖) hout]
    exact (summable_norm_xiSliceGaussianTail t H).sum_le_tsum _ (fun _ _ => norm_nonneg _)
  refine ⟨hR0, ?_⟩
  calc
    1 / (25 * R) = R * (1 / (25 * R ^ 2)) := by field_simp [hR0.ne']
    _ ≤ (S.card : ℝ) * (1 / (25 * R ^ 2)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ q ∈ S, (1 / (25 * R ^ 2)) := by simp
    _ ≤ ∑ q ∈ S, ‖xiSliceGaussianReciprocal t q‖ := Finset.sum_le_sum hterm
    _ ≤ xiSliceGaussianTailMass t H := hsum

/-- Removing the distance-`R` head bounds the fourth moment by the reciprocal-square mass. -/
theorem xiSliceGaussianTailFourth_le (t : ℝ) {R : ℝ} (hR : 0 < R) :
    xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) ≤
      xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) / R ^ 2 := by
  let H := xiSliceGaussianRadiusHead t R
  have hb (q : {q : XiZeroCopy // q ∉ H}) :
      ‖xiSliceGaussianReciprocal t q‖ ≤ 1 / R ^ 2 := by
    have hdist : R < ‖xiSpectralPoint q - (t : ℂ)‖ :=
      lt_of_not_ge (fun h => q.property ((mem_xiSliceGaussianRadiusHead t R q).2 h))
    rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hR)
      (pow_le_pow_left₀ hR.le hdist.le 2)
  calc
    xiSliceGaussianTailFourth t H = ∑' q : {q : XiZeroCopy // q ∉ H},
        ‖xiSliceGaussianReciprocal t q‖ ^ 2 := rfl
    _ ≤ ∑' q : {q : XiZeroCopy // q ∉ H}, ‖xiSliceGaussianReciprocal t q‖ / R ^ 2 := by
      refine Summable.tsum_le_tsum (fun q => ?_)
        (summable_sq_norm_xiSliceGaussianTail t H)
        ((summable_norm_xiSliceGaussianTail t H).div_const _)
      simpa only [pow_two, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        mul_le_mul_of_nonneg_right (hb q) (norm_nonneg (xiSliceGaussianReciprocal t q))
    _ = xiSliceGaussianTailMass t H / R ^ 2 := tsum_div_const

/-- The normalized fourth moment of the actual distant divisor tends to zero. -/
theorem eventually_xiSliceGaussianTailFourth_normalized_le (t : ℝ) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      0 < xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) ∧
      xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) /
          xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) ^ 2 ≤ 25 / R := by
  filter_upwards [eventually_xiSliceGaussianTailMass_lower t] with R hR
  have hR0 : 0 < R := hR.1
  let A := xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R)
  have hA : 0 < A := (by positivity : 0 < 1 / (25 * R)).trans_le hR.2
  have hmass : 1 ≤ 25 * R * A := by
    have h := (div_le_iff₀ (show 0 < 25 * R by positivity)).1 hR.2
    exact h.trans_eq (mul_comm A (25 * R))
  refine ⟨hR.1, hA, ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hA)).2
  refine (xiSliceGaussianTailFourth_le t hR.1).trans ?_
  apply (div_le_iff₀ (sq_pos_of_pos hR.1)).2
  calc
    A ≤ 25 * R * A ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hmass hA.le]
    _ = (25 / R * A ^ 2) * R ^ 2 := by field_simp [hR.1.ne']

/-- The critical strip aligns the distant quadratic sum with its positive norm mass. -/
theorem norm_xiSliceGaussianTailQuadratic_sub_mass_le (t : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R) -
      (xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) : ℂ)‖ ≤
        xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) / R := by
  let H := xiSliceGaussianRadiusHead t R
  have hs := summable_norm_xiSliceGaussianTail t H
  have hb (q : {q : XiZeroCopy // q ∉ H}) :
      ‖xiSliceGaussianReciprocal t q - (‖xiSliceGaussianReciprocal t q‖ : ℂ)‖ ≤
        ‖xiSliceGaussianReciprocal t q‖ / R := by
    have hdist : R < ‖xiSpectralPoint q - (t : ℂ)‖ :=
      lt_of_not_ge (fun h => q.property ((mem_xiSliceGaussianRadiusHead t R q).2 h))
    apply norm_inv_square_phase_le _ hR hdist.le
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith only [gaussianSpectral_im_abs_le_half q]
  have hsub := (hs.div_const R).of_nonneg_of_le (fun q => norm_nonneg _) hb
  have heq : xiSliceGaussianTailQuadratic t H - (xiSliceGaussianTailMass t H : ℂ) =
      ∑' q : {q : XiZeroCopy // q ∉ H},
        (xiSliceGaussianReciprocal t q - (‖xiSliceGaussianReciprocal t q‖ : ℂ)) := by
    rw [xiSliceGaussianTailQuadratic, xiSliceGaussianTailMass, Complex.ofReal_tsum,
      hs.of_norm.tsum_sub (Complex.summable_ofReal.mpr hs)]
  change ‖xiSliceGaussianTailQuadratic t H - (xiSliceGaussianTailMass t H : ℂ)‖ ≤ _
  rw [heq]
  exact (norm_tsum_le_tsum_norm hsub).trans
    ((Summable.tsum_le_tsum hb hsub (hs.div_const R)).trans_eq tsum_div_const)

/-- The actual tail in its reciprocal-mass coordinate. -/
def xiSliceGaussianNormalizedTail (t R : ℝ) (z : ℂ) : ℂ :=
  xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R)
    (z / (Real.sqrt (xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R)) : ℂ))

/-- A quantitative Gaussian approximation for the actual normalized distant Xi tail. -/
theorem eventually_norm_xiSliceGaussianNormalizedTail_sub_exp_le (t : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ z : ℂ,
      ‖xiSliceGaussianNormalizedTail t R z - Complex.exp (z ^ 2)‖ ≤
        Real.exp (2 * ‖z‖ ^ 2) * ‖z‖ ^ 4 * (25 / R) +
          Real.exp (‖z‖ ^ 2) * (Real.exp (‖z‖ ^ 2 / R) - 1) := by
  filter_upwards [eventually_xiSliceGaussianTailFourth_normalized_le t]
    with R hR
  intro z
  let H := xiSliceGaussianRadiusHead t R
  let A := xiSliceGaussianTailMass t H
  let B := xiSliceGaussianTailFourth t H
  let C := xiSliceGaussianTailQuadratic t H
  have hA : 0 < A := hR.2.1
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hsqc : (Real.sqrt A : ℂ) ^ 2 = (A : ℂ) := by
    exact_mod_cast Real.sq_sqrt hA.le
  have hphase : ‖C / (A : ℂ) - 1‖ ≤ 1 / R := by
    have hid : C / (A : ℂ) - 1 = (C - (A : ℂ)) / (A : ℂ) := by field_simp
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    calc
      ‖C - (A : ℂ)‖ / A ≤ (A / R) / A :=
        div_le_div_of_nonneg_right (norm_xiSliceGaussianTailQuadratic_sub_mass_le t hR.1) hA.le
      _ = 1 / R := by field_simp [hA.ne']
  have hquad : (z / (Real.sqrt A : ℂ)) ^ 2 * C = z ^ 2 * (C / (A : ℂ)) := by
    rw [div_pow, hsqc]
    ring
  have hn2 : ‖z / (Real.sqrt A : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / A := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
      div_pow, Real.sq_sqrt hA.le]
  have hn4 : ‖z / (Real.sqrt A : ℂ)‖ ^ 4 = ‖z‖ ^ 4 / A ^ 2 := by
    calc
      ‖z / (Real.sqrt A : ℂ)‖ ^ 4 = (‖z / (Real.sqrt A : ℂ)‖ ^ 2) ^ 2 := by ring
      _ = ‖z‖ ^ 4 / A ^ 2 := by rw [hn2, div_pow]; ring
  have hcomp :
      ‖xiSliceGaussianNormalizedTail t R z - Complex.exp (z ^ 2 * (C / (A : ℂ)))‖ ≤
        Real.exp (2 * ‖z‖ ^ 2) * ‖z‖ ^ 4 * (25 / R) := by
    have h := norm_xiSliceGaussianTail_sub_exp_le t H (z / (Real.sqrt A : ℂ))
    change ‖xiSliceGaussianNormalizedTail t R z -
      Complex.exp ((z / (Real.sqrt A : ℂ)) ^ 2 * C)‖ ≤
        Real.exp (2 * ‖z / (Real.sqrt A : ℂ)‖ ^ 2 * A) *
          (‖z / (Real.sqrt A : ℂ)‖ ^ 4 * B) at h
    rw [hquad, hn2, hn4,
      show 2 * (‖z‖ ^ 2 / A) * A = 2 * ‖z‖ ^ 2 by field_simp] at h
    calc
      _ ≤ Real.exp (2 * ‖z‖ ^ 2) * (‖z‖ ^ 4 / A ^ 2 * B) := h
      _ = Real.exp (2 * ‖z‖ ^ 2) * ‖z‖ ^ 4 * (B / A ^ 2) := by ring
      _ ≤ Real.exp (2 * ‖z‖ ^ 2) * ‖z‖ ^ 4 * (25 / R) :=
        mul_le_mul_of_nonneg_left hR.2.2 (by positivity)
  have harg : ‖z ^ 2 * (C / (A : ℂ)) - z ^ 2‖ ≤ ‖z‖ ^ 2 / R := by
    rw [show z ^ 2 * (C / (A : ℂ)) - z ^ 2 = z ^ 2 * (C / (A : ℂ) - 1) by ring,
      norm_mul, norm_pow]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hphase (sq_nonneg ‖z‖)
  have hexp : ‖Complex.exp (z ^ 2 * (C / (A : ℂ))) - Complex.exp (z ^ 2)‖ ≤
      Real.exp (‖z‖ ^ 2) * (Real.exp (‖z‖ ^ 2 / R) - 1) := by
    have h : ‖Complex.exp (z ^ 2 * (C / (A : ℂ))) - Complex.exp (z ^ 2)‖ ≤
        Real.exp (‖z‖ ^ 2) * (Real.exp ‖z ^ 2 * (C / (A : ℂ)) - z ^ 2‖ - 1) := by
      have h0 : ‖Complex.exp (z ^ 2 * (C / (A : ℂ))) - Complex.exp (z ^ 2)‖ ≤
          Real.exp ‖z ^ 2‖ * (Real.exp ‖z ^ 2 * (C / (A : ℂ)) - z ^ 2‖ - 1) := by
        simpa only [Complex.exp_eq_exp_ℂ] using
          GaloisForLFunctions.HTGeometry.FormationDust.norm_exp_sub_exp_le (𝔸 := ℂ)
            (z ^ 2 * (C / (A : ℂ))) (z ^ 2)
      rw [_root_.norm_pow] at h0
      exact h0
    exact h.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr harg) 1) (Real.exp_pos _).le)
  calc
    _ = ‖(xiSliceGaussianNormalizedTail t R z - Complex.exp (z ^ 2 * (C / (A : ℂ)))) +
        (Complex.exp (z ^ 2 * (C / (A : ℂ))) - Complex.exp (z ^ 2))‖ := by congr 1; ring
    _ ≤ ‖xiSliceGaussianNormalizedTail t R z - Complex.exp (z ^ 2 * (C / (A : ℂ)))‖ +
        ‖Complex.exp (z ^ 2 * (C / (A : ℂ))) - Complex.exp (z ^ 2)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hcomp hexp

/-- For every real center, the actual far Xi tail tends locally uniformly to `exp(z²)`
after rescaling by the square root of its reciprocal-square mass. -/
theorem tendstoUniformlyOn_xiSliceGaussianNormalizedTail (t M : ℝ) :
    TendstoUniformlyOn (xiSliceGaussianNormalizedTail t) (fun z : ℂ => Complex.exp (z ^ 2))
      atTop (Metric.closedBall 0 M) := by
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hlim : Tendsto (fun R : ℝ =>
      Real.exp (2 * K ^ 2) * K ^ 4 * (25 / R) +
        Real.exp (K ^ 2) * (Real.exp (K ^ 2 / R) - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => 25 / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun R : ℝ => K ^ 2 / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have he := Real.continuous_exp.continuousAt.tendsto.comp h2
    simpa only [Function.comp_apply, Real.exp_zero, sub_self, mul_zero, add_zero] using
      (h1.const_mul (Real.exp (2 * K ^ 2) * K ^ 4)).add
        ((he.sub_const 1).const_mul (Real.exp (K ^ 2)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_norm_xiSliceGaussianNormalizedTail_sub_exp_le t,
    hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with R hR hsmall hR0
  intro z hz
  have hzK : ‖z‖ ≤ K := (mem_closedBall_zero_iff.mp hz).trans (le_max_left _ _)
  have hz2 : ‖z‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzK 2
  have hz4 : ‖z‖ ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hzK 4
  rw [dist_eq_norm, norm_sub_rev]
  refine (hR z).trans_lt (lt_of_le_of_lt ?_ hsmall)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 25 / R)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith only [hz2])) hz4
      (by positivity) (Real.exp_pos _).le
  · exact mul_le_mul (Real.exp_le_exp.mpr hz2)
      (sub_le_sub_right (Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right hz2 hR0.le)) 1)
      (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (Real.exp_pos _).le

end
end RHTower
