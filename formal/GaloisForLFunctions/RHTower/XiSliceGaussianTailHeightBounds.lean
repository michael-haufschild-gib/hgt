import GaloisForLFunctions.RHTower.XiSliceGaussianTailLimit
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration

/-!
# Reciprocal moments of Xi tails at growing height

The critical strip and an unconditional partial-fraction estimate bound the
tail mass and fourth moment. The logarithmic Riemann--von Mangoldt remainder
supplies a matching lower mass scale on a translated ordinate band.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

private theorem gaussian_anchor_distance_le (σ t : ℝ) (q : XiZeroCopy) :
    ‖((σ : ℂ) + t * I) - (q.1 : ℂ)‖ ≤
      |σ - 1 / 2| + ‖xiSpectralPoint q - (t : ℂ)‖ := by
  have heq : ((σ : ℂ) + t * I) - (q.1 : ℂ) =
      ((σ - 1 / 2 : ℝ) : ℂ) - I * (xiSpectralPoint q - (t : ℂ)) := by
    apply Complex.ext <;> simp [xiSpectralPoint]
  rw [heq]
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I, one_mul] using
    norm_sub_le (((σ - 1 / 2 : ℝ) : ℂ)) (I * (xiSpectralPoint q - (t : ℂ)))

private theorem gaussian_two_anchor_distance (t : ℝ) (q : XiZeroCopy) :
    1 ≤ ‖((2 : ℂ) + t * I) - (q.1 : ℂ)‖ := by
  have hre : 1 ≤ (((2 : ℂ) + t * I) - (q.1 : ℂ)).re := by
    have heq : (((2 : ℂ) + t * I) - (q.1 : ℂ)).re = 2 - (q.1 : ℂ).re := by simp
    rw [heq]
    linarith only [xiZeroCopy_re_lt_one q]
  exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

private theorem gaussian_reciprocal_le_anchor_diff (t : ℝ) {R : ℝ} (hR : 3 ≤ R)
    (q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R}) :
    ‖xiSliceGaussianReciprocal t q‖ ≤ 4 *
      ‖(((2 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹ -
        (((3 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹‖ := by
  let d := ‖xiSpectralPoint q - (t : ℂ)‖
  have hdR : R < d := lt_of_not_ge (fun h =>
    q.property ((mem_xiSliceGaussianRadiusHead t R q).2 h))
  have hd : 0 < d := by linarith only [hR, hdR]
  have h2 : ‖((2 : ℂ) + t * I) - (q.val.1 : ℂ)‖ ≤ 2 * d := by
    have h := gaussian_anchor_distance_le 2 t q
    norm_num at h
    linarith only [h, hR, hdR]
  have h3 : ‖((3 : ℂ) + t * I) - (q.val.1 : ℂ)‖ ≤ 2 * d := by
    have h := gaussian_anchor_distance_le 3 t q
    norm_num at h
    linarith only [h, hR, hdR]
  have h2pos : 0 < ‖((2 : ℂ) + t * I) - (q.val.1 : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one (gaussian_two_anchor_distance t q)
  have h3pos : 0 < ‖((3 : ℂ) + t * I) - (q.val.1 : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_norm_anchor_sub t q)
  have hprod :
      ‖((2 : ℂ) + t * I) - (q.val.1 : ℂ)‖ *
        ‖((3 : ℂ) + t * I) - (q.val.1 : ℂ)‖ ≤ 4 * d ^ 2 := by
    calc
      _ ≤ (2 * d) * (2 * d) := mul_le_mul h2 h3 h3pos.le (by positivity)
      _ = 4 * d ^ 2 := by ring
  rw [norm_partialFractionDiff_eq (norm_pos_iff.mp h2pos) (norm_pos_iff.mp h3pos)]
  have hnum : ‖((3 : ℂ) + t * I) - ((2 : ℂ) + t * I)‖ = 1 := by
    rw [show ((3 : ℂ) + t * I) - ((2 : ℂ) + t * I) = 1 by ring, norm_one]
  rw [hnum, xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div, mul_one_div]
  exact (div_le_div_iff₀ (sq_pos_of_pos hd) (mul_pos h2pos h3pos)).2 (by
    simpa only [one_mul] using hprod)

/-- A uniform logarithmic bound for the actual reciprocal mass outside a fixed distance. -/
theorem xiSliceGaussianTailMass_le_log {t R : ℝ} (ht : 4 ≤ t) (hR : 3 ≤ R) :
    xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) ≤
      (4 * (3650 + 5 * smallHeightCount)) * Real.log t := by
  classical
  let H := xiSliceGaussianRadiusHead t R
  let e : {q : XiZeroCopy // q ∉ H} ↪ XiZeroCopy :=
    ⟨Subtype.val, Subtype.val_injective⟩
  apply (summable_norm_xiSliceGaussianTail t H).tsum_le_of_sum_le
  intro F
  have hsource := sum_norm_partialFractionDiff_le (σ := 2) (δ := 1)
    (by norm_num) le_rfl ht zero_lt_one le_rfl (gaussian_two_anchor_distance t) (F.map e)
  rw [Finset.sum_map] at hsource
  calc
    _ ≤ ∑ q ∈ F, 4 *
        ‖(((2 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹ -
          (((3 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹‖ :=
      Finset.sum_le_sum (fun q _ => gaussian_reciprocal_le_anchor_diff t hR q)
    _ = 4 * ∑ q ∈ F,
        ‖(((2 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹ -
          (((3 : ℂ) + t * I) - (q.val.1 : ℂ))⁻¹‖ := by rw [Finset.mul_sum]
    _ ≤ 4 * ((3650 + 5 * smallHeightCount) * Real.log t / 1) :=
      mul_le_mul_of_nonneg_left hsource (by norm_num)
    _ = (4 * (3650 + 5 * smallHeightCount)) * Real.log t := by ring

/-- The actual fourth moment decays with the cutoff, uniformly in the center height. -/
theorem xiSliceGaussianTailFourth_le_log {t R : ℝ} (ht : 4 ≤ t) (hR : 3 ≤ R) :
    xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) ≤
      (4 * (3650 + 5 * smallHeightCount)) * Real.log t / R ^ 2 :=
  (xiSliceGaussianTailFourth_le t (by linarith only [hR])).trans
    (div_le_div_of_nonneg_right (xiSliceGaussianTailMass_le_log ht hR) (sq_nonneg R))

/-- Riemann--von Mangoldt supplies reciprocal mass uniformly at growing center and cutoff. -/
theorem exists_xiSliceGaussianTailMass_height_lower :
    ∃ T₀ R₀ : ℝ, 4 ≤ T₀ ∧ 3 ≤ R₀ ∧ ∀ t R : ℝ,
      T₀ ≤ t → R₀ ≤ R → 4 * R ≤ t →
        Real.log t / (100 * Real.pi * R) ≤
          xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) := by
  classical
  obtain ⟨C, hC, T₀, hT₀, hclose⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨max T₀ (routeKRVMBase ^ 2), max 3 (16 * Real.pi * C),
    hT₀.trans (le_max_left _ _), le_max_left _ _, ?_⟩
  intro t R ht hR hRt
  have htT : T₀ ≤ t := (le_max_left _ _).trans ht
  have ht4 : 4 ≤ t := hT₀.trans htT
  have ht0 : 0 < t := by linarith only [ht4]
  have hR3 : 3 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := by linarith only [hR3]
  have hRC : 16 * Real.pi * C ≤ R := (le_max_right _ _).trans hR
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht4])
  have hlogbase : 2 * Real.log routeKRVMBase ≤ Real.log t := by
    have h := Real.log_le_log (pow_pos routeKRVMBase_pos 2) ((le_max_right _ _).trans ht)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  let a := t + 2 * R
  let b := t + 4 * R
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hta : t ≤ a := by dsimp only [a]; linarith only [hR0]
  have hab : a ≤ b := by dsimp only [a, b]; linarith only [hR0]
  have hba : b - a = 2 * R := by dsimp only [a, b]; ring
  have hbupper : b ≤ t ^ 2 := by
    dsimp only [b]
    nlinarith only [hRt, mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ t by linarith only [ht4]) ht0.le]
  have hloga : Real.log a ≤ 2 * Real.log t := by
    have h := Real.log_le_log ha0 (hab.trans hbupper)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogb : Real.log b ≤ 2 * Real.log t := by
    have h := Real.log_le_log hb0 hbupper
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hmain : R * Real.log t / (2 * Real.pi) ≤
      routeKSmoothRVMCount b - routeKSmoothRVMCount a := by
    rw [routeKSmoothRVMCount_sub_eq ha0 hb0]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log ht0 hta) (sub_nonneg.mpr hab)
    have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log ha0 hab) hb0.le
    have h3 := mul_le_mul_of_nonneg_left hlogbase hR0.le
    have hdiff : (b - a) * Real.log t ≤ b * Real.log b - a * Real.log a := by
      nlinarith only [h1, h2]
    rw [hba] at hdiff ⊢
    nlinarith only [hdiff, h3]
  have hca := (abs_le.mp (hclose a (htT.trans hta))).2
  have hcb := (abs_le.mp (hclose b (htT.trans (hta.trans hab)))).1
  have hCloga := mul_le_mul_of_nonneg_left hloga hC.le
  have hClogb := mul_le_mul_of_nonneg_left hlogb hC.le
  have hband : R * Real.log t / (2 * Real.pi) - 4 * C * Real.log t ≤
      (xiZeroCount b : ℝ) - (xiZeroCount a : ℝ) := by
    linarith only [hmain, hca, hcb, hCloga, hClogb]
  have hpay : 4 * C * Real.log t ≤ R * Real.log t / (4 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).2
    nlinarith only [mul_le_mul_of_nonneg_right hRC hlog0]
  have hhalf : R * Real.log t / (2 * Real.pi) = 2 * (R * Real.log t / (4 * Real.pi)) := by
    field_simp
    ring
  let F := xiCopiesPos b \ xiCopiesPos a
  have hsub : xiCopiesPos a ⊆ xiCopiesPos b := by
    intro q hq
    exact mem_xiCopiesPos.mpr ⟨(mem_xiCopiesPos.mp hq).1.trans hab, (mem_xiCopiesPos.mp hq).2⟩
  have haCard : ((xiCopiesPos a).card : ℝ) = (xiZeroCount a : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos ha0.le
  have hbCard : ((xiCopiesPos b).card : ℝ) = (xiZeroCount b : ℝ) := by
    exact_mod_cast intCast_card_xiCopiesPos hb0.le
  have hcardEq : (F.card : ℝ) = (xiZeroCount b : ℝ) - (xiZeroCount a : ℝ) := by
    dsimp only [F]
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), hbCard, haCard]
  have hcard : R * Real.log t / (4 * Real.pi) ≤ (F.card : ℝ) := by
    rw [hcardEq]
    rw [hhalf] at hband
    linarith only [hband, hpay]
  have hdist (q : XiZeroCopy) (hq : q ∈ F) :
      R < ‖xiSpectralPoint q - (t : ℂ)‖ ∧ ‖xiSpectralPoint q - (t : ℂ)‖ ≤ 5 * R := by
    obtain ⟨hqB, hqA⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hγb, hγ0⟩ := mem_xiCopiesPos.mp hqB
    rw [abs_of_pos hγ0] at hγb
    have haγ : a < (q.1 : ℂ).im := lt_of_not_ge (fun h =>
      hqA (mem_xiCopiesPos.mpr ⟨by simpa only [abs_of_pos hγ0] using h, hγ0⟩))
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have hγt : 0 < (q.1 : ℂ).im - t := by dsimp only [a] at haγ; linarith only [haγ, hR0]
    have hlow : (q.1 : ℂ).im - t ≤ ‖xiSpectralPoint q - (t : ℂ)‖ := by
      have h := (le_abs_self (xiSpectralPoint q - (t : ℂ)).re).trans (Complex.abs_re_le_norm _)
      simpa only [Complex.sub_re, Complex.ofReal_re, hre] using h
    have hi : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
      nlinarith only [xiSpectralPoint_im_sq_lt_quarter q,
        sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]
    constructor
    · dsimp only [a] at haγ
      linarith only [haγ, hlow, hR0]
    · have h := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q - (t : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re, hre, Complex.sub_im,
        Complex.ofReal_im, sub_zero, abs_of_pos hγt] at h
      dsimp only [b] at hγb
      linarith only [h, hγb, hi, hR3]
  let H := xiSliceGaussianRadiusHead t R
  have hout : ∀ q ∈ F, q ∉ H := by
    intro q hq
    change ¬ q ∈ xiSliceGaussianRadiusHead t R
    rw [mem_xiSliceGaussianRadiusHead]
    exact not_le.mpr (hdist q hq).1
  have hterm : ∀ q ∈ F, 1 / (25 * R ^ 2) ≤ ‖xiSliceGaussianReciprocal t q‖ := by
    intro q hq
    obtain ⟨hd0, hd1⟩ := hdist q hq
    rw [xiSliceGaussianReciprocal, norm_inv, norm_pow, ← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos (hR0.trans hd0))
    calc
      ‖xiSpectralPoint q - (t : ℂ)‖ ^ 2 ≤ (5 * R) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd1 2
      _ = 25 * R ^ 2 := by ring
  have hsum : (∑ q ∈ F, ‖xiSliceGaussianReciprocal t q‖) ≤ xiSliceGaussianTailMass t H := by
    rw [← Finset.sum_subtype_of_mem (fun q => ‖xiSliceGaussianReciprocal t q‖) hout]
    exact (summable_norm_xiSliceGaussianTail t H).sum_le_tsum _ (fun _ _ => norm_nonneg _)
  calc
    Real.log t / (100 * Real.pi * R) =
        (R * Real.log t / (4 * Real.pi)) * (1 / (25 * R ^ 2)) := by
      field_simp [hR0.ne']
      ring
    _ ≤ (F.card : ℝ) * (1 / (25 * R ^ 2)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ q ∈ F, 1 / (25 * R ^ 2) := by simp
    _ ≤ ∑ q ∈ F, ‖xiSliceGaussianReciprocal t q‖ := Finset.sum_le_sum hterm
    _ ≤ xiSliceGaussianTailMass t H := hsum

end
end RHTower

