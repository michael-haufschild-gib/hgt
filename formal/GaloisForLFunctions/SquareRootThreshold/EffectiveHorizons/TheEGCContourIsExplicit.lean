import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.XiZeroMass
import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.RHTower.PaperEGCEnclosedPoleCancellation

/-!
# Explicit constants for the EGC source contour

The mass-subtracted source contour differs from the zero count by the sum over the copies outside the rectangle. The
explicit Riemann–von Mangoldt count bounds that sum by `32 ε² log T / T` as soon as the rectangle contains every copy of
ordinate at most `T`:

* `sum_inv_norm_sq_le`: `Σ_{|γ| > T} |ρ|⁻² ≤ 4 log T / T` above the explicit height `xiMassHeight (1/100)`;
* `norm_contour_sub_count_le`: the explicit contour inequality;
* `egcHeight`: `T(n) = max(xiMassHeight (1/100), 10⁴ (n + 1)²)` gives error below `1/(n + 1)`.
-/

set_option autoImplicit false

open Complex Filter Set
open RHTower

namespace GaloisForLFunctions.SquareRootThreshold

noncomputable section

private theorem re_spectral (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

private theorem xiSymmetricMass_le {X : ℝ} (hX : xiMassHeight (1 / 100) ≤ X) :
    (xiSymmetricMass X : ℝ) ≤ 33 / 100 * (X * Real.log X) := by
  have h := xiSymmetricMass_close_explicit (by norm_num : (0 : ℝ) < 1 / 100) hX
  have hX4 : 4 ≤ X := (four_le_xiMassHeight _).trans hX
  have hlog : 0 ≤ X * Real.log X :=
    mul_nonneg (by linarith only [hX4]) (Real.log_nonneg (by linarith only [hX4]))
  have hπ2 : 1 / Real.pi ≤ 319 / 1000 := by
    rw [div_le_iff₀ Real.pi_pos]
    have := Real.pi_gt_d2
    linarith only [this]
  rw [abs_le] at h
  nlinarith only [h.2, hπ2, hlog]

private theorem sum_dyadic_two (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 2 ^ k = 6 - (2 * K + 6) / 2 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h2 : ((2 : ℝ) ^ K) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **The tail of the reciprocal squares.** Above the explicit height, any finite set of copies of ordinate above `T`
has `Σ |ρ|⁻² ≤ 4 log T / T`. -/
theorem sum_inv_norm_sq_le {T : ℝ} (hT : xiMassHeight (1 / 100) ≤ T) (B : Finset XiZeroCopy)
    (hB : ∀ q ∈ B, T < |(xiSpectralPoint q).re|) :
    ∑ q ∈ B, (‖xiSpectralPoint q‖ ^ 2)⁻¹ ≤ 4 * (Real.log T / T) := by
  classical
  have hT4 : 4 ≤ T := (four_le_xiMassHeight _).trans hT
  have hT0 : 0 < T := by linarith only [hT4]
  have hL : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith only [hT4])
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT4])
  have hstep (K : ℕ) : ∑ q ∈ B.filter fun q => |(xiSpectralPoint q).re| ≤ 2 ^ K * T,
      (‖xiSpectralPoint q‖ ^ 2)⁻¹ ≤
      66 / 100 * (Real.log T / T) * ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 2 ^ k := by
    induction K with
    | zero =>
      rw [Finset.filter_false_of_mem, Finset.sum_empty]
      · simp
      · intro q hq
        have := hB q hq
        rw [pow_zero, one_mul]
        exact not_le.2 this
    | succ K ih =>
      set X := (2 : ℝ) ^ K * T with hX
      have hX0 : 0 < X := by positivity
      have hX1 : T ≤ X := by
        rw [hX]
        exact le_mul_of_one_le_left hT0.le (one_le_pow₀ (by norm_num))
      have h2X : (2 : ℝ) ^ (K + 1) * T = 2 * X := by
        rw [hX, pow_succ]
        ring
      rw [h2X]
      have h2Xh : xiMassHeight (1 / 100) ≤ 2 * X := hT.trans (by linarith only [hX1, hT0])
      set S := B.filter fun q => |(xiSpectralPoint q).re| ≤ 2 * X with hS
      set S₀ := B.filter fun q => |(xiSpectralPoint q).re| ≤ X with hS₀
      have hsub : S₀ ⊆ S := by
        intro q hq
        rw [hS₀, Finset.mem_filter] at hq
        rw [hS, Finset.mem_filter]
        exact ⟨hq.1, hq.2.trans (by linarith only [hX0])⟩
      rw [← Finset.sum_sdiff hsub]
      have hshell : ∑ q ∈ S \ S₀, (‖xiSpectralPoint q‖ ^ 2)⁻¹ ≤
          ((S \ S₀).card : ℝ) * (X ^ 2)⁻¹ := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
        rw [Finset.mem_sdiff, hS, hS₀, Finset.mem_filter, Finset.mem_filter] at hq
        have hgt : X < |(xiSpectralPoint q).re| := by
          by_contra hc
          exact hq.2 ⟨hq.1.1, not_lt.1 hc⟩
        have hn : X ≤ ‖xiSpectralPoint q‖ := hgt.le.trans (Complex.abs_re_le_norm _)
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hX0.le hn 2)
      have hcard : ((S \ S₀).card : ℝ) ≤ xiSymmetricMass (2 * X) := by
        refine card_le_xiSymmetricMass_of_forall_abs_im_le (by positivity) fun q hq => ?_
        rw [Finset.mem_sdiff, hS, Finset.mem_filter] at hq
        rw [← re_spectral]
        exact hq.1.2
      have hmass := xiSymmetricMass_le h2Xh
      have hlog2X : Real.log (2 * X) ≤ ((K : ℝ) + 2) * Real.log T := by
        have e : 2 * X = 2 ^ (K + 1) * T := by
          rw [hX, pow_succ]
          ring
        rw [e, Real.log_mul (by positivity) hT0.ne', Real.log_pow]
        push_cast
        nlinarith only [hL, (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
      have hterm : ((S \ S₀).card : ℝ) * (X ^ 2)⁻¹ ≤
          66 / 100 * (Real.log T / T) * (((K : ℝ) + 2) / 2 ^ K) := by
        have hX2 : 0 < X ^ 2 := by positivity
        rw [← div_eq_mul_inv, div_le_iff₀ hX2]
        have hbound : ((S \ S₀).card : ℝ) ≤ 33 / 100 * (2 * X * (((K : ℝ) + 2) * Real.log T)) := by
          refine hcard.trans (hmass.trans ?_)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog2X (by positivity)) (by norm_num)
        refine hbound.trans (le_of_eq ?_)
        have hX2' : X ^ 2 = X * (2 ^ K * T) := by
          rw [hX]
          ring
        rw [hX2']
        have h2 : ((2 : ℝ) ^ K) ≠ 0 := by positivity
        field_simp
        ring
      rw [Finset.sum_range_succ, mul_add]
      linarith only [hshell, hterm, ih]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ q ∈ B, |(xiSpectralPoint q).re| ≤ 2 ^ K * T := by
    obtain ⟨M, hM⟩ := (B.image fun q => |(xiSpectralPoint q).re|).exists_le
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (M / T) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, fun q hq => (hM _ (Finset.mem_image_of_mem _ hq)).trans ?_⟩
    rw [div_lt_iff₀ hT0] at hK
    exact hK.le
  have hall := hstep K
  rw [Finset.filter_true_of_mem hK] at hall
  refine hall.trans ?_
  have hsum : ∑ k ∈ Finset.range K, ((k : ℝ) + 2) / 2 ^ k ≤ 6 := by
    rw [sum_dyadic_two]
    have : 0 ≤ (2 * (K : ℝ) + 6) / 2 ^ K := by positivity
    linarith only [this]
  have hpos : 0 ≤ Real.log T / T := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hsum hpos, hpos]

/-- **The explicit contour inequality.** If the rectangle contains every copy of ordinate at most `T`, the source
contour is its zero count up to `32 ε² log T / T`, uniformly in the small parameters and the enclosed height. -/
theorem norm_contour_sub_count_le {T : ℝ} (hT : xiMassHeight (1 / 100) ≤ T)
    (R : PaperEGCSourceRectangle)
    (hR : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ T →
      q ∈ xiZeroCopyClosedRectangle R.lower R.upper)
    (eps x : PaperEGCSmallParameter) (t : ℝ)
    (hp : R.Inside (((x : ℝ) : ℂ) + (t : ℂ) * I + ((eps : ℝ) : ℂ)))
    (hm : R.Inside (((x : ℝ) : ℂ) + (t : ℂ) * I - ((eps : ℝ) : ℂ))) :
    ‖normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ)
        (((x : ℝ) : ℂ) + (t : ℂ) * I) R.lower R.upper -
      ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ)‖ ≤
      32 * ((eps : ℝ) ^ 2 * (Real.log T / T)) := by
  classical
  rw [R.enclosed_poles_eq_count_add_exterior eps x t hp hm, add_sub_cancel_left]
  have hsum : Summable fun a : {a : XiZeroCopy // a ∉ xiZeroCopyClosedRectangle R.lower R.upper} =>
      ‖paperEGCLineCopy eps x t a.1‖ := (summable_norm_paperEGCLineCopy eps x t).subtype _
  refine (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_of_sum_le fun s => ?_)
  have hB : ∀ q ∈ s.map (Function.Embedding.subtype _), T < |(xiSpectralPoint q).re| := by
    intro q hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hq
    by_contra hc
    exact a.2 (hR a.1 (not_lt.mp hc))
  have hmain := sum_inv_norm_sq_le hT _ hB
  rw [Finset.sum_map] at hmain
  have heps : 0 ≤ 8 * (eps : ℝ) ^ 2 := by positivity
  calc
    _ ≤ ∑ a ∈ s, 8 * (eps : ℝ) ^ 2 * (‖xiSpectralPoint a.1‖ ^ 2)⁻¹ :=
      Finset.sum_le_sum fun a _ => by
        have h := norm_paperEGCLineCopy_le_scale eps x t a.1
        rwa [div_eq_mul_inv] at h
    _ = 8 * (eps : ℝ) ^ 2 * ∑ a ∈ s, (‖xiSpectralPoint a.1‖ ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 8 * (eps : ℝ) ^ 2 * (4 * (Real.log T / T)) := mul_le_mul_of_nonneg_left hmain heps
    _ = _ := by ring

/-- The explicit height at which the contour error falls below `1/(n + 1)`. -/
def egcHeight (n : ℕ) : ℝ :=
  max (xiMassHeight (1 / 100)) (10 ^ 4 * ((n : ℝ) + 1) ^ 2)

theorem thirtytwo_log_div_egcHeight_lt (n : ℕ) :
    32 * (Real.log (egcHeight n) / egcHeight n) < 1 / ((n : ℝ) + 1) := by
  obtain ⟨T, hTdef⟩ : ∃ T, T = egcHeight n := ⟨_, rfl⟩
  rw [← hTdef]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hT2 : 10 ^ 4 * ((n : ℝ) + 1) ^ 2 ≤ T := hTdef ▸ le_max_right _ _
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT2
  have hs : 100 * ((n : ℝ) + 1) ≤ Real.sqrt T := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    nlinarith only [hT2]
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have hlog : Real.log T ≤ 2 * Real.sqrt T := by
    have h1 := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hT0.le] at h1
    linarith only [h1]
  have hdiv : Real.log T / T ≤ 2 / (100 * ((n : ℝ) + 1)) := by
    rw [div_le_div_iff₀ hT0 (by positivity)]
    calc
      _ ≤ 2 * Real.sqrt T * (100 * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      _ ≤ 2 * Real.sqrt T * Real.sqrt T :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_assoc, hss]
  have hlt : 32 * (2 / (100 * ((n : ℝ) + 1))) < 1 / ((n : ℝ) + 1) := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) hn]
    nlinarith only [hn]
  linarith only [hdiv, hlt]

/-- **The contour at an explicit height.** Every source rectangle containing the copies of ordinate at most
`egcHeight n` has error below `1/(n + 1)`, and such rectangles exist around every centered prescribed pole. -/
theorem exists_explicit_centered_source_contour (n : ℕ) :
    ∃ R : PaperEGCSourceRectangle,
      (∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ egcHeight n →
        q ∈ xiZeroCopyClosedRectangle R.lower R.upper) ∧
      (∀ u ∈ Icc (-2 : ℝ) 2, R.Inside (u : ℂ)) ∧
      ∀ eps x : PaperEGCSmallParameter,
        ‖normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ) ((x : ℝ) : ℂ)
            R.lower R.upper - ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ)‖ <
          1 / ((n : ℝ) + 1) := by
  obtain ⟨R, hR, hwindow⟩ := PaperEGCSourceRectangle.exists_containing_centered_window
    (xiCopiesBand 0 (egcHeight n))
  have hmem : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ egcHeight n →
      q ∈ xiZeroCopyClosedRectangle R.lower R.upper := by
    intro q hq
    refine hR (mem_xiCopiesBand.mpr ⟨abs_pos.mpr (xiSupport_im_ne_zero q.1), ?_⟩)
    rwa [re_spectral] at hq
  refine ⟨R, hmem, hwindow, fun eps x => ?_⟩
  have hp : R.Inside (((x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I + ((eps : ℝ) : ℂ)) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_add]
    exact hwindow _ ⟨by linarith only [x.2.1, eps.2.1], by linarith only [x.2.2, eps.2.2]⟩
  have hm : R.Inside (((x : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ((eps : ℝ) : ℂ)) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_sub]
    exact hwindow _ ⟨by linarith only [x.2.1, eps.2.2], by linarith only [x.2.2, eps.2.1]⟩
  have hheight : xiMassHeight (1 / 100) ≤ egcHeight n := le_max_left _ _
  have hb := norm_contour_sub_count_le hheight R hmem eps x 0 hp hm
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hb
  have heps : (eps : ℝ) ^ 2 ≤ 1 := by nlinarith only [eps.2.1, eps.2.2]
  have h4 : 4 ≤ egcHeight n := (four_le_xiMassHeight _).trans hheight
  have hL : 0 ≤ Real.log (egcHeight n) / egcHeight n :=
    div_nonneg (Real.log_nonneg (by linarith only [h4])) (by linarith only [h4])
  calc
    _ ≤ _ := hb
    _ ≤ 32 * (1 * (Real.log (egcHeight n) / egcHeight n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heps hL) (by norm_num)
    _ = 32 * (Real.log (egcHeight n) / egcHeight n) := by rw [one_mul]
    _ < _ := thirtytwo_log_div_egcHeight_lt n

end

end GaloisForLFunctions.SquareRootThreshold
