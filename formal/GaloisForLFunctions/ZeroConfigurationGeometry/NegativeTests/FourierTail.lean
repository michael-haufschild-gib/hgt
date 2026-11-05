import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget

/-!
# Absolute Fourier tails and the negative pair sign

Reflection preserves the height band. Integer multiplicities then bound the
quadratic Weil tail by the square of its absolute Fourier tail. Quarter
accuracy at opposite real transform values preserves a negative pair image.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Absolute weighted Fourier mass outside a height band. -/
def fourierFarTerm (c : ℂ → ℂ) (f : ℝ → ℂ) (X R : ℝ) (z : ℂ) : ℝ :=
  if R < |z.im - X| then ‖c z‖ * ‖paperFT f (gammaOf z)‖ else 0

theorem fourierFarTerm_nonneg (c : ℂ → ℂ) (f : ℝ → ℂ) (X R : ℝ) (z : ℂ) :
    0 ≤ fourierFarTerm c f X R z := by
  unfold fourierFarTerm
  split_ifs <;> positivity

theorem multDiff_empty_ne_zero_iff (Z : ZeroConfig) (z : ℂ) :
    multDiff Z emptyZeroConfig z ≠ 0 ↔ z ∈ Z.carrier := by
  rw [multDiff_emptyZeroConfig]
  by_cases hz : z ∈ Z.carrier
  · rw [Set.indicator_of_mem hz]
    exact ⟨fun _ => hz,
      fun _ => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Z.one_le_mult z hz))⟩
  · rw [Set.indicator_of_notMem hz]
    exact ⟨fun h => False.elim (h rfl), fun h => False.elim (hz h)⟩

/-- The quadratic Weil tail is bounded by the square of its absolute Fourier
tail: reflection preserves height, and every nonzero multiplicity is at least one. -/
theorem quadratic_far_tail_le_square {Z : ZeroConfig} {f : ℝ → ℂ} {X R : ℝ}
    (hs : Summable (fourierFarTerm (multDiff Z emptyZeroConfig) f X R)) :
    (Summable fun z => ‖(if R < |z.im - X| then
      multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖) ∧
    ‖∑' z, (if R < |z.im - X| then
      multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖ ≤
      (∑' z, fourierFarTerm (multDiff Z emptyZeroConfig) f X R z) ^ 2 := by
  classical
  set L := ∑' z, fourierFarTerm (multDiff Z emptyZeroConfig) f X R z with hL
  have hL0 : 0 ≤ L := tsum_nonneg (fourierFarTerm_nonneg _ _ _ _)
  have hvalue (z : ℂ) (hz : multDiff Z emptyZeroConfig z ≠ 0)
      (hfar : R < |z.im - X|) : ‖paperFT f (gammaOf z)‖ ≤ L := by
    have h := hs.le_tsum z fun w _ => fourierFarTerm_nonneg _ _ _ _ w
    rw [fourierFarTerm, if_pos hfar] at h
    exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_norm_multDiff hz)).trans h
  have hbound (z : ℂ) :
      ‖(if R < |z.im - X| then multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖ ≤
        fourierFarTerm (multDiff Z emptyZeroConfig) f X R z * L := by
    by_cases hfar : R < |z.im - X|
    · rw [if_pos hfar, norm_mul, fourierFarTerm, if_pos hfar]
      by_cases hc : multDiff Z emptyZeroConfig z = 0
      · simpa only [hc, norm_zero, zero_mul] using (le_refl (0 : ℝ))
      · have hz := (multDiff_empty_ne_zero_iff Z z).mp hc
        have hrz := (multDiff_empty_ne_zero_iff Z (reflect z)).mpr (Z.reflect_mem z hz)
        have hfar' : R < |(reflect z).im - X| := by
          simpa only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im,
            zero_sub, neg_neg] using hfar
        have hv := hvalue (reflect z) hrz hfar'
        rw [gammaOf_reflect_eq_conj] at hv
        rw [pointImage, norm_mul, Complex.norm_conj]
        calc ‖multDiff Z emptyZeroConfig z‖ *
              (‖paperFT f (gammaOf z)‖ * ‖paperFT f (conj (gammaOf z))‖)
            = (‖multDiff Z emptyZeroConfig z‖ * ‖paperFT f (gammaOf z)‖) *
                ‖paperFT f (conj (gammaOf z))‖ := by ring
          _ ≤ (‖multDiff Z emptyZeroConfig z‖ * ‖paperFT f (gammaOf z)‖) * L :=
            mul_le_mul_of_nonneg_left hv (by positivity)
    · rw [if_neg hfar, norm_zero, fourierFarTerm, if_neg hfar, zero_mul]
  have hsNorm : Summable fun z => ‖(if R < |z.im - X| then
      multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖ :=
    (hs.mul_right L).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  refine ⟨hsNorm, ?_⟩
  calc ‖∑' z, (if R < |z.im - X| then
          multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖
      ≤ ∑' z, ‖(if R < |z.im - X| then
          multDiff Z emptyZeroConfig z * pointImage f f z else 0)‖ :=
        norm_tsum_le_tsum_norm hsNorm
    _ ≤ ∑' z, fourierFarTerm (multDiff Z emptyZeroConfig) f X R z * L :=
      hsNorm.tsum_le_tsum hbound (hs.mul_right L)
    _ = L ^ 2 := by rw [tsum_mul_right, sq]

/-- Subtracting two camera tests adds their absolute Fourier tails. -/
theorem fourier_far_tail_sub_le {c : ℂ → ℂ} {f g : ℝ → ℂ} {X R a : ℝ}
    (hf : ApertureWindow a f) (hg : ApertureWindow a g)
    (hfs : Summable (fourierFarTerm c f X R))
    (hgs : Summable (fourierFarTerm c g X R)) :
    Summable (fourierFarTerm c (fun t => f t - g t) X R) ∧
      (∑' z, fourierFarTerm c (fun t => f t - g t) X R z) ≤
        (∑' z, fourierFarTerm c f X R z) + ∑' z, fourierFarTerm c g X R z := by
  have hft (w : ℂ) : paperFT (fun t => f t - g t) w = paperFT f w - paperFT g w := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      paperFT_add_smul hf.1.continuous hf.hasCompactSupport hg.1.continuous
        hg.hasCompactSupport (-1) w
  have hle (z : ℂ) : fourierFarTerm c (fun t => f t - g t) X R z ≤
      fourierFarTerm c f X R z + fourierFarTerm c g X R z := by
    unfold fourierFarTerm
    split_ifs
    · rw [hft, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    · norm_num
  have hs := (hfs.add hgs).of_nonneg_of_le (fourierFarTerm_nonneg _ _ _ _) hle
  exact ⟨hs, (hs.tsum_le_tsum hle (hfs.add hgs)).trans_eq (hfs.tsum_add hgs)⟩

/-- Quarter-relative accuracy at opposite real Fourier values preserves the negative pair sign. -/
theorem re_pairImage_le_neg_sq_of_quarter_error {u v : ℂ} {δ : ℝ}
    (hu : ‖u - (δ : ℂ)‖ ≤ |δ| / 4)
    (hv : ‖v - (-δ : ℂ)‖ ≤ |δ| / 4) :
    (u * conj v).re ≤ -(7 / 16 : ℝ) * δ ^ 2 := by
  have hn : ‖(δ : ℂ)‖ = |δ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnn : ‖(-δ : ℂ)‖ = |δ| := by rw [norm_neg, hn]
  have he := norm_mul_conj_sub_le_of_rel (u := u) (v := v)
    (u₀ := (δ : ℂ)) (v₀ := (-δ : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by rw [hn]; linarith only [hu]) (by rw [hnn]; linarith only [hv])
  have hid : (δ : ℂ) * conj (-δ : ℂ) = -(δ : ℂ) ^ 2 := by
    rw [map_neg, Complex.conj_ofReal]
    ring
  rw [hid, hn, hnn] at he
  have hre := (Complex.re_le_norm (u * conj v - -(δ : ℂ) ^ 2)).trans he
  rw [Complex.sub_re, Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  nlinarith only [hre, sq_abs δ]

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.quadratic_far_tail_le_square
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.fourier_far_tail_sub_le
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.re_pairImage_le_neg_sq_of_quarter_error
