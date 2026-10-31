import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.RadiusHeadHeatPositivity

/-!
# Heat repair from the local depth and the local count

At a height `t` with `Ξ(t) ≠ 0`, write `δ` for the largest depth `|Re ρ − ½|` of the zeros with
`|Im ρ − t| < ½`, and `N(t, R)` for the number of zero copies within distance `R` of `½ + it`.

**Theorem** (`xiSliceHeatTransfer_nonneg_of_depth_count`).  If `R ≥ 0`, `R² ≥ 2δ²` and `64R² ≤ λ N(t, R)`,
then every heated slice coefficient `T_n(λ, 0, t)` is nonnegative.

With `R = √2 δ` the repair heat is `128δ²/N(t, √2δ)`: `≍ δ/log t` when the zeros near `t` have the
mean density `log t/2π`, `≍ δ²/log t` when `≍ log t` zeros sit within `√2δ` of `½ + it`, and at most
`128δ²` in every case.  This is the converse of detection: an off-line zero of depth `δ` at height
`t` makes some coefficient negative at every heat `λ ≤ δ²/(200 log t)`
(`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic`), and at heat `λ ≤ δ/(96(c+1) log t)` under
regular growth.  The local heat threshold is `depth²/local count` up to constants on both sides.

Proof.  Split the slice into the radius-`R` head and its tail (`sliceTruncPoly_eq_head_mul_sdiff`).
The head has `N(t, R)` roots in the disc of radius `R²` (in `x²`), so heat `λ/2 ≥ 32R²/N(t, R)`
repairs it (`coeffNonneg_heat_sliceTruncPoly_radiusHead`).  A tail copy is either at horizontal
distance `≥ ½`, where its depth `< ½` puts it outside the cone, or within `½`, where its depth is
`≤ δ` and its distance `> R ≥ √2 δ` again puts it outside the cone
(`im_sq_le_of_not_mem_radiusHead_of_depth`).  Outside the cone each pair factor is heat-positive
(`coeffNonneg_forwardPolyHeat_slicePair`), and heat positivity is closed under products.
-/

open Complex Filter Topology Polynomial
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticLocalDivisorGeometry
open RHTower.XiAtlasFinitePart

namespace RHTower.DeBruijn

noncomputable section

/-- **Tail copies are outside the cone.**  If every copy with `|Re z − t| < ½` has `(Im z)² ≤ δ²`
and `0 ≤ R`, `2δ² ≤ R²`, every copy outside the radius-`R` head satisfies `(Im z)² ≤ (Re z − t)²`. -/
theorem im_sq_le_of_not_mem_radiusHead_of_depth {t R δ : ℝ} (hR : 0 ≤ R) (hδR : 2 * δ ^ 2 ≤ R ^ 2)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    {q : XiZeroCopy} (hq : q ∉ xiSliceGaussianRadiusHead t R) :
    (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
  rw [mem_xiSliceGaussianRadiusHead, not_le] at hq
  have hnorm : R ^ 2 < ((xiSpectralPoint q).re - t) ^ 2 + (xiSpectralPoint q).im ^ 2 := by
    rw [← sq_norm_sub_ofReal]
    exact pow_lt_pow_left₀ hq hR two_ne_zero
  have h4 := xiSpectralPoint_im_sq_lt_quarter q
  by_cases hfar : 1 / 2 ≤ |(xiSpectralPoint q).re - t|
  · have hsq : (1 / 2 : ℝ) ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
      rw [← sq_abs ((xiSpectralPoint q).re - t)]
      exact pow_le_pow_left₀ (by norm_num) hfar 2
    linarith
  · push Not at hfar
    have hd := hdepth q hfar
    linarith

/-- **Heat positivity of the tail under a local depth bound.** -/
theorem coeffNonneg_forwardPolyHeat_sliceTruncPoly_sdiff_of_depth {t s R δ : ℝ} (ht : XiC t ≠ 0)
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hδR : 2 * δ ^ 2 ≤ R ^ 2)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    (S : Finset XiZeroCopy) :
    CoeffNonneg (forwardPolyHeat s
      (expand ℝ 2 (sliceTruncPoly t (S \ xiSliceGaussianRadiusHead t R)))) := by
  classical
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_forwardPolyHeat_mul hs
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q _ => ?_)
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q hq => ?_)
  · exact coeffNonneg_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity)
  · have hnotMem : q ∉ xiSliceGaussianRadiusHead t R :=
      (Finset.mem_sdiff.mp (mem_sliceTruncUp.mp hq).1).2
    have hcone := im_sq_le_of_not_mem_radiusHead_of_depth hR hδR hdepth hnotMem
    exact coeffNonneg_forwardPolyHeat_slicePair hs (xiSpectralPoint_ne_ofReal ht q)
      (by linarith)

/-- **Heat repair from the local depth and the local count.**  Let `Ξ(t) ≠ 0`, `λ > 0`, and suppose
every zero copy with `|Re z − t| < ½` has `(Im z)² ≤ δ²` (depth `≤ δ` within `½` of the height `t`).
If `0 ≤ R`, `2δ² ≤ R²` and `64R² ≤ λ N(t, R)`, where `N(t, R)` is the number of copies within distance `R` of
`t`, then `T_n(λ, 0, t) ≥ 0` for every `n`. -/
theorem xiSliceHeatTransfer_nonneg_of_depth_count {lam t R δ : ℝ} (hlam : 0 < lam)
    (ht : XiC t ≠ 0) (hR : 0 ≤ R) (hδR : 2 * δ ^ 2 ≤ R ^ 2)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    (hcount : 64 * R ^ 2 ≤ lam * (xiSliceGaussianRadiusHead t R).card) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  classical
  have hs : 0 < lam / 2 := by positivity
  have hhead : CoeffNonneg (forwardPolyHeat (lam / 2)
      (expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))) :=
    coeffNonneg_heat_sliceTruncPoly_radiusHead ht hs (by linarith)
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
  · set H := xiSliceGaussianRadiusHead t R
    have hev : ∀ᶠ S : Finset XiZeroCopy in atTop,
        0 ≤ (((forwardPolyHeat (lam / 2) (expand ℝ 2 (sliceTruncPoly t S))).coeff (2 * l) : ℝ)
          : ℂ) := by
      filter_upwards [eventually_ge_atTop H] with S hHS
      rw [sliceTruncPoly_eq_head_mul_sdiff t hHS, map_mul]
      exact Complex.zero_le_real.mpr
        ((coeffNonneg_forwardPolyHeat_mul hs.le hhead
          (coeffNonneg_forwardPolyHeat_sliceTruncPoly_sdiff_of_depth ht hs.le hR hδR hdepth S))
            (2 * l))
    have hq : 0 ≤ xiSliceHeatTransfer lam 0 t (2 * l) / xiHorizontalPair t 0 :=
      ge_of_tendsto (tendsto_coeff_forwardPolyHeat_sliceTruncPoly hlam.le ht l) hev
    rw [← mul_div_cancel₀ (xiSliceHeatTransfer lam 0 t (2 * l)) (xiHorizontalPair_zero_ne ht)]
    refine mul_nonneg ?_ hq
    rw [xiHorizontalPair_zero_eq_ofReal]
    exact Complex.zero_le_real.mpr (sq_nonneg _)
  · rw [xiSliceHeatTransfer_odd_eq_zero hlam.le]

/-- **The count-free bound.**  Under the depth hypothesis, heat `λ ≥ 128δ²` repairs the slice
whenever the radius-`√2δ` head contains a copy; in general `λ ≥ 64R²/N(t, R)`. -/
theorem xiSliceHeatTransfer_nonneg_of_depth_of_card_pos {lam t δ : ℝ} (hlam : 0 < lam)
    (ht : XiC t ≠ 0) (hδ : 0 ≤ δ)
    (hdepth : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re - t| < 1 / 2 →
      (xiSpectralPoint q).im ^ 2 ≤ δ ^ 2)
    (hcard : 0 < (xiSliceGaussianRadiusHead t (Real.sqrt 2 * δ)).card)
    (hlamδ : 128 * δ ^ 2 ≤ lam) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam 0 t n := by
  have hR2 : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  refine xiSliceHeatTransfer_nonneg_of_depth_count hlam ht (by positivity) hR2.ge hdepth ?_ n
  rw [hR2]
  have h1 : (1 : ℝ) ≤ (xiSliceGaussianRadiusHead t (Real.sqrt 2 * δ)).card := by
    exact_mod_cast hcard
  nlinarith

end

end RHTower.DeBruijn

