import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureThreeCenterSharpQuantum
import GaloisForLFunctions.RHTower.LiRemoteQuartetPhaseAlignment
import GaloisForLFunctions.RHTower.GaussTwoPieceL2Bound

/-!
# Uniform full-lattice charge of one HCF divisor point

The local HCF lower bound charges off-line zeros.  To combine it with zero density one also needs an
upper bound independent of the zero's ordinate and of the finite feature window.  A nearest-integer
split majorizes every translated critical feature by one fixed quartic lattice weight.  Translation
invariance and summability of that weight then give one absolute full-lattice constant.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Fixed quartic lattice majorant centered at `j`. -/
def criticalFeatureQuarticLatticeMajorant (j k : ℤ) : ℝ :=
  1024 / (1 + ((j - k).natAbs : ℝ)) ^ (4 : ℕ)

theorem criticalFeatureQuarticLatticeMajorant_nonneg (j k : ℤ) :
    0 ≤ criticalFeatureQuarticLatticeMajorant j k := by
  exact div_nonneg (by norm_num) (pow_nonneg (by positivity) _)

/-- The strip condition gives a denominator lower bound with quartic decay in horizontal distance. -/
theorem quartic_lower_le_criticalFeatureDenominatorNormSq
    (t : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (3 / 4 + (z.re - t) ^ 2) ^ 2 ≤ criticalFeatureDenominatorNormSq t z := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [y] using hz)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hbase : 0 ≤ 3 / 4 + u ^ 2 := by positivity
  have hlinear : 3 / 4 + u ^ 2 ≤ 1 + u ^ 2 - y ^ 2 := by
    nlinarith
  have hsq : (3 / 4 + u ^ 2) ^ 2 ≤ (1 + u ^ 2 - y ^ 2) ^ 2 :=
    (sq_le_sq₀ hbase (hbase.trans hlinear)).2 hlinear
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hsq ⊢
  exact hsq.trans (le_add_of_nonneg_right (sq_nonneg _))

/-- Every critical feature is bounded by the same translated quartic weight around the nearest
integer to the spectral ordinate. -/
theorem normSq_criticalFeatureCauchyKernelTest_le_quarticLatticeMajorant
    (k : ℤ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z) ≤
      criticalFeatureQuarticLatticeMajorant (nearestInteger z.re) k := by
  let j : ℤ := nearestInteger z.re
  let u : ℝ := z.re - (k : ℝ)
  have hj : |z.re - (j : ℝ)| ≤ 1 / 2 := by
    simpa [j, abs_sub_comm] using abs_nearestInteger_sub_le_half z.re
  have hden := quartic_lower_le_criticalFeatureDenominatorNormSq (k : ℝ) hz.le
  have hbase : 0 < 3 / 4 + u ^ 2 := by positivity
  have hamp : Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z) ≤
      4 / (3 / 4 + u ^ 2) ^ 2 := by
    rw [normSq_criticalFeatureCauchyKernelTest_eq_four_div (k : ℝ) hz]
    dsimp only [u] at hden ⊢
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hbase) hden
  by_cases hkj : k = j
  · subst k
    have hcentralDen : (9 / 16 : ℝ) ≤ (3 / 4 + u ^ 2) ^ 2 := by
      have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hbase.le).2
        (by nlinarith [sq_nonneg u] : (3 / 4 : ℝ) ≤ 3 / 4 + u ^ 2)
      norm_num at h ⊢
      exact h
    have hcentral : Complex.normSq (criticalFeatureCauchyKernelTest (j : ℝ) z) ≤
        64 / 9 := by
      calc
        Complex.normSq (criticalFeatureCauchyKernelTest (j : ℝ) z)
            ≤ 4 / (3 / 4 + u ^ 2) ^ 2 := hamp
        _ ≤ 4 / (9 / 16) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hcentralDen
        _ = 64 / 9 := by norm_num
    dsimp [criticalFeatureQuarticLatticeMajorant, j]
    simp only [sub_self, Int.natAbs_zero, Nat.cast_zero, add_zero]
    norm_num [Real.one_rpow]
    exact hcentral.trans (by norm_num)
  · have hm : j - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkj)
    have hmNat : 1 ≤ (j - k).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm)
    have hmReal : (1 : ℝ) ≤ ((j - k).natAbs : ℝ) := by exact_mod_cast hmNat
    have hmAbs : |(((j - k : ℤ) : ℝ))| = ((j - k).natAbs : ℝ) := by
      symm
      exact natAbs_cast_eq_abs (j - k)
    have htriangle : |(((j - k : ℤ) : ℝ))| ≤ |u| + |z.re - (j : ℝ)| := by
      have heq : (((j - k : ℤ) : ℝ)) = u - (z.re - (j : ℝ)) := by
        dsimp only [u]
        push_cast
        ring
      rw [heq]
      exact abs_sub _ _
    have hm_le_two_u : ((j - k).natAbs : ℝ) ≤ 2 * |u| := by
      rw [hmAbs] at htriangle
      nlinarith
    have hscale : 1 + ((j - k).natAbs : ℝ) ≤ 4 * |u| := by
      nlinarith
    have hu : 0 < |u| := by nlinarith
    have hu4 : 0 < u ^ 4 := by
      have hu0 : u ≠ 0 := by
        intro hu0
        rw [hu0, abs_zero] at hu
        exact lt_irrefl 0 hu
      rw [show u ^ 4 = (u ^ 2) ^ 2 by ring]
      positivity
    have hquarticDen : u ^ 4 ≤ (3 / 4 + u ^ 2) ^ 2 := by
      nlinarith [sq_nonneg u]
    have hampTail : Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z) ≤
        4 / u ^ 4 := by
      exact hamp.trans
        (div_le_div_of_nonneg_left (by norm_num) hu4 hquarticDen)
    have hscale4 : (1 + ((j - k).natAbs : ℝ)) ^ 4 ≤ (4 * |u|) ^ 4 := by
      gcongr
    have hscale4' :
        (1 + ((j - k).natAbs : ℝ)) ^ 4 ≤ 256 * u ^ 4 := by
      calc
        (1 + ((j - k).natAbs : ℝ)) ^ 4 ≤ (4 * |u|) ^ 4 := hscale4
        _ = 256 * u ^ 4 := by
          have hu4non : 0 ≤ u ^ 4 := by positivity
          rw [mul_pow, show |u| ^ 4 = u ^ 4 by
            rw [← abs_pow, abs_of_nonneg hu4non]]
          norm_num
    have hfrac : 4 / u ^ 4 ≤
        1024 / (1 + ((j - k).natAbs : ℝ)) ^ 4 := by
      rw [div_le_div_iff₀ hu4 (by positivity)]
      nlinarith [hscale4']
    simpa [criticalFeatureQuarticLatticeMajorant, j] using hampTail.trans hfrac

/-- Every finite integer feature window has one absolute per-zero charge ceiling. -/
theorem sum_normSq_criticalFeatureCauchyKernelTest_le_uniformLatticeCharge
    (K : Finset ℤ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    ∑ k ∈ K, Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z) ≤
      1024 * intNatAbsPowTotal 4 := by
  let j : ℤ := nearestInteger z.re
  have hweight : Summable (fun k : ℤ => criticalFeatureQuarticLatticeMajorant j k) := by
    have hbase := summable_one_div_one_add_natAbs_rpow (s := (4 : ℝ)) (by norm_num)
    have hshift := hbase.comp_injective (Equiv.subLeft j).injective
    have hshift' : Summable
        (fun k : ℤ => 1 / (1 + (((j - k : ℤ)).natAbs : ℝ)) ^ (4 : ℝ)) := by
      simpa [Function.comp_def] using hshift
    simpa [criticalFeatureQuarticLatticeMajorant, Real.rpow_natCast,
      div_eq_mul_inv] using hshift'.mul_left 1024
  have hfinite :
      ∑ k ∈ K, Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z) ≤
        ∑ k ∈ K, criticalFeatureQuarticLatticeMajorant j k := by
    exact Finset.sum_le_sum fun k _ =>
      normSq_criticalFeatureCauchyKernelTest_le_quarticLatticeMajorant k hz
  have hpartial :
      ∑ k ∈ K, criticalFeatureQuarticLatticeMajorant j k ≤
        ∑' k : ℤ, criticalFeatureQuarticLatticeMajorant j k :=
    hweight.sum_le_tsum K (fun k _ => criticalFeatureQuarticLatticeMajorant_nonneg j k)
  have htranslate :
      (∑' k : ℤ, 1 / (1 + (((j - k : ℤ)).natAbs : ℝ)) ^ (4 : ℕ)) =
        intNatAbsPowTotal 4 := by
    rw [intNatAbsPowTotal]
    simpa [Real.rpow_natCast] using (Equiv.subLeft j).tsum_eq
      (fun m : ℤ => 1 / (1 + (m.natAbs : ℝ)) ^ (4 : ℝ))
  calc
    ∑ k ∈ K, Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) z)
        ≤ ∑ k ∈ K, criticalFeatureQuarticLatticeMajorant j k := hfinite
    _ ≤ ∑' k : ℤ, criticalFeatureQuarticLatticeMajorant j k := hpartial
    _ = 1024 * ∑' k : ℤ,
          1 / (1 + (((j - k : ℤ)).natAbs : ℝ)) ^ (4 : ℕ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [criticalFeatureQuarticLatticeMajorant]
      ring
    _ = 1024 * intNatAbsPowTotal 4 := by rw [htranslate]

end

end RHTower
