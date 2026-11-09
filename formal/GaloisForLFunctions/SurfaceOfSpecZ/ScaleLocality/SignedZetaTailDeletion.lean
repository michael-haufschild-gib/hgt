import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedInfiniteDeletion
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaTailDeletion
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.LogSquareWindowLeakage

/-!
# Complex deletion of the zeta tail

The phase 2π/3 uses two-thirds of the half-period shift. Existing ordinate
moments therefore bound every signed prefix. Total variation stays finite,
while a cofinite set of spline modes is annihilated exactly.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23 _root_.RHTower
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

def zetaSignedDeletionShift (n : ℕ) : ℝ := 2 / 3 * zetaDeletionShift n

theorem summable_zetaSignedDeletionShift_sq :
    Summable fun n => zetaSignedDeletionShift n ^ 2 := by
  apply (summable_zetaDeletionShift_sq.mul_left ((2 / 3 : ℝ) ^ 2)).congr
  intro n
  dsimp only [zetaSignedDeletionShift]
  ring

/-- An ordinate-indexed tail preserves a chosen exponent and deletes a cofinite spline spectrum. -/
theorem exists_signed_zeta_deletion_tail (α : ℝ) (w₀ : ℂ) :
    ∃ (M : ℕ) (S : Finset ℂ),
      (∏' n, signedDeletionFactor (zetaDeletionDepth α (n + M))
        (zetaSignedDeletionShift (n + M)) w₀) ≠ 0 ∧
      ∀ z ∉ S, evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0 →
        (∏' n, signedDeletionFactor (zetaDeletionDepth α (n + M))
          (zetaSignedDeletionShift (n + M)) (z - (α : ℂ))) = 0 := by
  classical
  obtain ⟨M, hkeep⟩ := exists_nonzero_signed_tail_multiplier
    (zetaDeletionDepth α) zetaSignedDeletionShift summable_zetaSignedDeletionShift_sq w₀
  let e := xiZeroCopyThermalEquiv
  let S : Finset ℂ := (Finset.range M).image fun n => ((e n).1 : ℂ) - 1 / 2
  have hsq : Summable fun n => zetaSignedDeletionShift (n + M) ^ 2 :=
    (summable_nat_add_iff M).mpr summable_zetaSignedDeletionShift_sq
  refine ⟨M, S, hkeep, ?_⟩
  intro z hz hcz
  have hρ : (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
    rcases mem_of_evenCoeff_ne_zero hcz with hz | hz
    · exact hz
    · have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, map_div₀, map_add, map_one]
      simpa only [map_add, hhalf, Complex.conj_conj] using conj_mem_zetaZeroConfig hz
  have hne1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro he
    have hr := hρ.2.2
    rw [he, Complex.one_re] at hr
    exact (lt_irrefl _ hr).elim
  have hxi := (xi_eq_zero_iff hρ.2.1 hne1).mpr hρ.1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  let n : ℕ := e.symm q
  have hen : ((e n).1 : ℂ) = (1 / 2 : ℂ) + z := by
    dsimp only [n]
    rw [e.apply_symm_apply, hq]
  have hM : M ≤ n := by
    by_contra hn
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_range.mpr (lt_of_not_ge hn), ?_⟩
    rw [hen]
    ring
  have ha : (z - (α : ℂ)).re = zetaDeletionDepth α (n - M + M) := by
    rw [Nat.sub_add_cancel hM]
    dsimp only [zetaDeletionDepth]
    change _ = ((e n).1 : ℂ).re - 1 / 2 - α
    rw [hen]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    norm_num
  have hp : zetaSignedDeletionShift (n - M + M) * (z - (α : ℂ)).im = 2 * Real.pi / 3 := by
    rw [Nat.sub_add_cancel hM]
    have him : zeroOrdinate (e n) = z.im := by
      dsimp only [zeroOrdinate]
      rw [hen]
      simp
    have hγ : z.im ≠ 0 := by rw [← him]; exact xiCopyOrdinate_ne_zero _
    change (2 / 3 * (Real.pi / zeroOrdinate (e n))) * (z - (α : ℂ)).im = 2 * Real.pi / 3
    rw [him]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [mul_assoc, div_mul_cancel₀ _ hγ]
    ring
  have he : (zetaDeletionDepth α (n - M + M) : ℂ) +
      ((z - (α : ℂ)).im : ℂ) * I = z - (α : ℂ) := by
    rw [← ha, Complex.re_add_im]
  have hk := tprod_signedDeletionFactor_root (fun k => zetaDeletionDepth α (k + M))
    (fun k => zetaSignedDeletionShift (k + M)) hsq (n - M) hp
  rwa [he] at hk

/-- Every deleted depth lies in the shifted critical strip. -/
theorem abs_zetaDeletionDepth_le (α : ℝ) (n : ℕ) :
    |zetaDeletionDepth α n| ≤ 1 / 2 + |α| := by
  have hs := xi_zero_re_mem_open_unit
    (xi_eq_zero_of_mem_divisor_support (xiZeroCopyThermalEquiv n).1)
  have hc : |((xiZeroCopyThermalEquiv n).1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith only [hs.1, hs.2]
  have htri : |((xiZeroCopyThermalEquiv n).1 : ℂ).re - 1 / 2 - α| ≤
      |((xiZeroCopyThermalEquiv n).1 : ℂ).re - 1 / 2| + |α| := by
    simpa only [Real.norm_eq_abs] using
      norm_sub_le (((xiZeroCopyThermalEquiv n).1 : ℂ).re - 1 / 2) α
  exact htri.trans (add_le_add hc le_rfl)

/-- The signed zeta kernels have finite total-variation cost. -/
theorem summable_zetaSignedVariation (α : ℝ) (M : ℕ) :
    Summable fun n => 3 / 2 *
      (zetaSignedDeletionShift (n + M) * zetaDeletionDepth α (n + M)) ^ 2 := by
  have hs := (summable_nat_add_iff M).mpr summable_zetaSignedDeletionShift_sq
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (hs.mul_right (3 / 2 * (1 / 2 + |α|) ^ 2))
  intro n
  have hd := mul_self_le_mul_self (abs_nonneg (zetaDeletionDepth α (n + M)))
    (abs_zetaDeletionDepth_le α (n + M))
  simp only [← sq, sq_abs] at hd
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 3 / 2 * zetaSignedDeletionShift (n + M) ^ 2 by positivity)
  calc
    _ = (3 / 2 * zetaSignedDeletionShift (n + M) ^ 2) *
        zetaDeletionDepth α (n + M) ^ 2 := by ring
    _ ≤ (3 / 2 * zetaSignedDeletionShift (n + M) ^ 2) * (1 / 2 + |α|) ^ 2 := hm
    _ = _ := by ring

/-- Smaller signed shifts spend no more than the established ordinate moment bound. -/
theorem zeta_signed_mixedMomentCost_le (α : ℝ) (M N : ℕ) (s : ℝ) {H : ℝ}
    (hH : Real.exp 12 ≤ H) :
    mixedMomentCost (filterPrefix (fun n => zetaDeletionDepth α (n + M))
      (fun n => zetaSignedDeletionShift (n + M)) N) s ≤ zetaMixedMomentBound H s := by
  apply le_trans _ (zeta_mixedMomentCost_le α M N s hH)
  rw [mixedMomentCost_filterPrefix, mixedMomentCost_filterPrefix]
  apply Finset.sum_le_sum
  intro n _
  apply min_le_min
  · rw [zetaSignedDeletionShift, mul_assoc, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    linarith only [abs_nonneg (zetaDeletionShift (n + M) * s)]
  · dsimp only [zetaSignedDeletionShift]
    nlinarith only [mul_nonneg (sq_nonneg s) (sq_nonneg (zetaDeletionShift (n + M)))]

/-- Signed deletion on a log-square window has bounded variation and vanishing leakage. -/
theorem infinite_signed_zeta_logSquare_norm {ι : Type*} (α : ℝ) (M : ℕ) (c w : ι → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hc : Summable fun i => ‖c i‖)
    (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) {K B T t : ℝ}
    (hK : 0 ≤ K) (hDT : D ≤ T) (hT : 3 ≤ T) (hheight : Real.exp 12 ≤ T)
    (hE : 1 ≤ Real.log (T + 2)) (hED : D + 1 ≤ Real.log (T + 2) ^ 2)
    (ht : |t| ≤ T + B)
    (hlocal : ∀ u, |u - t| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2 →
      ‖∑' i, c i * Complex.exp (w i * u)‖ ≤ K) :
    ‖∑' i, c i * (∏' n, signedDeletionFactor (zetaDeletionDepth α (n + M))
        (zetaSignedDeletionShift (n + M)) (w i)) * Complex.exp (w i * t)‖ ≤
      Real.exp (∑' n, 3 / 2 *
        (zetaSignedDeletionShift (n + M) * zetaDeletionDepth α (n + M)) ^ 2) *
        (K + 2 * (∑' i, ‖c i‖) * Real.exp (D * B - T)) := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hsq : Summable fun n => zetaSignedDeletionShift (n + M) ^ 2 :=
    (summable_nat_add_iff M).mpr summable_zetaSignedDeletionShift_sq
  have hmoment := zetaMixedMomentBound_le_logSquare hD hDT hT hE
  have hf := infinite_signed_tail_translated_norm
    (fun n => zetaDeletionDepth α (n + M)) (fun n => zetaSignedDeletionShift (n + M))
    hsq (summable_zetaSignedVariation α M) c w hD hc hw hK hT0
    (fun N => (zeta_signed_mixedMomentCost_le α M N (D + T) hheight).trans hmoment) hlocal
  have harg : D * |t| - T * (zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2) +
      zetaLogSquareMomentConstant * T * Real.log (T + 2) ^ 2 ≤ D * B - T := by
    have hh := mul_le_mul_of_nonneg_left ht hD
    have he := mul_le_mul_of_nonneg_right hED hT0
    unfold zetaLogSquareRadius
    nlinarith only [hh, he]
  exact hf.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
      (by positivity))) (Real.exp_pos _).le)

#print axioms exists_signed_zeta_deletion_tail
#print axioms infinite_signed_zeta_logSquare_norm

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
