import GaloisForLFunctions.RHTower.XiLevinsonPortCriticalResonances
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# The defects of the canonical producer sit in off-line shadows

For `λ > 0` the canonical PTR producer is `ξ − λξ'` (the Levinson port `Ξ + iλΞ'` in the variable
`s = ½ + iz`). Its zeros left of the critical line are its defects.

**Theorem** (`exists_offLine_shadow_of_levinson_defect`). If `ξ(s) − λξ'(s) = 0` with
`Re s < ½`, then some zero `ρ = β + iγ` of `ξ` with `β ≠ ½` satisfies
`(½ − Re s)² + (Im s − γ)² ≤ (β − ½)²`. So `s` lies in the closed disk of radius `|β − ½|` centred at
`½ + iγ`: the shadow of an off-line zero.

**Proof.** This is the mirror image of the corpus theorem
`exists_xi_zero_disk_of_xiHermiteBiehler_eq_zero` (right zeros of `ξ + λξ'` lie in Speiser disks).
The reflection `s ↦ 1 − s̄` carries `ξ − λξ'` to the conjugate of `ξ + λξ'`. The disk has positive
radius `½ − Re s`, so its zero is off the line.

**Corollaries.**
* `levinson_no_defect_of_shadowFree`: the producer is lossless at every ordinate outside the
  off-line shadows. The defect locus is local.
* `one_div_hundred_log_le_re_of_levinson_defect`: with the explicit zero-free region
  `β ≤ 1 − 1/(100 log γ)`, every defect with `Im s ≥ 5` has
  `Re s ≥ 1/(100 log(Im s + ½))`. The defects stay within depth `½ − 1/(100 log)` of the line.
-/

noncomputable section

open Complex

namespace RHTower

/-- **Defects of `ξ − λξ'` lie in off-line shadows.** -/
theorem exists_offLine_shadow_of_levinson_defect {lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : xi s - (lam : ℂ) * deriv xi s = 0) (hre : s.re < 1 / 2) :
    ∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 ∧
      (1 / 2 - s.re) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2 ≤ ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  -- the mirror point is a right zero of the Hermite–Biehler partner `ξ + λξ'`
  set s' : ℂ := 1 - (starRingEnd ℂ) s with hs'
  have hre' : 1 / 2 < s'.re := by simp [hs']; linarith
  have hV : xiHermiteBiehler lam s' = 0 := by
    have e : xiHermiteBiehler lam s' = (starRingEnd ℂ) (xi s - (lam : ℂ) * deriv xi s) := by
      rw [xiHermiteBiehler, hs', xi_one_sub, xi_conj, deriv_xi_one_sub, deriv_xi_conj]
      simp [map_sub, map_mul, Complex.conj_ofReal]
      ring
    rw [e, hs, map_zero]
  obtain ⟨ρ, hρ, hdisk⟩ := exists_xi_zero_disk_of_xiHermiteBiehler_eq_zero hlam hre' hV
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have e1 : s'.re - 1 / 2 = 1 / 2 - s.re := by simp [hs']; ring
  have e2 : s'.im = s.im := by simp [hs']
  rw [e1, e2] at hdisk
  refine ⟨q, fun h => ?_, by rw [hq]; exact hdisk⟩
  rw [hq] at h
  rw [h, sub_self] at hdisk
  have hpos : 0 < 1 / 2 - s.re := by linarith
  nlinarith [sq_nonneg (s.im - ρ.im), mul_pos hpos hpos]

/-- **The producer is lossless outside the off-line shadows.** If no off-line zero of `ξ` has its
shadow disk reaching the point `s` with `Re s < ½`, then `s` is not a defect. -/
theorem levinson_no_defect_of_shadowFree {lam : ℝ} (hlam : 0 < lam) {s : ℂ} (hre : s.re < 1 / 2)
    (hfree : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < (1 / 2 - s.re) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2) :
    xi s - (lam : ℂ) * deriv xi s ≠ 0 := by
  intro hs
  obtain ⟨q, hq, hle⟩ := exists_offLine_shadow_of_levinson_defect hlam hs hre
  exact absurd hle (not_le.mpr (hfree q hq))

/-- **Horizon descent for the canonical producer.** Every defect `s` of `ξ − λξ'` with
`Im s ≥ 5` satisfies `Re s ≥ 1/(100 log(Im s + ½))`. -/
theorem one_div_hundred_log_le_re_of_levinson_defect {lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : xi s - (lam : ℂ) * deriv xi s = 0) (hre : s.re < 1 / 2) (him : 5 ≤ s.im) :
    1 / 100 / Real.log (s.im + 1 / 2) ≤ s.re := by
  obtain ⟨q, hq, hle⟩ := exists_offLine_shadow_of_levinson_defect hlam hs hre
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  -- the shadow radius dominates both the depth and the ordinate offset
  have hpos : 0 < 1 / 2 - s.re := by linarith
  have hdepth : 1 / 2 - s.re ≤ |β - 1 / 2| := by
    rw [← Real.sqrt_sq hpos.le, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (s.im - γ)])
  have hoff : |s.im - γ| ≤ |β - 1 / 2| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 / 2 - s.re)])
  -- zeros of `ξ` have `0 < β < 1`, so `|β − ½| < ½`
  have hstrip : |β - 1 / 2| < 1 / 2 := by
    have h1 := xiSpectralPoint_im_mem_openHalf q
    have hsp : (xiSpectralPoint q).im = β - 1 / 2 ∨ (xiSpectralPoint q).im = 1 / 2 - β := by
      simp [xiSpectralPoint, hβ]
    rcases hsp with h | h <;> rw [abs_lt] <;> constructor <;> linarith [h1.1, h1.2]
  have hγ4 : 4 ≤ γ := by
    have := (abs_le.mp (hoff.trans hstrip.le)).2
    linarith [(abs_le.mp hoff).1, (abs_le.mp hoff).2, hstrip]
  have hγle : γ ≤ s.im + 1 / 2 := by
    linarith [(abs_le.mp (hoff.trans hstrip.le)).1]
  -- the zero-free region for the zero or its mirror
  have hzf : |β - 1 / 2| ≤ 1 / 2 - 1 / 100 / Real.log γ := by
    rcases le_or_gt (1 / 2) β with hb | hb
    · have := xiZeroCopy_zero_free_from_four (q := q) hγ4
      rw [abs_of_nonneg (by linarith)]
      linarith
    · -- the mirror zero `1 − ρ̄` has real part `1 − β` and the same ordinate
      have hmir : xi (1 - (starRingEnd ℂ) (q.1 : ℂ)) = 0 := by
        rw [xi_one_sub, xi_conj, xi_xiZeroCopy_eq_zero, map_zero]
      obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_xi_eq_zero hmir
      have hre' : (q'.1 : ℂ).re = 1 - β := by rw [hq']; simp [hβ]
      have him' : (q'.1 : ℂ).im = γ := by rw [hq']; simp [hγ]
      have := xiZeroCopy_zero_free_from_four (q := q') (by rw [him']; exact hγ4)
      rw [hre', him'] at this
      rw [abs_of_neg (by linarith)]
      linarith
  have hlogγ : 0 < Real.log γ := Real.log_pos (by linarith)
  have hlogle : Real.log γ ≤ Real.log (s.im + 1 / 2) := Real.log_le_log (by linarith) hγle
  have hdiv : 1 / 100 / Real.log (s.im + 1 / 2) ≤ 1 / 100 / Real.log γ :=
    div_le_div_of_nonneg_left (by norm_num) hlogγ hlogle
  linarith

end RHTower
