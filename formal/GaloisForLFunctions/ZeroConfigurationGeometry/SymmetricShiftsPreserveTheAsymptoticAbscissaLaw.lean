import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator
import GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation

/-!+# Symmetric shifts preserve the asymptotic abscissa law

The zeros of `F(s+a)F(s-a)` are the two real translates of the zeros of `F`.
For `a≥0`, both a global right bound and a right bound beyond any fixed height
move by exactly `a`. Thus symmetric shifts preserve the implication from
eventual bounds to global bounds. For `ξ`, this implication is precisely AAL;
Hardy's critical-line zeros handle thresholds below `1/2`.
-/

set_option autoImplicit false

open Complex Set RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- Real translation preserves heights; the rightmost translated copy determines every bound. -/
theorem symmetricShiftProduct_heightBound_iff {F : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (σ T : ℝ) :
    (∀ z : ℂ, symmetricShiftProduct F a z = 0 → T ≤ |z.im| → z.re ≤ σ) ↔
      ∀ z : ℂ, F z = 0 → T ≤ |z.im| → z.re ≤ σ - a := by
  constructor
  · intro h z hz hT
    have hb := h (z + (a : ℂ)) (symmetricShiftProduct_zero_translates F a hz).1
      (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hT)
    simp only [Complex.add_re, Complex.ofReal_re] at hb
    linarith only [hb]
  · intro h z hz hT
    rcases mul_eq_zero.mp hz with hplus | hminus
    · have hb := h (z + (a : ℂ)) hplus
        (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hT)
      simp only [Complex.add_re, Complex.ofReal_re] at hb
      linarith only [ha, hb]
    · have hb := h (z - (a : ℂ)) hminus
        (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hT)
      simp only [Complex.sub_re, Complex.ofReal_re] at hb
      linarith only [hb]

/-- The global zero bound moves by the same amount as each high-height bound. -/
theorem symmetricShiftProduct_globalBound_iff {F : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (σ : ℝ) :
    (∀ z : ℂ, symmetricShiftProduct F a z = 0 → z.re ≤ σ) ↔
      ∀ z : ℂ, F z = 0 → z.re ≤ σ - a := by
  constructor
  · intro h z hz
    exact (symmetricShiftProduct_heightBound_iff ha σ 0).mp
      (fun w hw _ => h w hw) z hz (abs_nonneg _)
  · intro h z hz
    exact (symmetricShiftProduct_heightBound_iff ha σ 0).mpr
      (fun w hw _ => h w hw) z hz (abs_nonneg _)

theorem symmetricShiftProduct_eventualBound_iff {F : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (σ : ℝ) :
    (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
      symmetricShiftProduct F a z = 0 → T ≤ |z.im| → z.re ≤ σ) ↔
      ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, F z = 0 → T ≤ |z.im| → z.re ≤ σ - a := by
  simp_rw [symmetricShiftProduct_heightBound_iff ha]

/-- Symmetric shifts neither create nor remove a gap between eventual and global zero bounds. -/
theorem symmetricShiftProduct_eventualToGlobal_iff {F : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a) :
    (∀ σ : ℝ, (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
      symmetricShiftProduct F a z = 0 → T ≤ |z.im| → z.re ≤ σ) →
        ∀ z : ℂ, symmetricShiftProduct F a z = 0 → z.re ≤ σ) ↔
      ∀ σ : ℝ, (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        F z = 0 → T ≤ |z.im| → z.re ≤ σ) → ∀ z : ℂ, F z = 0 → z.re ≤ σ := by
  constructor
  · intro h σ hσ
    have htail : ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        symmetricShiftProduct F a z = 0 → T ≤ |z.im| → z.re ≤ σ + a := by
      apply (symmetricShiftProduct_eventualBound_iff ha (σ + a)).mpr
      simpa only [add_sub_cancel_right] using hσ
    have hb := (symmetricShiftProduct_globalBound_iff ha (σ + a)).mp (h (σ + a) htail)
    simpa only [add_sub_cancel_right] using hb
  · intro h σ hσ
    apply (symmetricShiftProduct_globalBound_iff ha σ).mpr
    exact h (σ - a) ((symmetricShiftProduct_eventualBound_iff ha σ).mp hσ)

/-- Hardy's unbounded critical-line zeros forbid an eventual bound below `1/2`. -/
theorem half_le_of_xi_eventualBound {σ : ℝ}
    (h : ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, xi z = 0 → T ≤ |z.im| → z.re ≤ σ) :
    1 / 2 ≤ σ := by
  obtain ⟨T, hT, hbound⟩ := h
  obtain ⟨t, ht, hzero⟩ := exists_Xi_zero_gt T
  have hxi : xi ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
    rw [xi_eq_XiC_comp]
    have he : (((1 / 2 : ℂ) + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp only [Complex.I_sq, mul_neg, mul_one, neg_neg]
    rw [he, XiC_ofReal, hzero]
    simp only [Complex.ofReal_zero]
  have him : ((1 / 2 : ℂ) + (t : ℂ) * I).im = t := by simp
  have hb := hbound _ hxi (by rw [him, abs_of_pos (hT.trans ht)]; exact ht.le)
  simpa using hb

/-- The usual finite-tail formulation of AAL is exactly eventual-to-global rigidity for `ξ`. -/
theorem asymptoticAbscissaLaw_iff_xi_eventualToGlobal :
    AsymptoticAbscissaLaw ↔ ∀ σ : ℝ,
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, xi z = 0 → T ≤ |z.im| → z.re ≤ σ) →
        ∀ z : ℂ, xi z = 0 → z.re ≤ σ := by
  constructor
  · intro hA σ hσ z hz
    have hhalf := half_le_of_xi_eventualBound hσ
    obtain ⟨T, hT, hbound⟩ := hσ
    have hmem : σ ∈ zetaAsymptoticAbscissaSet :=
      mem_zetaAsymptoticAbscissaSet_iff_eventually_height.mpr
        ⟨hhalf, T, hT, fun q hq => hbound _ (xi_xiZeroCopy_eq_zero q) hq⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
    have he : (1 / 2 : ℝ) + (σ - 1 / 2) = σ := by ring
    have hfin : {q : XiZeroCopy | 1 / 2 + (σ - 1 / 2) < (q.1 : ℂ).re}.Finite := by
      simpa only [he] using hmem.2
    have hb := hA (σ - 1 / 2) (by linarith only [hhalf]) hfin q
    simpa only [he, hq] using hb
  · intro hA h hh hfin q
    have hmem : 1 / 2 + h ∈ zetaAsymptoticAbscissaSet :=
      ⟨by linarith only [hh], hfin⟩
    obtain ⟨_, T, hT, hbound⟩ :=
      mem_zetaAsymptoticAbscissaSet_iff_eventually_height.mp hmem
    apply hA (1 / 2 + h) ?_ _ (xi_xiZeroCopy_eq_zero q)
    refine ⟨T, hT, fun z hz hheight => ?_⟩
    obtain ⟨r, hr⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
    simpa only [hr] using hbound r (by simpa only [hr] using hheight)

/-- The symmetric shifted product satisfies the zero-bound form of AAL exactly when `ζ` does. -/
theorem asymptoticAbscissaLaw_iff_symmetricShift_eventualToGlobal {a : ℝ} (ha : 0 ≤ a) :
    AsymptoticAbscissaLaw ↔ ∀ σ : ℝ,
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        symmetricShiftProduct xi a z = 0 → T ≤ |z.im| → z.re ≤ σ) →
          ∀ z : ℂ, symmetricShiftProduct xi a z = 0 → z.re ≤ σ :=
  asymptoticAbscissaLaw_iff_xi_eventualToGlobal.trans
    (symmetricShiftProduct_eventualToGlobal_iff ha).symm

end
end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.asymptoticAbscissaLaw_iff_symmetricShift_eventualToGlobal
