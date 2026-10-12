import GaloisForLFunctions.RHTower.LindelofOpenImpliesCriticalLine
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum

/-!
# Quasi-RH as a sub-half threshold of the cosine family

For `h > 0` let `A^h = cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2`. Quasi-RH is the statement that all zeros
of `ξ` satisfy `Re ρ ≤ ½ + α` for some `α < ½` (`XiZeroHalfPlaneBound α`).

**Theorem** (`exists_cosShiftXi_real_lt_half_iff_quasiRH`). Under the Lindelöf hypothesis,
quasi-RH holds if and only if `A^h` has only real zeros for some `0 < h < ½`.

The forward direction is unconditional (`exists_cosShiftXi_real_lt_half_of_quasiRH`): a strip
`|β − ½| ≤ α < h` makes `A^h` real-rooted (de Bruijn). For the converse, LH and real-rootedness of
`A^h` give `|β − ½| ≤ h + ε` at large height (`eventually_strip_of_lindelofCriticalLine`). Each zero
has `|β − ½| < ½`, so the finitely many low zeros stay inside a strip of some width `< ½`
(`exists_spectral_im_bound_of_re_le`).
-/

open Complex

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- Every zero copy lies strictly inside the critical strip: `|Im z| = |½ − β| < ½`. -/
theorem abs_spectral_im_lt_half (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 / 2 := by
  rw [spectral_im_eq, abs_lt]
  constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]

/-- The zero copies of bounded ordinate stay inside a strip of width `< ½`. -/
theorem exists_spectral_im_bound_of_re_le (T : ℝ) :
    ∃ Δ : ℝ, Δ < 1 / 2 ∧ ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ T →
      |(xiSpectralPoint q).im| ≤ Δ := by
  classical
  set m : ℕ := ⌈T + 1⌉₊ with hm
  set s := xiZeroBall m with hs
  have hmem : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ T → q ∈ s := by
    intro q hq
    rw [hs, mem_xiZeroBall]
    have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have h2 := abs_spectral_im_lt_half q
    have h3 : T + 1 ≤ (m : ℝ) := Nat.le_ceil _
    linarith
  rcases s.eq_empty_or_nonempty with he | hne
  · refine ⟨0, by norm_num, fun q hq => ?_⟩
    have := hmem q hq
    rw [he] at this
    exact absurd this (Finset.notMem_empty q)
  · obtain ⟨q₀, -, hq₀⟩ := s.exists_max_image (fun q => |(xiSpectralPoint q).im|) hne
    exact ⟨|(xiSpectralPoint q₀).im|, abs_spectral_im_lt_half q₀,
      fun q hq => hq₀ q (hmem q hq)⟩

/-- Quasi-RH bounds every zero copy on both sides of the line. -/
theorem abs_spectral_im_le_of_halfPlaneBound {α : ℝ} (hα : XiZeroHalfPlaneBound α)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ α := by
  have hz : xi (q.1 : ℂ) = 0 := xi_xiZeroCopy_eq_zero q
  have h1 := hα _ hz
  have h2 := hα (1 - (q.1 : ℂ)) (by rw [xi_one_sub]; exact hz)
  rw [Complex.sub_re, Complex.one_re] at h2
  rw [spectral_im_eq, abs_le]
  constructor <;> linarith

/-- A strip bound on every zero copy is quasi-RH. -/
theorem halfPlaneBound_of_abs_spectral_im_le {Δ : ℝ}
    (hΔ : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Δ) : XiZeroHalfPlaneBound Δ := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := hΔ q
  rw [spectral_im_eq, abs_le] at this
  linarith [this.1]

/-- **Quasi-RH makes the cosine family real-rooted below `½`** (de Bruijn, unconditional). -/
theorem exists_cosShiftXi_real_lt_half_of_quasiRH {α : ℝ} (hα1 : α < 1 / 2)
    (hα : XiZeroHalfPlaneBound α) :
    ∃ h : ℝ, 0 < h ∧ h < 1 / 2 ∧ ∀ z, cosShiftXi h z = 0 → z.im = 0 := by
  set h := max ((α + 1 / 2) / 2) (1 / 4) with hh
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hh1 : h < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hαh : α < h := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨h, hh0, hh1, ?_⟩
  intro z hz
  have hLP := laguerrePolya_cosineShiftXi_of_im_gt (h := h) fun q =>
    (abs_lt.mp (lt_of_le_of_lt (abs_spectral_im_le_of_halfPlaneBound hα q) hαh)).1
  exact GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya hLP (cosShiftXi_zero_ne h) hz

/-- **Under LH, sub-half real-rootedness of the cosine family is quasi-RH.** -/
theorem quasiRH_of_cosShiftXi_real_lt_half (hLH : LindelofCriticalLine) {h : ℝ} (hh0 : 0 < h)
    (hh1 : h < 1 / 2) (hreal : ∀ z, cosShiftXi h z = 0 → z.im = 0) :
    ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α := by
  set ε := (1 / 2 - h) / 2 with hε
  have hε0 : 0 < ε := by linarith
  obtain ⟨T, hT⟩ := eventually_strip_of_lindelofCriticalLine hLH hh0 hreal hε0
  obtain ⟨Δ, hΔ1, hΔ⟩ := exists_spectral_im_bound_of_re_le T
  refine ⟨max Δ (h + ε), max_lt hΔ1 (by linarith), halfPlaneBound_of_abs_spectral_im_le
    fun q => ?_⟩
  set z := xiSpectralPoint q with hz
  rcases le_or_gt |z.re| T with hlow | hhigh
  · exact (hΔ q hlow).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    -- the four symmetric copies `±z, ±z̄`
    have hrefl := xiSpectralPoint_reflect_symm q
    have hconj := xiSpectralPoint_lineConj_symm q
    have hboth := xiSpectralPoint_lineConj_symm (xiZeroCopyReflectEquiv.symm q)
    rw [hrefl] at hboth
    rw [abs_le]
    rcases lt_or_ge z.re 0 with hneg | hpos
    · have hre : T ≤ -z.re := by rw [abs_of_neg hneg] at hhigh; exact hhigh.le
      have h1 := hT (xiZeroCopyReflectEquiv.symm q) (by rw [hrefl]; simpa using hre)
      have h2 := hT (xiZeroCopyLineConjEquiv.symm (xiZeroCopyReflectEquiv.symm q))
        (by rw [hboth]; simpa using hre)
      rw [hrefl] at h1
      rw [hboth] at h2
      simp only [Complex.neg_im, Complex.conj_im, neg_neg] at h1 h2
      constructor <;> linarith
    · have hre : T ≤ z.re := by rw [abs_of_nonneg hpos] at hhigh; exact hhigh.le
      have h1 := hT q hre
      have h2 := hT (xiZeroCopyLineConjEquiv.symm q) (by rw [hconj]; simpa using hre)
      rw [hconj] at h2
      simp only [Complex.conj_im] at h2
      constructor <;> linarith

/-- **Quasi-RH as a sub-half threshold of the cosine family, under LH.** -/
theorem exists_cosShiftXi_real_lt_half_iff_quasiRH (hLH : LindelofCriticalLine) :
    (∃ h : ℝ, 0 < h ∧ h < 1 / 2 ∧ ∀ z, cosShiftXi h z = 0 → z.im = 0) ↔
      ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α :=
  ⟨fun ⟨_, hh0, hh1, hreal⟩ => quasiRH_of_cosShiftXi_real_lt_half hLH hh0 hh1 hreal,
    fun ⟨_, hα1, hα⟩ => exists_cosShiftXi_real_lt_half_of_quasiRH hα1 hα⟩

end

end RHTower.BacklundConverse
