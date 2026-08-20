import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle
import GaloisForLFunctions.RHTower.LevinsonEntireDetector

/-!
# Heights carrying no detector zero on the counting segment are dense

The entire detector `G♯` is not identically zero, so its zeros in the compact rectangle
`[1/2,4]×[a,b]` are finite; their ordinates form a finite set, and any nonempty open interval of
heights therefore contains a height at which the whole segment `[1/2,4]` misses the divisor.  These
are exactly the heights the rectangle argument principle admits.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- **Admissible heights for the detector are dense.** -/
theorem exists_levinsonG_admissible_height {lam : ℂ} (hlam : lam ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Set.Ioo a b,
      ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4, levinsonGEntire lam ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  classical
  set z₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + (a : ℂ) * I with hz₁
  set z₂ : ℂ := ((4 : ℝ) : ℂ) + (b : ℂ) * I with hz₂
  have hre₁ : z₁.re = (1 / 2 : ℝ) := by rw [hz₁]; simp
  have hre₂ : z₂.re = (4 : ℝ) := by rw [hz₂]; simp
  have him₁ : z₁.im = a := by rw [hz₁]; simp
  have him₂ : z₂.im = b := by rw [hz₂]; simp
  have hfin : {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) |
      levinsonGEntire lam z = 0}.Finite :=
    entire_zeros_closedRectangle_finite (analyticOnNhd_levinsonGEntire lam)
      (exists_levinsonGEntire_ne_zero hlam) z₁ z₂
  set ords : Finset ℝ := hfin.toFinset.image Complex.im with hords
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  obtain ⟨T, hTmem, hTnot⟩ := hinf.exists_notMem_finset ords
  refine ⟨T, hTmem, fun x hx hzero => ?_⟩
  refine hTnot ?_
  rw [hords, Finset.mem_image]
  refine ⟨(x : ℂ) + (T : ℂ) * I, ?_, by simp⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hzero⟩
  · rw [hre₁, hre₂]
    simpa using hx
  · have hxim : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
    rw [him₁, him₂, uIcc_of_le hab.le, hxim]
    exact ⟨hTmem.1.le, hTmem.2.le⟩

/-- The same, in terms of `G` itself: above height `0` the two vanishing conditions agree. -/
theorem exists_levinsonG_admissible_height' {lam : ℂ} (hlam : lam ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ T ∈ Set.Ioo a b,
      (∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4, levinsonGEntire lam ((x : ℂ) + (T : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4, levinsonG lam ((x : ℂ) + (T : ℂ) * I) ≠ 0) := by
  obtain ⟨T, hTmem, hT⟩ := exists_levinsonG_admissible_height hlam hab
  refine ⟨T, hTmem, hT, fun x hx => ?_⟩
  have hT0 : 0 < T := lt_trans ha hTmem.1
  have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im] at him
    linarith
  intro hzero
  exact hT x hx ((levinsonGEntire_eq_zero_iff lam hne1).mpr hzero)

end RHTower

end
