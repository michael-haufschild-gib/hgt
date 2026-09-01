import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle

/-!
# Heights at which an entire function misses a horizontal segment are dense

An entire function that is not identically zero has finitely many zeros in any compact rectangle,
so their ordinates form a finite set and every nonempty open interval of heights contains a height
whose whole horizontal segment misses the divisor.  These are exactly the heights admitted by the
rectangle argument principle and by Littlewood's identity.

This is the detector-free version of `exists_levinsonG_admissible_height`; applying it to a product
produces a height admissible for both factors simultaneously.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- **Admissible heights are dense for every entire function.** -/
theorem exists_entire_admissible_height {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0) (c d : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Set.Ioo a b, ∀ x ∈ Set.uIcc c d, f ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  classical
  set z₁ : ℂ := (c : ℂ) + (a : ℂ) * I with hz₁
  set z₂ : ℂ := (d : ℂ) + (b : ℂ) * I with hz₂
  have hre₁ : z₁.re = c := by rw [hz₁]; simp
  have hre₂ : z₂.re = d := by rw [hz₂]; simp
  have him₁ : z₁.im = a := by rw [hz₁]; simp
  have him₂ : z₂.im = b := by rw [hz₂]; simp
  have hfin : {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) | f z = 0}.Finite :=
    entire_zeros_closedRectangle_finite hf hne z₁ z₂
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

/-- The same height works for both factors of a product. -/
theorem exists_entire_admissible_height_pair {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hne : ∃ z : ℂ, f z * g z ≠ 0) (c d : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Set.Ioo a b,
      (∀ x ∈ Set.uIcc c d, f ((x : ℂ) + (T : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc c d, g ((x : ℂ) + (T : ℂ) * I) ≠ 0) := by
  have hfg : AnalyticOnNhd ℂ (fun z => f z * g z) Set.univ := fun z hz =>
    (hf z hz).mul (hg z hz)
  obtain ⟨T, hT, hzero⟩ := exists_entire_admissible_height hfg hne c d hab
  refine ⟨T, hT, fun x hx hfx => ?_, fun x hx hgx => ?_⟩
  · exact hzero x hx (by simp [hfx])
  · exact hzero x hx (by simp [hgx])

end RHTower

end
