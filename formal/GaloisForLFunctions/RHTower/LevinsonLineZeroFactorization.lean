import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle
import GaloisForLFunctions.RHTower.LevinsonEntirePhaseAdvance
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor

/-!
# The critical-line zeros of Levinson's entire detector

A zero of `G = ζ + λζ'` on the critical line forces `ζ` to vanish there together with `ζ'`, so the
entire detector `G♯ = (s-1)²G` can vanish on the critical segment.  The argument principle needs a
contour on which the function does not vanish, so those zeros are removed once and for all: they are
finitely many, and dividing out the corresponding node polynomial leaves an entire cofactor
nonvanishing on the whole segment while keeping every zero off the segment untouched.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- **Removing the critical-line zeros of the entire detector.**  On a window `[T₁,T₂]` the entire
detector `G♯` has finitely many zeros on the critical segment; dividing the corresponding node
polynomial out leaves an entire cofactor that is nonvanishing on the whole segment. -/
theorem exists_levinson_line_factorization {lam : ℂ} (hlam : lam ≠ 0) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ∃ (pts : Finset ℂ) (m : ℂ → ℕ) (H : ℂ → ℂ),
      (∀ c : ℂ, c ∈ pts ↔ (∃ τ ∈ Icc T₁ T₂, c = linePt τ) ∧ levinsonGEntire lam c = 0) ∧
      (∀ c ∈ pts, 1 ≤ m c) ∧
      (∀ c ∈ pts, analyticOrderAt (levinsonGEntire lam) c = ((m c : ℕ) : ℕ∞)) ∧
      Differentiable ℂ H ∧
      (∀ z, levinsonGEntire lam z = (∏ c ∈ pts, (z - c) ^ (m c)) * H z) ∧
      (∀ τ ∈ Icc T₁ T₂, H (linePt τ) ≠ 0) := by
  classical
  set F : ℂ → ℂ := levinsonGEntire lam with hF
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_levinsonGEntire lam
  have hFne : ∃ z : ℂ, F z ≠ 0 := exists_levinsonGEntire_ne_zero hlam
  have hfinite : {z ∈ (uIcc (linePt T₁).re (linePt T₂).re ×ℂ
      uIcc (linePt T₁).im (linePt T₂).im) | F z = 0}.Finite :=
    entire_zeros_closedRectangle_finite hFan hFne (linePt T₁) (linePt T₂)
  set pts : Finset ℂ := hfinite.toFinset with hpts
  have hlineIcc : uIcc (linePt T₁).im (linePt T₂).im = Icc T₁ T₂ := by
    rw [linePt_im, linePt_im, uIcc_of_le hT]
  have hmemiff : ∀ c : ℂ, c ∈ pts ↔ (∃ τ ∈ Icc T₁ T₂, c = linePt τ) ∧ F c = 0 := by
    intro c
    change c ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
    constructor
    · rintro ⟨hc, hz⟩
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hc
      rw [linePt_re, linePt_re, uIcc_self, Set.mem_singleton_iff] at hre
      rw [hlineIcc] at him
      refine ⟨⟨c.im, him, ?_⟩, hz⟩
      apply Complex.ext
      · rw [linePt_re]; exact hre
      · rw [linePt_im]
    · rintro ⟨⟨τ, hτ, rfl⟩, hz⟩
      refine ⟨?_, hz⟩
      rw [Complex.mem_reProdIm]
      constructor
      · rw [linePt_re, linePt_re, linePt_re, uIcc_self]; rfl
      · rw [hlineIcc, linePt_im]; exact hτ
  set m : ℂ → ℕ := fun w => (analyticOrderAt F w).toNat with hm
  have hordne : ∀ w : ℂ, analyticOrderAt F w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hFan hFne w
  have hordeq : ∀ c : ℂ, analyticOrderAt F c = ((m c : ℕ) : ℕ∞) := by
    intro c
    rw [hm]
    exact (ENat.coe_toNat (hordne c)).symm
  have hmpos : ∀ c ∈ pts, 1 ≤ m c := by
    intro c hc
    have hz : F c = 0 := ((hmemiff c).mp hc).2
    have hne0 : analyticOrderAt F c ≠ 0 := by
      intro h0
      exact ((hFan c (Set.mem_univ c)).analyticOrderAt_eq_zero.mp h0) hz
    have : m c ≠ 0 := by
      intro h
      apply hne0
      rw [hordeq c, h]
      simp
    omega
  obtain ⟨H, hH, hHne, hfact⟩ :=
    exists_entire_multiplicity_factor (f := F)
      (fun z => hFan z (Set.mem_univ z)) pts m (fun c _ => hordeq c)
  refine ⟨pts, m, H, hmemiff, hmpos, fun c _ => hordeq c,
    fun z => (hH z).differentiableAt, hfact, ?_⟩
  intro τ hτ
  by_cases hmem : linePt τ ∈ pts
  · exact hHne _ hmem
  · intro hzero
    have hF0 : F (linePt τ) = 0 := by rw [hfact (linePt τ), hzero, mul_zero]
    exact hmem ((hmemiff (linePt τ)).mpr ⟨⟨τ, hτ, rfl⟩, hF0⟩)

end RHTower

end
