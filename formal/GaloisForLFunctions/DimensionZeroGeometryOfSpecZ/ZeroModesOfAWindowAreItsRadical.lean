import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.HeckeSimilitudesOfAWindowAreScalars

/-!
# Zero modes of a window are its radical

A *zero mode* of a window is a nonzero window test `H` with `Q(H) = 0` on a window where Weil's form
is nonnegative: an edge of the positive cone. Under RH no window has one (Weil's form is positive
definite on each window); if RH fails, they are where negativity is born. This module fixes their
structure.

* **Zero modes are the radical** (`weilPair_eq_zero_of_zeroMode`): on a nonnegative window a test with
  `Q(H) = 0` pairs to zero with every window test, `W(H, G) = 0`: it solves the window Euler–Lagrange
  equation against every test, in particular against every short bump inside the window.
* **Zero modes are translation stable** (`weilQuad_comp_sub_zeroMode`): translates inside the window are
  zero modes.
* **At a first critical length a zero mode touches both ends**
  (`zeroMode_ne_zero_on_left_collar`, `zeroMode_ne_zero_on_right_collar`): if Weil's form is positive
  definite on every shorter window, a zero mode of `W_A` does not vanish on any collar
  `(−A, −A + δ)` or `(−δ, 0)`. An edge is born at full length; it cannot be pushed into a shorter
  window, and it carries mass on both collars where the newest folds act.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis

variable {A : ℝ} {H : ℝ → ℝ}

/-- **Zero modes of a nonnegative window are its radical.** -/
theorem weilPair_eq_zero_of_zeroMode (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    weilPair H G = 0 := by
  have hq : ∀ t : ℝ, 0 ≤ 2 * t * weilPair H G + t ^ 2 * weilQuad G := fun t => by
    have h := hpos _ (isWindowTest_lin hH hG 1 t)
    rw [weilQuad_plane (mem_realTests_of_isWindowTest hH) (mem_realTests_of_isWindowTest hG), h0]
      at h
    linarith
  have hq0 := hpos G hG
  have hden : 0 < weilQuad G + 1 := by linarith
  have h := hq (-(weilPair H G) / (weilQuad G + 1))
  have e : 2 * (-(weilPair H G) / (weilQuad G + 1)) * weilPair H G +
      (-(weilPair H G) / (weilQuad G + 1)) ^ 2 * weilQuad G =
        -(weilPair H G) ^ 2 * (weilQuad G + 2) / (weilQuad G + 1) ^ 2 := by
    field_simp
    ring
  rw [e] at h
  have h' : 0 ≤ -(weilPair H G) ^ 2 * (weilQuad G + 2) := by
    rcases div_nonneg_iff.mp h with h | h
    · exact h.1
    · exact absurd h.2 (not_le.mpr (by positivity))
  have hw : weilPair H G ^ 2 = 0 := by nlinarith [sq_nonneg (weilPair H G)]
  exact (pow_eq_zero_iff two_ne_zero).mp hw

/-- Translates of a zero mode are zero modes. -/
theorem weilQuad_comp_sub_zeroMode (h0 : weilQuad H = 0) (c : ℝ) :
    weilQuad (fun u => H (u - c)) = 0 := by
  rw [weilQuad_comp_sub, h0]

/-- A continuous function vanishing on `(a, b)` vanishes on `[a, b]`. -/
theorem eq_zero_on_Icc_of_Ioo {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h : ∀ u ∈ Ioo a b, f u = 0) : ∀ u ∈ Icc a b, f u = 0 := by
  have hcl : IsClosed {u | f u = 0} := isClosed_eq hf continuous_const
  have hsub : closure (Ioo a b) ⊆ {u | f u = 0} := hcl.closure_subset_iff.mpr h
  rw [closure_Ioo hab.ne] at hsub
  exact hsub

/-- **At a first critical length a zero mode touches the left end.** -/
theorem zeroMode_ne_zero_on_left_collar {δ : ℝ} (hδ : 0 < δ)
    (hpd : ∀ G : ℝ → ℝ, IsWindowTest (A - δ) G → (∃ u, G u ≠ 0) → 0 < weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (hne : ∃ u, H u ≠ 0) :
    ∃ u ∈ Ioo (-A) (-A + δ), H u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz := eq_zero_on_Icc_of_Ioo hH.continuous (by linarith) hcon
  have hwin : IsWindowTest (A - δ) H := ⟨hH.contDiff, fun y hy => by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · rcases lt_or_ge y (-A) with h' | h'
      · exact hH.vanish y fun hm => by linarith [hm.1]
      · exact hz y ⟨h', by linarith⟩
    · exact hH.vanish y fun hm => by linarith [hm.2]⟩
  have := hpd H hwin hne
  linarith

/-- **At a first critical length a zero mode touches the right end.** -/
theorem zeroMode_ne_zero_on_right_collar {δ : ℝ} (hδ : 0 < δ)
    (hpd : ∀ G : ℝ → ℝ, IsWindowTest (A - δ) G → (∃ u, G u ≠ 0) → 0 < weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (hne : ∃ u, H u ≠ 0) :
    ∃ u ∈ Ioo (-δ) 0, H u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz := eq_zero_on_Icc_of_Ioo hH.continuous (by linarith) hcon
  have hwin : IsWindowTest (A - δ) fun u => H (u - δ) :=
    ⟨hH.contDiff.comp (contDiff_id.sub contDiff_const), fun y hy => by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with h | h
      · exact hH.vanish _ fun hm => by linarith [hm.1]
      · rcases lt_or_ge 0 (y - δ) with h' | h'
        · exact hH.vanish _ fun hm => by linarith [hm.2]
        · exact hz _ ⟨by linarith, h'⟩⟩
  obtain ⟨u, hu⟩ := hne
  have := hpd _ hwin ⟨u + δ, by simpa using hu⟩
  rw [weilQuad_comp_sub_zeroMode h0] at this
  exact lt_irrefl 0 this

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
