import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheKickIsTheCollarReflection
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.ZeroModesOfAWindowAreItsRadical

/-!
# Zero modes have reflection parity

A zero mode of a nonnegative window `W_A` is a window test with `Q(H) = 0`; it lies in the radical
(DZG `weilPair_eq_zero_of_zeroMode`) and, at a first critical length, touches both ends (DZG).

* **The radical is reflection invariant** (`zeroMode_windowInvolution`, `zeroMode_evenPart`,
  `zeroMode_oddPart`): `σ_AH` and the parts `(H ± σ_AH)/2` are zero modes.
* **Every edge has a parity** (`exists_parity_zeroMode`): a window with a nonzero zero mode has a
  nonzero zero mode `G` with `σ_AG = G` or `σ_AG = −G`. At a first critical length such a `G` is
  nonzero on both collars, with mirrored values `G(−A − u) = ±G(u)`.
* **Gap law** (`gap_law`). If a zero mode splits as `G = G₁ + G₂` with `G₁` supported in `[−A, a]`,
  `G₂` in `[b, 0]`, `−A ≤ a < b ≤ 0` (it vanishes on the interior gap `(a, b)`), then
  `Q(G₁) = Q(G₂) = −W(G₁, G₂)`, and the two pieces have the same Weil orbit correlation across the
  gap: `W(G₁, G₁(· − δ)) = W(G₂, G₂(· + δ))` for `0 ≤ δ ≤ b − a`. A zero mode cannot be cut into
  independent pieces: the two sides of a gap are balanced translates of each other in Weil energy.
  This is the exact constraint that a unique-continuation principle across interior gaps would have
  to turn into a contradiction.
* **Unique continuation from an end collar** (`eq_zero_of_zeroMode_vanish_collar`,
  `zeroMode_eq_of_eq_on_collar`): at a first critical length a zero mode vanishing on an end collar
  of any width vanishes, and two zero modes agreeing on one end collar coincide. The radical restricts
  injectively to each end collar: the edge of the positive cone is determined by the data on which
  the newest fold acts.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri

variable {A : ℝ} {H : ℝ → ℝ}

/-- `W(H, G) = W(σH, σG)`: the window involution is an isometry of Weil's pairing. -/
theorem weilPair_windowInvolution {F G : ℝ → ℝ} (hF : F ∈ realTests) (hG : G ∈ realTests) :
    weilPair (windowInvolution A F) (windowInvolution A G) = weilPair F G := by
  have hσF : windowInvolution A F ∈ realTests :=
    ⟨hF.1.comp (contDiff_const.sub contDiff_id),
      hF.2.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft (-A)))⟩
  have hσG : windowInvolution A G ∈ realTests :=
    ⟨hG.1.comp (contDiff_const.sub contDiff_id),
      hG.2.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft (-A)))⟩
  have hp := weilQuad_plane hF hG 1 1
  have hm := weilQuad_plane hF hG 1 (-1)
  have hp' := weilQuad_plane hσF hσG 1 1
  have hm' := weilQuad_plane hσF hσG 1 (-1)
  have e1 : (fun u => 1 * windowInvolution A F u + 1 * windowInvolution A G u) =
      windowInvolution A (fun u => 1 * F u + 1 * G u) := rfl
  have e2 : (fun u => 1 * windowInvolution A F u + -1 * windowInvolution A G u) =
      windowInvolution A (fun u => 1 * F u + -1 * G u) := rfl
  rw [e1, weilQuad_windowInvolution, hp] at hp'
  rw [e2, weilQuad_windowInvolution, hm] at hm'
  rw [weilQuad_windowInvolution] at hp' hm'
  nlinarith

/-- **The reflection of a zero mode is a zero mode.** -/
theorem zeroMode_windowInvolution (h0 : weilQuad H = 0) :
    weilQuad (windowInvolution A H) = 0 := by
  rw [weilQuad_windowInvolution, h0]

/-- A zero mode is orthogonal to every window test after reflection as well. -/
theorem weilPair_windowInvolution_zeroMode
    (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G) (hH : IsWindowTest A H)
    (h0 : weilQuad H = 0) {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    weilPair (windowInvolution A H) G = 0 :=
  weilPair_eq_zero_of_zeroMode hpos hH.windowInvolution (zeroMode_windowInvolution h0) hG

/-- The radical is a subspace: a combination of zero modes is a zero mode. -/
theorem zeroMode_lin (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    {F G : ℝ → ℝ} (hF : IsWindowTest A F) (hG : IsWindowTest A G) (hF0 : weilQuad F = 0)
    (hG0 : weilQuad G = 0) (α β : ℝ) : weilQuad (fun u => α * F u + β * G u) = 0 := by
  rw [weilQuad_plane (mem_realTests_of_isWindowTest hF) (mem_realTests_of_isWindowTest hG),
    weilPair_eq_zero_of_zeroMode hpos hF hF0 hG, hF0, hG0]
  ring

/-- **The even part of a zero mode is a zero mode.** -/
theorem zeroMode_evenPart (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) : weilQuad (evenPart A H) = 0 :=
  zeroMode_lin hpos hH hH.windowInvolution h0 (zeroMode_windowInvolution h0) _ _

/-- **The odd part of a zero mode is a zero mode.** -/
theorem zeroMode_oddPart (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) : weilQuad (oddPart A H) = 0 :=
  zeroMode_lin hpos hH hH.windowInvolution h0 (zeroMode_windowInvolution h0) _ _

/-- **Every edge has a reflection parity.** If a nonnegative window carries a nonzero zero mode, it
carries a nonzero zero mode that is `σ_A`-even or `σ_A`-odd. -/
theorem exists_parity_zeroMode (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (hne : ∃ u, H u ≠ 0) :
    ∃ G : ℝ → ℝ, IsWindowTest A G ∧ weilQuad G = 0 ∧ (∃ u, G u ≠ 0) ∧
      (windowInvolution A G = G ∨ windowInvolution A G = fun u => -G u) := by
  obtain ⟨u, hu⟩ := hne
  have hsplit := congrFun (evenPart_add_oddPart A H) u
  simp only [one_mul] at hsplit
  by_cases he : evenPart A H u = 0
  · refine ⟨oddPart A H, isWindowTest_lin hH hH.windowInvolution _ _,
      zeroMode_oddPart hpos hH h0, ⟨u, fun ho => hu ?_⟩, Or.inr (oddPart_windowInvolution A H)⟩
    rw [← hsplit, he, ho, add_zero]
  · exact ⟨evenPart A H, isWindowTest_lin hH hH.windowInvolution _ _,
      zeroMode_evenPart hpos hH h0, ⟨u, he⟩, Or.inl (evenPart_windowInvolution A H)⟩

/-- **A parity edge at a first critical length.** If every shorter window (by `δ`) is positive
definite, a parity zero mode is nonzero on the left collar `(−A, −A + δ)`, and its right-collar
values mirror the left ones: `G(−A − u) = ±G(u)`. -/
theorem parity_zeroMode_collars {δ : ℝ} (hδ : 0 < δ)
    (hpd : ∀ G : ℝ → ℝ, IsWindowTest (A - δ) G → (∃ u, G u ≠ 0) → 0 < weilQuad G)
    {G : ℝ → ℝ} (hG : IsWindowTest A G) (h0 : weilQuad G = 0) (hne : ∃ u, G u ≠ 0)
    (hpar : windowInvolution A G = G ∨ windowInvolution A G = fun u => -G u) :
    (∃ u ∈ Ioo (-A) (-A + δ), G u ≠ 0) ∧ ∀ u, G (-A - u) = G u ∨ G (-A - u) = -G u := by
  refine ⟨zeroMode_ne_zero_on_left_collar hδ hpd hG h0 hne, fun u => ?_⟩
  rcases hpar with h | h
  · exact Or.inl (congrFun h u)
  · exact Or.inr (congrFun h u)

/-! ### The gap law -/

/-- **Gap law.** Let `G = G₁ + G₂` be a zero mode of a nonnegative window with `G₁` supported in
`[−A, a]` and `G₂` in `[b, 0]`, `a < b`. Then `Q(G₁) = Q(G₂) = −W(G₁, G₂)`, and for every
`0 ≤ δ ≤ b − a` the two pieces have the same Weil orbit correlation:
`W(G₁, G₁(· − δ)) = W(G₂, G₂(· + δ))`. -/
theorem gap_law (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    {G₁ G₂ : ℝ → ℝ} {a b : ℝ} (ha : -A ≤ a) (hb : b ≤ 0)
    (h1 : IsWindowTest A G₁) (h2 : IsWindowTest A G₂)
    (h1s : ∀ y, a < y → G₁ y = 0) (h2s : ∀ y, y < b → G₂ y = 0)
    (h0 : weilQuad (fun u => G₁ u + G₂ u) = 0) :
    weilQuad G₁ = weilQuad G₂ ∧ weilPair G₁ G₂ = -weilQuad G₁ ∧
      ∀ δ, 0 ≤ δ → δ ≤ b - a →
        weilPair G₁ (fun u => G₁ (u - δ)) = weilPair G₂ (fun u => G₂ (u + δ)) := by
  have hG := isWindowTest_add h1 h2
  have m1 := mem_realTests_of_isWindowTest h1
  have m2 := mem_realTests_of_isWindowTest h2
  have hsum : (fun u => G₁ u + G₂ u) = G₁ + G₂ := rfl
  -- the zero mode is orthogonal to its pieces and to their admissible translates
  have orth : ∀ {F : ℝ → ℝ}, IsWindowTest A F → weilPair G₁ F + weilPair G₂ F = 0 := fun hF => by
    have := weilPair_eq_zero_of_zeroMode hpos hG h0 hF
    rwa [hsum, weilPair_add_left m1 m2 (mem_realTests_of_isWindowTest hF)] at this
  have e1 := orth h1
  have e2 := orth h2
  have hQ1 : weilQuad G₁ = weilPair G₁ G₁ := rfl
  have hQ2 : weilQuad G₂ = weilPair G₂ G₂ := rfl
  rw [weilPair_comm G₂ G₁] at e1
  refine ⟨by rw [hQ1, hQ2]; linarith, by rw [hQ1]; linarith, fun δ hδ0 hδ => ?_⟩
  -- `G₂(· + δ)` and `G₁(· − δ)` are still window tests
  have h2δ : IsWindowTest A (fun u => G₂ (u + δ)) :=
    ⟨h2.contDiff.comp (contDiff_id.add contDiff_const), fun y hy => by
      rcases not_and_or.mp hy with hy | hy
      · exact h2s _ (by linarith [not_le.mp hy])
      · exact h2.vanish _ fun hm => by linarith [hm.2, not_le.mp hy]⟩
  have h1δ : IsWindowTest A (fun u => G₁ (u - δ)) :=
    ⟨h1.contDiff.comp (contDiff_id.sub contDiff_const), fun y hy => by
      rcases not_and_or.mp hy with hy | hy
      · exact h1.vanish _ fun hm => by linarith [hm.1, not_le.mp hy]
      · exact h1s _ (by linarith [not_le.mp hy])⟩
  have f1 := orth h2δ
  have f2 := orth h1δ
  -- translation invariance moves the cross terms onto each other
  have hcross : weilPair G₂ (fun u => G₁ (u - δ)) = weilPair G₁ (fun u => G₂ (u + δ)) := by
    rw [weilPair_comm]
    have := DimensionZeroGeometryOfSpecZ.weilPair_comp_sub G₁ (fun u => G₂ (u + δ)) δ
    simp only [sub_add_cancel] at this
    exact this
  linarith

/-! ### Unique continuation from an end collar -/

/-- **A zero mode vanishing on an end collar vanishes.** If every shorter window (by `δ`) is positive
definite, a test of Weil energy zero vanishing on the left collar `(−A, −A + δ)` or on the right
collar `(−δ, 0)` is zero. -/
theorem eq_zero_of_zeroMode_vanish_collar {δ : ℝ} (hδ : 0 < δ)
    (hpd : ∀ G : ℝ → ℝ, IsWindowTest (A - δ) G → (∃ u, G u ≠ 0) → 0 < weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0)
    (hcol : (∀ u ∈ Set.Ioo (-A) (-A + δ), H u = 0) ∨ ∀ u ∈ Set.Ioo (-δ) 0, H u = 0) : H = 0 := by
  funext u
  by_contra hu
  rcases hcol with hl | hr
  · obtain ⟨v, hv, hv0⟩ := zeroMode_ne_zero_on_left_collar hδ hpd hH h0 ⟨u, hu⟩
    exact hv0 (hl v hv)
  · obtain ⟨v, hv, hv0⟩ := zeroMode_ne_zero_on_right_collar hδ hpd hH h0 ⟨u, hu⟩
    exact hv0 (hr v hv)

/-- **Unique continuation from an end collar.** At a first critical length two zero modes of a
nonnegative window that agree on one end collar, however thin, agree everywhere: the radical of the
window restricts injectively to either end collar. -/
theorem zeroMode_eq_of_eq_on_collar (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    {δ : ℝ} (hδ : 0 < δ)
    (hpd : ∀ G : ℝ → ℝ, IsWindowTest (A - δ) G → (∃ u, G u ≠ 0) → 0 < weilQuad G)
    {G₁ G₂ : ℝ → ℝ} (h1 : IsWindowTest A G₁) (h2 : IsWindowTest A G₂) (h10 : weilQuad G₁ = 0)
    (h20 : weilQuad G₂ = 0)
    (hcol : (∀ u ∈ Set.Ioo (-A) (-A + δ), G₁ u = G₂ u) ∨ ∀ u ∈ Set.Ioo (-δ) 0, G₁ u = G₂ u) :
    G₁ = G₂ := by
  have hD : IsWindowTest A (fun u => 1 * G₁ u + -1 * G₂ u) := isWindowTest_lin h1 h2 1 (-1)
  have hD0 := zeroMode_lin hpos h1 h2 h10 h20 1 (-1)
  have hz := eq_zero_of_zeroMode_vanish_collar hδ hpd hD hD0 (by
    rcases hcol with hl | hr
    · exact Or.inl fun u hu => by rw [hl u hu]; ring
    · exact Or.inr fun u hu => by rw [hr u hu]; ring)
  funext u
  have := congrFun hz u
  simp only [Pi.zero_apply] at this
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
