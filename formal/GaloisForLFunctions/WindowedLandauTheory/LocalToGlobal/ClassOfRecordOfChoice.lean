import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.DesWin

/-! The arithmetic conditions carried by the selected design family. -/

namespace WindowedLandauTheory.L2.Top3

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions

abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

theorem withSm_of_withChN {𝒞 : FamClass} {eps : ℝ} (Fm : FamP eps) (h : WithChN 𝒞 Fm) :
    WithSm (WithChN 𝒞) Fm :=
  ⟨h, J.dGamSmooth_of_dvd Fm h.2.1⟩

theorem designChoices_upN {𝒞 : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (h : DesignChoices (WithTw 𝒞) C0 cT) :
    DesignChoices (WithTw (WithSm (WithChN 𝒞))) C0 cT := by
  obtain ⟨ε₀, hε₀, h⟩ := h
  refine ⟨ε₀, hε₀, fun eps he hle K => ?_⟩
  obtain ⟨Fm, CH, C5, Cb, hc, hCH, hL, h5, hb, hThick, hTT, hBad, hQD, hCode, hBox, hRow, hGam,
    hTu, hTame, hCF, hUp, hCYL⟩ := h eps he hle K
  have hCh : WithChN 𝒞 Fm := ⟨hc.1, hGam, hTame, hBox, hRow, hCYL⟩
  exact ⟨Fm, CH, C5, Cb, ⟨withSm_of_withChN Fm hCh, hc.2⟩, hCH, hL, h5, hb, hThick, hTT, hBad,
    hQD, hCode, hBox, hRow, hGam, hTu, hTame, hCF, hUp, hCYL⟩

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

theorem d3_a {C0 : ℝ} {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : D3 C0 𝒜 Fm) : 𝒜 Fm :=
  h.1.1.1.1

end WindowedLandauTheory.L2.Top3
