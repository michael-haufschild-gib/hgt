import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LandauWidomNearRadicalLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum

/-!
# The window index

The **window index** `ι(A)` of `Spec ℤ` is the largest number of negative squares of Weil's form on
a finite family of tests supported in a window of length `A` (`windowIndex`; the Hodge defect of
ACS at degree `A/2`). It is the integer of the window object: its negative `h¹`.

* **The index sees the window form** (`windowIndex_eq_zero_iff`): `ι(A) = 0` iff Weil's form is
  nonnegative on every real window test of length `A`; a complex test splits into its real and
  imaginary parts.
* **Laws in the length**: `ι` is nondecreasing (`windowIndex_mono`), zero on windows of length
  `≤ 3/5` (`windowIndex_eq_zero_of_le`), finite at every length (`windowIndex_lt_top`) with the
  Shannon bound `ι(A) ≤ ⌊1 + 2A·T(A/2)/π⌋` (`windowIndex_le_shannon`).
* **The windows exhaust the zeros** (`iSup_windowIndex`): `sup_A ι(A) = #{ρ : Re ρ > ½}`, an even
  number (`iSup_windowIndex_even`).
* **The first quantum** (`riemannHypothesis_iff_forall_windowIndex_lt_two`): RH holds iff every
  window has index `< 2`, iff every window has index `0`. A window of index one cannot exist in
  the limit: right zeros come in pairs.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri

/-- The **window index** `ι(A)`: negative squares of Weil's form on tests in a window of length `A`. -/
def windowIndex (A : ℝ) : ℕ∞ := hodgeDefectAt zetaZeroConfig (A / 2)

theorem windowIndex_mono : Monotone windowIndex := fun _ _ h =>
  hodgeDefectAt_mono zetaZeroConfig (by linarith)

/-- Windows of length `≤ 3/5` have index zero. -/
theorem windowIndex_eq_zero_of_le {A : ℝ} (hA : A ≤ 3 / 5) : windowIndex A = 0 :=
  zeta_hodgeDefectAt_eq_zero (by linarith)

/-- Every window has finite index. -/
theorem windowIndex_lt_top (A : ℝ) : windowIndex A < ⊤ := hodgeDefectAt_zeta_lt_top _

/-- **The Shannon bound**: `ι(A) ≤ ⌊1 + 2A·T(A/2)/π⌋`. -/
theorem windowIndex_le_shannon {A : ℝ} (hA : 0 ≤ A) :
    windowIndex A ≤ (⌊1 + 2 * A * horizonFreq (A / 2) / Real.pi⌋₊ : ℕ∞) := by
  have h := hodgeDefectAt_zeta_le_shannon (a := A / 2) (by linarith)
  rwa [show 4 * (A / 2) * horizonFreq (A / 2) = 2 * A * horizonFreq (A / 2) by ring] at h

/-- **The windows exhaust the right zeros.** -/
theorem iSup_windowIndex : ⨆ A, windowIndex A = (rightZeros zetaZeroConfig).encard := by
  rw [← iSup_hodgeDefectAt zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig]
  refine le_antisymm (iSup_le fun A => le_iSup (hodgeDefectAt zetaZeroConfig) (A / 2))
    (iSup_le fun a => ?_)
  have : hodgeDefectAt zetaZeroConfig a = windowIndex (2 * a) := by
    rw [windowIndex, mul_div_cancel_left₀ a two_ne_zero]
  rw [this]
  exact le_iSup windowIndex (2 * a)

/-- The limit of the window index is even. -/
theorem iSup_windowIndex_even :
    ⨆ A, windowIndex A = 2 * (sectorZeros zetaZeroConfig 1).encard := by
  rw [iSup_windowIndex, zeta_rightZeros_encard_eq_two_mul_sectorZeros]

/-- **The first quantum**: RH iff every window has index `< 2`. -/
theorem riemannHypothesis_iff_forall_windowIndex_lt_two :
    RiemannHypothesis ↔ ∀ A, windowIndex A < 2 := by
  rw [ArithmeticOrientationGeometry.riemannHypothesis_iff_encard_rightZeros_lt_two,
    ← iSup_windowIndex]
  constructor
  · exact fun h A => (le_iSup windowIndex A).trans_lt h
  · intro h
    refine lt_of_le_of_lt (iSup_le fun A => ?_) (by norm_num : (1 : ℕ∞) < 2)
    have h2 : windowIndex A < 1 + 1 := by rw [one_add_one_eq_two]; exact h A
    exact Order.le_of_lt_add_one h2

/-! ### The index sees the window form -/

/-- **`ι(A) = 0` iff Weil's form is nonnegative on every real window test of length `A`.** -/
theorem windowIndex_eq_zero_iff {A : ℝ} :
    windowIndex A = 0 ↔ ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ weilQuad H := by
  rw [windowIndex, hodgeDefectAt_eq_zero_iff zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig]
  constructor
  · intro h H hH
    -- centre the window test: `G(u) = H(u − A/2)` lives in `[−A/2, A/2]`
    set G : ℝ → ℝ := fun u => H (u - A / 2) with hG
    have hGc : ContDiff ℝ 2 G := hH.contDiff.comp (contDiff_id.sub contDiff_const)
    have hGv : ∀ y, y ∉ Icc (-(A / 2)) (A / 2) → G y = 0 := fun y hy => by
      refine hH.vanish _ fun hm => hy ⟨?_, ?_⟩ <;> linarith [hm.1, hm.2]
    have hGcs : HasCompactSupport G :=
      HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) hGv
    have hts : tsupport (fun u => (G u : ℂ)) ⊆ Icc (-(A / 2)) (A / 2) := by
      refine closure_minimal (fun y hy => ?_) isClosed_Icc
      by_contra hn
      exact hy (by simp [hGv y hn])
    have hW := h (fun u => (G u : ℂ)) (Complex.ofRealCLM.contDiff.comp hGc) hts
    rw [← LogCells.weilQuad_eq_zetaW hGc hGcs, hG, weilQuad_comp_sub] at hW
    exact hW
  · intro h f hf hts
    have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
    rw [RHTower.zeta_W_eq_weilFullFunctional hf hfc,
      RHTower.CHMDPolar.re_weilFullFunctional_split _ ⟨f, hf, hfc⟩]
    -- each part, moved into `[−A, 0]`, is a window test
    have hpart : ∀ (g : ℂ → ℝ) (hg : ContDiff ℝ 2 (fun x => g (f x))) (hg0 : g 0 = 0),
        0 ≤ weilQuad (fun x => g (f x)) := fun g hg hg0 => by
      have hv : ∀ y, y ∉ Icc (-A) 0 → g (f (y - -(A / 2))) = 0 := fun y hy => by
        have : f (y - -(A / 2)) = 0 := by
          by_contra hne
          exact hy ⟨by linarith [(hts (subset_tsupport f hne)).1],
            by linarith [(hts (subset_tsupport f hne)).2]⟩
        rw [this, hg0]
      have := h (fun y => g (f (y - -(A / 2))))
        ⟨hg.comp (contDiff_id.sub contDiff_const), hv⟩
      rwa [weilQuad_comp_sub (fun x => g (f x))] at this
    exact add_nonneg (hpart Complex.re (Complex.reCLM.contDiff.comp hf) Complex.zero_re)
      (hpart Complex.im (Complex.imCLM.contDiff.comp hf) Complex.zero_im)

/-! ### The index sees the window form -/

/-- **`ι(A) = 0` iff Weil's form is nonnegative on every real window test of length `A`.** -/
theorem windowIndex_eq_zero_iff {A : ℝ} :
    windowIndex A = 0 ↔ ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ weilQuad H := by
  rw [windowIndex, hodgeDefectAt_eq_zero_iff zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig]
  constructor
  · intro h H hH
    -- centre the window test: `G(u) = H(u − A/2)` lives in `[−A/2, A/2]`
    set G : ℝ → ℝ := fun u => H (u - A / 2) with hG
    have hGc : ContDiff ℝ 2 G := hH.contDiff.comp (contDiff_id.sub contDiff_const)
    have hGv : ∀ y, y ∉ Icc (-(A / 2)) (A / 2) → G y = 0 := fun y hy => by
      refine hH.vanish _ fun hm => hy ⟨?_, ?_⟩ <;> linarith [hm.1, hm.2]
    have hGcs : HasCompactSupport G :=
      HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) hGv
    have hts : tsupport (fun u => (G u : ℂ)) ⊆ Icc (-(A / 2)) (A / 2) := by
      refine closure_minimal (fun y hy => ?_) isClosed_Icc
      by_contra hn
      exact hy (by simp [hGv y hn])
    have hW := h (fun u => (G u : ℂ)) (Complex.ofRealCLM.contDiff.comp hGc) hts
    rw [← LogCells.weilQuad_eq_zetaW hGc hGcs, hG, weilQuad_comp_sub] at hW
    exact hW
  · intro h f hf hts
    have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
    rw [RHTower.zeta_W_eq_weilFullFunctional hf hfc,
      RHTower.CHMDPolar.re_weilFullFunctional_split _ ⟨f, hf, hfc⟩]
    -- each part, moved into `[−A, 0]`, is a window test
    have hpart : ∀ (g : ℂ → ℝ) (hg : ContDiff ℝ 2 (fun x => g (f x))) (hg0 : g 0 = 0),
        0 ≤ weilQuad (fun x => g (f x)) := fun g hg hg0 => by
      have hv : ∀ y, y ∉ Icc (-A) 0 → g (f (y - -(A / 2))) = 0 := fun y hy => by
        have : f (y - -(A / 2)) = 0 := by
          by_contra hne
          exact hy ⟨by linarith [(hts (subset_tsupport f hne)).1],
            by linarith [(hts (subset_tsupport f hne)).2]⟩
        rw [this, hg0]
      have := h (fun y => g (f (y - -(A / 2))))
        ⟨hg.comp (contDiff_id.sub contDiff_const), hv⟩
      rwa [weilQuad_comp_sub (fun x => g (f x))] at this
    exact add_nonneg (hpart Complex.re (Complex.reCLM.contDiff.comp hf) Complex.zero_re)
      (hpart Complex.im (Complex.imCLM.contDiff.comp hf) Complex.zero_im)

/-- RH iff every window has index `0`. -/
theorem riemannHypothesis_iff_forall_windowIndex_eq_zero :
    RiemannHypothesis ↔ ∀ A, windowIndex A = 0 := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  constructor
  · intro h A
    rcases le_total 0 A with hA | hA
    · exact windowIndex_eq_zero_iff.mpr (h A hA)
    · exact windowIndex_eq_zero_of_le (by linarith)
  · exact fun h A _ => windowIndex_eq_zero_iff.mp (h A)

/-- RH iff every window has index `0`. -/
theorem riemannHypothesis_iff_forall_windowIndex_eq_zero :
    RiemannHypothesis ↔ ∀ A, windowIndex A = 0 := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  constructor
  · intro h A
    rcases le_total 0 A with hA | hA
    · exact windowIndex_eq_zero_iff.mpr (h A hA)
    · exact windowIndex_eq_zero_of_le (by linarith)
  · exact fun h A _ => windowIndex_eq_zero_iff.mp (h A)

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
