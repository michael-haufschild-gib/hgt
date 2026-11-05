import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindows

/-!
# Moving a transform zero preserves the Weil form

Compact division at a transform zero `κ` writes `F(z) = -i(z-κ)G(z)` without changing
the aperture. Replacing `κ` by its conjugate preserves every Weil summand, since its
two transform factors contain the symmetric product `(z-κ)(z-conj κ)`.

This is the zero-moving isometry on smooth compact sources. It applies to the actual
zeta form without assuming positivity or locating its zeros on the critical line.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open Zeta23 ZeroConfigurationGeometry

/-- Conjugating a differential factor preserves each diagonal Weil summand. -/
theorem pointImage_annihilate_conj {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (κ ρ : ℂ) :
    pointImage (annihilate (conj κ) g) (annihilate (conj κ) g) ρ =
      pointImage (annihilate κ g) (annihilate κ g) ρ := by
  simp only [pointImage, paperFT_annihilate hg hgc, map_mul, map_neg, map_sub,
    Complex.conj_I, starRingEnd_self_apply]
  ring

/-- Zero-moving preserves the full form for every zero configuration. -/
theorem weilForm_annihilate_conj (Z : ZeroConfig) {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (κ : ℂ) :
    Z.W (annihilate (conj κ) g) (annihilate (conj κ) g) =
      Z.W (annihilate κ g) (annihilate κ g) := by
  rw [W_eq_tsum_indicator, W_eq_tsum_indicator]
  exact tsum_congr fun ρ => congrArg
    (fun z => Z.carrier.indicator (fun z => (Z.mult z : ℂ)) ρ * z)
    (pointImage_annihilate_conj hg hgc κ ρ)

/-- A smooth compact source admits zero-moving at the same aperture. The polynomial
transform identity includes the removable point; every configuration's Weil form is preserved. -/
theorem exists_same_aperture_zero_move {r : ℝ} (hr : 0 ≤ r) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfs : tsupport f ⊆ Icc (-r) r) {κ : ℂ}
    (hκ : paperFT f κ = 0) :
    ∃ h : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) h ∧ tsupport h ⊆ Icc (-r) r ∧
      paperFT h (conj κ) = 0 ∧
      (∀ z : ℂ, (z - κ) * paperFT h z = (z - conj κ) * paperFT f z) ∧
      (∀ Z : ZeroConfig, Z.W h h = Z.W f f) := by
  obtain ⟨g, hg, hgs, hfg⟩ := exists_smooth_window_div hr hf hfs hκ
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  refine ⟨annihilate (conj κ) g, contDiff_annihilate hg,
    (tsupport_annihilate_subset _ g).trans hgs, ?_, ?_, ?_⟩
  · rw [paperFT_annihilate hg hgc, sub_self, mul_zero, zero_mul]
  · intro z
    rw [paperFT_annihilate hg hgc, hfg]
    ring
  · intro Z
    rw [W_eq_tsum_indicator, W_eq_tsum_indicator]
    apply tsum_congr
    intro ρ
    apply congrArg (fun z => Z.carrier.indicator (fun z => (Z.mult z : ℂ)) ρ * z)
    simp only [pointImage, paperFT_annihilate hg hgc, hfg, map_mul, map_neg, map_sub,
      Complex.conj_I, starRingEnd_self_apply]
    ring

#print axioms pointImage_annihilate_conj
#print axioms weilForm_annihilate_conj
#print axioms exists_same_aperture_zero_move

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
