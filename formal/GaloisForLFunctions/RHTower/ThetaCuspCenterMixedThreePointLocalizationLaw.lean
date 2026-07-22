import GaloisForLFunctions.RHTower.HedenmalmCenterMixedLocalThreePoint
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedUniformCoalescedSquare

/-!
# Theta-cusp center-mixed three-point localization law

Uniform positive definiteness at the doubly coalesced corner and positive semidefiniteness at
large gap confine every possible failure to a bounded middle shell.  Equivalently, the global
three-point problem reduces exactly to that shell rather than to the full bounded square.
-/

namespace RHTower

noncomputable section

/-- Certificate localizing every possible loss of positive semidefiniteness of the center-mixed
theta three-point matrix to a bounded shell away from the coalesced corner. -/
def ThetaCuspCenterMixedThreePointLocalizationCertificate (a : ℝ) : Prop :=
  ∃ coalescenceRadius outerCutoff : ℝ,
    0 < coalescenceRadius ∧
    coalescenceRadius ≤ outerCutoff ∧
    (∀ x y : ℝ,
      0 < x → x < coalescenceRadius → 0 < y → y < coalescenceRadius →
        Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y)) ∧
    (∀ x y : ℝ,
      0 < x → 0 < y → outerCutoff ≤ x ∨ outerCutoff ≤ y →
        Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ∧
    (∀ x y : ℝ,
      0 < x → 0 < y →
        ¬ Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) →
          (coalescenceRadius ≤ x ∨ coalescenceRadius ≤ y) ∧
            x < outerCutoff ∧ y < outerCutoff) ∧
    ((∀ x y : ℝ, 0 < x → 0 < y →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ↔
      (∀ x y : ℝ, 0 < x → 0 < y →
        coalescenceRadius ≤ x ∨ coalescenceRadius ≤ y →
        x < outerCutoff → y < outerCutoff →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)))

/-- **Three-point localization law.**  At every critical aperture, all possible failures of the
center-mixed theta three-point PSD problem lie in one bounded shell separated from the doubly
coalesced corner.  Testing that shell is exactly equivalent to testing all positive gaps. -/
theorem thetaCuspCenterMixedThreePoint_localizationLaw
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ThetaCuspCenterMixedThreePointLocalizationCertificate a := by
  unfold ThetaCuspCenterMixedThreePointLocalizationCertificate
  rcases exists_thetaCuspCenterMixed_uniformCoalescedSquare_posDef ha0 ha with
    ⟨delta, hdelta, hnear⟩
  rcases exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap ha0 ha with
    ⟨Y₀, hfar₀⟩
  let Y := max Y₀ delta
  have hdeltaY : delta ≤ Y := by
    exact le_max_right _ _
  have hY₀Y : Y₀ ≤ Y := by
    exact le_max_left _ _
  have hfar : ∀ x y : ℝ, 0 < x → 0 < y → Y ≤ x ∨ Y ≤ y →
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) := by
    intro x y hx hy hlarge
    apply hfar₀ x y hx hy
    exact hlarge.imp (fun hYx => hY₀Y.trans hYx) (fun hYy => hY₀Y.trans hYy)
  have hfailure : ∀ x y : ℝ, 0 < x → 0 < y →
      ¬ Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) →
        (delta ≤ x ∨ delta ≤ y) ∧ x < Y ∧ y < Y := by
    intro x y hx hy hnot
    have hinner : delta ≤ x ∨ delta ≤ y := by
      by_contra hnotInner
      have hxdelta : x < delta := lt_of_not_ge (fun h => hnotInner (Or.inl h))
      have hydelta : y < delta := lt_of_not_ge (fun h => hnotInner (Or.inr h))
      exact hnot (hnear x y hx hxdelta hy hydelta).posSemidef
    have hxY : x < Y := by
      by_contra hnotx
      exact hnot (hfar x y hx hy (Or.inl (le_of_not_gt hnotx)))
    have hyY : y < Y := by
      by_contra hnoty
      exact hnot (hfar x y hx hy (Or.inr (le_of_not_gt hnoty)))
    exact ⟨hinner, hxY, hyY⟩
  refine ⟨delta, Y, hdelta, hdeltaY, hnear, hfar, hfailure, ?_⟩
  constructor
  · intro hall x y hx hy _ _ _
    exact hall x y hx hy
  · intro hshell x y hx hy
    by_contra hnot
    rcases hfailure x y hx hy hnot with ⟨hinner, hxY, hyY⟩
    exact hnot (hshell x y hx hy hinner hxY hyY)

end

end RHTower
