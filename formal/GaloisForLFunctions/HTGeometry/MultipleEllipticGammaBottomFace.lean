import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.EllipticGammaDefectFieldEscape

/-!
# The bottom face of the hierarchy is a translated order-one elliptic gamma

A deleted face with exactly two surviving parameters carries the order-one coordinate: reindexing
the two survivors and applying the two-period normalization identifies the face coordinate with a
fixed translate of the genuine elliptic-gamma logarithmic derivative.  This is the bridge that lets
the order-one packet theorem serve as the bottom-layer atomicity input of the all-order argument.

* `multipleEllipticGammaLogDerivMero_congr` — parameter congruence;
* **`multipleEllipticGammaLogDerivFaceMero_two_surviving`** — the identification.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

theorem multipleEllipticGammaLogDerivMero_congr {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ₁ τ₂ : κ → ℂ) (h : τ₁ = τ₂) (h₁ : ∀ i, 0 < (τ₁ i).im) (h₂ : ∀ i, 0 < (τ₂ i).im) :
    multipleEllipticGammaLogDerivMero τ₁ h₁ = multipleEllipticGammaLogDerivMero τ₂ h₂ := by
  subst h
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two surviving parameters of a deleted face, as an indexing equivalence. -/
def bottomFaceEquiv {J : Finset ι} {a b : ι} (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b) :
    Fin 2 ≃ MultipleEllipticGammaFaceIndex J where
  toFun k := if k = 0 then ⟨a, haJ⟩ else ⟨b, hbJ⟩
  invFun i := if (i : ι) = a then 0 else 1
  left_inv k := by
    fin_cases k
    · simp
    · simp [hab.symm]
  right_inv i := by
    rcases hJ (i : ι) i.2 with h | h
    · simp only [h]
      exact Subtype.ext h.symm
    · have hne : (i : ι) ≠ a := by
        rw [h]
        exact fun hh => hab hh.symm
      simp only [hne]
      exact Subtype.ext h.symm

/-- **A face with two surviving parameters carries a translated order-one elliptic gamma.** -/
theorem multipleEllipticGammaLogDerivFaceMero_two_surviving
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b) :
    multipleEllipticGammaLogDerivFaceMero τ hτ J =
      addTranslationMeroEquiv (-(1 + τ b) / 2)
        (ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b)) := by
  classical
  set e := bottomFaceEquiv haJ hbJ hab hJ with hedef
  have hparams : (fun k : Fin 2 => multipleEllipticGammaFaceParameters τ J (e k)) =
      ![τ a, τ b] := by
    funext k
    fin_cases k
    · simp [hedef, bottomFaceEquiv, multipleEllipticGammaFaceParameters]
    · simp [hedef, bottomFaceEquiv, multipleEllipticGammaFaceParameters]
  have hpos : ∀ k : Fin 2, 0 < (![τ a, τ b] k).im := by
    intro k
    fin_cases k
    · exact hτ a
    · exact hτ b
  calc multipleEllipticGammaLogDerivFaceMero τ hτ J
      = multipleEllipticGammaLogDerivMero
          (fun k : Fin 2 => multipleEllipticGammaFaceParameters τ J (e k))
          (fun k => hτ (e k : ι)) :=
        (multipleEllipticGammaLogDerivMero_reindex e (multipleEllipticGammaFaceParameters τ J)
          (fun i => hτ (i : ι))).symm
    _ = multipleEllipticGammaLogDerivMero ![τ a, τ b] hpos :=
        multipleEllipticGammaLogDerivMero_congr _ _ hparams _ _
    _ = addTranslationMeroEquiv (-(1 + τ b) / 2)
          (ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b)) :=
        multipleEllipticGammaLogDerivMero_fin_two (τ a) (τ b) (hτ a) (hτ b)

end

end GaloisForLFunctions
