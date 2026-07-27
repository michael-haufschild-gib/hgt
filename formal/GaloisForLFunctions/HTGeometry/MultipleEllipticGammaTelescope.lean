import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacket

/-!
# Telescoping a face coordinate along one deleted direction

Iterating the intrinsic coface equation expresses the total displacement of a face coordinate under
`k` translations in a structural direction as a finite sum of translates of the *next* face.  This
is the exact algebraic shape the free-shift nonsummability and orbit-height arguments consume: a
germ is `k`-fold periodic in a direction precisely when that telescoped sum of lower-face translates
vanishes.

* **`multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum`** — the telescope;
* **`sum_translate_eq_zero_of_periodic`** — the obstruction form: a periodic face coordinate forces
  the telescoped sum of lower-face translates to vanish;
* **`not_periodic_of_sum_translate_ne_zero`** — its contrapositive, the criterion the star
  injectivity hypothesis needs in the case of a single face.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Telescoped coface displacement.**  Translating a face coordinate `k` times in a deleted
direction displaces it by the sum of the first `k` translates of the next face. -/
theorem multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J) (k : ℕ) :
    addTranslationMeroEquiv ((k : ℂ) * τ q)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) -
      multipleEllipticGammaLogDerivFaceMero τ hτ J =
      ∑ j ∈ Finset.range k, addTranslationMeroEquiv ((j : ℂ) * τ q)
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) := by
  induction k with
  | zero =>
      simp [addTranslationMeroEquiv_zero_apply]
  | succ k ih =>
      set F := multipleEllipticGammaLogDerivFaceMero τ hτ J with hF
      set G := multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) with hG
      have hcast : (((k + 1 : ℕ)) : ℂ) * τ q = (k : ℂ) * τ q + τ q := by push_cast; ring
      have hstep : addTranslationMeroEquiv ((k : ℂ) * τ q) (addTranslationMeroEquiv (τ q) F) -
          addTranslationMeroEquiv ((k : ℂ) * τ q) F =
          addTranslationMeroEquiv ((k : ℂ) * τ q) G := by
        rw [← map_sub, hF, hG,
          multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq]
      rw [hcast, ← addTranslationMeroEquiv_add, Finset.sum_range_succ]
      calc addTranslationMeroEquiv ((k : ℂ) * τ q) (addTranslationMeroEquiv (τ q) F) - F
          = (addTranslationMeroEquiv ((k : ℂ) * τ q) (addTranslationMeroEquiv (τ q) F) -
              addTranslationMeroEquiv ((k : ℂ) * τ q) F) +
            (addTranslationMeroEquiv ((k : ℂ) * τ q) F - F) := by abel
        _ = addTranslationMeroEquiv ((k : ℂ) * τ q) G +
            ∑ j ∈ Finset.range k, addTranslationMeroEquiv ((j : ℂ) * τ q) G := by
            rw [hstep, ih]
        _ = (∑ j ∈ Finset.range k, addTranslationMeroEquiv ((j : ℂ) * τ q) G) +
            addTranslationMeroEquiv ((k : ℂ) * τ q) G := by abel

/-- **Obstruction form.**  If a face coordinate is `k`-fold periodic in a deleted direction, the
telescoped sum of translates of the next face vanishes. -/
theorem sum_translate_eq_zero_of_periodic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J) {k : ℕ}
    (hper : addTranslationMeroEquiv ((k : ℂ) * τ q)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        multipleEllipticGammaLogDerivFaceMero τ hτ J) :
    ∑ j ∈ Finset.range k, addTranslationMeroEquiv ((j : ℂ) * τ q)
      (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) = 0 := by
  rw [← multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum τ hτ J hq k, hper, sub_self]

/-- **Criterion form.**  A nonvanishing telescoped sum excludes `k`-fold periodicity of the face
coordinate in that direction. -/
theorem not_periodic_of_sum_translate_ne_zero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J) {k : ℕ}
    (hsum : ∑ j ∈ Finset.range k, addTranslationMeroEquiv ((j : ℂ) * τ q)
      (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) ≠ 0) :
    addTranslationMeroEquiv ((k : ℂ) * τ q)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      multipleEllipticGammaLogDerivFaceMero τ hτ J :=
  fun hper => hsum (sum_translate_eq_zero_of_periodic τ hτ J hq hper)

/-- The first instance: one translation displaces the face coordinate by exactly the next face, so
a nonzero next face already excludes one-step periodicity. -/
theorem not_periodic_one_of_next_face_ne_zero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hne : multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) ≠ 0) :
    addTranslationMeroEquiv (τ q) (multipleEllipticGammaLogDerivFaceMero τ hτ J) ≠
      multipleEllipticGammaLogDerivFaceMero τ hτ J := by
  intro hper
  apply hne
  rw [← multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq, hper, sub_self]

end

end GaloisForLFunctions
