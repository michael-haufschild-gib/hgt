import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionCommutator

/-!
# Arithmetic neighbor actions of tent projections

Every nonzero cross-family coefficient comes from an adjacent center. Spacing
at least three gives a unique neighbor; spacing two admits a two-arm star.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

def TentAdjacent (d i e j : ℕ) : Prop :=
  coprimeCenter d i + 1 = coprimeCenter e j ∨
    coprimeCenter e j + 1 = coprimeCenter d i

theorem tentAdjacent_iff (d i e j : ℕ) :
    TentAdjacent d i e j ↔ coprimeCenter d i + 1 = coprimeCenter e j ∨
      coprimeCenter e j + 1 = coprimeCenter d i := Iff.rfl

theorem TentAdjacent.symm {d i e j : ℕ} (h : TentAdjacent d i e j) :
    TentAdjacent e j d i := Or.symm h

theorem TentAdjacent.not_dvd {d i e j : ℕ} (h : TentAdjacent d i e j) :
    ¬d + 2 ∣ coprimeCenter e j := by
  intro hd
  rcases h with h | h
  · exact not_adjacent_of_common_divisor (by omega) (coprimeCenter_dvd d i) hd h
  · exact not_adjacent_of_common_divisor (by omega) hd (coprimeCenter_dvd d i) h

theorem TentAdjacent.ne {d i e j : ℕ} (h : TentAdjacent d i e j) :
    coprimeCenter d i ≠ coprimeCenter e j := by
  rcases h with h | h <;> omega

theorem tentAdjacent_unique {d e i k j : ℕ} (hd : 1 ≤ d)
    (hi : TentAdjacent d i e j) (hk : TentAdjacent d k e j) : i = k := by
  have hs : ∀ {a b : ℕ}, a < b → coprimeCenter d a + 3 ≤ coprimeCenter d b := by
    intro a b hab
    simp only [coprimeCenter]
    nlinarith
  rcases lt_trichotomy i k with h | h | h
  · have := hs h
    rcases hi with hi | hi <;> rcases hk with hk | hk <;> omega
  · exact h
  · have := hs h
    rcases hi with hi | hi <;> rcases hk with hk | hk <;> omega

theorem coprimeExtension_add (d : ℕ) (v w : TraceData) :
    coprimeExtension d (v + w) = coprimeExtension d v + coprimeExtension d w := by
  simp [coprimeExtension, smul_add]

theorem coprimeProjection_tent_no_neighbor (d e j : ℕ)
    (hd : ¬d + 2 ∣ coprimeCenter e j) (ha : ∀ i, ¬TentAdjacent d i e j) :
    coprimeProjection d (tentVelocity e j) = 0 := by
  have hc : coprimeCoefficients d (tentVelocity e j) = 0 := by
    apply lp.ext
    funext i
    have hn : coprimeCenter d i ≠ coprimeCenter e j := by
      intro h
      exact hd (h ▸ coprimeCenter_dvd d i)
    simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
      inner_tentVelocity_cross, hn, ← tentAdjacent_iff, ha i]
  rw [coprimeProjection_eq_extension, hc]
  simp [coprimeExtension]

/-- A unique adjacent center supplies the entire infinite projection. -/
theorem coprimeProjection_tent_one_neighbor {d e i j : ℕ} (hd : 1 ≤ d)
    (h : TentAdjacent d i e j) :
    coprimeProjection d (tentVelocity e j) = (-1 / 2 : ℝ) • tentVelocity d i := by
  have hc : coprimeCoefficients d (tentVelocity e j) = lp.single 2 i (-1 / 2 : ℝ) := by
    apply lp.ext
    funext k
    have hn : coprimeCenter d k ≠ coprimeCenter e j := by
      intro hk
      exact h.not_dvd (hk ▸ coprimeCenter_dvd d k)
    by_cases hk : k = i
    · subst k
      simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
        inner_tentVelocity_cross, h.ne, ← tentAdjacent_iff, h, lp.single_apply]
    · have ha : ¬TentAdjacent d k e j := fun ha => hk (tentAdjacent_unique hd ha h)
      simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
        inner_tentVelocity_cross, hn, ← tentAdjacent_iff, ha, lp.single_apply, hk]
  rw [coprimeProjection_eq_extension, hc, coprimeExtension_single]

/-- Both adjacent centers supply the two arms of a star. -/
theorem coprimeProjection_tent_two_neighbors {d e i k j : ℕ}
    (hi : coprimeCenter d i + 1 = coprimeCenter e j)
    (hk : coprimeCenter e j + 1 = coprimeCenter d k) :
    coprimeProjection d (tentVelocity e j) =
      (-1 / 2 : ℝ) • (tentVelocity d i + tentVelocity d k) := by
  have hai : TentAdjacent d i e j := Or.inl hi
  have hak : TentAdjacent d k e j := Or.inr hk
  have hik : i ≠ k := by intro h; subst k; omega
  have hc : coprimeCoefficients d (tentVelocity e j) =
      lp.single 2 i (-1 / 2 : ℝ) + lp.single 2 k (-1 / 2 : ℝ) := by
    apply lp.ext
    funext l
    have hn : coprimeCenter d l ≠ coprimeCenter e j := by
      intro hl
      exact hai.not_dvd (hl ▸ coprimeCenter_dvd d l)
    by_cases hli : l = i
    · subst l
      simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
        inner_tentVelocity_cross, hai.ne, ← tentAdjacent_iff, hai,
        lp.single_apply, hik]
    by_cases hlk : l = k
    · subst l
      simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
        inner_tentVelocity_cross, hak.ne, ← tentAdjacent_iff, hak,
        lp.single_apply, Ne.symm hik]
    have ha : ¬TentAdjacent d l e j := by
      rintro (hl | hl)
      · apply hli
        apply coprimeCenter_injective d
        omega
      · apply hlk
        apply coprimeCenter_injective d
        omega
    simp [coprimeCoefficients_apply, ← inner_tentVelocity_velocity,
      inner_tentVelocity_cross, hn, ← tentAdjacent_iff, ha,
      lp.single_apply, hli, hlk]
  rw [coprimeProjection_eq_extension, hc, coprimeExtension_add,
    coprimeExtension_single, coprimeExtension_single, smul_add]

/-- A non-even center at least three has two positive even neighbors. -/
theorem exists_two_even_neighbors {e j : ℕ} (he : 1 ≤ e)
    (h : ¬2 ∣ coprimeCenter e j) :
    ∃ i k, coprimeCenter 0 i + 1 = coprimeCenter e j ∧
      coprimeCenter e j + 1 = coprimeCenter 0 k := by
  have hb : 3 ≤ coprimeCenter e j := by
    simp only [coprimeCenter]
    nlinarith
  have hm : coprimeCenter e j % 2 = 1 := by omega
  have hdiv := Nat.mod_add_div (coprimeCenter e j) 2
  refine ⟨coprimeCenter e j / 2 - 1, coprimeCenter e j / 2, ?_, ?_⟩ <;>
    simp only [coprimeCenter, zero_add] at * <;> omega

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
