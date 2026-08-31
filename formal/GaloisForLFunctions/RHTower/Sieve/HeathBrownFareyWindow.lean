import GaloisForLFunctions.RHTower.Sieve.LargeSieveDual
import GaloisForLFunctions.RHTower.Sieve.LargeSieveCircleSharp
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-!
# Farey packing in a Heath--Brown collision window

Primitive positive directions are reduced fractions.  Farey separation therefore gives the exact
quadratic packing bound for all directions in one short ratio window.  This is the good-pair
counting input in Heath--Brown's sparse collision Lemma 6.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Real slope of a positive integral direction. -/
def heathBrownFareyValue (p : ℕ × ℕ) : ℝ :=
  (p.1 : ℝ) / (p.2 : ℝ)

/-- Reduced positive directions of order at most `Q` whose slopes lie in `[a,b]`. -/
def heathBrownFareyWindow (Q : ℕ) (a b : ℝ) : Finset (ℕ × ℕ) :=
  (fareySet Q).filter fun p => a ≤ heathBrownFareyValue p ∧ heathBrownFareyValue p ≤ b

theorem mem_heathBrownFareyWindow {Q : ℕ} {a b : ℝ} {p : ℕ × ℕ} :
    p ∈ heathBrownFareyWindow Q a b ↔
      p ∈ fareySet Q ∧ a ≤ heathBrownFareyValue p ∧ heathBrownFareyValue p ≤ b := by
  simp [heathBrownFareyWindow]

/-- Reduced positive directions have distinct real slopes. -/
theorem heathBrownFareyValue_injOn_fareySet {Q : ℕ} (hQ : 1 ≤ Q) :
    Set.InjOn heathBrownFareyValue (fareySet Q : Set (ℕ × ℕ)) := by
  intro p hp q hq hpq
  by_contra hpne
  have hsep := fareySet_sep p hp q hq hpne
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  change 1 / (Q : ℝ) ^ 2 ≤ toIntDist
    (heathBrownFareyValue q - heathBrownFareyValue p) at hsep
  rw [← hpq, sub_self] at hsep
  have hzero : toIntDist (0 : ℝ) = 0 := by simp [toIntDist]
  rw [hzero] at hsep
  linarith

/-- **Heath--Brown Farey-window packing.** A ratio interval of width `b-a` contains at most
`(b-a)Q²+1` primitive positive directions of height at most `Q`. -/
theorem card_heathBrownFareyWindow_le {Q : ℕ} (hQ : 1 ≤ Q)
    {a b : ℝ} (hab : a ≤ b) :
    ((heathBrownFareyWindow Q a b).card : ℝ) ≤
      (b - a) * (Q : ℝ) ^ 2 + 1 := by
  let W := heathBrownFareyWindow Q a b
  let V := W.image heathBrownFareyValue
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hL : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hinj : Set.InjOn heathBrownFareyValue (W : Set (ℕ × ℕ)) :=
    (heathBrownFareyValue_injOn_fareySet hQ).mono fun p hp =>
      (mem_heathBrownFareyWindow.mp hp).1
  have hcard : V.card = W.card := Finset.card_image_of_injOn hinj
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      1 / (Q : ℝ) ^ 2 ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hqW, rfl⟩ := Finset.mem_image.mp hy
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hxy rfl
    have hcirc := fareySet_sep p
      (mem_heathBrownFareyWindow.mp hpW).1 q
      (mem_heathBrownFareyWindow.mp hqW).1 hpq
    have habs := hcirc.trans
      (toIntDist_le_abs
        ((q.1 : ℝ) / (q.2 : ℝ) - (p.1 : ℝ) / (p.2 : ℝ)))
    simpa [heathBrownFareyValue, abs_sub_comm] using habs
  have hsub : ∀ x ∈ V, x ∈ Set.Icc a b := by
    intro x hx
    obtain ⟨p, hpW, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_heathBrownFareyWindow.mp hpW).2
  have hbound := card_le_of_separated_of_subset_Icc hL hab V hsep hsub
  rw [hcard] at hbound
  change (W.card : ℝ) ≤ _
  convert hbound using 1
  field_simp

end

end RHTower.Sieve
