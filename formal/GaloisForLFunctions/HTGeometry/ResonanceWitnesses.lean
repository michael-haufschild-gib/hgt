import GaloisForLFunctions.HTGeometry.Resonance

/-!
# Resonant weights exist, and not only the trivial one

Coordinate resonance asks that every coordinate weight kill its own frequency.  The zero weight
does so over every frequency family, and every frequency family over the zero group.  Beyond
those, a single torsion coordinate resonates: a weight concentrated at one index resonates exactly
when that index's frequency is killed by its value, which happens with nonzero weight in every
nontrivial torsion group.
-/

namespace GaloisForLFunctions

/-- The zero weight is coordinate resonant over every frequency family. -/
theorem coordinateResonant_zero {ι A : Type*} [AddCommGroup A] (ω : ι → A) :
    coordinateResonant ω 0 := by
  intro i
  simp

/-- Every weight is coordinate resonant over the zero frequency family. -/
theorem coordinateResonant_of_frequencies_zero {ι A : Type*} [AddCommGroup A] (m : ι →₀ ℤ) :
    coordinateResonant (fun _ : ι => (0 : A)) m := by
  intro i
  simp

/-- **A single torsion coordinate resonates.**  A weight concentrated at one index is coordinate
resonant exactly when that index's frequency is killed by the weight value. -/
theorem coordinateResonant_single {ι A : Type*} [AddCommGroup A] [DecidableEq ι]
    (ω : ι → A) (i₀ : ι) (z : ℤ) (hz : z • ω i₀ = 0) :
    coordinateResonant ω (Finsupp.single i₀ z) := by
  intro i
  by_cases h : i₀ = i
  · subst h
    simpa using hz
  · simp [h]

/-- Coordinate resonance is closed under restriction of the weight to a smaller support. -/
theorem coordinateResonant_of_eq_zero_or {ι A : Type*} [AddCommGroup A]
    {ω : ι → A} {m n : ι →₀ ℤ} (hm : coordinateResonant ω m)
    (h : ∀ i, n i = m i ∨ n i = 0) :
    coordinateResonant ω n := by
  intro i
  rcases h i with hi | hi
  · rw [hi]; exact hm i
  · rw [hi]; simp

/-- In a nontrivial cyclic group the resonance is realized by a nonzero weight. -/
theorem coordinateResonant_zmod {ι : Type*} [DecidableEq ι] (n : ℕ) (i₀ : ι) :
    coordinateResonant (fun _ : ι => (1 : ZMod n)) (Finsupp.single i₀ (n : ℤ)) := by
  refine coordinateResonant_single _ i₀ (n : ℤ) ?_
  simp [zsmul_eq_mul]

end GaloisForLFunctions
