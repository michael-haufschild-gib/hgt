import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Divisibility
import Mathlib.NumberTheory.FrobeniusNumber

/-! # Spectral content of a missing wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private def occupiedLabels (v : MissingWave) : Set ℕ := Subtype.val '' {k : ℕ+ | v.val k ≠ 0}

private theorem content_pos (v : MissingWave) : 0 < Nat.setGcd (occupiedLabels v) := by
  apply Nat.pos_of_ne_zero
  intro h
  apply missingWave_ne_zero v
  apply lp.ext
  funext k
  by_contra hk
  have hd := Nat.setGcd_dvd_of_mem (s := occupiedLabels v) (n := k.val) ⟨k,hk,rfl⟩
  rw [h,zero_dvd_iff] at hd
  exact k.ne_zero hd

/-- Greatest common divisor of the occupied labels. Its divisors can all be read from surviving native levels. -/
def occupationContent (v : MissingWave) : ℕ+ := ⟨Nat.setGcd (occupiedLabels v),content_pos v⟩

theorem dvd_content_iff (a : ℕ+) (v : MissingWave) :
    a ∣ occupationContent v ↔ ∀ k : ℕ+, v.val k ≠ 0 → a ∣ k := by
  rw [PNat.dvd_iff]
  change a.val ∣ Nat.setGcd (occupiedLabels v) ↔ _
  rw [Nat.dvd_setGcd_iff]
  constructor
  · intro h k hk
    exact PNat.dvd_iff.mpr (h _ ⟨k,hk,rfl⟩)
  · rintro h _ ⟨k,hk,rfl⟩
    exact PNat.dvd_iff.mp (h k hk)

theorem preimage_iff_dvd_content (a : ℕ+) (v : MissingWave) :
    (∃! u : MissingWave, insertMissing a u = v) ↔ a ∣ occupationContent v := by
  rw [insertion_preimage_iff_native,dvd_content_iff]
  constructor
  · intro h k hk
    obtain ⟨j,rfl⟩ := number_surjective k
    by_contra hn
    exact hk ((native_level_occurs_iff _ _).mp (h j hn))
  · intro h j hj
    apply (native_level_occurs_iff _ _).mpr
    by_contra hn
    exact hj (h _ hn)

theorem content_eq_of_spectrum {v w : MissingWave} (h : missingSpectrum v = missingSpectrum w) :
    occupationContent v = occupationContent w := by
  have he (a : ℕ+) : a ∣ occupationContent v ↔ a ∣ occupationContent w := by
    rw [← preimage_iff_dvd_content,← preimage_iff_dvd_content]
    exact same_spectrum_same_factors h a
  exact PNat.dvd_antisymm ((he _).mp dvd_rfl) ((he _).mpr dvd_rfl)

/-- Occupation insertion multiplies the entire common divisor, including every prime multiplicity. -/
theorem content_insert (a : ℕ+) (v : MissingWave) :
    occupationContent (insertMissing a v) = a*occupationContent v := by
  have hl : a*occupationContent v ∣ occupationContent (insertMissing a v) := by
    apply (dvd_content_iff _ _).mpr
    intro k hk
    by_cases h : k ∈ Set.range (insertLabels a)
    · obtain ⟨n,rfl⟩ := h
      change insertWave a v.val (a*n) ≠ 0 at hk
      rw [insertWave_at] at hk
      exact mul_dvd_mul_left a ((dvd_content_iff _ v).mp dvd_rfl n hk)
    · exact (hk (insertWave_off a v.val k h)).elim
  obtain ⟨d,hd⟩ := (dvd_mul_right a (occupationContent v)).trans hl
  have hdiv : d ∣ occupationContent v := by
    apply (dvd_content_iff _ _).mpr
    intro k hk
    have hmem : (insertMissing a v).val (a*k) ≠ 0 := by change insertWave a v.val (a*k) ≠ 0; rwa [insertWave_at]
    have hs := (dvd_content_iff _ _).mp (dvd_refl (occupationContent (insertMissing a v))) _ hmem
    rw [hd] at hs
    exact PNat.dvd_iff.mpr ((Nat.mul_dvd_mul_iff_left a.pos).mp (PNat.dvd_iff.mp hs))
  apply PNat.dvd_antisymm _ hl
  rw [hd]
  exact mul_dvd_mul_left a hdiv

#print axioms dvd_content_iff
#print axioms preimage_iff_dvd_content
#print axioms content_eq_of_spectrum
#print axioms content_insert

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
