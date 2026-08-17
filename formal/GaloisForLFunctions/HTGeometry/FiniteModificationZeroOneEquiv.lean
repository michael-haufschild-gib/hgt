import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOne

/-!
# The finite-modification zero–one law over any countably infinite index

The law is proved for products indexed by `ℕ`.  An equivalence `e : ℕ ≃ ι` transports it: the
reindexing map is a measurable equivalence carrying the product measure to the product measure, and
it carries finite-modification invariance across because a finite set of coordinates has finite
image.

This is what a product over a countable index other than `ℕ` — the primes, for instance — needs in
order to use the law.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The finite-modification zero–one law, over any index equivalent to `ℕ`.** -/
theorem measure_infinitePi_eq_zero_or_one_of_invariant_equiv
    {ι : Type*} {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (e : ℕ ≃ ι) (μ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ∀ i, Y i) {S : Set (∀ i, Y i)} (hS : MeasurableSet S)
    (hinv : ∀ x y : ∀ i, Y i, {i | x i ≠ y i}.Finite → (x ∈ S ↔ y ∈ S)) :
    Measure.infinitePi μ S = 0 ∨ Measure.infinitePi μ S = 1 := by
  classical
  set E := MeasurableEquiv.piCongrLeft Y e with hE
  have hEsymm : ∀ (z : ∀ i, Y i) (m : ℕ), (E.symm z) m = z (e m) := by
    intro z m
    simp [hE, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
  have hval : ∀ (x : ∀ m : ℕ, Y (e m)) (m : ℕ), (E x) (e m) = x m := by
    intro x m
    have h := hEsymm (E x) m
    rw [E.symm_apply_apply] at h
    exact h.symm
  have hpre : MeasurableSet (E ⁻¹' S) := E.measurable hS
  have hinv' : ∀ x y : ∀ m : ℕ, Y (e m), {m | x m ≠ y m}.Finite →
      (x ∈ E ⁻¹' S ↔ y ∈ E ⁻¹' S) := by
    intro x y hfin
    refine hinv (E x) (E y) ?_
    refine Set.Finite.subset (hfin.image e) ?_
    intro i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = e m := ⟨e.symm i, (Equiv.apply_symm_apply e i).symm⟩
    refine ⟨m, ?_, rfl⟩
    intro hcon
    exact hi (by rw [hval x m, hval y m, hcon])
  have hzo := measure_infinitePi_eq_zero_or_one_of_invariant (fun m => μ (e m))
    (fun m => a (e m)) hpre hinv'
  have hmap := Measure.infinitePi_map_piCongrLeft μ e
  rw [← hmap, Measure.map_apply E.measurable hS]
  exact hzo

/-- The primes are denumerable, so they carry an equivalence with `ℕ`. -/
def natEquivPrimes : ℕ ≃ Nat.Primes := by
  classical
  letI : Encodable Nat.Primes := Encodable.ofCountable _
  letI : Denumerable Nat.Primes := Denumerable.ofEncodableOfInfinite Nat.Primes
  exact (Denumerable.eqv Nat.Primes).symm

/-- **The finite-modification zero–one law for a product indexed by the primes.** -/
theorem measure_infinitePi_primes_eq_zero_or_one_of_invariant
    {Y : Nat.Primes → Type*} [∀ p, MeasurableSpace (Y p)]
    (μ : ∀ p, Measure (Y p)) [∀ p, IsProbabilityMeasure (μ p)]
    (a : ∀ p, Y p) {S : Set (∀ p, Y p)} (hS : MeasurableSet S)
    (hinv : ∀ x y : ∀ p, Y p, {p | x p ≠ y p}.Finite → (x ∈ S ↔ y ∈ S)) :
    Measure.infinitePi μ S = 0 ∨ Measure.infinitePi μ S = 1 :=
  measure_infinitePi_eq_zero_or_one_of_invariant_equiv natEquivPrimes μ a hS hinv

end GaloisForLFunctions.HTGeometry

end
