import GaloisForLFunctions.HTGeometry.KleinbockMargulis.PolynomialGood

namespace RHTower.Sieve

open MeasureTheory Set

/-- A uniform quadratic cardinality bound for finite separated subsets yields a quantitative
Lebesgue-measure bound for the ambient real set. -/
theorem volume_toReal_le_of_separated_finset_mul_sq_le
    {S : Set ℝ} {δ v R : ℝ}
    (hδ : 0 < δ) (hv : 0 < v) (hR : 0 ≤ R)
    (hcard : ∀ E : Finset ℝ, (E : Set ℝ) ⊆ S →
      (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x - y|) →
      (E.card : ℝ) * v ^ 2 ≤ R) :
    (volume S).toReal ≤ 2 * δ * (R / v ^ 2 + 1) := by
  by_contra hnot
  have hmeasure : 2 * δ * (R / v ^ 2 + 1) < (volume S).toReal :=
    lt_of_not_ge hnot
  let x : ℝ := R / v ^ 2
  let k : ℕ := ⌊x⌋₊ + 1
  have hvSq : 0 < v ^ 2 := sq_pos_of_pos hv
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hkLe : (k : ℝ) ≤ x + 1 := by
    have hfloor := Nat.floor_le hx
    dsimp only [k]
    push_cast
    linarith
  have hxk : x < (k : ℝ) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x)
  have hsepMeasure : 2 * (k : ℝ) * δ < (volume S).toReal := by
    have hle : 2 * (k : ℝ) * δ ≤ 2 * δ * (x + 1) := by
      nlinarith
    exact hle.trans_lt (by simpa only [x] using hmeasure)
  obtain ⟨E, hES, hEcard, hEsep⟩ :=
    GaloisForLFunctions.HTGeometry.KleinbockMargulis.exists_finset_separated
      hδ k hsepMeasure
  have hbound := hcard E hES hEsep
  have hRlt : R < (k : ℝ) * v ^ 2 := by
    rw [← div_lt_iff₀ hvSq]
    simpa only [x] using hxk
  rw [hEcard] at hbound
  norm_num only [Nat.cast_add, Nat.cast_one] at hbound
  nlinarith

end RHTower.Sieve
