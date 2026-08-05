import GaloisForLFunctions.HTGeometry.ClockFourierProduct

/-!
# Even coefficient families exist

Evenness of a two-sided coefficient family is a symmetry of the index, so every family that reads
only the modulus of its index is even.  The zero and constant families, and the geometric family
`r^{|k|}` that carries the analytic Wiener scale, are all of that form.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Any family reading only the modulus of the index is even.** -/
theorem evenCoeff_comp_natAbs (f : ℕ → ℝ) : EvenCoeff (fun k : ℤ => f k.natAbs) := by
  intro k
  show f (-k).natAbs = f k.natAbs
  rw [Int.natAbs_neg]

/-- The zero family is even. -/
theorem evenCoeff_zero : EvenCoeff (fun _ : ℤ => (0 : ℝ)) := fun _ => rfl

/-- Constant families are even. -/
theorem evenCoeff_const (c : ℝ) : EvenCoeff (fun _ : ℤ => c) := fun _ => rfl

/-- The geometric family carrying the analytic Wiener scale is even. -/
theorem evenCoeff_geometric (r : ℝ) : EvenCoeff (fun k : ℤ => r ^ k.natAbs) :=
  evenCoeff_comp_natAbs (fun n => r ^ n)

/-- Evenness is closed under addition and scalar multiples. -/
theorem EvenCoeff.add {f g : ℤ → ℝ} (hf : EvenCoeff f) (hg : EvenCoeff g) :
    EvenCoeff (fun k => f k + g k) := by
  intro k
  show f (-k) + g (-k) = f k + g k
  rw [hf k, hg k]

theorem EvenCoeff.const_mul {g : ℤ → ℝ} (hg : EvenCoeff g) (c : ℝ) :
    EvenCoeff (fun k => c * g k) := by
  intro k
  show c * g (-k) = c * g k
  rw [hg k]

end GaloisForLFunctions.HTGeometry
