import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectRationalIndependence

/-!
# Algebraic independence of a singleton Schanuel defect

Rational independence already forces every defect attached to a nonzero complex number to be
nonzero.  Over the algebraic closure of `ℚ` in `ℂ`, nonvanishing is exactly linear independence
for a singleton family.  This is the unconditional one-variable case of algebraic-coefficient
defect independence.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The Schanuel defect of a nonzero complex number is nonzero. -/
theorem schanuelDefect_ne_zero_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    schanuelDefect z ≠ 0 := by
  let x : Fin 1 → ℂ := fun _ => z
  have hx : LinearIndependent ℚ x := by
    rw [linearIndependent_unique_iff]
    simpa [x] using hz
  have hLI := schanuelDefect_linearIndependent_rational x hx
  rw [linearIndependent_unique_iff] at hLI
  simpa [x] using hLI

/-- The defect of one nonzero complex number is linearly independent over the algebraic closure
of `ℚ` in `ℂ`. -/
theorem schanuelDefect_linearIndependent_algebraic_singleton
    (z : ℂ) (hz : z ≠ 0) :
    LinearIndependent (algebraicClosure ℚ ℂ)
      (fun _ : Fin 1 => schanuelDefect z) := by
  rw [linearIndependent_unique_iff]
  exact schanuelDefect_ne_zero_of_ne_zero z hz

end


end GaloisForLFunctions.RHTower
