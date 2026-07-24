import GaloisForLFunctions.HTGeometry.JetScalingClockField

/-!
# The clock composition law on `C⟨y⟩`

The clock on the field `C⟨y⟩` is a homomorphism of the multiplicative group:
`ρ_λ ∘ ρ_μ = ρ_{λμ}`.  This is the `hmul` hypothesis of the abstract clock family.  It follows from
the ring-level composition law `clockDilationAlgHom_comp` by fraction-field surjectivity: every element
is a ratio of polynomial values, on which both sides reduce to the ring clock.
-/

namespace GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C]

/-- **Clock composition law on `C⟨y⟩`.**  `ρ_λ(ρ_μ z) = ρ_{λμ} z`. -/
theorem clockDilationFieldEquiv_comp (lam mu : C) (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (z : ScalarDifferentialField C) :
    clockDilationFieldEquiv lam hlam (clockDilationFieldEquiv mu hmu z)
      = clockDilationFieldEquiv (lam * mu) (mul_ne_zero hlam hmu) z := by
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective (DifferentialPolynomial Unit C) z
  rw [← hxy]
  simp only [map_div₀, clockDilationFieldEquiv_algebraMap, clockDilationAlgHom_apply_apply]

end

end GaloisForLFunctions
