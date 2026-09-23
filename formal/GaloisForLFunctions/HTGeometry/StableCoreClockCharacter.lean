import GaloisForLFunctions.HTGeometry.StableCoreClockSemilinear
import GaloisForLFunctions.HTGeometry.ClockFamilySemilinearMobius

/-!
# The restricted clock family diagonalizes to a `C^*`-character on the core

Assembling §3(b) at the persistent core.  The ambient clock family restricts to a commuting family of
semilinear automorphisms of the core `T = stableRangeCore φ`; once the differential Lüroth theorem
provides a single differential generator `q` of `T` and an anchor scaling, the family diagonalizes to
a multiplicative character `e : C → C` on `C^*` (`clock_family_scaling_character_from_semilinear`).
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- The ambient clock family restricted to the persistent core. -/
noncomputable def stableRangeCoreClockFamily (φ : F →ₐ[C] F) (ρ : C → (F ≃ₐ[C] F))
    (hcommφ : ∀ lam : C, ∀ x, φ (ρ lam x) = ρ lam (φ x)) :
    C → (stableRangeCore φ ≃ₐ[C] stableRangeCore φ) :=
  fun lam => stableRangeCoreSymmetryAlgEquiv φ (ρ lam) (hcommφ lam)

/-- **§3(b) at the core.**  With `C` carrying the zero derivation, the restricted clock family,
given an anchor scaling `ρ_{ν₀}(q) = ν q` (`ν ≠ 0, 1, -1`) at a differential generator `q` of the
core and its homomorphism/commutation at `q`, diagonalizes to a multiplicative character. -/
theorem stableRangeCoreSymmetry_family_character
    [IsAlgClosed C] [CharZero F] [Differential C] [Differential F] [DifferentialAlgebra C F]
    (φ : F →ₐ[C] F) (hφ : ∀ x : F, φ x′ = (φ x)′)
    (ρ : C → (F ≃ₐ[C] F)) (hcommφ : ∀ lam : C, ∀ x, φ (ρ lam x) = ρ lam (φ x))
    (hCzero : ∀ c : C, (c : C)′ = 0)
    (hsemiF : ∀ lam : C, lam ≠ 0 → ∀ x : F, ρ lam x′ = algebraMap C F lam * (ρ lam x)′) :
    letI : Differential (stableRangeCore φ) :=
      derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
    ∀ (ν₀ : C) {q : stableRangeCore φ} {ν : C}, ν ≠ 0 → ν ≠ 1 → ν ≠ -1 →
      HypertranscendentalOver C q →
      differentialAdjoin C ({q} : Set (stableRangeCore φ)) = ⊤ →
      (stableRangeCoreClockFamily φ ρ hcommφ ν₀).toAlgHom q
        = algebraMap C (stableRangeCore φ) ν * q →
      (∀ lam : C, lam ≠ 0 →
        (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom
            ((stableRangeCoreClockFamily φ ρ hcommφ ν₀).toAlgHom q)
          = (stableRangeCoreClockFamily φ ρ hcommφ ν₀).toAlgHom
            ((stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom q)) →
      (∀ lam mu : C, lam ≠ 0 → mu ≠ 0 →
        (stableRangeCoreClockFamily φ ρ hcommφ (lam * mu)).toAlgHom q
          = (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom
            ((stableRangeCoreClockFamily φ ρ hcommφ mu).toAlgHom q)) →
      ∃ e : C → C,
        (∀ lam : C, lam ≠ 0 →
          (stableRangeCoreClockFamily φ ρ hcommφ lam).toAlgHom q
            = algebraMap C (stableRangeCore φ) (e lam) * q)
          ∧ (∀ lam mu : C, lam ≠ 0 → mu ≠ 0 → e (lam * mu) = e lam * e mu) := by
  letI : Differential (stableRangeCore φ) :=
    derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
  haveI : DifferentialAlgebra C (stableRangeCore φ) := by
    refine ⟨fun c => ?_⟩
    apply Subtype.ext
    rw [derivationClosedDifferential_apply]
    show ((algebraMap C F c))′ = ((algebraMap C F c′))
    exact DifferentialAlgebra.deriv_algebraMap c
  have hconstT : ∀ lam : C, (algebraMap C (stableRangeCore φ) lam)′ = 0 := by
    intro lam
    apply Subtype.ext
    rw [derivationClosedDifferential_apply]
    show ((algebraMap C (stableRangeCore φ) lam : stableRangeCore φ) : F)′ = _
    rw [show ((algebraMap C (stableRangeCore φ) lam : stableRangeCore φ) : F) = algebraMap C F lam from by
      rw [IsScalarTower.algebraMap_apply C (stableRangeCore φ) F]; rfl,
      DifferentialAlgebra.deriv_algebraMap, hCzero]
    simp
  intro ν₀ q ν hν0 hν1 hνm1 hq hqtop hanchor hcomm hmul
  have htrans : Transcendental C q := by
    simpa using hypertranscendentalOver_jet_transcendental hq 0
  have hlin : ∀ x y z : C, algebraMap C (stableRangeCore φ) x
      + algebraMap C (stableRangeCore φ) y * q
      + algebraMap C (stableRangeCore φ) z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z heq
    have hinj := transcendental_iff_injective.mp htrans
    have hP : (Polynomial.aeval q)
        (Polynomial.C x + Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X ^ (2 : ℕ)) = 0 := by
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      exact heq
    have hP0 : Polynomial.C x + Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X ^ (2 : ℕ) = 0 :=
      hinj (by rw [hP, map_zero])
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 0) hP0; simpa using this
    · have := congrArg (Polynomial.coeff · 1) hP0; simpa using this
    · have := congrArg (Polynomial.coeff · 2) hP0; simpa using this
  exact clock_family_scaling_character_from_semilinear
    (stableRangeCoreClockFamily φ ρ hcommφ) ν₀ hν0 hν1 hνm1 hq hqtop hconstT
    (fun lam hlam => stableRangeCoreSymmetry_semilinear φ hφ (ρ lam) (hcommφ lam) (hsemiF lam hlam))
    hanchor hlin hcomm hmul

end GaloisForLFunctions.HTGeometry
