import GaloisForLFunctions.HTGeometry.EventSecondOrderSoldering

/-!
# Factor-retaining covariant solder law

A covariant composite normally permits cancellation between the covariance defects of its two
factors.  If the two transported defects are retained in disjoint grades, cancellation is
impossible.  Surjectivity of the first factor and injectivity of the second then force both
factors to be covariant separately.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R X Y Z : Type*}
variable [CommRing R]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y]
variable [AddCommGroup Z] [Module R Z]

/-- **Factor-retention law.**  A covariant two-step solder with disjointly graded internal
defects, a surjective first arrow, and an injective second arrow has covariant factors. -/
theorem factorRetaining_covariantSolder
    (A : Module.End R Z) (B : Module.End R Y) (C : Module.End R X)
    (j : Y →ₗ[R] Z) (r : X →ₗ[R] Y)
    (P Q : Submodule R Z)
    (hdisjoint : Disjoint P Q)
    (hcomposite :
      A.comp (splitQuadraticSolder j r) =
        (splitQuadraticSolder j r).comp C)
    (hr : Function.Surjective r)
    (hj : Function.Injective j)
    (hleftGrade : ∀ x,
      leftChannelCovariantDefect A B j (r x) ∈ P)
    (hrightGrade : ∀ x,
      j (rightChannelCovariantDefect B C r x) ∈ Q) :
    A.comp j = j.comp B ∧ B.comp r = r.comp C := by
  have hsum := splitQuadraticSolder_covariant_cancellation A B C j r
  rw [hcomposite, sub_self] at hsum
  have hleftTransport :
      (leftChannelCovariantDefect A B j).comp r = 0 := by
    ext x
    have hx := LinearMap.congr_fun hsum x
    simp only [LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] at hx
    have hleftQ : leftChannelCovariantDefect A B j (r x) ∈ Q := by
      have heq :
          leftChannelCovariantDefect A B j (r x) =
            -j (rightChannelCovariantDefect B C r x) := by
        exact eq_neg_of_add_eq_zero_left hx
      rw [heq]
      exact Q.neg_mem (hrightGrade x)
    exact
      (Submodule.disjoint_def.mp hdisjoint)
        _ (hleftGrade x) hleftQ
  have hrightTransport :
      j.comp (rightChannelCovariantDefect B C r) = 0 := by
    ext x
    have hx := LinearMap.congr_fun hsum x
    have hleftZero := LinearMap.congr_fun hleftTransport x
    simp only [LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] at hx hleftZero ⊢
    rw [hleftZero, zero_add] at hx
    exact hx
  constructor
  · apply sub_eq_zero.mp
    change leftChannelCovariantDefect A B j = 0
    ext y
    obtain ⟨x, rfl⟩ := hr y
    exact LinearMap.congr_fun hleftTransport x
  · apply sub_eq_zero.mp
    change rightChannelCovariantDefect B C r = 0
    ext x
    apply hj
    simpa using LinearMap.congr_fun hrightTransport x

end

end GaloisForLFunctions.HTGeometry
