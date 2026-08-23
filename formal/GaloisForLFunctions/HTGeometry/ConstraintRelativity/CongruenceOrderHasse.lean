import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderExteriorSquare

/-!
# Hasse classification for diagonal congruence orders

The diagonal congruence order is the image of polynomial evaluation at its local sheet generators.
Over a domain with nonzero congruence parameter, equality of evaluated local data is exactly
congruence modulo the presentation ideal.  This records the presentation as a CRT-style Hasse
criterion plus representative existence and uniqueness modulo global relations.
-/

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] {a : R} {m : ℕ}

/-- The polynomial presentation quotient is the diagonal congruence order. -/
noncomputable def congruenceOrderHasseQuotientEquiv (ha : a ≠ 0) :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ≃ₐ[R] congruenceOrder a (m + 1) :=
  congruencePresentation ha

/-- The congruence-order Hasse equivalence is induced by local sheet evaluation. -/
@[simp] theorem congruenceOrderHasseQuotientEquiv_mk
    (ha : a ≠ 0) (f : MvPolynomial (Fin m) R) :
    congruenceOrderHasseQuotientEquiv ha (Ideal.Quotient.mk _ f) =
      congruenceEvalRestrict (a := a) (m := m) f := by
  simp [congruenceOrderHasseQuotientEquiv, congruencePresentation]

/-- Two global polynomials have equal congruence-order local evaluations exactly when their
difference belongs to the presentation ideal. -/
theorem congruenceOrder_congr_hasse_iff
    (ha : a ≠ 0) (f g : MvPolynomial (Fin m) R) :
    f - g ∈ congruenceIdeal a m ↔
      congruenceEvalRestrict (a := a) (m := m) f = congruenceEvalRestrict g := by
  rw [← ker_congruenceEval ha, ← ker_congruenceEvalRestrict]
  change congruenceEvalRestrict (a := a) (m := m) (f - g) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every congruence-order element has a polynomial representative, unique modulo the presentation
ideal. -/
theorem congruenceOrder_exists_unique_mod_ideal
    (ha : a ≠ 0) (z : congruenceOrder a (m + 1)) :
    ∃ f : MvPolynomial (Fin m) R,
      congruenceEvalRestrict (a := a) (m := m) f = z ∧
      ∀ g, congruenceEvalRestrict (a := a) (m := m) g = z ↔
        g - f ∈ congruenceIdeal a m := by
  obtain ⟨f, hf⟩ := congruenceEvalRestrict_surjective (a := a) (m := m) z
  refine ⟨f, hf, fun g => ?_⟩
  rw [← hf]
  exact (congruenceOrder_congr_hasse_iff ha g f).symm

end

end HTGeometry.ConstraintRelativity
