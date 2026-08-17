import GaloisForLFunctions.HTGeometry.JetTailTrivial
import GaloisForLFunctions.HTGeometry.QuadraticLevelFour

/-!
# The quadratic orbifold tails are trivial

For `z ↦ z² + 1` and `z ↦ (z − 1)²` the substitution endomorphism of the free jet field has no
nonconstant fixed element at any jet order.  The three low levels are the classical invariant
structures — an invariant rational differential, a rational affine connection, a rational projective
structure — all of which these maps are already known to lack; the descent chain removes every level
above them.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The orbifold tail of `z ↦ z² + 1` is trivial.** -/
theorem quadOne_fixed_isConst (K : ℕ) {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, K < j → JetField.pd ((), j) g = 0)
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e :=
  fixed_isConst _ quadOne_substitutionDeriv_ne_zero
    (fun _ hw hwfix => quadOne_fixed_of_order_one hw hwfix)
    quadOne_not_hasNormalizingShift_two quadOne_not_hasNormalizingShift_three K hg hgfix

/-- **The orbifold tail of `z ↦ (z − 1)²` is trivial.** -/
theorem quadTwo_fixed_isConst (K : ℕ) {g : JetField ℂ Unit}
    (hg : ∀ j : ℕ, K < j → JetField.pd ((), j) g = 0)
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e :=
  fixed_isConst _ quadTwo_substitutionDeriv_ne_zero
    (fun _ hw hwfix => quadTwo_fixed_of_order_one hw hwfix)
    quadTwo_not_hasNormalizingShift_two quadTwo_not_hasNormalizingShift_three K hg hgfix

theorem exists_pd_order_bound {C : Type*} [Field C] (u : JetField C Unit) :
    ∃ K : ℕ, ∀ j : ℕ, K < j → JetField.pd ((), j) u = 0 := by
  classical
  obtain ⟨s, hs⟩ := JetField.exists_finset_pd_eq_zero (C := C) (ι := Unit) u
  refine ⟨s.sup (fun p => p.2), fun j hj => hs ((), j) ?_⟩
  intro hmem
  have hle := Finset.le_sup (f := fun p : Unit × ℕ => p.2) hmem
  simp only at hle
  omega

/-- **`Tail(z² + 1) = ℂ`.**  Every fixed element of the substitution endomorphism is constant. -/
theorem quadOne_tail_trivial {g : JetField ℂ Unit}
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne)
      quadOne_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  obtain ⟨K, hK⟩ := exists_pd_order_bound g
  exact quadOne_fixed_isConst K hK hgfix

/-- **`Tail((z − 1)²) = ℂ`.** -/
theorem quadTwo_tail_trivial {g : JetField ℂ Unit}
    (hgfix : jetSubstitution (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo)
      quadTwo_substitutionDeriv_ne_zero g = g) :
    ∃ e : ℂ, g = algebraMap ℂ (JetField ℂ Unit) e := by
  obtain ⟨K, hK⟩ := exists_pd_order_bound g
  exact quadTwo_fixed_isConst K hK hgfix

end

end GaloisForLFunctions.HTGeometry
