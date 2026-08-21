import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import GaloisForLFunctions.HTGeometry.PolynomialTotalDerivative
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# An algebraic element carries no new jets

Adjoining an element algebraic over a differential field produces a field that is again closed
under the derivation, so the differential field it generates is already the ordinary field it
generates.  Its degree is therefore the degree of the minimal polynomial: a differential degree
computation collapses to an order-zero one.

The mechanism is implicit differentiation on the minimal equation.  Differentiating
`m(a) = 0` splits, by the total derivative of a polynomial value, into the contribution of the
coefficients — which stay in the base field — and `m'(a) · a'`.  In characteristic zero `m'(a)`
is nonzero because `m` is minimal and `deg m' < deg m`, so `a'` is a rational expression in `a`
with coefficients in the base field.  That the whole generated field is then stable follows by
adjunction: the elements whose derivative stays inside form an intermediate field.

* `derivPart` — the derivation-stable part of an intermediate field;
* `deriv_mem_adjoin_of_isAlgebraic`;
* `derivationClosed_adjoin_of_isAlgebraic`;
* `differentialAdjoin_singleton_eq_adjoin`;
* `finrank_differentialAdjoin_singleton`, `finrank_eq_of_differentialAdjoin_singleton_eq_top`;
* `subfieldDifferential`, `subfield_differentialAlgebra` — the restricted derivation on a
  derivation-closed subfield;
* `derivationClosed_differentialAlgebra` — the same for a derivation-closed intermediate field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Differential F] [Differential K] [DifferentialAlgebra F K]

/-- The part of an intermediate field whose derivative stays inside it. -/
def derivPart (L : IntermediateField F K) : IntermediateField F K where
  carrier := {x | x ∈ L ∧ x′ ∈ L}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨L.mul_mem hx hy, ?_⟩
    rw [Derivation.leibniz]
    exact L.add_mem (L.mul_mem hx hy') (L.mul_mem hy hx')
  one_mem' := ⟨L.one_mem, by rw [Differential.deriv.map_one_eq_zero]; exact L.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨L.add_mem hx hy, by rw [map_add]; exact L.add_mem hx' hy'⟩
  zero_mem' := ⟨L.zero_mem, by rw [map_zero]; exact L.zero_mem⟩
  algebraMap_mem' := fun b =>
    ⟨L.algebraMap_mem b, by rw [deriv_algebraMap]; exact L.algebraMap_mem _⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨L.inv_mem hx, ?_⟩
    rw [Derivation.leibniz_inv]
    have hxinv : x⁻¹ ∈ L := L.inv_mem hx
    have hsq : x⁻¹ ^ (2 : ℕ) ∈ L := by simpa [pow_two] using L.mul_mem hxinv hxinv
    exact L.mul_mem (L.neg_mem hsq) hx'

@[simp] theorem mem_derivPart {L : IntermediateField F K} {x : K} :
    x ∈ derivPart L ↔ x ∈ L ∧ x′ ∈ L := Iff.rfl

theorem derivPart_le (L : IntermediateField F K) : derivPart L ≤ L := fun _ hx => hx.1

/-- **The derivative of an algebraic element lies in the field that element generates.** -/
theorem deriv_mem_adjoin_of_isAlgebraic [CharZero F] {a : K} (ha : IsAlgebraic F a) :
    a′ ∈ IntermediateField.adjoin F ({a} : Set K) := by
  classical
  have hmem : ∀ p : Polynomial F,
      Polynomial.aeval a p ∈ IntermediateField.adjoin F ({a} : Set K) := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin F {a} (Polynomial.aeval_mem_adjoin_singleton F a)
  have hint : IsIntegral F a := ha.isIntegral
  set m : Polynomial F := minpoly F a with hm
  have hm0 : m ≠ 0 := minpoly.ne_zero hint
  have hmdeg : 0 < m.natDegree := minpoly.natDegree_pos hint
  set M : Polynomial K := m.map (algebraMap F K) with hM
  have hMeval : Polynomial.eval a M = 0 := by
    rw [hM, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval F a
  have hdm0 : Polynomial.derivative m ≠ 0 := by
    intro hcon
    have hdeg := Polynomial.derivative_eq_zero.mp hcon
    omega
  have hB : Polynomial.eval a (Polynomial.derivative M)
      = Polynomial.aeval a (Polynomial.derivative m) := by
    rw [hM, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def]
  have hBne : Polynomial.eval a (Polynomial.derivative M) ≠ 0 := by
    rw [hB]
    intro hcon
    have hle := minpoly.degree_le_of_ne_zero F a hdm0 hcon
    have hlt := Polynomial.degree_derivative_lt hm0
    rw [← hm] at hle
    exact absurd hle (not_le.mpr hlt)
  have hcd : coeffDeriv M = (coeffDeriv m).map (algebraMap F K) := by
    refine Polynomial.ext fun i => ?_
    rw [coeffDeriv_coeff, hM, Polynomial.coeff_map, Polynomial.coeff_map, coeffDeriv_coeff,
      deriv_algebraMap]
  have hA : Polynomial.eval a (coeffDeriv M) = Polynomial.aeval a (coeffDeriv m) := by
    rw [hcd, Polynomial.eval_map, Polynomial.aeval_def]
  have hchain := deriv_eval M a
  rw [hMeval, map_zero] at hchain
  have hmul : Polynomial.eval a (Polynomial.derivative M) * a′
      = - Polynomial.eval a (coeffDeriv M) := by linear_combination -hchain
  have hval : a′ = - Polynomial.aeval a (coeffDeriv m)
      * (Polynomial.aeval a (Polynomial.derivative m))⁻¹ := by
    rw [← hA, ← hB]
    field_simp
    linear_combination hmul
  rw [hval]
  exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ (hmem _))
    (IntermediateField.inv_mem _ (hmem _))

/-- **Adjoining an algebraic element to a differential field gives a differential field.** -/
theorem derivationClosed_adjoin_of_isAlgebraic [CharZero F] {a : K} (ha : IsAlgebraic F a) :
    DerivationClosed (IntermediateField.adjoin F ({a} : Set K)) := by
  intro x hx
  have hle : IntermediateField.adjoin F ({a} : Set K)
      ≤ derivPart (IntermediateField.adjoin F ({a} : Set K)) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl : y = a)
    exact ⟨IntermediateField.subset_adjoin F _ rfl, deriv_mem_adjoin_of_isAlgebraic ha⟩
  exact (hle hx).2

/-- **An algebraic element has no new jets.**  The differential field it generates is the ordinary
field it generates. -/
theorem differentialAdjoin_singleton_eq_adjoin [CharZero F] {a : K} (ha : IsAlgebraic F a) :
    differentialAdjoin F ({a} : Set K) = IntermediateField.adjoin F ({a} : Set K) := by
  refine le_antisymm (differentialAdjoin_le F ?_ (derivationClosed_adjoin_of_isAlgebraic ha)) ?_
  · exact Set.singleton_subset_iff.2 (IntermediateField.subset_adjoin F _ rfl)
  · rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl : y = a)
    exact subset_differentialAdjoin F _ rfl

/-- The differential field generated by an algebraic element has degree the degree of its minimal
polynomial. -/
theorem finrank_differentialAdjoin_singleton [CharZero F] {a : K} (ha : IsAlgebraic F a) :
    Module.finrank F (differentialAdjoin F ({a} : Set K)) = (minpoly F a).natDegree := by
  rw [differentialAdjoin_singleton_eq_adjoin ha]
  exact IntermediateField.adjoin.finrank ha.isIntegral

/-- **A differential field differentially generated by one algebraic element is a finite extension
of degree the degree of that element.** -/
theorem finrank_eq_of_differentialAdjoin_singleton_eq_top [CharZero F] {a : K}
    (ha : IsAlgebraic F a) (htop : differentialAdjoin F ({a} : Set K) = ⊤) :
    Module.finrank F K = (minpoly F a).natDegree := by
  have h1 := finrank_differentialAdjoin_singleton ha
  rw [htop, IntermediateField.finrank_top'] at h1
  exact h1

theorem finiteDimensional_of_differentialAdjoin_singleton_eq_top [CharZero F] {a : K}
    (ha : IsAlgebraic F a) (htop : differentialAdjoin F ({a} : Set K) = ⊤) :
    FiniteDimensional F K := by
  have h1 : FiniteDimensional F (differentialAdjoin F ({a} : Set K)) := by
    rw [differentialAdjoin_singleton_eq_adjoin ha]
    exact IntermediateField.adjoin.finiteDimensional ha.isIntegral
  rw [htop] at h1
  exact (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional

/-! ### The restricted derivation on a derivation-closed subfield -/

/-- Restrict the ambient derivation to a derivation-closed subfield. -/
@[reducible]
noncomputable def subfieldDifferential {K : Type*} [Field K] [Differential K]
    (L : Subfield K) (hL : ∀ x ∈ L, x′ ∈ L) : Differential L where
  deriv :=
    { toLinearMap :=
        { toFun := fun x => ⟨x.1′, hL x.1 x.2⟩
          map_add' := fun x y => Subtype.ext (Differential.deriv.map_add x.1 y.1)
          map_smul' := fun n x => Subtype.ext (Differential.deriv.map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext Differential.deriv.map_one_eq_zero
      leibniz' := fun x y => Subtype.ext (Differential.deriv.leibniz x.1 y.1) }

/-- A derivation-closed subfield is a differential subalgebra. -/
theorem subfield_differentialAlgebra {K : Type*} [Field K] [Differential K]
    (L : Subfield K) (hL : ∀ x ∈ L, x′ ∈ L) :
    letI := subfieldDifferential L hL
    DifferentialAlgebra L K :=
  letI := subfieldDifferential L hL
  ⟨fun _ => rfl⟩

/-- A derivation-closed intermediate field is a differential subalgebra of the ambient field. -/
theorem derivationClosed_differentialAlgebra {C K : Type*} [Field C] [Field K] [Algebra C K]
    [Differential K] (L : IntermediateField C K) (hL : DerivationClosed L) :
    letI := derivationClosedDifferential L hL
    DifferentialAlgebra L K :=
  letI := derivationClosedDifferential L hL
  ⟨fun _ => rfl⟩

end GaloisForLFunctions.HTGeometry
