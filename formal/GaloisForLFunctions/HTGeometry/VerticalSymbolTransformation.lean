import GaloisForLFunctions.HTGeometry.ScalingInvariantRationalFunction

/-!
# The vertical symbol under a fibrewise scaling

A first-order tail datum is a rational function of the fibre coordinate `v`, and the protocol acts
on it by `v ↦ R'(z)·v` together with the pullback of the base coordinate.  Only the leading
behaviour at vertical infinity survives the comparison, and that behaviour is a pair: an integer
degree and a leading coefficient.

Under `v ↦ a v` with `a ≠ 0` the degree is unchanged and the leading coefficient is multiplied by
`a` to the power of that degree.  Comparing the two sides of the tail functional equation therefore
gives, at once, that the degree `k` is phase-independent and that the leading coefficients transform
as a `k`-differential — which is exactly the tensor chain law of the classification.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {L : Type*} [Field L]

/-- The leading coefficient after a fibrewise scaling. -/
theorem leadingCoeff_comp_scaling {a : L} (ha : a ≠ 0) (P : Polynomial L) :
    (P.comp (Polynomial.C a * Polynomial.X)).leadingCoeff = a ^ P.natDegree * P.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, natDegree_comp_scaling ha P,
    Polynomial.comp_C_mul_X_coeff]
  ring

/-- The degree of the vertical symbol of a coprime pair. -/
def symbolDegree (P Q : Polynomial L) : ℤ := (P.natDegree : ℤ) - (Q.natDegree : ℤ)

/-- The leading coefficient of the vertical symbol of a coprime pair. -/
noncomputable def symbolCoeff (P Q : Polynomial L) : L := P.leadingCoeff / Q.leadingCoeff

@[simp]
theorem symbolDegree_comp_scaling {a : L} (ha : a ≠ 0) (P Q : Polynomial L) :
    symbolDegree (P.comp (Polynomial.C a * Polynomial.X))
        (Q.comp (Polynomial.C a * Polynomial.X)) = symbolDegree P Q := by
  rw [symbolDegree, symbolDegree, natDegree_comp_scaling ha, natDegree_comp_scaling ha]

/-- **The vertical symbol transforms as a `k`-differential**, with `k` its own degree. -/
theorem symbolCoeff_comp_scaling {a : L} (ha : a ≠ 0) {P Q : Polynomial L}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    symbolCoeff (P.comp (Polynomial.C a * Polynomial.X))
        (Q.comp (Polynomial.C a * Polynomial.X))
      = a ^ (symbolDegree P Q) * symbolCoeff P Q := by
  have hlP : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hlQ : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  rw [symbolCoeff, symbolCoeff, leadingCoeff_comp_scaling ha, leadingCoeff_comp_scaling ha,
    symbolDegree, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp

/-- **Symbol comparison.**  If two symbol data are related by a fibrewise scaling, their degrees
agree and their leading coefficients obey the `k`-differential pullback law. -/
theorem symbol_comparison {a : L} (ha : a ≠ 0) {P Q P' Q' : Polynomial L}
    (hP' : P' ≠ 0) (hQ' : Q' ≠ 0)
    (hnum : P = P'.comp (Polynomial.C a * Polynomial.X))
    (hden : Q = Q'.comp (Polynomial.C a * Polynomial.X)) :
    symbolDegree P Q = symbolDegree P' Q' ∧
      symbolCoeff P Q = a ^ (symbolDegree P' Q') * symbolCoeff P' Q' := by
  subst hnum
  subst hden
  exact ⟨symbolDegree_comp_scaling ha P' Q', symbolCoeff_comp_scaling ha hP' hQ'⟩

/-- **The degree is phase-independent along a protocol.**  If every phase datum is the scaling of
the next, all symbol degrees are equal. -/
theorem symbolDegree_const_of_protocol {A : ℕ → L} (hA : ∀ i, A i ≠ 0)
    {P Q : ℕ → Polynomial L}
    (hnum : ∀ i, P i = (P (i + 1)).comp (Polynomial.C (A i) * Polynomial.X))
    (hden : ∀ i, Q i = (Q (i + 1)).comp (Polynomial.C (A i) * Polynomial.X)) (i : ℕ) :
    symbolDegree (P i) (Q i) = symbolDegree (P 0) (Q 0) := by
  induction i with
  | zero => rfl
  | succ i IH =>
      rw [← IH, hnum i, hden i, symbolDegree_comp_scaling (hA i)]

end GaloisForLFunctions.HTGeometry
