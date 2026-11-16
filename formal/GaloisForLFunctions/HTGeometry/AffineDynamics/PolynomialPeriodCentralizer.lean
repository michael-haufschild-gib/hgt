import GaloisForLFunctions.HTGeometry.AffineConstraintCentralizer
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Nonlinear symmetries of the period shears

The period coordinates are invariant under every period shear. Translating
the distinguished coordinate by any function of those invariants therefore
commutes with every shear. Polynomial functions give polynomial maps with
polynomial inverses, and distinct polynomials give distinct symmetries over
an infinite field.

This applies the invariant-function mechanism of Proposition 3.1 in
*On ergodicity and symmetry for affine systems*,
https://arxiv.org/abs/2611.14187, to the period-shear system. It exhibits the
nonlinear symmetries beyond its finite-dimensional affine centralizer.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {k ι : Type*} [Field k]

/-- Translation along a fibre by a function of the invariant period coordinates. -/
def invariantPeriodTranslation (h : (ι → k) → k) : Equiv.Perm (PeriodCoordinates k ι) where
  toFun q := (q.1 + h q.2, q.2)
  invFun q := (q.1 - h q.2, q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

/-- Every invariant-dependent translation commutes with every period shear. -/
theorem invariantPeriodTranslation_commutes (h : (ι → k) → k) (i : ι)
    (q : PeriodCoordinates k ι) :
    invariantPeriodTranslation h (periodShear i q) =
      periodShear i (invariantPeriodTranslation h q) := by
  apply Prod.ext
  · dsimp [invariantPeriodTranslation, periodShear]
    ring
  · rfl

theorem invariantPeriodTranslation_add (h g : (ι → k) → k) :
    invariantPeriodTranslation (h + g) =
      invariantPeriodTranslation h * invariantPeriodTranslation g := by
  ext q
  · dsimp [invariantPeriodTranslation]
    ring
  · rfl

/-- The full function parameter is recovered by evaluating the translation at zero. -/
theorem invariantPeriodTranslation_injective :
    Function.Injective (invariantPeriodTranslation (k := k) (ι := ι)) := by
  intro h g heq
  funext w
  have := congrArg (fun e : Equiv.Perm (PeriodCoordinates k ι) => (e (0, w)).1) heq
  simpa only [invariantPeriodTranslation, Equiv.coe_fn_mk, zero_add] using this

/-- Polynomial invariant functions give an additive family of commuting symmetries. -/
def polynomialPeriodTranslation (P : MvPolynomial ι k) : Equiv.Perm (PeriodCoordinates k ι) :=
  invariantPeriodTranslation (fun w => MvPolynomial.eval w P)

theorem polynomialPeriodTranslation_commutes (P : MvPolynomial ι k) (i : ι)
    (q : PeriodCoordinates k ι) :
    polynomialPeriodTranslation P (periodShear i q) =
      periodShear i (polynomialPeriodTranslation P q) :=
  invariantPeriodTranslation_commutes _ i q

/-- Over an infinite field no polynomial parameter is lost in the centralizer. -/
theorem polynomialPeriodTranslation_injective [Infinite k] :
    Function.Injective (polynomialPeriodTranslation (k := k) (ι := ι)) := by
  intro P Q h
  apply MvPolynomial.funext
  have heq := invariantPeriodTranslation_injective h
  exact congrFun heq

/-- The polynomial family respects addition and composition exactly. -/
theorem polynomialPeriodTranslation_add (P Q : MvPolynomial ι k) :
    polynomialPeriodTranslation (P + Q) =
      polynomialPeriodTranslation P * polynomialPeriodTranslation Q := by
  unfold polynomialPeriodTranslation
  rw [← invariantPeriodTranslation_add]
  congr 1
  funext w
  exact MvPolynomial.eval_add

/-- The same invariant multiplier gives a compatible vertical vector field. -/
theorem invariantPeriodField_compatible (h : (ι → k) → k) (i : ι)
    (q : PeriodCoordinates k ι) :
    (h (periodShear i q).2, (0 : ι → k)) =
      periodShear i (h q.2, 0) := by
  simp only [periodShear, Pi.zero_apply, add_zero]

#print axioms invariantPeriodTranslation_commutes
#print axioms polynomialPeriodTranslation_injective
#print axioms polynomialPeriodTranslation_add
end GaloisForLFunctions.HTGeometry
