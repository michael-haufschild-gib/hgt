import GaloisForLFunctions.RHTower.FieldOnePadicValuationUnitDecomposition
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientNonSquare
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Locally constant p-adic polynomial and discriminant valuations

On the nonvanishing locus of a coefficient polynomial, its p-adic valuation
is locally constant. The generic discriminant therefore has clopen valuation
strata away from its zero locus, and its valuation together with the fixed
degree is locally constant. This is the discriminant-continuity lemma used by
Knospe--Shen--Van Peski in *Refined random matrix conjectures for zeros of
p-adic L-functions*, specialized to the corpus's symmetric coefficient ring.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime] {σ : Type*}

/-- Coefficient points at which a polynomial is nonzero. -/
abbrev PadicPolynomialNonvanishing (P : MvPolynomial σ ℚ_[p]) :=
  {x : σ → ℚ_[p] // MvPolynomial.eval x P ≠ 0}

/-- Evaluation as a unit on the nonvanishing coefficient locus. -/
def padicPolynomialUnitValue (P : MvPolynomial σ ℚ_[p])
    (x : PadicPolynomialNonvanishing p P) : ℚ_[p]ˣ :=
  Units.mk0 (MvPolynomial.eval x.val P) x.property

/-- Polynomial unit evaluation is continuous, including its inverse coordinate. -/
theorem continuous_padicPolynomialUnitValue (P : MvPolynomial σ ℚ_[p]) :
    Continuous (padicPolynomialUnitValue p P) := by
  have he : Continuous (fun x : PadicPolynomialNonvanishing p P =>
      MvPolynomial.eval x.val P) := P.continuous_eval.comp continuous_subtype_val
  apply Units.continuous_iff.mpr
  exact ⟨he, he.inv₀ (fun x => x.property)⟩

/-- Every nonzero polynomial value has a neighborhood of constant p-adic valuation. -/
theorem padicPolynomialValuation_isLocallyConstant (P : MvPolynomial σ ℚ_[p]) :
    IsLocallyConstant (fun x : PadicPolynomialNonvanishing p P =>
      Padic.valuation (MvPolynomial.eval x.val P)) := by
  have h := (fieldOnePadic_valuation_isLocallyConstant p).comp_continuous
    (continuous_padicPolynomialUnitValue p P)
  exact h.comp Multiplicative.toAdd

/-- Fixed valuations give clopen strata inside the polynomial's nonvanishing locus. -/
theorem padicPolynomialValuation_stratum_isClopen (P : MvPolynomial σ ℚ_[p]) (k : ℤ) :
    IsClopen {x : PadicPolynomialNonvanishing p P |
      Padic.valuation (MvPolynomial.eval x.val P) = k} :=
  (padicPolynomialValuation_isLocallyConstant p P).isClopen_fiber k

/-- The actual generic discriminant has locally constant valuation off its zero locus. -/
theorem padicDiscriminantValuation_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (fun x : PadicPolynomialNonvanishing p (discCoeffPoly ℚ_[p] n) =>
      Padic.valuation (MvPolynomial.eval x.val (discCoeffPoly ℚ_[p] n))) :=
  padicPolynomialValuation_isLocallyConstant p _

/-- Discriminant valuation and degree are jointly locally constant on each coefficient component. -/
theorem padicDiscriminantDegree_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (fun x : PadicPolynomialNonvanishing p (discCoeffPoly ℚ_[p] n) =>
      (Padic.valuation (MvPolynomial.eval x.val (discCoeffPoly ℚ_[p] n)), n)) :=
  (padicDiscriminantValuation_isLocallyConstant p n).comp (fun k => (k, n))

/-- Discriminant valuation cuts the separable coefficient locus into clopen strata. -/
theorem padicDiscriminantValuation_stratum_isClopen (n : ℕ) (k : ℤ) :
    IsClopen {x : PadicPolynomialNonvanishing p (discCoeffPoly ℚ_[p] n) |
      Padic.valuation (MvPolynomial.eval x.val (discCoeffPoly ℚ_[p] n)) = k} :=
  padicPolynomialValuation_stratum_isClopen p _ k

#print axioms padicPolynomialValuation_isLocallyConstant
#print axioms padicDiscriminantDegree_isLocallyConstant
#print axioms padicDiscriminantValuation_stratum_isClopen

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
