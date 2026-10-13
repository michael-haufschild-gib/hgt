import GaloisForLFunctions.RHTower.WeilLogShiftFinitePolynomialInterpolation
import Mathlib.Topology.Algebra.Polynomial

/-! A continuous polynomial graph recovers every finite joint support point at every real tilt. -/

open MeasureTheory
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

noncomputable def finiteWeilCanonicalGraphPolynomial (r k : ℕ) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 1)

theorem finiteWeilCanonicalGraphPolynomial_degree_lt (r k : ℕ) :
    (finiteWeilCanonicalGraphPolynomial r k).degree < (r + 1 : ℕ) := by
  simpa only [finiteWeilCanonicalGraphPolynomial, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (fun i => finiteWeilCanonicalFluctuationPoint r k i 1)
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn

theorem finiteWeilCanonicalGraphPolynomial_eval_at_atom (r k : ℕ) (i : Fin (r + 1)) :
    (finiteWeilCanonicalGraphPolynomial r k).eval (finiteWeilCanonicalFluctuationPoint r k i 0) =
      finiteWeilCanonicalFluctuationPoint r k i 1 :=
  Lagrange.eval_interpolate_at_node (fun j => finiteWeilCanonicalFluctuationPoint r k j 1)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k).injOn (Finset.mem_univ i)

noncomputable def finiteWeilCanonicalPolynomialGraph (r k : ℕ) (x : ℝ) : E :=
  WithLp.toLp 2 ![x, (finiteWeilCanonicalGraphPolynomial r k).eval x]

theorem finiteWeilCanonicalPolynomialGraph_fst (r k : ℕ) (x : ℝ) :
    finiteWeilCanonicalPolynomialGraph r k x 0 = x := rfl

theorem continuous_finiteWeilCanonicalPolynomialGraph (r k : ℕ) :
    Continuous (finiteWeilCanonicalPolynomialGraph r k) := by
  unfold finiteWeilCanonicalPolynomialGraph
  fun_prop

theorem finiteWeilCanonicalPolynomialGraph_injective (r k : ℕ) :
    Function.Injective (finiteWeilCanonicalPolynomialGraph r k) := by
  intro x y h
  exact congrArg (fun z : E => z 0) h

theorem finiteWeilCanonicalPolynomialGraph_at_atom (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilCanonicalPolynomialGraph r k (finiteWeilCanonicalFluctuationPoint r k i 0) =
      finiteWeilCanonicalFluctuationPoint r k i := by
  ext j
  fin_cases j
  · rfl
  · exact finiteWeilCanonicalGraphPolynomial_eval_at_atom r k i

theorem finiteWeilCanonicalPolynomialGraph_base_ae (r k : ℕ) :
    ∀ᵐ z ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E),
      finiteWeilCanonicalPolynomialGraph r k (z 0) = z := by
  exact (finiteWeilCanonicalObservableLaw_ae_iff r k (finiteWeilCanonicalFluctuationPoint r k)
    (fun z => finiteWeilCanonicalPolynomialGraph r k (z 0) = z)).mpr
      (finiteWeilCanonicalPolynomialGraph_at_atom r k)

theorem finiteWeilCanonicalPolynomialGraph_tilted_ae (r k : ℕ) (a b d : ℝ) :
    ∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E),
      finiteWeilCanonicalPolynomialGraph r k (z 0) = z := by
  exact (finiteWeilCanonicalJointQuadraticTilt_ae_iff r k a b d _).mpr
    (finiteWeilCanonicalPolynomialGraph_at_atom r k)

end RHTower
