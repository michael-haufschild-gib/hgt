import GaloisForLFunctions.HTGeometry.ChristoffelKernel
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface

/-!
# The Christoffel function bounds the atoms of every representing measure

The Christoffel data of a moment sequence is built entirely from the moments — finite linear
algebra, with no measure in sight.  This module shows it nevertheless controls every measure that
represents the sequence: for each real `x`,

`μ {x} ≤ λ(x)`

where `λ = christoffelLimit` is the limit of the Christoffel function.  The mechanism is that a
polynomial normalised at `x` dominates the point mass after integration, so the variational
characterisation of `λ` transfers directly to an upper bound on the atom.

This is the first statement joining the two halves of the moment development: the finite-level
kernel side, and the measure side carried by `HasHamburgerMoments` and the classical Nevanlinna
extremal family.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ} {μ : Measure ℝ}

/-- **A normalised polynomial dominates the atom.**  If `p (x) = 1` then the mass `μ` gives to `{x}`
is at most the moment norm of `p`, because the integral of `p²` over the single point `{x}` is
exactly that mass and the integrand is nonnegative everywhere else. -/
theorem measureReal_singleton_le_momentInner
    (hs : ∀ k, s k = ∫ y, (y : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun y : ℝ => (y : ℝ) ^ k) μ)
    (x : ℝ) (p : Polynomial ℝ) (hval : p.eval x = 1) :
    μ.real {x} ≤ momentInner s p p := by
  have hmi : momentInner s p p = ∫ y, (Polynomial.eval y p) ^ (2 : ℕ) ∂μ := by
    rw [momentInner_def, momentFunctional_mul_eq_integral s hs hint p p]
    refine integral_congr_ae (ae_of_all μ fun y => ?_)
    ring
  have hIntegrable : Integrable (fun y : ℝ => (Polynomial.eval y p) ^ (2 : ℕ)) μ := by
    refine (integrable_eval hint (p ^ (2 : ℕ))).congr (Filter.Eventually.of_forall fun y => ?_)
    simp [eval_pow]
  have hsing : ∫ y in ({x} : Set ℝ), (Polynomial.eval y p) ^ (2 : ℕ) ∂μ = μ.real {x} := by
    rw [integral_singleton, hval, one_pow, smul_eq_mul, mul_one]
  calc μ.real {x}
      = ∫ y in ({x} : Set ℝ), (Polynomial.eval y p) ^ (2 : ℕ) ∂μ := hsing.symm
    _ ≤ ∫ y, (Polynomial.eval y p) ^ (2 : ℕ) ∂μ :=
        setIntegral_le_integral hIntegrable
          (Filter.Eventually.of_forall fun y => sq_nonneg _)
    _ = momentInner s p p := hmi.symm

/-- Every finite level of the Christoffel function already bounds the atom: the normalised kernel is
an admissible competitor with value `1` at `x`, and it attains the Christoffel value. -/
theorem measureReal_singleton_le_christoffel (h : PositiveMomentForm s)
    (hs : ∀ k, s k = ∫ y, (y : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun y : ℝ => (y : ℝ) ^ k) μ)
    (n : ℕ) (x : ℝ) :
    μ.real {x} ≤ christoffel s n x := by
  have hcomp := measureReal_singleton_le_momentInner hs hint x
    (christoffel s n x • cdKernel s n x) (normalisedKernel_eval_self h n x)
  rwa [christoffel_eq_momentInner_normalisedKernel h n x] at hcomp

/-- **The limit Christoffel function bounds the atom.**  Taking the infimum over all levels, the
mass that any representing measure places at a point is at most `λ (x)`. -/
theorem measureReal_singleton_le_christoffelLimit (h : PositiveMomentForm s)
    (hs : ∀ k, s k = ∫ y, (y : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun y : ℝ => (y : ℝ) ^ k) μ)
    (x : ℝ) :
    μ.real {x} ≤ christoffelLimit s x :=
  le_ciInf fun n => measureReal_singleton_le_christoffel h hs hint n x

/-- The same bound stated against the project's representing-measure predicate. -/
theorem measureReal_singleton_le_christoffelLimit_of_hasMoments (h : PositiveMomentForm s)
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ) (x : ℝ) :
    μ.real {x} ≤ christoffelLimit s x :=
  measureReal_singleton_le_christoffelLimit h (fun k => (hmu k).2.symm) (fun k => (hmu k).1) x

/-- **Vanishing Christoffel limit forces an atomless point.**  If `λ (x) = 0` then no representing
measure charges `x`. -/
theorem measureReal_singleton_eq_zero_of_christoffelLimit_eq_zero (h : PositiveMomentForm s)
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ) {x : ℝ}
    (hx : christoffelLimit s x = 0) :
    μ.real {x} = 0 := by
  refine le_antisymm ?_ measureReal_nonneg
  rw [← hx]
  exact measureReal_singleton_le_christoffelLimit_of_hasMoments h hmu x

/-- **Uniform atom bound for the classical N-extremal family.**  Every leaf of the family gives each
point at most the Christoffel limit — a bound depending only on the moment sequence, uniformly in
the boundary parameter. -/
theorem leaf_measureReal_singleton_le_christoffelLimit (h : PositiveMomentForm s)
    (F : GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s)
    (t : OnePoint ℝ) (x : ℝ) :
    (F.leaf t : Measure ℝ).real {x} ≤ christoffelLimit s x :=
  measureReal_singleton_le_christoffelLimit_of_hasMoments h (F.leaf_moments t) x

end HTGeometry
