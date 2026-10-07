import GaloisForLFunctions.HTGeometry.AlgebraicFiniteJetBranch
import GaloisForLFunctions.HTGeometry.NewtonPuiseuxRoot
import GaloisForLFunctions.HTGeometry.PolynomialBezoutDenominator
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Convergent ramified branches of monic algebraic equations

For a monic irreducible bivariate complex polynomial, some substitution `t = s ^ N`
admits an actual local analytic root. Formal Newton–Puiseux produces the formal
root; a denominator-cleared Bezout identity proves its formal derivative is
nonzero; exact finite-jet division then gives the analytic branch.

The separable version is also retained. No convergence of a formal series is
assumed, and no analytic growth estimate is used. This is classical machinery
for the algebraic-curve normalization dependency, not a new scientific claim.
-/

namespace GaloisForLFunctions.HTGeometry.AlgebraicRamifiedBranch

open Polynomial
open AlgebraicFiniteJetBranch
open scoped Topology

noncomputable section


/-- Substitute `s ^ N` for the coefficient parameter. -/
def ramify (P : BiPoly) (N : ℕ) : BiPoly :=
  P.map (Polynomial.expand ℂ N).toRingHom

theorem coe_expand (p : Polynomial ℂ) (N : ℕ) (hN : N ≠ 0) :
    ((Polynomial.expand ℂ N p : Polynomial ℂ) : Series) =
      PowerSeries.expand N hN (p : Series) := by
  ext i
  simp only [Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.pos_of_ne_zero hN),
    PowerSeries.coeff_expand]

theorem formalize_ramify (P : BiPoly) (N : ℕ) (hN : N ≠ 0) :
    formalize (ramify P N) =
      (formalize P).map (PowerSeries.expand N hN).toRingHom := by
  apply Polynomial.ext
  intro i
  simp only [formalize, ramify, Polynomial.coeff_map]
  exact coe_expand _ N hN

theorem evalAt_ramify (P : BiPoly) (N : ℕ) (s w : ℂ) :
    evalAt (ramify P N) s w = evalAt P (s ^ N) w := by
  apply congrArg (Polynomial.eval w)
  ext i
  simp [specialize, ramify, Polynomial.expand_eq_comp_X_pow, Polynomial.eval_comp]

/-- Generic separability keeps the derivative nonzero at every ramified formal root. -/
theorem formal_derivative_ne_zero (P : BiPoly)
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable)
    (N : ℕ) (hN : N ≠ 0) (y : Series)
    (hy : (formalize (ramify P N)).eval y = 0) :
    (formalize (ramify P N)).derivative.eval y ≠ 0 := by
  obtain ⟨U, V, r, hr, hbez⟩ := exists_bezout_of_isCoprime_map
    (K := FractionRing (Polynomial ℂ))
    (P := P) (Q := P.derivative)
    (by simpa only [Polynomial.separable_def, Polynomial.derivative_map] using hsep)
  have hr' : PowerSeries.expand N hN (r : Series) ≠ 0 := by
    intro heq
    apply hr
    ext i
    have hi := congrArg (PowerSeries.coeff (N * i)) heq
    simpa only [PowerSeries.coeff_expand_mul, Polynomial.coeff_coe,
      map_zero, Polynomial.coeff_zero] using hi
  intro hd
  have hh := congrArg (fun Q : BiPoly => (formalize (ramify Q N)).eval y) hbez
  have hderiv : formalize (ramify P.derivative N) =
      (formalize (ramify P N)).derivative := by simp [formalize, ramify]
  have hh' : (formalize (ramify U N)).eval y * (formalize (ramify P N)).eval y +
      (formalize (ramify V N)).eval y * (formalize (ramify P.derivative N)).eval y =
      PowerSeries.expand N hN (r : Series) := by
    rw [← coe_expand r N hN]
    simpa [formalize, ramify] using hh
  rw [hderiv, hy, hd, mul_zero, mul_zero, add_zero] at hh'
  exact hr' hh'.symm

/-- A generically separable monic polynomial acquires an analytic root after ramification. -/
theorem exists_ramified_analytic_root (P : BiPoly) (hP : P.Monic)
    (hdegree : 0 < P.natDegree)
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ AnalyticAt ℂ f 0 ∧
      ∀ᶠ s in 𝓝 0, evalAt P (s ^ N) (f s) = 0 := by
  have hmono : (formalize P).Monic := hP.map _
  have hdeg : (formalize P).natDegree = P.natDegree := hP.natDegree_map _
  obtain ⟨N, hN, y, hy⟩ := exists_isRoot_map_expand P.natDegree (formalize P)
    hmono hdeg hdegree
  have hy' : (formalize (ramify P N)).eval y = 0 := by
    rwa [formalize_ramify P N hN]
  obtain ⟨f, hf, _, hroot⟩ := exists_analytic_root (ramify P N) y hy'
    (formal_derivative_ne_zero P hsep N hN y hy')
  exact ⟨N, f, Nat.pos_of_ne_zero hN, hf, by simpa only [evalAt_ramify] using hroot⟩

/-- Irreducibility in characteristic zero discharges the separability requirement. -/
theorem exists_ramified_analytic_root_of_irreducible (P : BiPoly)
    (hP : P.Monic) (hirr : Irreducible P) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ AnalyticAt ℂ f 0 ∧
      ∀ᶠ s in 𝓝 0, evalAt P (s ^ N) (f s) = 0 := by
  have hdegree : 0 < P.natDegree := by
    by_contra h
    have heq : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP (by omega)
    exact hirr.not_isUnit (heq.symm ▸ isUnit_one)
  have hi : Irreducible (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) :=
    (hP.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hirr
  exact exists_ramified_analytic_root P hP hdegree hi.separable

end

end GaloisForLFunctions.HTGeometry.AlgebraicRamifiedBranch
