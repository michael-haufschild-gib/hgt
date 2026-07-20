import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The top homogeneous component of a multivariate polynomial

The top total-degree sector of a nonzero multivariate polynomial is nonzero.
This coefficient-ring- and index-independent form is shared by the simple-zero
Bell and simple-pole jet horizons, so those two boundary theories can be
imported and composed without competing local declarations.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The homogeneous component at total degree detects every nonzero
multivariate polynomial, over an arbitrary commutative semiring. -/
theorem homogeneousComponent_totalDegree_ne_zero
    {R σ : Type*} [CommSemiring R] {P : MvPolynomial σ R} (hP0 : P ≠ 0) :
    MvPolynomial.homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨m, hm, hmax⟩ := P.support.exists_mem_eq_sup
    (Finsupp.support_nonempty_iff.mpr hP0)
    (fun e : σ →₀ ℕ => e.sum fun _ k => k)
  have hdeg : m.degree = P.totalDegree := by
    rw [MvPolynomial.totalDegree]
    simpa [Finsupp.degree] using hmax.symm
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff m) hzero
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg,
    MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

end GaloisForLFunctions.HTGeometry
