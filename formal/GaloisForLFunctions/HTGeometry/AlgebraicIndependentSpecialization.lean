import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient

/-!
# Specialization criterion for algebraic independence over a fraction field

Independence over a large coefficient field is usually harder to certify than independence over the
constants.  When the coefficients are *functions* there is a standard reduction: clear denominators,
so that a relation has coefficients in the coefficient ring, then specialize at a point.  At a point
the coefficients become constants, so the specialized relation is a relation over the constants; if
enough points are available to detect a nonzero coefficient, the original relation was trivial.

This file states that reduction abstractly.  The data is a coefficient ring `R` with fraction field
`K`, a ring `RP` with fraction field `KP` receiving `R`, a family of specializations `σ p` of `RP`
which carry the image of `R` into the constants `T`, and the separation property that a nonzero
element of `R` is detected by some specialization.  The conclusion is independence over `K` of a
family which is independent over `T` after each specialization.

No analysis is involved: the only inputs are denominator clearing over a fraction field and the
naturality of polynomial evaluation under ring maps.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Specialization criterion for algebraic independence.**  A family whose specializations are
algebraically independent over the constants, at enough points to detect a nonzero coefficient, is
algebraically independent over the whole fraction field of the coefficient ring. -/
theorem algebraicIndependent_of_pointwise_specialization
    {ι Pt R K RP KP T : Type*}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing RP] [CommRing KP] [Algebra RP KP] [Algebra K KP]
    [CommRing T] {S : Pt → Type*} [∀ p, CommRing (S p)] [∀ p, Algebra T (S p)]
    (π : R →+* RP)
    (hπ : ∀ r : R, algebraMap K KP (algebraMap R K r) = algebraMap RP KP (π r))
    (hinj : Function.Injective (algebraMap RP KP))
    (x : ι → RP)
    (σ : ∀ p : Pt, RP →+* S p) (ev : Pt → (R →+* T))
    (hcomm : ∀ (p : Pt) (r : R), σ p (π r) = algebraMap T (S p) (ev p r))
    (hind : ∀ p : Pt, AlgebraicIndependent T fun i => σ p (x i))
    (hsep : ∀ r : R, (∀ p : Pt, ev p r = 0) → r = 0) :
    AlgebraicIndependent K fun i => algebraMap RP KP (x i) := by
  classical
  rw [algebraicIndependent_iff]
  intro Pol hPol
  by_contra hne
  obtain ⟨d, Q, hQne, hQ⟩ :=
    exists_mvPolynomial_fraction_clear_ne_zero (R := R) (K := K) (σ := ι) hne
  -- the cleared relation still evaluates to zero
  have hzero : (MvPolynomial.aeval fun i => algebraMap RP KP (x i))
      (MvPolynomial.map (algebraMap R K) Q) = 0 := by
    rw [hQ, map_mul, hPol, mul_zero]
  -- rewrite the evaluation as one over the coefficient ring
  have hcomp : (algebraMap K KP).comp (algebraMap R K) = (algebraMap RP KP).comp π :=
    RingHom.ext hπ
  have hRP : algebraMap RP KP (MvPolynomial.eval₂ π x Q) = 0 := by
    rw [MvPolynomial.eval₂_comp_left (algebraMap RP KP) π x Q]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hcomp] at hzero
    exact hzero
  have hRP0 : MvPolynomial.eval₂ π x Q = 0 := hinj (by simpa using hRP)
  -- specialize at every point
  have hmapzero : ∀ p : Pt, MvPolynomial.map (ev p) Q = 0 := by
    intro p
    have hσ : MvPolynomial.eval₂ ((σ p).comp π) (fun i => σ p (x i)) Q = 0 := by
      have h := MvPolynomial.eval₂_comp_left (σ p) π x Q
      rw [hRP0, map_zero] at h
      exact h.symm
    have hcomm' : (σ p).comp π = (algebraMap T (S p)).comp (ev p) := RingHom.ext (hcomm p)
    rw [hcomm'] at hσ
    have haeval : (MvPolynomial.aeval fun i => σ p (x i)) (MvPolynomial.map (ev p) Q) = 0 := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      exact hσ
    exact (algebraicIndependent_iff.mp (hind p)) _ haeval
  -- hence every coefficient of the cleared relation vanishes
  refine hQne (MvPolynomial.ext _ _ fun m => ?_)
  refine (hsep (Q.coeff m) fun p => ?_).trans (MvPolynomial.coeff_zero m).symm
  have := congrArg (MvPolynomial.coeff m) (hmapzero p)
  rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this

end

end GaloisForLFunctions.HTGeometry
