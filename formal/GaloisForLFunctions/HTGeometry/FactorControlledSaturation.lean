import GaloisForLFunctions.HTGeometry.ComponentFactorExclusion

/-!
# Replacing an uncontrolled saturation multiplier by the factor's own initial and separant

A saturation certificate produced over a fraction field carries a multiplier of unknown shape: the
powers of the initial and the separant belong to the polynomial before it was cleared, and clearing
denominators multiplies in an unknown coefficient.  For the divisibility bridge what matters is not
the existence of a multiplier but its variables, so such a certificate is unusable.

The exchange proved here removes that defect.  Given a certificate saturating a polynomial into the
differential ideal of an irreducible factor by powers of the initial and separant of the whole
polynomial, the factor's *own* initial and separant already suffice, and they do so over the
coefficient ring: no denominators, and every variable of the new multiplier already occurs in the
factor.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {K L : Type*} [CommRing K] [IsDomain K] [CharZero K] [Differential K]
variable [Field L] [Differential L] [CharZero L]

/-- **The controlled saturation certificate.**

Hypotheses: `φ` is an injective derivation-compatible coefficient map, the image of `A` is an
irreducible factor of a squarefree `C = φ(A) · B` with the same order, and a certificate saturates
`φ(W)` into the differential ideal of `φ(A)` by powers of the initial and separant of `C`.

Conclusion: powers of the initial and separant of `A` itself absorb `W` into the differential ideal
of `A`, over the coefficient ring.  The exceptional polynomials of `C` are cancelled against the
general component of `φ(A)`, where neither of them lies, and the reduction over the ring then
produces the new multiplier out of `A`. -/
theorem exists_factor_initial_separant_powers_mem_diffPolyIterateIdeal
    (φ : K →+* L) (hinj : Function.Injective φ) (hcomm : ∀ c : K, φ c′ = (φ c)′)
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty)
    {B : DifferentialPolynomial Unit L}
    (hAirr : Irreducible (MvPolynomial.map φ A))
    (hsquarefree : Squarefree (MvPolynomial.map φ A * B))
    (horder : scalarDifferentialPolynomialOrder (MvPolynomial.map φ A) =
      scalarDifferentialPolynomialOrder (MvPolynomial.map φ A * B))
    {W : DifferentialPolynomial Unit K} {a b : ℕ}
    (hsat : scalarDifferentialPolynomialInitial (MvPolynomial.map φ A * B) ^ a *
        (scalarDifferentialPolynomialSeparant (MvPolynomial.map φ A * B) ^ b *
          MvPolynomial.map φ W) ∈
      differentialPolynomialIterateIdeal (MvPolynomial.map φ A)) :
    ∃ a' b' : ℕ,
      scalarDifferentialPolynomialInitial A ^ a' *
          (scalarDifferentialPolynomialSeparant A ^ b' * W) ∈ diffPolyIterateIdeal A := by
  classical
  have hA'vars : (MvPolynomial.map φ A).vars.Nonempty := by
    obtain ⟨j, hj⟩ := hAvars
    exact ⟨j, by rw [MvPolynomial.vars_map_of_injective _ hinj]; exact hj⟩
  obtain ⟨P, hPprime, hPle, hPdvd, _hinit, _hsep, _hirr⟩ :=
    exists_component_prime_of_irreducible hA'vars hAirr
  have hWmem : MvPolynomial.map φ W ∈ P :=
    mem_of_initial_separant_powers_mem hAirr hA'vars hsquarefree horder hPprime hPdvd
      (hPle hsat)
  exact exists_oracle_initial_separant_powers_mem_diffPolyIterateIdeal φ hinj hcomm hAvars
    hPle hPdvd hWmem

end

end GaloisForLFunctions
