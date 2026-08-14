import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# No rational exponential eigenfunctions of a free coordinate derivative

A nonzero rational function in free coordinates cannot be an eigenvector of a coordinate
derivation with nonzero scalar eigenvalue.  The proof uses a reduced numerator and denominator:
relative primality forces each to divide its own partial derivative, while strict total-degree
drop forces both derivatives to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A free-coordinate derivation has no nonzero rational eigenfunction with nonzero scalar
eigenvalue. -/
theorem freeCoordinateDerivation_eq_const_mul_self_forces_zero
    {C σ : Type*} [Field C] [CharZero C] (i : σ)
    {c : C} (hc : c ≠ 0) {f : FreeCoordinateRationalField C σ}
    (hf : freeCoordinateDerivation C σ i f =
      algebraMap C (FreeCoordinateRationalField C σ) c * f) :
    f = 0 := by
  by_contra hf0
  let P := MvPolynomial σ C
  let F := FreeCoordinateRationalField C σ
  let p : P := IsFractionRing.num P f
  let q : P := IsFractionRing.den P f
  have hq : q ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den P f).property
  have hqF : algebraMap P F q ≠ 0 := by
    simpa using (IsFractionRing.injective P F).ne hq
  have hrel : algebraMap P F p = f * algebraMap P F q := by
    exact (div_eq_iff hqF).mp (IsFractionRing.mk'_num_den' P f)
  have hp : p ≠ 0 := by
    intro hp0
    rw [hp0, map_zero] at hrel
    exact hf0 ((mul_eq_zero.mp hrel.symm).resolve_right hqF)
  have hcoprime : IsRelPrime p q := by
    simpa only [p, q] using IsFractionRing.num_den_reduced P f
  have hderiv := congrArg (freeCoordinateDerivation C σ i) hrel
  rw [freeCoordinateDerivation_algebraMap, Derivation.leibniz,
    freeCoordinateDerivation_algebraMap, hf] at hderiv
  simp only [smul_eq_mul] at hderiv
  have hcrossF :
      algebraMap P F (MvPolynomial.pderiv i p * q) =
        algebraMap P F
          (p * (MvPolynomial.C c * q + MvPolynomial.pderiv i q)) := by
    simp only [map_mul, map_add]
    rw [show algebraMap P F (MvPolynomial.C c) = algebraMap C F c by
      exact IsScalarTower.algebraMap_apply C P F c]
    calc
      algebraMap P F (MvPolynomial.pderiv i p) * algebraMap P F q =
          (f * algebraMap P F (MvPolynomial.pderiv i q) +
            algebraMap P F q * (algebraMap C F c * f)) *
              algebraMap P F q := by rw [hderiv]
      _ = (f * algebraMap P F q) *
          (algebraMap C F c * algebraMap P F q +
            algebraMap P F (MvPolynomial.pderiv i q)) := by ring
      _ = algebraMap P F p *
          (algebraMap C F c * algebraMap P F q +
            algebraMap P F (MvPolynomial.pderiv i q)) := by
            rw [hrel]
  have hcross :
      MvPolynomial.pderiv i p * q =
        p * (MvPolynomial.C c * q + MvPolynomial.pderiv i q) :=
    (IsFractionRing.injective P F) hcrossF
  have hpdiv : p ∣ MvPolynomial.pderiv i p := by
    apply hcoprime.dvd_of_dvd_mul_right
    exact ⟨MvPolynomial.C c * q + MvPolynomial.pderiv i q, hcross⟩
  have hpderiv : MvPolynomial.pderiv i p = 0 :=
    mvPolynomial_pderiv_eq_zero_of_self_dvd p i hpdiv
  have hqrelation : MvPolynomial.pderiv i q = -(MvPolynomial.C c * q) := by
    rw [hpderiv, zero_mul] at hcross
    have hsum : MvPolynomial.C c * q + MvPolynomial.pderiv i q = 0 := by
      exact (mul_eq_zero.mp hcross.symm).resolve_left hp
    linear_combination hsum
  have hqdiv : q ∣ MvPolynomial.pderiv i q := by
    exact ⟨-MvPolynomial.C c, by rw [hqrelation]; ring⟩
  have hqderiv : MvPolynomial.pderiv i q = 0 :=
    mvPolynomial_pderiv_eq_zero_of_self_dvd q i hqdiv
  rw [hqderiv] at hqrelation
  have hcC : MvPolynomial.C c ≠ (0 : P) := MvPolynomial.C_ne_zero.mpr hc
  exact (mul_ne_zero hcC hq) (neg_eq_zero.mp hqrelation.symm)

end

end GaloisForLFunctions.HTGeometry
