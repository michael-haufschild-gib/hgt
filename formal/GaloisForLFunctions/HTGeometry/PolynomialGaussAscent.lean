import GaloisForLFunctions.HTGeometry.MvPolynomialGaussAscent
import GaloisForLFunctions.HTGeometry.MarkedCoordinateLinearDivisor

/-!
# Gauss ascent for univariate polynomials

A primitive irreducible polynomial over a unique-factorization domain remains irreducible after
mapping its coefficients into the fraction field.  The multivariate analogue already exists in
the corpus; the derivative-component construction needs the literal univariate form.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A polynomial whose injective fraction-field image is constant was already constant. -/
theorem polynomial_eq_C_of_fraction_map_eq_C
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {T : Polynomial R} {c : K}
    (hT : Polynomial.map (algebraMap R K) T = Polynomial.C c) :
    T = Polynomial.C (T.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hcoeff := congrArg (fun p : Polynomial K => p.coeff n) hT
    rw [Polynomial.coeff_map, Polynomial.coeff_C, if_neg hn] at hcoeff
    rw [Polynomial.coeff_C, if_neg hn]
    exact IsFractionRing.injective R K (by simpa using hcoeff)

/-- **Univariate Gauss ascent.**  A primitive irreducible polynomial remains irreducible over the
fraction field of its coefficient ring. -/
theorem Polynomial.IsPrimitive.irreducible_fraction_map
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizedGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    {P : Polynomial R} (hprim : P.IsPrimitive) (hirr : Irreducible P) :
    Irreducible (Polynomial.map (algebraMap R K) P) := by
  have hP0 : P ≠ 0 := hirr.ne_zero
  have hmapinj : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hmap0 : Polynomial.map (algebraMap R K) P ≠ 0 := fun h =>
    hP0 (hmapinj (by simpa using h))
  refine ⟨?_, ?_⟩
  · intro hu
    refine hirr.not_isUnit ?_
    have hdvd : Polynomial.map (algebraMap R K) P ∣
        Polynomial.map (algebraMap R K) (1 : Polynomial R) := by
      simpa using hu.dvd
    exact isUnit_of_dvd_one
      (GaloisForLFunctions.Polynomial.IsPrimitive.dvd_of_fraction_map_dvd hprim hP0 hdvd)
  · intro g h hgh
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hgh
      exact hmap0 hgh
    have hh0 : h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hgh
      exact hmap0 hgh
    obtain ⟨g₀, hg₀0, hg₀prim, a, hga⟩ :=
      exists_primitive_polynomial_fraction_clear (R := R) (K := K) hg0
    obtain ⟨h₀, hh₀0, hh₀prim, b, hhb⟩ :=
      exists_primitive_polynomial_fraction_clear (R := R) (K := K) hh0
    have hprod : Polynomial.map (algebraMap R K) (g₀ * h₀) =
        Polynomial.C ((a : K) * (b : K)) * Polynomial.map (algebraMap R K) P := by
      rw [Polynomial.map_mul, hga, hhb, hgh, Polynomial.C_mul]
      ring
    have hdvdK : Polynomial.map (algebraMap R K) P ∣
        Polynomial.map (algebraMap R K) (g₀ * h₀) :=
      ⟨Polynomial.C ((a : K) * (b : K)), by rw [hprod]; ring⟩
    obtain ⟨T, hT⟩ :=
      GaloisForLFunctions.Polynomial.IsPrimitive.dvd_of_fraction_map_dvd hprim hP0 hdvdK
    have hmapT : Polynomial.map (algebraMap R K) T =
        Polynomial.C ((a : K) * (b : K)) := by
      refine mul_left_cancel₀ hmap0 ?_
      rw [← Polynomial.map_mul, ← hT, hprod]
      ring
    have hTC : T = Polynomial.C (T.coeff 0) :=
      polynomial_eq_C_of_fraction_map_eq_C hmapT
    have hprimprod : (g₀ * h₀).IsPrimitive := hg₀prim.mul hh₀prim
    have htunit : IsUnit (T.coeff 0) := by
      refine hprimprod (T.coeff 0) ⟨P, ?_⟩
      rw [hT]
      conv_lhs => rw [hTC]
      ring
    obtain ⟨t, ht⟩ := htunit
    have hCt : Polynomial.C (t : R) * Polynomial.C ((t⁻¹ : Rˣ) : R) = 1 := by
      rw [← Polynomial.C_mul]
      simp
    have hTt : T = Polynomial.C (t : R) := by rw [hTC, ht]
    have hfac : g₀ * h₀ = P * Polynomial.C (t : R) := by rw [hT, hTt]
    have hPfac : P = (g₀ * Polynomial.C ((t⁻¹ : Rˣ) : R)) * h₀ := by
      calc
        P = (P * Polynomial.C (t : R)) * Polynomial.C ((t⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, hCt, mul_one]
        _ = (g₀ * h₀) * Polynomial.C ((t⁻¹ : Rˣ) : R) := by rw [hfac]
        _ = (g₀ * Polynomial.C ((t⁻¹ : Rˣ) : R)) * h₀ := by ring
    rcases hirr.isUnit_or_isUnit hPfac with hu | hu
    · left
      have hg₀unit : IsUnit g₀ := isUnit_of_mul_isUnit_left hu
      have hmapunit : IsUnit (Polynomial.map (algebraMap R K) g₀) :=
        hg₀unit.map (Polynomial.mapRingHom (algebraMap R K))
      rw [hga] at hmapunit
      exact isUnit_of_mul_isUnit_right hmapunit
    · right
      have hmapunit : IsUnit (Polynomial.map (algebraMap R K) h₀) :=
        hu.map (Polynomial.mapRingHom (algebraMap R K))
      rw [hhb] at hmapunit
      exact isUnit_of_mul_isUnit_right hmapunit

end

end GaloisForLFunctions
