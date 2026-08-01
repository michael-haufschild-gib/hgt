import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A prime times a non-multiple is never a square

If `p` is prime and does not divide `a`, then `p * a` is not a square: `p` occurs to an odd
multiplicity.  For a variable of a polynomial ring, not dividing is decided by setting that variable
to zero.

This is the arithmetic step that distinguishes the two candidate intersections in a Kummer base
change: the discriminant times the Kummer generator is a square only if the generator divides the
discriminant.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- **A prime times a non-multiple is not a square.** -/
theorem not_isSquare_of_prime_of_not_dvd {R : Type u} [CommMonoidWithZero R] [IsCancelMulZero R]
    {p a : R}
    (hp : Prime p) (hpa : ¬ p ∣ a) : ¬ IsSquare (p * a) := by
  rintro ⟨b, hb⟩
  have hdvd : p ∣ b * b := ⟨a, hb.symm⟩
  have hpb : p ∣ b := (hp.dvd_mul.1 hdvd).elim id id
  obtain ⟨c, rfl⟩ := hpb
  refine hpa ⟨c * c, ?_⟩
  refine mul_left_cancel₀ hp.ne_zero ?_
  rw [hb]
  simp only [mul_comm, mul_left_comm]

/-- **A ring hom killing `p` but not `f` witnesses that `p` does not divide `f`.** -/
theorem not_dvd_of_hom_ne_zero {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    {p f : R} (hp : φ p = 0) (hf : φ f ≠ 0) : ¬ (p ∣ f) := by
  rintro ⟨g, rfl⟩
  exact hf (by rw [map_mul, hp, zero_mul])

/-- **A variable does not divide a polynomial that survives setting it to zero.** -/
theorem not_X_dvd_of_aeval_ne_zero {σ : Type v} [DecidableEq σ] {K : Type u} [CommRing K]
    (i : σ) (f : MvPolynomial σ K)
    (h : (MvPolynomial.aeval (fun j => if j = i then 0 else MvPolynomial.X j) f :
      MvPolynomial σ K) ≠ 0) :
    ¬ (MvPolynomial.X i ∣ f) := by
  rintro ⟨g, rfl⟩
  exact h (by rw [map_mul, MvPolynomial.aeval_X, if_pos rfl, zero_mul])

/-- **The specialised fibre polynomial is separable.**  Setting the first coefficient to zero and the
others to the values `q = 1`, `c_1 = 1`, `c_2 = ⋯ = c_{n-1} = 0` turns the fibre equation into
`X^{n+1} - X`, which has distinct roots: the origin, which is now a simple root, and the `n`-th roots
of unity.

This is the witness that the discriminant does not vanish identically when the first coefficient is
set to zero, which is what makes that coefficient a non-divisor of the discriminant. -/
theorem separable_X_pow_succ_sub_X {K : Type u} [Field K] {n : ℕ} (hn0 : n ≠ 0)
    (hn : (n : K) ≠ 0) :
    (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial K).Separable := by
  have hfac : (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial K)
      = Polynomial.X * (Polynomial.X ^ n - 1) := by ring
  rw [hfac]
  refine Polynomial.Separable.mul Polynomial.separable_X ?_ ?_
  · simpa using Polynomial.separable_X_pow_sub_C (1 : K) hn one_ne_zero
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨Polynomial.X ^ m, -1, by ring⟩

/-- **A separable polynomial of positive degree has nonzero discriminant.** -/
theorem discr_ne_zero_of_separable {K : Type u} [Field K] [CharZero K] {f : Polynomial K}
    (hdeg : 0 < f.degree) (hsep : f.Separable) : f.discr ≠ 0 := by
  intro hc
  have hderiv : f.derivative.natDegree = f.natDegree - 1 := Polynomial.natDegree_derivative f
  have hres := Polynomial.resultant_deriv hdeg
  rw [hc, mul_zero] at hres
  rw [← hderiv] at hres
  have hzero := Polynomial.resultant_eq_zero_iff.1 hres
  exact hzero.2 hsep

/-- **The discriminant commutes with a specialisation that preserves the degree.** -/
theorem discr_map {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain S] (φ : R →+* S)
    {f : Polynomial R} (hpos : 0 < f.degree)
    (hdeg : (f.map φ).natDegree = f.natDegree) (hlc : φ f.leadingCoeff ≠ 0) :
    Polynomial.discr (f.map φ) = φ (Polynomial.discr f) := by
  have hposS : 0 < (f.map φ).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hdeg,
      Polynomial.natDegree_pos_iff_degree_pos]
    exact hpos
  have hlcmap : (f.map φ).leadingCoeff = φ f.leadingCoeff := by
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hdeg, Polynomial.coeff_map]
  have h1 := Polynomial.resultant_deriv hposS
  have h2 := congrArg φ (Polynomial.resultant_deriv hpos)
  rw [hdeg, hlcmap] at h1
  rw [map_mul, map_mul, map_pow, map_neg, map_one, ← Polynomial.resultant_map_map,
    ← Polynomial.derivative_map] at h2
  rw [h2] at h1
  have hne : ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) * φ f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by simp)) hlc
  exact (mul_left_cancel₀ hne h1).symm

end GaloisForLFunctions.HTGeometry
