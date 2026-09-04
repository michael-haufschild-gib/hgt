import GaloisForLFunctions.HTGeometry.SecondOrderCoefficientDecomposition

/-!
# Strelitz logarithmic-jet reduction for second-order ADEs

For an entire function `f`, put `u = z f' / f` and `v = z u'`.  The identity

`z² f'' = f (v + u² - u)`

turns every polynomial relation in `(f, f', f'')` into a polynomial relation in `(f, u, v)`
after multiplication by a single even power of `z`.  This file implements that transformation
exactly.  The substitution is triangular, so a nonzero input relation remains nonzero; no
Newton-face or nondegeneracy assumption is introduced.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex

/-- Euler logarithmic derivative `z f'(z) / f(z)`. -/
def eulerLogDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z / f z

/-- Euler derivative of the Euler logarithmic derivative. -/
def eulerLogDerivSecond (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv (eulerLogDeriv f) z

/-- Exact logarithmic-jet identity replacing the second derivative. -/
theorem eulerSecondDeriv_eq
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hdf : DifferentiableAt ℂ (deriv f) z) (hfz : f z ≠ 0) :
    z ^ 2 * deriv (deriv f) z =
      f z * (eulerLogDerivSecond f z + (eulerLogDeriv f z) ^ 2 - eulerLogDeriv f z) := by
  have hnum := (hasDerivAt_id z).mul hdf.hasDerivAt
  have hu := hnum.div hf.hasDerivAt hfz
  have hdu : deriv (eulerLogDeriv f) z =
      ((deriv f z + z * deriv (deriv f) z) * f z -
        (z * deriv f z) * deriv f z) / f z ^ 2 := by
    change deriv (fun x => x * deriv f x / f x) z = _
    convert hu.deriv using 1 <;> first | rfl | simp [id_eq]
  rw [eulerLogDerivSecond, eulerLogDeriv, hdu]
  field_simp
  ring

/-- Exponent vector after replacing `(f, f', f'')` by `(f, u, q)` and clearing powers of `f`. -/
def strelitzExponent (p : SecondOrderPowers) : Fin 3 → ℕ :=
  ![p.value + p.first + p.second, p.first, p.second]

theorem strelitzExponent_injective : Function.Injective strelitzExponent := by
  intro p q h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  simp [strelitzExponent] at h0 h1 h2
  cases p
  cases q
  simp_all

/-- Polynomial before the triangular replacement `q = v + u² - u`. -/
def strelitzRawPolynomial
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ) :
    MvPolynomial (Fin 3) (Polynomial ℂ) :=
  ∑ p ∈ S, MvPolynomial.monomial
    (Finsupp.equivFunOnFinite.symm (strelitzExponent p))
    (Polynomial.X ^ (2 * d - (p.first + 2 * p.second)) * A p)

/-- A nonzero collected coefficient makes the raw Strelitz polynomial nonzero. -/
theorem strelitzRawPolynomial_ne_zero
    {S : Finset SecondOrderPowers} {A : SecondOrderPowers → Polynomial ℂ} {d : ℕ}
    {q : SecondOrderPowers} (hq : q ∈ S) (hAq : A q ≠ 0) :
    strelitzRawPolynomial S A d ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (strelitzExponent q))) hzero
  rw [strelitzRawPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single q] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hAq) hcoeff
  · intro p hp hne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro heq
    apply hne
    apply strelitzExponent_injective
    have hfun := congrArg Finsupp.equivFunOnFinite heq
    simpa using hfun
  · exact fun h => absurd hq h

/-- Triangular replacement of the third variable by `v + u² - u`. -/
def strelitzShift : MvPolynomial (Fin 3) (Polynomial ℂ) →+*
    MvPolynomial (Fin 3) (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![
    MvPolynomial.X 0,
    MvPolynomial.X 1,
    MvPolynomial.X 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.X 1]

/-- Explicit inverse triangular replacement. -/
def strelitzUnshift : MvPolynomial (Fin 3) (Polynomial ℂ) →+*
    MvPolynomial (Fin 3) (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![
    MvPolynomial.X 0,
    MvPolynomial.X 1,
    MvPolynomial.X 2 - (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 1)]

theorem strelitzUnshift_shift (P : MvPolynomial (Fin 3) (Polynomial ℂ)) :
    strelitzUnshift (strelitzShift P) = P := by
  have hhom : strelitzUnshift.comp strelitzShift =
      RingHom.id (MvPolynomial (Fin 3) (Polynomial ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [strelitzShift, strelitzUnshift]
    · intro i
      fin_cases i
      · simp [strelitzShift, strelitzUnshift]
      · simp [strelitzShift, strelitzUnshift]
      · simp [strelitzShift, strelitzUnshift]
        ring
  exact DFunLike.congr_fun hhom P

theorem strelitzShift_injective : Function.Injective strelitzShift :=
  Function.LeftInverse.injective strelitzUnshift_shift

/-- Final polynomial relation in `(f, u, v)`. -/
def strelitzLogJetPolynomial
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ) :
    MvPolynomial (Fin 3) (Polynomial ℂ) :=
  strelitzShift (strelitzRawPolynomial S A d)

/-- The final Strelitz polynomial remains nonzero. -/
theorem strelitzLogJetPolynomial_ne_zero
    {S : Finset SecondOrderPowers} {A : SecondOrderPowers → Polynomial ℂ} {d : ℕ}
    {q : SecondOrderPowers} (hq : q ∈ S) (hAq : A q ≠ 0) :
    strelitzLogJetPolynomial S A d ≠ 0 := by
  intro hzero
  exact strelitzRawPolynomial_ne_zero hq hAq (strelitzShift_injective hzero)

/-- Evaluation commutes with the triangular shift. -/
theorem eval₂_strelitzShift (P : MvPolynomial (Fin 3) (Polynomial ℂ))
    (z F U V : ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] (strelitzShift P) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V + U ^ 2 - U] P := by
  have hhom :
      (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) ![F, U, V]).comp
          strelitzShift =
        MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) ![F, U, V + U ^ 2 - U] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [strelitzShift]
    · intro i
      fin_cases i <;> simp [strelitzShift]
  exact DFunLike.congr_fun hhom P

/-- Explicit evaluation of the raw relation. -/
theorem eval₂_strelitzRawPolynomial
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ)
    (z F U Q : ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, Q]
        (strelitzRawPolynomial S A d) =
      ∑ p ∈ S, (A p).eval z * z ^ (2 * d - (p.first + 2 * p.second)) *
        F ^ (p.value + p.first + p.second) * U ^ p.first * Q ^ p.second := by
  classical
  rw [strelitzRawPolynomial, MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hprod :
      (Finsupp.equivFunOnFinite.symm (strelitzExponent p)).prod
          (fun i e => (![F, U, Q] : Fin 3 → ℂ) i ^ e) =
        F ^ (p.value + p.first + p.second) * U ^ p.first * Q ^ p.second := by
    rw [Finsupp.prod_fintype _ _ (by intro i; simp), Fin.prod_univ_three]
    rfl
  rw [MvPolynomial.eval₂_monomial, hprod]
  change Polynomial.eval z
      (Polynomial.X ^ (2 * d - (p.first + 2 * p.second)) * A p) *
        (F ^ (p.value + p.first + p.second) * U ^ p.first * Q ^ p.second) = _
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- Explicit evaluation of the shifted relation. -/
theorem eval₂_strelitzLogJetPolynomial
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ)
    (z F U V : ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V]
        (strelitzLogJetPolynomial S A d) =
      ∑ p ∈ S, (A p).eval z * z ^ (2 * d - (p.first + 2 * p.second)) *
        F ^ (p.value + p.first + p.second) * U ^ p.first *
          (V + U ^ 2 - U) ^ p.second := by
  rw [strelitzLogJetPolynomial, eval₂_strelitzShift,
    eval₂_strelitzRawPolynomial]

/-- Exact scaling identity for one second-order monomial. -/
theorem scale_secondOrder_monomial
    (A z F W₁ W₂ U Q : ℂ) (a b c d : ℕ)
    (hdeg : b + 2 * c ≤ 2 * d)
    (h₁ : z * W₁ = F * U) (h₂ : z ^ 2 * W₂ = F * Q) :
    z ^ (2 * d) * (A * F ^ a * W₁ ^ b * W₂ ^ c) =
      A * z ^ (2 * d - (b + 2 * c)) * F ^ (a + b + c) * U ^ b * Q ^ c := by
  have hp₁ := congrArg (fun x : ℂ => x ^ b) h₁
  have hp₂ := congrArg (fun x : ℂ => x ^ c) h₂
  have hp₁' : z ^ b * W₁ ^ b = F ^ b * U ^ b := by
    simpa [mul_pow] using hp₁
  have hp₂' : z ^ (2 * c) * W₂ ^ c = F ^ c * Q ^ c := by
    simpa [mul_pow, pow_mul] using hp₂
  have hz : z ^ (2 * d) = z ^ (2 * d - (b + 2 * c)) * z ^ b * z ^ (2 * c) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hz]
  calc
    (z ^ (2 * d - (b + 2 * c)) * z ^ b * z ^ (2 * c)) *
          (A * F ^ a * W₁ ^ b * W₂ ^ c) =
        A * z ^ (2 * d - (b + 2 * c)) * F ^ a *
          (z ^ b * W₁ ^ b) * (z ^ (2 * c) * W₂ ^ c) := by ring
    _ = A * z ^ (2 * d - (b + 2 * c)) * F ^ a *
          (F ^ b * U ^ b) * (F ^ c * Q ^ c) := by rw [hp₁', hp₂']
    _ = A * z ^ (2 * d - (b + 2 * c)) * F ^ (a + b + c) * U ^ b * Q ^ c := by
      rw [pow_add, pow_add]
      ring

/-- The shifted polynomial is the original relation multiplied by `z^(2d)`. -/
theorem eval₂_strelitzLogJetPolynomial_eq_scaled_relation
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ)
    (z F W₁ W₂ U V : ℂ)
    (hdeg : ∀ p ∈ S, p.value + p.first + p.second ≤ d)
    (h₁ : z * W₁ = F * U)
    (h₂ : z ^ 2 * W₂ = F * (V + U ^ 2 - U)) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V]
        (strelitzLogJetPolynomial S A d) =
      z ^ (2 * d) *
        ∑ p ∈ S, (A p).eval z * F ^ p.value * W₁ ^ p.first * W₂ ^ p.second := by
  rw [eval₂_strelitzLogJetPolynomial, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hweighted : p.first + 2 * p.second ≤ 2 * d := by
    have htotal := hdeg p hp
    omega
  exact (scale_secondOrder_monomial ((A p).eval z) z F W₁ W₂ U
    (V + U ^ 2 - U) p.value p.first p.second d hweighted h₁ h₂).symm

/-- Analytic specialization of the exact scaling identity. -/
theorem eval₂_strelitzLogJetPolynomial_at_eulerLogDeriv
    (S : Finset SecondOrderPowers) (A : SecondOrderPowers → Polynomial ℂ) (d : ℕ)
    {f : ℂ → ℂ} {z : ℂ}
    (hdeg : ∀ p ∈ S, p.value + p.first + p.second ≤ d)
    (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        ![f z, eulerLogDeriv f z, eulerLogDerivSecond f z]
        (strelitzLogJetPolynomial S A d) =
      z ^ (2 * d) *
        ∑ p ∈ S, (A p).eval z * (f z) ^ p.value *
          (deriv f z) ^ p.first * (deriv (deriv f) z) ^ p.second := by
  apply eval₂_strelitzLogJetPolynomial_eq_scaled_relation S A d z
    (f z) (deriv f z) (deriv (deriv f) z)
    (eulerLogDeriv f z) (eulerLogDerivSecond f z) hdeg
  · rw [eulerLogDeriv]
    field_simp
  · exact eulerSecondDeriv_eq hf.differentiableAt
      hf.deriv.differentiableAt hfz

open GaloisForLFunctions

/-- **Strelitz logarithmic-jet compiler.** Every order-two ADE for an entire function yields a
nonzero polynomial-coefficient relation in `(f, zf'/f, z(zf'/f)')` wherever `f` is nonzero. -/
theorem exists_strelitzLogJetRelation_of_differentiallyAlgebraicOfOrder_two
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hDA : DifferentiallyAlgebraicOfOrder f 2) :
    ∃ Q : MvPolynomial (Fin 3) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ z : ℂ, f z ≠ 0 →
        MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          ![f z, eulerLogDeriv f z, eulerLogDerivSecond f z] Q = 0 := by
  obtain ⟨S, A, d, ⟨q, hq, hAq⟩, hdeg, hrel⟩ :=
    exists_secondOrderRelation_of_differentiallyAlgebraicOfOrder_two hDA
  refine ⟨strelitzLogJetPolynomial S A d,
    strelitzLogJetPolynomial_ne_zero hq hAq, ?_⟩
  intro z hfz
  rw [eval₂_strelitzLogJetPolynomial_at_eulerLogDeriv S A d hdeg (hf z (by simp)) hfz,
    hrel z, mul_zero]

end

end GaloisForLFunctions.HTGeometry
