import GaloisForLFunctions.HTGeometry.DeformedFibreJets

/-!
# The postcritical coefficient is not a rational function of the observation

Two values that a single rational expression in a *common* argument would have to compute are equal.
So two jets with the same critical observation and the same new raw coefficient, whose first
postcritical reciprocal coefficients differ, prove that no rational function of that data computes
the postcritical coefficient.

The argument needs nothing but a domain: if `v₀ Q = P` and `v₁ Q = P` for the same `P` and `Q`
evaluated at the same point, then `(v₀ - v₁) Q = 0`, so either the two values agree or the
denominator vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Two separated values admit no common rational expression in a common argument.** -/
theorem not_common_rational_of_ne {K S ι : Type*} [Field K] [CommRing S] [NoZeroDivisors S]
    [Algebra K S] {obs : ι → S} {v₀ v₁ : S} (hne : v₀ ≠ v₁)
    {P Q : MvPolynomial ι K} (hQ : MvPolynomial.aeval obs Q ≠ 0)
    (h₀ : v₀ * MvPolynomial.aeval obs Q = MvPolynomial.aeval obs P)
    (h₁ : v₁ * MvPolynomial.aeval obs Q = MvPolynomial.aeval obs P) : False := by
  refine hne ?_
  have hzero : (v₀ - v₁) * MvPolynomial.aeval obs Q = 0 := by linear_combination h₀ - h₁
  rcases mul_eq_zero.1 hzero with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hQ

variable (K : Type*) [Field K]

/-- The critical observation of a jet over the horizon, together with the new raw coefficient: the
raw coefficients from the raw critical order up to and including the horizon, and the reciprocal
coefficients from the reciprocal critical order up to the horizon. -/
noncomputable def criticalObservation {S : Type*} [CommRing S] (m n : ℕ) (Z W : S[X]) (τ : S) :
    Fin (n + 1) ⊕ Fin m → S
  | Sum.inl k => if (k : ℕ) < n then Z.coeff (m + (k : ℕ)) else τ
  | Sum.inr k => W.coeff (n + (k : ℕ))

/-- **The two deformed jets share their critical observation.** -/
theorem criticalObservation_eq {S : Type*} [CommRing S] {m n : ℕ} {Z₀ W₀ Z₁ W₁ : S[X]} {τ : S}
    (hZ : ∀ i, m ≤ i → Z₀.coeff i = Z₁.coeff i)
    (hW : ∀ j, n ≤ j → W₀.coeff j = W₁.coeff j) :
    criticalObservation m n Z₀ W₀ τ = criticalObservation m n Z₁ W₁ τ := by
  funext s
  rcases s with k | k
  · show (if (k : ℕ) < n then Z₀.coeff (m + (k : ℕ)) else τ)
      = (if (k : ℕ) < n then Z₁.coeff (m + (k : ℕ)) else τ)
    split_ifs with h
    · exact hZ _ (by omega)
    · rfl
  · exact hW _ (by omega)

/-- **The first postcritical reciprocal coefficient is not a rational function of the critical
observation and the new raw coefficient.**  Two jets over the universal deformation share that data
and separate the postcritical coefficient, so no polynomial fraction in it can compute the
coefficient for both. -/
theorem postcritical_not_rational {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A₀ B₀ A₁ B₁ : K[X]}
    (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m) (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    (hA₁ : A₁.Monic) (hA₁deg : A₁.natDegree = m) (hB₁ : B₁.Monic) (hB₁deg : B₁.natDegree = n)
    (hcop₀ : IsCoprime A₀ B₀) (hcop₁ : IsCoprime A₁ B₁)
    (hfac₀ : A₀ * B₀ = 1 + X ^ (m + n)) (hfac₁ : A₁ * B₁ = 1 + X ^ (m + n))
    (hsep : A₀.coeff 0 ≠ A₁.coeff 0) :
    ∃ (Z₀ W₀ Z₁ W₁ : (deformBase K m n)[X]) (v₀ v₁ : deformBase K m n),
      criticalObservation m n Z₀ W₀ (deformParam K m n)
          = criticalObservation m n Z₁ W₁ (deformParam K m n) ∧
      (X : (deformBase K m n)[X]) ^ (m + n + 1)
        ∣ (Z₀ + Polynomial.C (deformParam K m n) * X ^ (m + n))
          * (W₀ + Polynomial.C v₀ * X ^ (m + n)) - 1 ∧
      (X : (deformBase K m n)[X]) ^ (m + n + 1)
        ∣ (Z₁ + Polynomial.C (deformParam K m n) * X ^ (m + n))
          * (W₁ + Polynomial.C v₁ * X ^ (m + n)) - 1 ∧
      ∀ P Q : MvPolynomial (Fin (n + 1) ⊕ Fin m) K,
        MvPolynomial.aeval (criticalObservation m n Z₀ W₀ (deformParam K m n)) Q ≠ 0 →
        v₀ * MvPolynomial.aeval (criticalObservation m n Z₀ W₀ (deformParam K m n)) Q
            = MvPolynomial.aeval (criticalObservation m n Z₀ W₀ (deformParam K m n)) P →
        v₁ * MvPolynomial.aeval (criticalObservation m n Z₀ W₀ (deformParam K m n)) Q
            ≠ MvPolynomial.aeval (criticalObservation m n Z₀ W₀ (deformParam K m n)) P := by
  obtain ⟨Z₀, W₀, Z₁, W₁, v₀, v₁, hobsZ, hobsW, hpost₀, hpost₁, hvne, -, -, -, -, -, -⟩ :=
    exists_two_deformed_postcritical_jets K hm hn hA₀ hA₀deg hB₀ hB₀deg hA₁ hA₁deg hB₁ hB₁deg
      hcop₀ hcop₁ hfac₀ hfac₁ hsep
  refine ⟨Z₀, W₀, Z₁, W₁, v₀, v₁, criticalObservation_eq hobsZ hobsW, hpost₀, hpost₁,
    fun P Q hQ h₀ h₁ => ?_⟩
  exact not_common_rational_of_ne hvne hQ h₀ h₁

end GaloisForLFunctions.HTGeometry
