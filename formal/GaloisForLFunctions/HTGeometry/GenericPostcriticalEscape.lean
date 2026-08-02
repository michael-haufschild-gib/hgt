import GaloisForLFunctions.HTGeometry.GenericJetAlgebra
import GaloisForLFunctions.HTGeometry.DeformedObservationIndependent

/-!
# The postcritical reciprocal coefficient escapes the critical field

For the generic jet of horizon `L = m + n`, no rational function of the critical observation and the
new raw coefficient computes the first postcritical reciprocal coefficient.

The proof specialises the generic jet in two ways at once.  The universal deformation of the critical
observation carries two jets — two points of one fibre — which agree on the whole of that data and
disagree at the postcritical coefficient.  A rational expression valid generically would specialise
to both, and a rational expression cannot take two values at one argument.  The denominator survives
both specialisations because the deformed observation is algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K]

/-- The generic critical observation, together with the new raw coefficient. -/
noncomputable def genericObservation (m n : ℕ) :
    Fin (n + 1) ⊕ Fin m → genericJetAlgebra K (m + n)
  | Sum.inl k =>
      if (k : ℕ) < n then genericRaw K (m + n) (m + (k : ℕ)) else genericRaw K (m + n) (m + n)
  | Sum.inr k => genericRecip K (m + n) (n + (k : ℕ))

variable {K}

/-- **The postcritical reciprocal coefficient is not a rational function of the critical
observation and the new raw coefficient.**  For every nonzero denominator, the corresponding
rational relation fails for the generic jet. -/
theorem genericPostcritical_not_rational {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A₀ B₀ A₁ B₁ : K[X]}
    (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m) (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    (hA₁ : A₁.Monic) (hA₁deg : A₁.natDegree = m) (hB₁ : B₁.Monic) (hB₁deg : B₁.natDegree = n)
    (hcop₀ : IsCoprime A₀ B₀) (hcop₁ : IsCoprime A₁ B₁)
    (hfac₀ : A₀ * B₀ = 1 + X ^ (m + n)) (hfac₁ : A₁ * B₁ = 1 + X ^ (m + n))
    (hsepA : A₀.coeff 0 ≠ A₁.coeff 0)
    (P Q : MvPolynomial (Fin (n + 1) ⊕ Fin m) K) (hQ : Q ≠ 0) :
    genericRecip K (m + n) (m + n) * MvPolynomial.aeval (genericObservation K m n) Q
      ≠ MvPolynomial.aeval (genericObservation K m n) P := by
  classical
  intro hrel
  obtain ⟨Z₀, W₀, Z₁, W₁, v₀, v₁, hobsZ, hobsW, hpost₀, hpost₁, hvne, hW₀L, hW₁L,
      hZ₀deg, hZ₁deg, hZdec, hWdec⟩ :=
    exists_two_deformed_postcritical_jets K hm hn hA₀ hA₀deg hB₀ hB₀deg hA₁ hA₁deg hB₁ hB₁deg
      hcop₀ hcop₁ hfac₀ hfac₁ hsepA
  set τ : deformBase K m n := deformParam K m n with hτ
  have hshift : ∀ (Z : (deformBase K m n)[X]) (c : deformBase K m n) (j : ℕ), j < m + n →
      (Z + Polynomial.C c * X ^ (m + n)).coeff j = Z.coeff j := by
    intro Z c j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by omega), mul_zero, add_zero]
  have htop : ∀ (Z : (deformBase K m n)[X]) (c : deformBase K m n), Z.natDegree < m + n →
      (Z + Polynomial.C c * X ^ (m + n)).coeff (m + n) = c := by
    intro Z c hZ
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
      mul_one, Polynomial.coeff_eq_zero_of_natDegree_lt hZ, zero_add]
  -- from a jet of the fibre, a specialisation of the generic jet algebra
  have key : ∀ (Z W : (deformBase K m n)[X]) (v : deformBase K m n),
      (X : (deformBase K m n)[X]) ^ (m + n + 1) ∣ (Z + Polynomial.C τ * X ^ (m + n))
        * (W + Polynomial.C v * X ^ (m + n)) - 1 →
      Z.natDegree < m + n → W.coeff (m + n) = 0 →
      ∃ π : genericJetAlgebra K (m + n) →ₐ[K] deformBase K m n,
        (∀ s, π (genericObservation K m n s) = criticalObservation m n Z W τ s) ∧
        π (genericRecip K (m + n) (m + n)) = v := by
    intro Z W v hdvd hZdeg hWL
    set ZZ : (deformBase K m n)[X] := Z + Polynomial.C τ * X ^ (m + n) with hZZ
    set WW : (deformBase K m n)[X] := W + Polynomial.C v * X ^ (m + n) with hWW
    have hu : IsUnit (ZZ.coeff 0) := by
      refine ⟨⟨ZZ.coeff 0, WW.coeff 0, coeff_zero_mul_of_dvd hdvd, ?_⟩, rfl⟩
      rw [mul_comm]
      exact coeff_zero_mul_of_dvd hdvd
    set a : Fin (m + n + 1) → deformBase K m n := fun j => ZZ.coeff (j : ℕ) with ha
    have hau : IsUnit (a 0) := hu
    refine ⟨jetLiftₐ a hau, ?_, ?_⟩
    · intro s
      rcases s with k | k
      · show (jetLiftₐ a hau) (if (k : ℕ) < n then genericRaw K (m + n) (m + (k : ℕ))
          else genericRaw K (m + n) (m + n))
          = (if (k : ℕ) < n then Z.coeff (m + (k : ℕ)) else τ)
        by_cases hk : (k : ℕ) < n
        · rw [if_pos hk, if_pos hk, jetLiftₐ_apply,
            jetLift_genericRaw (K := K) a hau (by omega : m + (k : ℕ) < m + n + 1)]
          exact hshift Z τ (m + (k : ℕ)) (by omega)
        · rw [if_neg hk, if_neg hk, jetLiftₐ_apply,
            jetLift_genericRaw (K := K) a hau (by omega : m + n < m + n + 1)]
          exact htop Z τ hZdeg
      · have hkm : (k : ℕ) < m := k.2
        show (jetLiftₐ a hau) (genericRecip K (m + n) (n + (k : ℕ))) = W.coeff (n + (k : ℕ))
        rw [jetLiftₐ_apply,
          jetLift_genericRecip (K := K) (Z := ZZ) (W := WW) hdvd hu (n + (k : ℕ)) (by omega)]
        exact hshift W v (n + (k : ℕ)) (by omega)
    · rw [jetLiftₐ_apply,
        jetLift_genericRecip (K := K) (Z := ZZ) (W := WW) hdvd hu (m + n) (le_refl _)]
      rw [hWW, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
        mul_one, hWL, zero_add]
  obtain ⟨π₀, hπ₀obs, hπ₀pc⟩ := key Z₀ W₀ v₀ hpost₀ hZ₀deg hW₀L
  obtain ⟨π₁, hπ₁obs, hπ₁pc⟩ := key Z₁ W₁ v₁ hpost₁ hZ₁deg hW₁L
  set dobs : Fin (n + 1) ⊕ Fin m → deformBase K m n := criticalObservation m n Z₀ W₀ τ with hdobs
  have hπ₁obs' : ∀ s, π₁ (genericObservation K m n s) = dobs s := by
    intro s
    rw [hπ₁obs, hdobs, criticalObservation_eq hobsZ hobsW]
  have htrans : ∀ (π : genericJetAlgebra K (m + n) →ₐ[K] deformBase K m n)
      (R : MvPolynomial (Fin (n + 1) ⊕ Fin m) K),
      π (MvPolynomial.aeval (genericObservation K m n) R)
        = MvPolynomial.aeval (fun s => π (genericObservation K m n s)) R :=
    fun π R => MvPolynomial.comp_aeval_apply (genericObservation K m n) π R
  have h₀ : v₀ * MvPolynomial.aeval dobs Q = MvPolynomial.aeval dobs P := by
    have hc := congrArg π₀ hrel
    rw [map_mul, htrans, htrans, hπ₀pc] at hc
    rw [show (fun s => π₀ (genericObservation K m n s)) = dobs from funext hπ₀obs] at hc
    exact hc
  have h₁ : v₁ * MvPolynomial.aeval dobs Q = MvPolynomial.aeval dobs P := by
    have hc := congrArg π₁ hrel
    rw [map_mul, htrans, htrans, hπ₁pc] at hc
    rw [show (fun s => π₁ (genericObservation K m n s)) = dobs from funext hπ₁obs'] at hc
    exact hc
  have hind : AlgebraicIndependent K dobs :=
    algebraicIndependent_criticalObservation hn hA₀ hA₀deg hB₀ hB₀deg hZdec hWdec
  have hQ0 : MvPolynomial.aeval dobs Q ≠ 0 := by
    intro hcon
    exact hQ ((algebraicIndependent_iff_injective_aeval.1 hind) (by rw [hcon, map_zero]))
  exact not_common_rational_of_ne hvne hQ0 h₀ h₁

end GaloisForLFunctions.HTGeometry
