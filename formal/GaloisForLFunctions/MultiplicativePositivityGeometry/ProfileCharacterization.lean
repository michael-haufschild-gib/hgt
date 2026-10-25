import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteProfiles

/-!
# What multiplicative positivity permits on a progression

Let `d : ℤ → ℝ` be even and supported in `[−K, K]`. The following are equivalent:

1. `d` is the profile `m ↦ D(m t₀)` of the boundary divisor of some nonnegative weighted family;
2. `d` is positive definite on `ℤ`;
3. `P_d(θ) = d 0 + 2 Σ_{m ≤ K} d m cos(mθ) ≥ 0` for every `θ`.

(1 ⇒ 2) is boundary positivity restricted to the subgroup `t₀ℤ`; (2 ⇒ 3) is the Fejér limit
(`cosinePolynomial_profileCoeff_nonneg`). (3 ⇒ 1) is the arithmetic realization: the von Mangoldt
weights twisted by `P_d(log n)` have profile `d` (`twistedDivisor_profileCoeff`).

So the finitely supported boundary configurations allowed by nonnegative log-coefficients are
exactly the coefficient sequences of nonnegative cosine polynomials, and every one of them occurs
for an Euler product built from ζ (`boundary_profile_iff`, `profile_isEvenPosDef_iff`).
-/

open Finset

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {d : ℤ → ℝ} {K : ℕ}

/-- Twisting by the cosine polynomial of a profile reproduces the profile on `ℤ`. -/
theorem twistedDivisor_profileCoeff (hev : ∀ m, d (-m) = d m)
    (hsupp : ∀ m : ℤ, (K : ℤ) < |m| → d m = 0) (hP : ∀ θ, 0 ≤
      HTGeometry.cosinePolynomial (profileCoeff d) K θ) (m : ℤ) :
    twistedDivisor (profileCoeff d) K 1 m = d m := by
  have hnat : ∀ n : ℕ, twistedDivisor (profileCoeff d) K 1 n = d n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [profileCoeff] using twistedDivisor_zero (profileCoeff d) K one_ne_zero
    · by_cases hnK : n ≤ K
      · have h := twistedDivisor_mul (profileCoeff d) hn hnK one_ne_zero
        rw [mul_one] at h
        rw [h, profileCoeff, if_neg (Nat.pos_iff_ne_zero.mp hn)]
        ring
      · push Not at hnK
        have hn' : (K : ℤ) < |((n : ℕ) : ℤ)| := by
          rw [abs_of_nonneg (by positivity)]
          exact_mod_cast hnK
        rw [twistedDivisor_eq_zero, hsupp n hn']
        intro k hk
        have hkn : (k : ℝ) < n := by exact_mod_cast hk.trans_lt hnK
        constructor
        · rw [mul_one]; exact hkn.ne'
        · have : (0 : ℝ) ≤ k := by positivity
          rw [mul_one]; linarith
  have hpd := twistedDivisor_isEvenPosDef hP 1
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact_mod_cast hnat n
  · push_cast
    rw [hpd.even, hev]
    exact_mod_cast hnat n

/-- **Profiles: positive definite ⇔ nonnegative cosine polynomial.** -/
theorem profile_isEvenPosDef_iff (hev : ∀ m, d (-m) = d m)
    (hsupp : ∀ m : ℤ, (K : ℤ) < |m| → d m = 0) :
    IsEvenPosDef d ↔ ∀ θ, 0 ≤ HTGeometry.cosinePolynomial (profileCoeff d) K θ := by
  constructor
  · intro hd θ
    refine cosinePolynomial_profileCoeff_nonneg hd (fun r hr => hsupp _ ?_) θ
    rw [abs_of_nonneg (by positivity)]
    omega
  · intro hP
    have h := twistedProfile_isEvenPosDef hP 1
    have heq : (fun m : ℤ => twistedDivisor (profileCoeff d) K 1 (m * 1)) = d := by
      funext m
      rw [mul_one]
      exact twistedDivisor_profileCoeff hev hsupp hP m
    rwa [heq] at h

/-- **Boundary profiles are exactly nonnegative cosine polynomials.** A finitely supported even
profile is the progression profile of a boundary divisor of nonnegative weights iff its cosine
polynomial is nonnegative; the realizing datum can be taken to be twisted von Mangoldt weights. -/
theorem boundary_profile_iff (hev : ∀ m, d (-m) = d m)
    (hsupp : ∀ m : ℤ, (K : ℤ) < |m| → d m = 0) :
    (∃ (lam : ℕ → ℝ) (w : ℝ → ℕ → ℝ) (D : ℝ → ℝ) (t₀ : ℝ),
        IsBoundaryDivisor lam w D ∧ ∀ m : ℤ, D (m * t₀) = d m) ↔
      ∀ θ, 0 ≤ HTGeometry.cosinePolynomial (profileCoeff d) K θ := by
  constructor
  · rintro ⟨lam, w, D, t₀, hD, hd⟩
    have hpd := hD.isEvenPosDef.comp_addMonoidHom
      ((AddMonoidHom.mulRight t₀).comp (Int.castAddHom ℝ))
    have heq : (D ∘ ((AddMonoidHom.mulRight t₀).comp (Int.castAddHom ℝ))) = d := by
      funext m
      exact hd m
    rw [heq] at hpd
    exact (profile_isEvenPosDef_iff hev hsupp).mp hpd
  · intro hP
    refine ⟨logFrequency, twistedWeight (profileCoeff d) K 1, twistedDivisor (profileCoeff d) K 1,
      1, twisted_isBoundaryDivisor hP 1, fun m => ?_⟩
    rw [mul_one]
    exact twistedDivisor_profileCoeff hev hsupp hP m

end GaloisForLFunctions.MultiplicativePositivityGeometry
