import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts

/-!
# The trivial character and Dedekind zeta

The trivial ray class character has value one precisely on ideals prime to the finite modulus.
Its L-series is Dedekind zeta with the Euler factors at primes dividing that modulus removed.
-/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The modulus with unit finite part and no real-place conditions. -/
def trivialModulus : Modulus K := ⟨1, one_ne_zero, ∅⟩

theorem heckeValue_trivialModulus_one {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    heckeValue (trivialModulus K) 1 I = 1 := by
  have hm : idealUnit hI ∈ idealGroup (trivialModulus K) := by
    intro v hv
    exact (v.prime.not_unit (isUnit_of_dvd_one hv)).elim
  rw [heckeValue_of_mem (trivialModulus K) 1 hI hm]
  rfl

/-- For the unit modulus, the trivial-character coefficients count ideals of each positive norm. -/
theorem heckeCoeff_trivialModulus_one {n : ℕ} (hn : n ≠ 0) :
    heckeCoeff (trivialModulus K) 1 n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  rw [heckeCoeff]
  have hvalue (I : Ideal (𝓞 K)) (hI : I ∈ idealsOfNorm K n) :
      heckeValue (trivialModulus K) 1 I = 1 := by
    apply heckeValue_trivialModulus_one
    intro hzero
    apply hn
    rw [← mem_idealsOfNorm.mp hI, hzero, Ideal.absNorm_bot]
  rw [Finset.sum_congr rfl hvalue, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact congrArg (fun n : ℕ => (n : ℂ))
    (Nat.card_eq_card_finite_toFinset (Ideal.finite_setOf_absNorm_eq n)).symm

/-- Dedekind zeta is the trivial Hecke L-series for the unit modulus. -/
theorem heckeL_trivialModulus_one (s : ℂ) :
    heckeL (trivialModulus K) 1 s = dedekindZeta K s := by
  exact LSeries_congr (fun {_} hn => heckeCoeff_trivialModulus_one (K := K) hn) s

/-- The trivial ray class character deletes exactly the primes dividing the finite modulus. -/
theorem heckeValue_one_prime (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K)) :
    heckeValue 𝔪 1 v.asIdeal = if v.asIdeal ∣ 𝔪.fin then 0 else 1 := by
  by_cases hv : v.asIdeal ∣ 𝔪.fin
  · rw [if_pos hv]
    apply heckeValue_of_not_mem
    rintro ⟨hI, hm⟩
    have h := hm v hv
    rw [coe_idealUnit, count_self] at h
    exact one_ne_zero h
  · rw [if_neg hv]
    have hm : idealUnit v.ne_bot ∈ idealGroup 𝔪 := by
      intro w hw
      rw [coe_idealUnit]
      exact count_maximal_coprime K w (fun h => hv (h.symm ▸ hw))
    rw [heckeValue_of_mem 𝔪 1 v.ne_bot hm]
    rfl

/-- The trivial-character L-series is Dedekind zeta with finitely many Euler factors removed. -/
theorem heckeL_one_eq_dedekindZeta_mul (𝔪 : Modulus K) {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 1 s = dedekindZeta K s *
      ∏ v ∈ (finite_primes_dvd 𝔪).toFinset, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  let F (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
    if v.asIdeal ∣ 𝔪.fin then 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) else 1
  have hF : HasProd F
      (∏ v ∈ (finite_primes_dvd 𝔪).toFinset, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
    have h : HasProd F (∏ v ∈ (finite_primes_dvd 𝔪).toFinset, F v) :=
      hasProd_prod_of_ne_finset_one (by
        intro v hv
        simp only [Set.Finite.mem_toFinset] at hv
        exact if_neg hv)
    convert h using 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact (if_pos hv).symm
  have hζ := heckeL_eulerProduct_hasProd (trivialModulus K) 1 hs
  rw [heckeL_trivialModulus_one] at hζ
  have h := hζ.mul hF
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      (1 - heckePrimeTerm (trivialModulus K) 1 s v)⁻¹ * F v =
        (1 - heckePrimeTerm 𝔪 1 s v)⁻¹ := by
    have hv := heckeValue_trivialModulus_one v.ne_bot
    have hne := heckeEulerDenominator_ne_zero (trivialModulus K) 1 hs v
    simp only [heckePrimeTerm, hv, one_mul] at hne ⊢
    rw [heckeValue_one_prime]
    by_cases hm : v.asIdeal ∣ 𝔪.fin
    · simp only [F, if_pos hm, zero_mul, sub_zero, inv_one]
      exact inv_mul_cancel₀ hne
    · simp only [F, if_neg hm, one_mul, mul_one]
  simp only [hlocal] at h
  exact (heckeL_eulerProduct_hasProd 𝔪 1 hs).unique h

end GaloisForLFunctions.HeckeLFunctions
