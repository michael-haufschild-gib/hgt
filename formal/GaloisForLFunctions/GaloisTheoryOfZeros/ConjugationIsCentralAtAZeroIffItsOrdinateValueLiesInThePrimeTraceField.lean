import GaloisForLFunctions.GaloisTheoryOfZeros.TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField

/-!
# Conjugation is central at a zero iff its ordinate value lies in the prime trace field

`E` is the field of the prime values `p^ρ` of the zeros, `B` the prime trace field,
`G = Gal(E/B)`, `Δ` the integer span of the zeros. An element of `E` lies in `B` iff `G` fixes
it.

* **Fixed exponents** (`primeTraceExponentHom_fixed_iff`). `δ ∈ Δ` is fixed by `G` iff
  `2^δ ∈ B` and `3^δ ∈ B`.

The *ordinate* of a zero `ρ = β + iγ` is `ρ − ρ̄ = 2iγ ∈ Δ`. Its prime values `p^{2iγ}` have
modulus one; the *ordinate value* is the real number `p^{2iγ} + p^{−2iγ} = 2 cos(2γ log p)`.

* **Ordinate criterion** (`primeOrdinateValue_mem_iff_conj`). For one prime `p`:
  `2 cos(2γ log p) ∈ B` iff `σ(ρ̄)` is the conjugate of `σ(ρ)` for every `σ ∈ G`.
* **Centrality of conjugation** (`primeTraceConjugation_central_iff`). Conjugation is central
  in `G` iff the ordinate value of every zero lies in `B`.
* **The weight implies the ordinate** (`primeOrdinateValue_mem_of_weight_mem`). If
  `p^{2β} ∈ B`, then `2 cos(2γ log q) ∈ B` for every prime `q`. This holds at every zero with
  rational real part, in particular on the critical line.

Proof. An automorphism that fixes `x + x⁻¹`, `x = p^{2iγ}`, sends `x` to `x` or to `x⁻¹`, of
modulus one, so `σρ` and `σρ̄` have one real part. They are distinct zeros with ordinates `±γ`,
hence conjugate. Conversely `σ(ρ − ρ̄) = σρ − conj(σρ) = ±2iγ`.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local notation "Δ" => rawZeroRelationGroup
local instance : IsGalois B E := ⟨⟩

/-! ## The fixed field and the fixed exponents -/

/-- An element of `E` lies in `B` iff every arithmetic automorphism fixes it. -/
theorem coe_mem_primeTraceField_iff_fixed (x : E) : (x : ℂ) ∈ B ↔ ∀ σ : G, σ x = x := by
  constructor
  · intro h σ
    have hb : algebraMap B E ⟨(x : ℂ), h⟩ = x := Subtype.ext rfl
    calc σ x = σ (algebraMap B E ⟨(x : ℂ), h⟩) := by rw [hb]
      _ = algebraMap B E ⟨(x : ℂ), h⟩ := σ.commutes _
      _ = x := hb
  · intro hf
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hf
    rw [← congrArg (fun v : E => (v : ℂ)) hb]
    exact b.property

/-- The prime values at `2` and `3` determine an element of `Δ`. -/
theorem primeTraceExponentValue_two_three_ext {z w : Δ}
    (h2 : primeTraceExponentValue ⟨2, Nat.prime_two⟩ z =
      primeTraceExponentValue ⟨2, Nat.prime_two⟩ w)
    (h3 : primeTraceExponentValue ⟨3, Nat.prime_three⟩ z =
      primeTraceExponentValue ⟨3, Nat.prime_three⟩ w) : z = w := by
  apply Subtype.ext
  apply two_prime_exponential_injective Nat.prime_two Nat.prime_three (by decide)
  have e2 : (primeTraceExponentValue ⟨2, Nat.prime_two⟩ z : ℂ) =
      (primeTraceExponentValue ⟨2, Nat.prime_two⟩ w : ℂ) := congrArg (fun x : E => (x : ℂ)) h2
  have e3 : (primeTraceExponentValue ⟨3, Nat.prime_three⟩ z : ℂ) =
      (primeTraceExponentValue ⟨3, Nat.prime_three⟩ w : ℂ) := congrArg (fun x : E => (x : ℂ)) h3
  exact Prod.ext e2 e3

/-- The prime values of a fixed element of `Δ` lie in `B`. -/
theorem primeTraceExponentValue_mem_of_fixed {z : Δ}
    (h : ∀ σ : G, primeTraceExponentHom σ z = z) (p : Nat.Primes) :
    (primeTraceExponentValue p z : ℂ) ∈ B :=
  (coe_mem_primeTraceField_iff_fixed _).2 fun σ => by
    rw [← primeTraceExponentHom_value, h σ]

/-- **Fixed exponents.** An element of the integer span of the zeros is fixed by every
arithmetic automorphism iff its prime values at `2` and `3` lie in `B`. -/
theorem primeTraceExponentHom_fixed_iff (z : Δ) :
    (∀ σ : G, primeTraceExponentHom σ z = z) ↔
      (primeTraceExponentValue ⟨2, Nat.prime_two⟩ z : ℂ) ∈ B ∧
        (primeTraceExponentValue ⟨3, Nat.prime_three⟩ z : ℂ) ∈ B := by
  constructor
  · intro h
    exact ⟨primeTraceExponentValue_mem_of_fixed h _, primeTraceExponentValue_mem_of_fixed h _⟩
  · rintro ⟨h2, h3⟩ σ
    exact primeTraceExponentValue_two_three_ext
      ((primeTraceExponentHom_value σ _ z).trans ((coe_mem_primeTraceField_iff_fixed _).1 h2 σ))
      ((primeTraceExponentHom_value σ _ z).trans ((coe_mem_primeTraceField_iff_fixed _).1 h3 σ))

theorem primeTraceExponentValue_neg_coe (p : Nat.Primes) (z : Δ) :
    (primeTraceExponentValue p (-z) : ℂ) = (primeTraceExponentValue p z : ℂ)⁻¹ := by
  change Complex.exp ((Real.log (p : ℕ) : ℂ) * (-(z : ℂ))) =
    (Complex.exp ((Real.log (p : ℕ) : ℂ) * (z : ℂ)))⁻¹
  rw [mul_neg, Complex.exp_neg]

theorem norm_primeTraceExponentValue (p : Nat.Primes) (z : Δ) :
    ‖(primeTraceExponentValue p z : ℂ)‖ =
      Real.exp (Real.log ((p : ℕ) : ℝ) * ((z : Δ) : ℂ).re) := by
  rw [primeTraceExponentValue_coe, Complex.norm_exp, Complex.re_ofReal_mul]

/-! ## The ordinate of a zero -/

/-- The ordinate `ρ − ρ̄ = 2i Im ρ` of a zero in the integer span of the zeros. -/
def primeTraceOrdinate (ρ : XiDivisorSupport) : Δ :=
  primeTraceSupportRoot ρ - primeTraceSupportRoot (xiZeroConjEquiv ρ)

theorem primeTraceOrdinate_coe (ρ : XiDivisorSupport) :
    ((primeTraceOrdinate ρ : Δ) : ℂ) = ((2 * (ρ : ℂ).im : ℝ) : ℂ) * Complex.I :=
  Complex.sub_conj (ρ : ℂ)

/-- The ordinate value `p^{2iγ} + p^{−2iγ}` of a zero `ρ = β + iγ`. -/
def primeOrdinateValue (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeTraceExponentValue p (primeTraceOrdinate ρ) +
    primeTraceExponentValue p (-primeTraceOrdinate ρ)

/-- The ordinate value is the real number `2 cos(2γ log p)`. -/
theorem primeOrdinateValue_coe (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeOrdinateValue p ρ : ℂ) =
      ((2 * Real.cos (2 * (ρ : ℂ).im * Real.log ((p : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have h1 : (primeOrdinateValue p ρ : ℂ) =
      Complex.exp ((Real.log (p : ℕ) : ℂ) * ((ρ : ℂ) - starRingEnd ℂ (ρ : ℂ))) +
        Complex.exp ((Real.log (p : ℕ) : ℂ) * (-((ρ : ℂ) - starRingEnd ℂ (ρ : ℂ)))) := rfl
  have h2 : ((2 * Real.cos (2 * (ρ : ℂ).im * Real.log ((p : ℕ) : ℝ)) : ℝ) : ℂ) =
      Complex.exp (((2 * (ρ : ℂ).im * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-((2 * (ρ : ℂ).im * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.two_cos, Complex.ofReal_mul 2, Complex.ofReal_cos, Complex.ofReal_ofNat]
  rw [h1, Complex.sub_conj, h2]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The action of an automorphism on the ordinate of a zero. -/
theorem primeTraceExponentHom_ordinate (σ : G) (ρ : XiDivisorSupport) :
    primeTraceExponentHom σ (primeTraceOrdinate ρ) =
      primeTraceSupportRoot (primeTraceZeroMap σ ρ) -
        primeTraceSupportRoot (primeTraceZeroMap σ (xiZeroConjEquiv ρ)) := by
  rw [primeTraceOrdinate, map_sub, primeTraceExponentHom_root, primeTraceExponentHom_root]

/-! ## From the ordinate value to conjugate images -/

/-- An automorphism that fixes the ordinate value of `ρ` carries `ρ` and `ρ̄` to zeros of one
real part: it sends `x = p^{2iγ}` to `x` or to `x⁻¹`, of modulus one. -/
theorem primeTraceZeroMap_re_conj_of_fixed (p : Nat.Primes) (ρ : XiDivisorSupport) (σ : G)
    (hfix : σ (primeOrdinateValue p ρ) = primeOrdinateValue p ρ) :
    (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = (primeTraceZeroMap σ ρ : ℂ).re := by
  have hval : primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) +
      primeTraceExponentValue p (primeTraceExponentHom σ (-primeTraceOrdinate ρ)) =
      primeOrdinateValue p ρ := by
    rw [primeTraceExponentHom_value, primeTraceExponentHom_value, ← map_add]
    exact hfix
  have hC := congrArg (fun x : E => (x : ℂ)) hval
  change (primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ) +
      (primeTraceExponentValue p (primeTraceExponentHom σ (-primeTraceOrdinate ρ)) : ℂ) =
      (primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ) +
        (primeTraceExponentValue p (-primeTraceOrdinate ρ) : ℂ) at hC
  rw [map_neg, primeTraceExponentValue_neg_coe, primeTraceExponentValue_neg_coe] at hC
  have hX0 : (primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ) ≠ 0 := by
    rw [primeTraceExponentValue_coe]
    exact Complex.exp_ne_zero _
  have hY0 : (primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ)
      ≠ 0 := by
    rw [primeTraceExponentValue_coe]
    exact Complex.exp_ne_zero _
  have hX1 : ‖(primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ)‖ = 1 := by
    rw [norm_primeTraceExponentValue, primeTraceOrdinate_coe, Complex.re_ofReal_mul,
      Complex.I_re, mul_zero, mul_zero, Real.exp_zero]
  -- `(y − x)(xy − 1) = 0`
  have hfac : ((primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ) -
      (primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ)) *
      ((primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ) *
        (primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ) - 1)
      = 0 := by
    linear_combination
      (primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ) *
        (primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ) * hC -
      (primeTraceExponentValue p (primeTraceOrdinate ρ) : ℂ) * mul_inv_cancel₀ hY0 +
      (primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ) *
        mul_inv_cancel₀ hX0
  have hY1 : ‖(primeTraceExponentValue p (primeTraceExponentHom σ (primeTraceOrdinate ρ)) : ℂ)‖
      = 1 := by
    rcases mul_eq_zero.1 hfac with h | h
    · rw [sub_eq_zero.1 h, hX1]
    · have hn := congrArg norm (sub_eq_zero.1 h)
      rwa [norm_mul, hX1, one_mul, norm_one] at hn
  rw [norm_primeTraceExponentValue, Real.exp_eq_one_iff] at hY1
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hre := (mul_eq_zero.1 hY1).resolve_left hlog.ne'
  rw [primeTraceExponentHom_ordinate] at hre
  change ((primeTraceZeroMap σ ρ : ℂ) - (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ)).re = 0
    at hre
  rw [Complex.sub_re] at hre
  linarith only [hre]

/-- Two images of `ρ` and `ρ̄` with one real part are conjugate: they are distinct zeros with
ordinates `± Im ρ`. -/
theorem primeTraceZeroMap_conj_of_re (σ : G) (ρ : XiDivisorSupport)
    (hre : (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).re = (primeTraceZeroMap σ ρ : ℂ).re) :
    primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ) := by
  have hia := primeTraceZeroMap_height σ ρ
  have hib : |(primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).im| = |(ρ : ℂ).im| := by
    rw [primeTraceZeroMap_height]
    change |(starRingEnd ℂ (ρ : ℂ)).im| = _
    rw [Complex.conj_im, abs_neg]
  have hne : (primeTraceZeroMap σ ρ : ℂ).im ≠
      (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ).im := by
    intro him
    have heq : primeTraceZeroMap σ ρ = primeTraceZeroMap σ (xiZeroConjEquiv ρ) :=
      Subtype.ext (Complex.ext hre.symm him)
    have him' := congrArg (fun z : XiDivisorSupport => (z : ℂ).im)
      ((primeTraceZeroPermutation σ).injective heq)
    change (ρ : ℂ).im = (starRingEnd ℂ (ρ : ℂ)).im at him'
    rw [Complex.conj_im] at him'
    exact xi_divisor_support_im_ne_zero ρ (by linarith only [him'])
  apply Subtype.ext
  change (primeTraceZeroMap σ (xiZeroConjEquiv ρ) : ℂ) =
    starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ)
  apply Complex.ext
  · rw [Complex.conj_re]
    exact hre
  · rw [Complex.conj_im]
    rcases abs_eq_abs.1 hia with h1 | h1 <;> rcases abs_eq_abs.1 hib with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, neg_neg]
    · exact absurd (h1.trans h2.symm) hne

/-! ## The criterion -/

/-- **The ordinate criterion.** For one prime `p`: the ordinate value `2 cos(2γ log p)` of a zero
`ρ = β + iγ` lies in `B` iff every arithmetic automorphism carries `ρ̄` to the conjugate of the
image of `ρ`. -/
theorem primeOrdinateValue_mem_iff_conj (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeOrdinateValue p ρ : ℂ) ∈ B ↔ ∀ σ : G,
      primeTraceZeroMap σ (xiZeroConjEquiv ρ) = xiZeroConjEquiv (primeTraceZeroMap σ ρ) := by
  constructor
  · intro h σ
    exact primeTraceZeroMap_conj_of_re σ ρ (primeTraceZeroMap_re_conj_of_fixed p ρ σ
      ((coe_mem_primeTraceField_iff_fixed _).1 h σ))
  · intro h
    refine (coe_mem_primeTraceField_iff_fixed _).2 fun σ => ?_
    -- `σ(ρ − ρ̄) = ±(ρ − ρ̄)`
    have hord : primeTraceExponentHom σ (primeTraceOrdinate ρ) = primeTraceOrdinate ρ ∨
        primeTraceExponentHom σ (primeTraceOrdinate ρ) = -primeTraceOrdinate ρ := by
      rw [primeTraceExponentHom_ordinate, h σ]
      rcases abs_eq_abs.1 (primeTraceZeroMap_height σ ρ) with hi | hi
      · left
        apply Subtype.ext
        change (primeTraceZeroMap σ ρ : ℂ) - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ) =
          (ρ : ℂ) - starRingEnd ℂ (ρ : ℂ)
        rw [Complex.sub_conj, Complex.sub_conj, hi]
      · right
        apply Subtype.ext
        change (primeTraceZeroMap σ ρ : ℂ) - starRingEnd ℂ (primeTraceZeroMap σ ρ : ℂ) =
          -((ρ : ℂ) - starRingEnd ℂ (ρ : ℂ))
        rw [Complex.sub_conj, Complex.sub_conj, hi]
        push_cast
        ring
    rw [primeOrdinateValue, map_add, ← primeTraceExponentHom_value,
      ← primeTraceExponentHom_value, map_neg]
    rcases hord with h1 | h1
    · rw [h1]
    · rw [h1, neg_neg, add_comm]

/-- Membership of the ordinate value does not depend on the prime. -/
theorem primeOrdinateValue_mem_iff_mem (p q : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeOrdinateValue p ρ : ℂ) ∈ B ↔ (primeOrdinateValue q ρ : ℂ) ∈ B :=
  (primeOrdinateValue_mem_iff_conj p ρ).trans (primeOrdinateValue_mem_iff_conj q ρ).symm

/-- **Centrality of conjugation.** For one prime `p`: conjugation is central in the arithmetic
group iff the ordinate value of every zero lies in `B`. -/
theorem primeTraceConjugation_central_iff (p : Nat.Primes) :
    (∀ σ : G, primeTraceConjugation * σ = σ * primeTraceConjugation) ↔
      ∀ ρ : XiDivisorSupport, (primeOrdinateValue p ρ : ℂ) ∈ B := by
  constructor
  · intro h ρ
    refine (primeOrdinateValue_mem_iff_conj p ρ).2 fun σ => ?_
    have hσ := congrArg (fun τ : G => primeTraceZeroMap τ ρ) (h σ)
    change primeTraceZeroMap (primeTraceConjugation * σ) ρ =
      primeTraceZeroMap (σ * primeTraceConjugation) ρ at hσ
    rw [primeTraceZeroMap_mul, primeTraceZeroMap_mul, primeTraceZeroMap_conjugation,
      primeTraceZeroMap_conjugation] at hσ
    exact hσ.symm
  · intro h σ
    apply primeTraceGaloisAction_injective
    apply Equiv.ext
    intro ρ
    change primeTraceZeroMap (primeTraceConjugation * σ) ρ =
      primeTraceZeroMap (σ * primeTraceConjugation) ρ
    rw [primeTraceZeroMap_mul, primeTraceZeroMap_mul, primeTraceZeroMap_conjugation,
      primeTraceZeroMap_conjugation]
    exact ((primeOrdinateValue_mem_iff_conj p ρ).1 (h ρ) σ).symm

/-! ## The weight implies the ordinate -/

/-- **The weight implies the ordinate.** If `p^{2 Re ρ} ∈ B` for one prime `p`, then the ordinate
value of `ρ` lies in `B` at every prime. -/
theorem primeOrdinateValue_mem_of_weight_mem (p q : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (primeWeightValue p ρ : ℂ) ∈ B) : (primeOrdinateValue q ρ : ℂ) ∈ B := by
  refine (primeOrdinateValue_mem_iff_conj q ρ).2 fun σ => ?_
  have h1 := (primeWeightValue_mem_iff_re p ρ).1 h σ
  have h2 := (primeWeightValue_mem_iff_re p ρ).1 h (σ * primeTraceConjugation)
  rw [primeTraceZeroMap_mul, primeTraceZeroMap_conjugation] at h2
  exact primeTraceZeroMap_conj_of_re σ ρ (h2.trans h1.symm)

/-- At a zero with rational real part the ordinate value lies in `B`. -/
theorem primeOrdinateValue_mem_of_rational (q : Nat.Primes) (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re = (r : ℝ)) : (primeOrdinateValue q ρ : ℂ) ∈ B :=
  primeOrdinateValue_mem_of_weight_mem q q ρ (primeWeightValue_mem_of_rational q ρ hr)

/-- **Critical zeros.** For every zero `½ + iγ` on the critical line and every prime `q`, the
number `2 cos(2γ log q)` lies in the prime trace field. -/
theorem primeOrdinateValue_mem_of_critical (q : Nat.Primes) (ρ : XiDivisorSupport)
    (h : (ρ : ℂ).re = 1 / 2) : (primeOrdinateValue q ρ : ℂ) ∈ B :=
  primeOrdinateValue_mem_of_rational q ρ ⟨1 / 2, by rw [h]; norm_num⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
