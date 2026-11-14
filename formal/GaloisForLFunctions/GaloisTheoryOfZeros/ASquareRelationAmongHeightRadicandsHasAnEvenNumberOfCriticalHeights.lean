import GaloisForLFunctions.GaloisTheoryOfZeros.TheReflectionRadicalsOfOneHeightCarryTheParityOfItsZeros

/-!
# A square relation among height radicands has an even number of critical heights

For a height `t` and a prime `p`, `A_{t,p} = ∏_{Im ρ = t} (p^ρ − p^{1−ρ})` is the product of the
reflection radicals of the zeros of ordinate `t`; its square, the product of their reflection
radicands, lies in the prime trace field `B`. Conjugation acts by
`c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`, and `|U_t|` is odd iff `½ + it` is a zero.

* **Parity of square relations** (`even_card_critical_of_isSquare`). If finitely many heights `T`
  and primes `p_t` give nonzero `A_{t,p_t}` whose squares multiply to a square in `B`, then an
  even number of the heights in `T` carry a critical zero.

So in `B^×/B^{×2}` the classes of the radicand products of the heights that carry a critical
zero satisfy no relation of odd length. This is a parity law for square classes read off from
the zeros of each height; at the level of `B` it is exactly the constraint that conjugation, and
equally any lift of the reflection, imposes, and it does not decide the lift.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local instance : IsGalois B E := ⟨⟩

/-- **Parity of square relations.** A square relation in `B` among the radicand products of
finitely many heights involves an even number of heights carrying a critical zero. -/
theorem even_card_critical_of_isSquare (T : Finset ℝ) (p : ℝ → Nat.Primes)
    (hne : ∀ t ∈ T, primeHeightReflectionProduct (p t) t ≠ 0) {b : E} (hb : (b : ℂ) ∈ B)
    (hsq : ∏ t ∈ T, primeHeightReflectionProduct (p t) t * primeHeightReflectionProduct (p t) t =
      b * b) :
    Even (T.filter fun t => Odd (primeUpperFibre t).card).card := by
  rw [Finset.prod_mul_distrib] at hsq
  set A := ∏ t ∈ T, primeHeightReflectionProduct (p t) t
  have hA0 : A ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  -- `A = ±b` lies in `B`, so conjugation fixes it
  have hAB : primeTraceConjugation A = A := by
    have h0 : (A - b) * (A + b) = 0 := by
      linear_combination hsq
    have hcb : primeTraceConjugation b = b :=
      (coe_mem_primeTraceField_iff_fixed b).1 hb primeTraceConjugation
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hcb]
    · rw [eq_neg_of_add_eq_zero_left h, map_neg, hcb]
  -- conjugation multiplies `A` by `(−1)^{Σ |U_t|}`
  have hcA : primeTraceConjugation A = (-1) ^ (∑ t ∈ T, (primeUpperFibre t).card) * A := by
    rw [map_prod, Finset.prod_congr rfl fun t _ =>
      primeTraceConjugation_heightReflectionProduct (p t) t, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  rw [hAB] at hcA
  have hpow : ((-1 : E)) ^ (∑ t ∈ T, (primeUpperFibre t).card) = 1 := by
    have h1 : ((-1 : E) ^ (∑ t ∈ T, (primeUpperFibre t).card) - 1) * A = 0 := by
      linear_combination -hcA
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hA0)
  have heven : Even (∑ t ∈ T, (primeUpperFibre t).card) := by
    rcases Nat.even_or_odd (∑ t ∈ T, (primeUpperFibre t).card) with h | h
    · exact h
    · rw [h.neg_one_pow] at hpow
      have h2 : (2 : ℂ) = 0 := by
        have := congrArg (fun x : E => (x : ℂ)) hpow
        push_cast at this
        linear_combination -this
      norm_num at h2
  -- the parity of a sum is the parity of the number of odd terms
  rw [Finset.even_sum_iff_even_card_odd] at heven
  exact heven

end GaloisForLFunctions.GaloisTheoryOfZeros
