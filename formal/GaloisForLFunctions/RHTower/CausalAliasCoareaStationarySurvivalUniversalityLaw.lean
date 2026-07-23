import GaloisForLFunctions.RHTower.CausallyAnchoredFutureAliasRegrouping
import GaloisForLFunctions.RHTower.PhysicalCutoffConnectedCoareaSuccessor

/-!
# Causal alias/coarea stationary-survival universality

The Euler survival coefficient produced by causal future-frequency regrouping is exactly the
negative affine drift of the physical-cutoff coarea theory. Hence every future-remainder mode is
cutoff-stationary; in the even-gap sector it is nonzero and cannot be a bounded successor
coboundary.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The local future-remainder survival coefficient, expressed in physical-cutoff coarea
coordinates. -/
def causalFutureCoareaSurvival (c N r H : ℕ) (h : ℤ) : ℂ :=
  -physicalCutoffCoareaAffineDrift (c * r) H (N / r).primeFactors
    (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ))

/-- The coarea coefficient is exactly the local Euler survival product appearing in causal
future-alias regrouping. -/
theorem causalFutureCoareaSurvival_eq_product
    (c N r H : ℕ) (h : ℤ) :
    causalFutureCoareaSurvival c N r H h =
      ∏ p ∈ (N / r).primeFactors,
        (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ)) := by
  rw [causalFutureCoareaSurvival, physicalCutoffCoareaAffineDrift_eq_neg_survival]
  simp

/-- Causal future-alias regrouping rewritten entirely in physical-cutoff coarea coefficients. -/
theorem causallyAnchoredFutureAliasRegrouping_eq_coareaSurvival
    {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N) (hcN : c.Coprime N)
    (h : ℤ) (F : ℚ → ℂ) (hF : (Function.support F).Finite) (H : ℕ) :
    ∑ m ∈ N.divisors,
        ((ArithmeticFunction.moebius m : ℂ) / ((c * m : ℕ) : ℂ)) *
          ∑ᶠ (k : ℤ) (_ : k ≠ 0),
            F ((k : ℚ) / ((c * m : ℕ) : ℚ)) *
              quadraticCongruenceRootSumTotal (c * m) h k =
      ∑ r ∈ N.divisors,
          ((ArithmeticFunction.moebius r : ℂ) / ((c * r : ℕ) : ℂ)) *
            causalFutureCoareaSurvival c N r H h *
            ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
              F ((u : ℚ) / ((c * r : ℕ) : ℚ)) *
                quadraticCongruenceRootSumTotal (c * r) h u := by
  rw [causallyAnchoredFutureAliasRegrouping hc hN hcN h F hF]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [causalFutureCoareaSurvival_eq_product]

/-- In the even-gap sector every future-remainder coarea survival coefficient is stationary and
nonzero at every cutoff. -/
theorem causalFutureCoareaSurvival_stationary_and_ne_zero
    (c N r : ℕ) (h : ℤ) (heven : (2 : ℤ) ∣ h) :
    (∀ H : ℕ,
      causalFutureCoareaSurvival c N r (H + 1) h -
        causalFutureCoareaSurvival c N r H h = 0) ∧
      ∀ H : ℕ, causalFutureCoareaSurvival c N r H h ≠ 0 := by
  have hprime : ∀ p ∈ (N / r).primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  obtain ⟨hstationary, hne⟩ :=
    quadraticSurvivalRamp_stationary_and_ne_zero
      (c * r) (N / r).primeFactors hprime h heven
  constructor
  · intro H
    unfold causalFutureCoareaSurvival
    linear_combination -hstationary H
  · intro H
    simpa [causalFutureCoareaSurvival] using neg_ne_zero.mpr (hne H)

/-- A nonzero causal future-remainder survival coefficient admits no uniformly bounded successor
primitive on a cofinal aperture. -/
theorem causalFutureCoareaSurvival_no_bounded_successorPrimitive
    (c N r H : ℕ) (h : ℤ) (heven : (2 : ℤ) ∣ h)
    (Ψ : ℕ → ℂ) (H₀ : ℕ) (M : ℝ)
    (hbound : ∀ K, ‖Ψ K‖ ≤ M)
    (hstep : ∀ K, H₀ ≤ K → Ψ (K + 1) - Ψ K =
      -causalFutureCoareaSurvival c N r H h) : False := by
  exact no_bounded_primitive_of_ne_zero Ψ
    (causalFutureCoareaSurvival c N r H h)
    ((causalFutureCoareaSurvival_stationary_and_ne_zero c N r h heven).2 H)
    H₀ M hbound hstep

/-- **Causal alias/coarea stationary-survival universality law.** At every physical cutoff the
causal future-alias identity is carried by the same local coarea coefficients. For even gaps every
such coefficient is a nonzero stationary successor class and cannot be absorbed by a bounded
primitive. -/
theorem causalAlias_coareaStationarySurvivalUniversality
    {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N) (hcN : c.Coprime N)
    (h : ℤ) (heven : (2 : ℤ) ∣ h)
    (F : ℚ → ℂ) (hF : (Function.support F).Finite) :
    (∀ H : ℕ,
      ∑ m ∈ N.divisors,
          ((ArithmeticFunction.moebius m : ℂ) / ((c * m : ℕ) : ℂ)) *
            ∑ᶠ (k : ℤ) (_ : k ≠ 0),
              F ((k : ℚ) / ((c * m : ℕ) : ℚ)) *
                quadraticCongruenceRootSumTotal (c * m) h k =
        ∑ r ∈ N.divisors,
            ((ArithmeticFunction.moebius r : ℂ) / ((c * r : ℕ) : ℂ)) *
              causalFutureCoareaSurvival c N r H h *
              ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
                F ((u : ℚ) / ((c * r : ℕ) : ℚ)) *
                  quadraticCongruenceRootSumTotal (c * r) h u) ∧
      (∀ r ∈ N.divisors,
        (∀ H : ℕ,
          causalFutureCoareaSurvival c N r (H + 1) h -
            causalFutureCoareaSurvival c N r H h = 0) ∧
        (∀ H : ℕ, causalFutureCoareaSurvival c N r H h ≠ 0) ∧
        ∀ (H : ℕ) (Ψ : ℕ → ℂ) (H₀ : ℕ) (M : ℝ),
          (∀ K, ‖Ψ K‖ ≤ M) →
          (∀ K, H₀ ≤ K → Ψ (K + 1) - Ψ K =
            -causalFutureCoareaSurvival c N r H h) → False) := by
  constructor
  · exact fun H =>
      causallyAnchoredFutureAliasRegrouping_eq_coareaSurvival hc hN hcN h F hF H
  · intro r _hr
    obtain ⟨hstationary, hne⟩ :=
      causalFutureCoareaSurvival_stationary_and_ne_zero c N r h heven
    refine ⟨hstationary, hne, ?_⟩
    intro H Ψ H₀ M hbound hstep
    exact causalFutureCoareaSurvival_no_bounded_successorPrimitive
      c N r H h heven Ψ H₀ M hbound hstep

end

end RHTower
