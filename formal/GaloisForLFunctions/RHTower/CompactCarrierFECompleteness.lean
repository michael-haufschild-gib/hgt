import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection

/-!
# Functional-equation-odd compact-carrier completeness

An anti-invariant dual projection transfers the unpaired actual Euler-tangent
completeness theorem to paired functional-equation tangents on a symmetric
compact carrier.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The compact functional-equation paired actual Euler tangent. -/
def compactPrimeEulerUnitFETangent
    (s : C(K, ℂ)) (τ : C(K, K)) (p : ℕ) : C(K, ℂ) :=
  compactPrimeEulerUnitTangent s p -
    (compactPrimeEulerUnitTangent s p).comp τ

@[simp]
theorem compactPrimeEulerUnitFETangent_apply
    (s : C(K, ℂ)) (τ : C(K, K)) (p : ℕ) (k : K) :
    compactPrimeEulerUnitFETangent s τ p k =
      compactPrimeEulerUnitTangent s p k -
        compactPrimeEulerUnitTangent s p (τ k) := rfl

/-- Every anti-invariant coordinate monomial lies in the closed span of the
cofinite paired actual Euler tangents. -/
theorem odd_coordinate_pow_mem_closedSpan_primeEulerFETangents
    (s : C(K, ℂ)) (τ : C(K, K)) (δ M R₀ : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (N : ℕ) :
    s ^ N - (s ^ N).comp τ ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} =>
          compactPrimeEulerUnitFETangent s τ (p : Nat.Primes))).topologicalClosure := by
  let v : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} → C(K, ℂ) :=
    fun p => compactPrimeEulerUnitFETangent s τ (p : Nat.Primes)
  apply mem_topologicalClosure_span_of_forall_dual v
    (s ^ N - (s ^ N).comp τ)
  intro L hLv
  let P : C(K, ℂ) →L[ℂ] C(K, ℂ) :=
    ContinuousLinearMap.id ℂ C(K, ℂ) - ContinuousMap.compCLM ℂ ℂ τ
  let Lodd : C(K, ℂ) →L[ℂ] ℂ := L.comp P
  have hann : ∀ p : Nat.Primes, R₀ + 1 < Real.log (p : ℝ) →
      Lodd (compactPrimeEulerUnitTangent s (p : ℕ)) = 0 := by
    intro p hp
    have hv := hLv ⟨p, hp⟩
    simpa [v, Lodd, P, compactPrimeEulerUnitFETangent] using hv
  have hF := compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    Lodd s δ M R₀ hδ hM hR₀ hre him hann
  have hmono := map_coordinate_pow_eq_zero_of_fourierBorel_zero Lodd s hF N
  simpa [Lodd, P] using hmono

/-- If the carrier involution realizes `s ↦ 1-s`, the preceding theorem has
the literal functional-equation-odd polynomial form. -/
theorem fe_odd_coordinate_pow_mem_closedSpan
    (s : C(K, ℂ)) (τ : C(K, K))
    (hreflect : ∀ k : K, s (τ k) = 1 - s k)
    (δ M R₀ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (N : ℕ) :
    s ^ N - (1 - s) ^ N ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} =>
          compactPrimeEulerUnitFETangent s τ (p : Nat.Primes))).topologicalClosure := by
  have h := odd_coordinate_pow_mem_closedSpan_primeEulerFETangents
    s τ δ M R₀ hδ hM hR₀ hre him N
  convert h using 1
  ext k
  simp [hreflect]

/-- Evaluation of a scalar polynomial in a compact carrier coordinate. -/
def compactPolynomialEval (s : C(K, ℂ)) (P : Polynomial ℂ) : C(K, ℂ) :=
  ∑ n ∈ P.support, P.coeff n • s ^ n

@[simp]
theorem compactPolynomialEval_apply
    (s : C(K, ℂ)) (P : Polynomial ℂ) (k : K) :
    compactPolynomialEval s P k = P.eval (s k) := by
  rw [compactPolynomialEval]
  change (ContinuousMap.evalCLM ℂ k)
    (∑ n ∈ P.support, P.coeff n • s ^ n) = P.eval (s k)
  rw [map_sum]
  simp only [map_smul, ContinuousMap.evalCLM_apply, ContinuousMap.pow_apply,
    smul_eq_mul]
  exact Polynomial.eval_eq_sum.symm

/-- Every FE-oddified scalar polynomial belongs to the paired Euler-tangent
closed span. -/
theorem fe_odd_polynomial_mem_closedSpan
    (s : C(K, ℂ)) (τ : C(K, K))
    (hreflect : ∀ k : K, s (τ k) = 1 - s k)
    (δ M R₀ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (hR₀ : 0 < R₀)
    (hre : ∀ k : K, δ ≤ (s k).re)
    (him : ∀ k : K, |(s k).im| ≤ M)
    (P : Polynomial ℂ) :
    compactPolynomialEval s P - compactPolynomialEval (1 - s) P ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // R₀ + 1 < Real.log (p : ℝ)} =>
          compactPrimeEulerUnitFETangent s τ (p : Nat.Primes))).topologicalClosure := by
  rw [compactPolynomialEval, compactPolynomialEval]
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro n hn
  rw [← smul_sub]
  exact Submodule.smul_mem _ _
    (fe_odd_coordinate_pow_mem_closedSpan s τ hreflect δ M R₀
      hδ hM hR₀ hre him n)

end RHTower
