import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentArithmetic
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentTriangularMultiplication

/-!
# Uniform integrality of finite unipotent coefficient prefixes

Finitely many actual adeles share a cofinite set of integral places.
Completing a finite free-coefficient prefix by zeros therefore gives a
uniformly integral unipotent, including every rational prefix.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
noncomputable section

private theorem eventually_integral_prefix (x : ℕ → Adeles) (N : ℕ) :
    ∀ᶠ v : FinitePlace in cofinite, ∀ n < N, x n ∈ adeleIntegralAt v := by
  induction N with
  | zero => exact Eventually.of_forall fun _ n hn => (Nat.not_lt_zero n hn).elim
  | succ N ih =>
    filter_upwards [ih, (x N).1.property] with v hv hN
    intro n hn
    by_cases h : n < N
    · exact hv n h
    · have he : n = N := by omega
      subst n
      exact hN

private theorem uniform_of_stream_eventually_zero (g : unipotentCoefficientGroup Adeles)
    (N : ℕ) (hg : ∀ n, N ≤ n → unipotentCoefficientStreamEquiv Adeles g n = 0) :
    g ∈ uniformlyIntegralUnipotent := by
  apply (mem_uniformlyIntegralUnipotent g).mpr
  filter_upwards [eventually_integral_prefix (unipotentCoefficientStreamEquiv Adeles g) N] with v hv
  intro n
  by_cases hn : n < N
  · exact hv n hn
  · rw [hg n (Nat.le_of_not_gt hn)]
    exact (adeleIntegralAt v).zero_mem

/-- Every finite adelic prefix has one common set of integral places. -/
theorem unipotentPrefixCompletion_mem_uniformlyIntegral (N : ℕ) (x : Fin N → Adeles) :
    unipotentPrefixCompletion x ∈ uniformlyIntegralUnipotent := by
  apply uniform_of_stream_eventually_zero _ N
  intro n hn
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply, dif_neg (not_lt.mpr hn)]

/-- Every finite rational prefix lies in the actual restricted rational unipotent group. -/
theorem unipotentPrefixCompletion_mem_uniformlyIntegralRational (N : ℕ) (x : Fin N → K) :
    unipotentPrefixCompletion x ∈ uniformlyIntegralRationalUnipotent := by
  change unipotentCoefficientMap adeleEmbedding (unipotentPrefixCompletion x) ∈ uniformlyIntegralUnipotent
  rw [unipotentPrefixCompletion_map]
  apply uniform_of_stream_eventually_zero _ N
  intro n hn
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply, dif_neg (not_lt.mpr hn)]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentPrefixCompletion_mem_uniformlyIntegral

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentPrefixCompletion_mem_uniformlyIntegralRational
