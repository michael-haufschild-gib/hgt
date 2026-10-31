import GaloisForLFunctions.RHTower.ZeroEstimateOrder

/-!
# Finite scalar jets detect arbitrary prime support

Unique factorization separates the logarithmic frequencies of a finite
prime-exponent auxiliary. Vandermonde inversion therefore detects every
nonzero auxiliary before its support cardinality, at every complex point.
-/

noncomputable section
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Scalar jets below support size detect every nonzero prime-exponent auxiliary. -/
theorem friableExponentDirichletExp_has_nonzero_jet
    {P : (Nat.Primes →₀ ℕ) →₀ ℂ} (hP : P ≠ 0) (s : ℂ) :
    ∃ k : ℕ, k < P.support.card ∧
      iteratedDeriv k (friableExponentDirichletExp P) s ≠ 0 := by
  classical
  let e := (Fintype.equivFin P.support).symm
  let μ := fun j => -(Real.log (primeProduct (e j) : ℝ) : ℂ)
  let c := fun j => P (e j)
  have hμ : Function.Injective μ := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply primeProduct_injective
    have hlog : Real.log (primeProduct (e i) : ℝ) =
        Real.log (primeProduct (e j) : ℝ) :=
      Complex.ofReal_injective (neg_injective hij)
    have hi : (0 : ℝ) < primeProduct (e i) := by exact_mod_cast primeProduct_pos (e i)
    have hj : (0 : ℝ) < primeProduct (e j) := by exact_mod_cast primeProduct_pos (e j)
    exact_mod_cast Real.log_injOn_pos hi hj hlog
  have hc : c ≠ 0 := by
    intro hc
    apply hP
    ext m
    change P m = 0
    by_cases hm : m ∈ P.support
    · have h := congrFun hc (e.symm ⟨m, hm⟩)
      change P (e (e.symm ⟨m, hm⟩)) = 0 at h
      simpa only [e.apply_symm_apply] using h
    · exact Finsupp.notMem_support_iff.mp hm
  have htrace : friableExponentDirichletExp P = exponentialSum μ c := by
    funext z
    unfold friableExponentDirichletExp exponentialSum
    rw [Finsupp.sum, ← Finset.sum_coe_sort P.support, ← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro j _
    simp only [μ, c, mul_neg]
  obtain ⟨k, hk⟩ := exponentialSum_has_nonzero_iteratedDeriv_lt_card hμ hc s
  refine ⟨k, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using k.isLt
  · rw [htrace]
    exact hk

/-- Vanishing of the initial scalar jet vector forces the entire auxiliary to vanish. -/
theorem friableExponentDirichletExp_initial_jets_zero_iff
    (P : (Nat.Primes →₀ ℕ) →₀ ℂ) (s : ℂ) :
    (∀ k < P.support.card, iteratedDeriv k (friableExponentDirichletExp P) s = 0) ↔
      P = 0 := by
  constructor
  · intro h
    by_contra hP
    obtain ⟨k, hk, hne⟩ := friableExponentDirichletExp_has_nonzero_jet hP s
    exact hne (h k hk)
  · rintro rfl k hk
    exfalso
    simpa only [Finsupp.support_zero, Finset.card_empty, Nat.not_lt_zero] using hk

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.friableExponentDirichletExp_has_nonzero_jet
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.friableExponentDirichletExp_initial_jets_zero_iff
