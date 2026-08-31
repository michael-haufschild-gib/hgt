import GaloisForLFunctions.HTGeometry.ChainSimplexBase
import GaloisForLFunctions.HTGeometry.RegularSequenceBridge

/-!
# Variables outside a coordinate ideal are regular

```text
X_notMem_span_X_image        v ∉ S ⟹ X v ∉ span (X '' S)
isRegularOn_X_span_X_image   ** hence X v is a nonzerodivisor modulo span (X '' S) **
```

Both come straight from `mem_ideal_span_X_image` and the primality of coordinate ideals
(`isPrime_span_X_image`): a product landing in a prime with one factor outside forces the other
inside.

This is the step that turns the simplex base case of the Cohen–Macaulay recursion into an actual
regular sequence: modulo the coordinate ideal of the complement, the available variables are
successively regular, because at each stage the ideal generated so far is again a coordinate ideal
not containing the next variable.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [DecidableEq σ] {K : Type u} [Field K]

theorem X_notMem_span_X_image {S : Set σ} {v : σ} (hv : v ∉ S) :
    (X v : MvPolynomial σ K) ∉ Ideal.span (X '' S) := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro hcon
  have hsupp : (Finsupp.single v 1 : σ →₀ ℕ) ∈ (X v : MvPolynomial σ K).support := by
    rw [MvPolynomial.support_X]
    simp
  obtain ⟨i, hiS, hne⟩ := hcon _ hsupp
  have : i = v := by
    by_contra hcon2
    rw [Finsupp.single_apply, if_neg (fun h => hcon2 h.symm)] at hne
    exact hne rfl
  exact hv (this ▸ hiS)

/-- **A variable outside a coordinate ideal is a nonzerodivisor modulo it.** -/
theorem isRegularOn_X_span_X_image {S : Set σ} [DecidablePred (· ∈ S)] {v : σ} (hv : v ∉ S) :
    IsRegularOn (Ideal.span (X '' S)) (X v : MvPolynomial σ K) := by
  classical
  refine isRegularOn_of_notMem_inf_primes (s := ({0} : Finset ℕ))
    (P := fun _ => Ideal.span (X '' S)) (fun _ _ => isPrime_span_X_image S) ?_ ?_
  · simp
  · intro i _
    exact X_notMem_span_X_image hv

end GaloisForLFunctions.HTGeometry
