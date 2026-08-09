import GaloisForLFunctions.HTGeometry.ClearedChainRule
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation

/-!
# The cleared jets of a cascade with a denominator-carrying law

Each analytic jet of the last state is a ratio of two polynomials in the states, and the *same* pair
represents the corresponding jet of the rational model.  The recursion is the quotient rule with the
denominator cleared once:

`A_(i+1) = (δ̃A_i)·B_i − A_i·(δ̃B_i)`,   `B_(i+1) = Dtot·B_i²`,

and both the model identity and the pointwise identity propagate through it by the same algebra.
That is exactly the data the rational-model transfer consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Y : ℕ → ℂ → ℂ}

/-- A derivation preserving the generators preserves the subalgebra. -/
theorem derivation_mem_lowPoly {δp : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)} {N : ℕ}
    (hgen : ∀ k, k ≤ N → δp (MvPolynomial.X k) ∈ lowPoly N)
    {P : MvPolynomial ℕ ℂ} (hP : P ∈ lowPoly N) : δp P ∈ lowPoly N := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hgen k hk
  | algebraMap c =>
      rw [δp.map_algebraMap]
      exact zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      exact add_mem (mul_mem hx ihy) (mul_mem hy ihx)

/-- **The cleared jets.**  Every analytic jet of the last state, and the corresponding jet of the
rational model, are represented by one numerator/denominator pair of polynomials in the states. -/
theorem exists_clearedJets (hY : ∀ k, Differentiable ℂ (Y k))
    {δ : Derivation ℂ CascadeField CascadeField}
    {δp : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)} {Dtot : MvPolynomial ℕ ℂ}
    (hDtot : Dtot ≠ 0) {N : ℕ} (hDmem : Dtot ∈ lowPoly N)
    (hgen : ∀ k, k ≤ N → δp (MvPolynomial.X k) ∈ lowPoly N)
    (hlawA : ∀ k, k ≤ N → ∀ z : ℂ,
      evalAt Y z Dtot * deriv (Y k) z = evalAt Y z (δp (MvPolynomial.X k)))
    (hlawM : ∀ k, k ≤ N →
      algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot * δ (fx k)
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp (MvPolynomial.X k)))
    (i : ℕ) :
    ∃ A B : MvPolynomial ℕ ℂ, B ≠ 0 ∧ A ∈ lowPoly N ∧ B ∈ lowPoly N ∧
      (algebraMap (MvPolynomial ℕ ℂ) CascadeField B
          * ((δ : CascadeField → CascadeField)^[i]) (fx N)
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField A) ∧
      ∀ z : ℂ, evalAt Y z B * iteratedDeriv i (Y N) z = evalAt Y z A := by
  induction i with
  | zero =>
      refine ⟨MvPolynomial.X N, 1, one_ne_zero, X_mem_lowPoly (le_refl N), one_mem _, ?_, ?_⟩
      · rw [map_one, one_mul, Function.iterate_zero_apply]
        rfl
      · intro z
        rw [map_one, one_mul, iteratedDeriv_zero, evalAt_X]
  | succ i ih =>
      obtain ⟨A, B, hB0, hAmem, hBmem, hmodel, hval⟩ := ih
      have hBne : algebraMap (MvPolynomial ℕ ℂ) CascadeField B ≠ 0 := by
        simpa using (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField).ne hB0
      refine ⟨δp A * B - A * δp B, Dtot * B ^ 2, mul_ne_zero hDtot (pow_ne_zero 2 hB0),
        sub_mem (mul_mem (derivation_mem_lowPoly hgen hAmem) hBmem)
          (mul_mem hAmem (derivation_mem_lowPoly hgen hBmem)),
        mul_mem hDmem (pow_mem hBmem 2), ?_, ?_⟩
      · -- the model identity
        have hstep : δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField B)
              * ((δ : CascadeField → CascadeField)^[i]) (fx N)
            + algebraMap (MvPolynomial ℕ ℂ) CascadeField B
              * ((δ : CascadeField → CascadeField)^[i + 1]) (fx N)
            = δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField A) := by
          have h : δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField B
              * ((δ : CascadeField → CascadeField)^[i]) (fx N))
              = δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField A) := by rw [hmodel]
          rw [Derivation.leibniz] at h
          simp only [smul_eq_mul] at h
          rw [Function.iterate_succ_apply']
          linear_combination h
        have hA' := algebraMap_cleared (δ := δ) (δp := δp) (Dtot := Dtot) (N := N) hlawM hAmem
        have hB' := algebraMap_cleared (δ := δ) (δp := δp) (Dtot := Dtot) (N := N) hlawM hBmem
        rw [map_sub, map_mul, map_mul, map_mul, map_pow]
        linear_combination (algebraMap (MvPolynomial ℕ ℂ) CascadeField B) * hA'
          - (algebraMap (MvPolynomial ℕ ℂ) CascadeField A) * hB'
          + (algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot
              * algebraMap (MvPolynomial ℕ ℂ) CascadeField B) * hstep
          - (algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot
              * δ (algebraMap (MvPolynomial ℕ ℂ) CascadeField B)) * hmodel
      · -- the pointwise identity
        intro z
        have hdiffB : Differentiable ℂ (fun w => evalAt Y w B) := differentiable_evalAt hY B
        have hdiffA : Differentiable ℂ (fun w => evalAt Y w A) := differentiable_evalAt hY A
        have hdiffJ : Differentiable ℂ (iteratedDeriv i (Y N)) :=
          differentiable_iteratedDeriv_of_entire (hY N) i
        have hfun : (fun w => evalAt Y w B * iteratedDeriv i (Y N) w)
            = fun w => evalAt Y w A := by
          funext w
          exact hval w
        have hd1 : HasDerivAt (fun w => evalAt Y w B * iteratedDeriv i (Y N) w)
            (deriv (fun w => evalAt Y w B) z * iteratedDeriv i (Y N) z
              + evalAt Y z B * iteratedDeriv (i + 1) (Y N) z) z := by
          have h1 : HasDerivAt (fun w => evalAt Y w B) (deriv (fun w => evalAt Y w B) z) z :=
            (hdiffB z).hasDerivAt
          have h2 : HasDerivAt (iteratedDeriv i (Y N))
              (iteratedDeriv (i + 1) (Y N) z) z := by
            rw [iteratedDeriv_succ]
            exact (hdiffJ z).hasDerivAt
          exact h1.mul h2
        have hstep : deriv (fun w => evalAt Y w B) z * iteratedDeriv i (Y N) z
            + evalAt Y z B * iteratedDeriv (i + 1) (Y N) z
            = deriv (fun w => evalAt Y w A) z := by
          rw [← hd1.deriv, hfun]
        have hA' := deriv_evalAt_cleared hY (δp := δp) (Dtot := Dtot) (N := N) hlawA hAmem z
        have hB' := deriv_evalAt_cleared hY (δp := δp) (Dtot := Dtot) (N := N) hlawA hBmem z
        rw [map_sub, map_mul, map_mul, map_mul, map_pow]
        linear_combination (evalAt Y z B) * hA' - (evalAt Y z A) * hB'
          + (evalAt Y z Dtot * evalAt Y z B) * hstep
          - (evalAt Y z Dtot * deriv (fun w => evalAt Y w B) z) * (hval z)

end GaloisForLFunctions.HTGeometry
