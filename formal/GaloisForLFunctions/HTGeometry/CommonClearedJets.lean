import GaloisForLFunctions.HTGeometry.ClearedJets

/-!
# One denominator for all the jets

The rational-model transfer wants a *single* denominator for the whole family — the base coordinate
together with the jets.  Multiplying the individual denominators together supplies it, and the base
coordinate joins with the denominator itself as its numerator.

Assembling that with the cleared-jet recursion gives the analytic transfer for any cascade whose law
carries a denominator: algebraic independence of the jets in the rational model still excludes a
differential equation of the lower order.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Y : ℕ → ℂ → ℂ}

/-- **One denominator for the base coordinate and all the jets.** -/
theorem exists_ratModel_data (hY0 : Y 0 = id) {m : ℕ}
    {v' : Fin (m + 1) → CascadeField} {w' : ℂ → Fin (m + 1) → ℂ}
    (Ai Bi : Fin (m + 1) → MvPolynomial ℕ ℂ) (hBi : ∀ i, Bi i ≠ 0)
    (hmodel : ∀ i, algebraMap (MvPolynomial ℕ ℂ) CascadeField (Bi i) * v' i
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (Ai i))
    (hval : ∀ (i : Fin (m + 1)) (z : ℂ), evalAt Y z (Bi i) * w' z i = evalAt Y z (Ai i)) :
    ∃ (A : Fin (m + 2) → MvPolynomial ℕ ℂ) (B : MvPolynomial ℕ ℂ), B ≠ 0 ∧
      (∀ j, algebraMap (MvPolynomial ℕ ℂ) CascadeField B
          * (Fin.cons (fx 0) v' : Fin (m + 2) → CascadeField) j
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField (A j)) ∧
      (∀ (j : Fin (m + 2)) (z : ℂ),
        evalAt Y z B * (Fin.cons z (w' z) : Fin (m + 2) → ℂ) j = evalAt Y z (A j)) := by
  classical
  refine ⟨Fin.cons ((∏ i : Fin (m + 1), Bi i) * MvPolynomial.X 0)
      (fun i : Fin (m + 1) => Ai i * ∏ i' ∈ Finset.univ.erase i, Bi i'),
    ∏ i : Fin (m + 1), Bi i, Finset.prod_ne_zero_iff.mpr fun i _ => hBi i, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero, Fin.cons_zero, map_mul]
      rfl
    · rw [Fin.cons_succ, Fin.cons_succ, map_mul,
        ← Finset.mul_prod_erase Finset.univ Bi (Finset.mem_univ i), map_mul]
      linear_combination (algebraMap (MvPolynomial ℕ ℂ) CascadeField
        (∏ x ∈ Finset.univ.erase i, Bi x)) * hmodel i
  · intro j z
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.cons_zero, Fin.cons_zero, map_mul, evalAt_X, hY0]
      rfl
    · rw [Fin.cons_succ, Fin.cons_succ, map_mul,
        ← Finset.mul_prod_erase Finset.univ Bi (Finset.mem_univ i), map_mul]
      linear_combination (evalAt Y z (∏ x ∈ Finset.univ.erase i, Bi x)) * hval i z

/-- **The analytic transfer for a cascade whose law carries a denominator.** -/
theorem not_differentiallyAlgebraicOfOrder_of_clearedModel
    (hY : ∀ k, Differentiable ℂ (Y k)) (hY0 : Y 0 = id)
    {δ : Derivation ℂ CascadeField CascadeField}
    {δp : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)} {Dtot : MvPolynomial ℕ ℂ}
    (hDtot : Dtot ≠ 0) {N : ℕ} (hDmem : Dtot ∈ lowPoly N)
    (hgen : ∀ k, k ≤ N → δp (MvPolynomial.X k) ∈ lowPoly N)
    (hlawA : ∀ k, k ≤ N → ∀ z : ℂ,
      evalAt Y z Dtot * deriv (Y k) z = evalAt Y z (δp (MvPolynomial.X k)))
    (hlawM : ∀ k, k ≤ N →
      algebraMap (MvPolynomial ℕ ℂ) CascadeField Dtot * δ (fx k)
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField (δp (MvPolynomial.X k)))
    (hind : ∀ Q : MvPolynomial ℕ ℂ, Q ≠ 0 → ∃ z : ℂ, evalAt Y z Q ≠ 0)
    {m : ℕ}
    (hindep : AlgebraicIndependent ℂ
      (Fin.cons (fx 0)
        (fun i : Fin (m + 1) => ((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx N))
        : Fin (m + 2) → CascadeField)) :
    ¬ DifferentiallyAlgebraicOfOrder (Y N) m := by
  classical
  choose Aall Ball hB0 _ _ hmodelAll hvalAll using
    fun i : ℕ => exists_clearedJets (Y := Y) hY (δ := δ) (δp := δp) (Dtot := Dtot)
      hDtot (N := N) hDmem hgen hlawA hlawM i
  obtain ⟨A, B, hBne, hAmodel, hAval⟩ :=
    exists_ratModel_data (Y := Y) hY0
      (v' := fun i : Fin (m + 1) => ((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx N))
      (w' := fun z => fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) (Y N) z)
      (fun i => Aall (i : ℕ)) (fun i => Ball (i : ℕ)) (fun i => hB0 (i : ℕ))
      (fun i => hmodelAll (i : ℕ)) (fun i z => hvalAll (i : ℕ) z)
  exact not_differentiallyAlgebraicOfOrder_of_ratModel (Y := Y) (A := A) (B := B) hBne
    hAmodel hAval hind hindep

end GaloisForLFunctions.HTGeometry
