import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAncestralConservation
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFiniteJetRank

/-!
# Differential independence under an affine base gauge

Rescaling an observable by a nonzero element of the coefficient differential field does not change
its differential independence.  The additive half of this statement is already available as
`DifferentialIndependent.addBase`; this module supplies the multiplicative half, and therefore the
full affine gauge invariance

```text
x ↦ a * x + b,    a, b in the base,  a ≠ 0.
```

The mechanism is the binomial Leibniz rule.  The jets of `a * x` are

```text
jet n (a * x) = ∑_{k ≤ n} (n choose k) * jet (n - k) a * jet k x,
```

whose `k = n` term is `a * jet n x` and whose remaining terms only involve strictly lower jets of
`x`.  That is exactly a principal lower law with constant diagonal symbol `diagonal a`, so the
ancestral conservation theorem transports algebraic independence in both directions.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]
  [Fintype ι] [DecidableEq ι]

/-- The Leibniz coefficient attaching jet layer `k` of the observable to jet layer `n` of its
base rescaling. -/
def baseGaugeCoefficient (a : K) (n k : ℕ) : K :=
  if k ≤ n then (n.choose k : K) * differentialJet (n - k) a else 0

/-- The strictly-lower remainder of the Leibniz expansion of a base rescaling. -/
def baseGaugeRemainder {N : ℕ} (a : ι → K) :
    Matrix (Fin N × ι) (Fin N × ι) K :=
  fun p q =>
    if p.2 = q.2 ∧ (q.1 : ℕ) < (p.1 : ℕ) then
      baseGaugeCoefficient (a p.2) (p.1 : ℕ) (q.1 : ℕ)
    else 0

omit [Fintype ι] in
/-- Adding the diagonal symbol to the remainder recovers the full Leibniz coefficient. -/
theorem baseGaugeRemainder_add_diagonal_apply {N : ℕ} (a : ι → K)
    (p q : Fin N × ι) :
    (baseGaugeRemainder (N := N) a +
        matrixPrincipalBlockDiagonal (fun _ : Fin N ↦ Matrix.diagonal a)) p q =
      if p.2 = q.2 ∧ (q.1 : ℕ) ≤ (p.1 : ℕ) then
        baseGaugeCoefficient (a p.2) (p.1 : ℕ) (q.1 : ℕ)
      else 0 := by
  classical
  by_cases hi : p.2 = q.2
  · by_cases hlt : (q.1 : ℕ) < (p.1 : ℕ)
    · have hne : p.1 ≠ q.1 := by
        intro h
        rw [h] at hlt
        exact lt_irrefl _ hlt
      simp [baseGaugeRemainder, matrixPrincipalBlockDiagonal, hi, hlt, hne,
        le_of_lt hlt]
    · by_cases heq : (q.1 : ℕ) = (p.1 : ℕ)
      · have hfin : p.1 = q.1 := Fin.ext heq.symm
        simp [baseGaugeRemainder, matrixPrincipalBlockDiagonal,
          baseGaugeCoefficient, hi, hfin, Matrix.diagonal,
          differentialJet_zero]
      · have hnotle : ¬ ((q.1 : ℕ) ≤ (p.1 : ℕ)) := by omega
        have hne : p.1 ≠ q.1 := by
          intro h
          exact heq (congrArg (fun r : Fin N ↦ (r : ℕ)) h).symm
        simp [baseGaugeRemainder, matrixPrincipalBlockDiagonal, hi, hlt, hne,
          hnotle]
  · simp [baseGaugeRemainder, matrixPrincipalBlockDiagonal, hi,
      Matrix.diagonal]

/-- **Base rescaling is a principal lower law.**  The jets of `a * x` are obtained from the jets of
`x` by a jet-triangular matrix whose diagonal symbol is the constant matrix `diagonal a`. -/
theorem differentialJet_mulBase_lowerLaw (x : ι → L) (a : ι → K) :
    MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (x i))
      (fun n i ↦ differentialJet n (algebraMap K L (a i) * x i))
      (fun _ ↦ Matrix.diagonal a) := by
  classical
  intro N
  refine ⟨baseGaugeRemainder a, ?_, ?_⟩
  · intro p q hpq
    have hnotlt : ¬ ((q.1 : ℕ) < (p.1 : ℕ)) := by omega
    simp [baseGaugeRemainder, hnotlt]
  · funext p
    show differentialJet (p.1 : ℕ) (algebraMap K L (a p.2) * x p.2) =
      matrixLinearForms _ (fun q : Fin N × ι ↦ differentialJet (q.1 : ℕ) (x q.2)) p
    -- Expand the left side by the binomial Leibniz rule.
    rw [differentialJet_mul_binomial]
    have hbase : ∀ m : ℕ,
        differentialJet m (algebraMap K L (a p.2)) =
          algebraMap K L (differentialJet m (a p.2)) :=
      fun m ↦ differentialJet_algebraMap_apply m (a p.2)
    -- Rewrite the right side as a single sum over jet layers.
    rw [matrixLinearForms]
    simp only [baseGaugeRemainder_add_diagonal_apply]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ n : Fin N,
        (∑ i : ι, algebraMap K L
            (if p.2 = i ∧ (n : ℕ) ≤ (p.1 : ℕ) then
              baseGaugeCoefficient (a p.2) (p.1 : ℕ) (n : ℕ) else 0) *
              differentialJet (n : ℕ) (x i)) =
          (if (n : ℕ) ≤ (p.1 : ℕ) then
            algebraMap K L (baseGaugeCoefficient (a p.2) (p.1 : ℕ) (n : ℕ)) *
              differentialJet (n : ℕ) (x p.2) else 0) := by
      intro n
      rw [Finset.sum_eq_single p.2]
      · by_cases hle : (n : ℕ) ≤ (p.1 : ℕ) <;> simp [hle]
      · intro i _ hip
        simp [Ne.symm hip]
      · intro hcontra
        exact absurd (Finset.mem_univ p.2) hcontra
    rw [Finset.sum_congr rfl (fun n _ ↦ hinner n)]
    -- Compare the two layer sums.
    rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ if k ≤ (p.1 : ℕ) then
        algebraMap K L (baseGaugeCoefficient (a p.2) (p.1 : ℕ) k) *
          differentialJet k (x p.2) else 0) N]
    have hp1 : (p.1 : ℕ) < N := p.1.2
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hp1)]
    have htail : (∑ k ∈ Finset.Ico ((p.1 : ℕ) + 1) N,
        (if k ≤ (p.1 : ℕ) then
          algebraMap K L (baseGaugeCoefficient (a p.2) (p.1 : ℕ) k) *
            differentialJet k (x p.2) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Ico] at hk
      have : ¬ (k ≤ (p.1 : ℕ)) := by omega
      simp [this]
    rw [htail, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ (p.1 : ℕ) := Nat.lt_succ_iff.mp hk
    rw [if_pos hkle, baseGaugeCoefficient, if_pos hkle, hbase]
    push_cast
    simp [nsmul_eq_mul]
    ring

omit [Differential K] in
/-- A diagonal symbol of nonzero base entries is nonsingular. -/
theorem diagonal_baseGauge_det_ne_zero (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    ∀ _n : ℕ, (Matrix.diagonal a).det ≠ 0 := by
  intro _n
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ ha i

/-- **Multiplicative base gauge invariance.**  Rescaling every observable by a nonzero element of
the coefficient differential field preserves differential independence in both directions. -/
theorem differentialIndependent_mulBase_iff
    (x : ι → L) (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent K (fun i ↦ algebraMap K L (a i) * x i) ↔
      DifferentialIndependent K x := by
  have hpacket := matrixPrincipalLowerLaw_ancestral_independence_iff
    (fun n i ↦ differentialJet n (x i))
    (fun n i ↦ differentialJet n (algebraMap K L (a i) * x i))
    (fun _ ↦ Matrix.diagonal a)
    (differentialJet_mulBase_lowerLaw x a)
    (diagonal_baseGauge_det_ne_zero a ha)
  have hshuffle : ∀ y : ι → L,
      AlgebraicIndependent K (fun p : ι × ℕ ↦ differentialJet p.2 (y p.1)) ↔
        AlgebraicIndependent K (fun p : ℕ × ι ↦ differentialJet p.1 (y p.2)) := by
    intro y
    simpa [Function.comp_def] using
      (algebraicIndependent_equiv (R := K) (Equiv.prodComm ι ℕ) :
        AlgebraicIndependent K
            ((fun p : ℕ × ι ↦ differentialJet p.1 (y p.2)) ∘ Equiv.prodComm ι ℕ) ↔
          AlgebraicIndependent K
            (fun p : ℕ × ι ↦ differentialJet p.1 (y p.2)))
  unfold DifferentialIndependent
  rw [hshuffle (fun i ↦ algebraMap K L (a i) * x i), hshuffle x]
  exact hpacket

/-- **Affine base gauge invariance.**  Combining the multiplicative gauge with the additive one,
differential independence is invariant under `x ↦ a * x + b` for base coefficients with nonzero
multiplier. -/
theorem differentialIndependent_affineBase_iff
    (x : ι → L) (a b : ι → K) (ha : ∀ i, a i ≠ 0) :
    DifferentialIndependent K
        (fun i ↦ algebraMap K L (a i) * x i + algebraMap K L (b i)) ↔
      DifferentialIndependent K x := by
  rw [differentialIndependent_addBase_iff (fun i ↦ algebraMap K L (a i) * x i) b]
  exact differentialIndependent_mulBase_iff x a ha

end

end GaloisForLFunctions.HTGeometry
