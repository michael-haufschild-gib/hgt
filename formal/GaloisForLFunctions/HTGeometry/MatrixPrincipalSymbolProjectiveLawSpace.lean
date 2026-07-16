import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDerivationLawHorizon
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAncestralConservation

/-!
# Before time is projective

A selected derivation is a law direction, not a clock rate.  Multiplying it by a nonzero constant
rescales its `n`th jet by the nonzero factor `c^n`, so it cannot change algebraic independence of
the complete jet packet.  The hypertranscendental phase therefore descends from the vector space
of derivations to its projectivization.

The proof is routed through an explicit diagonal principal-symbol law.  It is unconditional and
does not assume in advance that either the original or rescaled jet packet is independent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

/-- Iterating a derivation rescaled by a base-field constant rescales its `n`th jet by `c^n`. -/
theorem selectedDerivationJet_smul_base
    (D : Derivation K L L) (c : K) (n : ℕ) (x : L) :
    selectedDerivationJet (c • D) n x =
      c ^ n • selectedDerivationJet D n x := by
  induction n with
  | zero => simp [selectedDerivationJet]
  | succ n ih =>
      simp only [selectedDerivationJet, Function.iterate_succ_apply']
      change c • D (selectedDerivationJet (c • D) n x) =
        c ^ (n + 1) • D (selectedDerivationJet D n x)
      rw [ih, D.map_smul]
      simp [pow_succ, smul_smul, mul_comm]

/-- The diagonal principal symbol of constant rescaling at jet layer `n`. -/
def derivationRayPrincipalSymbol (c : K) (n : ℕ) : Matrix ι ι K :=
  Matrix.diagonal fun _ ↦ c ^ n

/-- Constant rescaling of a derivation is an exact diagonal principal lower law. -/
theorem selectedDerivationJet_smul_base_lowerLaw
    (observable : ι → L) (D : Derivation K L L) (c : K) :
    MatrixPrincipalLowerLaw
      (fun n i ↦ selectedDerivationJet D n (observable i))
      (fun n i ↦ selectedDerivationJet (c • D) n (observable i))
      (fun n ↦ derivationRayPrincipalSymbol (K := K) (ι := ι) c n) := by
  intro N
  refine ⟨0, ?_, ?_⟩
  · simp
  · funext p
    change selectedDerivationJet (c • D) (p.1 : ℕ) (observable p.2) = _
    rw [selectedDerivationJet_smul_base]
    simp only [zero_add, matrixLinearForms, matrixPrincipalBlockDiagonal,
      derivationRayPrincipalSymbol]
    rw [Finset.sum_eq_single p]
    · simp [Algebra.smul_def]
    · intro q _ hqp
      by_cases hlevel : p.1 = q.1
      · have hindex : p.2 ≠ q.2 := by
          intro h
          exact hqp (Prod.ext hlevel.symm h.symm)
        simp [hlevel, hindex]
      · simp [hlevel]
    · simp

/-- Every diagonal ray symbol is nonsingular when the rescaling constant is nonzero. -/
theorem derivationRayPrincipalSymbol_det_ne_zero
    (c : K) (hc : c ≠ 0) :
    ∀ n, (derivationRayPrincipalSymbol (K := K) (ι := ι) c n).det ≠ 0 := by
  intro n
  simp [derivationRayPrincipalSymbol, hc]

/-- **Projectivization theorem for derivation laws.**  Complete differential-algebraic
independence is invariant under every nonzero constant rescaling of the selected derivation. -/
theorem derivationIndependentOver_smul_base_iff
    (observable : ι → L) (D : Derivation K L L)
    (c : K) (hc : c ≠ 0) :
    DerivationIndependentOver K (c • D) observable ↔
      DerivationIndependentOver K D observable := by
  have hpacket := matrixPrincipalLowerLaw_ancestral_independence_iff
    (fun n i ↦ selectedDerivationJet D n (observable i))
    (fun n i ↦ selectedDerivationJet (c • D) n (observable i))
    (fun n ↦ derivationRayPrincipalSymbol (K := K) (ι := ι) c n)
    (selectedDerivationJet_smul_base_lowerLaw observable D c)
    (derivationRayPrincipalSymbol_det_ne_zero (ι := ι) c hc)
  have htarget :
      AlgebraicIndependent K
          (fun p : ι × ℕ ↦ selectedDerivationJet (c • D) p.2 (observable p.1)) ↔
        AlgebraicIndependent K
          (fun p : ℕ × ι ↦ selectedDerivationJet (c • D) p.1 (observable p.2)) := by
    simpa [Function.comp_def] using
      (algebraicIndependent_equiv (R := K) (Equiv.prodComm ι ℕ) :
        AlgebraicIndependent K
            ((fun p : ℕ × ι ↦
              selectedDerivationJet (c • D) p.1 (observable p.2)) ∘
                Equiv.prodComm ι ℕ) ↔
          AlgebraicIndependent K
            (fun p : ℕ × ι ↦
              selectedDerivationJet (c • D) p.1 (observable p.2)))
  have hsource :
      AlgebraicIndependent K
          (fun p : ι × ℕ ↦ selectedDerivationJet D p.2 (observable p.1)) ↔
        AlgebraicIndependent K
          (fun p : ℕ × ι ↦ selectedDerivationJet D p.1 (observable p.2)) := by
    simpa [Function.comp_def] using
      (algebraicIndependent_equiv (R := K) (Equiv.prodComm ι ℕ) :
        AlgebraicIndependent K
            ((fun p : ℕ × ι ↦ selectedDerivationJet D p.1 (observable p.2)) ∘
              Equiv.prodComm ι ℕ) ↔
          AlgebraicIndependent K
            (fun p : ℕ × ι ↦ selectedDerivationJet D p.1 (observable p.2)))
  exact htarget.trans (hpacket.trans hsource.symm)

/-- The set of derivations for which an observable family is differentially independent. -/
def derivationIndependentPhase (observable : ι → L) : Set (Derivation K L L) :=
  {D | DerivationIndependentOver K D observable}

/-- The derivation-independent phase is a union of punctured scalar rays. -/
theorem smul_mem_derivationIndependentPhase_iff
    (observable : ι → L) (D : Derivation K L L)
    (c : K) (hc : c ≠ 0) :
    c • D ∈ derivationIndependentPhase observable ↔
      D ∈ derivationIndependentPhase observable :=
  derivationIndependentOver_smul_base_iff observable D c hc

/-- Rank-one form: hypertranscendence for a selected law depends only on its projective ray. -/
theorem hypertranscendentalForDerivation_smul_base_iff
    (x : L) (D : Derivation K L L) (c : K) (hc : c ≠ 0) :
    HypertranscendentalForDerivation K (c • D) x ↔
      HypertranscendentalForDerivation K D x :=
  derivationIndependentOver_smul_base_iff (fun _ : Unit ↦ x) D c hc

end

end GaloisForLFunctions.HTGeometry
