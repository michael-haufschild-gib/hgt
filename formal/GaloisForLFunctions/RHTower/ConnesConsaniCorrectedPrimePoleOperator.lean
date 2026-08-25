import GaloisForLFunctions.RHTower.ConnesConsaniCorrectedPrimeHardyIsometry
import GaloisForLFunctions.RHTower.ConnesConsaniCorrectedPrimePoleResidue
import GaloisForLFunctions.RHTower.ConnesConsaniDoublePoleFiniteRank
import GaloisForLFunctions.RHTower.IsometricSandwichApproxNumber

/-!
# Corrected Connes--Consani prime-pole operator

The corrected source isometry is placed inside the positive and negative paper Hardy half-spaces.
Sandwiching the corrected reduced Gauss block between these two embeddings constructs the literal
finite-prime pole block in the paper circle coordinate.  Its energy is an isometric zero extension
of the corrected reduced energy, so every approximation number and the measurable logarithmic
residue are preserved exactly.
-/

namespace RHTower

noncomputable section

/-- Corrected source isometry followed by the negative Hardy embedding. -/
def connesConsaniCorrectedPrimeNegativeCircleIsometry (p : Nat.Primes) :
    CCMCircleL2 →ₗᵢ[ℂ] CCMCircleL2 :=
  ccmNegativeHardyIsometry.comp (connesConsaniCorrectedPrimeHardyIsometry p)

/-- Corrected source isometry followed by the positive Hardy embedding. -/
def connesConsaniCorrectedPrimePositiveCircleIsometry (p : Nat.Primes) :
    CCMCircleL2 →ₗᵢ[ℂ] CCMCircleL2 :=
  ccmPositiveHardyIsometry.comp (connesConsaniCorrectedPrimeHardyIsometry p)

/-- Corrected distinguished finite-prime pole block in the paper circle coordinate. -/
def connesConsaniCorrectedPrimePoleOperator (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  (connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap ∘L
    connesConsaniCorrectedReducedPrimePoleDefect p ∘L
      ContinuousLinearMap.adjoint
        (connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap

/-- The corrected negative circle isometry carries every normalized literal source feature to the
paper's named Hardy feature in the negative Fourier half-space. -/
theorem connesConsaniCorrectedPrimeNegativeCircleIsometry_apply_feature
    (p : Nat.Primes) (n : ℤ) :
    connesConsaniCorrectedPrimeNegativeCircleIsometry p
        (connesConsaniNormalizedPrimeSourceFeature p n) =
      ccmNegativeHardyIsometry (connesConsaniPrimeHardyFeature p n) := by
  exact congrArg ccmNegativeHardyIsometry
    (connesConsaniCorrectedPrimeHardyIsometry_apply_feature p n)

/-- The corrected positive circle isometry carries every normalized literal source feature to the
paper's named Hardy feature in the positive Fourier half-space. -/
theorem connesConsaniCorrectedPrimePositiveCircleIsometry_apply_feature
    (p : Nat.Primes) (n : ℤ) :
    connesConsaniCorrectedPrimePositiveCircleIsometry p
        (connesConsaniNormalizedPrimeSourceFeature p n) =
      ccmPositiveHardyIsometry (connesConsaniPrimeHardyFeature p n) := by
  exact congrArg ccmPositiveHardyIsometry
    (connesConsaniCorrectedPrimeHardyIsometry_apply_feature p n)

/-- On its incoming Hardy range, the paper-coordinate pole block is exactly the corrected reduced
Gauss block followed by the outgoing Hardy isometry. -/
theorem connesConsaniCorrectedPrimePoleOperator_apply_positiveRange
    (p : Nat.Primes) (v : CCMCircleL2) :
    connesConsaniCorrectedPrimePoleOperator p
        (connesConsaniCorrectedPrimePositiveCircleIsometry p v) =
      connesConsaniCorrectedPrimeNegativeCircleIsometry p
        (connesConsaniCorrectedReducedPrimePoleDefect p v) := by
  have hcancel := DFunLike.congr_fun
    (connesConsaniCorrectedPrimePositiveCircleIsometry p).adjoint_comp_self v
  have hcancel' : ContinuousLinearMap.adjoint
      (connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap
        ((connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap v) = v := by
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      one_apply_eq_self] using hcancel
  simp only [connesConsaniCorrectedPrimePoleOperator,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  change (connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap
      (connesConsaniCorrectedReducedPrimePoleDefect p
        (ContinuousLinearMap.adjoint
          (connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap
            ((connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap v))) =
    (connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap
      (connesConsaniCorrectedReducedPrimePoleDefect p v)
  rw [hcancel']

/-- Exact matrix-form recovery of the corrected reduced block inside the paper Hardy half-spaces. -/
theorem inner_connesConsaniCorrectedPrimePoleOperator_ranges
    (p : Nat.Primes) (u v : CCMCircleL2) :
    inner ℂ (connesConsaniCorrectedPrimeNegativeCircleIsometry p u)
        (connesConsaniCorrectedPrimePoleOperator p
          (connesConsaniCorrectedPrimePositiveCircleIsometry p v)) =
      inner ℂ u (connesConsaniCorrectedReducedPrimePoleDefect p v) := by
  rw [connesConsaniCorrectedPrimePoleOperator_apply_positiveRange]
  exact (connesConsaniCorrectedPrimeNegativeCircleIsometry p).inner_map_map u
    (connesConsaniCorrectedReducedPrimePoleDefect p v)

/-- Hilbert adjoint of the corrected paper-coordinate finite-prime pole block. -/
theorem adjoint_connesConsaniCorrectedPrimePoleOperator (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) =
      (connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap ∘L
        connesConsaniCorrectedReducedPrimePoleDefect p ∘L
          ContinuousLinearMap.adjoint
            (connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap := by
  rw [connesConsaniCorrectedPrimePoleOperator,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    adjoint_connesConsaniCorrectedReducedPrimePoleDefect]
  rw [ContinuousLinearMap.comp_assoc]

/-- The paper-coordinate pole energy is the isometric zero extension of the corrected reduced
energy. -/
theorem connesConsaniCorrectedPrimePoleOperator_modulusSq (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) ∘L
        connesConsaniCorrectedPrimePoleOperator p =
      ((connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap ∘L
          (ContinuousLinearMap.adjoint
              (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
            connesConsaniCorrectedReducedPrimePoleDefect p)) ∘L
        ContinuousLinearMap.adjoint
          (connesConsaniCorrectedPrimePositiveCircleIsometry p).toContinuousLinearMap := by
  rw [adjoint_connesConsaniCorrectedPrimePoleOperator,
    connesConsaniCorrectedPrimePoleOperator]
  apply ContinuousLinearMap.ext
  intro x
  have hcancel (y : CCMCircleL2) :
      ContinuousLinearMap.adjoint
          (connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap
        ((connesConsaniCorrectedPrimeNegativeCircleIsometry p).toContinuousLinearMap y) = y := by
    have h := DFunLike.congr_fun
      (connesConsaniCorrectedPrimeNegativeCircleIsometry p).adjoint_comp_self y
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      one_apply_eq_self] using h
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hcancel]
  rw [adjoint_connesConsaniCorrectedReducedPrimePoleDefect]

/-- Every approximation number of the corrected paper-coordinate pole energy equals the
corresponding reduced-energy approximation number. -/
theorem approxNumber_connesConsaniCorrectedPrimePoleOperator_modulusSq
    (p : Nat.Primes) (n : ℕ) :
    approxNumber
        (ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) ∘L
          connesConsaniCorrectedPrimePoleOperator p) n =
      approxNumber
        (ContinuousLinearMap.adjoint
            (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
          connesConsaniCorrectedReducedPrimePoleDefect p) n := by
  rw [connesConsaniCorrectedPrimePoleOperator_modulusSq]
  exact approxNumber_linearIsometry_adjoint_sandwich
    (connesConsaniCorrectedPrimePositiveCircleIsometry p)
    (ContinuousLinearMap.adjoint
        (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
      connesConsaniCorrectedReducedPrimePoleDefect p) n

/-- The corrected paper-coordinate prime-pole energy belongs to weak Schatten one. -/
theorem memWeakSchattenClass_connesConsaniCorrectedPrimePoleOperator_modulusSq
    (p : Nat.Primes) :
    MemWeakSchattenClass 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) ∘L
        connesConsaniCorrectedPrimePoleOperator p) := by
  obtain ⟨C, hC, hbound⟩ :=
    memWeakSchattenClass_connesConsaniCorrectedReducedPrimePoleDefect_modulusSq p
  refine ⟨C, hC, fun n => ?_⟩
  rw [approxNumber_connesConsaniCorrectedPrimePoleOperator_modulusSq]
  exact hbound n

/-- Exact corrected measurable logarithmic residue of the paper-coordinate prime-pole energy. -/
theorem hasSchattenLogResidue_connesConsaniCorrectedPrimePoleOperator_modulusSq
    (p : Nat.Primes) :
    HasSchattenLogResidue 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) ∘L
        connesConsaniCorrectedPrimePoleOperator p)
      (connesConsaniCorrectedPrimePoleResidue p) := by
  have h :=
    hasSchattenLogResidue_connesConsaniCorrectedReducedPrimePoleDefect_modulusSq p
  unfold HasSchattenLogResidue at h ⊢
  simpa only [schattenPowerPartialSum,
    approxNumber_connesConsaniCorrectedPrimePoleOperator_modulusSq] using h

/-- Positive corrected residue excludes trace class for the paper-coordinate prime-pole energy. -/
theorem connesConsaniCorrectedPrimePoleOperator_modulusSq_not_memSchattenClass
    (p : Nat.Primes) :
    ¬ MemSchattenClass 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedPrimePoleOperator p) ∘L
        connesConsaniCorrectedPrimePoleOperator p) := by
  exact
    (hasSchattenLogResidue_connesConsaniCorrectedPrimePoleOperator_modulusSq p).not_memSchattenClass
      (connesConsaniCorrectedPrimePoleResidue_pos p)

end


end RHTower
