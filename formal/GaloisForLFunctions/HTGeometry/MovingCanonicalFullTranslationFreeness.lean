import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.SingularContinuousFullTranslationFamilyFreenessUniversalityLaw

/-!
# Full-translation differential freeness of moving canonical log-derivatives

For a bounded real sequence `θ` (supremum norm), the moving canonical divisor has simple positive
zeros `a_n(θ) = n + 1 + δ(θ n)` with displacement `δ ∈ (-1/4, 1/4)`, and
`L_θ(z) = Σ_n ((a_n(θ) - z)⁻¹ - a_n(θ)⁻¹)` is the negative logarithmic derivative of the associated
canonical product. For a dense residual set of `θ`, for every `m` and every configuration of `m`
distinct complex shifts `s_i`, the family of translates `z ↦ L_θ(z + s_i)` satisfies no nonzero
polynomial relation in `z` and finitely many derivatives of the family members on the set of `z`
with every `z + s_i` in the upper half-plane.

## Main results

- `not_familyDifferentiallyAlgebraicOn_movingCanonicalLogDerivative_of_relationFree`: if `θ`
  has no nonzero coefficient vector for any finite expanded pattern relation, then no
  distinct-translate family of `L_θ` is differentially algebraic.
- `movingCanonical_fullTranslationFreeness_denseResidual`: the pattern-relation-free `θ` form a
  dense residual set, and for each of them every distinct-translate family of `L_θ` is not
  differentially algebraic on the common upper translation domain.

## Hypotheses

`movingCanonical_fullTranslationFreeness_denseResidual` is unconditional. The intermediate theorem
`not_familyDifferentiallyAlgebraicOn_movingCanonicalLogDerivative_of_relationFree` takes the
all-patterns relation-freeness of `θ` as a hypothesis; the main theorem discharges it on a dense
residual set via `allFinitePatterns_movingCanonicalExpandedRelationFree_dense_residual`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- The expanded packet entry at row `r` and jet slot `(i, k)` is the `k`-th derivative of
`L_θ(· + s_i)` at the row point, the matching coordinate of `familyJetVec`. -/
theorem movingCanonicalExpandedPacketValue_eq_familyJetVec
    {m n : ℕ} {row : Type} [Fintype row] [DecidableEq row]
    (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration (Fin m)) (r : row)
    (t : Σ _ : Fin m, Fin (n + 1)) :
    movingCanonicalExpandedPacketValue
        (fun _ : Fin m => n + 1) packet θ shift
        (r, Fintype.equivFin (Σ _ : Fin m, Fin (n + 1)) t) =
      familyJetVec (n := n)
        (fun i w => movingCanonicalLogDerivative θ (w + shift.1 i))
        (packet.1 r) (Sum.inr (t.1, t.2)) := by
  rw [movingCanonicalExpandedPacketValue]
  show iteratedDeriv _ _ _ = _
  rw [(Fintype.equivFin (Σ _ : Fin m, Fin (n + 1))).symm_apply_apply t]
  show _ = iteratedDeriv (t.2 : ℕ)
    (fun w => movingCanonicalLogDerivative θ (w + shift.1 t.1))
    (packet.1 r)
  rw [iteratedDeriv_comp_add_right]
  rfl

/-- Assuming `hfree` (every expanded pattern relation satisfied by `θ` has zero coefficients), no
family of distinct translates `z ↦ L_θ(z + s_i)` satisfies a nonzero polynomial differential
relation on the common upper translation domain. -/
theorem not_familyDifferentiallyAlgebraicOn_movingCanonicalLogDerivative_of_relationFree
    (m : ℕ) (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      movingCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => movingCanonicalLogDerivative θ (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  let shiftCode : Fin m → ℕ := naturalFamilyShiftCode m
  have hshiftCode : Function.Injective shiftCode :=
    naturalFamilyShiftCode_injective m
  let Q : MvPolynomial
      (Σ _ : Fin m, Fin (n + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets m n (familyReshapeJet m n P)
  let p : FiniteDifferentialPattern ℕ :=
    codedFamilyPatternOfRelation shiftCode hshiftCode P
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) :=
    ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector
      shiftCode hshiftCode (familyOrders m n) Q
  let coeff :
      CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff
      (Fintype.equivFin (PatternShape p) col)
  have hrelation : movingCanonicalExpandedPatternRelationHolds
      (row := CarrierPatternRow p)
      p.coefficientDegree p.orders
      (carrierPatternExponent p) θ shiftP coeff := by
    intro packet hinj hupper r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      movingCanonicalExpandedPacketValue p.orders packet θ shiftP
    let x : sigma → ℂ := fun t =>
      familyJetVec (n := n)
        (fun i w => movingCanonicalLogDerivative θ (w + shift.1 i))
        z (Sum.inr (t.1, t.2))
    have hy : ∀ t : sigma,
        y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      simpa [y, x, p, Q, shiftP, shiftCode,
        codedFamilyPatternOfRelation, familyOrders] using!
        (movingCanonicalExpandedPacketValue_eq_familyJetVec
          packet θ shift r
          (⟨t.1, t.2⟩ : Σ _ : Fin m, Fin (n + 1)))
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod
            (fun k e => y (r, k) ^ e) =
          (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply,
        Finsupp.prod_equivMapDomain]
      apply Finsupp.prod_congr
      intro t ht
      rw [hy t]
    have hsum :
        (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1
            (carrierPatternExponent p) y r col) =
          ∑ b : PatternRow p,
            patternCoeff b * z ^ patternDegree p b *
              (patternExponent p b).prod
                (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv
        (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree,
        patternExponent, z]
      ring
    rw [hsum]
    have hdomain :
        z ∈ commonUpperTranslationDomain shift := by
      intro i
      have hi := hupper (r, i)
      simpa [commonUpperTranslationDomain,
        combinedProjectiveRowShiftPacket,
        z, shiftP, p, codedFamilyPatternOfRelation] using hi
    calc
      (∑ b : PatternRow p,
          patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod
              (fun t e => x t ^ e)) =
          MvPolynomial.eval
            (Sum.elim (fun _ => z)
              fun q => x ⟨q.1, q.2⟩) P := by
        simpa [patternCoeff, p, Q] using!
          (codedFamilyPatternExpansion_eq_eval
            shiftCode hshiftCode P z x)
      _ = 0 := hPzero z hdomain
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p,
      patternCoeff b = 0 := by
    intro b
    let col : PatternShape p :=
      (Fintype.equivFin (PatternShape p)).symm b
    have hz := hcoeffZero col
    simpa [coeff, col] using hz
  have hP : P = 0 :=
    familyJetRelation_eq_zero_of_codedPatternCoefficients_zero
      shiftCode hshiftCode P (by
        intro b
        exact hpatternZero b)
  exact hPne hP

/-- For a dense residual set of bounded real sequences `θ`, every finite family of distinct
translates `z ↦ L_θ(z + s_i)` of the moving canonical log-derivative is not differentially
algebraic on `{z | ∀ i, 0 < Im (z + s_i)}`. -/
theorem movingCanonical_fullTranslationFreeness_denseResidual :
    let universalPhase : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        movingCanonicalExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence ∧
      ∀ θ ∈ universalPhase, ∀ (m : ℕ)
        (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z =>
            movingCanonicalLogDerivative θ (z + shift.1 i))
          (commonUpperTranslationDomain shift) := by
  dsimp only
  let universalPhase : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      movingCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0}
  have hphase : Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence := by
    simpa only [universalPhase] using
      (allFinitePatterns_movingCanonicalExpandedRelationFree_dense_residual
        (Γ := ℕ))
  refine ⟨hphase.1, hphase.2, ?_⟩
  intro θ hθ m shift
  exact
    not_familyDifferentiallyAlgebraicOn_movingCanonicalLogDerivative_of_relationFree
      m θ hθ shift

end

end GaloisForLFunctions.HTGeometry
