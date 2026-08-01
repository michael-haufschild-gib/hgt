import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRankGenericity
import GaloisForLFunctions.HTGeometry.JetFactorialScale
import GaloisForLFunctions.HTGeometry.SingularContinuousFullTranslationFamilyFreenessUniversalityLaw

/-!
# Full-translation differential freeness for arbitrary-measure Herglotz charts

Normalized Cauchy moments differ from actual derivatives by coordinatewise nonzero factorials.
Scaling the variables of a hypothetical family differential polynomial by those factorials gives a
nonzero polynomial in normalized moment coordinates.  The all-pattern coefficient-rigidity phase
therefore excludes the original relation for every finite tuple of distinct complex translations.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 2000000

/-- Factorial multiplier on a family jet coordinate; the spectral base coordinate has multiplier
one. -/
def familyJetFactorialMultiplier {m n : ℕ} : FamilyJetIndex m n → ℂ :=
  Sum.elim (fun _ => 1) (fun p => ((p.2.1.factorial : ℕ) : ℂ))

/-- Every family-jet factorial multiplier is nonzero. -/
theorem familyJetFactorialMultiplier_ne_zero {m n : ℕ} :
    ∀ q : FamilyJetIndex m n, familyJetFactorialMultiplier q ≠ 0 := by
  intro q
  cases q with
  | inl u => cases u; simp [familyJetFactorialMultiplier]
  | inr p =>
      simp only [familyJetFactorialMultiplier, Sum.elim_inr]
      exact_mod_cast Nat.factorial_ne_zero p.2.1

/-- A normalized Herglotz packet coordinate is the corresponding kernel moment of the finite
exponentially reweighted measure. -/
theorem herglotzExpandedPacketValue_eq_cauchyKernelMoment
    {row ι : Type} [Fintype row] [DecidableEq row] [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) (hwnn : ∀ t, 0 ≤ w t)
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (u : Lp ℝ ⊤ μ) (shift : InjectiveShiftConfiguration ι)
    (r : row) (t : Σ i, Fin (orders i)) :
    herglotzExpandedPacketValue μ w orders packet u shift
        (r, Fintype.equivFin (Σ i, Fin (orders i)) t) =
      cauchyKernelMoment (expWeightedMeasure μ w u) t.2.1
        (packet.1 r + shift.1 t.1) := by
  have hmoment := nodeJet_eq_cauchyKernelMoment μ w hwnn
    hw.aestronglyMeasurable.aemeasurable t.2.1 u (packet.1 r + shift.1 t.1)
  change herglotzJetMap μ w (combinedProjectiveRowShiftPacket packet shift)
    (fun x : row × ι => orders x.2) u
      ⟨(r, ((Fintype.equivFin (Σ i, Fin (orders i))).symm
        (Fintype.equivFin (Σ i, Fin (orders i)) t)).1),
        ((Fintype.equivFin (Σ i, Fin (orders i))).symm
          (Fintype.equivFin (Σ i, Fin (orders i)) t)).2⟩ = _
  rw [(Fintype.equivFin (Σ i, Fin (orders i))).symm_apply_apply t]
  change nodeJet μ w t.2.1 u (packet.1 r + shift.1 t.1) = _
  exact hmoment

/-- **Coefficient rigidity excludes every finite translated Cauchy-family differential
relation.**  This is the exact relation-descent step from normalized moment packets to actual
iterated derivatives. -/
theorem not_familyDifferentiallyAlgebraicOn_expWeightedCauchy_of_allFinitePatterns_relationFree
    (m : ℕ)
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) (hwnn : ∀ t, 0 ≤ w t)
    (u : Lp ℝ ⊤ μ)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      herglotzExpandedPatternRelationHolds
        (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
          (carrierPatternExponent p) u shift coeff →
        ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => cauchyTransform (expWeightedMeasure μ w u) (z + shift.1 i))
      (commonUpperTranslationDomain shift) := by
  intro hDA
  obtain ⟨n, P, hPne, hPzero⟩ := hDA
  let scale : FamilyJetIndex m n → ℂ := familyJetFactorialMultiplier
  let Q : MvPolynomial (FamilyJetIndex m n) ℂ := mvPolynomialDiagonalScale scale P
  have hQne : Q ≠ 0 :=
    mvPolynomialDiagonalScale_ne_zero scale familyJetFactorialMultiplier_ne_zero hPne
  let shiftCode : Fin m → ℕ := naturalFamilyShiftCode m
  have hshiftCode : Function.Injective shiftCode := naturalFamilyShiftCode_injective m
  let R : MvPolynomial (Σ _ : Fin m, Fin (n + 1)) (Polynomial ℂ) :=
    renameToFamilyShiftJets m n (familyReshapeJet m n Q)
  let p : FiniteDifferentialPattern ℕ :=
    codedFamilyPatternOfRelation shiftCode hshiftCode Q
  let shiftP : InjectiveShiftConfiguration (CarrierPatternShift p) :=
    ⟨shift.1, shift.2⟩
  let patternCoeff : PatternRow p → ℂ :=
    polynomialPatternCoefficientVector shiftCode hshiftCode (familyOrders m n) R
  let coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ :=
    fun col => patternCoeff (Fintype.equivFin (PatternShape p) col)
  let ν : Measure ℝ := expWeightedMeasure μ w u
  letI : IsFiniteMeasure ν := isFiniteMeasure_expWeightedMeasure μ w hw hwnn u
  have hrelation : herglotzExpandedPatternRelationHolds
      (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
        (carrierPatternExponent p) u shiftP coeff := by
    intro packet hinj hupper r
    let z : ℂ := packet.1 r
    let sigma := Σ i : CarrierPatternShift p, Fin (p.orders i)
    let y : CarrierPatternRow p × Fin (Fintype.card sigma) → ℂ :=
      herglotzExpandedPacketValue μ w p.orders packet u shiftP
    let x : sigma → ℂ := fun t => y (r, Fintype.equivFin sigma t)
    have hy : ∀ t : sigma, y (r, Fintype.equivFin sigma t) = x t := by
      intro t
      rfl
    have hprod : ∀ a : CarrierPatternMonomial p,
        (carrierPatternExponent p a).prod (fun k e => y (r, k) ^ e) =
          (p.jetExponent a).prod (fun t e => x t ^ e) := by
      intro a
      rw [carrierPatternExponent, Finsupp.equivCongrLeft_apply,
        Finsupp.prod_equivMapDomain]
    have hsum :
        (∑ col, coeff col *
          expandedDifferentialEvaluationMatrix p.coefficientDegree
            (Fintype.card sigma) packet.1 (carrierPatternExponent p) y r col) =
          ∑ b : PatternRow p,
            patternCoeff b * z ^ patternDegree p b *
              (patternExponent p b).prod (fun t e => x t ^ e) := by
      apply Fintype.sum_equiv (Fintype.equivFin (PatternShape p))
      intro col
      rw [expandedDifferentialEvaluationMatrix_apply, hprod]
      simp [coeff, patternCoeff, patternDegree, patternExponent, z]
      ring
    rw [hsum]
    have hdomain : z ∈ commonUpperTranslationDomain shift := by
      intro i
      have hi := hupper (r, i)
      simpa [commonUpperTranslationDomain, combinedProjectiveRowShiftPacket,
        z, shiftP, p, codedFamilyPatternOfRelation] using hi
    let point : FamilyJetIndex m n → ℂ :=
      Sum.elim (fun _ : Unit => z)
        (fun t : Fin m × Fin (n + 1) => x ⟨t.1, t.2⟩)
    have hscaledVec :
        (fun q : FamilyJetIndex m n => scale q * point q) =
          familyJetVec
            (fun i z => cauchyTransform ν (z + shift.1 i)) z := by
      rw [familyJetVec_translates]
      funext q
      cases q with
      | inl a => cases a; simp [scale, point, familyJetFactorialMultiplier]
      | inr t =>
          obtain ⟨i, j⟩ := t
          simp only [Sum.elim_inr, scale, familyJetFactorialMultiplier]
          have hznode : (z + shift.1 i).im ≠ 0 := ne_of_gt (hdomain i)
          rw [iteratedDeriv_cauchyTransform ν j.1 hznode]
          congr 1
          have hmoment := herglotzExpandedPacketValue_eq_cauchyKernelMoment
            μ w hw hwnn p.orders packet u shiftP r
              (⟨i, j⟩ : Σ i : CarrierPatternShift p, Fin (p.orders i))
          change x ⟨i, j⟩ =
            cauchyKernelMoment ν j.1 (z + shift.1 i)
          simpa only [point, x, y, z, ν, sigma, shiftP] using hmoment
    calc
      (∑ b : PatternRow p,
          patternCoeff b * z ^ patternDegree p b *
            (patternExponent p b).prod (fun t e => x t ^ e)) =
          MvPolynomial.eval
            point Q := by
              change (∑ b : PatternRow p,
                  patternCoeff b * z ^ patternDegree p b *
                    (patternExponent p b).prod (fun t e => x t ^ e)) =
                MvPolynomial.eval
                  (Sum.elim (fun _ => z) fun q => x ⟨q.1, q.2⟩) Q
              simpa [patternCoeff, p, R] using!
                (codedFamilyPatternExpansion_eq_eval shiftCode hshiftCode Q z x)
      _ = MvPolynomial.eval
          (fun q : FamilyJetIndex m n => scale q * point q) P := by
            exact eval_mvPolynomialDiagonalScale scale _ P
      _ = MvPolynomial.eval
          (familyJetVec (fun i z => cauchyTransform ν (z + shift.1 i)) z) P := by
            rw [hscaledVec]
      _ = 0 := hPzero z hdomain
  have hcoeffZero := hfree p shiftP coeff hrelation
  have hpatternZero : ∀ b : PatternRow p, patternCoeff b = 0 := by
    intro b
    let col : PatternShape p := (Fintype.equivFin (PatternShape p)).symm b
    have hz := hcoeffZero col
    simpa [coeff, col] using hz
  have hQ : Q = 0 := familyJetRelation_eq_zero_of_codedPatternCoefficients_zero
    shiftCode hshiftCode Q (by
      intro b
      exact hpatternZero b)
  exact hQne hQ

/-- **Measure-universal full-translation Cauchy-family freeness.**  For every infinite-support
base measure and strictly positive integrable density, one dense residual set of bounded
exponential parameters excludes every mixed differential relation among every finite family of
distinct complex translates of the resulting finite Cauchy transform. -/
theorem herglotz_fullTranslationCauchyFamilyFreeness_denseResidual
    (μ : Measure ℝ) (hμ : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t) :
    let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
      (p : FiniteDifferentialPattern ℕ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      herglotzExpandedPatternRelationHolds
        (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
          (carrierPatternExponent p) u shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧ universalPhase ∈ residual (Lp ℝ ⊤ μ) ∧
      ∀ u ∈ universalPhase, ∀ (m : ℕ)
        (shift : InjectiveShiftConfiguration (Fin m)),
        ¬ FamilyDifferentiallyAlgebraicOn
          (fun i z => cauchyTransform (expWeightedMeasure μ w u) (z + shift.1 i))
          (commonUpperTranslationDomain shift) := by
  dsimp only
  let universalPhase : Set (Lp ℝ ⊤ μ) := {u | ∀
    (p : FiniteDifferentialPattern ℕ)
    (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
    (coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
    herglotzExpandedPatternRelationHolds
      (row := CarrierPatternRow p) μ w p.coefficientDegree p.orders
        (carrierPatternExponent p) u shift coeff →
      ∀ col, coeff col = 0}
  have hphase : Dense universalPhase ∧
      universalPhase ∈ residual (Lp ℝ ⊤ μ) := by
    simpa only [universalPhase] using
      (allFinitePatterns_herglotzExpandedRelationFree_dense_residual
        (Γ := ℕ) μ hμ w hw hwpos)
  refine ⟨hphase.1, hphase.2, ?_⟩
  intro u hu m shift
  exact not_familyDifferentiallyAlgebraicOn_expWeightedCauchy_of_allFinitePatterns_relationFree
    m μ w hw (fun t => (hwpos t).le) u hu shift

end

end GaloisForLFunctions.HTGeometry
