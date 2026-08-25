import GaloisForLFunctions.HTGeometry.GammaGerbeDixmierDouadyGenerator
import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCovariantStokesFlat

/-!
# Relative Gamma anomaly matching and compact reduction

The Gamma bulk class cannot be cancelled: its Dixmier--Douady cocycle is not a coboundary.
Nevertheless every Xi divisor copy is flat after one uniquely forced rank-one boundary twist.
The twist is the expanding light-cone eigenvalue of a reciprocal Lorentz pair. It admits a
positive compact reduction exactly when it untwists to the fixed Deninger source, equivalently
exactly on the critical line.

Thus neither bulk-anomaly cancellation, relative flatness, nor functional-equation duality is the
RH selector. The selector is compact reduction of the uniquely matched relative boundary system.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Boundary anomaly matching means that the physical Xi character is flat for the chosen
rank-one source holonomy. -/
def XiGammaBoundaryRelativeAnomalyMatched (q : XiZeroCopy) (u : ℝ) : Prop :=
  (sourceHorizontalGammaSixCyclicCharacterReadout
      (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).comp
    (sourceHorizontalGammaSixHolonomyBoundary u) = 0

/-- Compact-real-form test for reciprocal holonomy attached to one Xi divisor copy. -/
def XiGammaBoundaryAdmitsCompactReduction (q : XiZeroCopy) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
    IsPositiveMetric P ∧
      IsContractionIn P
        (lorentzBoost
          (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))) ∧
      IsContractionIn P
        (lorentzBoost
          (-sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ)))

private theorem identity_isPositiveMetric :
    IsPositiveMetric (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro v hv
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp [h.1, h.2]
  rw [metricForm]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rcases hv' with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0]
  · nlinarith [sq_pos_of_ne_zero h1]

private theorem identity_isContractionIn_identity :
    IsContractionIn (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
  intro v
  simp

/-- Reciprocal Gamma-six boundary holonomy admits a positive compact reduction exactly when its
rapidity vanishes. -/
theorem xiGammaBoundaryAdmitsCompactReduction_iff_parameter_eq_zero
    (q : XiZeroCopy) :
    XiGammaBoundaryAdmitsCompactReduction q ↔
      sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ) = 0 := by
  constructor
  · rintro ⟨P, hP, hforward, hreflected⟩
    exact rapidity_eq_zero_of_contraction_pair hP hforward hreflected
  · intro hzero
    refine ⟨1, identity_isPositiveMetric, ?_, ?_⟩
    · simpa [hzero] using identity_isContractionIn_identity
    · simpa [hzero] using identity_isContractionIn_identity

/-- Boundary holonomy selected by coefficient faithfulness is exactly the expanding light-cone
eigenvalue of the reciprocal Lorentz pair; reflection supplies its inverse. -/
theorem sourceHorizontalGammaSixPhysicalHolonomy_reciprocalBoostPair
    (q : XiZeroCopy) :
    (lorentzBoost
        (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).mulVec ![1, 1] =
      sourceHorizontalGammaSixPhysicalHolonomy q • ![1, 1] ∧
    (lorentzBoost
        (-sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).mulVec ![1, 1] =
      (sourceHorizontalGammaSixPhysicalHolonomy q)⁻¹ • ![1, 1] := by
  constructor
  · simpa [sourceHorizontalGammaSixPhysicalHolonomy] using
      lorentzBoost_mulVec_plus
        (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))
  · simpa [sourceHorizontalGammaSixPhysicalHolonomy, Real.exp_neg] using
      lorentzBoost_mulVec_plus
        (-sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))

/-- Coefficient faithfulness gives a unique relative boundary twist: physical holonomy. -/
theorem xiGammaBoundaryRelativeAnomalyMatched_iff
    (q : XiZeroCopy) (u : ℝ) :
    XiGammaBoundaryRelativeAnomalyMatched q u ↔
      u = sourceHorizontalGammaSixPhysicalHolonomy q := by
  simpa [XiGammaBoundaryRelativeAnomalyMatched,
    sourceHorizontalGammaSixPhysicalHolonomy] using
      sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary_eq_zero_iff
        (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ)) u

theorem existsUnique_xiGammaBoundaryRelativeAnomalyMatched
    (q : XiZeroCopy) :
    ∃! u : ℝ, XiGammaBoundaryRelativeAnomalyMatched q u := by
  refine ⟨sourceHorizontalGammaSixPhysicalHolonomy q, ?_, ?_⟩
  · exact (xiGammaBoundaryRelativeAnomalyMatched_iff q _).2 rfl
  · intro u hu
    exact (xiGammaBoundaryRelativeAnomalyMatched_iff q u).1 hu

theorem sourceHorizontalGammaSixPhysicalCharacterParameter_eq_zero_iff
    (q : XiZeroCopy) :
    sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixPhysicalCharacterParameter]
  have hlog : Real.log (6 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · intro h
    have : 2 * (q.1 : ℂ).re - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_right hlog
    linarith
  · intro h
    rw [h]
    norm_num

/-- Flatness in the uniquely matched local system does not select the line: if an off-line Xi
copy exists, it is still relatively flat, but has no positive compact reduction. -/
theorem xiGammaBoundary_relativeMatched_but_notCompact_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    XiGammaBoundaryRelativeAnomalyMatched q
        (sourceHorizontalGammaSixPhysicalHolonomy q) ∧
      ¬ XiGammaBoundaryAdmitsCompactReduction q := by
  refine ⟨(xiGammaBoundaryRelativeAnomalyMatched_iff q _).2 rfl, ?_⟩
  intro hcompact
  apply hoff
  exact (sourceHorizontalGammaSixPhysicalCharacterParameter_eq_zero_iff q).1
    ((xiGammaBoundaryAdmitsCompactReduction_iff_parameter_eq_zero q).1 hcompact)

/-- Main relative-anomaly/compact-reduction law. Absolute Gamma-gerbe cancellation is impossible,
while every Xi boundary has one unique matched local system. That matched system reduces to the
fixed positive source exactly on the critical line. -/
theorem gammaBulkNontrivial_relativeBoundaryMatching_compactReduction_law
    (q : XiZeroCopy) :
    (¬ ∃ g : GaloisForLFunctions.GerbeCharacteristic.TripticLattice →
        GaloisForLFunctions.GerbeCharacteristic.TripticLattice → ℤ,
      GaloisForLFunctions.GerbeCharacteristic.gammaGerbeDD =
        GaloisForLFunctions.GerbeCharacteristic.coboundary₂ g) ∧
    (∃! u : ℝ, XiGammaBoundaryRelativeAnomalyMatched q u) ∧
    (XiGammaBoundaryAdmitsCompactReduction q ↔
      sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap) ∧
    (XiGammaBoundaryAdmitsCompactReduction q ↔ (q.1 : ℂ).re = 1 / 2) := by
  refine ⟨GaloisForLFunctions.GerbeCharacteristic.gammaGerbeDD_not_coboundary,
    existsUnique_xiGammaBoundaryRelativeAnomalyMatched q, ?_, ?_⟩
  · rw [xiGammaBoundaryAdmitsCompactReduction_iff_parameter_eq_zero,
      sourceHorizontalGammaSixPhysicalCharacterParameter_eq_zero_iff,
      sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff]
  · rw [xiGammaBoundaryAdmitsCompactReduction_iff_parameter_eq_zero,
      sourceHorizontalGammaSixPhysicalCharacterParameter_eq_zero_iff]

end

end RHTower
