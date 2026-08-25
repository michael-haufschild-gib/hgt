import GaloisForLFunctions.RHTower.XiShiftedTerminalFrontierParabolicSynchronization
import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWall

/-!
# Parabolic ultraviolet source-wall phase

False RH does not merely produce defects at unbounded Hankel degree. Its canonical strict
frontiers form a cofinal cascade inside the source-derived parabolic cone, and every rung carries
a non-integrable Christoffel source wall. Conversely, local `L¹` regularity only in the eventual
frontier tail already forces RH; arbitrary bounded infrared walls may be ignored.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- False-RH ultraviolet phase with both pieces of quantitative geometry retained: canonical
frontiers stay inside the universal parabolic cone while their exact source walls have infinite
local action. -/
def XiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      xiShiftedHigherBlockTerminalFrontier (n + 1) <
        routeUParabolicDegreeHorizon * (((n + 3 : ℕ) : ℝ) ^ 2) ∧
      ∀ b : ℝ, xiShiftedHigherBlockTerminalFrontier (n + 1) < b →
        ¬IntervalIntegrable
          (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1))
          volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b

/-- False RH forces a parabolically confined cofinal cascade of infinite-action source walls. -/
theorem xiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, hparabolic⟩ :=
    exists_cofinal_sourceAdaptive_parabolicFrontierCertificate_of_not_riemannHypothesis hnot A
  exact ⟨n, hne, hA, hstrict, hparabolic, fun _b hb =>
    not_intervalIntegrable_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
      hne hstrict hb⟩

/-- RH excludes the parabolic infinite-action ultraviolet phase. -/
theorem not_xiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- RH is exactly absence of the parabolically confined ultraviolet source-wall cascade. -/
theorem riemannHypothesis_iff_not_xiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase :
    RiemannHypothesis ↔
      ¬XiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase := by
  constructor
  · exact
      not_xiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedParabolicCofinalNonintegrableChristoffelSourceWallPhase_of_not_riemannHypothesis
        hnotRH)

/-- Ultraviolet regularity modulo bounded infrared defects: after one finite mass threshold,
every occupied strict-frontier Christoffel source wall is locally `L¹` on some right interval. -/
def XiShiftedChristoffelSourceWallEventuallyLocallyIntegrable : Prop :=
  ∃ A : ℝ, ∀ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty →
    A < xiShiftedHigherBlockTerminalFrontier n →
    xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1) →
    ∃ b : ℝ,
      xiShiftedHigherBlockTerminalFrontier (n + 1) < b ∧
      IntervalIntegrable
        (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1))
        volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b

/-- Under RH ultraviolet regularity holds vacuously because no failure frontier is occupied. -/
theorem xiShiftedChristoffelSourceWallEventuallyLocallyIntegrable_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiShiftedChristoffelSourceWallEventuallyLocallyIntegrable := by
  refine ⟨0, ?_⟩
  intro n hne _hA _hstrict
  exfalso
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Exact falsifier: false RH destroys every proposed ultraviolet regularity threshold. -/
theorem not_xiShiftedChristoffelSourceWallEventuallyLocallyIntegrable_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    ¬XiShiftedChristoffelSourceWallEventuallyLocallyIntegrable := by
  rintro ⟨A, hregular⟩
  obtain ⟨n, hne, hA, hstrict, _hparabolic⟩ :=
    exists_cofinal_sourceAdaptive_parabolicFrontierCertificate_of_not_riemannHypothesis hnot A
  obtain ⟨b, hb, hintegrable⟩ := hregular n hne hA hstrict
  exact
    (not_intervalIntegrable_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
      hne hstrict hb) hintegrable

/-- **Ultraviolet tail criterion.** RH is equivalent to eventual local `L¹` regularity of exact
source walls; no regularity is required at any bounded collection of infrared frontiers. -/
theorem riemannHypothesis_iff_xiShiftedChristoffelSourceWallEventuallyLocallyIntegrable :
    RiemannHypothesis ↔
      XiShiftedChristoffelSourceWallEventuallyLocallyIntegrable := by
  constructor
  · exact xiShiftedChristoffelSourceWallEventuallyLocallyIntegrable_of_riemannHypothesis
  · intro hregular
    by_contra hnotRH
    exact
      (not_xiShiftedChristoffelSourceWallEventuallyLocallyIntegrable_of_not_riemannHypothesis
        hnotRH) hregular

end

end RHTower
