import GaloisForLFunctions.HTGeometry.CertificateGenealogyTailRealization
import GaloisForLFunctions.HTGeometry.PositiveScalarCertificateOperator

/-! # Arbitrary admissible completed-tail profiles on the original fibre

Every strictly decreasing profile with boundary one occurs on `FibSeq 1`, with
the genealogy's proven infinite compact-ideal cost. The canonical realization
has positive scalar coefficients; every other realization is its normalized
unitary phase conjugate on the full original carrier.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology
open scoped ENNReal ComplexConjugate

private theorem tail_strictAnti (a : OpCertStream 1) (ha : IsHilbertSchmidt (1 - a.genealogy)) :
    StrictAnti (paperCertificateTailValue a) := by
  have h := (paperCertificateTailRecovery_iff a).mpr ha
  apply strictAnti_nat_of_succ_lt
  intro n
  have hd := (h.1 n).2.1
  have he := (eq_div_iff (by linarith :
    2 * paperCertificateTailValue a (n + 1) - paperCertificateTailValue a (n + 2) ≠ 0)).mp
      (h.1 n).2.2
  have hc := norm_pos_iff.mpr (scalarCertificateCoefficient_ne_zero a n)
  have hp := mul_pos (sq_pos_of_pos hc) (show
    0 < 2 * paperCertificateTailValue a (n + 1) - paperCertificateTailValue a (n + 2) by linarith)
  nlinarith

def paperCertificateOfTailProfile (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) : OpCertStream 1 :=
  scalarCertificateOperator (certificateOfTailProfile Z hZ hlim)

theorem paperCertificateOfTailProfile_coefficient (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) (n : ℕ) :
    scalarCertificateCoefficient (paperCertificateOfTailProfile Z hZ hlim) n =
      (genealogyProfileCoefficient Z n : ℂ) :=
  scalarCertificateOperator_coefficient _ n

theorem paperCertificateOfTailProfile_genealogy (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    (paperCertificateOfTailProfile Z hZ hlim).genealogy =
      RHTower.unitaryPush scalarCertificateCoordinates.symm (certificateOfTailProfile Z hZ hlim).genealogy :=
  scalarCertificateOperator_genealogy _

theorem paperCertificateOfTailProfile_hilbertSchmidt (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    IsHilbertSchmidt (1 - (paperCertificateOfTailProfile Z hZ hlim).genealogy) :=
  (scalarCertificateOperator_hilbertSchmidt_iff _).mpr
    (certificateOfTailProfile_hilbertSchmidt Z hZ hlim)

theorem paperCertificateOfTailProfile_realizes (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    paperCertificateTailValue (paperCertificateOfTailProfile Z hZ hlim) = Z := by
  funext n
  rw [paperCertificateOfTailProfile, scalarCertificateOperator_tailValue,
    certificateOfTailProfile_realizes]

theorem paperCertificateOfTailProfile_infiniteCost (Z : ℕ → ℝ) (hZ : StrictAnti Z)
    (hlim : Tendsto Z atTop (𝓝 1)) :
    compactOperatorTraceCost (FibSeq 1) (paperCertificateOfTailProfile Z hZ hlim).genealogy = ∞ ∧
      IsHilbertSchmidt (1 - (paperCertificateOfTailProfile Z hZ hlim).genealogy) ∧
      paperCertificateTailValue (paperCertificateOfTailProfile Z hZ hlim) = Z :=
  ⟨compactOperatorTraceCost_genealogy 0 _, paperCertificateOfTailProfile_hilbertSchmidt Z hZ hlim,
    paperCertificateOfTailProfile_realizes Z hZ hlim⟩

theorem paperCertificateTailProfile_iff (Z : ℕ → ℝ) :
    (∃ a : OpCertStream 1, compactOperatorTraceCost (FibSeq 1) a.genealogy = ∞ ∧
      IsHilbertSchmidt (1 - a.genealogy) ∧ paperCertificateTailValue a = Z) ↔
      StrictAnti Z ∧ Tendsto Z atTop (𝓝 1) := by
  constructor
  · rintro ⟨a, _, ha, rfl⟩
    exact ⟨tail_strictAnti a ha, ((paperCertificateTailRecovery_iff a).mpr ha).2⟩
  · rintro ⟨hZ, hlim⟩
    exact ⟨paperCertificateOfTailProfile Z hZ hlim,
      paperCertificateOfTailProfile_infiniteCost Z hZ hlim⟩

theorem paperCertificateTailProfile_unique_iff (Z : ℕ → ℝ) :
    (∃ a : OpCertStream 1, compactOperatorTraceCost (FibSeq 1) a.genealogy = ∞ ∧
      IsHilbertSchmidt (1 - a.genealogy) ∧ paperCertificateTailValue a = Z ∧
      (∀ n, scalarCertificateCoefficient a n = (genealogyProfileCoefficient Z n : ℂ)) ∧
      ∀ b : OpCertStream 1, IsHilbertSchmidt (1 - b.genealogy) → paperCertificateTailValue b = Z →
        ∃ (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1), u 0 = 1 ∧
          (∀ n, scalarCertificateCoefficient b n =
            u n * scalarCertificateCoefficient a n * conj (u (n + 1))) ∧
          b.genealogy = RHTower.unitaryPush (scalarCertificatePhaseUnitary u hu) a.genealogy) ↔
      StrictAnti Z ∧ Tendsto Z atTop (𝓝 1) := by
  constructor
  · rintro ⟨a, hc, ha, he, _⟩
    exact (paperCertificateTailProfile_iff Z).mp ⟨a, hc, ha, he⟩
  · rintro ⟨hZ, hlim⟩
    let a := paperCertificateOfTailProfile Z hZ hlim
    obtain ⟨hc, ha, he⟩ := paperCertificateOfTailProfile_infiniteCost Z hZ hlim
    refine ⟨a, hc, ha, he, paperCertificateOfTailProfile_coefficient Z hZ hlim, ?_⟩
    intro b hb hbe
    exact ((paperCertificateTailValue_eq_iff_phaseGauge a b).mp
      ⟨ha, hb, fun k => congrFun (he.trans hbe.symm) k⟩).2

end
end GaloisForLFunctions.HTGeometry
