import GaloisForLFunctions.HTGeometry.RankOneDifferenceBoundaryTomography
import GaloisForLFunctions.HTGeometry.SharedClockRankOneRigidity

/-!
# Projective calibration of a rank-one coefficient jet

The boundary-current tower for a scalar difference coefficient has a source-specific incoming
covector and a universal factorial-tail outgoing vector.  General rank-one factorization rigidity
therefore leaves exactly one calibration scalar.  Evaluating the calibrated source factor on the
coordinate probes recovers every visible positive coefficient derivative with that same scalar.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every nonzero factorization of one coefficient boundary current differs from its canonical
incoming-covector/factorial-tail factorization by one unique global scalar. -/
theorem rankOneCoefficientPairedBoundaryCurrent_factorization_unique_up_to_scale
    (c : ℕ → ℂ) (n : ℕ) (k : Fin (n + 1))
    (hck : c (n + 1 - (k : ℕ)) ≠ 0)
    (source : (Fin (n + 1) → ℂ) → ℂ) (boundary : Fin (n + 1) → ℂ)
    (hfactor : ∀ a i,
      rankOneCoefficientPairedBoundaryCurrent c n a i = source a * boundary i) :
    ∃! lambda : ℂ, lambda ≠ 0 ∧
      source = (fun a ↦ lambda * rankOneCoefficientIncomingCovector c n a) ∧
      boundary = (fun i ↦ lambda⁻¹ * gammaClockBoundaryVector (n + 1) i) := by
  have hincoming :
      rankOneCoefficientIncomingCovector c n (Pi.single k 1) ≠ 0 := by
    rw [rankOneCoefficientIncomingCovector_single]
    apply mul_ne_zero
    · exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt k.isLt)
    · exact hck
  have hboundary : gammaClockBoundaryVector (n + 1) (Fin.last n) ≠ 0 := by
    simp [gammaClockBoundaryVector, Nat.factorial_ne_zero]
  apply sharedClockObservation_factorization_unique_up_to_scale
    (rankOneCoefficientIncomingCovector c n) source
    (gammaClockBoundaryVector (n + 1)) boundary
    (Pi.single k 1) (Fin.last n) hincoming hboundary
  funext a i
  simp only [sharedClockObservation]
  calc
    rankOneCoefficientIncomingCovector c n a * gammaClockBoundaryVector (n + 1) i =
        rankOneCoefficientPairedBoundaryCurrent c n a i := by
      symm
      exact congrFun (rankOneCoefficientPairedBoundaryCurrent_eq_outerProduct c n a) i
    _ = source a * boundary i := hfactor a i

/-- **Projective coefficient-jet calibration law.**  An arbitrary nonzero separation of the
rank-one boundary current determines the entire visible positive coefficient jet up to one—and
only one—global scalar, which simultaneously calibrates the universal outgoing response. -/
theorem rankOneCoefficientPairedBoundaryCurrent_projectiveJetCalibration
    (c : ℕ → ℂ) (n : ℕ) (k : Fin (n + 1))
    (hck : c (n + 1 - (k : ℕ)) ≠ 0)
    (source : (Fin (n + 1) → ℂ) → ℂ) (boundary : Fin (n + 1) → ℂ)
    (hfactor : ∀ a i,
      rankOneCoefficientPairedBoundaryCurrent c n a i = source a * boundary i) :
    ∃! lambda : ℂ, lambda ≠ 0 ∧
      source = (fun a ↦ lambda * rankOneCoefficientIncomingCovector c n a) ∧
      boundary = (fun i ↦ lambda⁻¹ * gammaClockBoundaryVector (n + 1) i) ∧
      ∀ j : Fin (n + 1),
        source (Pi.single j 1) =
          lambda *
            (((Nat.choose (n + 1) (j : ℕ) : ℕ) : ℂ) *
              c (n + 1 - (j : ℕ))) := by
  obtain ⟨lambda, hlambda, hunique⟩ :=
    rankOneCoefficientPairedBoundaryCurrent_factorization_unique_up_to_scale
      c n k hck source boundary hfactor
  refine ⟨lambda, ⟨hlambda.1, hlambda.2.1, hlambda.2.2, ?_⟩, ?_⟩
  · intro j
    rw [hlambda.2.1, rankOneCoefficientIncomingCovector_single]
  · intro mu hmu
    exact hunique mu ⟨hmu.1, hmu.2.1, hmu.2.2.1⟩

end

end GaloisForLFunctions.HTGeometry
