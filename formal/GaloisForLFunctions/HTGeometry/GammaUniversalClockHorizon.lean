import GaloisForLFunctions.HTGeometry.GammaIrreversibleClockHorizon
import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchProductDensity

/-!
# Algebraically universal clocks on the irreversible Gamma horizon

The dimension-zero constrained horizon has more than symbolic capacity.  At each permitted pole
label, attach the complete normalized formal inverse-Gamma branch jet.  Every finite legal block
of clock depths is Zariski detecting at every finite jet resolution: no nonzero mixed polynomial
observable vanishes on all legal blocks.

Unlike the earlier representative-parametrized density statements, this file chooses an actual
representative of each pole-index germ by `Quotient.out`.  The terminal theorem is therefore
unconditional.  The same legal finite pole words extend to points of the actual analytic Baire
horizon, whose Gamma dynamics and dimension were proved in the imported modules.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- A fixed sequence representative of every normalized inverse-Gamma branch coefficient germ. -/
def gammaInversePoleBranchCoefficientSequence (j : Nat) : Nat -> Complex :=
  (gammaInversePoleBranchCoefficientGerm j).out

theorem gammaInversePoleBranchCoefficientSequence_germ (j : Nat) :
    (gammaInversePoleBranchCoefficientSequence j : NatGerm) =
      gammaInversePoleBranchCoefficientGerm j := by
  exact Quotient.out_eq _

/-- Variable blocks for `d+1` finite clock depths, each with `m` jet coordinates. -/
def GammaHorizonJetVariables (m : Nat) : Nat -> Type
  | 0 => Fin m
  | d + 1 => GammaHorizonJetVariables m d ⊕ Fin m

/-- Legal pole words for `d+1` clock depths.  The label at depth `k` is constrained to be at
least `gammaThinSchedule k`. -/
def GammaHorizonPoleWords : Nat -> Type
  | 0 => {n : Nat // gammaThinSchedule 0 <= n}
  | d + 1 => GammaHorizonPoleWords d × {n : Nat // gammaThinSchedule (d + 1) <= n}

/-- Evaluation of all normalized inverse-branch clock jets on a finite legal pole word. -/
def gammaHorizonJetEvaluation (m : Nat) :
    (d : Nat) -> GammaHorizonJetVariables m d -> GammaHorizonPoleWords d -> Complex
  | 0, j, n => gammaInversePoleBranchCoefficientSequence
      ((show Fin m from j) : Nat)
      (show {a : Nat // gammaThinSchedule 0 <= a} from n).1
  | d + 1, q, w =>
      Sum.elim
        (fun i => gammaHorizonJetEvaluation m d i w.1)
        (fun j : Fin m => gammaInversePoleBranchCoefficientSequence (j : Nat) w.2) q

/-- Every finite legal Gamma clock block detects every nonzero mixed polynomial observable. -/
theorem gammaHorizonJetEvaluation_zariskiDetecting (m : Nat) :
    forall d, ZariskiDetectingFamily (gammaHorizonJetEvaluation m d) := by
  intro d
  induction d with
  | zero =>
      have hcofinal := gammaInversePoleBranchCoefficient_fin_cofinallyZariskiDense
        m gammaInversePoleBranchCoefficientSequence
        gammaInversePoleBranchCoefficientSequence_germ
      simpa [gammaHorizonJetEvaluation, GammaHorizonPoleWords,
        GammaHorizonJetVariables] using
          hcofinal.zariskiDetectingFamily_tail (gammaThinSchedule 0)
  | succ d ih =>
      have hcofinal := gammaInversePoleBranchCoefficient_fin_cofinallyZariskiDense
        m gammaInversePoleBranchCoefficientSequence
        gammaInversePoleBranchCoefficientSequence_germ
      have hlast := hcofinal.zariskiDetectingFamily_tail (gammaThinSchedule (d + 1))
      simpa [gammaHorizonJetEvaluation, GammaHorizonPoleWords,
        GammaHorizonJetVariables] using ih.sum hlast

/-- Extend a finite legal pole word to a literal Baire history on the analytic Gamma horizon. -/
def gammaHorizonPoleWordExtension :
    (d : Nat) -> GammaHorizonPoleWords d -> Nat -> Nat
  | 0, w => fun k => if k = 0 then
      (show {n : Nat // gammaThinSchedule 0 <= n} from w).1 - gammaThinSchedule 0 else 0
  | d + 1, w => Function.update (gammaHorizonPoleWordExtension d w.1) (d + 1)
      ((w.2 : Nat) - gammaThinSchedule (d + 1))

/-- The final pole label stored in a nonempty finite legal word. -/
def gammaHorizonPoleWordLast :
    (d : Nat) -> GammaHorizonPoleWords d -> Nat
  | 0, w => (show {n : Nat // gammaThinSchedule 0 <= n} from w).1
  | _d + 1, w => w.2.1

/-- The extension realizes the last prescribed pole label exactly. -/
theorem gammaCodeLabel_gammaHorizonPoleWordExtension_last :
    forall d (w : GammaHorizonPoleWords d),
      gammaCodeLabel gammaThinSchedule (gammaHorizonPoleWordExtension d w) d =
        gammaHorizonPoleWordLast d w := by
  intro d w
  cases d with
  | zero =>
      simp [gammaCodeLabel, gammaHorizonPoleWordExtension,
        gammaHorizonPoleWordLast,
        Nat.add_sub_of_le w.property]
  | succ d =>
      simp [gammaCodeLabel, gammaHorizonPoleWordExtension,
        gammaHorizonPoleWordLast,
        Nat.add_sub_of_le w.2.property]

/-- Every finite legal clock word therefore decorates an actual point of the analytic constrained
Gamma horizon. -/
theorem gammaBaireCode_poleWordExtension_mem
    (d : Nat) (w : GammaHorizonPoleWords d) :
    gammaBaireCode gammaThinSchedule (gammaHorizonPoleWordExtension d w) ∈
      gammaConstrainedHorizon := by
  exact ⟨gammaHorizonPoleWordExtension d w, rfl⟩

/-- **Dimension-zero algebraically universal irreversible Gamma horizon.**  At arbitrary positive
finite depth and arbitrary finite inverse-jet resolution, every nonzero mixed polynomial is
detected by a legal pole word which extends to an actual point of the Hausdorff-dimension-zero,
aperiodic Gamma horizon. -/
theorem gamma_dimensionZero_algebraicallyUniversal_irreversibleClockHorizon
    (m d : Nat) (P : MvPolynomial (GammaHorizonJetVariables m d) Complex) (hP : P ≠ 0) :
    dimH gammaConstrainedHorizon = 0 ∧
      (exists w : GammaHorizonPoleWords d,
        MvPolynomial.eval (fun q => gammaHorizonJetEvaluation m d q w) P ≠ 0 ∧
          gammaBaireCode gammaThinSchedule (gammaHorizonPoleWordExtension d w) ∈
            gammaConstrainedHorizon) ∧
      (∀ z ∈ gammaConstrainedHorizon, ∀ r, 0 < r ->
        (Complex.Gamma^[r]) z ≠ z) ∧
      (⋂ r : Nat, (Complex.Gamma^[r]) '' gammaConstrainedHorizon) = ∅ := by
  have hdetect := gammaHorizonJetEvaluation_zariskiDetecting m d P hP
  obtain ⟨w, hw⟩ := hdetect
  exact ⟨dimH_gammaConstrainedHorizon,
    ⟨w, hw, gammaBaireCode_poleWordExtension_mem d w⟩,
    fun _z hz _r hr => Gamma_iterate_ne_self_on_gammaConstrainedHorizon hz hr,
    iInter_Gamma_iterate_image_gammaConstrainedHorizon_eq_empty⟩

end

end GaloisForLFunctions
