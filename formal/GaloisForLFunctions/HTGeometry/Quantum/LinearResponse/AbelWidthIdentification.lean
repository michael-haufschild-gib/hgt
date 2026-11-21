import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardProbeGeneric
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelWidthCalibration
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelWidthScaling
import GaloisForLFunctions.HTGeometry.ShellCoeffScaling

/-!
# Identifying a Hamiltonian at an unknown damping width

The two zero-centered readings recover the Hamiltonian modulo a
common width rescaling and an energy shift. A single off-center trace
then fixes the width, removing the scale ambiguity.
-/

open Matrix Set MeasureTheory
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d N : ℕ}

/-- At an unknown width the two fixed probes determine the scaled Hamiltonian.
The exceptional set is independent of the competing Hamiltonian and width. -/
theorem ae_abelForwardReadings_eq_iff_rescale_sub_scalar (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, (P a).IsHermitian) :
    ∀ᵐ θ : Fin N → ℝ ∂volume,
      ∀ (η : Ioi (0 : ℝ)) (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian),
        let hH := isHermitian_spectralEnsembleMatrix hP θ
        (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
            hamiltonianDampedGapResponse hK 0 η (abelDiagonalProbe d) ∧
          hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
            hamiltonianDampedGapResponse hK 0 η (abelSumProbe d)) ↔
          ∃ r : ℝ, spectralEnsembleMatrix P θ - abelHamiltonianAtWidth K η ε = (r : ℂ) • 1 := by
  filter_upwards [ae_abelForwardReadings_eq_iff_scalarDifference o ε P hP] with θ hθ
  intro η K hK
  dsimp only
  rw [← abelResponse_rescale_width hK η ε]
  exact (hθ _ (abelHamiltonianAtWidth_isHermitian hK η ε)).trans
    (hermitian_scalarDifference_iff_real o (isHermitian_spectralEnsembleMatrix hP θ)
      (abelHamiltonianAtWidth_isHermitian hK η ε))

/-- Two zero-centered outputs and the width calibration trace. -/
def abelCalibratedReadings (o : Fin d) {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) × ℂ :=
  ((hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d),
    hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)),
    (hamiltonianDampedGapResponse hH 1 ε (Matrix.single o o 1)).trace)

/-- The calibrated experiment determines the width and the Hamiltonian
up to a real scalar shift, for almost every coupling vector. -/
theorem ae_abelCalibratedReadings_eq_iff (o : Fin d) (ε : Ioi (0 : ℝ))
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, (P a).IsHermitian) :
    ∀ᵐ θ : Fin N → ℝ ∂volume,
      ∀ (η : Ioi (0 : ℝ)) (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian),
        abelCalibratedReadings o (isHermitian_spectralEnsembleMatrix hP θ) ε =
            abelCalibratedReadings o hK η ↔
          ε = η ∧ ∃ r : ℝ, spectralEnsembleMatrix P θ - K = (r : ℂ) • 1 := by
  filter_upwards [ae_abelForwardReadings_eq_iff_scalarDifference o ε P hP] with θ hθ
  intro η K hK
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  constructor
  · intro h
    have hwidth := (abelCalibrationTrace_eq_iff o hH hK ε η).mp (congrArg Prod.snd h)
    subst η
    have hz := congrArg Prod.fst h
    exact ⟨rfl, (hermitian_scalarDifference_iff_real o hH hK).mp
      ((hθ K hK).mp ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩)⟩
  · rintro ⟨rfl, hr⟩
    have hp := (hθ K hK).mpr ((hermitian_scalarDifference_iff_real o hH hK).mpr hr)
    exact Prod.ext (Prod.ext hp.1 hp.2) ((abelCalibrationTrace_eq_iff o hH hK ε ε).mpr rfl)

/-- Without calibration, the nearest-neighbor Pauli readings determine
every coupling divided by the damping width. -/
theorem ae_pauliAbelForwardReadings_eq_iff_div_width (n : ℕ) (ε : Ioi (0 : ℝ)) :
    ∀ᵐ θ : Fin (Fintype.card (ChainLabel n)) → ℝ ∂volume,
      ∀ η (α : Fin (Fintype.card (ChainLabel n)) → ℝ),
        let response := fun β : Fin (Fintype.card (ChainLabel n)) → ℝ =>
          hamiltonianDampedGapResponse
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) β) 0
        (response θ ε (abelDiagonalProbe (2 ^ n)), response θ ε (abelSumProbe (2 ^ n))) =
          (response α η (abelDiagonalProbe (2 ^ n)), response α η (abelSumProbe (2 ^ n))) ↔
          ∀ i, θ i / (ε : ℝ) = α i / (η : ℝ) := by
  filter_upwards [ae_pauliAbelForwardReadings_eq_iff n ε] with θ hθ
  intro η α
  dsimp only
  let o : Fin (2 ^ n) := ⟨0, by positivity⟩
  let s := (ε : ℝ) / (η : ℝ)
  let β := fun i => s * α i
  let hα := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) α
  let hβ := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) β
  let hR := abelHamiltonianAtWidth_isHermitian hα η ε
  have hscale : spectralEnsembleMatrix (chainPauliFin n) β =
      abelHamiltonianAtWidth (spectralEnsembleMatrix (chainPauliFin n) α) η ε :=
    spectralEnsembleMatrix_smul (chainPauliFin n) s α
  have hsame := (hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference o hβ hR ε).mpr
    ⟨0, by rw [hscale, sub_self, zero_smul]⟩
  have hresponse : hamiltonianDampedGapResponse hβ 0 ε = hamiltonianDampedGapResponse hα 0 η :=
    hsame.trans (abelResponse_rescale_width hα η ε)
  rw [← hresponse]
  refine (hθ β).trans ?_
  have hε : (ε : ℝ) ≠ 0 := (show 0 < (ε : ℝ) from ε.2).ne'
  have hr (i : Fin (Fintype.card (ChainLabel n))) : β i / (ε : ℝ) = α i / (η : ℝ) := by
    apply (div_eq_iff hε).mpr
    simp only [β, s, div_eq_mul_inv]
    ring
  constructor
  · intro h i
    rw [h, hr]
  · intro h
    funext i
    calc
      θ i = (θ i / (ε : ℝ)) * (ε : ℝ) := (div_mul_cancel₀ _ hε).symm
      _ = (β i / (ε : ℝ)) * (ε : ℝ) := by rw [h i, hr i]
      _ = β i := div_mul_cancel₀ _ hε

/-- For the nearest-neighbor Pauli family the calibrated readings
determine both the width and the entire coupling vector. -/
theorem ae_pauliAbelCalibratedReadings_eq_iff (n : ℕ) (ε : Ioi (0 : ℝ)) :
    ∀ᵐ θ : Fin (Fintype.card (ChainLabel n)) → ℝ ∂volume,
      ∀ η (α : Fin (Fintype.card (ChainLabel n)) → ℝ),
        let o : Fin (2 ^ n) := ⟨0, by positivity⟩
        abelCalibratedReadings o
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ) ε =
          abelCalibratedReadings o
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) α) η ↔
          (ε, θ) = (η, α) := by
  filter_upwards [ae_pauliAbelForwardReadings_eq_iff n ε] with θ hθ
  intro η α
  let o : Fin (2 ^ n) := ⟨0, by positivity⟩
  let hH := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ
  let hK := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) α
  change abelCalibratedReadings o hH ε = abelCalibratedReadings o hK η ↔ _
  constructor
  · intro h
    have hwidth := (abelCalibrationTrace_eq_iff o hH hK ε η).mp (congrArg Prod.snd h)
    subst η
    exact Prod.ext rfl ((hθ α).mp (congrArg Prod.fst h))
  · intro h
    have hwidth : ε = η := congrArg Prod.fst h
    have hc : θ = α := congrArg Prod.snd h
    subst η
    subst α
    rfl

#print axioms ae_abelForwardReadings_eq_iff_rescale_sub_scalar
#print axioms ae_abelCalibratedReadings_eq_iff
#print axioms ae_pauliAbelForwardReadings_eq_iff_div_width
#print axioms ae_pauliAbelCalibratedReadings_eq_iff

end

end GaloisForLFunctions.HTGeometry
