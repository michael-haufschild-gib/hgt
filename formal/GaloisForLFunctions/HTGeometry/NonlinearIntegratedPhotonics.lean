import GaloisForLFunctions.HTGeometry.FiniteModalHadamardAlgebra
import GaloisForLFunctions.HTGeometry.FiniteTemporalCascadeStabilizationLaw
import GaloisForLFunctions.HTGeometry.InfiniteTemporalCascadeWitness
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Algebraic nonlinear optics on sampled modal carriers

This module isolates exact algebraic structures shared by nonlinear optical
models.  A lossless scalar Kerr response applies an intensity-dependent phase
and therefore preserves amplitude norm; composition accumulates its nonlinear
phase.  Sampled carriers are closed under third powers and under the
conjugated triple product used by four-wave mixing.  A cubic response to a
finite modal packet has a finite presentation of width at most `d^(3 : ℕ)`.

The final two theorems state the finite-versus-countable cascade dichotomy in
the temporal-spectrum formalism.  They are structural analogues of finite
fission and unbounded sideband cascades, not claims about a propagation model:
dispersion, loss, phase matching, and nonlinear gain are not represented here.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Lossless scalar Kerr phase response with real nonlinear coupling. -/
def opticalKerrPhaseShift (coupling : ℝ) (amplitude : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((coupling * ‖amplitude‖ ^ (2 : ℕ) : ℝ) : ℂ)) * amplitude

/-- A lossless scalar Kerr phase shift preserves optical amplitude norm exactly. -/
theorem norm_opticalKerrPhaseShift (coupling : ℝ) (amplitude : ℂ) :
    ‖opticalKerrPhaseShift coupling amplitude‖ = ‖amplitude‖ := by
  unfold opticalKerrPhaseShift
  rw [Complex.norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

/-- Cascaded Kerr sections add their nonlinear phases. -/
theorem opticalKerrPhaseShift_compose (coupling₁ coupling₂ : ℝ) (amplitude : ℂ) :
    opticalKerrPhaseShift coupling₂ (opticalKerrPhaseShift coupling₁ amplitude) =
      opticalKerrPhaseShift (coupling₁ + coupling₂) amplitude := by
  change Complex.exp (Complex.I *
      ((coupling₂ * ‖opticalKerrPhaseShift coupling₁ amplitude‖ ^ (2 : ℕ) : ℝ) : ℂ)) *
      opticalKerrPhaseShift coupling₁ amplitude =
    opticalKerrPhaseShift (coupling₁ + coupling₂) amplitude
  rw [norm_opticalKerrPhaseShift]
  unfold opticalKerrPhaseShift
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A sampled complex carrier with modal amplitude and node. -/
def opticalCarrier (amplitude node : ℂ) (n : ℕ) : ℂ := amplitude * node ^ n

/-- Multiplication of sampled carriers forms their combination carrier. -/
theorem opticalCarrier_mul (a p b q : ℂ) (n : ℕ) :
    opticalCarrier a p n * opticalCarrier b q n = opticalCarrier (a * b) (p * q) n := by
  unfold opticalCarrier
  rw [mul_pow]
  ring

/-- Cubing a sampled carrier produces its third-harmonic carrier. -/
theorem opticalCarrier_thirdHarmonic (a p : ℂ) (n : ℕ) :
    opticalCarrier a p n ^ (3 : ℕ) = opticalCarrier (a ^ (3 : ℕ)) (p ^ (3 : ℕ)) n := by
  unfold opticalCarrier
  rw [mul_pow]
  ring

/-- Complex conjugation sends a carrier to its conjugate amplitude and node. -/
theorem star_opticalCarrier (a p : ℂ) (n : ℕ) :
    star (opticalCarrier a p n) = opticalCarrier (star a) (star p) n := by
  simp [opticalCarrier]

/-- A conjugated triple product obeys the four-wave-mixing carrier rule. -/
theorem opticalCarrier_fourWaveMix (a p b q c r : ℂ) (n : ℕ) :
    opticalCarrier a p n * opticalCarrier b q n * star (opticalCarrier c r n) =
      opticalCarrier (a * b * star c) (p * q * star r) n := by
  rw [star_opticalCarrier, opticalCarrier_mul, opticalCarrier_mul]

/-- The sampled sum of two optical carriers. -/
def opticalTwoTone (a p b q : ℂ) (n : ℕ) : ℂ :=
  opticalCarrier a p n + opticalCarrier b q n

/-- Cubic response of two tones contains the two self and two mixed sidebands. -/
theorem opticalTwoTone_cubic_sidebands (a p b q : ℂ) (n : ℕ) :
    opticalTwoTone a p b q n ^ (3 : ℕ) =
      opticalCarrier a p n ^ (3 : ℕ) +
        3 * opticalCarrier a p n ^ (2 : ℕ) * opticalCarrier b q n +
        3 * opticalCarrier a p n * opticalCarrier b q n ^ (2 : ℕ) +
        opticalCarrier b q n ^ (3 : ℕ) := by
  unfold opticalTwoTone
  ring

/-- Cubic modal amplitudes, indexed by three successive pair-product maps. -/
def finiteModalCubicWeight {d : ℕ} (weight : Fin d → ℂ) : Fin ((d * d) * d) → ℂ :=
  finiteModalProductWeight (finiteModalProductWeight weight weight) weight

/-- Cubic modal nodes, indexed by three successive pair-product maps. -/
def finiteModalCubicNode {d : ℕ} (node : Fin d → ℂ) : Fin ((d * d) * d) → ℂ :=
  finiteModalProductNode (finiteModalProductNode node node) node

/-- The exact cubic response of a finite modal packet is a finite modal packet. -/
theorem finiteModalSequence_cube (weight node : Fin d → ℂ) (n : ℕ) :
    finiteModalSequence weight node n ^ (3 : ℕ) =
      finiteModalSequence (finiteModalCubicWeight weight) (finiteModalCubicNode node) n := by
  rw [pow_three, finiteModalSequence_mul weight node weight node n,
    mul_comm (finiteModalSequence weight node n),
    finiteModalSequence_mul (finiteModalProductWeight weight weight)
      (finiteModalProductNode node node) weight node n]
  rfl

/-- A `d`-mode packet has a cubic sideband presentation of width at most `d^(3 : ℕ)`. -/
theorem finiteModalSequence_cube_width (weight node : Fin d → ℂ) :
    FiniteModalWidthAtMost ((d * d) * d)
      (fun n => finiteModalSequence weight node n ^ (3 : ℕ)) := by
  refine ⟨finiteModalCubicWeight weight, finiteModalCubicNode node, ?_⟩
  funext n
  exact finiteModalSequence_cube weight node n

/-- Every finite temporal spectrum reaches a stable cubic-fission constraint layer. -/
theorem finiteSpectrum_cubicFission_stabilizes {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    ∃ R : ℕ, ∀ s, R ≤ s →
      GaloisForLFunctions.HTGeometry.temporalDimension jet s =
        GaloisForLFunctions.HTGeometry.temporalDimension jet R :=
  GaloisForLFunctions.HTGeometry.exists_temporalDimension_stabilization jet

/-- A countable analytic sideband cascade has a distinct positive birth order at every level. -/
theorem countableSidebandCascade_no_terminal (b : ℕ) :
    GaloisForLFunctions.HTGeometry.HasPositiveBirthProfile
      (fun g =>
        |GaloisForLFunctions.HTGeometry.infiniteTorusCharacterDetuning
          (GaloisForLFunctions.HTGeometry.infiniteTemporalCascadeCharacter b)
          (GaloisForLFunctions.HTGeometry.infiniteTemporalCascadeFrequency g)|)
      (b + 1) 1 :=
  GaloisForLFunctions.HTGeometry.infiniteTemporalCascadeCharacter_birthProfile b

end

end HTGeometry
