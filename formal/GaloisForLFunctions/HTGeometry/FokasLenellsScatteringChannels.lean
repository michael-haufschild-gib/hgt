import GaloisForLFunctions.HTGeometry.FokasLenellsReflection
import GaloisForLFunctions.HTGeometry.Arxiv2607PiecewiseSymmetric
import GaloisForLFunctions.HTGeometry.RepresentationFracture
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.InteractionCrossFibre

/-!
# Scattering symmetry channels across the Lean corpus

The reverse-space symmetry in arXiv:2607.19649 produces an actual matrix
involution from the scattering data of every Schwartz potential at positive
real spectral parameter. This file applies existing results from:

* `Arxiv2607PiecewiseSymmetric`: unique complementary symmetry channels;
* `RepresentationFracture`: idempotent projections and their exact rank;
* `QuantumAlg.Util.MatrixExpInvolution` and `ConstraintRelativity.InteractionCrossFibre`:
  exact hyperbolic and trigonometric operator exponentials.

Both projections have complex rank one. The exponential acts by `exp z` and
`exp (-z)` on the two channels. These are algebraic flows of the constructed
scattering involution; they are not identified with the nonlinear PDE's time evolution.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


def scatteringInvolution (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  scatteringMatrix q κ*swapMatrix

theorem scatteringInvolution_mul_self (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    scatteringInvolution q κ*scatteringInvolution q κ = 1 := by
  simpa only [scatteringInvolution, pow_two] using scattering_swap_involution q κ

def scatteringChannelEnd (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := (scatteringInvolution q κ).toLin'

theorem scatteringChannelEnd_involutive (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    scatteringChannelEnd q κ (scatteringChannelEnd q κ v) = v := by
  have h := congrArg Matrix.toLin' (scatteringInvolution_mul_self q κ)
  rw [Matrix.toLin'_mul, Matrix.toLin'_one] at h
  exact congrArg (fun f => f v) h

/-- Canonical positive and negative scattering channels reuse the corpus's tensor splitting. -/
def positiveScatteringChannel (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  involutionSymPart (scatteringChannelEnd q κ) v

def negativeScatteringChannel (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  involutionAltPart (scatteringChannelEnd q κ) v

theorem scattering_channels_reconstruct (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    positiveScatteringChannel q κ v + negativeScatteringChannel q κ v = v :=
  involution_sym_add_alt (scatteringChannelEnd q κ) v

theorem positiveScatteringChannel_fixed (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    scatteringChannelEnd q κ (positiveScatteringChannel q κ v) = positiveScatteringChannel q κ v :=
  involutionSymPart_fixed _ (scatteringChannelEnd_involutive q κ) v

theorem negativeScatteringChannel_negated (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    scatteringChannelEnd q κ (negativeScatteringChannel q κ v) = -negativeScatteringChannel q κ v :=
  involutionAltPart_antiFixed _ (scatteringChannelEnd_involutive q κ) v

/-- Every incoming vector has exactly one decomposition into the two scattering characters. -/
theorem scattering_channel_split_existsUnique (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    ∃! p : (Fin 2 → ℂ) × (Fin 2 → ℂ),
      v = p.1 + p.2 ∧ scatteringChannelEnd q κ p.1 = p.1 ∧
        scatteringChannelEnd q κ p.2 = -p.2 := by
  refine ⟨(positiveScatteringChannel q κ v, negativeScatteringChannel q κ v),
    ⟨(scattering_channels_reconstruct q κ v).symm,
      positiveScatteringChannel_fixed q κ v, negativeScatteringChannel_negated q κ v⟩, ?_⟩
  intro p hp
  have h := involution_split_unique (scatteringChannelEnd q κ) hp.1 hp.2.1 hp.2.2
  exact Prod.ext h.1.symm h.2.symm

theorem scattering_channel_subspaces_complementary (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    IsCompl (involutionFixedSubmodule (scatteringChannelEnd q κ))
      (involutionAntiFixedSubmodule (scatteringChannelEnd q κ)) :=
  involution_fixed_isCompl_antiFixed _ (scatteringChannelEnd_involutive q κ)

/-- The negative-channel projection from the representation-fracture corpus. -/
def scatteringNegativeProjection (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  involutionProjection (scatteringInvolution q κ)

theorem scatteringNegativeProjection_idempotent (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    IsIdempotentElem (scatteringNegativeProjection q κ) :=
  involutionProjection_isIdempotent _ (scatteringInvolution_mul_self q κ)

theorem scatteringNegativeProjection_trace (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringNegativeProjection q κ).trace = 1 := by
  rw [scatteringNegativeProjection, involutionProjection, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_one, scatteringInvolution, scattering_swap_trace]
  simp

/-- The negative symmetry channel has complex dimension one. -/
theorem scatteringNegativeProjection_rank_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Module.finrank ℂ (LinearMap.range (scatteringNegativeProjection q κ).toLin') = 1 := by
  have h := involutionProjection_trace_eq_finrank _ (scatteringInvolution_mul_self q κ)
  change (scatteringNegativeProjection q κ).trace = _ at h
  rw [scatteringNegativeProjection_trace] at h
  exact_mod_cast h.symm

/-- The positive channel is the negative projection of the opposite involution. -/
def scatteringPositiveProjection (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  involutionProjection (-scatteringInvolution q κ)

theorem scatteringPositiveProjection_idempotent (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    IsIdempotentElem (scatteringPositiveProjection q κ) :=
  involutionProjection_isIdempotent _ (by simpa using scatteringInvolution_mul_self q κ)

theorem scatteringPositiveProjection_trace (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (scatteringPositiveProjection q κ).trace = 1 := by
  rw [scatteringPositiveProjection, involutionProjection, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_one, Matrix.trace_neg, scatteringInvolution, scattering_swap_trace]
  simp

theorem scatteringPositiveProjection_rank_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Module.finrank ℂ (LinearMap.range (scatteringPositiveProjection q κ).toLin') = 1 := by
  have hh : (-scatteringInvolution q κ)*(-scatteringInvolution q κ) = 1 := by
    simpa using scatteringInvolution_mul_self q κ
  have h := involutionProjection_trace_eq_finrank _ hh
  change (scatteringPositiveProjection q κ).trace = _ at h
  rw [scatteringPositiveProjection_trace] at h
  exact_mod_cast h.symm

theorem scatteringNegativeProjection_apply (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    scatteringNegativeProjection q κ *ᵥ v = negativeScatteringChannel q κ v := by
  simp [scatteringNegativeProjection, involutionProjection, negativeScatteringChannel,
    involutionAltPart, scatteringChannelEnd, Matrix.toLin'_apply, Matrix.sub_mulVec,
    Matrix.smul_mulVec]

theorem scatteringPositiveProjection_apply (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : Fin 2 → ℂ) :
    scatteringPositiveProjection q κ *ᵥ v = positiveScatteringChannel q κ v := by
  simp only [scatteringPositiveProjection, involutionProjection, positiveScatteringChannel,
    involutionSymPart, scatteringChannelEnd, Matrix.toLin'_apply, sub_neg_eq_add,
    Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The quantum-algebra exponential theorem applies to the actual scattering involution. -/
theorem scatteringInvolution_exponential (q : SchwartzMap ℝ ℂ) (κ : ℝ) (z : ℂ) :
    NormedSpace.exp (z • scatteringInvolution q κ) =
      Complex.cosh z • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.sinh z • scatteringInvolution q κ :=
  QuantumAlg.exp_smul_of_mul_self_eq_one z (scatteringInvolution_mul_self q κ)

/-- Imaginary-parameter evolution has an exact trigonometric formula; no unitarity is asserted. -/
theorem scatteringInvolution_oscillation (q : SchwartzMap ℝ ℂ) (κ t : ℝ) :
    NormedSpace.exp ((I*(t:ℂ)) • scatteringInvolution q κ) =
      (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (I*(Real.sin t : ℂ)) • scatteringInvolution q κ :=
  _root_.HTGeometry.ConstraintRelativity.exp_I_smul_involution _
    (scatteringInvolution_mul_self q κ) t

theorem scatteringNegativeProjection_exponential (q : SchwartzMap ℝ ℂ) (κ : ℝ) (z : ℂ) :
    NormedSpace.exp (z • scatteringNegativeProjection q κ) =
      1 + (Complex.exp z-1) • scatteringNegativeProjection q κ :=
  QuantumAlg.exp_smul_isIdempotentElem z (scatteringNegativeProjection_idempotent q κ)

/-- Exact evolution of every vector along its two complementary scattering channels. -/
theorem scatteringInvolution_exponential_channels (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (z : ℂ) (v : Fin 2 → ℂ) :
    NormedSpace.exp (z • scatteringInvolution q κ) *ᵥ v =
      Complex.exp z • positiveScatteringChannel q κ v +
        Complex.exp (-z) • negativeScatteringChannel q κ v := by
  rw [scatteringInvolution_exponential, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [positiveScatteringChannel, negativeScatteringChannel, involutionSymPart,
    involutionAltPart, scatteringChannelEnd, Matrix.toLin'_apply, Complex.cosh, Complex.sinh]
  module

end
end GaloisForLFunctions.HTGeometry.FokasLenells
