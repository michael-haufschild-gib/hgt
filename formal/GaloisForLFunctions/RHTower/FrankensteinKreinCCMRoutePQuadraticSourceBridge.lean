import GaloisForLFunctions.RHTower.FrankensteinKreinCCMRoutePSignedConormalResidueBridge
import GaloisForLFunctions.RHTower.XiWardCubicCompletedPairResidueIncidence

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Forward Route-P conormal current with its logarithmic pole supplied by the literal signed
primitive-depth/CCM source.  The factor `-i` makes its residue the positive analytic
multiplicity. -/
def frankensteinKreinCCMRoutePForwardSourceColumn (u : ℂ) (r : ℝ) : ℂ :=
  -I * xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u *
    routePXiBaseConormalResidueFeature (u + 1) r

/-- Reflected Route-P mate current on the same literal signed source family. -/
def frankensteinKreinCCMRoutePReflectedSourceColumn (u : ℂ) (r : ℝ) : ℂ :=
  -I * xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u *
    xiWardCubicReflectedConormalMateFeature (u + 1) r

theorem frankensteinKreinCCMRoutePForwardSourceColumn_residue
    (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        frankensteinKreinCCMRoutePForwardSourceColumn u r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds ((inverseTiltedXiMultiplicity rho : ℂ) *
        routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
  have h :=
    (frankensteinKreinCCMRoutePSignedConormalColumn_residue rho r).const_mul (-I)
  convert h using 1
  · funext u
    simp only [frankensteinKreinCCMRoutePForwardSourceColumn,
      frankensteinKreinCCMRoutePSignedConormalColumn]
    ring
  · congr 1
    ring_nf
    rw [Complex.I_sq]
    ring

theorem frankensteinKreinCCMRoutePReflectedSourceColumn_residue
    (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        frankensteinKreinCCMRoutePReflectedSourceColumn u r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds ((inverseTiltedXiMultiplicity rho : ℂ) *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r)) := by
  have htrace :=
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_residue rho
  have hfeature : Tendsto
      (fun u : ℂ => xiWardCubicReflectedConormalMateFeature (u + 1) r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (xiWardCubicReflectedConormalMateFeature (rho : ℂ) r)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt
        (fun u : ℂ => xiWardCubicReflectedConormalMateFeature (u + 1) r)
        (criticalMellinXiPole rho) := by
      unfold xiWardCubicReflectedConormalMateFeature
      unfold routePXiBaseConormalResidueFeature
      fun_prop
    convert hc.tendsto using 1
    rw [criticalMellinXiPole_add_one]
  have h := (htrace.const_mul (-I)).mul hfeature
  convert h using 1
  · funext u
    simp only [frankensteinKreinCCMRoutePReflectedSourceColumn]
    ring
  · congr 1
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Two-variable completed quadratic current formed entirely on the source side, before either
CCM divisor residue is taken.  Thus no zero-fed logarithmic derivative remains in the carrier. -/
def frankensteinKreinCCMRoutePQuadraticSourceCurrent
    (u v : ℂ) (r : ℝ) : ℂ :=
  frankensteinKreinCCMRoutePReflectedSourceColumn u r *
    frankensteinKreinCCMRoutePForwardSourceColumn v r

def frankensteinKreinCCMRoutePQuadraticSourceRightResidue
    (u : ℂ) (tau : XiDivisorSupport) (r : ℝ) : ℂ :=
  frankensteinKreinCCMRoutePReflectedSourceColumn u r *
    ((inverseTiltedXiMultiplicity tau : ℂ) *
      routePXiBaseConormalResidueFeature (tau : ℂ) r)

theorem frankensteinKreinCCMRoutePQuadraticSourceCurrent_right_residue
    (u : ℂ) (tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun v : ℂ => (v - criticalMellinXiPole tau) *
        frankensteinKreinCCMRoutePQuadraticSourceCurrent u v r)
      (nhdsWithin (criticalMellinXiPole tau) ({criticalMellinXiPole tau}ᶜ))
      (nhds (frankensteinKreinCCMRoutePQuadraticSourceRightResidue u tau r)) := by
  have h := (frankensteinKreinCCMRoutePForwardSourceColumn_residue tau r).const_mul
    (frankensteinKreinCCMRoutePReflectedSourceColumn u r)
  simpa [frankensteinKreinCCMRoutePQuadraticSourceCurrent,
    frankensteinKreinCCMRoutePQuadraticSourceRightResidue, mul_assoc,
    mul_left_comm] using h

/-- Iterated residues of the literal source quadratic current are exactly W-H186's full
multiplicity product and reflected conormal pair. -/
theorem frankensteinKreinCCMRoutePQuadraticSourceCurrent_iterated_residue
    (rho tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        frankensteinKreinCCMRoutePQuadraticSourceRightResidue u tau r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (((inverseTiltedXiMultiplicity rho : ℂ) *
          (inverseTiltedXiMultiplicity tau : ℂ)) *
        (xiWardCubicReflectedConormalMateFeature (rho : ℂ) r *
          routePXiBaseConormalResidueFeature (tau : ℂ) r))) := by
  have h := (frankensteinKreinCCMRoutePReflectedSourceColumn_residue rho r).mul_const
    ((inverseTiltedXiMultiplicity tau : ℂ) *
      routePXiBaseConormalResidueFeature (tau : ℂ) r)
  simpa [frankensteinKreinCCMRoutePQuadraticSourceRightResidue, mul_assoc,
    mul_left_comm, mul_comm] using h

/-- Finite matrix obtained by radially integrating the iterated residues of the literal source
quadratic current. -/
def frankensteinKreinCCMRoutePRawSourcePairResidueMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ r : ℝ in Ioi 0,
    (((inverseTiltedXiMultiplicity (q i).1.1 : ℂ) *
        (inverseTiltedXiMultiplicity (q j).1.1 : ℂ)) *
      (xiWardCubicReflectedConormalMateFeature ((q i).1.1 : ℂ) r *
        routePXiBaseConormalResidueFeature ((q j).1.1 : ℂ) r))

/-- Exact matrix-complete source handoff: W-H186's raw completed pair-residue matrix is literally
the finite integrated iterated residue matrix of the primitive-depth/CCM source current. -/
theorem frankensteinKreinCCMRoutePRawSourcePairResidueMatrix_eq
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    frankensteinKreinCCMRoutePRawSourcePairResidueMatrix q =
      xiWardCubicRawCompletedPairResidueMatrix q := by
  ext i j
  rw [frankensteinKreinCCMRoutePRawSourcePairResidueMatrix]
  rw [xiWardCubicRawCompletedPairResidueMatrix_apply_eq_integral q i j]
  rfl

end

end RHTower
