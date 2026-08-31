import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBDirectThirdJetCausalCutRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingCubicPeierlsPolarization

/-!
# HB Peierls stationary-channel elimination

The complete Einstein--Teukolsky `++-` cokernel causal cut initially contains a stationary `+-`
response projection and a radiative `++` response projection.  The direct-third-jet rigidity theorem
reduces its zero set to possible anti-alignment of those two complex numbers.

For a physical cyclic variational realization, however, the stationary projection is the Peierls
self-pairing of its own mixed quadratic source.  Causal skewness annihilates it identically.  Thus
the full cut is exactly the radiative `++` projection, with identical zero and nonzero loci.
Nontrivial stationary/radiative anti-alignment is impossible: anti-alignment occurs precisely when
the radiative projection itself vanishes.

This kills the stationary-channel cancellation branch of HB.  The sole surviving causal-cut burden
is extinction of the second-harmonic radiative left-cokernel projection.

`[PROVED HERE] [LEAN-PROVED] [HB] [ROUTE KILL] [NOVELTY AUDITED 2026-08-31]`
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- In every cyclic Peierls realization, the full nonlinear cokernel cut is exactly its radiative
`++` response projection; the stationary `+-` arm is a vanishing causal self-pairing. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_radiative_of_Peierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m =
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq, hRpm,
    d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero pairing B Delta p m
      hB hcyclic hskew, zero_add]

/-- Physical full-cut extinction is exactly radiative `++` extinction. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_zero_iff_radiative_of_Peierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m = 0 ↔
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) = 0 := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_radiative_of_Peierls
    pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m hB hcyclic hRpm hskew]

/-- Physical full-cut nonvanishing is carried exactly by the radiative `++` projection. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_ne_zero_iff_radiative_of_Peierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m ≠ 0 ↔
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) ≠ 0 := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_radiative_of_Peierls
    pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m hB hcyclic hRpm hskew]

/-- The anti-alignment survivor from the direct-third-jet theorem becomes trivial under physical
Peierls incidence: it holds exactly when the radiative term vanishes by itself. -/
theorem d4GaugeFixedTeukolsky_responseJumpAntiAligned_iff_radiative_eq_zero_of_Peierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : RpmRet - RpmAdv = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    pairing m (B p ((RpmRet - RpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) =
        -pairing m (B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) ↔
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) = 0 := by
  rw [hRpm, d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero pairing B Delta p m
    hB hcyclic hskew]
  constructor <;> intro h <;> linear_combination h

/-- Closed route class: source-derived cyclic Peierls incidence leaves no nontrivial
stationary/radiative cancellation mechanism in the HB causal cut. -/
def D4HBPeierlsStationaryRadiativeAntiAlignmentRouteKilled : Prop :=
  ∀ (X Y : Type) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X),
    (∀ x y, B x y = B y x) →
    (∀ x y z, pairing x (B y z) = pairing z (B x y)) →
    RpmRet - RpmAdv = Delta →
    (∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) →
    (d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C RppRet RpmRet RppAdv RpmAdv p m = 0 ↔
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) = 0) ∧
    (pairing m (B p ((RpmRet - RpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) =
        -pairing m (B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) ↔
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) = 0)

/-- Premise-free Lean certificate killing the physical stationary/radiative anti-alignment branch
of the HB causal-cut route. -/
theorem d4HBPeierlsStationaryRadiativeAntiAlignmentRouteKilled :
    D4HBPeierlsStationaryRadiativeAntiAlignmentRouteKilled := by
  intro X Y _ _ _ _ pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m
    hB hcyclic hRpm hskew
  exact ⟨
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_zero_iff_radiative_of_Peierls
      pairing B C Delta RppRet RpmRet RppAdv RpmAdv p m hB hcyclic hRpm hskew,
    d4GaugeFixedTeukolsky_responseJumpAntiAligned_iff_radiative_eq_zero_of_Peierls
      pairing B Delta RppRet RpmRet RppAdv RpmAdv p m hB hcyclic hRpm hskew⟩

end

end RHTower
