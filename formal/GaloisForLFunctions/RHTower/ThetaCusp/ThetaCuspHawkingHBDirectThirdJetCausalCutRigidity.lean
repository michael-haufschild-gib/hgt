import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTotalThirdOrderCausalCut

/-!
# HB direct-third-jet causal-cut rigidity

The complete gauge-fixed Einstein--Teukolsky `++-` source contains two propagated quadratic
responses and one direct cubic Taylor term.  A one-sided resonant section can be changed by the
direct third jet.  The HB endpoint, however, uses the retarded-minus-advanced cokernel cut with
the same local Einstein action in both causal orientations.

The common direct cubic term cancels from that cut before projection.  This gives the exact
remaining cancellation law

`projectedJump_+- = -projectedJump_++`.

More strongly, allowing an arbitrary local direct third jet has no power to create a zero of the
cut: some third jet cancels the cut if and only if the zero third jet already does.  This kills the
entire direct-local-cubic-counterterm branch of the HB causal-cut route.  The only survivors are
the stationary `+-` and radiative `++` response discontinuities.

The scope is sharp.  The theorem does not concern a one-sided retarded section, and it does not
allow different local actions in the retarded and advanced problems.  Either modification leaves
the direct-third-jet-only route class.

`[PROVED HERE] [LEAN-PROVED] [HB] [ROUTE KILL] [NOVELTY AUDITED 2026-08-31]`
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Exact survivor after the local cubic contact term is removed: the full `++-` cokernel causal
cut vanishes exactly when its two projected quadratic response jumps anti-align. -/
theorem
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_zero_iff_responseJumpAntiAligned
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m = 0 ↔
      ell (B p ((RpmRet - RpmAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) =
        -ell (B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq]
  constructor <;> intro h <;> linear_combination h

/-- Nonvanishing form of the survivor: a causal-cut obstruction remains precisely when the two
projected quadratic response jumps fail the forced anti-alignment. -/
theorem
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_ne_zero_iff_responseJump_not_antiAligned
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m ≠ 0 ↔
      ell (B p ((RpmRet - RpmAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) ≠
        -ell (B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) := by
  exact not_congr
    (d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_zero_iff_responseJumpAntiAligned
      ell B C RppRet RpmRet RppAdv RpmAdv p m)

/-- Existential tuning classification.  Some common local direct third jet cancels the causal cut
if and only if the cut already vanishes with no direct third jet at all. -/
theorem
    exists_d4GaugeFixedTeukolskyDirectThirdJet_cokernelCausalCut_eq_zero_iff_zeroThirdJet
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    (∃ C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y,
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m = 0) ↔
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B 0 RppRet RpmRet RppAdv RpmAdv p m = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    rw [← d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_independent_directThirdJet
      ell B C 0 RppRet RpmRet RppAdv RpmAdv p m]
    exact hC
  · intro hzero
    exact ⟨0, hzero⟩

/-- Closed route class: changing only the common local direct Einstein third jet cannot create
HB causal-cut cancellation. -/
def D4HBDirectThirdJetCausalCutCancellationRouteKilled : Prop :=
  ∀ (X Y : Type) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X),
    (∃ C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y,
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m = 0) ↔
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B 0 RppRet RpmRet RppAdv RpmAdv p m = 0

/-- Premise-free Lean certificate killing the direct-local-third-jet HB causal-cut route. -/
theorem d4HBDirectThirdJetCausalCutCancellationRouteKilled :
    D4HBDirectThirdJetCausalCutCancellationRouteKilled := by
  intro X Y _ _ _ _ ell B RppRet RpmRet RppAdv RpmAdv p m
  exact
    exists_d4GaugeFixedTeukolskyDirectThirdJet_cokernelCausalCut_eq_zero_iff_zeroThirdJet
      ell B RppRet RpmRet RppAdv RpmAdv p m

end

end RHTower
