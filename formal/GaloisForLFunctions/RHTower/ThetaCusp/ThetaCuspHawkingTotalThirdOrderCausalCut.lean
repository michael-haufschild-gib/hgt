import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTotalThirdOrderCokernelSchurSection

/-!
# Contact-free nonlinear Teukolsky causal cut

Compare the complete retarded and advanced `++-` Schur sources while keeping the same local
Einstein Taylor data. Their difference kills the direct third derivative before any cokernel
projection. The surviving nonlinear causal cut is exactly the bilinear Einstein coupling applied
to the `++` and `+-` response-map jumps.

Consequently, no coherent same-grade local third-order counterterm can alter this cut. A nonzero
cut must be carried by a discontinuity of at least one complete bulk-plus-horizon response.
-/

open Complex

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Retarded-minus-advanced cut of the complete nonlinear `++-` Schur source. -/
def d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) : Y :=
  d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource
      B C RppRet RpmRet p m -
    d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource
      B C RppAdv RpmAdv p m

/-- The total causal cut contains response discontinuities and no direct third-order residual. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_responseDifference
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m =
      B p (d4GaugeFixedTeukolskyRetardedPlusMinusResponse B RpmRet p m -
        d4GaugeFixedTeukolskyRetardedPlusMinusResponse B RpmAdv p m) +
      B m (d4GaugeFixedTeukolskyRetardedPlusPlusResponse B RppRet p -
        d4GaugeFixedTeukolskyRetardedPlusPlusResponse B RppAdv p) := by
  simp [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource, map_sub]
  abel

/-- Resolvent-jump form of the contact-free nonlinear causal cut. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m =
      B p ((RpmRet - RpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)) +
      B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_responseDifference]
  simp [d4GaugeFixedTeukolskyRetardedPlusMinusResponse,
    d4GaugeFixedTeukolskyRetardedPlusPlusResponse]

/-- No change of the common direct Einstein third jet changes the nonlinear causal cut. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_independent_directThirdJet
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C₁ C₂ : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C₁ RppRet RpmRet RppAdv RpmAdv p m =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C₂ RppRet RpmRet RppAdv RpmAdv p m := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump]

/-- If both sourced response discontinuities vanish, the total nonlinear causal cut vanishes. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_zero_of_responseJumps_eq_zero
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hpm : (RpmRet - RpmAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) = 0)
    (hpp : (RppRet - RppAdv)
      (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) = 0) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m = 0 := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    hpm, hpp]
  simp

/-- Nonzero total causal source localizes to a nonzero sourced `+-` or `++` response jump. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_ne_zero_imp_responseJump
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hcut : d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
      B C RppRet RpmRet RppAdv RpmAdv p m ≠ 0) :
    (RpmRet - RpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) ≠ 0 ∨
      (RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) ≠ 0 := by
  contrapose! hcut
  exact d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_zero_of_responseJumps_eq_zero
    B C RppRet RpmRet RppAdv RpmAdv p m hcut.1 hcut.2

/-- Left-cokernel projection of the total nonlinear causal cut. -/
def d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) : ℂ :=
  ell (d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
    B C RppRet RpmRet RppAdv RpmAdv p m)

/-- Cokernel causal cut is literally the retarded total section minus the advanced total
section. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_section_sub
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          ell B C RppRet RpmRet p m -
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
          ell B C RppAdv RpmAdv p m := by
  simp [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection, map_sub]

/-- The nonlinear cokernel cut is the sum of the two projected response discontinuities. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m =
      ell (B p ((RpmRet - RpmAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m))) +
        ell (B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump]
  exact map_add ell _ _

/-- The projected causal cut is likewise independent of every common direct third jet. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_independent_directThirdJet
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C₁ C₂ : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C₁ RppRet RpmRet RppAdv RpmAdv p m =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C₂ RppRet RpmRet RppAdv RpmAdv p m := by
  simp only [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_independent_directThirdJet
      B C₁ C₂]

/-- A nonzero projected cut still forces a nonzero sourced response discontinuity. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_ne_zero_imp_responseJump
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hcut : d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
      ell B C RppRet RpmRet RppAdv RpmAdv p m ≠ 0) :
    (RpmRet - RpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m) ≠ 0 ∨
      (RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) ≠ 0 := by
  apply d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_ne_zero_imp_responseJump
    B C RppRet RpmRet RppAdv RpmAdv p m
  intro hsource
  apply hcut
  simp [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut, hsource]

end

end RHTower
