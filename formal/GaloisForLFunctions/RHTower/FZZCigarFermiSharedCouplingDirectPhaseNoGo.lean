import GaloisForLFunctions.RHTower.FZZCigarFermiCouplingExchange
import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaPhaseOrderRigidity

/-!
# FZZ shared-coupling to balanced-phase direct-identity no-go

The source-native Fermi shared-coupling response is a fully integrated first-order
radial FZZ insertion.  It vanishes exactly at zero momentum.  The balanced
external-Gamma phase is the already closed FZZ-P endpoint: its vanishing, and its
vacuum-delay saturation, are equivalent to linear replica-area passivity and hence
to RH when imposed on every parity-Mellin divisor mode.

One tempting way to close the remaining source-dynamical edge is to identify those
two literal receivers pointwise after an affine momentum calibration:

`shared-coupling source response(a * P + b) = unwrapped balanced phase(P)`.

This cannot be the missing identity.  At `P = 0`, both sides force `b = 0`.
The source response is then even in `P`, while the unwrapped balanced phase is
strictly increasing, hence takes different values at `P = -1` and `P = 1`.

This kills only the direct affine pointwise transmutation route:

`shared-coupling source -> affine pointwise phase identity -> Ward-delay saturation
  -> FZZ passivity -> RH`.

The positive survivor is precise.  The two receivers have the same zero locus after
a nonzero centered scale, so a viable source law need only transport the *zero
locus* (or a non-pointwise, mode-dependent Ward current); it must not claim their
full complex/real values agree pointwise.  Establishing that source-frame transport
on literal parity-Mellin modes remains the live FZZ-P burden.
-/

namespace RHTower

noncomputable section

/-- No affine reparameterization makes the literal fully integrated shared-coupling FZZ source
response equal pointwise to the unwrapped balanced external-Gamma phase. -/
theorem not_exists_fzzFermiSharedCoupling_affine_balancedPhase_bridge :
    ¬ ∃ (v a b : ℝ), ∀ P : ℝ,
      GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse v (a * P + b) =
        (fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) : ℂ) := by
  rintro ⟨v, a, b, h⟩
  have hbresponse : GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse v b = 0 := by
    simpa using h 0
  have hb : b = 0 :=
    (GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse_zero_iff v b).mp
      hbresponse
  have hplus := h 1
  have hminus := h (-1)
  rw [hb] at hplus hminus
  norm_num at hplus hminus
  have hsource :
      GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse v a =
        GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse v (-a) := by
    rw [GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse_neg_momentum]
  rw [hsource] at hplus
  have hphaseCast :
      (fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * (1 : ℝ)) : ℂ) =
        (fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * (-1 : ℝ)) : ℂ) := by
    norm_num
    exact_mod_cast hplus.symm.trans hminus
  have hphase :
      fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * (1 : ℝ)) =
        fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * (-1 : ℝ)) := by
    exact_mod_cast hphaseCast
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact (fzzHJBalancedExternalGammaPhaseLift_strictMono
    (by nlinarith [hsqrt] : Real.sqrt 2 * (-1 : ℝ) < Real.sqrt 2 * (1 : ℝ))).ne' hphase

/-- Closed FZZ-P route class: the shared radial source and balanced phase cannot be joined by a
direct affine pointwise receiver identity. -/
def FZZCigarFermiSharedCouplingDirectPhaseRouteKilled : Prop :=
  ¬ ∃ (v a b : ℝ), ∀ P : ℝ,
    GaloisForLFunctions.RHTower.fzzFermiSharedCouplingMarkedResponse v (a * P + b) =
      (fzzHJBalancedExternalGammaPhaseLift (Real.sqrt 2 * P) : ℂ)

theorem fzzCigarFermiSharedCouplingDirectPhaseRouteKilled :
    FZZCigarFermiSharedCouplingDirectPhaseRouteKilled :=
  not_exists_fzzFermiSharedCoupling_affine_balancedPhase_bridge

end

end RHTower
