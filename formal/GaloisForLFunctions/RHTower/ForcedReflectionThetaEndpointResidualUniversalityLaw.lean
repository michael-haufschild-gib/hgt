import GaloisForLFunctions.RHTower.SeamMeromorphicRigidity
import GaloisForLFunctions.RHTower.XiThetaEndpointResidual

/-!
# Forced-reflection theta-endpoint residual universality law

The two poles of the meromorphic completion force every reflection symmetry to be the functional
equation.  The same forced reflection then preserves the entire theta-endpoint residual and carries
its rational anchor exactly to the Xi zero set.
-/

namespace RHTower

/-- The exact theta-endpoint residual is invariant under the functional-equation reflection. -/
theorem xiThetaEndpointResidual_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiThetaEndpointResidual (1 - s) = xiThetaEndpointResidual s := by
  have hrs0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hrs1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  rw [xiThetaEndpointResidual_eq (1 - s) hrs0 hrs1,
    xiThetaEndpointResidual_eq s hs0 hs1, xi_one_sub]
  congr 1
  ring

/-- **Forced-reflection theta-endpoint residual universality law.**  An arbitrary reflection of
the meromorphic completed zeta is forced to center one; it therefore preserves the endpoint
residual and makes the reflected rational anchor equivalent to the original Xi-zero condition. -/
theorem completedReflection_forces_thetaEndpointResidual_and_xiAnchor
    {b s : ℂ}
    (hb : ∀ w, completedRiemannZeta (b - w) = completedRiemannZeta w)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    b = 1 ∧
      xiThetaEndpointResidual (b - s) = xiThetaEndpointResidual s ∧
      (completedRiemannZeta₀ (b - s) =
          -(1 / ((b - s) * ((b - s) - 1))) ↔ xi s = 0) := by
  have hb1 : b = 1 := completedRiemannZeta_reflection_center_eq_half hb
  subst b
  have hrs0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hrs1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  refine ⟨rfl, xiThetaEndpointResidual_one_sub s hs0 hs1, ?_⟩
  rw [completedRiemannZeta₀_eq_neg_inv_mul_iff_xi_eq_zero (1 - s) hrs0 hrs1,
    xi_one_sub]

end RHTower
