import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointCoordinate

/-!
# Literal cyclic Peierls radial fibres

The two exterior radii used to witness noncancellation are actual points of the
original tortoise chart, not formal radius values.  This makes the `R = 2, 3`
alternative available to the literal radial current.

Proof-chain role:
`literal tortoise fibres R=2,3`
`-> nonzero cap/square residual on one literal fibre`
`-> noncompact B2 growth transport -> RBH/PW extinction`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsRadialFibre

open D4BMIngoingCoordinates D4BMJointWave
noncomputable section
set_option autoImplicit false

private theorem tortoise_neg (r : ℝ) (hr : 1 < r) : tortoise r < 0 := by
  have h := Real.log_lt_log (show 0 < r - 1 by linarith) (show r - 1 < r + 1 by linarith)
  dsimp [tortoise]
  linarith

private theorem radius_inverse (r : ℝ) (hr : 1 < r) :
    tortoiseRadius (tortoise r) = r := by
  let R := tortoiseRadius (tortoise r)
  have hR : 1 < R := tortoiseRadius_exterior _ (tortoise_neg r hr)
  have h := tortoise_original_inverse (tortoise r) (tortoise_neg r hr)
  change tortoise R = tortoise r at h
  have hRm : R - 1 ≠ 0 := by linarith
  have hRp : R + 1 ≠ 0 := by linarith
  have hrm : r - 1 ≠ 0 := by linarith
  have hrp : r + 1 ≠ 0 := by linarith
  rw [tortoise, tortoise, ← Real.log_div hRm hRp, ← Real.log_div hrm hrp] at h
  have he := congrArg Real.exp
    (show Real.log ((R - 1) / (R + 1)) = Real.log ((r - 1) / (r + 1)) by linarith)
  rw [Real.exp_log (div_pos (by linarith) (by linarith)),
    Real.exp_log (div_pos (by linarith) (by linarith))] at he
  field_simp [hRp, hrp] at he
  change R = r
  nlinarith

/-- The first literal witness fibre of the self-copy residual. -/
theorem tortoiseRadius_at_two : tortoiseRadius (tortoise 2) = 2 :=
  radius_inverse 2 (by norm_num)

/-- The second literal witness fibre of the self-copy residual. -/
theorem tortoiseRadius_at_three : tortoiseRadius (tortoise 3) = 3 :=
  radius_inverse 3 (by norm_num)

end
end RHTower.D4BMLiteralCyclicPeierlsRadialFibre
