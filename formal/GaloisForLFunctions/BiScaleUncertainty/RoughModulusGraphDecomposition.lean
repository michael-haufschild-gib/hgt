import GaloisForLFunctions.BiScaleUncertainty.RoughSobolevModulus
import GaloisForLFunctions.BiScaleUncertainty.CompactSourceGraphAdmission

/-!
# Exact nodal loss and path-slack transfer under modulus

Taking modulus stays inside the actual rough Sobolev domain. Every path budget
is unchanged; its nodal jump loss becomes additional slack. These addition
identities hold for the entire mixed measure even at infinite total energy.
Compact sources give finite real energy differences and unchanged source mass.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

theorem budget_modulusVelocity (q : Velocity) (c : ℝ) (e : Edge) :
    budget (modulusVelocity q c) e = budget q e := by
  rw [budget_eq_physical, budget_eq_physical, energy_modulusVelocity]

/-- Exact Beurling--Deny loss with the modulus represented by an actual L2 velocity. -/
theorem jump_modulus_decomposition (q : Velocity) (c : ℝ) (e : Edge) :
    jump q e = jump (modulusVelocity q c) e + nodalCost q c e := by
  have h := nodal_mulJump_sq_decomp
    (fun j : ℕ => if j = 1 then c+logPrimitive q e.2 else c+logPrimitive q (e.2+e.1)) 2 1
  have hd : (logPrimitive q (e.2+e.1)-logPrimitive q e.2)^2 =
      (|c+logPrimitive q (e.2+e.1)|-|c+logPrimitive q e.2|)^2 +
      4*(max (c+logPrimitive q (e.2+e.1)) 0 * max (-(c+logPrimitive q e.2)) 0 +
        max (-(c+logPrimitive q (e.2+e.1))) 0 * max (c+logPrimitive q e.2) 0) := by
    simpa [mulJump, seqPos, seqNeg] using h
  have hm : |c+logPrimitive q (e.2+e.1)|-|c+logPrimitive q e.2| =
      logPrimitive (modulusVelocity q c) (e.2+e.1)-logPrimitive (modulusVelocity q c) e.2 := by
    rw [← logPrimitive_modulusVelocity, ← logPrimitive_modulusVelocity]
    ring
  unfold jump nodalCost
  rw [hd, hm, ENNReal.ofReal_add (sq_nonneg _) (by positivity)]

theorem jump_modulus_le (q : Velocity) (c : ℝ) (e : Edge) :
    jump (modulusVelocity q c) e ≤ jump q e := by
  rw [jump_modulus_decomposition q c e]
  exact le_add_right le_rfl

/-- At each finite-budget edge the lost nodal jump becomes additional path slack. -/
theorem slack_modulus_decomposition (q : Velocity) (c : ℝ) (e : Edge) :
    slack (modulusVelocity q c) e = slack q e + nodalCost q c e := by
  have hf : jump (modulusVelocity q c) e ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.add_right_inj hf).mp
  calc
    _ = budget (modulusVelocity q c) e := jump_add_slack _ _
    _ = budget q e := budget_modulusVelocity q c e
    _ = jump q e + slack q e := (jump_add_slack q e).symm
    _ = _ := by rw [jump_modulus_decomposition q c e]; ac_rfl

/-- No total-energy finiteness or truncation premise is needed. -/
theorem jumpEnergy_modulus_decomposition (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    jumpEnergy D q = jumpEnergy D (modulusVelocity q c) + nodalEnergy D q c := by
  calc
    _ = ∫⁻ e, jump (modulusVelocity q c) e + nodalCost q c e ∂edgeMeasure D :=
      lintegral_congr (jump_modulus_decomposition q c)
    _ = _ := lintegral_add_left (measurable_jump _) (nodalCost q c)

theorem jumpEnergy_modulus_le (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    jumpEnergy D (modulusVelocity q c) ≤ jumpEnergy D q :=
  lintegral_mono (jump_modulus_le q c)

/-- The exact slack transfer remains valid when either side is infinite. -/
theorem slackEnergy_modulus_decomposition (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    slackEnergy D (modulusVelocity q c) = slackEnergy D q + nodalEnergy D q c := by
  calc
    _ = ∫⁻ e, slack q e + nodalCost q c e ∂edgeMeasure D :=
      lintegral_congr (slack_modulus_decomposition q c)
    _ = _ := lintegral_add_left (measurable_slack q) (nodalCost q c)

theorem congestionEnergy_modulusVelocity (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    congestionEnergy D (modulusVelocity q c) = congestionEnergy D q := by
  rw [congestionEnergy_eq_budget, congestionEnergy_eq_budget]
  exact lintegral_congr (budget_modulusVelocity q c)

theorem sourceMass_modulusVelocity (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    sourceMass ψ (modulusVelocity q c) |c| = sourceMass ψ q c := by
  apply lintegral_congr
  intro x
  rw [logPrimitive_modulusVelocity, sq_abs]

/-- Compact-source finiteness makes the nodal loss an ordinary real difference. -/
theorem compact_jumpEnergy_modulus_difference (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    (jumpEnergy (compactMixture ψ weights) q).toReal -
      (jumpEnergy (compactMixture ψ weights) (modulusVelocity q c)).toReal =
      (nodalEnergy (compactMixture ψ weights) q c).toReal := by
  rw [jumpEnergy_modulus_decomposition _ q c,
    ENNReal.toReal_add (compact_jumpEnergy_ne_top ψ weights (modulusVelocity q c))
      (compact_nodalEnergy_ne_top ψ weights q c)]
  ring

/-- The entire admitted source-mass plus graph form has the exact nodal defect. -/
theorem compact_formEnergy_modulus_decomposition (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    sourceMass ψ q c + jumpEnergy (compactMixture ψ weights) q =
      (sourceMass ψ (modulusVelocity q c) |c| +
        jumpEnergy (compactMixture ψ weights) (modulusVelocity q c)) +
        nodalEnergy (compactMixture ψ weights) q c := by
  rw [sourceMass_modulusVelocity, jumpEnergy_modulus_decomposition _ q c]
  ac_rfl

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
