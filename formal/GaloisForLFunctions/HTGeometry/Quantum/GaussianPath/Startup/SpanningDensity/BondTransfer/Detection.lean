import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.PhysicalSignal

/-! # Detecting even a weak bond in a calibrated Pauli frame -/

open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon
noncomputable section
variable {n : ℕ}

private theorem edge_norm_from_box (u : PathShell n) (e : Fin (n+1)) {w : ℝ}
    (he : ∀ ab : Fin 3×Fin 3, |u (.inr (e,ab))|≤w) : ‖edgePart u e‖≤9*w := by
  unfold edgePart
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ab : Fin 3×Fin 3, w := by
      apply sum_le_sum
      intro ab _
      simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,norm_finitePauliMatrix,mul_one] using he ab
    _ = _ := by simp [nsmul_eq_mul]

/-- In a frame where the longitudinal coordinate has largest magnitude
w, the full-chain normalized signal is at least tw. The time condition
depends only on the largest coupling at either endpoint, uniformly in w. -/
theorem detectable_bond (u : PathShell n) (e : Fin (n+1)) {t R : ℝ} (ht : 0≤t)
    (hR : 0≤R) (hcap : ∀ l∈({e.castSucc,e.succ}:Finset _).biUnion pathIncidentLabels, |u l|≤R)
    (hw : |u (bondLabel e)|≤R)
    (hmax : ∀ ab : Fin 3×Fin 3, |u (.inr (e,ab))|≤|u (bondLabel e)|)
    (hsmall : 3348*t*R≤1) : t* |u (bondLabel e)|≤|bondSignal e u t| := by
  let S : Finset (Fin (n+2)) := {e.castSucc,e.succ}
  let I := S.biUnion pathIncidentLabels
  let E := ∑ l∈I, |u l|
  let w := |u (bondLabel e)|
  have hn : S.card≤2 := (card_insert_le e.castSucc {e.succ}).trans (by simp)
  have hN : I.card≤42 := (pathIncident_union_card S).trans (Nat.mul_le_mul_left 21 hn)
  have hE : E≤42*R := calc
    _ ≤ ∑ _l∈I, R := sum_le_sum hcap
    _ = I.card*R := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hR
  have hJ := edge_norm_from_box u e hmax
  change ‖edgePart u e‖≤9*w at hJ
  change w≤R at hw
  have hj : 2*E+‖edgePart u e‖≤93*R := by linarith only [hE,hJ,hw]
  have h₁ := mul_le_mul hJ hj (by dsimp only [E]; positivity) (by dsimp only [w]; positivity)
  have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0≤4*t^2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hsmall (show 0≤t*w from mul_nonneg ht (abs_nonneg _))
  have herr := bond_signal_relative u e t ht
  change |bondSignal e u t-2*t*u (bondLabel e)|≤4*t^2*‖edgePart u e‖*(2*E+‖edgePart u e‖) at herr
  have hs := abs_sub_abs_le_abs_sub (2*t*u (bondLabel e)) (bondSignal e u t)
  rw [abs_mul,abs_of_nonneg (mul_nonneg zero_le_two ht),abs_sub_comm] at hs
  change 2*t*w-|bondSignal e u t|≤_ at hs
  linarith only [herr,h₂,h₃,hs]

#print axioms detectable_bond
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
