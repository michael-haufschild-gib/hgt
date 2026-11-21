import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # The Gaussian dilation price and the protected time width -/
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- The sign-packing exponent pays for all Gaussian coordinates and a
summable exceptional probability on a single infinite chain. -/
theorem prefix_dilation_price (k : ℕ) (hk : 64 ≤ k) :
    Fintype.card (Fin (Fintype.card (ChainLabel (k+3))))+1+k ≤ 2^(k+3)/1024 := by
  have grow (n : ℕ) (hn : 64 ≤ n) : 16384*(n+1) ≤ 2^n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ 2 n]; omega
  have hc : Fintype.card (Fin (Fintype.card (ChainLabel (k+3)))) = Fintype.card (PathLabel (k+1)) :=
    Fintype.card_congr (pathCoeffEquiv (k+1))
  rw [hc]
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1024)).mpr
  apply le_trans _ (grow (k+3) (by omega))
  omega

/-- The entire laboratory window, doubled by dilation, and one sampling
cell fit into the protected physical width. -/
theorem prescribed_width_fits (k : ℕ) (hk : 64 ≤ k) :
    2*(2:ℝ)^(2^(k+3)/4096)+1 ≤ (2:ℝ)^(2^(k+3)/2048) := by
  let D := 2^(k+3)
  let A := (2:ℝ)^(D/4096)
  have hD : 8192 ≤ D := by
    change 2^13 ≤ 2^(k+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hex : 2 ≤ D/4096 := (Nat.le_div_iff_mul_le (by decide)).mpr hD
  have hA : 4 ≤ A := by
    simpa only [show (2:ℝ)^2 = 4 by norm_num] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hex
  change 2*A+1 ≤ _
  calc
    _ ≤ A*A := by nlinarith only [sq_nonneg (A-2),hA]
    _ = (2:ℝ)^(D/4096+D/4096) := (pow_add _ _ _).symm
    _ ≤ (2:ℝ)^(D/2048) := pow_le_pow_right₀ (by norm_num) (by omega)

#print axioms prefix_dilation_price
#print axioms prescribed_width_fits
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
