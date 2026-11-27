import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.MergeMass

/-! # Exponential probability cost per restored block length -/
open Set MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open Dephasing.GappedSpin.CentralCut
noncomputable section

private theorem seam_floor : ∃ a ∈ Ioc (0:ℝ) 1, ∀ K : ℕ, ∀ z ∈ Ioc (0:ℝ) 1,
    a*((gapScale K)^9*z^9) ≤ (standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale K/20*z)) := by
  let c := (2*(sqrt (2*π))⁻¹/20)^9*exp (-(9:ℝ)/2)
  have hc : 0<c := by dsimp only [c]; positivity
  refine ⟨min 1 c,⟨lt_min zero_lt_one hc,min_le_left ..⟩,?_⟩
  intro K z hz
  have hg := gapScale_pos K
  have hg₁ : gapScale K≤1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have h := gaussian_rectangular_floor (∅ : Finset (Fin 3×Fin 3)) (fun _ => 0)
    (mul_pos (div_pos hg (by norm_num : (0:ℝ)<20)) hz.1)
    ((mul_le_of_le_one_right (by positivity : 0≤gapScale K/20) hz.2).trans (by linarith only [hg₁]))
    (le_refl (1:ℝ))
  simp only [Finset.notMem_empty,if_false,Finset.card_empty,pow_zero,one_mul,
    abs_zero,zero_add,one_pow,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,mul_one,zero_sub] at h
  apply (mul_le_mul_of_nonneg_right (min_le_right 1 c)
    (mul_nonneg (pow_nonneg hg.le 9) (pow_nonneg hz.1.le 9))).trans
  apply le_trans _ h
  apply le_of_eq
  dsimp only [c]
  norm_num
  ring

private theorem dilation_cost (l r : ℕ) :
    (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r)) ≤ ((2:ℝ)^16)^(l+r+4) := by
  have hdim : Fintype.card (PathLabel r)≤12*(r+2) := by
    simp only [PathLabel,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]; omega
  have hh := Nat.mul_le_mul (gridCount_bound l r)
    (Nat.pow_le_pow_right (by decide : 0<2) hdim)
  rw [←pow_add] at hh
  have he : 2*(l+r+4)+1+12*(r+2)≤16*(l+r+4) := by omega
  have hh' := hh.trans (Nat.pow_le_pow_right (by decide : 0<2) he)
  rw [pow_mul] at hh'
  exact_mod_cast hh'

/-- A fractional reduction z of the final joining-bond radius costs
only z⁹ beyond the exponential loss for the block length. -/
theorem priced_join_mass : ∃ ρ ∈ Ioc (0:ℝ) 1, ∀ l r : ℕ, ∀ z ∈ Ioc (0:ℝ) 1, ∀ R : ℝ, 0≤R →
    gapMass l*gapMass r*(standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale (l+r+4)/20*z)) ≤
      (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*R →
    ρ^(l+r+4)*gapMass l*gapMass r*z^9 ≤ R := by
  obtain ⟨a,ha,hfloor⟩ := seam_floor
  let b := (1/1024:ℝ)^9
  let v := (2:ℝ)^16
  let ρ := a*b/v
  have hb : 0<b := by dsimp only [b]; positivity
  have hv : 0<v := by dsimp only [v]; positivity
  have hρ : 0<ρ := div_pos (mul_pos ha.1 hb) hv
  have hρ₁ : ρ≤1 := (div_le_one hv).mpr ((mul_le_mul_of_nonneg_right ha.2 hb.le).trans (by norm_num [v,b]))
  refine ⟨ρ,⟨hρ,hρ₁⟩,?_⟩
  intro l r z hz R hR hjoin
  let K := l+r+4
  have hK : 1≤K := by dsimp only [K]; omega
  have haK : a^K≤a := (pow_le_pow_of_le_one ha.1.le ha.2 hK).trans_eq (pow_one _)
  have he : (gapScale K)^9=b^K := by
    dsimp only [gapScale,b]
    rw [←pow_mul,←pow_mul,Nat.mul_comm K 9]
  have hseam := hfloor K z hz
  rw [he] at hseam
  have hm := hjoin.trans (mul_le_mul_of_nonneg_right (dilation_cost l r) hR)
  have hs := (mul_le_mul_of_nonneg_right haK (mul_nonneg (pow_nonneg hb.le K) (pow_nonneg hz.1.le 9))).trans hseam
  have h₁ := (mul_le_mul_of_nonneg_left hs (mul_nonneg (show 0≤gapMass l from measureReal_nonneg)
    (show 0≤gapMass r from measureReal_nonneg))).trans hm
  change gapMass l*gapMass r*(a^K*(b^K*z^9))≤v^K*R at h₁
  have hd : 0<v^K := pow_pos hv K
  change (a*b/v)^K*gapMass l*gapMass r*z^9 ≤ _
  rw [div_pow,mul_pow,div_mul_eq_mul_div,div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  linarith only [h₁]

/-- Every balanced merger loses at most an exponential factor in the total block length. -/
theorem gaussian_merge_loss : ∃ ρ ∈ Ioc (0:ℝ) 1, ∀ l r : ℕ, l≤r → r≤l+1 →
    ρ^(l+r+4)*gapMass l*gapMass r ≤ gapMass (l+r+2) := by
  obtain ⟨ρ,hρ,h⟩ := priced_join_mass
  refine ⟨ρ,hρ,fun l r hl hr => ?_⟩
  have hj := balanced_merge_mass l r hl hr
  simpa only [one_pow,mul_one] using h l r 1 ⟨zero_lt_one,le_rfl⟩ (gapMass (l+r+2)) measureReal_nonneg
    (by simpa only [mul_one] using hj)

#print axioms gaussian_merge_loss
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
