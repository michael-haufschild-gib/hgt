import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionCapacity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Capacity-generated fusion heat

The levels are logarithms of proved fusion capacity suprema. Their exact spacing
produces a geometric heat trace. Subtracting its continuous density gives a
bounded positive defect with an exact dyadic relation to the Fermi kernel.
No numerical result enters these proofs.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def fusionHeat (u : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-fusionEnergy (n+1)*Real.exp u)

theorem fusionHeat_hasSum (u : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-fusionEnergy (n+1)*Real.exp u))
      (1/(Real.exp (fusionSpacing*Real.exp u)-1)) := by
  let b := fusionSpacing*Real.exp u
  let q := Real.exp (-b)
  have hb : 0 < b := mul_pos fusionSpacing_pos (Real.exp_pos u)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb)
  have hgeo := hasSum_geometric_of_lt_one (Real.exp_pos (-b)).le hq
  have hmul := hgeo.mul_left q
  have hterm (n : ℕ) : Real.exp (-fusionEnergy (n+1)*Real.exp u)=q*q^n := by
    rw [fusionEnergy_eq]
    calc
      _ = Real.exp (((n+1 : ℕ) : ℝ)*(-b)) := by congr 1; dsimp only [b]; ring
      _ = (Real.exp (-b))^(n+1) := Real.exp_nat_mul (-b) (n+1)
      _ = q*q^n := by rw [pow_succ,mul_comm]
  have he : 1 < Real.exp b := Real.one_lt_exp_iff.mpr hb
  have hden : Real.exp b-1 ≠ 0 := ne_of_gt (sub_pos.mpr he)
  have hvalue : q*(1-q)⁻¹=1/(Real.exp b-1) := by
    dsimp only [q]
    rw [Real.exp_neg]
    field_simp
  change HasSum (fun n : ℕ => q*q^n) (q*(1-q)⁻¹) at hmul
  rw [hvalue] at hmul
  simpa only [hterm] using hmul

theorem fusionHeat_eq (u : ℝ) : fusionHeat u=1/(Real.exp (fusionSpacing*Real.exp u)-1) :=
  (fusionHeat_hasSum u).tsum_eq

def fusionBoseDefect (t : ℝ) : ℝ :=
  if 0 < t then 1/t-1/(Real.exp t-1) else 0

theorem fusionBoseDefect_bounds (t : ℝ) :
    0 ≤ fusionBoseDefect t ∧ fusionBoseDefect t ≤ 1 ∧ fusionBoseDefect t ≤ 1/|t| := by
  by_cases ht : 0 < t
  · have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
    have hd : 0 < Real.exp t-1 := sub_pos.mpr he
    have hprod : 0 < t*(Real.exp t-1) := mul_pos ht hd
    have hform : fusionBoseDefect t=(Real.exp t-1-t)/(t*(Real.exp t-1)) := by
      rw [fusionBoseDefect,if_pos ht]
      field_simp
    have hnum : 0 ≤ Real.exp t-1-t := by
      have hh := Real.add_one_le_exp t
      linarith only [hh]
    have hex := Real.add_one_le_exp (-t)
    have hx := mul_le_mul_of_nonneg_right hex (Real.exp_pos t).le
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at hx
    refine ⟨?_,?_,?_⟩
    · rw [hform]
      exact div_nonneg hnum hprod.le
    · rw [hform]
      apply (div_le_one hprod).mpr
      nlinarith only [hx]
    · rw [fusionBoseDefect,if_pos ht,abs_of_pos ht]
      exact sub_le_self _ (one_div_nonneg.mpr hd.le)
  · simp only [fusionBoseDefect,if_neg ht]
    exact ⟨le_rfl,zero_le_one,one_div_nonneg.mpr (abs_nonneg _)⟩

theorem fusionBoseDefect_dyadic (t : ℝ) :
    2*fusionBoseDefect (2*t)-fusionBoseDefect t =
      if 0 < t then 1/(Real.exp t+1) else 0 := by
  by_cases ht : 0 < t
  · have h2t : 0 < 2*t := mul_pos (by positivity) ht
    have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
    have hd : Real.exp t-1 ≠ 0 := ne_of_gt (sub_pos.mpr he)
    have hd2 : (Real.exp t)^2-1 ≠ 0 := by nlinarith only [he]
    have hp : Real.exp t+1 ≠ 0 := by positivity
    have hex : Real.exp (2*t)=(Real.exp t)^2 := by
      rw [show 2*t=t+t by ring,Real.exp_add,pow_two]
    simp only [fusionBoseDefect,if_pos ht,if_pos h2t,hex]
    field_simp
    ring
  · have h2t : ¬0 < 2*t := by linarith only [ht]
    simp only [fusionBoseDefect,if_neg ht,if_neg h2t,mul_zero,sub_self]

def fusionRegularizedKernel (t : ℝ) : ℂ :=
  (fusionBoseDefect (fusionSpacing*t) : ℝ)

theorem fusionRegularizedKernel_discrete (u : ℝ) :
    fusionRegularizedKernel (Real.exp u)=
      ((1/(fusionSpacing*Real.exp u)-fusionHeat u : ℝ) : ℂ) := by
  rw [fusionRegularizedKernel,fusionBoseDefect,
    if_pos (mul_pos fusionSpacing_pos (Real.exp_pos u)),fusionHeat_eq]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
