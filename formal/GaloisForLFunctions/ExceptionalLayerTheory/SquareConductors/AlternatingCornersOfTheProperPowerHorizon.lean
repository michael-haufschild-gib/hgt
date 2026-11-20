import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFiniteHorizonProfileOfProperPrimePowers

/-!
# Alternating corners of the proper-power horizon

On each closed unit cell the finite-horizon profile is affine in the
square root of the horizon ratio. At an odd integer one moving edge
enters. At an even integer another edge simultaneously reaches the
top of the octave and reverses the sign of the slope change.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Slope of the profile in square-root coordinates on cell [n,n+1]. -/
def properHorizonSlope (n : ℕ) := ∑ j ∈ Ioc (n/2) n,(Real.sqrt j)⁻¹

/-- Exact formula on every closed cell, with both adjacent formulas
valid at their common endpoint. -/
theorem proper_profile_on_unit_cell {t : ℝ} (n : ℕ) (hl : (n:ℝ)≤t) (hu : t≤(n:ℝ)+1) :
    properHorizonProfile t = (n/2:ℕ)*(Real.sqrt 2-1)+Real.sqrt t*properHorizonSlope n-(n-n/2:ℕ) := by
  have hp : 0≤t := (Nat.cast_nonneg n).trans hl
  have hcap : ⌊t⌋₊≤n+1 := by
    have h : t ≤ ((n+1:ℕ):ℝ) := by simpa only [Nat.cast_succ] using hu
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor h
  rw [proper_horizon_profile_with_cap hcap,sum_Ioc_succ_top (Nat.zero_le _)]
  have z : properHorizonClip t (n+1)=1 := by
    apply max_eq_left
    exact (min_le_right _ _).trans ((div_le_one (Nat.cast_pos.mpr (Nat.succ_pos n))).mpr
      (by simpa only [Nat.cast_succ] using hu))
  rw [z,Real.sqrt_one,sub_self,add_zero]
  let f := fun j : ℕ => Real.sqrt (properHorizonClip t j)-1
  change (∑ j ∈ Ioc 0 n, f j)=_
  rw [←sum_Ioc_consecutive f (Nat.zero_le (n/2)) (Nat.div_le_self ..)]
  have low (j : ℕ) (hj : j∈Ioc 0 (n/2)) : f j = Real.sqrt 2-1 := by
    obtain ⟨jp,jn⟩ := mem_Ioc.mp hj
    have h : 2*(j:ℝ) ≤ n := by exact_mod_cast (show 2*j≤n by omega)
    have hc : (2:ℝ) ≤ t/j := (le_div_iff₀ (Nat.cast_pos.mpr jp)).mpr (h.trans hl)
    simp only [f,properHorizonClip,min_eq_left hc,max_eq_right (by norm_num : (1:ℝ)≤2)]
  have high (j : ℕ) (hj : j∈Ioc (n/2) n) : f j = Real.sqrt t*(Real.sqrt j)⁻¹-1 := by
    obtain ⟨hlj,hjn⟩ := mem_Ioc.mp hj
    have jp : 0<j := by omega
    have h : (n:ℝ)+1 ≤ 2*j := by exact_mod_cast (show n+1≤2*j by omega)
    have hlow : (1:ℝ)≤t/j := (one_le_div (Nat.cast_pos.mpr jp)).mpr ((Nat.cast_le.mpr hjn).trans hl)
    have hhi : t/j≤2 := (div_le_iff₀ (Nat.cast_pos.mpr jp)).mpr (hu.trans h)
    simp only [f,properHorizonClip]
    rw [min_eq_right hhi,max_eq_right hlow,Real.sqrt_div hp,div_eq_mul_inv]
  rw [sum_congr rfl low,sum_congr rfl high,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,
    sum_sub_distrib,←mul_sum,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,properHorizonSlope]
  ring

/-- Exact upward jump in square-root slope at every odd integer. -/
theorem proper_slope_at_odd (k : ℕ) :
    properHorizonSlope (2*k+1)-properHorizonSlope (2*k) = (Real.sqrt (2*k+1:ℕ))⁻¹ := by
  rw [properHorizonSlope,properHorizonSlope,show (2*k+1)/2=k by omega,show (2*k)/2=k by omega,
    sum_Ioc_succ_top (by omega)]
  ring

/-- At every positive even integer the upper clipping removes √2
times the entering slope. -/
theorem proper_slope_at_even (k : ℕ) :
    properHorizonSlope (2*(k+1))-properHorizonSlope (2*k+1) =
      (1-Real.sqrt 2)/Real.sqrt (2*(k+1):ℕ) := by
  rw [properHorizonSlope,properHorizonSlope,show (2*(k+1))/2=k+1 by omega,
    show (2*k+1)/2=k by omega,show 2*(k+1)=2*k+1+1 by omega,sum_Ioc_succ_top (by omega)]
  have h := sum_Ioc_consecutive (fun j : ℕ => (Real.sqrt j)⁻¹) (Nat.le_succ k)
    (show k+1≤2*k+1 by omega)
  rw [sum_Ioc_succ_top le_rfl,Ioc_self,sum_empty,zero_add] at h
  have hh : Real.sqrt (2*k+1+1:ℕ) = Real.sqrt 2*Real.sqrt (k+1:ℕ) := by
    rw [show 2*k+1+1=2*(k+1) by omega,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  rw [hh,←h]
  have htwo := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hkp := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k) : 0<((k+1:ℕ):ℝ))
  field_simp [htwo.ne',hkp.ne']
  <;> ring

/-- The finite-ratio limit starts at the first cofactor and has exact
square-root growth through its first octave. -/
theorem first_active_proper_horizon {t : ℝ} (hl : 1≤t) (hu : t≤2) :
    properHorizonProfile t = Real.sqrt t-1 := by
  rw [proper_profile_on_unit_cell 1 (by simpa using hl) (by norm_num; exact hu)]
  norm_num [properHorizonSlope]

#print axioms proper_profile_on_unit_cell
#print axioms proper_slope_at_odd
#print axioms proper_slope_at_even
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
