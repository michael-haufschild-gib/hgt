import GaloisForLFunctions.SignedArithmeticCorrespondences.CountingTheTrianglesOfThePrimeContactMatrix
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Slopes of the cubic trace on dilated integer windows

On `(N,⌊xN⌋]`, division by `N` turns the number of starting sites for
outer ratio `r` into the positive part of `x/r-1`. The resulting
piecewise affine trace changes slope at every proper prime power.
-/
noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments

/-- Limiting trace per unit of the lower endpoint for dilation `x`. -/
def cubicDilationProfile (x : ℝ) : ℝ :=
  6*∑ r ∈ Icc 2 ⌊x⌋₊, max (x/(r:ℝ)-1) 0 * trianglePrice r

private theorem starting_sites_limit {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    Tendsto (fun n : ℕ => ((⌊x*n⌋₊/r-n:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (max (x/(r:ℝ)-1) 0)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (div_nonneg hx (Nat.cast_nonneg r))).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply ((h.sub_const 1).max (tendsto_const_nhds (x:=(0:ℝ)))).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  change max ((⌊(x/(r:ℝ))*(n:ℝ)⌋₊:ℝ)/(n:ℝ)-1) 0 = _
  rw [show (x/(r:ℝ))*(n:ℝ)=(x*n)/r by ring,Nat.floor_div_natCast]
  by_cases room : n ≤ ⌊x*n⌋₊/r
  · rw [Nat.cast_sub room,sub_div,div_self np.ne',max_eq_left (sub_nonneg.mpr
      ((one_le_div np).mpr (Nat.cast_le.mpr room)))]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge room),Nat.cast_zero,zero_div,
      max_eq_right (sub_nonpos.mpr ((div_le_one np).mpr (Nat.cast_le.mpr (le_of_not_ge room))))]

/-- The actual finite matrices have the dilation profile as their limit. -/
theorem cubic_trace_on_dilated_windows {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => Matrix.trace ((primeContactMatrix n ⌊x*n⌋₊)^3)/(n:ℝ)) atTop
      (𝓝 (cubicDilationProfile x)) := by
  let K := ⌊x⌋₊
  have total := tendsto_finsetSum (Icc 2 K)
    (fun r _ => (starting_sites_limit hx r).mul_const (trianglePrice r))
  apply (total.const_mul 6).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  let B := ⌊x*n⌋₊
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have kb : K ≤ B := Nat.floor_mono (le_mul_of_one_le_right hx (Nat.one_le_cast.mpr hn))
  have trunc : (∑ r∈Icc 2 K,((B/r-n:ℕ):ℝ)*trianglePrice r) =
      ∑ r∈Icc 2 B,((B/r-n:ℕ):ℝ)*trianglePrice r := by
    apply sum_subset (Icc_subset_Icc_right kb)
    intro r hr absent
    have kr : K < r := lt_of_not_ge (fun u => absent (mem_Icc.mpr ⟨(mem_Icc.mp hr).1,u⟩))
    have rx := (Nat.floor_lt hx).mp kr
    have below : B < n*r := (Nat.floor_lt (mul_nonneg hx np.le)).mpr (by
      rw [Nat.cast_mul,mul_comm (n:ℝ)]
      exact mul_lt_mul_of_pos_right rx np)
    have rp : 0 < r := (by decide : 0 < 2).trans_le (mem_Icc.mp hr).1
    rw [Nat.sub_eq_zero_of_le ((Nat.div_lt_iff_lt_mul rp).mpr below).le,Nat.cast_zero,zero_mul]
  change 6*(∑ r∈Icc 2 K,((B/r-n:ℕ):ℝ)/(n:ℝ)*trianglePrice r) =
    Matrix.trace ((primeContactMatrix n B)^3)/(n:ℝ)
  rw [cubic_prime_contact_floor_sum,←trunc,mul_div_assoc,Finset.sum_div]
  exact congrArg ((6:ℝ)*·) (sum_congr rfl fun _ _ => by ring)

/-- Slope on the unit interval starting at `k`. -/
def cubicDilationSlope (k : ℕ) : ℝ := 6*∑ r∈Icc 2 k,trianglePrice r/(r:ℝ)

private theorem profile_on_band {k : ℕ} {x : ℝ} (lo : (k:ℝ) ≤ x) (hi : x ≤ (k:ℝ)+1) :
    cubicDilationProfile x = 6*∑ r∈Icc 2 k,(x/(r:ℝ)-1)*trianglePrice r := by
  have sub : Icc 2 k ⊆ Icc 2 ⌊x⌋₊ := Icc_subset_Icc_right (Nat.le_floor lo)
  unfold cubicDilationProfile
  apply congrArg ((6:ℝ)*·)
  calc
    _ = ∑ r∈Icc 2 k,max (x/(r:ℝ)-1) 0 * trianglePrice r := by
      symm
      apply sum_subset sub
      intro r hr out
      have kr : k < r := lt_of_not_ge (fun h => out (mem_Icc.mpr ⟨(mem_Icc.mp hr).1,h⟩))
      have xr : x ≤ (r:ℝ) := hi.trans (by exact_mod_cast (show k+1 ≤ r from kr))
      have rp : 0 < (r:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le k).trans_lt kr)
      rw [max_eq_right (sub_nonpos.mpr ((div_le_one rp).mpr xr)),zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      have rp : 0 < (r:ℝ) := Nat.cast_pos.mpr ((by decide : 0<2).trans_le (mem_Icc.mp hr).1)
      rw [max_eq_left (sub_nonneg.mpr ((one_le_div rp).mpr ((Nat.cast_le.mpr (mem_Icc.mp hr).2).trans lo)))]

theorem cubic_dilation_profile_difference {k : ℕ} {x y : ℝ} (xl : (k:ℝ) ≤ x) (xh : x ≤ (k:ℝ)+1)
    (yl : (k:ℝ) ≤ y) (yh : y ≤ (k:ℝ)+1) :
    cubicDilationProfile y-cubicDilationProfile x = (y-x)*cubicDilationSlope k := by
  rw [profile_on_band yl yh,profile_on_band xl xh,←mul_sub,←sum_sub_distrib,cubicDilationSlope,
    mul_left_comm (y-x) 6,mul_sum]
  rw [mul_sum,mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- At a proper prime power the right slope exceeds the left slope by
six times the triangle weight divided by the outer ratio. -/
theorem cubic_dilation_slope_jump {p b : ℕ} (hp : p.Prime) (hb : 1 < b) :
    cubicDilationSlope (p^b)-cubicDilationSlope (p^b-1) =
      6*((b:ℝ)-1)*(Real.log p)^3/((p^b:ℕ):ℝ) ∧
    cubicDilationSlope (p^b-1) < cubicDilationSlope (p^b) := by
  have two : 2 ≤ p^b := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have k : p^b-1+1=p^b := by omega
  have step := sum_Icc_succ_top (f:=fun r : ℕ => trianglePrice r/(r:ℝ))
    (show 2 ≤ p^b-1+1 by omega)
  rw [k] at step
  have price : cubicDilationSlope (p^b)-cubicDilationSlope (p^b-1) =
      6*((b:ℝ)-1)*(Real.log p)^3/((p^b:ℕ):ℝ) := by
    rw [cubicDilationSlope,cubicDilationSlope,step,trianglePrice_prime_power hp (by omega)]
    ring
  refine ⟨price,sub_pos.mp ?_⟩
  rw [price]
  have bl : 0 < (b:ℝ)-1 := sub_pos.mpr (Nat.one_lt_cast.mpr hb)
  have lp := Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt : (1:ℝ) < p)
  positivity

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments
