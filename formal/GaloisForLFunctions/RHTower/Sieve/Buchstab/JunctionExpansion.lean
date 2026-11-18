import GaloisForLFunctions.RHTower.Sieve.Buchstab.GlobalDelay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive expansion of the Buchstab function at integer junctions

Successive continuations of the interval profiles differ by an iterated
positive primitive. Its factorial leading coefficient is the first term
by which the branches disagree. Summing the differences recovers the
original function pointwise on every cell.
-/

namespace RHTower.Sieve.Buchstab
open MeasureTheory Set Filter Topology Finset
noncomputable section

/-- Difference from the preceding branch continued to the next interval. -/
def junctionGap : ℕ → ℝ → ℝ
  | 0 => profile 0
  | n+1 => fun x => profile (n+1) x - profile n (x+1)

private theorem gap_continuous (n : ℕ) : Continuous (junctionGap n) := by
  cases n with
  | zero => exact profile_continuous 0
  | succ n => exact (profile_continuous _).sub ((profile_continuous _).comp (continuous_id.add_const 1))

/-- Each new branch difference is a positive primitive of the preceding one
divided by the physical argument of the delay equation. -/
theorem junctionGap_primitive (n : ℕ) (x : Ici (0:ℝ)) :
    junctionGap (n+1) x = (∫ t in (0:ℝ)..x.val, junctionGap n t)/((n:ℝ)+2+x.val) := by
  have hx : 0 ≤ x.val := x.property
  cases n with
  | zero =>
    change profile (0+1) x.val - profile 0 (x.val+1) =
      (∫ t in (0:ℝ)..x.val, profile 0 t)/((0:ℝ)+2+x.val)
    have hb : profile 0 1 = 1/2 := by norm_num [profile,intervalMass]
    have ht : profile 0 (x.val+1) = 1/(2+x.val) := by
      simp only [profile,intervalMass,Nat.cast_zero,zero_add,max_eq_left (show 0 ≤ x.val+1 by linarith)]
      ring
    simp only [profile_succ_mean 0 hx,hb,ht,Nat.cast_zero,zero_add]
    ring
  | succ n =>
    let d : ℝ := ((n+1:ℕ):ℝ)+2+x.val
    have he : d = (n:ℝ)+2+(x.val+1) := by dsimp [d]; push_cast; ring
    have hn := profile_succ_mean n (show 0 ≤ x.val+1 by linarith)
    have h₁ := profile_succ_mean n (show (0:ℝ) ≤ 1 by norm_num)
    have h₀ : ((n+1:ℕ):ℝ)+2 = (n:ℝ)+2+1 := by push_cast; ring
    rw [← he] at hn
    have hd : (n:ℝ)+2+1 ≠ 0 := by positivity
    have hc : (((n+1:ℕ):ℝ)+2)*profile (n+1) 1 =
        ((n:ℝ)+2)*profile n 1 + ∫ t in (0:ℝ)..1, profile n t := by
      rw [h₀,h₁]
      field_simp
    have hs : (∫ t in (0:ℝ)..x.val, profile n (t+1)) =
        ∫ t in (1:ℝ)..(x.val+1), profile n t := by
      simpa only [zero_add] using intervalIntegral.integral_comp_add_right (profile n) 1 (a:=0) (b:=x.val)
    have ha := intervalIntegral.integral_add_adjacent_intervals
      ((profile_continuous n).intervalIntegrable (μ:=volume) 0 1)
      ((profile_continuous n).intervalIntegrable (μ:=volume) 1 (x.val+1))
    change profile (n+1+1) x.val-profile (n+1) (x.val+1) =
      (∫ t in (0:ℝ)..x.val, profile (n+1) t-profile n (t+1))/d
    have hshift : Continuous (fun t : ℝ => profile n (t+1)) :=
      (profile_continuous n).comp (continuous_id.add_const 1)
    rw [profile_succ_mean _ hx,hn,hc,← ha,intervalIntegral.integral_sub
      ((profile_continuous (n+1)).intervalIntegrable (μ:=volume) 0 x.val)
      (hshift.intervalIntegrable (μ:=volume) 0 x.val),hs]
    dsimp only [d]
    ring

/-- Reciprocal of the two adjacent factorials controlling the new term. -/
def junctionCoefficient (n : ℕ) : ℝ := 1/((n.factorial:ℝ)*((n+1).factorial:ℝ))

private theorem junctionCoefficient_pos (n : ℕ) : 0 < junctionCoefficient n := by
  unfold junctionCoefficient
  positivity

private theorem coefficient_succ (n : ℕ) :
    junctionCoefficient (n+1) = junctionCoefficient n / ((n:ℝ)+1) / ((n:ℝ)+2) := by
  unfold junctionCoefficient
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem integral_scaled_power (c x : ℝ) (n : ℕ) :
    (∫ t in (0:ℝ)..x, c*t^n) = c*x^(n+1)/((n:ℝ)+1) := by
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n),sub_zero]
  ring

/-- Global two-sided bounds. They agree to leading order at every junction
and give a strict sign for the difference of the continuations. -/
theorem junctionGap_bounds (n : ℕ) (x : Ici (0:ℝ)) :
    junctionGap n x ∈ Icc (junctionCoefficient n*x.val^n/(1+x.val)^(n+1))
      (junctionCoefficient n*x.val^n) := by
  have hx : 0 ≤ x.val := x.property
  induction n generalizing x with
  | zero =>
    simp only [junctionGap,junctionCoefficient,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,
      div_one,pow_zero,pow_one,mul_one,profile,intervalMass,Nat.cast_zero,zero_add,max_eq_left hx]
    exact ⟨le_rfl,(div_le_one (by linarith)).mpr (by linarith)⟩
  | succ n ih =>
    let c := junctionCoefficient n
    let d := (1+x.val)^(n+1)
    have hc : 0 ≤ c := (junctionCoefficient_pos n).le
    have hd : 0 < d := pow_pos (by linarith) _
    have hx' : 0 < 1+x.val := by linarith
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hm : 0 < (n:ℝ)+2 := by positivity
    have hden : 0 < (n:ℝ)+2+x.val := by linarith
    have hlo (t : ℝ) (ht : t ∈ Icc 0 x.val) : (c/d)*t^n ≤ junctionGap n t := by
      have h := (ih ⟨t,ht.1⟩ ht.1).1
      have hpow : (1+t)^(n+1) ≤ d := pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [ht.2]) _
      calc
        _ = c*t^n/d := by ring
        _ ≤ c*t^n/(1+t)^(n+1) := div_le_div_of_nonneg_left (mul_nonneg hc (pow_nonneg ht.1 _))
          (pow_pos (by linarith [ht.1]) _) hpow
        _ ≤ _ := h
    have hhi (t : ℝ) (ht : t ∈ Icc 0 x.val) : junctionGap n t ≤ c*t^n := (ih ⟨t,ht.1⟩ ht.1).2
    have hi (a : ℝ) : IntervalIntegrable (fun t : ℝ => a*t^n) volume 0 x :=
      (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
    have hL := intervalIntegral.integral_mono_on hx (hi (c/d)) ((gap_continuous n).intervalIntegrable _ _) hlo
    have hU := intervalIntegral.integral_mono_on hx ((gap_continuous n).intervalIntegrable _ _) (hi c) hhi
    rw [integral_scaled_power] at hL hU
    rw [junctionGap_primitive,coefficient_succ]
    constructor
    · apply (le_div_iff₀ hden).mpr
      apply le_trans _ hL
      have hk : (n:ℝ)+2+x.val ≤ ((n:ℝ)+2)*(1+x.val) := by nlinarith only [mul_nonneg hn.le hx]
      have hp : 0 ≤ c/((n:ℝ)+1)/((n:ℝ)+2)*x.val^(n+1)/(1+x.val)^(n+1+1) := by positivity
      apply (mul_le_mul_of_nonneg_left hk hp).trans_eq
      dsimp only [d]
      rw [pow_succ (1+x.val) (n+1)]
      field_simp [hx'.ne',hn.ne',hm.ne']
    · apply (div_le_div_of_nonneg_right hU hden.le).trans
      calc
        _ ≤ c*x.val^(n+1)/((n:ℝ)+1)/((n:ℝ)+2) := div_le_div_of_nonneg_left (by positivity) hm (by linarith)
        _ = _ := by ring

theorem junctionGap_pos (n : ℕ) (x : Ioi (0:ℝ)) : 0 < junctionGap n x := by
  have hx : 0 < x.val := x.property
  exact (div_pos (mul_pos (junctionCoefficient_pos n) (pow_pos hx n))
    (pow_pos (add_pos zero_lt_one hx) (n+1))).trans_le (junctionGap_bounds n ⟨x.val,hx.le⟩).1

/-- The first discrepancy at junction n+1 has exact order n and leading
coefficient 1/(n!(n+1)!). -/
theorem junctionGap_leading (n : ℕ) :
    Tendsto (fun x => junctionGap n x/x^n) (𝓝[>] (0:ℝ)) (𝓝 (junctionCoefficient n)) := by
  have hc : ContinuousAt (fun x : ℝ => junctionCoefficient n/(1+x)^(n+1)) 0 := by fun_prop (disch := norm_num)
  have hlo : Tendsto (fun x : ℝ => junctionCoefficient n/(1+x)^(n+1)) (𝓝[>] 0) (𝓝 (junctionCoefficient n)) :=
    by simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (0:ℝ) < x at hx
    have h := (junctionGap_bounds n ⟨x,le_of_lt hx⟩).1
    apply (le_div_iff₀ (pow_pos hx n)).mpr
    simpa only [div_mul_eq_mul_div] using h
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (0:ℝ) < x at hx
    exact (div_le_iff₀ (pow_pos hx n)).mpr (junctionGap_bounds n ⟨x,le_of_lt hx⟩).2

/-- The complete function is a locally finite sum of positive contributions
born at successive integers. -/
theorem buchstab_cell_expansion (n : ℕ) (x : Icc (0:ℝ) 1) :
    buchstab ((n:ℝ)+1+x.val) =
      ∑ j ∈ range (n+1), junctionGap j ((n:ℝ)+x.val-j) := by
  have he (k : ℕ) (y : ℝ) : profile k y =
      ∑ j ∈ range (k+1), junctionGap j ((k:ℝ)+y-j) := by
    induction k generalizing y with
    | zero => simp [junctionGap]
    | succ k ih =>
      rw [sum_range_succ]
      simp only [Nat.cast_succ,add_sub_cancel_left]
      have hh (j : ℕ) : (k:ℝ)+1+y-j = k+(y+1)-j := by ring
      simp_rw [hh,← ih]
      change profile (k+1) y = profile k (y+1) + (profile (k+1) y-profile k (y+1))
      ring
  rw [buchstab_cell n x x.property,he]

#print axioms junctionGap_primitive
#print axioms junctionGap_leading
#print axioms buchstab_cell_expansion
end
end RHTower.Sieve.Buchstab
