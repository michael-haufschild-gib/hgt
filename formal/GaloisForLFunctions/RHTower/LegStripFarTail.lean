/-
# The far-ahead energy envelope — exponential kernel decay to a polynomial tail

The reduced energy `W(m) = ¼Σ_k rcsch²((m − t_k)/2)` at the gap midpoint `m = harmMid c i` is
dominated at the near poles by the balanced-model steepness `π²/c²` (`harmonic_midpoint_energy_steepness`).
Promoting that to a general pole count `d` needs the contribution of the far-ahead poles `j ≥ 2i+2`
to vanish under the `(i+1)²` rescaling. The obstruction is that the near-pole bound
`rcsch²(z) < 1/z²` loses the exponential decay of the `csch²` kernel; this file supplies it.

* `rcsch_sq_le_exp` : `rcsch(z)² ≤ 4/(1−e^{−2z₀})²·e^{−2z}` for `0 < z₀ ≤ z` — the missing exponential
  decay of `1/sinh²`, from `e^z − e^{−z} = e^z(1 − e^{−2z}) ≥ e^z(1 − e^{−2z₀})`.
* `harmMid_far_dist_lower` : `harmPole c j − harmMid c i ≥ c·log((j+1)/(i+2))` for `j ≥ i+2` — the
  harmonic distance from a far pole to the midpoint, from the tree's harmonic-log tail bound.
* `farEnergy_term_le` : for `j ≥ 2i+2`, `rcsch²((harmPole c j − harmMid c i)/2) ≤ C_c·((i+2)/(j+1))^c`
  with `C_c = 4/(1−(2/3)^c)²` a fixed constant (the uniform floor `(j+1)/(i+2) ≥ 3/2`). The exponential
  kernel is turned into a polynomial `p`-series envelope in `j` — the exact analog, for the energy, of
  the rational per-term envelope that controls the truncation train.
-/
import GaloisForLFunctions.RHTower.LegStripSteepnessHarmonic
open Real Set
noncomputable section
namespace RHTower

/-- Exponential decay of `rcsch² = 1/sinh²`: for `0 < z₀ ≤ z`, `rcsch(z)² ≤ 4/(1−e^{−2z₀})²·e^{−2z}`.
The near-pole bound `rcsch²(z) < 1/z²` captures only the `z → 0` behaviour; this is the `z → ∞` tail. -/
theorem rcsch_sq_le_exp {z z₀ : ℝ} (hz₀ : 0 < z₀) (hz : z₀ ≤ z) :
    (rcsch z)^2 ≤ 4/(1 - Real.exp (-(2*z₀)))^2 * Real.exp (-(2*z)) := by
  have hz0 : 0 < z := lt_of_lt_of_le hz₀ hz
  have hB0 : 0 < 1 - Real.exp (-(2*z₀)) := by
    have : Real.exp (-(2*z₀)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hBz : 1 - Real.exp (-(2*z₀)) ≤ 1 - Real.exp (-(2*z)) := by
    have : Real.exp (-(2*z)) ≤ Real.exp (-(2*z₀)) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hd : Real.exp z - Real.exp (-z) = Real.exp z * (1 - Real.exp (-(2*z))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
  have hpos : 0 < Real.exp z * (1 - Real.exp (-(2*z₀))) := by positivity
  have hge : Real.exp z * (1 - Real.exp (-(2*z₀))) ≤ Real.exp z - Real.exp (-z) := by
    rw [hd]; exact mul_le_mul_of_nonneg_left hBz (Real.exp_pos z).le
  have hsinh : Real.sinh z = (Real.exp z - Real.exp (-z))/2 := Real.sinh_eq z
  have hsq : (rcsch z)^2 = 4/(Real.exp z - Real.exp (-z))^2 := by
    rw [rcsch, hsinh]; rw [div_pow, div_pow]; norm_num
  have hexpsq : Real.exp (2*z) = (Real.exp z)^2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hden : Real.exp (2*z) * (1 - Real.exp (-(2*z₀)))^2 ≤ (Real.exp z - Real.exp (-z))^2 := by
    rw [hexpsq, ← mul_pow]
    exact pow_le_pow_left₀ hpos.le hge 2
  rw [hsq]
  calc 4/(Real.exp z - Real.exp (-z))^2
      ≤ 4/(Real.exp (2*z) * (1 - Real.exp (-(2*z₀)))^2) := by
        have hpd : 0 < Real.exp (2*z) * (1 - Real.exp (-(2*z₀)))^2 := by positivity
        exact div_le_div_of_nonneg_left (by norm_num) hpd hden
  _ = 4/(1 - Real.exp (-(2*z₀)))^2 * Real.exp (-(2*z)) := by
        rw [Real.exp_neg (2*z), mul_comm (Real.exp (2*z)) ((1 - Real.exp (-(2*z₀)))^2),
          ← div_div, div_eq_mul_inv]

/-- Distance from a far pole `j ≥ i+2` to the gap midpoint `m = harmMid c i`, bounded below by the
logarithm `c·log((j+1)/(i+2))` via the harmonic-log tail. -/
theorem harmMid_far_dist_lower {c : ℝ} (hc : 0 < c) {i j : ℕ} (hj : i + 2 ≤ j) :
    c * Real.log (((j:ℝ)+1)/((i:ℝ)+2)) ≤ harmPole c j - harmMid c i := by
  have hi1 : 1 ≤ i + 2 := by omega
  have hsplit : harmPole c j - harmPole c (i+1)
      = c * ∑ l ∈ Finset.Ico (i+1) j, 1/((l:ℝ)+1) := by
    rw [harmPole, harmPole, ← mul_sub]
    congr 1
    have h := Finset.sum_range_add_sum_Ico (fun l => 1/((l:ℝ)+1)) (by omega : i+1 ≤ j)
    simp only [] at h
    linarith
  have hre : (∑ l ∈ Finset.Ico (i+1) j, 1/((l:ℝ)+1))
      = ∑ p ∈ Finset.range (j-(i+1)), 1/(((i+2:ℕ):ℝ)+p) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro p _; push_cast; ring
  have hk : (i+2) + (j-(i+1)) = j + 1 := by omega
  have hlog := harmonic_log_upper (i+2) hi1 (j-(i+1))
  rw [hre] at hsplit
  have hmid : harmPole c (i+1) - harmMid c i = c/(2*((i:ℝ)+1)) := by
    have hne : ((i:ℝ)+1) ≠ 0 := by positivity
    rw [harmMid, harmPole_succ]; field_simp; ring
  have hcast : (((i+2:ℕ):ℝ)+(((j-(i+1)):ℕ):ℝ)) = (j:ℝ)+1 := by
    rw [Nat.cast_sub (by omega : i+1 ≤ j)]; push_cast; ring
  have hpos : 0 ≤ c/(2*((i:ℝ)+1)) := by positivity
  have hgoal : c * Real.log (((j:ℝ)+1)/((i:ℝ)+2)) ≤ harmPole c j - harmPole c (i+1) := by
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ hc.le
    calc Real.log (((j:ℝ)+1)/((i:ℝ)+2))
        = Real.log (((((i+2:ℕ):ℝ)+(((j-(i+1)):ℕ):ℝ)))/((i+2:ℕ):ℝ)) := by
          rw [hcast]; norm_num
      _ ≤ _ := hlog
  linarith [hmid, hgoal, hpos]

/-- **Far-ahead energy envelope.** For `j ≥ 2i+2` the energy kernel at a far pole is bounded by a
polynomial `p`-series term: `rcsch²((harmPole c j − harmMid c i)/2) ≤ 4/(1−(2/3)^c)²·((i+2)/(j+1))^c`.
The uniform floor `(j+1)/(i+2) ≥ 3/2` fixes the constant; the exponential kernel decay becomes the
`((i+2)/(j+1))^c` polynomial tail. -/
theorem farEnergy_term_le {c : ℝ} (hc : 0 < c) {i j : ℕ} (hj : 2*i+2 ≤ j) :
    (rcsch ((harmPole c j - harmMid c i)/2))^2
      ≤ 4/(1 - Real.exp (-(c * Real.log (3/2))))^2 * (((i:ℝ)+2)/((j:ℝ)+1))^c := by
  have hij : i + 2 ≤ j := by omega
  have hdist := harmMid_far_dist_lower hc hij
  -- ratio floor: (j+1)/(i+2) ≥ 3/2, so log((j+1)/(i+2)) ≥ log(3/2)
  have hfrac : (3:ℝ)/2 ≤ ((j:ℝ)+1)/((i:ℝ)+2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (2:ℝ)*i + 3 ≤ (j:ℝ)+1 := by
      have : 2*i+3 ≤ j+1 := by omega
      exact_mod_cast this
    nlinarith [this, Nat.cast_nonneg (α := ℝ) i]
  have hlogfloor : Real.log (3/2) ≤ Real.log (((j:ℝ)+1)/((i:ℝ)+2)) :=
    Real.log_le_log (by norm_num) hfrac
  -- z₀ = c·log(3/2)/2 ≤ z = dist/2
  have hz₀pos : 0 < c * Real.log (3/2) / 2 := by
    have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    positivity
  have hz : c * Real.log (3/2) / 2 ≤ (harmPole c j - harmMid c i)/2 := by
    have h1 : c * Real.log (3/2) ≤ c * Real.log (((j:ℝ)+1)/((i:ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hlogfloor hc.le
    linarith [hdist]
  have hbound := rcsch_sq_le_exp hz₀pos hz
  -- rewrite the exp arguments: 2·(c log(3/2)/2) = c log(3/2), 2·(dist/2) = dist
  have e1 : 2 * (c * Real.log (3/2) / 2) = c * Real.log (3/2) := by ring
  have e2 : 2 * ((harmPole c j - harmMid c i)/2) = harmPole c j - harmMid c i := by ring
  rw [e1, e2] at hbound
  -- exp(-dist) ≤ ((i+2)/(j+1))^c
  have hfracpos : 0 < ((i:ℝ)+2)/((j:ℝ)+1) := by positivity
  have hexptail : Real.exp (-(harmPole c j - harmMid c i)) ≤ (((i:ℝ)+2)/((j:ℝ)+1))^c := by
    rw [Real.rpow_def_of_pos hfracpos]
    apply Real.exp_le_exp.mpr
    have hlogrecip : Real.log (((i:ℝ)+2)/((j:ℝ)+1)) = -Real.log (((j:ℝ)+1)/((i:ℝ)+2)) := by
      rw [← Real.log_inv]; congr 1; rw [inv_div]
    rw [hlogrecip]
    have h2 : c * Real.log (((j:ℝ)+1)/((i:ℝ)+2)) ≤ harmPole c j - harmMid c i := hdist
    nlinarith [h2]
  have hCpos : 0 < 4/(1 - Real.exp (-(c * Real.log (3/2))))^2 := by
    have hlt : Real.exp (-(c * Real.log (3/2))) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
      nlinarith [this]
    have : 0 < 1 - Real.exp (-(c * Real.log (3/2))) := by linarith
    positivity
  calc (rcsch ((harmPole c j - harmMid c i)/2))^2
      ≤ 4/(1 - Real.exp (-(c * Real.log (3/2))))^2 * Real.exp (-(harmPole c j - harmMid c i)) := hbound
  _ ≤ 4/(1 - Real.exp (-(c * Real.log (3/2))))^2 * (((i:ℝ)+2)/((j:ℝ)+1))^c :=
        mul_le_mul_of_nonneg_left hexptail hCpos.le

end RHTower
end
