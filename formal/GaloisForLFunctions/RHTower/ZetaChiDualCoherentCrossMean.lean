import GaloisForLFunctions.RHTower.ZetaChiDualRationalBlock
import GaloisForLFunctions.RHTower.ZetaChiDualCoherentBlock

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The literal Gaussian-smoothed integer block used in the physical first-mean calculation. -/
def zetaChiDualCoherentCarrier (s : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ zetaChiDualCoherentBlock m,
    smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) * zetaChiDualInteriorAtom s n t

/-- A fixed open ratio neighborhood preserves every saddle margin of the complete block. -/
theorem zetaChiDualCoherentBlock_ratio_saddle {m : ℕ} (hm : 1 ≤ m)
    {n : ℕ} (hn : n ∈ zetaChiDualCoherentBlock m)
    {ξ : ℝ} (hξlo : 49 / 50 ≤ ξ) (hξhi : ξ ≤ 51 / 50) :
    (5 * (m : ℝ)) ^ 10 + (5 * (m : ℝ)) ^ 6 ≤ 2 * Real.pi * (ξ * n) ∧
      2 * Real.pi * (ξ * n) + (5 * (m : ℝ)) ^ 6 ≤ 2 * (5 * (m : ℝ)) ^ 10 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlo : (5 : ℝ) ^ 9 * (m : ℝ) ^ 10 ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hup : (n : ℝ) ≤ 6 * (5 : ℝ) ^ 8 * (m : ℝ) ^ 10 := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hpow : (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 10 := by
    have h4 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hmR
    nlinarith only [mul_nonneg (sub_nonneg.mpr h4) (show 0 ≤ (m : ℝ) ^ 6 by positivity)]
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hξ : 0 ≤ ξ := by linarith
  have hphaseLo : 6 * (49 / 50 : ℝ) * n ≤ 2 * Real.pi * (ξ * n) := by
    calc
      _ ≤ 6 * ξ * n := by gcongr
      _ = 6 * (ξ * n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (mul_nonneg hξ hnn)
  have hphaseHi : 2 * Real.pi * (ξ * n) ≤ 8 * (51 / 50 : ℝ) * n := by
    calc
      _ ≤ 8 * (ξ * n) := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (mul_nonneg hξ hnn)
      _ = 8 * ξ * n := by ring
      _ ≤ _ := by gcongr
  constructor <;> nlinarith only [hlo, hup, hpow, hphaseLo, hphaseHi,
    show 0 ≤ (m : ℝ) ^ 6 by positivity]

private theorem norm_ratio_cpow_le_two {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ ≤ 2) : ‖(ξ : ℂ) ^ (1 - s)‖ ≤ 2 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hξ]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ (2 : ℝ) ^ (1 - s.re) := Real.rpow_le_rpow hξ.le hξ2 (by linarith)
    _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := Real.rpow_one 2

private theorem sum_zetaChiDualCoherentBlock_eq_range (m : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ zetaChiDualCoherentBlock m, f n =
      ∑ j ∈ Finset.range (5 ^ 8 * m ^ 10 + 1), f (5 ^ 9 * m ^ 10 + j) := by
  have htop : 6 * 5 ^ 8 * m ^ 10 = 5 ^ 9 * m ^ 10 + 5 ^ 8 * m ^ 10 := by ring
  symm
  apply Finset.sum_bij (fun j _ => 5 ^ 9 * m ^ 10 + j)
  · intro j hj
    apply Finset.mem_Icc.mpr
    have hlt := Finset.mem_range.mp hj
    constructor <;> omega
  · intro i _ j _ hij
    omega
  · intro n hn
    have hlo := (Finset.mem_Icc.mp hn).1
    have hup := (Finset.mem_Icc.mp hn).2
    refine ⟨n - 5 ^ 9 * m ^ 10, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  · intro j _
    rfl

/-- Uniform off-divisibility first cross moments for the full literal coherent
block. The constant is independent of both rational numerator and denominator. -/
theorem exists_zetaChi_dual_coherent_cross_mean_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ a q : ℕ, 0 < q → ¬ q ∣ a → 49 / 50 ≤ (a : ℝ) / q → (a : ℝ) / q ≤ 51 / 50 →
      ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
        zetaChiDualCoherentCarrier s m t * bourgainOscillation (t * Real.log ((a : ℝ) / q))‖ ≤
        C * ((q : ℝ) + (5 * (m : ℝ)) ^ 10 / m) := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_dual_rational_block_integral_bound c hr hc0 hc1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hb
  refine ⟨4 * Real.pi + 2 * D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with m hmM hm1
  intro s hs a q hq hdiv hξlo hξhi
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  let A : ℕ := 5 ^ 9 * m ^ 10
  let K : ℕ := 5 ^ 8 * m ^ 10 + 1
  have hmNat : 0 < m := by omega
  have hA : 0 < A := by dsimp [A]; positivity
  have hmem (j : ℕ) (hj : j ∈ Finset.range K) : A + j ∈ zetaChiDualCoherentBlock m := by
    apply Finset.mem_Icc.mpr
    have hlt := Finset.mem_range.mp hj
    dsimp [A]
    dsimp [K] at hlt
    have htop : 6 * 5 ^ 8 * m ^ 10 = 5 ^ 9 * m ^ 10 + 5 ^ 8 * m ^ 10 := by ring
    constructor <;> omega
  have hbnd := hM (5 * m) (by omega) s hs a q A K hq hdiv hA
    (fun j hj => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      zetaChiDualCoherentBlock_ratio_saddle hm1 (hmem j hj) hξlo hξhi)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hbnd
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 ≤ s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re ≤ 1 := by linarith [(abs_le.mp hre).2]
  have hcoef : ‖(((a : ℝ) / q : ℝ) : ℂ) ^ (1 - s)‖ ≤ 2 :=
    norm_ratio_cpow_le_two hs0 hs1 (by linarith) (by linarith)
  have hK : (K : ℝ) ≤ (5 * (m : ℝ)) ^ 10 := by
    dsimp [K]
    push_cast
    have hp : (1 : ℝ) ≤ (m : ℝ) ^ 10 := one_le_pow₀ hmR
    nlinarith only [hp]
  have hfrac : D / (5 * (m : ℝ)) ≤ D / m :=
    div_le_div_of_nonneg_left hD.le hm0 (by linarith)
  have hcost : (D / (5 * (m : ℝ))) * K ≤ D * ((5 * (m : ℝ)) ^ 10 / m) := by
    calc
      _ ≤ (D / m) * (5 * (m : ℝ)) ^ 10 :=
        mul_le_mul hfrac hK (Nat.cast_nonneg K) (by positivity)
      _ = _ := by ring
  have hupper := hbnd.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
  have hsmall : ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
      ∑ n ∈ Finset.range K, smoothAFECutoff (((A + n : ℕ) : ℝ) / (5 * (m : ℝ)) ^ 10) *
        zetaChiDualInteriorAtom s (A + n) t * bourgainOscillation (t * Real.log ((a : ℝ) / q))‖ ≤
      (4 * Real.pi + 2 * D) * ((q : ℝ) + (5 * (m : ℝ)) ^ 10 / m) := by
    have hpq := mul_nonneg hD.le (Nat.cast_nonneg q)
    have hpiN := mul_nonneg Real.pi_pos.le (show 0 ≤ (5 * (m : ℝ)) ^ 10 / m by positivity)
    nlinarith only [hupper, hcost, hpq, hpiN]
  have hint : (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
      zetaChiDualCoherentCarrier s m t * bourgainOscillation (t * Real.log ((a : ℝ) / q))) =
      (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
        ∑ n ∈ Finset.range K, smoothAFECutoff (((A + n : ℕ) : ℝ) / (5 * (m : ℝ)) ^ 10) *
          zetaChiDualInteriorAtom s (A + n) t * bourgainOscillation (t * Real.log ((a : ℝ) / q))) := by
    apply intervalIntegral.integral_congr
    intro t _
    unfold zetaChiDualCoherentCarrier
    dsimp only
    rw [Finset.sum_mul, sum_zetaChiDualCoherentBlock_eq_range]
  rw [hint]
  exact hsmall

end RHTower
