import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateCriticalBounds
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateExactOccupation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Critical zero-gate occupation

The fixed-cardinality overlap terms converge to the coefficients of an
exponential series. A factorial majorant permits summation over every
cardinality, yielding the critical circular-spacing limit.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev registerDimension (n : ℕ) : ℕ := 2 ^ n

private theorem cast_registerDimension (n : ℕ) :
    (registerDimension n : ℝ) = (2 : ℝ) ^ n := by
  simp only [registerDimension, Nat.cast_pow, Nat.cast_ofNat]

private theorem registerDimension_pos (n : ℕ) : 0 < (registerDimension n : ℝ) := by
  rw [cast_registerDimension]
  positivity

private theorem cast_registerDimension_sub_one (n : ℕ) :
    ((registerDimension n - 1 : ℕ) : ℝ) = (registerDimension n : ℝ) - 1 := by
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))), Nat.cast_one]

private abbrev criticalGap (y : ℝ) (n : ℕ) : ℝ := 1 - (zeroGateCriticalArcRadius y n : ℝ)

/-- Total joint mass over subsets of size `k`, including the empty subset of mass one. -/
def zeroGateAnchorBinomialMoment (D : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  (D.choose k : ℝ) * max 0 (1 - (k : ℝ) * (1 - r)) ^ (D - 1)

private theorem tendsto_normalizedChoose (k : ℕ) :
    Tendsto (fun D : ℕ => (D.choose k : ℝ) / (D : ℝ) ^ k) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  let f (i D : ℕ) : ℝ := 1 - (i : ℝ) / (D : ℝ)
  have hinv : Tendsto (fun D : ℕ => (D : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hf (i : ℕ) : Tendsto (f i) atTop (𝓝 (1 : ℝ)) := by
    simpa only [f, div_eq_mul_inv, mul_zero, sub_zero] using (hinv.const_mul (i : ℝ)).const_sub 1
  have hp : Tendsto (fun D => ∏ i ∈ Finset.range k, f i D) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Finset.prod_const_one] using tendsto_finsetProd (Finset.range k) (fun i _ => hf i)
  apply (hp.div_const (k.factorial : ℝ)).congr'
  filter_upwards [eventually_ge_atTop (max k 1)] with D hD
  have hD1 : (1 : ℕ) ≤ D := (le_max_right k 1).trans hD
  have hD0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD1)
  have he : (∏ i ∈ Finset.range k, f i D) = (D.descFactorial k : ℝ) / (D : ℝ) ^ k := by
    calc
      _ = ∏ i ∈ Finset.range k, ((D - i : ℕ) : ℝ) / (D : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiD := (Finset.mem_range.mp hi).le.trans ((le_max_left k 1).trans hD)
        dsimp only [f]
        rw [Nat.cast_sub hiD, sub_div, div_self hD0]
      _ = _ := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
          Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [he, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hk0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp [pow_ne_zero k hD0, hk0]

/-- Each binomial moment of the covering-anchor count has its Poisson limit. -/
theorem tendsto_zeroGateAnchorBinomialMoment (k : ℕ) (y : ℝ) :
    Tendsto (fun n => zeroGateAnchorBinomialMoment (2 ^ n) (zeroGateCriticalArcRadius y n) k)
      atTop (𝓝 (Real.exp (-y) ^ k / (k.factorial : ℝ))) := by
  have hD : Tendsto registerDimension atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hchoose := (tendsto_normalizedChoose k).comp hD
  have hsmall : ∀ᶠ n in atTop, (k : ℝ) * criticalGap y n < 1 := by
    have h := (tendsto_zeroGateCriticalGap y).const_mul (k : ℝ)
    rw [mul_zero] at h
    exact (tendsto_order.mp h).2 1 zero_lt_one
  have hpow : Tendsto (fun n => (registerDimension n : ℝ) ^ k *
      max 0 (1 - (k : ℝ) * criticalGap y n) ^ (registerDimension n - 1))
      atTop (𝓝 (Real.exp (-y) ^ k)) := by
    rw [← Real.exp_nat_mul, mul_neg]
    apply (tendsto_zeroGateCriticalAnchorPower k y).congr'
    filter_upwards [hsmall, eventually_zeroGateCriticalGap_eq y] with n hn he
    have hnonneg := sub_nonneg.mpr hn.le
    rw [max_eq_right hnonneg, cast_registerDimension]
    simp only [criticalGap, he]
  have hlim := hchoose.mul hpow
  rw [one_div, inv_mul_eq_div] at hlim
  apply hlim.congr
  intro n
  dsimp only [Function.comp_apply, zeroGateAnchorBinomialMoment, criticalGap]
  rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero k (registerDimension_pos n).ne')]

private theorem eventually_zeroGateAnchorBinomialMoment_le (y : ℝ) :
    ∀ᶠ n in atTop, ∀ k : ℕ,
      zeroGateAnchorBinomialMoment (registerDimension n) (zeroGateCriticalArcRadius y n) k ≤
        Real.exp (1 - y) ^ k / (k.factorial : ℝ) := by
  filter_upwards [eventually_zeroGateCriticalGap_eq y] with n hn k
  let D := registerDimension n
  let s := criticalGap y n
  have hD : 0 < (D : ℝ) := registerDimension_pos n
  have hs : s ≤ 1 := sub_le_self _ (zeroGateCriticalArcRadius y n).2.1
  have hscale : (D : ℝ) * s = Real.log (D : ℝ) + y := by
    change (registerDimension n : ℝ) * (1 - (zeroGateCriticalArcRadius y n : ℝ)) = _
    rw [show D = registerDimension n from rfl, cast_registerDimension, hn, mul_comm, div_mul_cancel₀ _
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
  have he : (D : ℝ) * Real.exp (-(((D : ℝ) - 1) * s)) = Real.exp (s - y) := by
    -- The factor `D` cancels the logarithm in the critical gap.
    calc
      _ = Real.exp (Real.log (D : ℝ) + -(((D : ℝ) - 1) * s)) := by rw [Real.exp_add, Real.exp_log hD]
      _ = _ := congrArg Real.exp (by linear_combination -hscale)
  have hb : max 0 (1 - (k : ℝ) * s) ≤ Real.exp (-((k : ℝ) * s)) := by
    refine max_le (Real.exp_nonneg _) ?_
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((k : ℝ) * s))
  have hp := pow_le_pow_left₀ (le_max_left (0 : ℝ) (1 - (k : ℝ) * s)) hb (D - 1)
  have hswap : Real.exp (-((k : ℝ) * s)) ^ (D - 1) =
      Real.exp (-(((D : ℝ) - 1) * s)) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, cast_registerDimension_sub_one n]
    congr 1
    ring
  calc
    _ ≤ (D.choose k : ℝ) * Real.exp (-(((D : ℝ) - 1) * s)) ^ k := by
      rw [← hswap]
      exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ ≤ ((D : ℝ) ^ k / (k.factorial : ℝ)) * Real.exp (-(((D : ℝ) - 1) * s)) ^ k :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k D) (by positivity)
    _ = Real.exp (s - y) ^ k / (k.factorial : ℝ) := by
      rw [div_mul_eq_mul_div, ← mul_pow, he]
    _ ≤ _ := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr (sub_le_sub_right hs y)) k)
      (Nat.cast_nonneg _)

private theorem one_sub_zeroGateArcOccupationPolynomial (D : ℕ) (r : ℝ) :
    1 - zeroGateArcOccupationPolynomial D r =
      ∑' k, (-1 : ℝ) ^ k * zeroGateAnchorBinomialMoment D r k := by
  let f (k : ℕ) := (-1 : ℝ) ^ k * zeroGateAnchorBinomialMoment D r k
  have hf : ∑' k, f k = ∑ k ∈ Finset.range (D + 1), f k := by
    apply tsum_eq_sum
    intro k hk
    have hdk : D < k := by
      simp only [Finset.mem_range] at hk
      omega
    simp only [f, zeroGateAnchorBinomialMoment, Nat.choose_eq_zero_of_lt hdk, Nat.cast_zero, zero_mul, mul_zero]
  have he : (Finset.range (D + 1)).erase 0 = Finset.Icc 1 D := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  change 1 - zeroGateArcOccupationPolynomial D r = ∑' k, f k
  rw [hf, ← Finset.add_sum_erase (Finset.range (D + 1)) f (Finset.mem_range.mpr (Nat.succ_pos D)), he]
  have hzero : f 0 = 1 := by simp [f, zeroGateAnchorBinomialMoment]
  rw [hzero, sub_eq_add_neg, zeroGateArcOccupationPolynomial, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [f, zeroGateAnchorBinomialMoment, pow_succ]
  ring

/-- The binomial-moment generating series converges at every real argument. -/
theorem tendsto_zeroGateAnchorBinomialSeries (y u : ℝ) :
    Tendsto (fun n => ∑' k : ℕ, u ^ k * zeroGateAnchorBinomialMoment (2 ^ n) (zeroGateCriticalArcRadius y n) k)
      atTop (𝓝 (Real.exp (u * Real.exp (-y)))) := by
  let f (n k : ℕ) := u ^ k *
    zeroGateAnchorBinomialMoment (registerDimension n) (zeroGateCriticalArcRadius y n) k
  let g (k : ℕ) := (u * Real.exp (-y)) ^ k / (k.factorial : ℝ)
  have hf (k : ℕ) : Tendsto (fun n => f n k) atTop (𝓝 (g k)) := by
    simpa only [f, g, mul_pow, mul_div_assoc] using
      (tendsto_zeroGateAnchorBinomialMoment k y).const_mul (u ^ k)
  have hbound : ∀ᶠ n in atTop, ∀ k, ‖f n k‖ ≤ (|u| * Real.exp (1 - y)) ^ k / (k.factorial : ℝ) := by
    filter_upwards [eventually_zeroGateAnchorBinomialMoment_le y] with n hn k
    have hnonneg : 0 ≤ zeroGateAnchorBinomialMoment (registerDimension n) (zeroGateCriticalArcRadius y n) k := by
      unfold zeroGateAnchorBinomialMoment
      positivity
    dsimp only [f]
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hnonneg, Real.norm_eq_abs, mul_pow, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hn k) (pow_nonneg (abs_nonneg _) _)
  have hg : HasSum g (Real.exp (u * Real.exp (-y))) := by
    simpa only [g, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (u * Real.exp (-y))
  have h := tendsto_tsum_of_dominated_convergence (Real.summable_pow_div_factorial _) hf hbound
  rwa [hg.tsum_eq] at h

/-- The critical occupation mass converges to the upper tail of the standard Gumbel law. -/
theorem tendsto_zeroGateCriticalArcMass (y : ℝ) :
    Tendsto (fun n => zeroGateFullArcMass n (zeroGateCriticalArcRadius y n)) atTop
      (𝓝 (1 - Real.exp (-Real.exp (-y)))) := by
  have h := tendsto_zeroGateAnchorBinomialSeries y (-1)
  rw [neg_one_mul] at h
  apply (h.const_sub 1).congr
  intro n
  rw [← one_sub_zeroGateArcOccupationPolynomial, sub_sub_cancel, zeroGateFullArcMass_eq_exactPolynomial]

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- On one typical Gaussian draw, the limiting time fractions in the
critical window approach the same Gumbel tail across the open prefixes. -/
theorem gaussian_path_zeroGateCriticalArcOccupation_limit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ y a : ℝ,
      (∀ k : ℕ,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        Tendsto (fun T => volume.real (zeroGateReturnSet H (zeroGateCriticalArcRadius y (k + 3)) ∩ Icc a T) / (T - a))
          atTop (𝓝 (zeroGateFullArcMass (k + 3) (zeroGateCriticalArcRadius y (k + 3))))) ∧
      Tendsto (fun k : ℕ => zeroGateFullArcMass (k + 3) (zeroGateCriticalArcRadius y (k + 3))) atTop
        (𝓝 (1 - Real.exp (-Real.exp (-y)))) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro y a
  exact ⟨fun k => hω k (zeroGateCriticalArcRadius y (k + 3)) a,
    (tendsto_zeroGateCriticalArcMass y).comp (tendsto_add_atTop_nat 3)⟩

#print axioms tendsto_zeroGateAnchorBinomialMoment
#print axioms tendsto_zeroGateAnchorBinomialSeries
#print axioms tendsto_zeroGateCriticalArcMass
#print axioms gaussian_path_zeroGateCriticalArcOccupation_limit

end

end GaloisForLFunctions.HTGeometry
