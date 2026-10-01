import GaloisForLFunctions.RHTower.SteinhausFinitePrimeWeightedCofactor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


open Filter Topology Finset
noncomputable section
namespace RHTower

private theorem nonnegRatio_cpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) :
    ((a / b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z / (b : ℂ) ^ z := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha (inv_nonneg.mpr hb)]
  simp only [Complex.ofReal_inv, Complex.inv_cpow (b : ℂ) z
    (by simpa only [Complex.arg_ofReal_of_nonneg hb] using Real.pi_pos.ne), div_eq_mul_inv]

private theorem tendsto_floor_normalized {P : ℕ → ℂ} {z L : ℂ}
    (h : Tendsto (fun N : ℕ => P N * (N : ℂ) ^ (-z)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => P ⌊x⌋₊ * (x : ℂ) ^ (-z)) atTop (𝓝 L) := by
  have hratio : Tendsto (fun x : ℝ => (((⌊x⌋₊ : ℝ) / x : ℝ) : ℂ) ^ z) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Complex.ofReal_one, Complex.one_cpow] using
      (Complex.continuousAt_ofReal_cpow_const 1 z (Or.inr one_ne_zero)).tendsto.comp
        tendsto_nat_floor_div_atTop
  have hprod := (h.comp tendsto_nat_floor_atTop).mul hratio
  simp only [mul_one] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hfloor : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hfC : (⌊x⌋₊ : ℂ) ≠ 0 := by exact_mod_cast hfloor.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hx).ne'
  dsimp only [Function.comp_apply]
  rw [nonnegRatio_cpow (Nat.cast_nonneg _) (zero_le_one.trans hx), Complex.ofReal_natCast,
    Complex.cpow_neg, Complex.cpow_neg]
  have hfPow : (⌊x⌋₊ : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hfC)
  have hxPow : (x : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hxC)
  field_simp [hfPow, hxPow]

/-- The actual coherent weighted cofactor mean persists at every real cutoff. -/
theorem tendsto_finitePrimeTwistExtension_weighted_mean_realScale
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Icc 1 ⌊x⌋₊, SteinhausModel.X n (finitePrimeTwistExtension S ω t) *
        (n : ℂ) ^ (s - 1)) * (x : ℂ) ^ (-(s + (t : ℂ) * Complex.I))) atTop
      (𝓝 (finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)) /
        (s + (t : ℂ) * Complex.I))) :=
  tendsto_floor_normalized
    (P := fun N : ℕ => ∑ n ∈ Icc 1 N,
      SteinhausModel.X n (finitePrimeTwistExtension S ω t) * (n : ℂ) ^ (s - 1))
    (z := s + (t : ℂ) * Complex.I)
    (L := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)) /
      (s + (t : ℂ) * Complex.I))
    (tendsto_finitePrimeTwistExtension_weighted_mean S ω t (s := s) hs hs1)

/-- One power majorant bounds every real cutoff of the literal coherent weighted prefix. -/
theorem exists_norm_finitePrimeTwistExtension_weighted_prefix_real_le
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, SteinhausModel.X n (finitePrimeTwistExtension S ω t) *
        (n : ℂ) ^ (s - 1)‖ ≤ C * x ^ s.re := by
  let P := fun N : ℕ => ∑ n ∈ Icc 1 N,
    SteinhausModel.X n (finitePrimeTwistExtension S ω t) * (n : ℂ) ^ (s - 1)
  have hlim := tendsto_finitePrimeTwistExtension_weighted_mean S ω t (s := s) hs hs1
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
  have hbound (N : ℕ) : ‖P N‖ ≤ (|C| + 1) * (N : ℝ) ^ s.re := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [P, Real.zero_rpow hs.ne']
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := hC _ ⟨N, rfl⟩
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
      Real.rpow_neg hNR.le, ← div_eq_mul_inv] at hb
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hNR s.re)).mp hb
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C])
      (Real.rpow_nonneg hNR.le _))
  refine ⟨|C| + 1, by positivity, fun x hx => ?_⟩
  exact (hbound ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx) hs.le) (by positivity))

end RHTower
