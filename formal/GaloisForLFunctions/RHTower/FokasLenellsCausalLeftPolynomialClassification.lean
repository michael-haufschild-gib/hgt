import GaloisForLFunctions.RHTower.FokasLenellsCausalLeftHigherRoots
import GaloisForLFunctions.Bottcher.PolyAsymptotic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Exact polynomial and exponential-polynomial boundedness on the left half-plane.
The existing Böttcher leading-term limit detects every ray. The actual left-half-plane
root construction rules out all degrees above one, leaving precisely causal affine slopes. -/
open Complex Polynomial Set Filter Topology
open scoped NNReal
namespace RHTower.FokasLenells
noncomputable section

private theorem scaled_ray_limit (p : ℂ[X]) (v : ℂ) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ p.natDegree * p.eval (v * (t : ℂ)))
      atTop (𝓝 (p.leadingCoeff * v ^ p.natDegree)) := by
  let q : ℂ[X] := p.comp (C v * X)
  have hqdeg : q.natDegree = p.natDegree := by
    simp only [q, Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X v hv, mul_one]
  have hqlead : q.leadingCoeff = p.leadingCoeff * v ^ p.natDegree := by
    exact (Polynomial.leadingCoeff_comp (by
      rw [Polynomial.natDegree_C_mul_X v hv]
      exact one_ne_zero)).trans (by rw [Polynomial.leadingCoeff_C_mul_X])
  have ht : Tendsto (fun t : ℝ => (t : ℂ) / (t : ℂ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))).symm
  have h := Bottcher.univariate_scaled_eval_tendsto_leadingCoeff_of_tendsto_div q ht
  simpa only [hqdeg, hqlead, q, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using h

private theorem leading_re_nonpos_strict (p : ℂ[X]) (B : ℝ)
    (hB : ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B)
    (hd : 0 < p.natDegree) (v : ℂ) (hv : v.re < 0) :
    (p.leadingCoeff * v ^ p.natDegree).re ≤ 0 := by
  have hvne : v ≠ 0 := by
    intro h
    simpa only [h, Complex.zero_re, lt_self_iff_false] using hv
  have hcomplex := scaled_ray_limit p v hvne
  have hreal : Tendsto (fun t : ℝ =>
      t⁻¹ ^ p.natDegree * (p.eval (v * (t : ℂ))).re)
      atTop (𝓝 (p.leadingCoeff * v ^ p.natDegree).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hcomplex
    convert h using 1
    funext t
    simp only [Function.comp_apply, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hinv : Tendsto (fun t : ℝ => t⁻¹ ^ p.natDegree * B) atTop (𝓝 0) := by
    simpa only [zero_pow (ne_of_gt hd), zero_mul] using
      (tendsto_inv_atTop_zero.pow p.natDegree).mul_const B
  apply le_of_tendsto_of_tendsto hreal hinv
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr ht.le) _)
  apply hB
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    mul_neg_of_neg_of_pos hv ht

private theorem leading_re_nonpos_closed (p : ℂ[X]) (B : ℝ)
    (hB : ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B)
    (hd : 0 < p.natDegree) (v : ℂ) (hv : v.re ≤ 0) :
    (p.leadingCoeff * v ^ p.natDegree).re ≤ 0 := by
  have hi : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
  have hlim : Tendsto (fun t : ℝ => v - ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 v) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  have hc : Continuous (fun z : ℂ => (p.leadingCoeff * z ^ p.natDegree).re) :=
    Complex.continuous_re.comp (continuous_const.mul (continuous_id.pow _))
  apply le_of_tendsto ((hc.tendsto v).comp hlim)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  apply leading_re_nonpos_strict p B hB hd
  simp only [Complex.sub_re, Complex.ofReal_re]
  exact sub_neg.mpr (lt_of_le_of_lt hv (inv_pos.mpr ht))

private theorem bounded_re_degree_le_one (p : ℂ[X]) (B : ℝ)
    (hB : ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B) : p.natDegree ≤ 1 := by
  by_contra hn
  have hd : 2 ≤ p.natDegree := by omega
  have hp : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have ha : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  let n := p.natDegree - 2
  have hnd : n + 2 = p.natDegree := by omega
  let v := causalLeftPowerRoot n p.leadingCoeff⁻¹
  have hv : v.re ≤ 0 := causalLeftPowerRoot_re_nonpos n p.leadingCoeff⁻¹
  have hpow : v ^ p.natDegree = p.leadingCoeff⁻¹ := by
    rw [← hnd]
    exact causalLeftPowerRoot_pow n p.leadingCoeff⁻¹
  have he : (p.leadingCoeff * v ^ p.natDegree).re = 1 := by
    rw [hpow, mul_inv_cancel₀ ha, Complex.one_re]
  have hle := leading_re_nonpos_closed p B hB (by omega) v hv
  linarith

private theorem bounded_re_linear_slope (p : ℂ[X]) (B : ℝ)
    (hB : ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B) (hd : p.natDegree = 1) :
    0 ≤ p.leadingCoeff.re ∧ p.leadingCoeff.im = 0 := by
  have ha : 0 ≤ p.leadingCoeff.re := by
    have h := leading_re_nonpos_closed p B hB (by omega) (-1) (by norm_num)
    simpa only [hd, pow_one, mul_neg, mul_one, Complex.neg_re, neg_nonpos] using h
  refine ⟨ha, ?_⟩
  by_contra hn
  let r : ℝ := (p.leadingCoeff.re + 1) / p.leadingCoeff.im
  let v : ℂ := -1 - (r : ℂ) * I
  have hv : v.re < 0 := by simp [v]
  have h := leading_re_nonpos_strict p B hB (by omega) v hv
  have he : (p.leadingCoeff * v ^ p.natDegree).re = 1 := by
    simp only [hd, pow_one, v, Complex.mul_re, Complex.sub_re, Complex.neg_re,
      Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_im, Complex.neg_im, Complex.one_im, Complex.mul_im]
    dsimp [r]
    field_simp [hn]
    <;> ring
  linarith

/-- A polynomial has bounded real part on the left half-plane exactly when its
slope is real and nonnegative and every higher coefficient vanishes. -/
theorem causalLeftPolynomial_re_bounded_iff (p : ℂ[X]) :
    (∃ B : ℝ, ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B) ↔
      ∃ a : ℝ≥0, ∃ b : ℂ, p = C ((a : ℝ) : ℂ) * X + C b := by
  constructor
  · rintro ⟨B, hB⟩
    have hd := bounded_re_degree_le_one p B hB
    by_cases hzero : p.natDegree = 0
    · refine ⟨0, p.coeff 0, ?_⟩
      simpa using Polynomial.eq_C_of_natDegree_eq_zero hzero
    · have hone : p.natDegree = 1 := by omega
      obtain ⟨ha, hi⟩ := bounded_re_linear_slope p B hB hone
      refine ⟨⟨p.leadingCoeff.re, ha⟩, p.coeff 0, ?_⟩
      have hc : p.coeff 1 = p.leadingCoeff := by
        simpa only [hone] using Polynomial.coeff_natDegree (p := p)
      have he : p.leadingCoeff = (p.leadingCoeff.re : ℂ) := by
        apply Complex.ext
        · rfl
        · exact hi
      exact (Polynomial.eq_X_add_C_of_natDegree_le_one hd).trans
        (congrArg (fun z : ℂ => C z * X + C (p.coeff 0)) (hc.trans he))
  · rintro ⟨a, b, rfl⟩
    refine ⟨b.re, fun z hz => ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact add_le_of_nonpos_left (mul_nonpos_of_nonneg_of_nonpos a.property hz.le)

/-- A complex polynomial bounded in norm on the left half-plane is exactly a constant. -/
theorem causalLeftPolynomial_norm_bounded_iff (p : ℂ[X]) :
    (∃ B : ℝ, ∀ z : ℂ, z.re < 0 → ‖p.eval z‖ ≤ B) ↔
      ∃ b : ℂ, p = C b := by
  constructor
  · rintro ⟨B, hB⟩
    have hp : ∃ B : ℝ, ∀ z : ℂ, z.re < 0 → (p.eval z).re ≤ B :=
      ⟨B, fun z hz => (Complex.re_le_norm _).trans (hB z hz)⟩
    have hn : ∃ B : ℝ, ∀ z : ℂ, z.re < 0 → ((-p).eval z).re ≤ B := by
      refine ⟨B, fun z hz => ?_⟩
      exact (Complex.re_le_norm _).trans (by simpa only [Polynomial.eval_neg, norm_neg] using hB z hz)
    obtain ⟨a, b, he⟩ := (causalLeftPolynomial_re_bounded_iff p).mp hp
    obtain ⟨c, d, hf⟩ := (causalLeftPolynomial_re_bounded_iff (-p)).mp hn
    have hsum : (-(a : ℝ)) = (c : ℝ) := by
      have h := congrArg (fun q : ℂ[X] => (q.coeff 1).re) hf
      simpa [he] using h
    have ha : (a : ℝ) = 0 := by
      apply le_antisymm
      · have hc0 : (0 : ℝ) ≤ -(a : ℝ) := hsum.symm ▸ c.property
        linarith only [hc0]
      · exact a.property
    refine ⟨b, ?_⟩
    simpa only [ha, Complex.ofReal_zero, Polynomial.C_0, zero_mul, zero_add] using he
  · rintro ⟨b, rfl⟩
    exact ⟨‖b‖, fun z _ => by simp⟩

/-- The exponential of a polynomial is bounded on the left half-plane exactly
for a nonnegative real affine slope; this is the scalar causal flow classification. -/
theorem causalLeftPolynomial_exp_bounded_iff (p : ℂ[X]) :
    (∃ B : ℝ, ∀ z : ℂ, z.re < 0 → ‖Complex.exp (p.eval z)‖ ≤ B) ↔
      ∃ a : ℝ≥0, ∃ b : ℂ, p = C ((a : ℝ) : ℂ) * X + C b := by
  rw [← causalLeftPolynomial_re_bounded_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun z hz => ?_⟩
    have h := hB z hz
    rw [Complex.norm_exp] at h
    have he := Real.add_one_le_exp (p.eval z).re
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨Real.exp B, fun z hz => ?_⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hB z hz)

end
end RHTower.FokasLenells
