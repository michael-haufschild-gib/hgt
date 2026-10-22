import GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationMean
import GaloisForLFunctions.RHTower.OddHarmonicExpConvergence
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The sawtooth is the sum of its sine series

The identity `∑_{n ≥ 1} sin(nθ)/n = (π - θ)/2` on `(0, 2π)` is the one input the endpoint-oscillation
estimates take from Fourier theory, and it is not available in mathlib: the series is only
conditionally convergent, so it cannot be phrased as a `HasSum`.  It is proved here as convergence of
partial sums, by the same route as the corpus's odd-harmonic series — Dirichlet's test for the
convergence, the logarithm's power series inside the disc, and Abel's limit theorem to reach the
boundary.

* `expCoeff`, `norm_sum_exp_le`, `exists_tendsto_sum_expCoeff` — the harmonic exponential
  coefficients, the geometric bound on the exponential partial sums, and convergence off the lattice.
* `tsum_expCoeff_mul_pow` — inside the disc the generating function is `-log(1 - x e^{iθ})`.
* `tendsto_sum_expCoeff` — the boundary value: the harmonic exponential series sums to
  `-log(1 - e^{iθ})`.
* `arg_one_sub_exp_mul_I`, `im_neg_log_one_sub_exp` — the boundary value's imaginary part.
* `tendsto_sum_sawtoothSine` — the sawtooth Fourier series: on `(0, 2π)` the sine series converges to
  `sawWave θ`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset Filter Topology

/-! ## The harmonic exponential coefficients -/

/-- The harmonic exponential coefficients `e^{inθ}/n`.  At `n = 0` the value is `0`, matching the
indexing of mathlib's logarithm series. -/
def expCoeff (θ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) / (n : ℂ)

theorem expCoeff_zero (θ : ℝ) : expCoeff θ 0 = 0 := by
  rw [expCoeff]
  simp

theorem exp_natCast_mul (θ : ℝ) (n : ℕ) :
    Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)
      = (Complex.exp ((θ : ℂ) * Complex.I)) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Geometric bound on the exponential partial sums.**  Off the lattice the rotated geometric sums
are bounded by the reciprocal chord length. -/
theorem norm_sum_exp_le {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) (N : ℕ) :
    ‖∑ k ∈ range N, Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I)‖
      ≤ 2 / ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have hw1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hgeom := _root_.RHTower.norm_geom_sum_le hw1 hθ N
  have hrw : (∑ k ∈ range N, Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I))
      = Complex.exp ((θ : ℂ) * Complex.I) * ∑ k ∈ range N,
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : ((((k : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + (k : ℂ) * ((θ : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hc, Complex.exp_add, ← Complex.exp_nat_mul]
  rw [hrw, norm_mul, hw1, one_mul]
  exact hgeom

theorem antitone_oneDivSucc : Antitone (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  intro a b hab
  have hle : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have hc : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    linarith
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hle

theorem tendsto_oneDivSucc : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Dirichlet's test.**  Off the lattice the harmonic exponential series converges. -/
theorem exists_tendsto_sum_expCoeff {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ range N, expCoeff θ n) atTop (𝓝 L) := by
  have hcauchyShift : CauchySeq fun N => ∑ k ∈ range N,
      (1 / ((k : ℝ) + 1)) • Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I) :=
    antitone_oneDivSucc.cauchySeq_series_mul_of_tendsto_zero_of_bounded tendsto_oneDivSucc
      (b := 2 / ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖) fun n => norm_sum_exp_le hθ n
  have hterm : ∀ k : ℕ,
      (1 / ((k : ℝ) + 1)) • Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I)
        = expCoeff θ (k + 1) := by
    intro k
    have hc1 : (((k + 1 : ℕ) : ℝ) * θ : ℝ) = (((k : ℝ) + 1) * θ : ℝ) := by push_cast; ring
    rw [expCoeff, hc1, Complex.real_smul]
    push_cast
    ring
  have hshift : ∀ N : ℕ, (∑ k ∈ range N,
      (1 / ((k : ℝ) + 1)) • Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I))
      = ∑ n ∈ range (N + 1), expCoeff θ n := by
    intro N
    rw [Finset.sum_range_succ' (expCoeff θ) N, expCoeff_zero, add_zero]
    exact Finset.sum_congr rfl fun k _ => hterm k
  have hfun : (fun N => ∑ k ∈ range N,
      (1 / ((k : ℝ) + 1)) • Complex.exp (((((k : ℝ) + 1) * θ : ℝ)) * Complex.I))
      = fun N => ∑ n ∈ range (N + 1), expCoeff θ n := funext hshift
  rw [hfun] at hcauchyShift
  have hcauchy : CauchySeq fun N => ∑ n ∈ range N, expCoeff θ n := by
    rw [← cauchySeq_shift 1]
    exact hcauchyShift
  exact cauchySeq_tendsto_of_complete hcauchy

/-! ## The generating function inside the disc -/

theorem tsum_expCoeff_mul_pow {θ x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, expCoeff θ n * (x : ℂ) ^ n)
      = -Complex.log (1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hnorm : ‖(x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hseries := Complex.hasSum_taylorSeries_neg_log hnorm
  have hcongr : ∀ n : ℕ, expCoeff θ n * (x : ℂ) ^ n
      = ((x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ n / (n : ℂ) := by
    intro n
    rw [expCoeff, exp_natCast_mul, mul_pow]
    ring
  rw [(hseries.congr_fun hcongr).tsum_eq]

/-! ## The boundary value -/

theorem re_one_sub_exp_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    0 < (1 - Complex.exp ((θ : ℂ) * Complex.I)).re := by
  have hexp : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcos : Real.cos θ < 1 := by
    rcases eq_or_lt_of_le (Real.cos_le_one θ) with h | h
    · exfalso
      have hsin : Real.sin θ = 0 := by
        have := Real.sin_sq_add_cos_sq θ
        nlinarith
      have hhalf : Real.sin (θ / 2) ≠ 0 := by
        refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]) |>.ne'
      have hcos2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ (2 : ℕ) := by
        have hc := Real.cos_two_mul' (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at hc
        nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
      have : Real.sin (θ / 2) ^ (2 : ℕ) = 0 := by nlinarith
      exact hhalf (pow_eq_zero_iff (by norm_num) |>.mp this)
    · exact h
  simp
  linarith

/-- The boundary chord `1 - e^{iθ}` in polar form. -/
theorem one_sub_exp_mul_I_eq {θ : ℝ} :
    1 - Complex.exp ((θ : ℂ) * Complex.I)
      = ((2 * Real.sin (θ / 2) : ℝ) : ℂ)
        * Complex.exp ((((θ - Real.pi) / 2 : ℝ)) * Complex.I) := by
  have hL : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hR : Complex.exp ((((θ - Real.pi) / 2 : ℝ)) * Complex.I)
      = (Real.cos ((θ - Real.pi) / 2) : ℂ)
        + (Real.sin ((θ - Real.pi) / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : Real.cos ((θ - Real.pi) / 2) = Real.sin (θ / 2) := by
    have : (θ - Real.pi) / 2 = θ / 2 - Real.pi / 2 := by ring
    rw [this, Real.cos_sub_pi_div_two]
  have hs : Real.sin ((θ - Real.pi) / 2) = -Real.cos (θ / 2) := by
    have : (θ - Real.pi) / 2 = θ / 2 - Real.pi / 2 := by ring
    rw [this, Real.sin_sub_pi_div_two]
  have hcosθ : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ (2 : ℕ) := by
    have hc2 := Real.cos_two_mul' (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hc2
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hsinθ : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have hs2 := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hs2
    exact hs2
  rw [hL, hR, hc, hs]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    nlinarith [hcosθ, hsinθ]

theorem arg_one_sub_exp_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    Complex.arg (1 - Complex.exp ((θ : ℂ) * Complex.I)) = (θ - Real.pi) / 2 := by
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hpos : (0 : ℝ) < 2 * Real.sin (θ / 2) := by linarith
  rw [one_sub_exp_mul_I_eq, Complex.arg_real_mul _ hpos]
  have hmem : (θ - Real.pi) / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · have := Real.pi_pos
      linarith [hθ.1]
    · have := Real.pi_pos
      linarith [hθ.2]
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hmem

theorem im_neg_log_one_sub_exp {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    (-Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))).im = (Real.pi - θ) / 2 := by
  rw [Complex.neg_im, Complex.log_im, arg_one_sub_exp_mul_I hθ]
  ring

/-! ## The sawtooth series -/

/-- **The harmonic exponential series at the boundary.** -/
theorem tendsto_sum_expCoeff {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    Tendsto (fun N => ∑ n ∈ range N, expCoeff θ n) atTop
      (𝓝 (-Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I)))) := by
  have hre := re_one_sub_exp_pos_of_mem_Ioo hθ
  have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  obtain ⟨L, hL⟩ := exists_tendsto_sum_expCoeff hne
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (f := expCoeff θ) (l := L) hL
  rw [Filter.tendsto_map'_iff] at habel
  have hinner : Tendsto (fun x : ℝ => 1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 - Complex.exp ((θ : ℂ) * Complex.I))) := by
    have h1 : Continuous fun x : ℝ => 1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      fun_prop
    have hval : (1 : ℂ) - (((1 : ℝ)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        = 1 - Complex.exp ((θ : ℂ) * Complex.I) := by
      push_cast
      ring
    have h3 : Tendsto (fun x : ℝ => 1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℂ) - (((1 : ℝ)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
      h1.continuousAt.continuousWithinAt
    rw [hval] at h3
    exact h3
  have hcont := (hinner.clog (Or.inl hre)).neg
  have heq : ∀ᶠ x in 𝓝[<] (1 : ℝ),
      ((fun z : ℂ => ∑' n, expCoeff θ n * z ^ n) ∘ (fun r : ℝ => (r : ℂ))) x
        = -Complex.log (1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    have hgt : ∀ᶠ x in 𝓝[<] (1 : ℝ), (-1 : ℝ) < x :=
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hgt] with x hx1 hx2
    have hlt : x < 1 := hx1
    exact tsum_expCoeff_mul_pow (abs_lt.mpr ⟨hx2, hlt⟩)
  have hLeq : L = -Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I)) :=
    tendsto_nhds_unique (habel.congr' heq) hcont
  rw [← hLeq]
  exact hL

/-- **The sawtooth Fourier series.**  On `(0, 2π)` the sine series converges to the sawtooth. -/
theorem tendsto_sum_sawtoothSine {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    Tendsto (fun N => ∑ n ∈ range N, Real.sin ((n : ℝ) * θ) / (n : ℝ)) atTop
      (𝓝 (sawWave θ)) := by
  have hexp := tendsto_sum_expCoeff hθ
  have him := (Complex.continuous_im.tendsto _).comp hexp
  rw [im_neg_log_one_sub_exp hθ] at him
  have hval : sawWave θ = (Real.pi - θ) / 2 := by
    rw [sawWave_eq_of_mem_Ioo hθ]
  rw [hval]
  refine him.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [Complex.im_sum _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [expCoeff_zero]
    simp
  · have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [expCoeff, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.div_im]
    have hnre : ((n : ℂ)).re = (n : ℝ) := by simp
    have hnim : ((n : ℂ)).im = 0 := by simp
    have hnorm : Complex.normSq (n : ℂ) = (n : ℝ) ^ (2 : ℕ) := by
      rw [Complex.normSq_apply, hnre, hnim]
      ring
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, hnre, hnim, hnorm]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
    ring

/-! ## The uniform bound, and the periodic extension -/

/-- **Equation (7).**  The sawtooth sine series converges and its sum is bounded by `π/2`,
uniformly. -/
theorem exists_sum_sawtoothSine_abs_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ∃ S : ℝ, Tendsto (fun N => ∑ n ∈ range N, Real.sin ((n : ℝ) * θ) / (n : ℝ)) atTop (𝓝 S)
      ∧ |S| ≤ Real.pi / 2 :=
  ⟨sawWave θ, tendsto_sum_sawtoothSine hθ, abs_sawWave_le θ⟩

/-- Reduction of an arbitrary angle to one period. -/
theorem exists_mem_Ioo_sub_int_mul_two_pi {θ : ℝ} (hθ : ∀ k : ℤ, θ ≠ (k : ℝ) * (2 * Real.pi)) :
    ∃ (k : ℤ) (θ' : ℝ), θ' ∈ Set.Ioo 0 (2 * Real.pi) ∧ θ = θ' + (k : ℝ) * (2 * Real.pi) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊θ / (2 * Real.pi)⌋ with hk
  refine ⟨k, θ - (k : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, by ring⟩
  · rcases lt_trichotomy (θ - (k : ℝ) * (2 * Real.pi)) 0 with h | h | h
    · exfalso
      have hlt : θ / (2 * Real.pi) < (k : ℝ) := by
        rw [div_lt_iff₀ hpi]
        linarith
      exact absurd (Int.floor_le (θ / (2 * Real.pi))) (not_le.mpr (by rw [← hk]; exact hlt))
    · exact absurd (by linarith : θ = (k : ℝ) * (2 * Real.pi)) (hθ k)
    · exact h
  · have hlt : θ / (2 * Real.pi) < (k : ℝ) + 1 := by
      rw [hk]
      exact Int.lt_floor_add_one _
    rw [div_lt_iff₀ hpi] at hlt
    linarith

theorem sawtoothSine_periodic (θ : ℝ) (k : ℤ) (n : ℕ) :
    Real.sin ((n : ℝ) * (θ + (k : ℝ) * (2 * Real.pi))) = Real.sin ((n : ℝ) * θ) := by
  have hexp : (n : ℝ) * (θ + (k : ℝ) * (2 * Real.pi))
      = (n : ℝ) * θ + ((n * k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hexp, Real.sin_add_int_mul_two_pi]

/-- **Equation (7), for every angle off the lattice.**  The bound is uniform in the angle. -/
theorem exists_sum_sawtoothSine_abs_le_of_ne {θ : ℝ}
    (hθ : ∀ k : ℤ, θ ≠ (k : ℝ) * (2 * Real.pi)) :
    ∃ S : ℝ, Tendsto (fun N => ∑ n ∈ range N, Real.sin ((n : ℝ) * θ) / (n : ℝ)) atTop (𝓝 S)
      ∧ |S| ≤ Real.pi / 2 := by
  obtain ⟨k, θ', hθ', hsum⟩ := exists_mem_Ioo_sub_int_mul_two_pi hθ
  obtain ⟨S, hS, hbound⟩ := exists_sum_sawtoothSine_abs_le hθ'
  refine ⟨S, ?_, hbound⟩
  refine hS.congr fun N => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hsum, sawtoothSine_periodic θ' k n]

end GaloisForLFunctions.RHTower

end
