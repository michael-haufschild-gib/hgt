import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelMass
import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing
import GaloisForLFunctions.HTGeometry.IntervalIntegralHolderSwap

/-!
# Poisson windows of the band-limited critical weight

The critical kernel weight `u⁻²(1 - cos(2πu/12))` is the restriction to `u > 0` of the even
band-limited weight `γ(u) = (π²/72) sinc²(πu/12)`, whose spectrum is the triangle on
`|ξ| ≤ π/6`. Poisson summation gives `Σ_{z∈ℤ} γ(t+z) = π²/6` at every point, so every one-sided
harmonic tail is fixed by a finite window of `2m` translates. The triangle representation
turns the window's deviation from its unit-cell mean into a spectral integral against
`sin(ξm)·(cos(ξ(t-½))/sin(ξ/2) - 2/ξ)`, bounded uniformly in `m` and `t`.
-/

open MeasureTheory Set Filter Asymptotics
open GaloisForLFunctions.HTGeometry.BandLimitedPositiveDensity

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The Fourier transform of `sinc²(πu/12)` is the triangle `12·max(0, 1 - |12w|)`. -/
theorem fourier_sincSq_div_twelve (w : ℝ) :
    FourierTransform.fourier (fun u : ℝ => ((sincSq (u / 12) : ℝ) : ℂ)) w =
      12 * (triangle (12 * w) : ℂ) := by
  rw [Real.fourier_real_eq]
  let h : ℝ → ℂ := fun y => Complex.exp (((2 * Real.pi * y * (-(12 * w)) : ℝ) : ℂ) * Complex.I) *
    (sincSq y : ℂ)
  have hfun : (fun v : ℝ => Real.fourierChar (-(v * w)) • ((sincSq (v / 12) : ℝ) : ℂ)) =
      fun v => h ((1 / 12 : ℝ) * v) := by
    funext v
    simp only [h, Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
    congr 2
    · push_cast; ring_nf
    · ring_nf
  rw [hfun, Measure.integral_comp_mul_left, integral_cexp_mul_sincSq]
  have ht : triangle (-(12 * w)) = triangle (12 * w) := by simp [triangle, abs_neg]
  rw [ht]
  norm_num

/-- Poisson summation: the integer translates of `sinc²(πu/12)` sum to `12` everywhere, because
the triangle spectrum vanishes at every nonzero integer. -/
theorem tsum_sincSq_div_twelve (x : ℝ) : ∑' n : ℤ, sincSq ((x + n) / 12) = 12 := by
  let f : ℝ → ℂ := fun u => ((sincSq (u / 12) : ℝ) : ℂ)
  have hc : Continuous f := by
    have := continuous_sincSq; fun_prop
  have hf : f =O[cocompact ℝ] fun u => |u| ^ (-(2 : ℝ)) := by
    refine IsBigO.of_bound 32 ?_
    filter_upwards [GaloisForLFunctions.HTGeometry.eventually_abs_ge_cocompact 1] with u hu
    have hu0 : 0 < |u| := by linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sincSq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by positivity), Real.rpow_neg hu0.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have h1 := sincSq_le (u / 12)
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hu2 : 0 < u ^ 2 := by rw [← sq_abs]; positivity
    have hden : u ^ 2 / 16 ≤ (Real.pi * (u / 12)) ^ 2 := by
      have : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      nlinarith
    have hinv : (1 + (Real.pi * (u / 12)) ^ 2)⁻¹ ≤ 16 / u ^ 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hu2]; nlinarith
    calc sincSq (u / 12) ≤ 2 * (1 + (Real.pi * (u / 12)) ^ 2)⁻¹ := h1
      _ ≤ 2 * (16 / u ^ 2) := by gcongr
      _ = 32 * (u ^ 2)⁻¹ := by ring
  have hF : FourierTransform.fourier f =O[cocompact ℝ] fun u => |u| ^ (-(2 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [GaloisForLFunctions.HTGeometry.eventually_abs_ge_cocompact 1] with u hu
    have h0 : triangle (12 * u) = 0 := triangle_eq_zero (by rw [abs_mul]; norm_num; linarith)
    rw [fourier_sincSq_div_twelve, h0]
    simp only [Complex.ofReal_zero, mul_zero, norm_zero, one_mul]
    positivity
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc (by norm_num : (1 : ℝ) < 2) hf hF x
  have hR : ∑' n : ℤ, FourierTransform.fourier f n * (fourier n) (x : UnitAddCircle) = 12 := by
    rw [tsum_eq_single 0]
    · rw [fourier_sincSq_div_twelve]; simp [triangle_zero]
    · intro n hn
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      have h0 : triangle (12 * (n : ℝ)) = 0 := triangle_eq_zero (by rw [abs_mul]; norm_num; linarith)
      rw [fourier_sincSq_div_twelve, h0]; simp
  rw [hR] at hP
  have hcast : ((∑' n : ℤ, sincSq ((x + n) / 12) : ℝ) : ℂ) = 12 := by
    rw [Complex.ofReal_tsum]; exact hP
  exact_mod_cast hcast

/-- The even band-limited critical weight `γ(u) = (π²/72) sinc²(πu/12)`; for `u > 0` it is
`u⁻²(1 - cos(2πu/12))`, and `γ(0) = π²/72`. -/
def criticalBandWeight (u : ℝ) : ℝ := (Real.pi ^ 2 / 72) * sincSq (u / 12)

theorem criticalBandWeight_nonneg (u : ℝ) : 0 ≤ criticalBandWeight u :=
  mul_nonneg (by positivity) (sincSq_nonneg _)

theorem continuous_criticalBandWeight : Continuous criticalBandWeight := by
  unfold criticalBandWeight; have := continuous_sincSq; fun_prop

/-- The band-limited weight is even. -/
theorem criticalBandWeight_neg (u : ℝ) : criticalBandWeight (-u) = criticalBandWeight u := by
  simp only [criticalBandWeight, sincSq, neg_div, mul_neg, Real.sinc_neg]

/-- On the positive half-line the critical kernel weight is the band-limited weight. -/
theorem factorialCriticalPrimeKernelWeight_eq_band {u : ℝ} (hu : 0 < u) :
    factorialCriticalPrimeKernelWeight u = criticalBandWeight u := by
  rw [factorialCriticalPrimeKernelWeight_eq_sincSq hu, criticalBandWeight]; congr 2; ring

/-- **Poisson identity.** The integer translates of `γ` carry total mass `π²/6` at every point. -/
theorem tsum_criticalBandWeight (x : ℝ) :
    ∑' n : ℤ, criticalBandWeight (x + n) = Real.pi ^ 2 / 6 := by
  simp only [criticalBandWeight]; rw [tsum_mul_left, tsum_sincSq_div_twelve]; ring

/-- A nonnegative series with nonzero sum: the integer translates of `γ` are summable. -/
theorem summable_criticalBandWeight (x : ℝ) :
    Summable fun n : ℤ => criticalBandWeight (x + n) := by
  by_contra h
  have h0 := tsum_eq_zero_of_not_summable h
  rw [tsum_criticalBandWeight] at h0
  have := Real.pi_pos
  nlinarith

/-- Triangle representation `γ(u) = ∫₀^{π/6} (π/6 - ξ) cos(ξu) dξ`. -/
theorem criticalBandWeight_eq_integral (u : ℝ) :
    criticalBandWeight u =
      ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * Real.cos (ξ * u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
        (fun ξ : ℝ => Real.pi / 6 * ξ - ξ ^ 2 / 2) (Real.pi / 6 - ξ) ξ := by
      intro ξ _
      have := ((hasDerivAt_id ξ).const_mul (Real.pi / 6)).sub ((hasDerivAt_pow 2 ξ).div_const 2)
      exact this.congr_deriv (by simp)
    simp only [mul_zero, Real.cos_zero, mul_one]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [criticalBandWeight, sincSq]
    ring
  · have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
        (fun ξ : ℝ => (Real.pi / 6 - ξ) * Real.sin (ξ * u) / u - Real.cos (ξ * u) / u ^ 2)
        ((Real.pi / 6 - ξ) * Real.cos (ξ * u)) ξ := by
      intro ξ _
      have h1 : HasDerivAt (fun ξ : ℝ => ξ * u) u ξ := by
        simpa using (hasDerivAt_id ξ).mul_const u
      have hs := (Real.hasDerivAt_sin (ξ * u)).comp ξ h1
      have hc := (Real.hasDerivAt_cos (ξ * u)).comp ξ h1
      have hl : HasDerivAt (fun ξ : ℝ => Real.pi / 6 - ξ) (-1) ξ := by
        simpa using (hasDerivAt_id ξ).const_sub (Real.pi / 6)
      have := ((hl.mul hs).div_const u).sub (hc.div_const (u ^ 2))
      exact this.congr_deriv (by simp only [Function.comp_apply]; field_simp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have hθ : Real.pi * (u / 12) ≠ 0 := mul_ne_zero Real.pi_ne_zero (div_ne_zero hu (by norm_num))
    have hcos : Real.cos (Real.pi / 6 * u) = 1 - 2 * Real.sin (Real.pi * (u / 12)) ^ 2 := by
      rw [show Real.pi / 6 * u = 2 * (Real.pi * (u / 12)) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    simp only [criticalBandWeight, sincSq, Real.sinc_of_ne_zero hθ, sub_self, zero_mul,
      zero_div, Real.sin_zero, Real.cos_zero, mul_zero, sub_zero]
    rw [hcos]
    field_simp
    ring

/-- The finite Poisson window `W_m(t) = Σ_{n<m} (γ(t+n) + γ(t-n-1))`: the `2m` translates
`t + z` with `-m ≤ z ≤ m-1`. -/
def criticalBandWindow (m : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, (criticalBandWeight (t + n) + criticalBandWeight (t - n - 1))

/-- Forward integer translates are summable. -/
theorem summable_criticalBandWeight_nat (t : ℝ) :
    Summable fun n : ℕ => criticalBandWeight (t + (n : ℝ)) := by
  have := (summable_criticalBandWeight t).comp_injective Nat.cast_injective
  simpa [Function.comp_def] using this

/-- Backward integer translates are summable. -/
theorem summable_criticalBandWeight_nat_neg (t : ℝ) :
    Summable fun n : ℕ => criticalBandWeight (t - n - 1) := by
  have hi : Function.Injective (fun n : ℕ => (-((n : ℤ) + 1) : ℤ)) := by
    intro a b h; simpa using h
  refine ((summable_criticalBandWeight t).comp_injective hi).congr fun n => ?_
  simp only [Function.comp_apply]
  congr 1; push_cast; ring

/-- The translates outside the window carry exactly `π²/6 - W_m(t)`. -/
theorem tsum_criticalBandWeight_outside_window (m : ℕ) (t : ℝ) :
    ∑' k : ℕ, (criticalBandWeight (t + ((k + m : ℕ) : ℝ)) +
      criticalBandWeight (t - ((k + m : ℕ) : ℝ) - 1)) =
      Real.pi ^ 2 / 6 - criticalBandWindow m t := by
  have hpos := summable_criticalBandWeight_nat t
  have hneg := summable_criticalBandWeight_nat_neg t
  have hZ := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => criticalBandWeight (t + n))
    (by simpa using hpos) (by
      refine hneg.congr fun n => ?_
      congr 1; push_cast; ring)
  rw [tsum_criticalBandWeight] at hZ
  have e1 : (∑' n : ℕ, (fun n : ℤ => criticalBandWeight (t + n)) (n : ℤ)) =
      ∑' n : ℕ, criticalBandWeight (t + (n : ℝ)) := by simp
  have e2 : (∑' n : ℕ, (fun n : ℤ => criticalBandWeight (t + n)) (-((n : ℤ) + 1))) =
      ∑' n : ℕ, criticalBandWeight (t - n - 1) := by
    congr 1; funext n; simp only; congr 1; push_cast; ring
  rw [e1, e2, ← hpos.sum_add_tsum_nat_add m, ← hneg.sum_add_tsum_nat_add m] at hZ
  rw [Summable.tsum_add ((summable_nat_add_iff m).mpr hpos) ((summable_nat_add_iff m).mpr hneg)]
  unfold criticalBandWindow
  rw [Finset.sum_add_distrib]
  push_cast at hZ ⊢
  linarith

/-- Dirichlet telescoping of the window cosines:
`sin(ξ/2) Σ_{n<m} (cos ξ(t+n) + cos ξ(t-n-1)) = cos(ξ(t-½)) sin(ξm)`. -/
theorem sin_half_mul_bandWindowCos (ξ t : ℝ) (m : ℕ) :
    Real.sin (ξ / 2) * ∑ n ∈ Finset.range m,
      (Real.cos (ξ * (t + n)) + Real.cos (ξ * (t - n - 1))) =
      Real.cos (ξ * (t - 1 / 2)) * Real.sin (ξ * m) := by
  have key (A B P : ℝ) : Real.cos A * Real.sin (P - B) +
      Real.sin B * (Real.cos (A + P) + Real.cos (A - P)) = Real.cos A * Real.sin (P + B) := by
    simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]; ring
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := key (ξ * (t - 1 / 2)) (ξ / 2) (ξ / 2 + ξ * m)
    push_cast
    convert h using 3 <;> ring_nf

/-- `x·sinc(ξx) = sin(ξx)/ξ` for `ξ ≠ 0`. -/
theorem natCast_mul_sinc_eq {ξ : ℝ} (hξ : ξ ≠ 0) (x : ℝ) :
    x * Real.sinc (ξ * x) = Real.sin (ξ * x) / ξ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hξ hx)]; field_simp

/-- `∫₀^x cos(ξu) du = x·sinc(ξx)`, including `ξ = 0`. -/
theorem integral_cos_mul_eq_sinc (ξ x : ℝ) :
    ∫ u in (0 : ℝ)..x, Real.cos (ξ * u) = x * Real.sinc (ξ * x) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hξ, integral_cos,
      natCast_mul_sinc_eq hξ]
    simp [div_eq_inv_mul]

/-- Fubini in the triangle representation: `∫₀^x γ = ∫₀^{π/6} (π/6 - ξ)·x·sinc(ξx) dξ`. -/
theorem integral_criticalBandWeight_eq (x : ℝ) (hx : 0 ≤ x) :
    ∫ u in (0 : ℝ)..x, criticalBandWeight u =
      ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * (x * Real.sinc (ξ * x)) := by
  simp_rw [criticalBandWeight_eq_integral]
  rw [GaloisForLFunctions.HTGeometry.intervalIntegral_integral_swap_of_continuous
    (F := fun u ξ => (Real.pi / 6 - ξ) * Real.cos (ξ * u)) (by fun_prop) hx (by positivity)]
  congr 1; funext ξ
  rw [intervalIntegral.integral_const_mul, integral_cos_mul_eq_sinc]

/-- Curvature of the symmetric window: `|cos(ξs)/sin(ξ/2) - 2/ξ| ≤ (6/35)ξ` for
`0 < ξ ≤ π/6` and `|s| ≤ ½`, from Taylor bounds for sine and cosine at `ξ/2 ≤ π/12`. -/
theorem abs_cos_div_sin_half_sub_le {ξ s : ℝ} (hξ : 0 < ξ) (hξc : ξ ≤ Real.pi / 6)
    (hs : |s| ≤ 1 / 2) :
    |Real.cos (ξ * s) / Real.sin (ξ / 2) - 2 / ξ| ≤ (6 / 35) * ξ := by
  set x := ξ / 2 with hxdef
  set y := Real.cos (ξ * s) with hydef
  set S := Real.sin x with hSdef
  have hξx : ξ = 2 * x := by rw [hxdef]; ring
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 3 / 10 := by have := Real.pi_lt_d2; linarith
  have hx2 : x ^ 2 ≤ 9 / 100 := by nlinarith
  have hx5 : x ^ 5 ≤ (9 / 100) * x ^ 3 := by
    have := pow_pos hx0 3
    have h5 : x ^ 5 = x ^ 3 * x ^ 2 := by ring
    rw [h5]; nlinarith
  have hx3 : x ^ 3 ≤ (9 / 100) * x := by
    have h3 : x ^ 3 = x * x ^ 2 := by ring
    rw [h3]; nlinarith
  have hlo : x - x ^ 3 / 6 < S := Real.sin_gt_sub_cube hx0
  have hhi : S ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
    have h := Real.sin_bound (x := x) (by rw [abs_of_pos hx0]; linarith)
    rw [abs_of_pos hx0] at h
    linarith [(abs_le.mp h).2]
  have hS : 0 < S := by linarith
  have hcx : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hy1 : y ≤ 1 := Real.cos_le_one _
  have hy0 : Real.cos x ≤ y := by
    rw [hydef, ← Real.cos_abs (ξ * s)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
    rw [abs_mul, abs_of_pos hξ, hξx]
    nlinarith
  have hrw : y / S - 2 / ξ = (x * y - S) / (x * S) := by
    rw [hξx]; field_simp
  have hgoal : (6 / 35) * ξ = (12 / 35) * x := by rw [hξx]; ring
  rw [hrw, hgoal, abs_div, abs_of_pos (mul_pos hx0 hS), div_le_iff₀ (mul_pos hx0 hS), abs_le]
  have a1 : x * Real.cos x ≤ x * y := mul_le_mul_of_nonneg_left hy0 hx0.le
  have a2 : x * (1 - x ^ 2 / 2) ≤ x * Real.cos x := mul_le_mul_of_nonneg_left hcx hx0.le
  have a3 : x ^ 2 * (x - x ^ 3 / 6) ≤ x ^ 2 * S := mul_le_mul_of_nonneg_left hlo.le (sq_nonneg x)
  have a5 : x * y ≤ x := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The cosine kernel of the window at band frequency `ξ`. -/
def criticalBandWindowCos (m : ℕ) (ξ t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, (Real.cos (ξ * (t + n)) + Real.cos (ξ * (t - n - 1)))

/-- The window in the triangle representation. -/
theorem criticalBandWindow_eq_integral (m : ℕ) (t : ℝ) :
    criticalBandWindow m t =
      ∫ ξ in (0 : ℝ)..Real.pi / 6, (Real.pi / 6 - ξ) * criticalBandWindowCos m ξ t := by
  unfold criticalBandWindow criticalBandWindowCos
  simp_rw [criticalBandWeight_eq_integral, Finset.mul_sum, mul_add]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  · intro n _
    apply Continuous.intervalIntegrable; fun_prop

/-- The unit-cell mean of the window is `2∫₀^m γ`: reflection pairs each cell `[n, n+1]`
with its mirror image. -/
theorem integral_criticalBandWindow (m : ℕ) :
    ∫ t in (0 : ℝ)..1, criticalBandWindow m t = 2 * ∫ u in (0 : ℝ)..m, criticalBandWeight u := by
  have hc := continuous_criticalBandWeight
  unfold criticalBandWindow
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  have hcell (n : ℕ) : ∫ t in (0 : ℝ)..1,
      (criticalBandWeight (t + n) + criticalBandWeight (t - n - 1)) =
      2 * ∫ u in (n : ℝ)..(n + 1 : ℕ), criticalBandWeight u := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have hr : ∀ t : ℝ, criticalBandWeight (t - n - 1) = criticalBandWeight ((n + 1 : ℝ) - t) := by
      intro t; rw [← criticalBandWeight_neg]; ring_nf
    simp_rw [hr]
    rw [intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_sub_left]
    push_cast
    ring_nf
  simp_rw [hcell, ← Finset.mul_sum]
  congr 1
  have := intervalIntegral.sum_integral_adjacent_intervals (f := criticalBandWeight)
    (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := m)
    (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)
  simpa using this

/-- Half of the total band mass: `∫_{u>0} γ = π²/12`. -/
theorem integral_Ioi_criticalBandWeight :
    ∫ u in Ioi (0 : ℝ), criticalBandWeight u = Real.pi ^ 2 / 12 := by
  have hall : ∫ u : ℝ, criticalBandWeight u = Real.pi ^ 2 / 6 := by
    simp only [criticalBandWeight]
    rw [integral_const_mul, show (fun u : ℝ => sincSq (u / 12)) =
      fun u => sincSq ((1 / 12 : ℝ) * u) by funext u; ring_nf,
      Measure.integral_comp_mul_left (fun u => sincSq u), integral_sincSq]
    norm_num; ring
  have habs := integral_comp_abs (f := criticalBandWeight)
  have heven : (fun x : ℝ => criticalBandWeight |x|) = criticalBandWeight := by
    funext x
    rcases abs_choice x with h | h <;> rw [h]
    exact criticalBandWeight_neg x
  rw [heven, hall] at habs
  linarith

theorem integrable_criticalBandWeight : Integrable criticalBandWeight := by
  unfold criticalBandWeight
  refine Integrable.const_mul ?_ _
  have := integrable_sincSq.comp_mul_left' (by norm_num : (1 / 12 : ℝ) ≠ 0)
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  ring_nf

/-- The harmonic defect is the complementary band mass: `J_m = m(π²/12 - ∫₀^m γ)`. -/
theorem factorialCriticalHarmonicDefect_eq_band {m : ℕ} (hm : 0 < m) :
    factorialCriticalHarmonicDefect m =
      (m : ℝ) * (Real.pi ^ 2 / 12 - ∫ u in (0 : ℝ)..m, criticalBandWeight u) := by
  have h1 := factorialCriticalPatternHarmonicMass_eq_common_tail {0} (fun _ => 1) hm
  rw [factorialCriticalPatternHarmonicMass_singleton] at h1
  have hQ (u : ℝ) : factorialCriticalPatternDensity {0} (fun _ => 1) u = 1 := by
    simp [factorialCriticalPatternDensity]
  simp only [hQ, mul_one, one_pow, one_mul] at h1
  rw [h1]
  congr 1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htail : ∫ u in Ioi (m : ℝ), factorialCriticalPrimeKernelWeight u =
      ∫ u in Ioi (m : ℝ), criticalBandWeight u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu =>
      factorialCriticalPrimeKernelWeight_eq_band (lt_trans hmR hu)
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := m))
    measurableSet_Ioi integrable_criticalBandWeight.integrableOn
    integrable_criticalBandWeight.integrableOn
  rw [Ioc_union_Ioi_eq_Ioi hmR.le, integral_Ioi_criticalBandWeight,
    ← intervalIntegral.integral_of_le hmR.le] at hsplit
  rw [htail]
  linarith

/-- Deviation of the window from its unit-cell mean, `W_m(t) - 2∫₀^m γ`. -/
def criticalBandWindowDeviation (m : ℕ) (t : ℝ) : ℝ :=
  criticalBandWindow m t - 2 * ∫ u in (0 : ℝ)..m, criticalBandWeight u

/-- Spectral form of the window deviation. -/
theorem criticalBandWindowDeviation_eq_integral (m : ℕ) (t : ℝ) :
    criticalBandWindowDeviation m t = ∫ ξ in (0 : ℝ)..Real.pi / 6,
      (Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t - 2 * ((m : ℝ) * Real.sinc (ξ * m))) := by
  have hcos : Continuous fun ξ => criticalBandWindowCos m ξ t := by
    unfold criticalBandWindowCos; fun_prop
  unfold criticalBandWindowDeviation
  rw [criticalBandWindow_eq_integral, integral_criticalBandWeight_eq m (Nat.cast_nonneg m),
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; have := Real.continuous_sinc; fun_prop)]
  congr 1; funext ξ; ring

/-- On the band the deviation integrand is `sin(ξm)` times the window curvature. -/
theorem norm_criticalBandWindowDeviation_integrand_le (m : ℕ) {t ξ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hξ : ξ ∈ Ioc (0 : ℝ) (Real.pi / 6)) :
    ‖(Real.pi / 6 - ξ) * (criticalBandWindowCos m ξ t - 2 * ((m : ℝ) * Real.sinc (ξ * m)))‖ ≤
      (6 / 35) * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by
  obtain ⟨hξ0, hξc⟩ := hξ
  have hpi := Real.pi_gt_three
  have hs2 : 0 < Real.sin (ξ / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hD : criticalBandWindowCos m ξ t =
      Real.cos (ξ * (t - 1 / 2)) * Real.sin (ξ * m) / Real.sin (ξ / 2) := by
    rw [eq_div_iff hs2.ne', mul_comm]; exact sin_half_mul_bandWindowCos ξ t m
  have hsinc : (m : ℝ) * Real.sinc (ξ * m) = Real.sin (ξ * m) / ξ := natCast_mul_sinc_eq hξ0.ne' m
  have hfac : criticalBandWindowCos m ξ t - 2 * ((m : ℝ) * Real.sinc (ξ * m)) =
      Real.sin (ξ * m) * (Real.cos (ξ * (t - 1 / 2)) / Real.sin (ξ / 2) - 2 / ξ) := by
    rw [hD, hsinc]; ring
  have hts : |t - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hg := abs_cos_div_sin_half_sub_le hξ0 hξc hts
  have hc0 : 0 ≤ Real.pi / 6 - ξ := by linarith
  rw [hfac, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc0]
  calc (Real.pi / 6 - ξ) * (|Real.sin (ξ * m)| *
        |Real.cos (ξ * (t - 1 / 2)) / Real.sin (ξ / 2) - 2 / ξ|) ≤
      (Real.pi / 6 - ξ) * (|Real.sin (ξ * m)| * ((6 / 35) * ξ)) := by gcongr
    _ = (6 / 35) * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by ring

/-- The window deviation is bounded by its spectral curvature integral. -/
theorem abs_criticalBandWindowDeviation_le (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |criticalBandWindowDeviation m t| ≤
      ∫ ξ in (0 : ℝ)..Real.pi / 6, (6 / 35) * ((Real.pi / 6 - ξ) * ξ * |Real.sin (ξ * m)|) := by
  rw [criticalBandWindowDeviation_eq_integral, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le (by positivity)
  · exact Filter.Eventually.of_forall fun ξ hξ => norm_criticalBandWindowDeviation_integrand_le m ht hξ
  · apply Continuous.intervalIntegrable; fun_prop

private theorem integral_band_moment_one :
    ∫ ξ in (0 : ℝ)..Real.pi / 6, (6 / 35) * ((Real.pi / 6 - ξ) * ξ) = (Real.pi / 6) ^ 3 / 35 := by
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
      (fun ξ : ℝ => (6 / 35) * (Real.pi / 6 * ξ ^ 2 / 2 - ξ ^ 3 / 3))
      ((6 / 35) * ((Real.pi / 6 - ξ) * ξ)) ξ := by
    intro ξ _
    have := (((hasDerivAt_pow 2 ξ).const_mul (Real.pi / 6)).div_const 2).sub
      ((hasDerivAt_pow 3 ξ).div_const 3) |>.const_mul (6 / 35)
    exact this.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

private theorem integral_band_moment_two (m : ℕ) :
    ∫ ξ in (0 : ℝ)..Real.pi / 6, (6 / 35) * ((Real.pi / 6 - ξ) * ξ * (ξ * m)) =
      (m : ℝ) * (Real.pi / 6) ^ 4 / 70 := by
  have hd : ∀ ξ ∈ Set.uIcc (0 : ℝ) (Real.pi / 6), HasDerivAt
      (fun ξ : ℝ => (6 / 35) * (m : ℝ) * (Real.pi / 6 * ξ ^ 3 / 3 - ξ ^ 4 / 4))
      ((6 / 35) * ((Real.pi / 6 - ξ) * ξ * (ξ * m))) ξ := by
    intro ξ _
    have := (((hasDerivAt_pow 3 ξ).const_mul (Real.pi / 6)).div_const 3).sub
      ((hasDerivAt_pow 4 ξ).div_const 4) |>.const_mul ((6 / 35) * (m : ℝ))
    exact this.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- Uniform window bound `|W_m(t) - 2∫₀^m γ| ≤ (π/6)³/35` for every `m` and `t ∈ [0, 1]`. -/
theorem abs_criticalBandWindowDeviation_le_cube (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |criticalBandWindowDeviation m t| ≤ (Real.pi / 6) ^ 3 / 35 := by
  refine (abs_criticalBandWindowDeviation_le m ht).trans ?_
  rw [← integral_band_moment_one]
  apply intervalIntegral.integral_mono_on (by positivity)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro ξ hξ
  have h0 : 0 ≤ (Real.pi / 6 - ξ) * ξ := mul_nonneg (by linarith [hξ.2]) hξ.1
  have := Real.abs_sin_le_one (ξ * m)
  have := mul_le_mul_of_nonneg_left this h0
  nlinarith

/-- Small-window bound `|W_m(t) - 2∫₀^m γ| ≤ m (π/6)⁴/70` for `t ∈ [0, 1]`. -/
theorem abs_criticalBandWindowDeviation_le_quartic (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |criticalBandWindowDeviation m t| ≤ (m : ℝ) * (Real.pi / 6) ^ 4 / 70 := by
  refine (abs_criticalBandWindowDeviation_le m ht).trans ?_
  rw [← integral_band_moment_two]
  apply intervalIntegral.integral_mono_on (by positivity)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro ξ hξ
  have h0 : 0 ≤ (Real.pi / 6 - ξ) * ξ := mul_nonneg (by linarith [hξ.2]) hξ.1
  have hs : |Real.sin (ξ * m)| ≤ ξ * m := by
    have := Real.abs_sin_le_abs (x := ξ * m)
    rwa [abs_of_nonneg (mul_nonneg hξ.1 (Nat.cast_nonneg m))] at this
  have := mul_le_mul_of_nonneg_left hs h0
  nlinarith

/-- The window is nonnegative. -/
theorem criticalBandWindow_nonneg (m : ℕ) (t : ℝ) : 0 ≤ criticalBandWindow m t :=
  Finset.sum_nonneg fun _ _ => add_nonneg (criticalBandWeight_nonneg _) (criticalBandWeight_nonneg _)

end GaloisForLFunctions.ArithmeticPositivityTheory
