import GaloisForLFunctions.RHTower.HalfWeightModalWhittaker
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.HalfWeightThetaMultiplier

/-!
# The zeroth Fourier coefficient of `U(4z) \overline{θ(z)}`

* `coefficient_periodic`: for a `1`-periodic slice, the width-`M` Fourier coefficient of index `n` is
  the width-`1` coefficient of index `n/M` when `M ∣ n`, and `0` otherwise (the window `[0,M]` splits into
  `M` unit windows, weighted by the powers of the root of unity `e^{-2πin/M}`).
* `conj_theta_hasSum`: `\overline{θ(x+iy)} = Σ_m e^{-2πm²y} e^{-2πim²x}`.
* `integral_eq_coefficient_four`: `∫_0^1 U(4x+4iy) e^{-2πim²x} dx` is the width-`4` coefficient of index
  `m²` at height `4y`.
* **`hasSum_integral_U_conj_theta'`**: for bounded continuous `1`-periodic `U`,
  `∫_0^1 U(4z) \overline{θ(z)} dx = Σ_{j ∈ ℤ} e^{-8πj²y} c_{j²}(4y)` with `c_k` the width-`1` coefficients
  (only even `m = 2j` survive, `4 ∣ m² ↔ 2 ∣ m`).

This is the Dirichlet-series side of Shimura's integral: only the square-index coefficients of `U`
enter.
-/

open Real Complex Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.RHTower.HalfWeight

open SelbergMaassFourier SelbergMaassMean

noncomputable section

/-! ### Fourier coefficients of a `1`-periodic function over a longer window -/

theorem kernel_add_one (M : ℕ) (n : ℤ) (x : ℝ) :
    _root_.RHTower.deningerFourierKernel M n (x + 1) =
      cexp (-(2 * π * I * n) / M) * _root_.RHTower.deningerFourierKernel M n x := by
  unfold _root_.RHTower.deningerFourierKernel
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- For a `1`-periodic slice, the width-`M` coefficient of index `n` vanishes unless `M ∣ n`, and equals the
width-`1` coefficient of index `n/M` when it does. -/
theorem coefficient_periodic (M : ℕ) (hM : 0 < M) (n : ℤ) {F : ℂ → ℂ} {y : ℝ}
    (hc : Continuous fun x : ℝ => F (point x y)) (hper : ∀ x : ℝ, F (point (x + 1) y) = F (point x y)) :
    coefficient M n F y = if (M : ℤ) ∣ n then coefficient 1 (n / M) F y else 0 := by
  set g : ℝ → ℂ := fun x => _root_.RHTower.deningerFourierKernel M n x * F (point x y)
  set ζ : ℂ := cexp (-(2 * π * I * n) / M)
  have hgc : Continuous g := by
    refine Continuous.mul ?_ hc
    unfold _root_.RHTower.deningerFourierKernel; fun_prop
  have hshift : ∀ x : ℝ, g (x + 1) = ζ * g x := by
    intro x; simp only [g]; rw [kernel_add_one, hper]; ring
  have hshiftj : ∀ (j : ℕ) (x : ℝ), g (x + j) = ζ ^ j * g x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [show x + ((j + 1 : ℕ) : ℝ) = (x + j) + 1 by push_cast; ring, hshift, ih, pow_succ]; ring
  have hsplit : (∫ x in (0 : ℝ)..(M : ℝ), g x) = (∑ j ∈ Finset.range M, ζ ^ j) * ∫ x in (0 : ℝ)..1, g x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun j : ℕ => (j : ℝ)) (n := M) (fun k _ => hgc.intervalIntegrable _ _)
    simp only [Nat.cast_zero] at h
    rw [← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e := intervalIntegral.integral_comp_add_right g (a := 0) (b := 1) (j : ℝ)
    simp only [zero_add] at e
    rw [show ((j + 1 : ℕ) : ℝ) = 1 + j by push_cast; ring, ← e]
    simp_rw [hshiftj j]
    rw [intervalIntegral.integral_const_mul]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold coefficient _root_.RHTower.deningerFourierCoeff
  by_cases hd : (M : ℤ) ∣ n
  · rw [if_pos hd]
    obtain ⟨k, rfl⟩ := hd
    have hζ : ζ = 1 := by
      simp only [ζ]; rw [Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; field_simp⟩
    rw [hsplit, hζ]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hM.ne')]
    have hk : ∀ x : ℝ, _root_.RHTower.deningerFourierKernel M (M * k) x =
        _root_.RHTower.deningerFourierKernel ((1 : ℕ) : ℝ) k x := by
      intro x
      unfold _root_.RHTower.deningerFourierKernel
      congr 1; push_cast; field_simp
    simp only [g, hk]
    push_cast
    field_simp
  · rw [if_neg hd, hsplit]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      simp only [ζ] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      apply hd
      refine ⟨-m, ?_⟩
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : (n : ℂ) = (M : ℂ) * (-m : ℤ) := by
        field_simp at hm
        push_cast
        linear_combination -hm
      exact_mod_cast this
    have hζM : ζ ^ M = 1 := by
      simp only [ζ]; rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨-n, by push_cast; field_simp⟩
    rw [geom_sum_eq hζ1, hζM, sub_self, zero_div, zero_mul, mul_zero]


/-! ### The zeroth Fourier coefficient of `U(4z) \overline{θ(z)}` -/

theorem conj_theta_hasSum {x y : ℝ} (hy : 0 < y) :
    HasSum (fun m : ℤ => ((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
      cexp (-(2 * π * I * (m : ℂ) ^ 2 * x))) (starRingEnd ℂ (theta (point x y))) := by
  have hz : 0 < (point x y).im := by simpa [point] using hy
  have h := (summable_theta_terms hz).hasSum
  rw [← theta_eq_tsum] at h
  have hc := Complex.hasSum_conj'.2 h
  refine hc.congr_fun fun m => ?_
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [point, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_pow, map_intCast,
    map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- Substitution `x' = 4x`: `∫_0^1 U(4x + 4iy) e^{-2πi m² x} dx` is the width-`4` coefficient of index `m²`. -/
theorem integral_eq_coefficient_four (U : ℂ → ℂ) (y : ℝ) (m : ℤ) :
    ∫ x in (0 : ℝ)..1, U (point (4 * x) (4 * y)) * cexp (-(2 * π * I * (m : ℂ) ^ 2 * x)) =
      coefficient 4 (m ^ 2) U (4 * y) := by
  set h : ℝ → ℂ := fun x' => _root_.RHTower.deningerFourierKernel 4 (m ^ 2) x' * U (point x' (4 * y))
  have e : ∀ x : ℝ, U (point (4 * x) (4 * y)) * cexp (-(2 * π * I * (m : ℂ) ^ 2 * x)) = h (4 * x) := by
    intro x
    simp only [h, _root_.RHTower.deningerFourierKernel]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left h (by norm_num : (4 : ℝ) ≠ 0)]
  unfold coefficient _root_.RHTower.deningerFourierCoeff
  simp only [mul_zero, mul_one, Complex.real_smul]
  push_cast
  ring

/-- **The zeroth coefficient**: for bounded continuous `1`-periodic `U`,
`∫_0^1 U(4z) \overline{θ(z)} dx = Σ_{m} e^{-2πm²y} c₄(m²; 4y)`. -/
theorem hasSum_integral_U_conj_theta {U : ℂ → ℂ} {y : ℝ} (hy : 0 < y) {B : ℝ}
    (hB : ∀ x : ℝ, ‖U (point x (4 * y))‖ ≤ B) (hc : Continuous fun x : ℝ => U (point x (4 * y))) :
    HasSum (fun m : ℤ => ((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 4 (m ^ 2) U (4 * y))
      (∫ x in (0 : ℝ)..1, U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point x y))) := by
  set F : ℤ → ℝ → ℂ := fun m x => U (point (4 * x) (4 * y)) *
    (((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * cexp (-(2 * π * I * (m : ℂ) ^ 2 * x)))
  have hc4 : Continuous fun x : ℝ => U (point (4 * x) (4 * y)) := hc.comp (continuous_const.mul continuous_id)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsumE : Summable fun m : ℤ => B * Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) := by
    have hz : 0 < (point 0 y).im := by simpa [point] using hy
    have := (summable_theta_terms hz).norm.mul_left B
    refine this.congr fun m => ?_
    rw [Complex.norm_exp]
    congr 2
    rw [show ((m : ℂ) ^ 2) = (((m : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    simp only [point, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := 1)
    (F := F) (f := fun x => U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point x y)))
    (fun m x => B * Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)))
    (fun m => (hc4.mul (by fun_prop)).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun x _ => by
      simp only [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have : (-(2 * π * I * (m : ℂ) ^ 2 * (x : ℂ))).re = 0 := by
        have him : ((m : ℂ) ^ 2).im = 0 := by rw [← Int.cast_pow, Complex.intCast_im]
        have hre : ((m : ℂ) ^ 2).re = (m : ℝ) ^ 2 := by
          rw [← Int.cast_pow, Complex.intCast_re]; push_cast; ring
        simp [Complex.mul_re, Complex.mul_im, him, hre]
      rw [this, Real.exp_zero, mul_one]
      exact mul_le_mul_of_nonneg_right (hB (4 * x)) (Real.exp_pos _).le)
    (Eventually.of_forall fun x _ => hsumE)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => (conj_theta_hasSum hy).mul_left _)
  refine hmain.congr_fun fun m => ?_
  simp only [F]
  rw [← integral_eq_coefficient_four, ← intervalIntegral.integral_const_mul]
  congr 1; funext x; ring

theorem four_dvd_sq_iff (m : ℤ) : (4 : ℤ) ∣ m ^ 2 ↔ 2 ∣ m := by
  constructor
  · intro h
    have h2 : (2 : ℤ) ∣ m ^ 2 := (by norm_num : (2 : ℤ) ∣ 4).trans h
    exact Int.Prime.dvd_pow' Nat.prime_two h2
  · rintro ⟨j, rfl⟩; exact ⟨j ^ 2, by ring⟩

/-- **The zeroth coefficient in terms of width-`1` coefficients**: for bounded continuous `1`-periodic `U`,
`∫_0^1 U(4z) \overline{θ(z)} dx = Σ_{j ∈ ℤ} e^{-8πj²y} c₁(j²; 4y)`. -/
theorem hasSum_integral_U_conj_theta' {U : ℂ → ℂ} {y : ℝ} (hy : 0 < y) {B : ℝ}
    (hB : ∀ x : ℝ, ‖U (point x (4 * y))‖ ≤ B) (hc : Continuous fun x : ℝ => U (point x (4 * y)))
    (hper : ∀ x : ℝ, U (point (x + 1) (4 * y)) = U (point x (4 * y))) :
    HasSum (fun j : ℤ => ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 1 (j ^ 2) U (4 * y))
      (∫ x in (0 : ℝ)..1, U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point x y))) := by
  have h := hasSum_integral_U_conj_theta hy hB hc
  set f : ℤ → ℂ := fun m => ((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 4 (m ^ 2) U (4 * y)
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun a b hab => by simpa using hab
  have h4 : ∀ n : ℤ, coefficient 4 n U (4 * y) = if (4 : ℤ) ∣ n then coefficient 1 (n / 4) U (4 * y) else 0 := by
    intro n
    have := coefficient_periodic 4 (by norm_num) n hc hper
    simpa using this
  have hzero : ∀ m ∉ Set.range (fun j : ℤ => 2 * j), f m = 0 := by
    intro m hm
    have hnd : ¬ (4 : ℤ) ∣ m ^ 2 := by
      rw [four_dvd_sq_iff]; rintro ⟨j, rfl⟩; exact hm ⟨j, rfl⟩
    simp only [f]
    rw [h4, if_neg hnd, mul_zero]
  rw [← hinj.hasSum_iff hzero] at h
  refine h.congr_fun fun j => ?_
  simp only [Function.comp, f]
  have hd : (4 : ℤ) ∣ (2 * j) ^ 2 := ⟨j ^ 2, by ring⟩
  rw [h4, if_pos hd]
  rw [show (2 * j) ^ 2 / 4 = j ^ 2 by rw [show (2 * j) ^ 2 = 4 * j ^ 2 by ring]; exact Int.mul_ediv_cancel_left _ (by norm_num)]
  congr 3
  push_cast
  ring
