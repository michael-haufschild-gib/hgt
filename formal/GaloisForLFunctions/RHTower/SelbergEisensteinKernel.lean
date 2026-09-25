import GaloisForLFunctions.RHTower.SelbergPoincareKernel

open Real Complex MeasureTheory Filter
open scoped FourierTransform

/-!
# Fourth-order Fourier decay of the Eisenstein kernel `(y/(x²+y²))^s`

For `β = 0` the Poincaré kernel is `ker_{0,y,s} = exp(s log(y/(x²+y²)))`. Its derivatives are `h_k · ker` with
`h₁ = sL'`, `h_{k+1} = h_k' + h_k h₁` (`hasDerivAt_k1`–`hasDerivAt_k3`), where `|L^{(k)}| ≤ c_k y^{-k}`
(`abs_L3_le`, `abs_L4_le`), so `|h_k| ≤ C_k ((1+|s|)/y)^k` (`nh1`–`nh4`). Four applications of
`𝓕(f') = 2πiξ 𝓕 f` give `(2πξ)⁴ |𝓕 ker_{0,y,s}(ξ)| ≤ 109 ((1+|s|)/y)⁴ y^{1-σ} C_σ` (`norm_fourier_ker0_le_four`),
the decay needed to sum the Eisenstein series' Fourier expansion against the Ramanujan-sum bound `|S_N(0,n;c)| ≤ N|n|`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinKernel
open GaloisForLFunctions.RHTower.SelbergPoincareKernel

variable {y : ℝ} {s : ℂ}

/-- `L''' = -4x(x² - 3y²)/(x²+y²)³`. -/
noncomputable def L3 (y x : ℝ) : ℝ := -(4 * x * (x ^ 2 - 3 * y ^ 2)) / (x ^ 2 + y ^ 2) ^ 3

/-- `L'''' = 12(x⁴ - 6x²y² + y⁴)/(x²+y²)⁴`. -/
noncomputable def L4 (y x : ℝ) : ℝ := 12 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4) / (x ^ 2 + y ^ 2) ^ 4

theorem hasDerivAt_L2 (hy : 0 < y) (x : ℝ) : HasDerivAt (L2 y) (L3 y x) x := by
  have hq : HasDerivAt (fun t : ℝ => (t ^ 2 + y ^ 2) ^ 2) (2 * (x ^ 2 + y ^ 2) * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).pow 2
    exact this.congr_deriv (by push_cast; ring)
  have hne : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by positivity
  have hn : HasDerivAt (fun t : ℝ => 2 * (t ^ 2 - y ^ 2)) (2 * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).sub_const (y ^ 2)).const_mul 2
    exact this.congr_deriv (by push_cast; ring)
  exact (hn.div hq hne).congr_deriv (by unfold L3; field_simp; ring)

theorem hasDerivAt_L3 (hy : 0 < y) (x : ℝ) : HasDerivAt (L3 y) (L4 y x) x := by
  have hq : HasDerivAt (fun t : ℝ => (t ^ 2 + y ^ 2) ^ 3) (3 * (x ^ 2 + y ^ 2) ^ 2 * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).pow 3
    exact this.congr_deriv (by push_cast; ring)
  have hne : (x ^ 2 + y ^ 2) ^ 3 ≠ 0 := by positivity
  have hn : HasDerivAt (fun t : ℝ => -(4 * t * (t ^ 2 - 3 * y ^ 2))) (-(4 * (3 * x ^ 2 - 3 * y ^ 2))) x := by
    have h1 : HasDerivAt (fun t : ℝ => 4 * t * (t ^ 2 - 3 * y ^ 2))
        (4 * 1 * (x ^ 2 - 3 * y ^ 2) + 4 * x * (2 * x)) x := by
      have := ((hasDerivAt_id' x).const_mul 4).mul ((hasDerivAt_pow 2 x).sub_const (3 * y ^ 2))
      exact this.congr_deriv (by push_cast; ring)
    exact h1.neg.congr_deriv (by ring)
  exact (hn.div hq hne).congr_deriv (by unfold L4; field_simp; ring)

theorem abs_L3_le (hy : 0 < y) (x : ℝ) : |L3 y x| ≤ 12 / y ^ 3 := by
  unfold L3
  have hp : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : 0 < (x ^ 2 + y ^ 2) ^ 3), div_le_div_iff₀ (by positivity) (by positivity),
    abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 : |x| * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (|x| - y), sq_abs x]
  have h2 : |x ^ 2 - 3 * y ^ 2| ≤ 3 * (x ^ 2 + y ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have h3 : y ^ 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x]
  have hx := abs_nonneg x
  calc 4 * |x| * |x ^ 2 - 3 * y ^ 2| * y ^ 3 = 4 * (|x| * y) * y ^ 2 * |x ^ 2 - 3 * y ^ 2| := by ring
    _ ≤ 4 * (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) * (3 * (x ^ 2 + y ^ 2)) := by gcongr
    _ = 12 * (x ^ 2 + y ^ 2) ^ 3 := by ring

theorem abs_L4_le (hy : 0 < y) (x : ℝ) : |L4 y x| ≤ 36 / y ^ 4 := by
  unfold L4
  have hp : 0 < x ^ 2 + y ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : 0 < (x ^ 2 + y ^ 2) ^ 4), div_le_div_iff₀ (by positivity) (by positivity),
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  have h2 : |x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4| ≤ 3 * (x ^ 2 + y ^ 2) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have h3 : y ^ 4 ≤ (x ^ 2 + y ^ 2) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  calc 12 * |x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4| * y ^ 4 ≤ 12 * (3 * (x ^ 2 + y ^ 2) ^ 2) * (x ^ 2 + y ^ 2) ^ 2 := by
        gcongr
    _ = 36 * (x ^ 2 + y ^ 2) ^ 4 := by ring

/-- Multiplying by the `β = 0` kernel: `(h k)' = (h' + h·sL') k`. -/
theorem hasDerivAt_mul_ker (hy : 0 < y) {h : ℝ → ℂ} {h' : ℂ} {x : ℝ} (hh : HasDerivAt h h' x) :
    HasDerivAt (fun t => h t * ker 0 y s t) ((h' + h x * (s * (L1 y x : ℂ))) * ker 0 y s x) x := by
  have hk := hasDerivAt_ker (β := 0) (s := s) hy x
  refine (hh.mul hk).congr_deriv ?_
  simp only [g1]; push_cast; ring

/-- The polynomial coefficients `h₁, …, h₄` with `ker^{(k)} = h_k ker`. -/
noncomputable def h1 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L1 y x : ℂ)
noncomputable def h2 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L2 y x : ℂ) + h1 y s x * h1 y s x
noncomputable def h2' (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := s * (L3 y x : ℂ) + 2 * (s * (L2 y x : ℂ)) * h1 y s x
noncomputable def h3 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := h2' y s x + h2 y s x * h1 y s x
noncomputable def h3' (y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  s * (L4 y x : ℂ) + 2 * (s * (L3 y x : ℂ) * h1 y s x + s * (L2 y x : ℂ) * (s * (L2 y x : ℂ))) +
    (h2' y s x * h1 y s x + h2 y s x * (s * (L2 y x : ℂ)))
noncomputable def h4 (y : ℝ) (s : ℂ) (x : ℝ) : ℂ := h3' y s x + h3 y s x * h1 y s x

theorem hasDerivAt_h1 (hy : 0 < y) (x : ℝ) : HasDerivAt (h1 y s) (s * (L2 y x : ℂ)) x :=
  ((hasDerivAt_L1 hy x).ofReal_comp).const_mul s

theorem hasDerivAt_h2 (hy : 0 < y) (x : ℝ) : HasDerivAt (h2 y s) (h2' y s x) x := by
  have := (((hasDerivAt_L2 hy x).ofReal_comp).const_mul s).add ((hasDerivAt_h1 (s := s) hy x).mul (hasDerivAt_h1 (s := s) hy x))
  exact this.congr_deriv (by simp only [h2']; ring)

theorem hasDerivAt_h3 (hy : 0 < y) (x : ℝ) : HasDerivAt (h3 y s) (h3' y s x) x := by
  have hL3 := ((hasDerivAt_L3 hy x).ofReal_comp).const_mul s
  have hL2 := ((hasDerivAt_L2 hy x).ofReal_comp).const_mul s
  have h2d : HasDerivAt (h2' y s) (s * (L4 y x : ℂ) + 2 * (s * (L3 y x : ℂ) * h1 y s x + s * (L2 y x : ℂ) * (s * (L2 y x : ℂ)))) x := by
    have := hL3.add ((hL2.const_mul 2).mul (hasDerivAt_h1 (s := s) hy x))
    exact this.congr_deriv (by ring)
  have := h2d.add ((hasDerivAt_h2 (s := s) hy x).mul (hasDerivAt_h1 (s := s) hy x))
  exact this.congr_deriv (by simp only [h3'])

theorem deriv_ker0 (hy : 0 < y) : deriv (ker 0 y s) = fun x => h1 y s x * ker 0 y s x := by
  funext x
  have := hasDerivAt_ker (β := 0) (s := s) hy x
  rw [this.deriv]; simp only [g1, h1]; push_cast; ring

theorem hasDerivAt_k1 (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => h1 y s t * ker 0 y s t) (h2 y s x * ker 0 y s x) x :=
  (hasDerivAt_mul_ker hy (hasDerivAt_h1 hy x)).congr_deriv (by simp only [h2, h1])

theorem hasDerivAt_k2 (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => h2 y s t * ker 0 y s t) (h3 y s x * ker 0 y s x) x :=
  (hasDerivAt_mul_ker hy (hasDerivAt_h2 hy x)).congr_deriv (by simp only [h3, h1])

theorem hasDerivAt_k3 (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => h3 y s t * ker 0 y s t) (h4 y s x * ker 0 y s x) x :=
  (hasDerivAt_mul_ker hy (hasDerivAt_h3 hy x)).congr_deriv (by simp only [h4, h1])

/-- The scale `v = (1 + |s|)/y`. -/
noncomputable def vv (y : ℝ) (s : ℂ) : ℝ := (1 + ‖s‖) / y

theorem norm_mul_L_le (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) {Lk : ℝ} {ck : ℝ} (hL : |Lk| ≤ ck / y ^ k) :
    ‖s * (Lk : ℂ)‖ ≤ ck * vv y s ^ k := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have ha : ‖s‖ ≤ (1 + ‖s‖) ^ k := by
    have h1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    calc ‖s‖ ≤ 1 + ‖s‖ := by linarith
      _ = (1 + ‖s‖) ^ 1 := (pow_one _).symm
      _ ≤ (1 + ‖s‖) ^ k := pow_le_pow_right₀ h1 hk
  have hck : 0 ≤ ck := by
    by_contra h; push Not at h
    have : ck / y ^ k < 0 := div_neg_of_neg_of_pos h (by positivity)
    linarith [abs_nonneg Lk]
  calc ‖s‖ * |Lk| ≤ (1 + ‖s‖) ^ k * (ck / y ^ k) := mul_le_mul ha hL (abs_nonneg _) (by positivity)
    _ = ck * vv y s ^ k := by unfold vv; rw [div_pow]; ring

theorem vv_nonneg (hy : 0 < y) : 0 ≤ vv y s := by unfold vv; positivity

theorem nh1 (hy : 0 < y) (x : ℝ) : ‖h1 y s x‖ ≤ vv y s := by
  have := norm_mul_L_le (s := s) hy le_rfl (show |L1 y x| ≤ 1 / y ^ 1 by rw [pow_one]; exact abs_L1_le hy x)
  simpa [h1] using this

theorem nL2 (hy : 0 < y) (x : ℝ) : ‖s * (L2 y x : ℂ)‖ ≤ 2 * vv y s ^ 2 := norm_mul_L_le hy (by norm_num) (abs_L2_le hy x)
theorem nL3 (hy : 0 < y) (x : ℝ) : ‖s * (L3 y x : ℂ)‖ ≤ 12 * vv y s ^ 3 := norm_mul_L_le hy (by norm_num) (abs_L3_le hy x)
theorem nL4 (hy : 0 < y) (x : ℝ) : ‖s * (L4 y x : ℂ)‖ ≤ 36 * vv y s ^ 4 := norm_mul_L_le hy (by norm_num) (abs_L4_le hy x)

theorem nprod {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B :=
  (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))

theorem nsum {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a + b‖ ≤ A + B :=
  (norm_add_le _ _).trans (add_le_add ha hb)

theorem nh2 (hy : 0 < y) (x : ℝ) : ‖h2 y s x‖ ≤ 3 * vv y s ^ 2 := by
  have a := nh1 (s := s) hy x
  refine (nsum (nL2 hy x) (nprod a a)).trans (le_of_eq ?_); ring

theorem nh2' (hy : 0 < y) (x : ℝ) : ‖h2' y s x‖ ≤ 16 * vv y s ^ 3 := by
  have a := nh1 (s := s) hy x
  have two : ‖(2 : ℂ)‖ ≤ 2 := by simp
  refine (nsum (nL3 hy x) (nprod (nprod two (nL2 hy x)) a)).trans (le_of_eq ?_); ring

theorem nh3 (hy : 0 < y) (x : ℝ) : ‖h3 y s x‖ ≤ 19 * vv y s ^ 3 := by
  refine (nsum (nh2' hy x) (nprod (nh2 hy x) (nh1 hy x))).trans (le_of_eq ?_); ring

theorem nh3' (hy : 0 < y) (x : ℝ) : ‖h3' y s x‖ ≤ 90 * vv y s ^ 4 := by
  have a := nh1 (s := s) hy x
  have two : ‖(2 : ℂ)‖ ≤ 2 := by simp
  refine (nsum (nsum (nL4 hy x) (nprod two (nsum (nprod (nL3 hy x) a) (nprod (nL2 hy x) (nL2 hy x)))))
    (nsum (nprod (nh2' hy x) a) (nprod (nh2 hy x) (nL2 hy x)))).trans (le_of_eq ?_)
  ring

theorem nh4 (hy : 0 < y) (x : ℝ) : ‖h4 y s x‖ ≤ 109 * vv y s ^ 4 := by
  refine (nsum (nh3' hy x) (nprod (nh3 hy x) (nh1 hy x))).trans (le_of_eq ?_); ring

theorem integrable_hk (hy : 0 < y) (hs : 1 / 2 < s.re) {h : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C)
    (hc : Continuous (fun x => h x * ker 0 y s x)) : Integrable (fun x => h x * ker 0 y s x) := by
  refine ((integrable_wt_rpow hy hs).const_mul C).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC x) (norm_ker_le le_rfl hy s x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

theorem continuous_L4 (hy : 0 < y) : Continuous (L4 y) := by
  unfold L4
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)

theorem continuous_h4 (hy : 0 < y) : Continuous (h4 y s) := by
  have c1 : Continuous (h1 y s) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_h1 hy x).continuousAt
  have c2 : Continuous (h2 y s) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_h2 hy x).continuousAt
  have c3 : Continuous (h3 y s) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_h3 hy x).continuousAt
  have cL2 : Continuous (L2 y) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_L2 hy x).continuousAt
  have cL3 : Continuous (L3 y) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_L3 hy x).continuousAt
  have cL1 : Continuous (L1 y) := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_L1 hy x).continuousAt
  have c2' : Continuous (h2' y s) := by
    unfold h2'; exact (continuous_const.mul (Complex.continuous_ofReal.comp cL3)).add
      ((continuous_const.mul (continuous_const.mul (Complex.continuous_ofReal.comp cL2))).mul c1)
  have c3' : Continuous (h3' y s) := by
    unfold h3'
    have hL4 := Complex.continuous_ofReal.comp (continuous_L4 hy)
    have hL3 := Complex.continuous_ofReal.comp cL3
    have hL2 := Complex.continuous_ofReal.comp cL2
    fun_prop
  unfold h4; exact c3'.add (c3.mul c1)

/-- **Fourth-order Fourier decay of the Eisenstein kernel**:
`(2πξ)⁴ |𝓕 ker_{0,y,s}(ξ)| ≤ 109 ((1+|s|)/y)⁴ y^{1-σ} C_σ`. -/
theorem norm_fourier_ker0_le_four (hy : 0 < y) (hs : 1 / 2 < s.re) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ 4 * ‖𝓕 (ker 0 y s) ξ‖ ≤ 109 * vv y s ^ 4 * (y ^ (1 - s.re) * cst s.re) := by
  have v := vv_nonneg (s := s) hy
  set f0 := ker 0 y s
  have hd0 : ∀ x, HasDerivAt f0 (h1 y s x * f0 x) x := fun x => by
    have := hasDerivAt_ker (β := 0) (s := s) hy x
    exact this.congr_deriv (by simp only [g1, h1]; push_cast; ring)
  have D0 : deriv f0 = fun x => h1 y s x * f0 x := funext fun x => (hd0 x).deriv
  have D1 : deriv (fun x => h1 y s x * f0 x) = fun x => h2 y s x * f0 x := funext fun x => (hasDerivAt_k1 hy x).deriv
  have D2 : deriv (fun x => h2 y s x * f0 x) = fun x => h3 y s x * f0 x := funext fun x => (hasDerivAt_k2 hy x).deriv
  have D3 : deriv (fun x => h3 y s x * f0 x) = fun x => h4 y s x * f0 x := funext fun x => (hasDerivAt_k3 hy x).deriv
  have i0 : Integrable f0 := integrable_ker le_rfl hy hs
  have i1 : Integrable (fun x => h1 y s x * f0 x) :=
    integrable_hk hy hs (fun x => nh1 hy x) (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_k1 hy x).continuousAt)
  have i2 : Integrable (fun x => h2 y s x * f0 x) :=
    integrable_hk hy hs (fun x => nh2 hy x) (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_k2 hy x).continuousAt)
  have i3 : Integrable (fun x => h3 y s x * f0 x) :=
    integrable_hk hy hs (fun x => nh3 hy x) (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_k3 hy x).continuousAt)
  have i4 : Integrable (fun x => h4 y s x * f0 x) :=
    integrable_hk hy hs (fun x => nh4 hy x) ((continuous_h4 hy).mul (continuous_ker hy))
  have F1 := Real.fourier_deriv i0 (fun x => (hd0 x).differentiableAt) (by rw [D0]; exact i1)
  have F2 := Real.fourier_deriv i1 (fun x => (hasDerivAt_k1 hy x).differentiableAt) (by rw [D1]; exact i2)
  have F3 := Real.fourier_deriv i2 (fun x => (hasDerivAt_k2 hy x).differentiableAt) (by rw [D2]; exact i3)
  have F4 := Real.fourier_deriv i3 (fun x => (hasDerivAt_k3 hy x).differentiableAt) (by rw [D3]; exact i4)
  rw [D0] at F1; rw [D1] at F2; rw [D2] at F3; rw [D3] at F4
  have h : 𝓕 (fun x => h4 y s x * f0 x) ξ = (2 * Real.pi * Complex.I * ξ) ^ 4 * 𝓕 f0 ξ := by
    rw [F4, F3, F2, F1]; simp only [smul_eq_mul]; ring
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * ξ) ^ 4‖ = (2 * Real.pi * |ξ|) ^ 4 := by
    rw [norm_pow]; simp [abs_of_pos Real.pi_pos]
  rw [← hn, ← norm_mul, ← h]
  refine (norm_fourier_le_integral ξ).trans ?_
  rw [← integral_wt_rpow hy, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_wt_rpow hy hs).const_mul _) (Eventually.of_forall fun x => ?_)
  show ‖h4 y s x * f0 x‖ ≤ 109 * vv y s ^ 4 * wt y x ^ s.re
  rw [norm_mul]
  exact mul_le_mul (nh4 hy x) (norm_ker_le le_rfl hy s x) (norm_nonneg _) (by positivity)

end GaloisForLFunctions.RHTower.SelbergEisensteinKernel
