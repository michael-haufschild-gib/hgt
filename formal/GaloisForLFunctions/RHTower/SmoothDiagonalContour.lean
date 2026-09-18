import GaloisForLFunctions.RHTower.SmoothDiagonalMellin
import GaloisForLFunctions.RHTower.RectangleTwoPoleResidue
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralHorizontal
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# The smoothed diagonal: contour shift and asymptotic

The diagonal Mellin integrand `F(w) = ζ(2σ₀+2w)(x/c)^w e^{w²}/w` is integrated along `Re w = 1`.
Moving the line to `Re w = −1/4` crosses the kernel pole at `0` (residue `ζ(2σ₀)`) and the zeta
pole at `δ₀ = ½ − σ₀` (residue `(x/c)^{δ₀}e^{δ₀²}/(2δ₀)`); the horizontal edges vanish by the
Gaussian against the polynomial strip growth of `ζ`, and on the left line `|(x/c)^w| = (x/c)^{-1/4}`
while `ζ(2σ₀ − ½ + 2it)` has uniform polynomial growth for `0 ≤ 2σ₀ − ½ ≤ ½`.  Hence

`Σ_j (j+1)^{-2σ₀} V((j+1)²c/x) = ζ(2σ₀) + (x/c)^{δ₀}e^{δ₀²}/(2δ₀) + O((x/c)^{-1/4})`

with an implied constant independent of `σ₀ ∈ [¼, ½)`, `c` and `x`.  The `1/δ₀` in the second
residue is the `1/(1 − 2σ₀)` that cancels against the dual diagonal.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology

/-! ## Zeta bounds -/

/-- Uniform polynomial growth of `ζ` on the closed strip `0 ≤ σ ≤ ¾`, at every height. -/
theorem exists_norm_riemannZeta_le_leftStrip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  -- the compact part
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc (0 : ℝ) (3 / 4) ×ˢ Set.Icc (-2 : ℝ) 2)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn riemannZeta K := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hne : (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hp.1.2]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₀ 0 + 20 * Real.exp 2, by positivity, fun σ t hσ0 hσ1 => ?_⟩
  rcases le_or_gt 2 |t| with ht | ht
  · have h := norm_riemannZeta_le_smoothAFE_strip (σ := σ) (t := t) (by linarith) (by linarith) ht
    refine h.trans ?_
    have h4 : 4 + |t| ≤ 4 * (1 + |t|) := by linarith [abs_nonneg t]
    calc 5 * Real.exp 2 * (1 + |t|) * (4 + |t|) ≤ 5 * Real.exp 2 * (1 + |t|) * (4 * (1 + |t|)) := by
          gcongr
      _ = 20 * Real.exp 2 * (1 + |t|) ^ 2 := by ring
      _ ≤ (max C₀ 0 + 20 * Real.exp 2) * (1 + |t|) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [le_max_right C₀ 0]
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K :=
      ⟨(σ, t), ⟨⟨hσ0, hσ1⟩, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩, rfl⟩
    have h := hC₀ _ hmem
    have h1 : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ max C₀ 0 + 20 * Real.exp 2 := by linarith [le_max_left C₀ 0, Real.exp_pos 2]
      _ = (max C₀ 0 + 20 * Real.exp 2) * 1 := by ring
      _ ≤ (max C₀ 0 + 20 * Real.exp 2) * (1 + |t|) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The trivial bound right of `Re s = 2`. -/
theorem norm_riemannZeta_le_of_two_le_re_tsum {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2 := by
  have hre : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hsum2 : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n + 1 : ℂ) ^ s‖ ≤ 1 / (n + 1 : ℝ) ^ 2 := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [norm_div, norm_one, show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    apply one_div_le_one_div_of_le (by positivity)
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n + 1) hs
    simpa [Real.rpow_two] using this
  have hsn : Summable (fun n : ℕ => ‖(1 : ℂ) / (n + 1 : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum2
  exact (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum hterm hsn hsum2)

/-! ## Pointwise bounds on the integrand -/

theorem norm_smoothAFEGaussianKernel_eq_contour (w : ℂ) :
    ‖smoothAFEGaussianKernel w‖ = Real.exp (w.re ^ 2 - w.im ^ 2) / ‖w‖ := by
  unfold smoothAFEGaussianKernel
  rw [norm_div, Complex.norm_exp]
  congr 2
  simp [sq]

theorem norm_cpow_ofReal_div_le {b : ℝ} (hb : 0 < b) {u : ℝ} (hu1 : -(1 / 4) ≤ u) (hu2 : u ≤ 1)
    (t : ℝ) :
    ‖((b : ℝ) : ℂ) ^ ((u : ℂ) + (t : ℂ) * I)‖ ≤ max b (b ^ (-(1 / 4 : ℝ))) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  rcases le_or_gt 1 b with hb1 | hb1
  · calc b ^ u ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hu2
      _ = b := Real.rpow_one b
      _ ≤ max b (b ^ (-(1 / 4 : ℝ))) := le_max_left _ _
  · calc b ^ u ≤ b ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hb hb1.le hu1
      _ ≤ max b (b ^ (-(1 / 4 : ℝ))) := le_max_right _ _

/-- The integrand on a horizontal edge `u ± iT`, `−1/4 ≤ u ≤ 1`, `T ≥ 1`. -/
theorem norm_smoothDiagonalIntegrand_horizontal_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, |σ| ≤ 3 → 1 ≤ |t| → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {u T : ℝ} (hu1 : -(1 / 4) ≤ u) (hu2 : u ≤ 1) (hT : 1 ≤ T) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * max (x / c) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1) * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  -- zeta factor
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      = ((2 * σ₀ + 2 * u : ℝ) : ℂ) + ((2 * (ε * T) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ C * (2 * T) ^ N := by
    rw [harg]
    have h := hζ (2 * σ₀ + 2 * u) (2 * (ε * T)) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < T)]; linarith)
    rw [abs_mul, abs_mul, hεabs, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (by linarith : (0 : ℝ) < T)] at h
    simpa using h
  -- power factor
  have hp := norm_cpow_ofReal_div_le (div_pos hx hc) hu1 hu2 (ε * T)
  -- kernel factor
  have hk : ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
    rw [norm_smoothAFEGaussianKernel_eq_contour]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    have hnorm : T ≤ ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
      rw [abs_mul, hεabs, one_mul, abs_of_pos (by linarith : (0 : ℝ) < T)] at this
      exact this
    have hu2' : u ^ 2 ≤ 1 := by nlinarith
    have hsq : (ε * T) ^ 2 = T ^ 2 := by rw [mul_pow, hεsq, one_mul]
    rw [hsq]
    calc Real.exp (u ^ 2 - T ^ 2) / ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖
        ≤ Real.exp (u ^ 2 - T ^ 2) / 1 := by
          apply div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos
          linarith
      _ = Real.exp (u ^ 2) * Real.exp (-(T ^ 2)) := by rw [div_one, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu2') (Real.exp_pos _).le
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * (2 * T) ^ N) * max (x / c) ((x / c) ^ (-(1 / 4 : ℝ)))
          * (Real.exp 1 * Real.exp (-(T ^ 2))) :=
        mul_le_mul (mul_le_mul hz hp (norm_nonneg _) (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (C * max (x / c) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1)
          * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by ring

/-- The integrand on the left line `Re w = −1/4`. -/
theorem norm_smoothDiagonalIntegrand_left_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 1 / 4 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2)
    (t : ℝ) :
    ‖smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I))
      = ((2 * σ₀ - 1 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I))‖
      ≤ C * (1 + |2 * t|) ^ 2 := by
    rw [harg]
    exact hζ (2 * σ₀ - 1 / 2) (2 * t) (by linarith) (by linarith)
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I)‖ = (x / c) ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp
  have hk : ‖smoothAFEGaussianKernel ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ 4 * Real.exp (1 / 16) * Real.exp (-(t ^ 2)) := by
    rw [norm_smoothAFEGaussianKernel_eq_contour]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    have hnorm : (1 / 4 : ℝ) ≤ ‖(((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I)
      rw [show ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I).re = -(1 / 4) by simp, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at this
      exact this
    calc Real.exp ((-(1 / 4)) ^ 2 - t ^ 2) / ‖(((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I‖
        ≤ Real.exp ((-(1 / 4)) ^ 2 - t ^ 2) / (1 / 4) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
      _ = 4 * Real.exp (1 / 16) * Real.exp (-(t ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add,
            show ((-(1 / 4) : ℝ)) ^ 2 - t ^ 2 = 1 / 16 + -(t ^ 2) by ring]
          field_simp
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((((-(1 / 4) : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * (1 + |2 * t|) ^ 2) * (x / c) ^ (-(1 / 4 : ℝ))
          * (4 * Real.exp (1 / 16) * Real.exp (-(t ^ 2))) := by
        rw [hp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
          * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by ring

/-- The integrand on the right line `Re w = 1`. -/
theorem norm_smoothDiagonalIntegrand_right_le {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (t : ℝ) :
    ‖smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) * (x / c) * Real.exp 1) * Real.exp (-(t ^ 2)) := by
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * (((1 : ℝ) : ℂ) + (t : ℂ) * I))‖
      ≤ ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2 := by
    apply norm_riemannZeta_le_of_two_le_re_tsum
    simp
    linarith
  have hp : ‖((x / c : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖ = x / c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp
  have hk := norm_smoothAFEGaussianKernel_vertical_le (σ := 1) one_pos t
  have hk' : ‖smoothAFEGaussianKernel (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Real.exp 1 * Real.exp (-(t ^ 2)) := by
    simpa using hk
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * (((1 : ℝ) : ℂ) + (t : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) * (x / c) * (Real.exp 1 * Real.exp (-(t ^ 2))) := by
        rw [hp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hk' (norm_nonneg _)
          (by positivity)
    _ = ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) * (x / c) * Real.exp 1) * Real.exp (-(t ^ 2)) := by ring

/-! ## Continuity and integrability on vertical lines -/

theorem continuous_smoothDiagonalIntegrand_line {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x) {u : ℝ}
    (hu : u ≠ 0) (hpole : 2 * σ₀ + 2 * u ≠ 1) :
    Continuous (fun t : ℝ => smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + (t : ℂ) * I)) := by
  unfold smoothDiagonalIntegrand
  have hz : Continuous (fun t : ℝ => riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + (t : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + (t : ℂ) * I)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hpole (by linarith)
    exact ContinuousAt.comp (g := riemannZeta)
      (f := fun t : ℝ => (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + (t : ℂ) * I)))
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  have hp : Continuous (fun t : ℝ => ((x / c : ℝ) : ℂ) ^ ((u : ℂ) + (t : ℂ) * I)) := by
    haveI : NeZero ((x / c : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (div_pos hx hc).ne'⟩
    exact (continuous_const_cpow ((x / c : ℝ) : ℂ)).comp (by fun_prop)
  have hk : Continuous (fun t : ℝ => smoothAFEGaussianKernel ((u : ℂ) + (t : ℂ) * I)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (by fun_prop)).div (by fun_prop) (fun t h => by
      have := congrArg Complex.re h
      simp at this
      exact hu this)
  exact (hz.mul hp).mul hk

theorem integrable_smoothDiagonalIntegrand_right {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) :
    Integrable (fun t : ℝ => smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hcont := continuous_smoothDiagonalIntegrand_line (σ₀ := σ₀) hc hx (u := 1) one_ne_zero
    (by linarith)
  refine Integrable.mono' (((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
    ((∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) * (x / c) * Real.exp 1))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have := norm_smoothDiagonalIntegrand_right_le hc hx hσ0 t
  simpa [neg_mul, one_mul] using this

theorem integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq :
    Integrable (fun t : ℝ => (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) := by
  have h := GaloisForLFunctions.HTGeometry.integrable_one_add_abs_pow_mul_exp_neg_sq 2
  refine (h.const_mul 4).mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : 1 + |2 * t| ≤ 2 * (1 + |t|) := by rw [abs_mul, abs_two]; linarith
  have h2 : (1 + |2 * t|) ^ 2 ≤ 4 * (1 + |t|) ^ 2 := by
    calc (1 + |2 * t|) ^ 2 ≤ (2 * (1 + |t|)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 4 * (1 + |t|) ^ 2 := by ring
  nlinarith [Real.exp_pos (-(t ^ 2))]

theorem integrable_smoothDiagonalIntegrand_left {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 1 / 4 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) :
    Integrable (fun t : ℝ => smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hcont := continuous_smoothDiagonalIntegrand_line (σ₀ := σ₀) hc hx (u := -(1 / 4))
    (by norm_num) (by linarith)
  refine Integrable.mono' (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul
    (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_smoothDiagonalIntegrand_left_le hc hx hσ0 hσ1 hC0 hζ t)

/-! ## The rectangle and its horizontal edges -/

theorem rectIntegral_smoothDiagonalIntegrand_eq {σ₀ c x T : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ < 1 / 2) (hT : 0 < T) :
    rectIntegral (smoothDiagonalIntegrand σ₀ c x) (((-(1 / 4) : ℝ) : ℂ) - (T : ℂ) * I)
        (((1 : ℝ) : ℂ) + (T : ℂ) * I)
      = 2 * Real.pi * I * (riemannZeta ((2 * σ₀ : ℝ) : ℂ) + smoothDiagonalShiftedResidue σ₀ c x) := by
  have hσ : σ₀ ≠ 1 / 2 := ne_of_lt hσ1
  apply rectIntegral_eq_two_pole_residues (p := 0) (q := diagonalShift σ₀)
    (R := smoothDiagonalRemainder σ₀ c x)
  · simp
  · simp
  · simpa using hT
  · simpa using hT
  · unfold diagonalShift; simp; linarith
  · unfold diagonalShift; simp; linarith
  · unfold diagonalShift; simpa using hT
  · unfold diagonalShift; simpa using hT
  · exact differentiable_smoothDiagonalRemainder hc hx σ₀
  · intro z hz0 hzδ
    simpa only [sub_zero, add_assoc] using
      smoothDiagonalIntegrand_eq_two_poles_add_remainder hσ c x hz0 hzδ

/-- Both horizontal edges vanish as `T → ∞`. -/
theorem tendsto_smoothDiagonalIntegrand_horizontal {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 0 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  set B : ℝ := C * max (x / c) ((x / c) ^ (-(1 / 4 : ℝ))) * Real.exp 1 with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ => ((5 / 4) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq 0 N).const_mul ((5 / 4) * B * 2 ^ N)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-(1 / 4) : ℝ) (1 : ℝ),
      ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num)] at hu
    exact norm_smoothDiagonalIntegrand_horizontal_le hc hx hσ0 hσ1 hC hζ hu.1.le hu.2 hT hε
  calc ‖∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
        smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((2 * T) ^ N * Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-(1 / 4))| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((5 / 4) * B * 2 ^ N) * ((0 + T) ^ N * Real.exp (-(T ^ 2))) := by
        rw [show |(1 : ℝ) - (-(1 / 4))| = 5 / 4 by norm_num, mul_pow, zero_add]
        ring

/-! ## The contour shift -/

/-- **The smoothed diagonal is the two residues plus the left-line integral.** -/
theorem smoothDiagonal_eq_residues_add_left {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 1 / 4 ≤ σ₀) (hσ1 : σ₀ < 1 / 2) :
    smoothDiagonal σ₀ c x
      = riemannZeta ((2 * σ₀ : ℝ) : ℂ) + smoothDiagonalShiftedResidue σ₀ c x
        + (1 / (2 * Real.pi)) • ∫ t : ℝ,
            smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hσ0' : 0 ≤ σ₀ := by linarith
  have hbottom' := tendsto_smoothDiagonalIntegrand_horizontal hc hx hσ0' hσ1.le (ε := -1) (Or.inr rfl)
  have htop' := tendsto_smoothDiagonalIntegrand_horizontal hc hx hσ0' hσ1.le (ε := 1) (Or.inl rfl)
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    refine hbottom'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine htop'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have hright : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_smoothDiagonalIntegrand_right hc hx hσ0')
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_smoothDiagonalIntegrand_left hc hx hσ0 hσ1.le)
      tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  set R : ℂ := riemannZeta ((2 * σ₀ : ℝ) : ℂ) + smoothDiagonalShiftedResidue σ₀ c x with hRdef
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
          smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          (∫ u : ℝ in (-(1 / 4) : ℝ)..(1 : ℝ),
            smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
        = 2 * Real.pi * I * R := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hrect := rectIntegral_smoothDiagonalIntegrand_eq (σ₀ := σ₀) (c := c) (x := x) (T := T)
      hc hx hσ0' hσ1 hT
    rw [hRdef]
    rw [← hrect]
    simp only [RHTower.rectIntegral, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
      add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_sub, zero_add]
  have h := tendsto_nhds_unique (hlimit.congr' hevent) (tendsto_const_nhds (x := 2 * Real.pi * I * R))
  have h' : I • ((∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
      ∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
      = 2 * Real.pi * I * R := by
    rw [smul_sub]
    simpa [sub_eq_add_neg] using h
  have hI : (∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      = 2 * Real.pi * R + ∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I) := by
    have hI2 : I * ((∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        ∫ v : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I))
        = I * (2 * Real.pi * R) := by
      rw [← smul_eq_mul, h']
      ring
    have := mul_left_cancel₀ I_ne_zero hI2
    linear_combination this
  rw [smoothDiagonal_eq_integral hc hx hσ0', hI, smul_add, hRdef]
  congr 1
  rw [Complex.real_smul]
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast
  field_simp

/-- **The left-line remainder is `O((x/c)^{-1/4})`**, uniformly in `σ₀ ∈ [¼, ½)`, `c`, `x`. -/
theorem exists_norm_smoothDiagonal_left_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ₀ c x : ℝ, 1 / 4 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖(1 / (2 * Real.pi)) • ∫ t : ℝ,
          smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ K * (x / c) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C, hC0, hζ⟩ := exists_norm_riemannZeta_le_leftStrip
  have hG0 : 0 ≤ ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) :=
    integral_nonneg fun t => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (4 * C * Real.exp (1 / 16)
    * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))), by positivity,
    fun σ₀ c x hσ0 hσ1 hc hx => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun t : ℝ => norm_smoothDiagonalIntegrand_left_le hc hx hσ0 hσ1 hC0 hζ t
  have hnorm : ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) := by
    calc ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
            * ((1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (integrable_one_add_abs_two_mul_sq_mul_exp_neg_sq.const_mul _)
            (Filter.Eventually.of_forall fun t => hbound t)
      _ = (4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
            * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2)) := by
          rw [integral_const_mul]
  calc (1 / (2 * Real.pi)) * ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((-(1 / 4) : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * ((4 * C * Real.exp (1 / 16) * (x / c) ^ (-(1 / 4 : ℝ)))
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 / (2 * Real.pi)) * (4 * C * Real.exp (1 / 16)
          * ∫ t : ℝ, (1 + |2 * t|) ^ 2 * Real.exp (-(t ^ 2))) * (x / c) ^ (-(1 / 4 : ℝ)) := by ring

end RHTower

end
