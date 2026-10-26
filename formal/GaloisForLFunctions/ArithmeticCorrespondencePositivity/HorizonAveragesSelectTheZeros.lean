import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeRankCountsTheDominantZeros

/-!
# Horizon averages select the zeros

The escape states of a dominant configuration `F(u) = Σ_k c_k e^{(x + i y_k) u}` are the phase
kernels `K_θ` (`TheEscapeRankCountsTheDominantZeros`); along the horizon `L` the phase is
`θ_k(L) = e^{i y_k L}`, and the cross terms `k ≠ l` of `K_{θ(L)}` oscillate like `e^{i(y_k − y_l)L}`.
Averaging over horizons removes them.

* **Phase form** (`escapeKernel_phase`). `K_{θ(L)}(a, b) = Σ_{k,l} D_{kl}(a, b) e^{i(y_k − y_l)L}`
  with `D_{kl} = c_k ψ_k(a) conj(c_l ψ_l(b)) / (2x + i(y_k − y_l))`.
* **The spacing bound** (`norm_integral_phaseExp_le`). For `ω ≠ 0`,
  `|∫_0^T e^{iωL} dL| ≤ 2/|ω|`: a window of length `T` damps the cross term at frequency `ω` by
  `2/(|ω| T)`.
* **Selection** (`norm_avg_escapeKernel_sub_le`, `tendsto_avg_escapeKernel`). The horizon average
  `T^{−1} ∫_0^T K_{θ(L)} dL` differs from the **diagonal kernel**
  `D(a, b) = Σ_k c_k ψ_k(a) conj(c_k ψ_k(b)) / (2x)` by at most
  `(2/T) Σ_{k ≠ l} |D_{kl}(a, b)| / |y_k − y_l|`, and tends to it.
* **The Cesàro escape state** (`tendsto_avg_gram`). The horizon averages of the scaled Grams
  `e^{−2xL} ∫_0^L F(u − a) F̄(u − b) du` tend to the same diagonal kernel.

So an average over horizons becomes a sum of points: the averaged escape state is
`Σ_k (|c_k|²/2x) ψ_k ⊗ ψ̄_k`, each dominant zero selected with its own mass and no interaction.
The window must exceed the inverse spacing `1/|y_k − y_l|` of the zeros it separates: this is
selection at the zero-spacing scale for the escape model. Single escape states keep the cross
terms (they are phase kernels); averaging over horizons is what isolates the zeros.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {r : ℕ}

/-- The coefficient `D_{kl}(a, b)` of the cross term at frequency `y_k − y_l`. -/
def crossCoeff (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (a b : ℝ) (k l : Fin r) : ℂ :=
  c k * transChar x (y k) a * conj (c l * transChar x (y l) b) /
    (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)

/-- The diagonal kernel `Σ_k c_k ψ_k(a) conj(c_k ψ_k(b)) / (2x)`. -/
def diagKernel (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (a b : ℝ) : ℂ :=
  ∑ k, c k * transChar x (y k) a * conj (c k * transChar x (y k) b) / (2 * (x : ℂ))

/-- **Phase form** of the escape kernel along the horizons. -/
theorem escapeKernel_phase (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (L a b : ℝ) :
    escapeKernel x y c (phase y L) a b =
      ∑ k, ∑ l, crossCoeff x y c a b k l * Complex.exp (((y k : ℂ) - y l) * I * L) := by
  unfold escapeKernel crossCoeff
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hθ : phase y L k * conj (phase y L l) = Complex.exp (((y k : ℂ) - y l) * I * L) := by
    simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp only [map_mul]
  linear_combination (c k * transChar x (y k) a * (conj (c l) * conj (transChar x (y l) b)) /
    (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)) * hθ

theorem continuous_phaseExp (ω : ℂ) : Continuous fun L : ℝ => Complex.exp (ω * L) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- **The spacing bound**: `|∫_0^T e^{iωL} dL| ≤ 2/|ω|` for `ω ≠ 0`. -/
theorem norm_integral_phaseExp_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖∫ L in (0 : ℝ)..T, Complex.exp ((ω : ℂ) * I * L)‖ ≤ 2 / |ω| := by
  have hc : (ω : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc, Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖Complex.exp ((ω : ℂ) * I * T)‖ = 1 := by
    rw [show (ω : ℂ) * I * T = ((ω * T : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖Complex.exp ((ω : ℂ) * I * T) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [h1, norm_one]
    norm_num
  exact div_le_div_of_nonneg_right h2 (abs_nonneg ω)

theorem integral_phaseExp_zero (T : ℝ) :
    ∫ L in (0 : ℝ)..T, Complex.exp (((0 : ℝ) : ℂ) * I * L) = T := by
  simp

/-- The integral of the escape kernel along the horizons, term by term. -/
theorem integral_escapeKernel_phase (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (a b T : ℝ) :
    ∫ L in (0 : ℝ)..T, escapeKernel x y c (phase y L) a b =
      ∑ k, ∑ l, crossCoeff x y c a b k l *
        ∫ L in (0 : ℝ)..T, Complex.exp (((y k - y l : ℝ) : ℂ) * I * L) := by
  have hfun : (fun L : ℝ => escapeKernel x y c (phase y L) a b) = fun L : ℝ =>
      ∑ k, ∑ l, crossCoeff x y c a b k l * Complex.exp (((y k - y l : ℝ) : ℂ) * I * L) := by
    funext L
    rw [escapeKernel_phase]
    simp only [Complex.ofReal_sub]
  rw [hfun, intervalIntegral.integral_finsetSum fun k _ =>
    (continuous_finsetSum _ fun l _ => continuous_gramTerm (crossCoeff x y c a b k l)
      (((y k - y l : ℝ) : ℂ) * I)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ => (continuous_gramTerm
      (crossCoeff x y c a b k l) (((y k - y l : ℝ) : ℂ) * I)).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun l _ => intervalIntegral.integral_const_mul _ _

/-- The off-diagonal remainder of the horizon average. -/
theorem avg_escapeKernel_sub_eq {x : ℝ} {y : Fin r → ℝ} (c : Fin r → ℂ) (a b : ℝ) {T : ℝ} (hT : T ≠ 0) :
    (T : ℂ)⁻¹ * (∫ L in (0 : ℝ)..T, escapeKernel x y c (phase y L) a b) - diagKernel x y c a b =
      ∑ k, ∑ l, if k = l then 0 else crossCoeff x y c a b k l *
        ((T : ℂ)⁻¹ * ∫ L in (0 : ℝ)..T, Complex.exp (((y k - y l : ℝ) : ℂ) * I * L)) := by
  have hdiag : diagKernel x y c a b = ∑ k, ∑ l, if k = l then crossCoeff x y c a b k l *
      ((T : ℂ)⁻¹ * ∫ L in (0 : ℝ)..T, Complex.exp (((y k - y l : ℝ) : ℂ) * I * L)) else 0 := by
    rw [diagKernel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k), sub_self, integral_phaseExp_zero, crossCoeff,
      sub_self, zero_mul, add_zero, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT), mul_one]
  rw [integral_escapeKernel_phase, Finset.mul_sum, hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

/-- **Selection at the zero-spacing scale.** The horizon average of the escape kernel differs from
the diagonal kernel by at most `(2/T) Σ_{k ≠ l} |D_{kl}| / |y_k − y_l|`. -/
theorem norm_avg_escapeKernel_sub_le {x : ℝ} {y : Fin r → ℝ} (hy : Function.Injective y)
    (c : Fin r → ℂ) (a b : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖(T : ℂ)⁻¹ * (∫ L in (0 : ℝ)..T, escapeKernel x y c (phase y L) a b) - diagKernel x y c a b‖ ≤
      2 / T * ∑ k, ∑ l, if k = l then 0 else ‖crossCoeff x y c a b k l‖ / |y k - y l| := by
  rw [avg_escapeKernel_sub_eq c a b hT.ne', Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs with hkl
  · simp
  · have hω : y k - y l ≠ 0 := sub_ne_zero.mpr fun h => hkl (hy h)
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have hb := norm_integral_phaseExp_le hω T
    have hn := norm_nonneg (crossCoeff x y c a b k l)
    calc ‖crossCoeff x y c a b k l‖ * (T⁻¹ *
          ‖∫ L in (0 : ℝ)..T, Complex.exp (((y k - y l : ℝ) : ℂ) * I * L)‖)
        ≤ ‖crossCoeff x y c a b k l‖ * (T⁻¹ * (2 / |y k - y l|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)) hn
      _ = 2 / T * (‖crossCoeff x y c a b k l‖ / |y k - y l|) := by ring

/-- **Horizon averages select the zeros**: the average of the escape kernel tends to the diagonal
kernel. -/
theorem tendsto_avg_escapeKernel (x : ℝ) {y : Fin r → ℝ} (hy : Function.Injective y)
    (c : Fin r → ℂ) (a b : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ L in (0 : ℝ)..T, escapeKernel x y c (phase y L) a b)
      atTop (𝓝 (diagKernel x y c a b)) := by
  set S := ∑ k, ∑ l, if k = l then 0 else ‖crossCoeff x y c a b k l‖ / |y k - y l|
  have hlim : Tendsto (fun T : ℝ => 2 / T * S) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const S
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact norm_avg_escapeKernel_sub_le hy c a b hT

theorem continuous_escapeKernel_phase (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (a b : ℝ) :
    Continuous fun L : ℝ => escapeKernel x y c (phase y L) a b := by
  have h : (fun L : ℝ => escapeKernel x y c (phase y L) a b) = fun L : ℝ =>
      ∑ k, ∑ l, crossCoeff x y c a b k l * Complex.exp ((((y k : ℂ) - y l) * I) * L) :=
    funext fun L => escapeKernel_phase x y c L a b
  rw [h]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    continuous_const.mul (continuous_phaseExp _)

/-- `|∫_0^T e^{−2xL} dL| ≤ 1/x` for `T ≥ 0`. -/
theorem norm_integral_exp_neg_le {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ L in (0 : ℝ)..T, (Real.exp (-(2 * x * L)) : ℂ)‖ ≤ 1 / x := by
  have hc : (((-(2 * x)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have e : (fun L : ℝ => (Real.exp (-(2 * x * L)) : ℂ)) =
      fun L : ℝ => Complex.exp ((((-(2 * x)) : ℝ) : ℂ) * L) := by
    funext L
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    ring
  have h1 : ‖Complex.exp ((((-(2 * x)) : ℝ) : ℂ) * T)‖ ≤ 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : ‖Complex.exp ((((-(2 * x)) : ℝ) : ℂ) * T) - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  rw [e, integral_exp_mul_complex hc, Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : -(2 * x) < 0), neg_neg,
    div_le_div_iff₀ (by linarith) hx]
  nlinarith

/-- **The Cesàro escape state** of a dominant configuration is the diagonal kernel. -/
theorem tendsto_avg_gram {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ} (hy : Function.Injective y)
    (c : Fin r → ℂ) (a b : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ L in (0 : ℝ)..T,
        (Real.exp (-(2 * x * L)) : ℂ) * hermGram (domProfile x y c) L a b)
      atTop (𝓝 (diagKernel x y c a b)) := by
  have hdecay : Continuous fun L : ℝ => (Real.exp (-(2 * x * L)) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
  -- the horizon law splits the integrand into the phase kernel and a decaying term
  have hsplit : ∀ T : ℝ, ∫ L in (0 : ℝ)..T,
      (Real.exp (-(2 * x * L)) : ℂ) * hermGram (domProfile x y c) L a b =
        (∫ L in (0 : ℝ)..T, escapeKernel x y c (phase y L) a b) -
          (∫ L in (0 : ℝ)..T, (Real.exp (-(2 * x * L)) : ℂ)) * escapeKernel x y c 1 a b := by
    intro T
    simp_rw [exp_mul_hermGram_eq hx]
    have hdec : Continuous fun L : ℝ => (Real.exp (-(2 * x * L)) : ℂ) * escapeKernel x y c 1 a b :=
      hdecay.mul continuous_const
    rw [intervalIntegral.integral_sub ((continuous_escapeKernel_phase x y c a b).intervalIntegrable _ _)
      (hdec.intervalIntegrable _ _), intervalIntegral.integral_mul_const]
  simp_rw [hsplit, mul_sub]
  rw [← sub_zero (diagKernel x y c a b)]
  refine (tendsto_avg_escapeKernel x hy c a b).sub ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ => T⁻¹ * (1 / x * ‖escapeKernel x y c 1 a b‖)) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (1 / x * ‖escapeKernel x y c 1 a b‖)
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (norm_integral_exp_neg_le hx hT.le) (norm_nonneg _))
    (inv_nonneg.mpr hT.le)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
