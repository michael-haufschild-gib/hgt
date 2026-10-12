import GaloisForLFunctions.HTGeometry.HermiteCoherentPoisson
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen
import Mathlib.Analysis.Fourier.Convolution

/-!
# The Hermite tail of a Gaussian-smoothed compactly supported function

For a Schwartz function `f` vanishing outside `[−T, T]`, the Gaussian smoothing
`w = f ⋆ e^{-πx²}` (`gaussSmooth`) is a superposition `∫ f(t) ψ_t dt` of translated Gaussians.  Its
Hermite coefficients are the corresponding superpositions of the coherent-state coefficients
(`hermiteCoeff_gaussSmooth`), and each of those is bounded by the Poisson weight of the extreme
translate `πT²` once the index exceeds `πT²`.  Hence (`norm_sq_sub_hermiteTrunc_gaussSmooth_le`)

`‖w − Π_N w‖² ≤ ‖f‖₁² ‖ψ_0‖² (θ e^{1-θ})^N/(1 − θ)`   whenever `πT² ≤ θN`, `0 ≤ θ < 1`.

Degree `N` truncation captures the smoothing of every function supported in `|x| ≤ T` with
exponentially small error exactly when `πT² < N`.
-/

open scoped Real SchwartzMap Convolution
open Complex MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- The Gaussian smoothing `f ⋆ e^{-πx²}`. -/
def gaussSmooth (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f gaussianSchwartz

theorem gaussSmooth_apply (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    gaussSmooth f y = ∫ t : ℝ, f t * coherentGauss t y := by
  rw [gaussSmooth, SchwartzMap.convolution_apply]
  simp only [convolution_def, ContinuousLinearMap.mul_apply', gaussianSchwartz_apply,
    coherentGauss_apply]

theorem norm_coherentGauss_apply_le (t y : ℝ) : ‖coherentGauss t y‖ ≤ 1 := by
  rw [coherentGauss_apply, Complex.norm_real, Real.norm_of_nonneg (gaussReal_pos _).le]
  exact Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, sq_nonneg (y - t)])

theorem continuous_coherentGauss_uncurry :
    Continuous (fun p : ℝ × ℝ => coherentGauss p.1 p.2) := by
  simp only [coherentGauss_apply, gaussReal]
  fun_prop

/-- **Fubini.**  `⟨f ⋆ ψ_0, g⟩ = ∫ f(t) ⟨ψ_t, g⟩ dt`. -/
theorem schwartzPair_gaussSmooth (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (gaussSmooth f) g = ∫ t : ℝ, f t * schwartzPair (coherentGauss t) g := by
  rw [schwartzPair_eq_integral]
  simp_rw [gaussSmooth_apply, schwartzPair_eq_integral]
  have hint : Integrable (fun p : ℝ × ℝ => f p.2 * coherentGauss p.2 p.1 * g p.1)
      ((volume : Measure ℝ).prod volume) := by
    refine ((g.integrable (μ := volume)).norm.mul_prod (f.integrable (μ := volume)).norm).mono'
      ((((f.continuous.comp continuous_snd).mul
        (continuous_coherentGauss_uncurry.comp continuous_swap)).mul
        (g.continuous.comp continuous_fst)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul]
    have := norm_coherentGauss_apply_le p.2 p.1
    calc ‖f p.2‖ * ‖coherentGauss p.2 p.1‖ * ‖g p.1‖ ≤ ‖f p.2‖ * 1 * ‖g p.1‖ := by gcongr
      _ = ‖g p.1‖ * ‖f p.2‖ := by ring
  have h1 : ∫ y : ℝ, (∫ t : ℝ, f t * coherentGauss t y) * g y =
      ∫ y : ℝ, ∫ t : ℝ, f t * coherentGauss t y * g y := by
    congr 1; funext y; rw [← integral_mul_const]
  rw [h1, integral_integral_swap hint]
  congr 1
  funext t
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem hermiteCoeff_gaussSmooth (f : 𝓢(ℝ, ℂ)) (j : ℕ) :
    hermiteCoeff (gaussSmooth f) j = ∫ t : ℝ, f t * hermiteCoeff (coherentGauss t) j := by
  rw [hermiteCoeff, schwartzPair_gaussSmooth, ← integral_const_mul]
  congr 1
  funext t
  rw [hermiteCoeff]
  ring

/-- Translation does not change the `L²` norm of the Gaussian. -/
theorem norm_toLp_coherentGauss (t : ℝ) :
    ‖(coherentGauss t).toLp 2 (volume : Measure ℝ)‖ =
      ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ := by
  have h : ∀ t : ℝ, ‖(coherentGauss t).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) =
      ∫ y : ℝ, ‖coherentGauss 0 y‖ ^ (2 : ℕ) := fun t => by
    rw [norm_toLp_sq_eq_integral]
    have := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => ‖coherentGauss 0 y‖ ^ (2 : ℕ)) t
    rw [← this]
    congr 1
    funext y
    simp
  have h2 := h t
  rw [← h 0] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- **The coefficient bound past the Poisson mean.**  For `|t| ≤ T` and `πT² ≤ j`,
`|c_j(ψ_t)|² ≤ ‖ψ_0‖² e^{-πT²} (πT²)ʲ/j!`. -/
theorem norm_sq_hermiteCoeff_coherentGauss_le {T t : ℝ} (ht : |t| ≤ T) {j : ℕ}
    (hj : π * T ^ 2 ≤ j) :
    ‖hermiteCoeff (coherentGauss t) j‖ ^ 2 ≤
      ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
        (Real.exp (-(π * T ^ 2)) * ((π * T ^ 2) ^ j / j.factorial)) := by
  rw [norm_sq_hermiteCoeff_coherentGauss, norm_sq_hermiteCoeff_coherentGauss_zero,
    norm_toLp_coherentGauss]
  have hl : π * t ^ 2 ≤ π * T ^ 2 := by
    have : t ^ 2 ≤ T ^ 2 := by
      have := abs_nonneg t
      nlinarith [sq_abs t]
    nlinarith [Real.pi_pos]
  have hm := pow_mul_exp_neg_le_of_le_of_le (by positivity) hl hj
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hc := sq_nonneg ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖
  calc ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 * Real.exp (-(π * t ^ 2)) *
        ((π * t ^ 2) ^ j / j.factorial)
      = ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
          ((π * t ^ 2) ^ j * Real.exp (-(π * t ^ 2))) / j.factorial := by ring
    _ ≤ ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
          ((π * T ^ 2) ^ j * Real.exp (-(π * T ^ 2))) / j.factorial := by gcongr
    _ = _ := by ring

/-- **The Hermite tail of a Gaussian smoothing.**  If `f` vanishes outside `[−T, T]` and
`πT² ≤ θN` with `0 ≤ θ < 1`, then
`‖w − Π_N w‖² ≤ (∫|f|)² ‖ψ_0‖² (θ e^{1-θ})^N/(1 − θ)` for `w = f ⋆ e^{-πx²}`. -/
theorem norm_sq_sub_hermiteTrunc_gaussSmooth_le (f : 𝓢(ℝ, ℂ)) {T θ : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → f t = 0) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N : ℕ}
    (hN : π * T ^ 2 ≤ θ * N) :
    ‖(gaussSmooth f - hermiteTrunc (gaussSmooth f) N).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      (∫ t : ℝ, ‖f t‖) ^ 2 * ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
        ((θ * Real.exp (1 - θ)) ^ N / (1 - θ)) := by
  set l := π * T ^ 2 with hl_def
  have hl : 0 ≤ l := by positivity
  set c := ‖(coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ with hc_def
  set F := ∫ t : ℝ, ‖f t‖ with hF_def
  have hF : 0 ≤ F := integral_nonneg fun _ => norm_nonneg _
  have hNθ : (θ * N : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  -- the per-coefficient bound
  have hcoef : ∀ i : ℕ, ‖hermiteCoeff (gaussSmooth f) (i + N)‖ ^ 2 ≤
      F ^ 2 * c ^ 2 * (Real.exp (-l) * (l ^ (i + N) / (i + N).factorial)) := by
    intro i
    have hj : l ≤ ((i + N : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ ((i + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N i
      linarith
    set B := Real.sqrt (c ^ 2 * (Real.exp (-l) * (l ^ (i + N) / (i + N).factorial))) with hB
    have hB0 : 0 ≤ B := Real.sqrt_nonneg _
    have hpt : ∀ t : ℝ, ‖f t * hermiteCoeff (coherentGauss t) (i + N)‖ ≤ ‖f t‖ * B := by
      intro t
      rw [norm_mul]
      by_cases ht : T < |t|
      · rw [hsupp t ht, norm_zero, zero_mul, zero_mul]
      · have h := norm_sq_hermiteCoeff_coherentGauss_le (le_of_not_gt ht) hj
        have h2 : ‖hermiteCoeff (coherentGauss t) (i + N)‖ ≤ B := by
          rw [hB]
          exact Real.le_sqrt_of_sq_le h
        exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hint : ‖hermiteCoeff (gaussSmooth f) (i + N)‖ ≤ F * B := by
      rw [hermiteCoeff_gaussSmooth]
      calc ‖∫ t : ℝ, f t * hermiteCoeff (coherentGauss t) (i + N)‖
          ≤ ∫ t : ℝ, ‖f t‖ * B :=
            norm_integral_le_of_norm_le ((f.integrable (μ := volume)).norm.mul_const B)
              (Filter.Eventually.of_forall hpt)
        _ = F * B := by rw [integral_mul_const]
    have hsq : (F * B) ^ 2 = F ^ 2 * (c ^ 2 * (Real.exp (-l) * (l ^ (i + N) / (i + N).factorial))) := by
      rw [mul_pow, hB, Real.sq_sqrt (by positivity)]
    calc ‖hermiteCoeff (gaussSmooth f) (i + N)‖ ^ 2 ≤ (F * B) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hint 2
      _ = _ := by rw [hsq]; ring
  -- the comparison series
  have hexpS : Summable (fun i : ℕ => l ^ (i + N) / (i + N).factorial) := by
    have := (NormedSpace.expSeries_div_hasSum_exp l).summable
    exact (summable_nat_add_iff N).2 this
  have hdom : Summable (fun i : ℕ => F ^ 2 * c ^ 2 * (Real.exp (-l) *
      (l ^ (i + N) / (i + N).factorial))) :=
    (hexpS.mul_left (Real.exp (-l))).mul_left _
  have htail := hasSum_norm_sq_hermiteCoeff_tail (gaussSmooth f) N
  have hle := hasSum_le hcoef htail hdom.hasSum
  refine hle.trans ?_
  rw [tsum_mul_left, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (exp_neg_mul_tsum_tail_le hl hθ0 hθ1 hN) (by positivity)

/-! ## The truncation as a polynomial–Gaussian -/

theorem natDegree_hermitePoly_le_self (n : ℕ) : (hermitePoly n).natDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermitePoly_succ, hermiteStep]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_
      have : (2 * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
        have h := Polynomial.natDegree_mul_le (p := (2 : Polynomial ℝ)) (q := Polynomial.X)
        have h2 : (2 : Polynomial ℝ).natDegree = 0 := Polynomial.natDegree_ofNat 2
        have h3 := Polynomial.natDegree_X_le (R := ℝ)
        omega
      omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_derivative_le _).trans (by omega))

theorem hermitePoly_comp_neg (n : ℕ) :
    (hermitePoly n).comp (-Polynomial.X) = (-1 : ℝ) ^ n • hermitePoly n := by
  apply Polynomial.funext
  intro x
  have h := hermiteSchwartz_neg n x
  simp only [hermiteSchwartz_apply] at h
  have hg : gaussReal (-x) = gaussReal x := by simp [gaussReal]
  rw [hg] at h
  have hgpos := gaussReal_pos x
  have h2 : (((hermitePoly n).eval (-x) : ℝ) : ℂ) * ((gaussReal x : ℝ) : ℂ) =
      (((-1 : ℝ) ^ n * (hermitePoly n).eval x : ℝ) : ℂ) * ((gaussReal x : ℝ) : ℂ) := by
    push_cast at h ⊢; linear_combination h
  have h3 : (hermitePoly n).eval (-x) = (-1 : ℝ) ^ n * (hermitePoly n).eval x := by
    have hne : ((gaussReal x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    exact_mod_cast mul_right_cancel₀ hne h2
  simp [Polynomial.eval_comp, h3]

/-- The real polynomial of the degree-`N` truncation. -/
def hermiteTruncPoly (w : 𝓢(ℝ, ℂ)) (N : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range N, Polynomial.C ((hermiteCoeff w j).re /
    ‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖) * hermitePoly j

theorem hermiteTrunc_apply_of_real (w : 𝓢(ℝ, ℂ)) (N : ℕ)
    (hreal : ∀ j, (hermiteCoeff w j).im = 0) (x : ℝ) :
    hermiteTrunc w N x = polyGaussSchwartz (hermiteTruncPoly w N) x := by
  simp only [hermiteTrunc, sum_apply, smul_apply, smul_eq_mul, polyGaussSchwartz_apply,
    hermiteTruncPoly, Polynomial.eval_finsetSum, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hermiteUnit, smul_apply, hermiteSchwartz_apply, smul_eq_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  have hc : hermiteCoeff w j = ((hermiteCoeff w j).re : ℂ) := by
    apply Complex.ext <;> simp [hreal j]
  nth_rw 1 [hc]
  push_cast
  ring

theorem natDegree_hermiteTruncPoly_le (w : 𝓢(ℝ, ℂ)) (N : ℕ) :
    (hermiteTruncPoly w N).natDegree ≤ N - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((natDegree_hermitePoly_le_self j).trans ?_)
  have := Finset.mem_range.1 hj
  omega

/-- The coefficients of an even function vanish at odd indices. -/
theorem hermiteCoeff_eq_zero_of_even (w : 𝓢(ℝ, ℂ)) (heven : ∀ x, w (-x) = w x) {j : ℕ}
    (hj : Odd j) : hermiteCoeff w j = 0 := by
  rw [hermiteCoeff, schwartzPair_eq_integral]
  have h : ∫ x : ℝ, w x * hermiteSchwartz j x = -∫ x : ℝ, w x * hermiteSchwartz j x := by
    conv_lhs => rw [← integral_neg_eq_self]
    rw [← integral_neg]
    congr 1
    funext x
    rw [heven, hermiteSchwartz_neg, hj.neg_one_pow]
    ring
  have h0 : ∫ x : ℝ, w x * hermiteSchwartz j x = 0 := by linear_combination h / 2
  rw [h0, mul_zero]

theorem hermiteTruncPoly_comp_neg (w : 𝓢(ℝ, ℂ)) (heven : ∀ x, w (-x) = w x) (N : ℕ) :
    (hermiteTruncPoly w N).comp (-Polynomial.X) = hermiteTruncPoly w N := by
  rw [hermiteTruncPoly, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, hermitePoly_comp_neg]
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow, one_smul]
  · rw [hermiteCoeff_eq_zero_of_even w heven hj]
    simp

theorem hermiteCoeff_im_eq_zero_of_real (w : 𝓢(ℝ, ℂ)) (hreal : ∀ x, (w x).im = 0) (j : ℕ) :
    (hermiteCoeff w j).im = 0 := by
  rw [hermiteCoeff, schwartzPair_eq_integral]
  have h : ∫ x : ℝ, w x * hermiteSchwartz j x =
      ((∫ x : ℝ, (w x).re * ((hermitePoly j).eval x * gaussReal x)) : ℝ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    have hw : w x = ((w x).re : ℂ) := by apply Complex.ext <;> simp [hreal x]
    rw [hermiteSchwartz_apply, hw]
    push_cast
    simp
  rw [h, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_im]

end

end GaloisForLFunctions
