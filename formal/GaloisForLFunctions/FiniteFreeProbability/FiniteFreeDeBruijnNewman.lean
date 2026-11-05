import GaloisForLFunctions.FiniteFreeProbability.HermiteHeatOperator
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary
import GaloisForLFunctions.HTGeometry.ContactOrderEulerIntegral
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya

/-!
# The finite free de Bruijn–Newman law for the Jensen polynomials of `Ξ`

Let `J_d` be the degree-`d` Jensen polynomial of `Ξ(z) = ξ(1/2 + iz)` and `He_{d,s} = e^{sD²}X^d`.
For `s > 0`, `J_d ⊞_d He_{d,s} = e^{sD²} J_d` is the backward heat flow of `J_d` by time `s`.

**Theorem.** For every `t > 0`, `e^{(t/d²)D²} J_d` is not real-rooted for all large `d`.

So any finite free factorization `J_d = He_{d,−s} ⊞_d r` with `r` real-rooted, a Gaussian
(semicircle) component of variance `s`, has `s = o(d^{-2})`: the Jensen polynomials of `Ξ` carry
no Gaussian component at the de Bruijn–Newman scale `d^{-2}`.

Mechanism. Riemann's kernel `Φ` represents `J_d(X) = ∫ Φ(x) (1 + ixX)^d dx`, so
`(e^{(t/d²)D²} J_d)(z/d) = ∫ Φ(x) Σ_k ((−t x²)^k/k!) (d^{(2k)}/d^{2k}) (1 + ixz/d)^{d−2k} dx`.
Tannery's theorem in `k` and dominated convergence in `x` give the pointwise limit
`∫ Φ(x) e^{−t x²} e^{ixz} dx = H_{−t}(z)`, with the uniform bound `∫ Φ e^{t x²} e^{R|x|}` on
`|z| < R`; Vitali upgrades this to locally uniform convergence. Real-rootedness along a
subsequence would put `H_{−t}` in the Laguerre–Pólya class, contradicting the existence of
non-real zeros of `H_{−t}` (Rodgers–Tao).
-/

open Polynomial Filter Topology Complex MeasureTheory Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-! ## Moments of Riemann's kernel are the Taylor coefficients of `Ξ` -/

theorem integrable_riemannKernel_mul_pow (j : ℕ) :
    Integrable (fun x : ℝ => (riemannKernelReal x : ℂ) * (I * x) ^ j) := by
  refine ((riemannKernel_superExp.integrable_mul_exp 1).const_mul (j.factorial : ℝ)).mono'
    ((Complex.continuous_ofReal.comp riemannKernel_superExp.continuous).mul
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hΦ := riemannKernel_superExp.nonneg x
  have hpow : |x| ^ j ≤ (j.factorial : ℝ) * Real.exp |x| := by
    have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) j
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦ, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
  calc riemannKernelReal x * |x| ^ j ≤ riemannKernelReal x * ((j.factorial : ℝ) * Real.exp |x|) :=
        mul_le_mul_of_nonneg_left hpow hΦ
    _ = _ := by ring

/-- `Ξ^{(j)}(0) = ∫ Φ(x) (ix)^j dx`. -/
theorem iteratedDeriv_XiC_zero_eq_moment (j : ℕ) :
    iteratedDeriv j XiC 0 = ∫ x, (riemannKernelReal x : ℂ) * (I * x) ^ j := by
  rcases Nat.even_or_odd j with ⟨n, rfl⟩ | hodd
  · rw [show n + n = 2 * n by ring, iteratedDeriv_XiC_zero_eq_rawEvenMoment]
    have hint : Integrable (fun x : ℝ => x ^ (2 * n) * riemannKernelReal x) := by
      have h := (integrable_riemannKernel_mul_pow (2 * n)).norm
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_I,
        one_mul, abs_of_nonneg (riemannKernel_superExp.nonneg x)]
      rw [Even.pow_abs (even_two_mul n) x]; ring
    have heven := GaloisForLFunctions.HTGeometry.integral_even_eq_two_mul hint
      (fun x => by rw [riemannKernel_superExp.even, Even.neg_pow (even_two_mul n)])
    have hfun : (fun x : ℝ => (riemannKernelReal x : ℂ) * (I * x) ^ (2 * n)) =
        fun x : ℝ => (((-1) ^ n * (x ^ (2 * n) * riemannKernelReal x) : ℝ) : ℂ) := by
      funext x
      rw [pow_mul, mul_pow, I_sq]
      push_cast; ring
    rw [hfun, integral_complex_ofReal, integral_const_mul, heven, thetaCuspRawEvenMoment]
    congr 3
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [thetaCuspFullSource_eq_riemannKernelReal]
  · rw [iteratedDeriv_XiC_odd_zero hodd]
    set f : ℝ → ℂ := fun x => (riemannKernelReal x : ℂ) * (I * x) ^ j
    have hneg : (∫ x, f x) = -∫ x, f x := by
      conv_lhs => rw [← integral_neg_eq_self f volume]
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [f, riemannKernel_superExp.even, Complex.ofReal_neg, mul_neg, neg_pow,
        Odd.neg_one_pow hodd]
      ring
    linear_combination -hneg / 2

/-! ## The kernel representation of the heat-deformed Jensen polynomials -/

/-- The Jensen polynomial of `Ξ` over `ℂ` has coefficients `∫ Φ(x) C(d,j) (ix)^j dx`. -/
theorem jensenPoly_XiC_map (d : ℕ) :
    (jensenPoly (realTaylorCoeff XiC) d).map (algebraMap ℝ ℂ) =
      ∑ j ∈ Finset.range (d + 1),
        C (∫ x, (riemannKernelReal x : ℂ) * ((d.choose j : ℂ) * (I * x) ^ j)) * X ^ j := by
  rw [jensenPoly, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  have hc := ofReal_realTaylorCoeff (fun z => XiC_conj z) j
  have hdesc : (d.descFactorial j : ℂ) = (j.factorial : ℂ) * (d.choose j : ℂ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose d j
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  show ((realTaylorCoeff XiC j * (d.descFactorial j : ℝ) : ℝ) : ℂ) = _
  push_cast
  rw [hc, iteratedDeriv_XiC_zero_eq_moment, hdesc]
  have hfun : (fun x : ℝ => (riemannKernelReal x : ℂ) * ((d.choose j : ℂ) * (I * x) ^ j)) =
      fun x : ℝ => (d.choose j : ℂ) * ((riemannKernelReal x : ℂ) * (I * x) ^ j) := by
    funext x; ring
  rw [hfun, integral_const_mul]
  field_simp

/-- The integrand of the coefficients assembles into `Φ(x) (1 + ixX)^d`. -/
theorem sum_kernel_monomials (d : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range (d + 1),
        C ((riemannKernelReal x : ℂ) * ((d.choose j : ℂ) * (I * x) ^ j)) * X ^ j =
      C (riemannKernelReal x : ℂ) * (1 + C (I * x) * X) ^ d := by
  rw [add_comm (1 : ℂ[X]), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [one_pow, mul_one, mul_pow, ← C_pow, ← C_eq_natCast, C_mul]
  ring

/-- The heat operator commutes with integrating coefficients. -/
theorem eval_heatOp_integral (s w : ℂ) (d : ℕ) (b : ℕ → ℝ → ℂ) (hb : ∀ j, Integrable (b j)) :
    (heatOp s d (∑ j ∈ Finset.range (d + 1), C (∫ x, b j x) * X ^ j)).eval w =
      ∫ x, (heatOp s d (∑ j ∈ Finset.range (d + 1), C (b j x) * X ^ j)).eval w := by
  simp only [heatOp_sum, heatOp_C_mul, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum _ fun j _ => (hb j).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]

/-- **Kernel representation.** `(e^{sD²} J_d)(w) = ∫ Φ(x) Σ_k (s^k/k!) (ix)^{2k} d^{(2k)}
(1 + ixw)^{d−2k} dx`. -/
theorem eval_heatOp_jensenPoly_XiC (s : ℝ) (d : ℕ) (w : ℂ) :
    ((heatOp s d (jensenPoly (realTaylorCoeff XiC) d)).map (algebraMap ℝ ℂ)).eval w =
      ∫ x, (riemannKernelReal x : ℂ) *
        ∑ k ∈ Finset.range (d + 1), (s : ℂ) ^ k / (k.factorial : ℂ) * (I * x) ^ (2 * k) *
          (d.descFactorial (2 * k) : ℂ) * (1 + I * x * w) ^ (d - 2 * k) := by
  rw [heatOp_map, jensenPoly_XiC_map, Complex.coe_algebraMap,
    eval_heatOp_integral _ _ _ _ fun j => ((integrable_riemannKernel_mul_pow j).const_mul
      (d.choose j : ℂ)).congr (Eventually.of_forall fun x => by simp only; ring)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [sum_kernel_monomials, heatOp_C_mul, eval_mul, eval_C, eval_heatOp_one_add_C_mul_X_pow]

/-! ## Pointwise limit -/

/-- The `k`-th term of the scaled heat-deformed kernel. -/
def dbnTerm (t x : ℝ) (z : ℂ) (d k : ℕ) : ℂ :=
  (t : ℂ) ^ k / (k.factorial : ℂ) * (-(x : ℂ) ^ 2) ^ k *
    ((d.descFactorial (2 * k) : ℂ) / (d : ℂ) ^ (2 * k)) * (1 + I * x * z / d) ^ (d - 2 * k)

theorem dbnTerm_eq_zero {t x : ℝ} {z : ℂ} {d k : ℕ} (hk : d < 2 * k) : dbnTerm t x z d k = 0 := by
  simp [dbnTerm, Nat.descFactorial_eq_zero_iff_lt.2 hk]

/-- The scaled integrand is the finite sum of the `dbnTerm`s. -/
theorem kernel_sum_eq_dbnTerm (t x : ℝ) (z : ℂ) (d : ℕ) :
    ∑ k ∈ Finset.range (d + 1), ((t / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ k / (k.factorial : ℂ) *
        (I * x) ^ (2 * k) * (d.descFactorial (2 * k) : ℂ) * (1 + I * x * (z / d)) ^ (d - 2 * k) =
      ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dbnTerm, show (1 + I * x * (z / d)) = 1 + I * x * z / d by ring, pow_mul, mul_pow, I_sq]
  set B := (1 + I * x * z / d) ^ (d - 2 * k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : 0 < 2 * k)]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, div_pow, ← pow_mul]
  field_simp

theorem tsum_dbnTerm_eq_sum (t x : ℝ) (z : ℂ) (d : ℕ) :
    ∑' k, dbnTerm t x z d k = ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k :=
  tsum_eq_sum fun k hk => dbnTerm_eq_zero (by
    have := Finset.mem_range.not.1 hk; omega)

theorem tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun d : ℕ => (d.descFactorial m : ℂ) / (d : ℂ) ^ m) atTop (𝓝 1) := by
  have hreal : Tendsto (fun d : ℕ => ∏ i ∈ Finset.range m, (((d - i : ℕ) : ℝ) / d)) atTop
      (𝓝 (∏ _i ∈ Finset.range m, (1 : ℝ))) := by
    refine tendsto_finsetProd _ fun i _ => ?_
    have h1 : Tendsto (fun d : ℕ => (1 : ℝ) - (i : ℝ) * (1 / (d : ℝ))) atTop (𝓝 (1 - i * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with d hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Nat.cast_sub (by omega)]
    field_simp
  rw [Finset.prod_const_one] at hreal
  have hc := (Complex.continuous_ofReal.tendsto 1).comp hreal
  rw [Complex.ofReal_one] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  simp only [Function.comp_apply, Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_range]

theorem tendsto_one_add_div_pow_sub (a : ℂ) (m : ℕ) :
    Tendsto (fun d : ℕ => (1 + a / d) ^ (d - m)) atTop (𝓝 (Complex.exp a)) := by
  have hdiv : Tendsto (fun d : ℕ => a / (d : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
    rw [Complex.ofReal_zero] at h
    have := h.const_mul a
    rw [mul_zero] at this
    refine this.congr fun d => ?_
    simp [div_eq_mul_inv]
  have hpow : Tendsto (fun d : ℕ => (1 + a / d) ^ m) atTop (𝓝 1) := by
    have := ((continuous_pow m).tendsto (1 + 0)).comp (tendsto_const_nhds.add hdiv)
    simpa [Function.comp_def] using this
  have hq := (Complex.tendsto_one_add_div_pow_exp a).div hpow one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  have hne : ∀ᶠ d : ℕ in atTop, 1 + a / d ≠ 0 := by
    have := hdiv.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    filter_upwards [this] with d hd h0
    have : a / d = -1 := by linear_combination h0
    rw [this, dist_zero_right, norm_neg, norm_one] at hd
    exact lt_irrefl _ hd
  filter_upwards [hne, eventually_ge_atTop m] with d hd hdm
  rw [Pi.div_apply, pow_sub₀ _ hd hdm, div_eq_mul_inv]

theorem norm_one_add_div_pow_le (a : ℂ) {d m : ℕ} (hm : m ≤ d) :
    ‖(1 + a / d) ^ m‖ ≤ Real.exp ‖a‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.le_zero.1 hm, pow_zero, norm_one]; exact Real.one_le_exp (norm_nonneg _)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ‖1 + a / d‖ ≤ Real.exp (‖a‖ / d) := by
    calc ‖1 + a / d‖ ≤ ‖(1 : ℂ)‖ + ‖a / d‖ := norm_add_le _ _
      _ = ‖a‖ / d + 1 := by rw [norm_one, norm_div, Complex.norm_natCast]; ring
      _ ≤ _ := Real.add_one_le_exp _
  rw [norm_pow]
  calc ‖1 + a / d‖ ^ m ≤ Real.exp (‖a‖ / d) ^ m := pow_le_pow_left₀ (norm_nonneg _) h1 m
    _ = Real.exp (m * (‖a‖ / d)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp ‖a‖ := by
      apply Real.exp_le_exp.2
      have hmd : (m : ℝ) ≤ d := by exact_mod_cast hm
      rw [mul_div_assoc', div_le_iff₀ hd']
      nlinarith [norm_nonneg a]

theorem norm_dbnTerm_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) (z : ℂ) (d k : ℕ) :
    ‖dbnTerm t x z d k‖ ≤ (t * x ^ 2) ^ k / (k.factorial : ℝ) * Real.exp (|x| * ‖z‖) := by
  rw [dbnTerm, norm_mul, norm_mul, norm_mul]
  have h1 : ‖(t : ℂ) ^ k / (k.factorial : ℂ)‖ * ‖(-(x : ℂ) ^ 2) ^ k‖ =
      (t * x ^ 2) ^ k / (k.factorial : ℝ) := by
    simp only [norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    rw [abs_of_nonneg ht, sq_abs, mul_pow]
    ring
  have h2 : ‖(d.descFactorial (2 * k) : ℂ) / (d : ℂ) ^ (2 * k)‖ ≤ 1 := by
    rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · simp [zero_pow (by omega : 2 * k ≠ 0)]
    · rw [div_le_one (by positivity)]
      exact_mod_cast Nat.descFactorial_le_pow d (2 * k)
  have h3 : ‖(1 + I * x * z / d) ^ (d - 2 * k)‖ ≤ Real.exp (|x| * ‖z‖) := by
    have := norm_one_add_div_pow_le (I * x * z) (d := d) (m := d - 2 * k) (Nat.sub_le _ _)
    rwa [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
  rw [← h1]
  have hnn : 0 ≤ ‖(t : ℂ) ^ k / (k.factorial : ℂ)‖ * ‖(-(x : ℂ) ^ 2) ^ k‖ := by positivity
  calc ‖(t : ℂ) ^ k / (k.factorial : ℂ)‖ * ‖(-(x : ℂ) ^ 2) ^ k‖ *
        ‖(d.descFactorial (2 * k) : ℂ) / (d : ℂ) ^ (2 * k)‖ * ‖(1 + I * x * z / d) ^ (d - 2 * k)‖
      ≤ ‖(t : ℂ) ^ k / (k.factorial : ℂ)‖ * ‖(-(x : ℂ) ^ 2) ^ k‖ * 1 *
          Real.exp (|x| * ‖z‖) := by gcongr
    _ = _ := by ring

/-- **Tannery step.** The scaled kernel sum tends to `e^{−t x²} e^{ixz}`. -/
theorem tendsto_sum_dbnTerm {t : ℝ} (ht : 0 ≤ t) (x : ℝ) (z : ℂ) :
    Tendsto (fun d : ℕ => ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k) atTop
      (𝓝 ((Real.exp (-(t * x ^ 2)) : ℂ) * Complex.exp (I * x * z))) := by
  simp_rw [← tsum_dbnTerm_eq_sum]
  set g : ℕ → ℂ := fun k => ((t : ℂ) * (-(x : ℂ) ^ 2)) ^ k / (k.factorial : ℂ) *
    Complex.exp (I * x * z)
  have hg : HasSum g ((Real.exp (-(t * x ^ 2)) : ℂ) * Complex.exp (I * x * z)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * (-(x : ℂ) ^ 2))
    rw [← Complex.exp_eq_exp_ℂ] at h
    have := h.mul_right (Complex.exp (I * x * z))
    have hval : ((Real.exp (-(t * x ^ 2)) : ℝ) : ℂ) = Complex.exp ((t : ℂ) * (-(x : ℂ) ^ 2)) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [hval]
    exact this
  rw [← hg.tsum_eq]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k => (t * x ^ 2) ^ k / (k.factorial : ℝ) * Real.exp (|x| * ‖z‖))
    ((Real.summable_pow_div_factorial _).mul_right _) (fun k => ?_)
    (Eventually.of_forall fun d k => norm_dbnTerm_le ht x z d k)
  have hlim := ((tendsto_descFactorial_div_pow (2 * k)).mul
    (tendsto_one_add_div_pow_sub (I * x * z) (2 * k))).const_mul
      ((t : ℂ) ^ k / (k.factorial : ℂ) * (-(x : ℂ) ^ 2) ^ k)
  rw [one_mul] at hlim
  refine (hlim.congr fun d => ?_).trans (le_of_eq ?_)
  · simp only [dbnTerm]; ring
  · simp only [g]; rw [mul_pow]; ring_nf

/-! ## Locally uniform convergence to `H_{−t}` -/

/-- The scaled heat-deformed Jensen polynomial `z ↦ (e^{(t/d²)D²} J_d)(z/d)`. -/
def scaledHeatJensen (t : ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  ((heatOp (t / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)).map (algebraMap ℝ ℂ)).eval
    (z / d)

theorem scaledHeatJensen_eq_integral (t : ℝ) (d : ℕ) (z : ℂ) :
    scaledHeatJensen t d z =
      ∫ x, (riemannKernelReal x : ℂ) * ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k := by
  rw [scaledHeatJensen, eval_heatOp_jensenPoly_XiC]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [kernel_sum_eq_dbnTerm]

/-- The dominating kernel `Φ(x) e^{t x²} e^{R|x|}`. -/
theorem integrable_heatEnvelope {t : ℝ} (ht : 0 ≤ t) (R : ℝ) :
    Integrable (fun x : ℝ => riemannKernelReal x * (Real.exp (t * x ^ 2) * Real.exp (|x| * R))) := by
  have h := (riemannKernel_superExp.mul_exp_sq ht).integrable_mul_exp R
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only; ring_nf

theorem norm_kernel_sum_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) (z : ℂ) (d : ℕ) :
    ‖(riemannKernelReal x : ℂ) * ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k‖ ≤
      riemannKernelReal x * (Real.exp (t * x ^ 2) * Real.exp (|x| * ‖z‖)) := by
  have hΦ := riemannKernel_superExp.nonneg x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦ]
  refine mul_le_mul_of_nonneg_left ?_ hΦ
  calc ‖∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k‖
      ≤ ∑ k ∈ Finset.range (d + 1), (t * x ^ 2) ^ k / (k.factorial : ℝ) *
          Real.exp (|x| * ‖z‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_dbnTerm_le ht x z d k)
    _ = (∑ k ∈ Finset.range (d + 1), (t * x ^ 2) ^ k / (k.factorial : ℝ)) *
          Real.exp (|x| * ‖z‖) := by rw [Finset.sum_mul]
    _ ≤ Real.exp (t * x ^ 2) * Real.exp (|x| * ‖z‖) := by
        gcongr
        exact Real.sum_le_exp_of_nonneg (by positivity) _

theorem continuous_kernel_sum (t : ℝ) (z : ℂ) (d : ℕ) :
    Continuous (fun x : ℝ => (riemannKernelReal x : ℂ) *
      ∑ k ∈ Finset.range (d + 1), dbnTerm t x z d k) := by
  refine (Complex.continuous_ofReal.comp riemannKernel_superExp.continuous).mul
    (continuous_finsetSum _ fun k _ => ?_)
  unfold dbnTerm
  fun_prop

/-- **Pointwise limit.** `(e^{(t/d²)D²} J_d)(z/d) → H_{−t}(z)`. -/
theorem tendsto_scaledHeatJensen {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Tendsto (fun d => scaledHeatJensen t d z) atTop (𝓝 (riemannHeat (-t) z)) := by
  simp_rw [scaledHeatJensen_eq_integral]
  have hlim : riemannHeat (-t) z = ∫ x, (riemannKernelReal x : ℂ) *
      ((Real.exp (-(t * x ^ 2)) : ℂ) * Complex.exp (I * x * z)) := by
    rw [riemannHeat, cosTransform]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    push_cast
    ring_nf
  rw [hlim]
  exact tendsto_integral_of_dominated_convergence _
    (fun d => (continuous_kernel_sum t z d).aestronglyMeasurable) (integrable_heatEnvelope ht ‖z‖)
    (fun d => Eventually.of_forall fun x => norm_kernel_sum_le ht x z d)
    (Eventually.of_forall fun x => (tendsto_sum_dbnTerm ht x z).const_mul _)

/-- Uniform bound on `‖z‖ < R`. -/
theorem norm_scaledHeatJensen_le {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (d : ℕ) {z : ℂ} (hz : ‖z‖ < R) :
    ‖scaledHeatJensen t d z‖ ≤
      ∫ x, riemannKernelReal x * (Real.exp (t * x ^ 2) * Real.exp (|x| * R)) := by
  rw [scaledHeatJensen_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) (integrable_heatEnvelope ht R)
    (Eventually.of_forall fun x => ?_))
  refine (norm_kernel_sum_le ht x z d).trans ?_
  have hΦ := riemannKernel_superExp.nonneg x
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left hz.le (abs_nonneg x))) (Real.exp_pos _).le) hΦ

theorem differentiable_scaledHeatJensen (t : ℝ) (d : ℕ) :
    Differentiable ℂ (scaledHeatJensen t d) := by
  unfold scaledHeatJensen
  have h1 : Differentiable ℂ (fun z : ℂ => z / (d : ℂ)) := differentiable_id.div_const _
  exact (Polynomial.differentiable _).comp h1

/-- **Locally uniform convergence** of the scaled heat-deformed Jensen polynomials to `H_{−t}`. -/
theorem tendstoLocallyUniformly_scaledHeatJensen {t : ℝ} (ht : 0 ≤ t) :
    TendstoLocallyUniformly (scaledHeatJensen t) (riemannHeat (-t)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_ball 0
  set r := max r₀ 1
  have hr : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKr : K ⊆ ball 0 r := hr₀.trans (ball_subset_ball (le_max_left _ _))
  set R := 2 * r + 2
  obtain ⟨G, -, hG⟩ := vitali_tendstoLocallyUniformlyOn (F := scaledHeatJensen t) (c := 0)
    (R := R) (r := r) (z₀ := 0) (Y := ball 0 r)
    (C := ∫ x, riemannKernelReal x * (Real.exp (t * x ^ 2) * Real.exp (|x| * R)))
    hr (by simp only [R]; linarith)
    (fun d => (differentiable_scaledHeatJensen t d).differentiableOn)
    (fun d z hz => norm_scaledHeatJensen_le ht d (by simpa using hz))
    subset_rfl (mem_ball_self hr)
    ((eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds 0 hr)).frequently)
    (fun z _ => ⟨_, tendsto_scaledHeatJensen ht z⟩)
  have hGeq : Set.EqOn G (riemannHeat (-t)) (ball 0 r) := fun z hz =>
    tendsto_nhds_unique (hG.tendsto_at hz) (tendsto_scaledHeatJensen ht z)
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1
    (hG.congr_right hGeq) K hKr hK

/-! ## The finite free de Bruijn–Newman law -/

theorem superExpKernel_mul_exp_neg_sq {t : ℝ} (ht : 0 ≤ t) :
    SuperExpKernel (fun x => riemannKernelReal x * Real.exp (-t * x ^ 2)) where
  continuous := riemannKernel_superExp.continuous.mul (by fun_prop)
  even x := by simp only [even_two.neg_pow, riemannKernel_superExp.even]
  nonneg x := mul_nonneg (riemannKernel_superExp.nonneg x) (Real.exp_pos _).le
  pos_zero := by simpa using riemannKernel_superExp.pos_zero
  decay := by
    obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := riemannKernel_superExp.decay
    refine ⟨A, B, b, c, hA, hB, hb, hc, fun x => ?_⟩
    have h1 : Real.exp (-t * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    calc riemannKernelReal x * Real.exp (-t * x ^ 2) ≤ riemannKernelReal x * 1 :=
          mul_le_mul_of_nonneg_left h1 (riemannKernel_superExp.nonneg x)
      _ ≤ _ := by rw [mul_one]; exact hdec x

/-- Real-rootedness of the scaled backward heat flows along infinitely many degrees puts `H_{−t}`
in the Laguerre–Pólya class. -/
theorem laguerrePolya_riemannHeat_of_frequently_splits {t : ℝ} (ht : 0 ≤ t)
    (h : ∃ᶠ d : ℕ in atTop,
      (heatOp (t / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)).Splits) :
    LaguerrePolya (riemannHeat (-t)) := by
  obtain ⟨φ, hφ, hsplit⟩ := Filter.extraction_of_frequently_atTop h
  set ψ : ℕ → ℕ := fun m => φ (m + 1)
  have hψpos : ∀ m, 0 < ψ m := fun m => lt_of_le_of_lt (Nat.zero_le _) (hφ (Nat.lt_succ_self m))
  have hψ : Tendsto ψ atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  set p : ℕ → ℝ[X] := fun m =>
    (heatOp (t / (ψ m : ℝ) ^ 2) (ψ m) (jensenPoly (realTaylorCoeff XiC) (ψ m))).comp
      (C ((ψ m : ℝ)⁻¹) * X)
  have hpsplit : ∀ m, (p m).Splits := fun m =>
    (splits_iff_comp_splits_of_natDegree_eq_one (by
      rw [natDegree_C_mul_X _ (inv_ne_zero (by exact_mod_cast (hψpos m).ne'))])).1 (hsplit (m + 1))
  have hpeval : ∀ m, polyEvalC (p m) = scaledHeatJensen t (ψ m) := fun m => by
    funext z
    rw [polyEvalC_eq_eval_map, Polynomial.map_comp, eval_comp, scaledHeatJensen]
    congr 1
    simp [div_eq_inv_mul]
  have hconv : TendstoLocallyUniformly (fun m => polyEvalC (p m)) (riemannHeat (-t)) atTop := by
    simp_rw [hpeval]
    intro u hu x
    obtain ⟨s, hs, hev⟩ := tendstoLocallyUniformly_scaledHeatJensen ht u hu x
    exact ⟨s, hs, hψ.eventually hev⟩
  exact ⟨p, hpsplit, hconv⟩

/-- **The finite free de Bruijn–Newman law.** For every `t > 0`, the backward heat flow
`e^{(t/d²)D²} J_d = J_d ⊞_d He_{d,t/d²}` of the degree-`d` Jensen polynomial of `Ξ` fails to be
real-rooted for every sufficiently large `d`. -/
theorem eventually_not_splits_heatOp_jensenPoly_XiC {t : ℝ} (ht : 0 < t) :
    ∀ᶠ d : ℕ in atTop,
      ¬ (heatOp (t / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)).Splits := by
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  have hLP := laguerrePolya_riemannHeat_of_frequently_splits ht.le h
  have h0 : riemannHeat (-t) 0 ≠ 0 := (superExpKernel_mul_exp_neg_sq ht.le).cosTransform_zero_ne
  obtain ⟨z, hz, him⟩ := not_real_rooted_of_neg (t := -t) (by linarith)
  exact him (im_eq_zero_of_laguerrePolya hLP h0 hz)

theorem heatOp_zero {K : Type*} [Field K] (d : ℕ) (p : K[X]) : heatOp (0 : K) d p = p := by
  rw [heatOp_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [zero_pow hk]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

/-- **RH from infinitely many degrees.** The Riemann hypothesis holds as soon as infinitely many
Jensen polynomials of `Ξ` are real-rooted; conversely it makes all of them real-rooted. -/
theorem riemannHypothesis_iff_frequently_splits_jensenPoly_XiC :
    RiemannHypothesis ↔ ∃ᶠ d : ℕ in atTop, (jensenPoly (realTaylorCoeff XiC) d).Splits := by
  constructor
  · intro hRH
    exact Filter.Frequently.of_forall fun d => splits_jensenPoly_realTaylorCoeff
      (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH) (fun z => XiC_conj z) d
  · intro h
    have h' : ∃ᶠ d : ℕ in atTop,
        (heatOp ((0 : ℝ) / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)).Splits := by
      simpa [zero_div, heatOp_zero] using h
    have hLP := laguerrePolya_riemannHeat_of_frequently_splits le_rfl h'
    have h0 : riemannHeat (-0) 0 ≠ 0 := (superExpKernel_mul_exp_neg_sq le_rfl).cosTransform_zero_ne
    refine riemannHypothesis_iff_riemannHeat_zero_real.2 fun z hz => ?_
    rw [← neg_zero] at hz
    exact im_eq_zero_of_laguerrePolya hLP h0 hz

/-- **No Gaussian component at the de Bruijn–Newman scale.** For every `t > 0` and all large `d`,
the Jensen polynomial of `Ξ` convolved with the backward Hermite polynomial `He_{d,t/d²}` is not
real-rooted. -/
theorem eventually_not_splits_ffConv_hermite_jensenPoly_XiC {t : ℝ} (ht : 0 < t) :
    ∀ᶠ d : ℕ in atTop, ¬ (ffConv d (jensenPoly (realTaylorCoeff XiC) d)
      (hermiteFF (t / (d : ℝ) ^ 2) d)).Splits := by
  filter_upwards [eventually_not_splits_heatOp_jensenPoly_XiC ht] with d hd
  rwa [← heatOp_eq_ffConv (natDegree_jensenPoly_le _ _)]

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_not_splits_heatOp_jensenPoly_XiC
#print axioms FiniteFreeProbability.eventually_not_splits_ffConv_hermite_jensenPoly_XiC
#print axioms FiniteFreeProbability.riemannHypothesis_iff_frequently_splits_jensenPoly_XiC
