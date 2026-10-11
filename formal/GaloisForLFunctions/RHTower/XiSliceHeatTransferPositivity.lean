import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary
import GaloisForLFunctions.RHTower.RiemannHeatSliceTaylorPositivity
import GaloisForLFunctions.RHTower.ScalarPowerSeriesUniqueness

/-!
# Heat transfer of slice positivity back to `Ξ`

Let `Φ` be Riemann's kernel, `H_λ(z) = ∫ Φ(u) e^{λu²} e^{izu} du` and `S_λ(t, x) = H_λ(t − ix) H_λ(t + ix)`,
so `S_0` is the slice `ξ(½+x+it) ξ(½−x+it)`.  For a kernel `g` the slice of its transform is the
double integral `∫∫ g(u) g(v) e^{it(u+v)} e^{x(u−v)}`, so its Taylor coefficients at a real point
`x₀` are the moments
`M_n(g, x₀, t) = ∫∫ g(u) g(v) e^{x₀(u−v)} (u − v)ⁿ/n! e^{it(u+v)}`
(`kernelSliceMoment`, `kernelSliceMoment_eq_iteratedDeriv`).

**Transfer identity** (`integral_heightGaussian_mul_kernelSliceMoment_heat`).  Average the slice
coefficients of `H_λ` over heights with the Gaussian of variance `λ` (`σ² = 1/(2λ)`).  Since
`e^{λ(u²+v²)} e^{−λ(u+v)²/2} = e^{λ(u−v)²/2}`,

  `∫ G(t − t′) M_n(Φe^{λu²}, x₀, t′) dt′ = T_n(λ, x₀, t)
      := ∫∫ Φ(u) Φ(v) e^{λ(u−v)²/2} e^{x₀(u−v)} (u − v)ⁿ/n! e^{it(u+v)}`,

and expanding `e^{λ(u−v)²/2}` (`hasSum_xiSliceHeatTransfer_kernelSliceMoment`),

  `T_n(λ, x₀, t) = Σ_k (λ/2)^k/k! · (n+2k)!/n! · S_0^{(n+2k)}(t, x₀)/(n+2k)!`.

So `T_n(λ, x₀, t)` is the `n`-th Taylor coefficient at `x₀` of `e^{(λ/2)∂_x²} S_0(t, ·)`: the Gaussian
height average of the `λ`-slices is the slice of `Ξ` itself, heated in the slice variable for time
`λ/2`.

**The heat–abscissa trade-off** (`xiSliceHeatTransfer_nonneg_debruijn`).  For `λ > 0` every zero of
`H_λ` satisfies `(Im ζ)² ≤ max(¼ − 2λ, 0)` (de Bruijn).  By the hyperbola criterion
(`nonnegTaylorAtZero_slice_shift_of_hyperbola`) every slice of `H_λ` is then absolutely monotone
from `x₀ = √max(¼ − 2λ, 0)`, and so is their average.  Hence for every height `t` the heated slice
`e^{(λ/2)∂_x²} S_0(t, ·)` has nonnegative Taylor coefficients at `x₀ = √max(¼ − 2λ, 0)`.  At `λ → 0`
this is the unconditional absolute monotonicity of `|ξ(σ + it)|²` on `σ ≥ 1`; at `λ ≥ 1/8` it is
positivity at the centre (`xiSliceHeatTransfer_nonneg`):

  `Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t) ≥ 0`   (`λ ≥ 1/8`, every height `t`).

The trade-off curve `x₀² + 2λ = ¼` is de Bruijn's strip bound transported to the slices.  It
holds pointwise in the height: the price of removing the Gaussian height average of the Husimi
identity is the heat factor `e^{(λ/2)∂_x²}` in the slice variable.

**The Riemann hypothesis** (`riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg`).  RH holds
iff `T_n(λ, 0, t) ≥ 0` for every `λ > 0`, height `t` and order `n`.  As `λ → 0⁺`,
`T_n(λ, 0, t) → c_n(t)`.  Forward heat in `x` preserves nonnegative coefficients, so the admissible
`λ` at the centre form an interval `[λ_WD, ∞)` with `λ_WD ≤ 1/8`, and RH is `λ_WD ≤ 0`.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-! ## The slice of a kernel transform as a double integral -/

section Abstract

variable {g : ℝ → ℝ}

/-- The horizontal slice of `T g` as a double integral. -/
theorem cosTransform_slice_eq_integral (g : ℝ → ℝ) (t : ℝ) (x : ℂ) :
    cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x) =
      ∫ p : ℝ × ℝ, ((g p.1 * g p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + x * (p.1 - p.2)) := by
  unfold cosTransform
  rw [← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have e : I * ((t : ℂ) - I * x) * p.1 + I * ((t : ℂ) + I * x) * p.2 =
      I * t * (p.1 + p.2) + x * (p.1 - p.2) := by
    ring_nf
    rw [I_sq]
    ring
  show (g p.1 : ℂ) * cexp (I * ((t : ℂ) - I * x) * p.1) *
      ((g p.2 : ℂ) * cexp (I * ((t : ℂ) + I * x) * p.2)) =
    ((g p.1 * g p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + x * (p.1 - p.2))
  rw [← e, Complex.exp_add]
  push_cast
  ring

/-- The slice moments at `x₀`, `M_n(g, x₀, t) = ∫∫ g(u) g(v) e^{x₀(u−v)} (u − v)ⁿ/n! e^{it(u+v)}`. -/
def kernelSliceMoment (g : ℝ → ℝ) (x₀ t : ℝ) (n : ℕ) : ℂ :=
  ∫ p : ℝ × ℝ, ((g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) :
    ℝ) : ℂ) * cexp (I * t * (p.1 + p.2))

theorem norm_cexp_I_mul_ofReal_add (t a b : ℝ) : ‖cexp (I * t * ((a : ℂ) + b))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- `e^{c|u − v|} ≤ e^{c|u|} e^{c|v|}`. -/
theorem exp_mul_abs_sub_le {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    Real.exp (c * |u - v|) ≤ Real.exp (c * |u|) * Real.exp (c * |v|) := by
  rw [← Real.exp_add, ← mul_add]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_sub _ _) hc)

/-- `e^{x₀(u−v)} e^{c|u−v|} ≤ e^{(|x₀|+c)|u|} e^{(|x₀|+c)|v|}`. -/
theorem exp_mul_sub_mul_exp_le (x₀ : ℝ) {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    Real.exp (x₀ * (u - v)) * Real.exp (c * |u - v|) ≤
      Real.exp ((|x₀| + c) * |u|) * Real.exp ((|x₀| + c) * |v|) := by
  rw [← Real.exp_add]
  refine (Real.exp_le_exp.mpr ?_).trans (exp_mul_abs_sub_le (by positivity) u v)
  have h := neg_abs_le (x₀ * (u - v))
  have h' : x₀ * (u - v) ≤ |x₀| * |u - v| := by
    rw [← abs_mul]; exact le_abs_self _
  nlinarith

/-- `|u − v|ⁿ/n! · e^{x₀(u−v)} ≤ e^{(|x₀|+1)|u|} e^{(|x₀|+1)|v|}`. -/
theorem abs_sub_pow_div_mul_exp_le (x₀ u v : ℝ) (n : ℕ) :
    |u - v| ^ n / n.factorial * Real.exp (x₀ * (u - v)) ≤
      Real.exp ((|x₀| + 1) * |u|) * Real.exp ((|x₀| + 1) * |v|) := by
  have h1 := Real.pow_div_factorial_le_exp _ (abs_nonneg (u - v)) n
  have h2 := exp_mul_sub_mul_exp_le x₀ zero_le_one u v
  rw [one_mul] at h2
  calc |u - v| ^ n / n.factorial * Real.exp (x₀ * (u - v))
      ≤ Real.exp |u - v| * Real.exp (x₀ * (u - v)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (x₀ * (u - v)) * Real.exp |u - v| := mul_comm _ _
    _ ≤ _ := h2

/-- The product majorant `g(u) e^{c|u|} g(v) e^{c|v|}` is integrable. -/
theorem integrable_prod_majorant (hg : SuperExpKernel g) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => g p.1 * Real.exp (c * |p.1|) * (g p.2 * Real.exp (c * |p.2|))) :=
  (hg.integrable_mul_exp c).mul_prod (hg.integrable_mul_exp c)

/-- **The moment series of the slice at `x₀`.**  `S(t, x₀ + y) = Σ_n M_n(g, x₀, t) yⁿ` for every
complex `y`. -/
theorem hasSum_kernelSliceMoment (hg : SuperExpKernel g) (x₀ t : ℝ) (y : ℂ) :
    HasSum (fun n => kernelSliceMoment g x₀ t n * y ^ n)
      (cosTransform g ((t : ℂ) - I * (x₀ + y)) * cosTransform g ((t : ℂ) + I * (x₀ + y))) := by
  rw [cosTransform_slice_eq_integral]
  set F : ℕ → ℝ × ℝ → ℂ := fun n p =>
    ((g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
      cexp (I * t * (p.1 + p.2)) * y ^ n with hF
  set c : ℝ := |x₀| + ‖y‖ with hc
  set D : ℝ × ℝ → ℝ := fun p =>
    g p.1 * Real.exp (c * |p.1|) * (g p.2 * Real.exp (c * |p.2|)) with hD
  have hDi : Integrable D := integrable_prod_majorant hg c
  have hg0 := hg.nonneg
  have hnormF : ∀ n p, ‖F n p‖ = g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) *
      (|p.1 - p.2| ^ n / n.factorial) * ‖y‖ ^ n := by
    intro n p
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, norm_pow, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hg0 _),
      abs_of_pos (Real.exp_pos _)]
  have hbound : ∀ N : ℕ, ∀ p : ℝ × ℝ, ∑ n ∈ Finset.range N, ‖F n p‖ ≤ D p := by
    intro N p
    simp only [hnormF]
    have e : ∑ n ∈ Finset.range N, g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) *
        (|p.1 - p.2| ^ n / n.factorial) * ‖y‖ ^ n =
        g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) *
          ∑ n ∈ Finset.range N, (‖y‖ * |p.1 - p.2|) ^ n / n.factorial := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow]
      ring
    rw [e]
    have h1 := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ ‖y‖ * |p.1 - p.2|) N
    have h2 := exp_mul_sub_mul_exp_le x₀ (norm_nonneg y) p.1 p.2
    have hgg : 0 ≤ g p.1 * g p.2 := mul_nonneg (hg0 _) (hg0 _)
    calc g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) *
          ∑ n ∈ Finset.range N, (‖y‖ * |p.1 - p.2|) ^ n / n.factorial
        ≤ g p.1 * g p.2 * (Real.exp (x₀ * (p.1 - p.2)) * Real.exp (‖y‖ * |p.1 - p.2|)) := by
          rw [mul_assoc (g p.1 * g p.2)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) hgg
      _ ≤ g p.1 * g p.2 * (Real.exp (c * |p.1|) * Real.exp (c * |p.2|)) :=
          mul_le_mul_of_nonneg_left h2 hgg
      _ = D p := by simp only [hD]; ring
  have hmeas : ∀ n, AEStronglyMeasurable (F n) := by
    intro n
    refine Continuous.aestronglyMeasurable ?_
    have := hg.continuous
    simp only [hF]
    fun_prop
  have hint : ∀ n, Integrable (F n) := by
    intro n
    refine hDi.mono' (hmeas n) (Eventually.of_forall fun p => ?_)
    have := hbound (n + 1) p
    rw [Finset.sum_range_succ] at this
    have hnn : 0 ≤ ∑ i ∈ Finset.range n, ‖F i p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hsum : Summable (fun n => ∫ p, ‖F n p‖) := by
    refine summable_of_sum_range_le (c := ∫ p, D p)
      (fun n => integral_nonneg fun p => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ (fun n _ => (hint n).norm)]
    exact integral_mono (integrable_finsetSum _ fun n _ => (hint n).norm) hDi (hbound N)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' n, F n p =
      ((g p.1 * g p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + ((x₀ : ℂ) + y) * (p.1 - p.2)) := by
    intro p
    have hexp := NormedSpace.expSeries_div_hasSum_exp (y * ((p.1 - p.2 : ℝ) : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at hexp
    simp only [mul_pow] at hexp
    have hF' : (fun n => F n p) = fun n => (((g p.1 * g p.2 : ℝ) : ℂ) *
        ((Real.exp (x₀ * (p.1 - p.2)) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2))) *
        (y ^ n * ((p.1 - p.2 : ℝ) : ℂ) ^ n / n.factorial) := by
      funext n
      simp only [hF]
      push_cast
      ring
    rw [hF', (hexp.mul_left _).tsum_eq, Complex.ofReal_exp, mul_assoc, mul_assoc,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [htsum] at h
  refine h.congr_fun fun n => ?_
  simp only [hF, kernelSliceMoment]
  rw [integral_mul_const]

/-- **The slice moments are the Taylor coefficients at `x₀`.** -/
theorem kernelSliceMoment_eq_iteratedDeriv (hg : SuperExpKernel g) (x₀ t : ℝ) (n : ℕ) :
    kernelSliceMoment g x₀ t n = iteratedDeriv n
      (fun x => cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)) x₀ /
        n.factorial := by
  rw [PowerSeriesUniqueness.coeff_eq_iteratedDeriv_div_factorial_of_hasSum one_pos
    (fun w _ => hasSum_kernelSliceMoment hg x₀ t w) n]
  congr 1
  have h := congrFun (iteratedDeriv_comp_const_add n
    (fun x => cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)) (x₀ : ℂ)) 0
  simp only [add_zero] at h
  exact h

/-- **Gaussian height average of the slice moments.**
`∫ G_σ(t − t′) M_n(g, x₀, t′) dt′ = ∫∫ g(u) g(v) e^{x₀(u−v)} (u − v)ⁿ/n! e^{it(u+v) − (u+v)²/(4σ²)}`. -/
theorem integral_heightGaussian_mul_kernelSliceMoment (hg : SuperExpKernel g) {σ : ℝ}
    (hσ : 0 < σ) (x₀ t : ℝ) (n : ℕ) :
    ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) * kernelSliceMoment g x₀ t' n =
      ∫ p : ℝ × ℝ, ((g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
        cexp (I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2)) := by
  simp_rw [kernelSliceMoment, ← integral_const_mul]
  rw [integral_integral_swap]
  · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have e : ∀ t' : ℝ, (heightGaussian σ t t' : ℂ) *
        (((g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) :
          ℂ) * cexp (I * t' * (p.1 + p.2))) =
        ((g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) :
          ℂ) * (((σ / Real.sqrt Real.pi * Real.exp (-(σ ^ 2 * (t - t') ^ 2)) : ℝ) : ℂ) *
            cexp (-(I * t' * ((-(p.1 + p.2) : ℝ) : ℂ)))) := by
      intro t'
      have harg : -(I * (t' : ℂ) * ((-(p.1 + p.2) : ℝ) : ℂ)) = I * t' * (p.1 + p.2) := by
        push_cast; ring
      rw [harg]
      simp only [heightGaussian]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_heightGaussian_mul_cexp hσ]
    congr 2
    push_cast
    ring
  · have hG := integrable_heightGaussian hσ t
    have hM := integrable_prod_majorant hg (|x₀| + 1)
    refine (hG.mul_prod hM).mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have := hg.continuous
      unfold heightGaussian
      fun_prop
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_cexp_I_mul_ofReal_add, mul_one]
      have hGz : 0 ≤ heightGaussian σ t z.1 := by unfold heightGaussian; positivity
      have hg1 := hg.nonneg z.2.1
      have hg2 := hg.nonneg z.2.2
      rw [abs_of_nonneg hGz, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_pos (Real.exp_pos _),
        abs_div, abs_pow, Nat.abs_cast]
      refine mul_le_mul_of_nonneg_left ?_ hGz
      have h := abs_sub_pow_div_mul_exp_le x₀ z.2.1 z.2.2 n
      calc g z.2.1 * g z.2.2 * Real.exp (x₀ * (z.2.1 - z.2.2)) *
            (|z.2.1 - z.2.2| ^ n / n.factorial)
          = g z.2.1 * g z.2.2 *
              (|z.2.1 - z.2.2| ^ n / n.factorial * Real.exp (x₀ * (z.2.1 - z.2.2))) := by ring
        _ ≤ g z.2.1 * g z.2.2 * (Real.exp ((|x₀| + 1) * |z.2.1|) *
              Real.exp ((|x₀| + 1) * |z.2.2|)) := mul_le_mul_of_nonneg_left h (mul_nonneg hg1 hg2)
        _ = _ := by ring

end Abstract

/-! ## The heat transfer -/

/-- `T_n(λ, x₀, t) = ∫∫ Φ(u) Φ(v) e^{λ(u−v)²/2} e^{x₀(u−v)} (u − v)ⁿ/n! e^{it(u+v)}`, the `n`-th
Taylor coefficient at `x₀` of the slice of `Ξ` at height `t` heated for time `λ/2` in the slice
variable. -/
def xiSliceHeatTransfer (lam x₀ t : ℝ) (n : ℕ) : ℂ :=
  ∫ p : ℝ × ℝ, ((riemannKernelReal p.1 * riemannKernelReal p.2 *
    Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
      ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2))

/-- **The transfer identity.**  The Gaussian height average (variance `λ`) of the slice moments of
`H_λ` at `x₀` is `T_n(λ, x₀, t)`. -/
theorem integral_heightGaussian_mul_kernelSliceMoment_heat {lam : ℝ} (hlam : 0 < lam)
    (x₀ t : ℝ) (n : ℕ) :
    ∫ t' : ℝ, (heightGaussian (Real.sqrt (1 / (2 * lam))) t t' : ℂ) *
      kernelSliceMoment (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) x₀ t' n =
        xiSliceHeatTransfer lam x₀ t n := by
  set σ := Real.sqrt (1 / (2 * lam)) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : σ ^ 2 = 1 / (2 * lam) := Real.sq_sqrt (by positivity)
  rw [integral_heightGaussian_mul_kernelSliceMoment (riemannKernel_superExp.mul_exp_sq hlam.le) hσ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  have hlamc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have hσc : (σ : ℂ) ^ 2 = ((1 / (2 * lam) : ℝ) : ℂ) := by rw [← Complex.ofReal_pow, hσ2]
  have harg : I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * (σ : ℂ) ^ 2) =
      I * t * ((p.1 : ℂ) + p.2) + ((-(lam * (p.1 + p.2) ^ 2 / 2) : ℝ) : ℂ) := by
    rw [hσc]
    push_cast
    field_simp
    ring
  have hexp : Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) *
      Real.exp (-(lam * (p.1 + p.2) ^ 2 / 2)) = Real.exp (lam * (p.1 - p.2) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hreal : riemannKernelReal p.1 * Real.exp (lam * p.1 ^ 2) *
      (riemannKernelReal p.2 * Real.exp (lam * p.2 ^ 2)) * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) * Real.exp (-(lam * (p.1 + p.2) ^ 2 / 2)) =
      riemannKernelReal p.1 * riemannKernelReal p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
        Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) := by
    rw [← hexp]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  calc ((riemannKernelReal p.1 * Real.exp (lam * p.1 ^ 2) *
          (riemannKernelReal p.2 * Real.exp (lam * p.2 ^ 2)) * Real.exp (x₀ * (p.1 - p.2)) *
            ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * (cexp (I * t * ((p.1 : ℂ) + p.2)) *
          ((Real.exp (-(lam * (p.1 + p.2) ^ 2 / 2)) : ℝ) : ℂ))
      = ((riemannKernelReal p.1 * Real.exp (lam * p.1 ^ 2) *
          (riemannKernelReal p.2 * Real.exp (lam * p.2 ^ 2)) * Real.exp (x₀ * (p.1 - p.2)) *
            ((p.1 - p.2) ^ n / n.factorial) * Real.exp (-(lam * (p.1 + p.2) ^ 2 / 2)) : ℝ) : ℂ) *
          cexp (I * t * ((p.1 : ℂ) + p.2)) := by
        push_cast; ring
    _ = _ := by rw [hreal]

/-- **The transfer series.**  `T_n(λ, x₀, t) = Σ_k (λ/2)^k/k! · (n+2k)!/n! · M_{n+2k}(Φ, x₀, t)`. -/
theorem hasSum_xiSliceHeatTransfer_kernelSliceMoment {lam : ℝ} (hlam : 0 ≤ lam) (x₀ t : ℝ)
    (n : ℕ) :
    HasSum (fun k : ℕ => (((lam / 2) ^ k / k.factorial *
        ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) *
      kernelSliceMoment riemannKernelReal x₀ t (n + 2 * k)) (xiSliceHeatTransfer lam x₀ t n) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℕ → ℝ × ℝ → ℂ := fun k p =>
    ((Φ p.1 * Φ p.2 * ((lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
      Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
      cexp (I * t * (p.1 + p.2)) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (lam * p.1 ^ 2) * Real.exp ((|x₀| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (lam * p.2 ^ 2) * Real.exp ((|x₀| + 1) * |p.2|)) with hD
  have hDi : Integrable D := by
    have := integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hlam) (|x₀| + 1)
    exact this
  have hnormF : ∀ k p, ‖F k p‖ = Φ p.1 * Φ p.2 *
      ((lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
        (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) := by
    intro k p
    have hq : 0 ≤ lam * (p.1 - p.2) ^ 2 / 2 := by positivity
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _), abs_of_nonneg hq,
      abs_of_pos (Real.exp_pos _)]
    ring
  have hexpsq : ∀ p : ℝ × ℝ, Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
      Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) := by
    intro p
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (p.1 + p.2)]
  have hbound : ∀ N : ℕ, ∀ p : ℝ × ℝ, ∑ k ∈ Finset.range N, ‖F k p‖ ≤ D p := by
    intro N p
    simp only [hnormF]
    have hq : 0 ≤ lam * (p.1 - p.2) ^ 2 / 2 := by positivity
    have e : ∑ k ∈ Finset.range N, Φ p.1 * Φ p.2 *
        ((lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) =
        Φ p.1 * Φ p.2 * (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) *
          ∑ k ∈ Finset.range N, (lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e]
    have h1 := Real.sum_le_exp_of_nonneg hq N
    have h2 := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 n
    have hΦΦ : 0 ≤ Φ p.1 * Φ p.2 := mul_nonneg (hΦ0 _) (hΦ0 _)
    calc Φ p.1 * Φ p.2 * (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) *
          ∑ k ∈ Finset.range N, (lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial
        ≤ Φ p.1 * Φ p.2 * (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) *
            (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hΦΦ) (h1.trans (hexpsq p))
            (Finset.sum_nonneg fun k _ => by positivity) (by positivity)
      _ = D p := by simp only [hD]; ring
  have hmeas : ∀ k, AEStronglyMeasurable (F k) := by
    intro k
    refine Continuous.aestronglyMeasurable ?_
    have := continuous_riemannKernelReal
    simp only [hF, hΦ]
    fun_prop
  have hint : ∀ k, Integrable (F k) := by
    intro k
    refine hDi.mono' (hmeas k) (Eventually.of_forall fun p => ?_)
    have := hbound (k + 1) p
    rw [Finset.sum_range_succ] at this
    have hnn : 0 ≤ ∑ i ∈ Finset.range k, ‖F i p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hsum : Summable (fun k => ∫ p, ‖F k p‖) := by
    refine summable_of_sum_range_le (c := ∫ p, D p)
      (fun k => integral_nonneg fun p => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ (fun k _ => (hint k).norm)]
    exact integral_mono (integrable_finsetSum _ fun k _ => (hint k).norm) hDi (hbound N)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' k, F k p =
      ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) := by
    intro p
    have hexp := NormedSpace.expSeries_div_hasSum_exp (lam * (p.1 - p.2) ^ 2 / 2)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    have hR := (hexp.mul_left (Φ p.1 * Φ p.2)).mul_right
      (Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial))
    have hC := (Complex.hasSum_ofReal.mpr hR).mul_right (cexp (I * t * (p.1 + p.2)))
    refine (hC.congr_fun fun k => ?_).tsum_eq.trans ?_
    · simp only [hF]
      push_cast
      ring
    · push_cast
      ring
  simp_rw [htsum] at h
  refine h.congr_fun fun k => ?_
  simp only [hF, kernelSliceMoment]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfac2 : (((n + 2 * k).factorial : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hkfac : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hreal : Φ p.1 * Φ p.2 * ((lam * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
      Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) =
      (lam / 2) ^ k / k.factorial * ((n + 2 * k).factorial / n.factorial) *
        (Φ p.1 * Φ p.2 * Real.exp (x₀ * (p.1 - p.2)) *
          ((p.1 - p.2) ^ (n + 2 * k) / (n + 2 * k).factorial)) := by
    simp only [pow_add, pow_mul, div_pow, mul_pow]
    field_simp
  beta_reduce
  rw [hreal]
  push_cast
  ring

/-- The slice of `T Φ` is the slice of `Ξ`. -/
theorem cosTransform_riemannKernel_slice (t : ℝ) :
    (fun x => cosTransform riemannKernelReal ((t : ℂ) - I * x) *
      cosTransform riemannKernelReal ((t : ℂ) + I * x)) = xiSliceProduct t := by
  have hk : (fun x => riemannKernelReal x * Real.exp (0 * x ^ 2)) = riemannKernelReal := by
    funext x; simp
  funext x
  have hX : XiC = riemannHeat 0 := by
    funext z; rw [riemannHeat_zero, XiC, mul_comm I z]
  rw [xiSliceProduct_eq_XiC, hX]
  simp only [riemannHeat, hk]

/-- The slice moments of `Φ` at `x₀` are the Taylor coefficients of the slice of `Ξ` at `x₀`. -/
theorem kernelSliceMoment_riemannKernel_eq (x₀ t : ℝ) (n : ℕ) :
    kernelSliceMoment riemannKernelReal x₀ t n =
      iteratedDeriv n (xiSliceProduct t) x₀ / n.factorial := by
  rw [kernelSliceMoment_eq_iteratedDeriv riemannKernel_superExp, cosTransform_riemannKernel_slice]

/-- At the centre the slice moments of `Φ` are the slice coefficients of `Ξ`. -/
theorem kernelSliceMoment_riemannKernel_eq_xiSliceCoeff (t : ℝ) (n : ℕ) :
    kernelSliceMoment riemannKernelReal 0 t n = xiSliceCoeff t n := by
  rw [kernelSliceMoment_riemannKernel_eq, xiSliceCoeff, div_eq_inv_mul, Complex.ofReal_zero]

/-- The slice moments of `Φ e^{λu²}` at `x₀` are the Taylor coefficients at `x₀` of the slice of
`H_λ`. -/
theorem kernelSliceMoment_heat_eq {lam : ℝ} (hlam : 0 ≤ lam) (x₀ t : ℝ) (n : ℕ) :
    kernelSliceMoment (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) x₀ t n =
      iteratedDeriv n (fun x => riemannHeat lam ((t : ℂ) - I * x) *
        riemannHeat lam ((t : ℂ) + I * x)) x₀ / n.factorial :=
  kernelSliceMoment_eq_iteratedDeriv (riemannKernel_superExp.mul_exp_sq hlam) x₀ t n

/-- Slice moments of `H_λ` at `x₀ ≥ 0` are nonnegative at every height when every zero of `H_λ`
satisfies `(Im ζ)² ≤ x₀²`. -/
theorem kernelSliceMoment_heat_nonneg {lam x₀ : ℝ} (hlam : 0 ≤ lam) (hx₀ : 0 ≤ x₀)
    (hstrip : ∀ ζ, riemannHeat lam ζ = 0 → ζ.im ^ 2 ≤ x₀ ^ 2) (t : ℝ) (n : ℕ) :
    0 ≤ kernelSliceMoment (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) x₀ t n := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq hlam).exists_envelope
  have hNT := nonnegTaylorAtZero_slice_shift_of_hyperbola hC (riemannHeat_analytic hlam)
    (riemannHeat_zero_ne hlam) (riemannHeat_neg hlam) (riemannHeat_conj hlam) hbound
    (t := t) hx₀ fun ζ hζ => by nlinarith [hstrip ζ hζ, sq_nonneg (ζ.re - t)]
  have hd := congrFun (iteratedDeriv_comp_const_add n
    (fun x => riemannHeat lam ((t : ℂ) - I * x) * riemannHeat lam ((t : ℂ) + I * x)) (x₀ : ℂ)) 0
  simp only [add_zero] at hd
  rw [kernelSliceMoment_heat_eq hlam, ← hd, div_eq_mul_inv,
    show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
  exact mul_nonneg (hNT.2 n) (Complex.zero_le_real.mpr (by positivity))

/-- **Positivity of the transfer under a strip bound for the flow.** -/
theorem xiSliceHeatTransfer_nonneg_of_strip {lam x₀ : ℝ} (hlam : 0 < lam) (hx₀ : 0 ≤ x₀)
    (hstrip : ∀ ζ, riemannHeat lam ζ = 0 → ζ.im ^ 2 ≤ x₀ ^ 2) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam x₀ t n := by
  rw [← integral_heightGaussian_mul_kernelSliceMoment_heat hlam]
  set M : ℝ → ℂ := fun t' =>
    kernelSliceMoment (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) x₀ t' n with hM
  have hM0 : ∀ t', 0 ≤ M t' := fun t' => kernelSliceMoment_heat_nonneg hlam.le hx₀ hstrip t' n
  have hMr : ∀ t', M t' = (((M t').re : ℝ) : ℂ) := fun t' =>
    Complex.ext (by simp) (by simp [((Complex.nonneg_iff.mp (hM0 t')).2).symm])
  have e : (fun t' : ℝ => (heightGaussian (Real.sqrt (1 / (2 * lam))) t t' : ℂ) * M t') =
      fun t' => ((heightGaussian (Real.sqrt (1 / (2 * lam))) t t' * (M t').re : ℝ) : ℂ) := by
    funext t'
    rw [hMr t']
    push_cast
    simp
  rw [e, integral_complex_ofReal]
  refine Complex.zero_le_real.mpr (integral_nonneg fun t' => ?_)
  have hG : 0 ≤ heightGaussian (Real.sqrt (1 / (2 * lam))) t t' := by
    unfold heightGaussian; positivity
  exact mul_nonneg hG (Complex.nonneg_iff.mp (hM0 t')).1

/-- **The heat–abscissa trade-off.**  For every `λ > 0` and every height `t`, the heated slice
`e^{(λ/2)∂_x²} S_0(t, ·)` has nonnegative Taylor coefficients at `x₀ = √max(¼ − 2λ, 0)`:
`Σ_k (λ/2)^k/k! · (n+2k)!/n! · S_0^{(n+2k)}(t, x₀)/(n+2k)! = T_n(λ, x₀, t) ≥ 0`. -/
theorem xiSliceHeatTransfer_nonneg_debruijn {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => (((lam / 2) ^ k / k.factorial *
        ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) *
        (iteratedDeriv (n + 2 * k) (xiSliceProduct t) (Real.sqrt (max (1 / 4 - 2 * lam) 0)) /
          (n + 2 * k).factorial))
      (xiSliceHeatTransfer lam (Real.sqrt (max (1 / 4 - 2 * lam) 0)) t n) ∧
    0 ≤ xiSliceHeatTransfer lam (Real.sqrt (max (1 / 4 - 2 * lam) 0)) t n := by
  set x₀ := Real.sqrt (max (1 / 4 - 2 * lam) 0) with hx₀def
  have hx₀ : 0 ≤ x₀ := Real.sqrt_nonneg _
  have hx₀2 : x₀ ^ 2 = max (1 / 4 - 2 * lam) 0 := Real.sq_sqrt (le_max_right _ _)
  refine ⟨?_, xiSliceHeatTransfer_nonneg_of_strip hlam hx₀ (fun ζ hζ => by
    rw [hx₀2]; exact riemannHeat_zeros_im_sq_le hlam hζ) t n⟩
  have h := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam.le x₀ t n
  simpa only [kernelSliceMoment_riemannKernel_eq] using h

/-- **Unconditional heated slice positivity at every height.**  For `λ ≥ 1/8`, every height `t`
and every `n`, `Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t) = T_n(λ, 0, t) ≥ 0`. -/
theorem xiSliceHeatTransfer_nonneg {lam : ℝ} (hlam : 1 / 8 ≤ lam) (t : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => (((lam / 2) ^ k / k.factorial *
        ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) * xiSliceCoeff t (n + 2 * k))
      (xiSliceHeatTransfer lam 0 t n) ∧ 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  refine ⟨?_, xiSliceHeatTransfer_nonneg_of_strip (by linarith) le_rfl (fun ζ hζ => by
    rw [riemannHeat_zeros_real hlam hζ]) t n⟩
  have h := hasSum_xiSliceHeatTransfer_kernelSliceMoment (by linarith : (0 : ℝ) ≤ lam) 0 t n
  simpa only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] using h

/-- **The transfer returns the slice coefficient as `λ → 0⁺`.** -/
theorem tendsto_xiSliceHeatTransfer_zero (t : ℝ) (n : ℕ) :
    Tendsto (fun lam => xiSliceHeatTransfer lam 0 t n) (𝓝[>] 0) (𝓝 (xiSliceCoeff t n)) := by
  rw [← kernelSliceMoment_riemannKernel_eq_xiSliceCoeff]
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set F : ℝ → ℝ × ℝ → ℂ := fun lam p =>
    ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (0 * (p.1 - p.2)) *
      ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) with hF
  set bound : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (1 * p.1 ^ 2) * Real.exp ((|0| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (1 * p.2 ^ 2) * Real.exp ((|0| + 1) * |p.2|)) with hbound
  have hbi : Integrable bound :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq zero_le_one) (|0| + 1)
  have hlim : ∀ p : ℝ × ℝ, Tendsto (fun lam => F lam p) (𝓝[>] 0) (𝓝 (F 0 p)) := by
    intro p
    have hc : Continuous (fun lam : ℝ => F lam p) := by
      simp only [hF]
      fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hF0 : (fun p => F 0 p) = fun p : ℝ × ℝ =>
      ((Φ p.1 * Φ p.2 * Real.exp (0 * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
        cexp (I * t * (p.1 + p.2)) := by
    funext p
    simp only [hF, zero_mul, zero_div, Real.exp_zero, mul_one]
  have h := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun lam => by
      refine Continuous.aestronglyMeasurable ?_
      have := continuous_riemannKernelReal
      simp only [hF, hΦ]
      fun_prop)
    (by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with lam hlam
      refine Eventually.of_forall fun p => ?_
      have hg1 := hΦ0 p.1
      have hg2 := hΦ0 p.2
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
        mul_one, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_pos (Real.exp_pos _),
        abs_div, abs_pow, Nat.abs_cast]
      have h1 := abs_sub_pow_div_mul_exp_le 0 p.1 p.2 n
      have h2 : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
          Real.exp (1 * p.1 ^ 2) * Real.exp (1 * p.2 ^ 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hb : 0 ≤ (p.1 - p.2) ^ 2 := sq_nonneg _
        nlinarith [sq_nonneg (p.1 + p.2), hlam.1, hlam.2]
      calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (0 * (p.1 - p.2)) *
            (|p.1 - p.2| ^ n / n.factorial)
          = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
              (|p.1 - p.2| ^ n / n.factorial * Real.exp (0 * (p.1 - p.2))) := by ring
        _ ≤ Φ p.1 * Φ p.2 * (Real.exp (1 * p.1 ^ 2) * Real.exp (1 * p.2 ^ 2)) *
              (Real.exp ((|0| + 1) * |p.1|) * Real.exp ((|0| + 1) * |p.2|)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (mul_nonneg hg1 hg2)) h1
              (by positivity) (by positivity)
        _ = bound p := by simp only [hbound]; ring)
    hbi (Eventually.of_forall hlim)
  rw [hF0] at h
  exact h

/-- **The Riemann hypothesis as heated slice positivity.**  RH holds iff
`T_n(λ, 0, t) = Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t)` is nonnegative for every `λ > 0`, every
height `t` and every `n`. -/
theorem riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg :
    RiemannHypothesis ↔
      ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  constructor
  · intro hRH lam hlam t n
    rw [riemannHypothesis_iff_newmanConstant_eq_zero] at hRH
    have hmem := (mem_realRootedTimes_iff hlam.le).mpr (by rw [hRH]; exact hlam.le)
    exact xiSliceHeatTransfer_nonneg_of_strip hlam le_rfl
      (fun ζ hζ => by rw [hmem.2 ζ hζ]) t n
  · intro h
    refine riemannHypothesis_iff_xiSliceCoeff_nonneg.mpr fun t n => ?_
    exact ge_of_tendsto (tendsto_xiSliceHeatTransfer_zero t n)
      (eventually_nhdsWithin_of_forall fun lam hlam => h lam hlam t n)

end

end RHTower.DeBruijn
