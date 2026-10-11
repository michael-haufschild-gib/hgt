import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary
import GaloisForLFunctions.RHTower.RiemannHeatSliceTaylorPositivity
import GaloisForLFunctions.RHTower.ScalarPowerSeriesUniqueness

/-!
# Heat transfer of slice positivity back to `Ξ`

Let `Φ` be Riemann's kernel, `H_λ(z) = ∫ Φ(u) e^{λu²} e^{izu} du` and `S_λ(t, x) = H_λ(t − ix) H_λ(t + ix)`,
so `S_0` is the slice `ξ(½+x+it) ξ(½−x+it)` with Taylor coefficients `c_n(t)` (`xiSliceCoeff`).
For a kernel `g` the slice of its transform is the double integral
`∫∫ g(u) g(v) e^{it(u+v)} e^{x(u−v)}`, so its Taylor coefficients are the moments
`M_n(g, t) = ∫∫ g(u) g(v) (u − v)ⁿ/n! e^{it(u+v)}` (`sliceMoment`, `sliceMoment_eq_iteratedDeriv`).

**Transfer identity** (`integral_heightGaussian_mul_sliceMoment_heat`).  Average the slice
coefficients of `H_λ` over heights with the Gaussian of variance `λ` (`σ² = 1/(2λ)`).  Since
`e^{λ(u²+v²)} e^{−λ(u+v)²/2} = e^{λ(u−v)²/2}`,

  `∫ G(t − t′) M_n(Φe^{λu²}, t′) dt′ = T_n(λ, t) := ∫∫ Φ(u) Φ(v) e^{λ(u−v)²/2} (u − v)ⁿ/n! e^{it(u+v)}`,

and expanding `e^{λ(u−v)²/2}` (`hasSum_xiSliceHeatTransfer`),

  `T_n(λ, t) = Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t)`.

So `Σ_n T_n(λ, t) xⁿ = e^{(λ/2)∂_x²} S_0(t, x)`: the Gaussian height average of the `λ`-slices is
the slice of `Ξ` itself, heated in the slice variable for time `λ/2`.

**Unconditional positivity at every height** (`xiSliceHeatTransfer_nonneg`).  For `λ ≥ 1/8` all
zeros of `H_λ` are real (de Bruijn), so every slice of `H_λ` has nonnegative Taylor coefficients
(`nonnegTaylorAtZero_riemannHeat_slice_of_cone`), and so does their average.  Hence for every
height `t` and every `n`

  `Σ_k (λ/2)^k/k! · (n+2k)!/n! · c_{n+2k}(t) ≥ 0`   (`λ ≥ 1/8`).

This holds pointwise in the height, with no averaging over `t`: the price of removing the Gaussian
height average of the Husimi identity is the heat factor `e^{(λ/2)∂_x²}` in the slice variable.

**The Riemann hypothesis** (`riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg`).  RH holds
iff `T_n(λ, t) ≥ 0` for every `λ > 0`, height `t` and order `n`.  As `λ → 0⁺`, `T_n(λ, t) → c_n(t)`.
Forward heat in `x` preserves nonnegative coefficients, so the admissible `λ` form an interval
`[λ_WD, ∞)` with `λ_WD ≤ 1/8`, and RH is `λ_WD ≤ 0`.
-/

open Complex MeasureTheory Filter Topology

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

/-- The slice moments `M_n(g, t) = ∫∫ g(u) g(v) (u − v)ⁿ/n! e^{it(u+v)}`. -/
def sliceMoment (g : ℝ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  ∫ p : ℝ × ℝ, ((g p.1 * g p.2 * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) *
    cexp (I * t * (p.1 + p.2))

theorem norm_cexp_I_mul_ofReal_add (t a b : ℝ) : ‖cexp (I * t * ((a : ℂ) + b))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- `e^{c|u − v|} ≤ e^{c|u|} e^{c|v|}`. -/
theorem exp_mul_abs_sub_le {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    Real.exp (c * |u - v|) ≤ Real.exp (c * |u|) * Real.exp (c * |v|) := by
  rw [← Real.exp_add, ← mul_add]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_sub _ _) hc)

/-- The product majorant `g(u) e^{c|u|} g(v) e^{c|v|}` is integrable. -/
theorem integrable_prod_majorant (hg : SuperExpKernel g) (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => g p.1 * Real.exp (c * |p.1|) * (g p.2 * Real.exp (c * |p.2|))) :=
  (hg.integrable_mul_exp c).mul_prod (hg.integrable_mul_exp c)

/-- **The moment series of the slice.**  `S(t, x) = Σ_n M_n(g, t) xⁿ` for every complex `x`. -/
theorem hasSum_sliceMoment (hg : SuperExpKernel g) (t : ℝ) (x : ℂ) :
    HasSum (fun n => sliceMoment g t n * x ^ n)
      (cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)) := by
  rw [cosTransform_slice_eq_integral]
  set F : ℕ → ℝ × ℝ → ℂ := fun n p =>
    ((g p.1 * g p.2 * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) *
      x ^ n with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    g p.1 * Real.exp (‖x‖ * |p.1|) * (g p.2 * Real.exp (‖x‖ * |p.2|)) with hD
  have hDi : Integrable D := integrable_prod_majorant hg ‖x‖
  have hg0 := hg.nonneg
  have hnormF : ∀ n p, ‖F n p‖ = g p.1 * g p.2 * (|p.1 - p.2| ^ n / n.factorial) * ‖x‖ ^ n := by
    intro n p
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, norm_pow, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hg0 _)]
  have hbound : ∀ N : ℕ, ∀ p : ℝ × ℝ, ∑ n ∈ Finset.range N, ‖F n p‖ ≤ D p := by
    intro N p
    simp only [hnormF]
    have e : ∑ n ∈ Finset.range N, g p.1 * g p.2 * (|p.1 - p.2| ^ n / n.factorial) * ‖x‖ ^ n =
        g p.1 * g p.2 * ∑ n ∈ Finset.range N, (‖x‖ * |p.1 - p.2|) ^ n / n.factorial := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow]
      ring
    rw [e]
    have h1 := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ ‖x‖ * |p.1 - p.2|) N
    have h2 := exp_mul_abs_sub_le (norm_nonneg x) p.1 p.2
    have hgg : 0 ≤ g p.1 * g p.2 := mul_nonneg (hg0 _) (hg0 _)
    calc g p.1 * g p.2 * ∑ n ∈ Finset.range N, (‖x‖ * |p.1 - p.2|) ^ n / n.factorial
        ≤ g p.1 * g p.2 * (Real.exp (‖x‖ * |p.1|) * Real.exp (‖x‖ * |p.2|)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hgg
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
      ((g p.1 * g p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + x * (p.1 - p.2)) := by
    intro p
    have hexp := NormedSpace.expSeries_div_hasSum_exp (x * ((p.1 - p.2 : ℝ) : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at hexp
    simp only [mul_pow] at hexp
    have hF' : (fun n => F n p) = fun n => (((g p.1 * g p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2))) *
        (x ^ n * ((p.1 - p.2 : ℝ) : ℂ) ^ n / n.factorial) := by
      funext n
      simp only [hF]
      push_cast
      ring
    rw [hF', (hexp.mul_left _).tsum_eq, Complex.exp_add]
    push_cast
    ring
  simp_rw [htsum] at h
  refine h.congr_fun fun n => ?_
  simp only [hF, sliceMoment]
  rw [integral_mul_const]

/-- **The slice moments are the Taylor coefficients.** -/
theorem sliceMoment_eq_iteratedDeriv (hg : SuperExpKernel g) (t : ℝ) (n : ℕ) :
    sliceMoment g t n = iteratedDeriv n
      (fun x => cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)) 0 /
        n.factorial :=
  PowerSeriesUniqueness.coeff_eq_iteratedDeriv_div_factorial_of_hasSum one_pos (fun w _ => hasSum_sliceMoment hg t w) n

end Abstract

end

end RHTower.DeBruijn
