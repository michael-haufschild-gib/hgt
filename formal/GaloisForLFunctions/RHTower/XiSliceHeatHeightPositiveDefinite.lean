import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity
import GaloisForLFunctions.RHTower.XiLaguerreOffLineNeighbourhood

/-!
# Even slice coefficients are positive-definite functions of the height

Every even-order slice coefficient used by routes WD and LA is a Fourier transform, in the variable
`u + v`, of a nonnegative integrable weight on `ℝ²`:

* the heated Ξ-slice coefficient at abscissa `x₀`,
  `T_{2k}(λ, x₀, t) = ∫∫ Φ(u)Φ(v) e^{λ(u−v)²/2} e^{x₀(u−v)} (u−v)^{2k}/(2k)! e^{it(u+v)}`, `λ ≥ 0`
  (`xiSliceHeatTransfer`);
* the slice moment of any super-exponential kernel `g`, in particular of the de Bruijn–Newman flow
  `g = Φ e^{μu²}`, `M_{2k}(g, x₀, t) = ∫∫ g(u)g(v) e^{x₀(u−v)} (u−v)^{2k}/(2k)! e^{it(u+v)}`
  (`kernelSliceMoment`).

For such a transform `T(t) = ∫ w(p) e^{it(p₁+p₂)}` with `w ≥ 0` (`heightTransform`):

* **positive definiteness** (`sum_sum_mul_heightTransform_nonneg`): for heights `t_i` and complex
  `a_i`, `Σ_{i,j} a_i conj(a_j) T(t_i − t_j) = ∫ w |Σ_i a_i e^{it_i(p₁+p₂)}|² ≥ 0`;
* **central domination** (`norm_heightTransform_le_central`): `|T(t)| ≤ T(0) = ∫ w`, and `T(0) > 0`
  when `w` is continuous and positive somewhere (`heightTransform_central_pos`).

At `λ = 0`, `x₀ = 0` this is the Ξ-slice itself (`norm_xiSliceCoeff_le_central`): every Taylor
coefficient `c_{2k}(t)` of `ξ(½+x+it) ξ(½−x+it)` satisfies `|c_{2k}(t)| ≤ c_{2k}(0)`, the
corresponding Taylor coefficient of `ξ(½+x)²`, which is positive.  For `k = 1` this says that the first Laguerre
expression of `Ξ` is maximal at the origin (`norm_laguerre_XiC_le_central`):
`|Ξ'(t)² − Ξ(t)Ξ''(t)| ≤ Ξ'(0)² − Ξ(0)Ξ''(0)`.  So the negative part of every
even slice coefficient, at every height, heat and abscissa, is bounded by the central coefficient:
RH asks the coefficient function to lie in the positive cone, and it already lies in the Bochner
cone.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexOrder ComplexConjugate

namespace RHTower.DeBruijn

noncomputable section

/-! ## Fourier transforms of nonnegative weights along `u + v` -/

section Abstract

variable {w : ℝ × ℝ → ℝ}

/-- The height transform `T(t) = ∫ w(p) e^{it(p₁+p₂)}` of a weight on `ℝ²`. -/
def heightTransform (w : ℝ × ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, (w p : ℂ) * cexp (I * t * (p.1 + p.2))

theorem integrable_const_mul_weight_mul_cexp (hwi : Integrable w) (t : ℝ) (c : ℂ) :
    Integrable fun p : ℝ × ℝ => c * ((w p : ℂ) * cexp (I * t * (p.1 + p.2))) := by
  refine (hwi.norm.const_mul ‖c‖).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have hw : AEStronglyMeasurable (fun p => (w p : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.aestronglyMeasurable
    exact aestronglyMeasurable_const.mul
      (hw.mul (Continuous.aestronglyMeasurable (by fun_prop)))
  · rw [norm_mul, norm_mul, Complex.norm_real, norm_cexp_I_mul_ofReal_add, mul_one]

/-- The pointwise Hermitian square: `Σ_{i,j} a_i conj(a_j) e^{i(t_i−t_j)σ} = |Σ_i a_i e^{it_iσ}|²`. -/
theorem sum_sum_mul_cexp_eq_normSq {ι : Type*} (s : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) (σ : ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * σ) =
      ((Complex.normSq (∑ i ∈ s, a i * cexp (I * τ i * σ)) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have hc : conj (I * (τ j : ℂ) * σ) = -(I * τ j * σ) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hc, show a i * cexp (I * τ i * σ) * (conj (a j) * cexp (-(I * τ j * σ))) =
    a i * conj (a j) * (cexp (I * τ i * σ) * cexp (-(I * τ j * σ))) by ring, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **Positive definiteness in the height.** -/
theorem sum_sum_mul_heightTransform_nonneg (hw0 : ∀ p, 0 ≤ w p) (hwi : Integrable w)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * heightTransform w (τ i - τ j) := by
  unfold heightTransform
  simp_rw [← integral_const_mul]
  have hinner : ∀ i, ∑ j ∈ s, ∫ p : ℝ × ℝ, a i * conj (a j) *
      ((w p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2))) =
      ∫ p : ℝ × ℝ, ∑ j ∈ s, a i * conj (a j) *
        ((w p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2))) :=
    fun i => (integral_finsetSum s fun j _ => integrable_const_mul_weight_mul_cexp hwi _ _).symm
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← integral_finsetSum s fun i _ =>
    integrable_finsetSum s fun j _ => integrable_const_mul_weight_mul_cexp hwi _ _]
  have e : (fun p : ℝ × ℝ => ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) *
      ((w p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2)))) =
      fun p => ((w p *
        Complex.normSq (∑ i ∈ s, a i * cexp (I * τ i * ((p.1 + p.2 : ℝ) : ℂ))) : ℝ) : ℂ) := by
    funext p
    have h := sum_sum_mul_cexp_eq_normSq s a τ (p.1 + p.2)
    push_cast at h ⊢
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun p =>
    mul_nonneg (hw0 p) (Complex.normSq_nonneg _))

/-- The central value is the total mass of the weight. -/
theorem heightTransform_zero (w : ℝ × ℝ → ℝ) :
    heightTransform w 0 = ((∫ p : ℝ × ℝ, w p : ℝ) : ℂ) := by
  rw [heightTransform, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp

/-- **Central domination.**  `|T(t)| ≤ T(0)`. -/
theorem norm_heightTransform_le_central (hw0 : ∀ p, 0 ≤ w p) (t : ℝ) :
    ‖heightTransform w t‖ ≤ (heightTransform w 0).re := by
  rw [heightTransform_zero, Complex.ofReal_re, heightTransform]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun p => ?_)))
  dsimp only
  rw [norm_mul, Complex.norm_real, norm_cexp_I_mul_ofReal_add, mul_one,
    Real.norm_of_nonneg (hw0 p)]

/-- **The central value is strictly positive** for a continuous weight positive somewhere. -/
theorem heightTransform_central_pos (hw0 : ∀ p, 0 ≤ w p) (hwi : Integrable w)
    (hwc : Continuous w) (hpos : ∃ p, 0 < w p) : 0 < (heightTransform w 0).re := by
  rw [heightTransform_zero, Complex.ofReal_re]
  obtain ⟨p, hp⟩ := hpos
  refine (integral_pos_iff_support_of_nonneg hw0 hwi).mpr ?_
  exact hwc.isOpen_support.measure_pos volume ⟨p, hp.ne'⟩

end Abstract

/-- A point `a ≠ 0` with `Φ(a) > 0`. -/
theorem exists_riemannKernelReal_pos_ne_zero : ∃ a : ℝ, 0 < riemannKernelReal a ∧ a ≠ 0 := by
  have h1 : ∀ᶠ a in 𝓝[≠] (0 : ℝ), 0 < riemannKernelReal a :=
    nhdsWithin_le_nhds ((continuous_riemannKernelReal.tendsto 0).eventually
      (lt_mem_nhds riemannKernel_superExp.pos_zero))
  exact (h1.and self_mem_nhdsWithin).exists

/-! ## Heated Ξ-slice coefficients at abscissa `x₀` -/

/-- The weight of the even heated slice coefficient at abscissa `x₀`,
`Φ(u) Φ(v) e^{λ(u−v)²/2} e^{x₀(u−v)} (u − v)^{2k}/(2k)!`. -/
def sliceHeatWeight (lam x₀ : ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  riemannKernelReal p.1 * riemannKernelReal p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
    Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial)

theorem xiSliceHeatTransfer_eq_heightTransform (lam x₀ t : ℝ) (k : ℕ) :
    xiSliceHeatTransfer lam x₀ t (2 * k) = heightTransform (sliceHeatWeight lam x₀ k) t := rfl

theorem sliceHeatWeight_nonneg (lam x₀ : ℝ) (k : ℕ) (p : ℝ × ℝ) :
    0 ≤ sliceHeatWeight lam x₀ k p := by
  have h1 := riemannKernel_superExp.nonneg p.1
  have h2 := riemannKernel_superExp.nonneg p.2
  have h3 : 0 ≤ (p.1 - p.2) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  unfold sliceHeatWeight
  positivity

theorem continuous_sliceHeatWeight (lam x₀ : ℝ) (k : ℕ) :
    Continuous (sliceHeatWeight lam x₀ k) := by
  have := continuous_riemannKernelReal
  unfold sliceHeatWeight
  fun_prop

/-- The weight is dominated by the integrable product majorant of `Φ e^{λu²}`. -/
theorem integrable_sliceHeatWeight {lam : ℝ} (hlam : 0 ≤ lam) (x₀ : ℝ) (k : ℕ) :
    Integrable (sliceHeatWeight lam x₀ k) := by
  have hD := integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hlam) (|x₀| + 1)
  refine hD.mono' (continuous_sliceHeatWeight lam x₀ k).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (sliceHeatWeight_nonneg lam x₀ k p)]
  have hsq : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
      Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p.1 + p.2)])
  have hpow := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 (2 * k)
  rw [(even_two_mul k).pow_abs] at hpow
  calc sliceHeatWeight lam x₀ k p
      = riemannKernelReal p.1 * riemannKernelReal p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial * Real.exp (x₀ * (p.1 - p.2))) := by
        unfold sliceHeatWeight; ring
    _ ≤ riemannKernelReal p.1 * riemannKernelReal p.2 *
          (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) *
          (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) := by
        have hΦ : 0 ≤ riemannKernelReal p.1 * riemannKernelReal p.2 :=
          mul_nonneg (riemannKernel_superExp.nonneg _) (riemannKernel_superExp.nonneg _)
        gcongr
        exact mul_nonneg (div_nonneg ((even_two_mul k).pow_nonneg _) (by positivity))
          (Real.exp_pos _).le
    _ = _ := by ring

theorem exists_sliceHeatWeight_pos (lam x₀ : ℝ) (k : ℕ) : ∃ p, 0 < sliceHeatWeight lam x₀ k p := by
  obtain ⟨a, ha, ha0⟩ := exists_riemannKernelReal_pos_ne_zero
  refine ⟨(a, 0), ?_⟩
  have h0 := riemannKernel_superExp.pos_zero
  have hp : 0 < (a - 0) ^ (2 * k) := by
    rw [sub_zero, pow_mul]; exact pow_pos (by positivity) k
  unfold sliceHeatWeight
  positivity

/-- **Heated slice coefficients are positive definite in the height**, at every heat `λ ≥ 0`,
abscissa `x₀` and even order `2k`. -/
theorem sum_sum_mul_xiSliceHeatTransfer_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (x₀ : ℝ) (k : ℕ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * xiSliceHeatTransfer lam x₀ (τ i - τ j) (2 * k) :=
  sum_sum_mul_heightTransform_nonneg (sliceHeatWeight_nonneg lam x₀ k)
    (integrable_sliceHeatWeight hlam x₀ k) s a τ

/-- **Central domination of heated slice coefficients:** `|T_{2k}(λ, x₀, t)| ≤ T_{2k}(λ, x₀, 0)`,
and the central value is strictly positive. -/
theorem norm_xiSliceHeatTransfer_le_central {lam : ℝ} (hlam : 0 ≤ lam) (x₀ t : ℝ) (k : ℕ) :
    ‖xiSliceHeatTransfer lam x₀ t (2 * k)‖ ≤ (xiSliceHeatTransfer lam x₀ 0 (2 * k)).re ∧
      0 < (xiSliceHeatTransfer lam x₀ 0 (2 * k)).re :=
  ⟨norm_heightTransform_le_central (sliceHeatWeight_nonneg lam x₀ k) t,
    heightTransform_central_pos (sliceHeatWeight_nonneg lam x₀ k)
      (integrable_sliceHeatWeight hlam x₀ k) (continuous_sliceHeatWeight lam x₀ k)
      (exists_sliceHeatWeight_pos lam x₀ k)⟩

/-! ## Slices of super-exponential kernels: the de Bruijn–Newman flow -/

section Kernel

variable {g : ℝ → ℝ}

/-- The weight of the even slice moment of a kernel `g` at abscissa `x₀`. -/
def kernelSliceWeight (g : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  g p.1 * g p.2 * Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial)

theorem kernelSliceMoment_eq_heightTransform (g : ℝ → ℝ) (x₀ t : ℝ) (k : ℕ) :
    kernelSliceMoment g x₀ t (2 * k) = heightTransform (kernelSliceWeight g x₀ k) t := rfl

theorem kernelSliceWeight_nonneg (hg : SuperExpKernel g) (x₀ : ℝ) (k : ℕ) (p : ℝ × ℝ) :
    0 ≤ kernelSliceWeight g x₀ k p := by
  have h1 := hg.nonneg p.1
  have h2 := hg.nonneg p.2
  have h3 : 0 ≤ (p.1 - p.2) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  unfold kernelSliceWeight
  positivity

theorem continuous_kernelSliceWeight (hg : SuperExpKernel g) (x₀ : ℝ) (k : ℕ) :
    Continuous (kernelSliceWeight g x₀ k) := by
  have := hg.continuous
  unfold kernelSliceWeight
  fun_prop

theorem integrable_kernelSliceWeight (hg : SuperExpKernel g) (x₀ : ℝ) (k : ℕ) :
    Integrable (kernelSliceWeight g x₀ k) := by
  refine (integrable_prod_majorant hg (|x₀| + 1)).mono'
    (continuous_kernelSliceWeight hg x₀ k).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (kernelSliceWeight_nonneg hg x₀ k p)]
  have hpow := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 (2 * k)
  rw [(even_two_mul k).pow_abs] at hpow
  have hgg : 0 ≤ g p.1 * g p.2 := mul_nonneg (hg.nonneg _) (hg.nonneg _)
  calc kernelSliceWeight g x₀ k p
      = g p.1 * g p.2 * ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial *
          Real.exp (x₀ * (p.1 - p.2))) := by unfold kernelSliceWeight; ring
    _ ≤ g p.1 * g p.2 * (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) :=
        mul_le_mul_of_nonneg_left hpow hgg
    _ = _ := by ring

theorem exists_kernelSliceWeight_pos (hg : SuperExpKernel g) (x₀ : ℝ) (k : ℕ) :
    ∃ p, 0 < kernelSliceWeight g x₀ k p := by
  obtain ⟨a, ha, ha0⟩ : ∃ a : ℝ, 0 < g a ∧ a ≠ 0 := by
    have h1 : ∀ᶠ a in 𝓝[≠] (0 : ℝ), 0 < g a :=
      nhdsWithin_le_nhds ((hg.continuous.tendsto 0).eventually (lt_mem_nhds hg.pos_zero))
    exact (h1.and self_mem_nhdsWithin).exists
  refine ⟨(a, 0), ?_⟩
  have h0 := hg.pos_zero
  have hp : 0 < (a - 0) ^ (2 * k) := by
    rw [sub_zero, pow_mul]; exact pow_pos (by positivity) k
  unfold kernelSliceWeight
  positivity

/-- **Kernel slice moments are positive definite in the height.**  For `g = Φ e^{μu²}`, `μ ≥ 0`,
these are the Taylor coefficients at `x₀` of the slices of the de Bruijn–Newman flow `H_μ`
(`kernelSliceMoment_heat_eq`). -/
theorem sum_sum_mul_kernelSliceMoment_nonneg (hg : SuperExpKernel g) (x₀ : ℝ) (k : ℕ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * kernelSliceMoment g x₀ (τ i - τ j) (2 * k) :=
  sum_sum_mul_heightTransform_nonneg (kernelSliceWeight_nonneg hg x₀ k)
    (integrable_kernelSliceWeight hg x₀ k) s a τ

/-- **Central domination of kernel slice moments.** -/
theorem norm_kernelSliceMoment_le_central (hg : SuperExpKernel g) (x₀ t : ℝ) (k : ℕ) :
    ‖kernelSliceMoment g x₀ t (2 * k)‖ ≤ (kernelSliceMoment g x₀ 0 (2 * k)).re ∧
      0 < (kernelSliceMoment g x₀ 0 (2 * k)).re :=
  ⟨norm_heightTransform_le_central (kernelSliceWeight_nonneg hg x₀ k) t,
    heightTransform_central_pos (kernelSliceWeight_nonneg hg x₀ k)
      (integrable_kernelSliceWeight hg x₀ k) (continuous_kernelSliceWeight hg x₀ k)
      (exists_kernelSliceWeight_pos hg x₀ k)⟩

end Kernel

/-! ## The unheated Ξ-slice -/

/-- **Ξ-slice coefficients are positive definite in the height.** -/
theorem sum_sum_mul_xiSliceCoeff_nonneg (k : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * xiSliceCoeff (τ i - τ j) (2 * k) := by
  simpa only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] using
    sum_sum_mul_kernelSliceMoment_nonneg riemannKernel_superExp 0 k s a τ

/-- **Every Ξ-slice coefficient is dominated by the central one.**  `|c_{2k}(t)| ≤ c_{2k}(0)` and
`c_{2k}(0) > 0`, where `c_n(t)` are the Taylor coefficients of `ξ(½+x+it) ξ(½−x+it)` at `x = 0`. -/
theorem norm_xiSliceCoeff_le_central (t : ℝ) (k : ℕ) :
    ‖xiSliceCoeff t (2 * k)‖ ≤ (xiSliceCoeff 0 (2 * k)).re ∧ 0 < (xiSliceCoeff 0 (2 * k)).re := by
  simpa only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] using
    norm_kernelSliceMoment_le_central riemannKernel_superExp 0 t k

/-- **The first Laguerre expression of `Ξ` is maximal at the origin:**
`|Ξ'(t)² − Ξ(t)Ξ''(t)| ≤ Ξ'(0)² − Ξ(0)Ξ''(0)`, and the right side is positive. -/
theorem norm_laguerre_XiC_le_central (t : ℝ) :
    ‖deriv XiC t ^ 2 - XiC t * deriv (deriv XiC) t‖ ≤
        (deriv XiC 0 ^ 2 - XiC 0 * deriv (deriv XiC) 0).re ∧
      0 < (deriv XiC 0 ^ 2 - XiC 0 * deriv (deriv XiC) 0).re := by
  have h := norm_xiSliceCoeff_le_central t 1
  rw [show 2 * 1 = 2 from rfl, xiSliceCoeff_two_eq_laguerre, xiSliceCoeff_two_eq_laguerre] at h
  simpa using h

end

end RHTower.DeBruijn
