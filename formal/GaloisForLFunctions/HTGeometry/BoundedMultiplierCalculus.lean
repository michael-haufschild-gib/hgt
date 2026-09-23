import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Norm calculus for one-parameter families of bounded multiplication operators

A one-parameter family of multiplication operators is differentiable *in operator norm* as soon as
its symbols are uniformly second-order close to a fixed symbol, because the operator norm of a
multiplier is controlled by the sup-norm of its symbol.  This is exactly the situation for the free
Schrödinger group of a bounded energy function, `exp (-i t ω)`, whose second-order Taylor remainder
is `O(h²)` uniformly in the energy label.

The file supplies

* `hasDerivAt_of_ae_mul`, the abstract differentiation criterion;
* `freeHamiltonian`, multiplication by a bounded real energy function, and its symmetry;
* `freeGroup`, the unitary group `exp (-i t ω)`, its group law, isometry, commutation with the
  Hamiltonian and its norm derivative `-i H₀ U₀ t`.

Nothing here uses spectral theory: the "spectral measure" of the model is the underlying measure
itself.
-/

open MeasureTheory Filter Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## The differentiation criterion -/

/-- **Norm differentiability from a uniform second-order symbol estimate.**  If a family of
operators acts almost everywhere as multiplication by symbols `φ t` whose increments agree with
`h • ψ` to second order, uniformly in the label, then the family is differentiable in operator
norm with derivative the multiplier of `ψ`. -/
theorem hasDerivAt_of_ae_mul
    {T : ℝ → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)} {D : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    {φ : ℝ → α → ℂ} {ψ : α → ℂ} {t K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ s, ∀ f : Lp ℂ 2 μ, ((T s f : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => φ s x * (f : α → ℂ) x)
    (hD : ∀ f : Lp ℂ 2 μ, ((D f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ψ x * (f : α → ℂ) x)
    (hbound : ∀ᶠ h : ℝ in nhds (0 : ℝ),
      ∀ x, ‖φ (t + h) x - φ t x - (h : ℂ) * ψ x‖ ≤ K * h ^ (2 : ℕ)) :
    HasDerivAt T D t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hpos : 0 < c / (K + 1) := by positivity
  have hball : ∀ᶠ h : ℝ in nhds (0 : ℝ), |h| ≤ c / (K + 1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    have hd : dist h 0 < c / (K + 1) := Metric.mem_ball.mp hh
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  filter_upwards [hbound, hball] with h hb hsmall
  have hnorm : ‖T (t + h) - T t - h • D‖ ≤ K * h ^ (2 : ℕ) := by
    refine MeasureTheory.norm_le_of_ae_mul
      (ψ := fun x => φ (t + h) x - φ t x - (h : ℂ) * ψ x) (by positivity) hb ?_
    intro f
    have hsub : ((T (t + h) - T t - h • D) f : Lp ℂ 2 μ)
        = (T (t + h) f - T t f) - (h : ℂ) • (D f) := by
      rw [show ((h : ℂ) • (D f)) = h • (D f) from
        (RCLike.real_smul_eq_coe_smul (K := ℂ) h (D f)).symm]
      simp
    rw [hsub]
    filter_upwards [Lp.coeFn_sub (T (t + h) f - T t f) ((h : ℂ) • (D f)),
      Lp.coeFn_sub (T (t + h) f) (T t f), Lp.coeFn_smul (h : ℂ) (D f),
      hT (t + h) f, hT t f, hD f] with x h1 h2 h3 h4 h5 h6
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h4, h5, h6]
    ring
  refine hnorm.trans ?_
  rw [Real.norm_eq_abs]
  have habs : h ^ (2 : ℕ) = |h| * |h| := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg h)]; ring
  rw [habs]
  have hKle : K * |h| ≤ c := by
    have h1 : K * |h| ≤ K * (c / (K + 1)) := by
      exact mul_le_mul_of_nonneg_left hsmall hK
    have h2 : K * (c / (K + 1)) ≤ c := by
      rw [mul_div_assoc'] at h1 ⊢
      rw [div_le_iff₀ (by positivity : (0:ℝ) < K + 1)]
      nlinarith [hc.le, hK]
    linarith
  calc K * (|h| * |h|) = (K * |h|) * |h| := by ring
    _ ≤ c * |h| := mul_le_mul_of_nonneg_right hKle (abs_nonneg h)

/-! ## The free Hamiltonian -/

/-- Multiplication by a bounded real energy function: the free Hamiltonian of the model. -/
def freeHamiltonian (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ) (φ := fun x => ((ω x : ℝ) : ℂ))
    (by exact Complex.measurable_ofReal.comp hω) hC0
    (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x)

theorem freeHamiltonian_coeFn (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (f : Lp ℂ 2 μ) :
    ((freeHamiltonian (μ := μ) ω hω hC0 hC f : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => ((ω x : ℝ) : ℂ) * (f : α → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- **The free Hamiltonian is self-adjoint.** -/
theorem isSelfAdjoint_freeHamiltonian (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) : IsSelfAdjoint (freeHamiltonian (μ := μ) ω hω hC0 hC) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  exact lpBoundedMulCLM_inner_real _ _ _ (fun x => by simp) f g

/-! ## The free unitary group -/

/-- The symbol `exp (-i t ω)` of the free Schrödinger group. -/
def freeSymbol (ω : α → ℝ) (t : ℝ) (x : α) : ℂ :=
  Complex.exp (((-(t * ω x) : ℝ) : ℂ) * Complex.I)

theorem measurable_freeSymbol {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) :
    Measurable (freeSymbol ω t) := by
  unfold freeSymbol
  exact (Complex.measurable_ofReal.comp ((hω.const_mul t).neg)).mul_const Complex.I |>.cexp

omit [MeasurableSpace α] in
@[simp] theorem norm_freeSymbol (ω : α → ℝ) (t : ℝ) (x : α) : ‖freeSymbol ω t x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The free Schrödinger group of a bounded energy function. -/
def freeGroup (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpBoundedMulCLM (p := 2) (μ := μ) (measurable_freeSymbol hω t) zero_le_one
    (fun x => le_of_eq (norm_freeSymbol ω t x))

theorem freeGroup_coeFn (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) (f : Lp ℂ 2 μ) :
    ((freeGroup ω hω t f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => freeSymbol ω t x * (f : α → ℂ) x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem freeGroup_comp (ω : α → ℝ) (hω : Measurable ω) (s t : ℝ) :
    (freeGroup (μ := μ) ω hω s) ∘L (freeGroup (μ := μ) ω hω t) = freeGroup ω hω (s + t) := by
  refine lpBoundedMulCLM_comp _ _ _ _ _ _ _ _ _ ?_
  filter_upwards with x
  unfold freeSymbol
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem freeGroup_zero (ω : α → ℝ) (hω : Measurable ω) :
    freeGroup (μ := μ) ω hω 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  refine lpBoundedMulCLM_eq_id _ _ _ ?_
  filter_upwards with x
  simp [freeSymbol]

theorem norm_freeGroup_apply (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) (f : Lp ℂ 2 μ) :
    ‖freeGroup (μ := μ) ω hω t f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [freeGroup_coeFn ω hω t f] with x hx
  rw [hx, norm_mul, norm_freeSymbol, one_mul]

theorem norm_freeGroup_le_one (ω : α → ℝ) (hω : Measurable ω) (t : ℝ) :
    ‖freeGroup (μ := μ) ω hω t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_freeGroup_apply, one_mul]

/-- The free Hamiltonian commutes with its own group. -/
theorem freeHamiltonian_comp_freeGroup (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (t : ℝ) :
    (freeHamiltonian (μ := μ) ω hω hC0 hC) ∘L (freeGroup (μ := μ) ω hω t)
      = (freeGroup (μ := μ) ω hω t) ∘L (freeHamiltonian (μ := μ) ω hω hC0 hC) := by
  have hmeas : Measurable (fun x : α => ((ω x : ℝ) : ℂ) * freeSymbol ω t x) :=
    (Complex.measurable_ofReal.comp hω).mul (measurable_freeSymbol hω t)
  have hB0 : (0 : ℝ) ≤ C * 1 := by positivity
  have hB : ∀ x : α, ‖((ω x : ℝ) : ℂ) * freeSymbol ω t x‖ ≤ C * 1 := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_freeSymbol, mul_one, mul_one]
    exact hC x
  have h1 : (freeHamiltonian (μ := μ) ω hω hC0 hC) ∘L (freeGroup (μ := μ) ω hω t)
      = lpBoundedMulCLM (p := 2) (μ := μ) hmeas hB0 hB := by
    refine lpBoundedMulCLM_comp _ _ hmeas _ _ _ _ hB0 hB ?_
    filter_upwards with x
    rfl
  have h2 : (freeGroup (μ := μ) ω hω t) ∘L (freeHamiltonian (μ := μ) ω hω hC0 hC)
      = lpBoundedMulCLM (p := 2) (μ := μ) hmeas hB0 hB := by
    refine lpBoundedMulCLM_comp _ _ hmeas _ _ _ _ hB0 hB ?_
    filter_upwards with x
    exact mul_comm _ _
  rw [h1, h2]

/-! ## A uniform second-order bound for the exponential -/

theorem norm_exp_sub_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z‖ ≤ 3 / 4 * ‖z‖ ^ (2 : ℕ) := by
  have h := Complex.exp_bound hz (n := 2) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 2, z ^ m / (Nat.factorial m : ℂ) = 1 + z := by
    simp [Finset.sum_range_succ]
  rw [hsum] at h
  have hconst : ((Nat.succ 2 : ℕ) : ℝ) * ((Nat.factorial 2 : ℝ) * (2 : ℕ)) ⁻¹ = 3 / 4 := by
    norm_num
  calc ‖Complex.exp z - 1 - z‖ = ‖Complex.exp z - (1 + z)‖ := by rw [sub_sub]
    _ ≤ ‖z‖ ^ (2 : ℕ) * (((Nat.succ 2 : ℕ) : ℝ) * ((Nat.factorial 2 : ℝ) * (2 : ℕ)) ⁻¹) := h
    _ = 3 / 4 * ‖z‖ ^ (2 : ℕ) := by rw [hconst]; ring

/-- **The free group solves the free Schrödinger equation**, in operator norm. -/
theorem hasDerivAt_freeGroup (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) (t : ℝ) :
    HasDerivAt (freeGroup (μ := μ) ω hω)
      ((-Complex.I) • ((freeHamiltonian (μ := μ) ω hω hC0 hC) ∘L
        (freeGroup (μ := μ) ω hω t))) t := by
  refine hasDerivAt_of_ae_mul (K := 3 / 4 * C ^ (2 : ℕ))
    (φ := fun s => freeSymbol ω s)
    (ψ := fun x => -Complex.I * ((ω x : ℝ) : ℂ) * freeSymbol ω t x) (by positivity) ?_ ?_ ?_
  · intro s f
    exact freeGroup_coeFn ω hω s f
  · intro f
    have hval : (((-Complex.I) • ((freeHamiltonian (μ := μ) ω hω hC0 hC) ∘L
          (freeGroup (μ := μ) ω hω t))) f)
        = (-Complex.I) • ((freeHamiltonian (μ := μ) ω hω hC0 hC)
          ((freeGroup (μ := μ) ω hω t) f)) := rfl
    rw [hval]
    filter_upwards [Lp.coeFn_smul (-Complex.I)
        ((freeHamiltonian (μ := μ) ω hω hC0 hC) ((freeGroup (μ := μ) ω hω t) f)),
      freeHamiltonian_coeFn ω hω hC0 hC ((freeGroup (μ := μ) ω hω t) f),
      freeGroup_coeFn ω hω t f] with x h1 h2 h3
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, h3]
    ring
  · have hpos : (0 : ℝ) < 1 / (C + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    have hhabs : |h| ≤ 1 / (C + 1) := by
      have hd := Metric.mem_ball.mp hh
      rw [Real.dist_eq, sub_zero] at hd
      exact hd.le
    intro x
    set z : ℂ := ((-(h * ω x) : ℝ) : ℂ) * Complex.I with hzdef
    have hznorm : ‖z‖ = |h * ω x| := by
      rw [hzdef, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one, abs_neg]
    have hzle : ‖z‖ ≤ 1 := by
      rw [hznorm, abs_mul]
      have h1 : |ω x| ≤ C := hC x
      have h2 : |h| * |ω x| ≤ (1 / (C + 1)) * C :=
        mul_le_mul hhabs h1 (abs_nonneg _) (by positivity)
      have h3 : (1 / (C + 1)) * C ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
      linarith
    have hsplit : freeSymbol ω (t + h) x = freeSymbol ω t x * Complex.exp z := by
      rw [freeSymbol, freeSymbol, hzdef, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hdiff : freeSymbol ω (t + h) x - freeSymbol ω t x
        - (h : ℂ) * (-Complex.I * ((ω x : ℝ) : ℂ) * freeSymbol ω t x)
        = freeSymbol ω t x * (Complex.exp z - 1 - z) := by
      rw [hsplit, hzdef]
      push_cast
      ring
    rw [hdiff, norm_mul, norm_freeSymbol, one_mul]
    have hsq : (ω x) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
      have h1 : |ω x| ≤ C := hC x
      have h2 : (0 : ℝ) ≤ |ω x| := abs_nonneg _
      nlinarith [sq_abs (ω x)]
    calc ‖Complex.exp z - 1 - z‖ ≤ 3 / 4 * ‖z‖ ^ (2 : ℕ) := norm_exp_sub_one_sub_le hzle
      _ = 3 / 4 * (h ^ (2 : ℕ) * (ω x) ^ (2 : ℕ)) := by rw [hznorm, sq_abs]; ring
      _ ≤ 3 / 4 * (h ^ (2 : ℕ) * C ^ (2 : ℕ)) := by nlinarith [sq_nonneg h]
      _ = 3 / 4 * C ^ (2 : ℕ) * h ^ (2 : ℕ) := by ring

theorem continuous_freeGroup (ω : α → ℝ) (hω : Measurable ω) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |ω x| ≤ C) : Continuous (freeGroup (μ := μ) ω hω) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_freeGroup ω hω hC0 hC t).continuousAt

end GaloisForLFunctions.HTGeometry
