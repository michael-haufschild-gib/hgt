import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity

/-!
# Heated Ξ-slice coefficients are positive-definite functions of the height

For even order `2k` and heat `λ ≥ 0`, the heated slice coefficient is

  `T_{2k}(λ, 0, t) = ∫∫ w(u, v) e^{it(u+v)}`,
  `w(u, v) = Φ(u) Φ(v) e^{λ(u−v)²/2} (u − v)^{2k}/(2k)! ≥ 0`,

a Fourier transform in the variable `u + v` of a nonnegative integrable weight
(`xiSliceHeatTransfer_eq_integral`).  Hence, as a function of the height `t`:

* **positive definiteness** (`sum_sum_mul_xiSliceHeatTransfer_nonneg`): for heights `t_i` and complex
  `a_i`, `Σ_{i,j} a_i conj(a_j) T_{2k}(λ, 0, t_i − t_j) = ∫ w |Σ_i a_i e^{it_i(u+v)}|² ≥ 0`;
* **central domination** (`norm_xiSliceHeatTransfer_le_central`): `|T_{2k}(λ, 0, t)| ≤ T_{2k}(λ, 0, 0)`,
  and the central value is real and strictly positive (`xiSliceHeatTransfer_central_pos`).

At `λ = 0` this is the Ξ-slice itself (`norm_xiSliceCoeff_le_central`): every Taylor coefficient
`c_{2k}(t)` of `ξ(½+x+it) ξ(½−x+it)` satisfies `|c_{2k}(t)| ≤ c_{2k}(0)`, the corresponding Taylor
coefficient of `ξ(½+x)²`, which is positive.  So the negative part of every slice coefficient, at
every height and every heat, is bounded by the central coefficient: RH asks the coefficient
function to lie in the positive cone, and it already lies in the Bochner cone.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexOrder ComplexConjugate

namespace RHTower.DeBruijn

noncomputable section

/-- The nonnegative weight of the even heated slice coefficient,
`w(u, v) = Φ(u) Φ(v) e^{λ(u−v)²/2} (u − v)^{2k}/(2k)!` (with the trivial centre factor
`e^{0·(u−v)}` kept so that the transfer integrand matches definitionally). -/
def sliceHeatWeight (lam : ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  riemannKernelReal p.1 * riemannKernelReal p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
    Real.exp (0 * (p.1 - p.2)) * ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial)

theorem sliceHeatWeight_nonneg (lam : ℝ) (k : ℕ) (p : ℝ × ℝ) : 0 ≤ sliceHeatWeight lam k p := by
  have h1 := riemannKernel_superExp.nonneg p.1
  have h2 := riemannKernel_superExp.nonneg p.2
  have h3 : 0 ≤ (p.1 - p.2) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  unfold sliceHeatWeight
  positivity

theorem continuous_sliceHeatWeight (lam : ℝ) (k : ℕ) : Continuous (sliceHeatWeight lam k) := by
  have := continuous_riemannKernelReal
  unfold sliceHeatWeight
  fun_prop

/-- The weight is dominated by the integrable product majorant of `Φ e^{λu²}`. -/
theorem integrable_sliceHeatWeight {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    Integrable (sliceHeatWeight lam k) := by
  have hD := integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq hlam) 1
  refine hD.mono' (continuous_sliceHeatWeight lam k).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (sliceHeatWeight_nonneg lam k p)]
  have hΦ : 0 ≤ riemannKernelReal p.1 * riemannKernelReal p.2 :=
    mul_nonneg (riemannKernel_superExp.nonneg _) (riemannKernel_superExp.nonneg _)
  have hsq : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤
      Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p.1 + p.2)])
  have hpow := abs_sub_pow_div_mul_exp_le 0 p.1 p.2 (2 * k)
  rw [abs_zero, zero_add, (even_two_mul k).pow_abs] at hpow
  calc sliceHeatWeight lam k p
      = riemannKernelReal p.1 * riemannKernelReal p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          ((p.1 - p.2) ^ (2 * k) / (2 * k).factorial * Real.exp (0 * (p.1 - p.2))) := by
        unfold sliceHeatWeight; ring
    _ ≤ riemannKernelReal p.1 * riemannKernelReal p.2 *
          (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2)) *
          (Real.exp (1 * |p.1|) * Real.exp (1 * |p.2|)) := by
        gcongr
        exact mul_nonneg (div_nonneg ((even_two_mul k).pow_nonneg _) (by positivity))
          (Real.exp_pos _).le
    _ = _ := by ring

/-- The even heated slice coefficient is the Fourier transform of its weight in `u + v`. -/
theorem xiSliceHeatTransfer_eq_integral (lam t : ℝ) (k : ℕ) :
    xiSliceHeatTransfer lam 0 t (2 * k) =
      ∫ p : ℝ × ℝ, (sliceHeatWeight lam k p : ℂ) * cexp (I * t * (p.1 + p.2)) := rfl

theorem integrable_sliceHeatWeight_mul_cexp {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) (t : ℝ) (c : ℂ) :
    Integrable fun p : ℝ × ℝ =>
      c * ((sliceHeatWeight lam k p : ℂ) * cexp (I * t * (p.1 + p.2))) := by
  refine ((integrable_sliceHeatWeight hlam k).norm.const_mul ‖c‖).mono' ?_
    (Eventually.of_forall fun p => ?_)
  · have := continuous_sliceHeatWeight lam k
    exact Continuous.aestronglyMeasurable (by fun_prop)
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

/-- **Positive definiteness in the height.**  For every heat `λ ≥ 0`, order `2k`, heights `t_i`
and coefficients `a_i`, `Σ_{i,j} a_i conj(a_j) T_{2k}(λ, 0, t_i − t_j) ≥ 0`. -/
theorem sum_sum_mul_xiSliceHeatTransfer_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * xiSliceHeatTransfer lam 0 (τ i - τ j) (2 * k) := by
  simp_rw [xiSliceHeatTransfer_eq_integral, ← integral_const_mul]
  have hinner : ∀ i, ∑ j ∈ s, ∫ p : ℝ × ℝ, a i * conj (a j) *
      ((sliceHeatWeight lam k p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2))) =
      ∫ p : ℝ × ℝ, ∑ j ∈ s, a i * conj (a j) *
        ((sliceHeatWeight lam k p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2))) :=
    fun i => (integral_finsetSum s fun j _ => integrable_sliceHeatWeight_mul_cexp hlam k _ _).symm
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← integral_finsetSum s fun i _ =>
    integrable_finsetSum s fun j _ => integrable_sliceHeatWeight_mul_cexp hlam k _ _]
  have e : (fun p : ℝ × ℝ => ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) *
      ((sliceHeatWeight lam k p : ℂ) * cexp (I * ((τ i - τ j : ℝ) : ℂ) * (p.1 + p.2)))) =
      fun p => ((sliceHeatWeight lam k p *
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
    mul_nonneg (sliceHeatWeight_nonneg lam k p) (Complex.normSq_nonneg _))

/-- The central heated coefficient is the total mass of the weight. -/
theorem xiSliceHeatTransfer_central_eq (lam : ℝ) (k : ℕ) :
    xiSliceHeatTransfer lam 0 0 (2 * k) = ((∫ p : ℝ × ℝ, sliceHeatWeight lam k p : ℝ) : ℂ) := by
  rw [xiSliceHeatTransfer_eq_integral, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp

/-- **Central domination.**  `|T_{2k}(λ, 0, t)| ≤ T_{2k}(λ, 0, 0)` at every height. -/
theorem norm_xiSliceHeatTransfer_le_central (lam t : ℝ) (k : ℕ) :
    ‖xiSliceHeatTransfer lam 0 t (2 * k)‖ ≤ (xiSliceHeatTransfer lam 0 0 (2 * k)).re := by
  rw [xiSliceHeatTransfer_central_eq, Complex.ofReal_re, xiSliceHeatTransfer_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun p => ?_)))
  dsimp only
  rw [norm_mul, Complex.norm_real, norm_cexp_I_mul_ofReal_add, mul_one,
    Real.norm_of_nonneg (sliceHeatWeight_nonneg lam k p)]

/-- The weight is positive somewhere: near the diagonal point `(a, 0)` with `Φ(a) > 0`, `a ≠ 0`. -/
theorem exists_sliceHeatWeight_pos (lam : ℝ) (k : ℕ) : ∃ p, 0 < sliceHeatWeight lam k p := by
  obtain ⟨a, ha, ha0⟩ : ∃ a : ℝ, 0 < riemannKernelReal a ∧ a ≠ 0 := by
    have h1 : ∀ᶠ a in 𝓝[≠] (0 : ℝ), 0 < riemannKernelReal a :=
      nhdsWithin_le_nhds ((continuous_riemannKernelReal.tendsto 0).eventually
        (lt_mem_nhds riemannKernel_superExp.pos_zero))
    exact (h1.and self_mem_nhdsWithin).exists
  refine ⟨(a, 0), ?_⟩
  have h0 := riemannKernel_superExp.pos_zero
  have hp : 0 < (a - 0) ^ (2 * k) := by
    rw [sub_zero, pow_mul]; exact pow_pos (by positivity) k
  unfold sliceHeatWeight
  positivity

/-- **The central heated coefficient is strictly positive.** -/
theorem xiSliceHeatTransfer_central_pos {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    0 < (xiSliceHeatTransfer lam 0 0 (2 * k)).re := by
  rw [xiSliceHeatTransfer_central_eq, Complex.ofReal_re]
  obtain ⟨p, hp⟩ := exists_sliceHeatWeight_pos lam k
  refine (integral_pos_iff_support_of_nonneg (sliceHeatWeight_nonneg lam k)
    (integrable_sliceHeatWeight hlam k)).mpr ?_
  exact (continuous_sliceHeatWeight lam k).isOpen_support.measure_pos volume ⟨p, hp.ne'⟩

/-! ## The unheated slice -/

theorem xiSliceHeatTransfer_heat_zero (t : ℝ) (n : ℕ) :
    xiSliceHeatTransfer 0 0 t n = xiSliceCoeff t n := by
  rw [← kernelSliceMoment_riemannKernel_eq_xiSliceCoeff]
  unfold xiSliceHeatTransfer kernelSliceMoment
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp

/-- **Slice coefficients are positive definite in the height.** -/
theorem sum_sum_mul_xiSliceCoeff_nonneg (k : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (τ : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * xiSliceCoeff (τ i - τ j) (2 * k) := by
  simpa only [xiSliceHeatTransfer_heat_zero] using
    sum_sum_mul_xiSliceHeatTransfer_nonneg le_rfl k s a τ

/-- **Every Ξ-slice coefficient is dominated by the central one.**  `|c_{2k}(t)| ≤ c_{2k}(0)` and
`c_{2k}(0) > 0`, where `c_n(t)` are the Taylor coefficients of `ξ(½+x+it) ξ(½−x+it)` at `x = 0`. -/
theorem norm_xiSliceCoeff_le_central (t : ℝ) (k : ℕ) :
    ‖xiSliceCoeff t (2 * k)‖ ≤ (xiSliceCoeff 0 (2 * k)).re ∧ 0 < (xiSliceCoeff 0 (2 * k)).re := by
  simpa only [xiSliceHeatTransfer_heat_zero] using
    And.intro (norm_xiSliceHeatTransfer_le_central 0 t k) (xiSliceHeatTransfer_central_pos
      le_rfl k)

end

end RHTower.DeBruijn
