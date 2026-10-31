import GaloisForLFunctions.AdelicKreinGeometry.JordanPairKernelsOnDilations
import GaloisForLFunctions.AdelicKreinGeometry.HeatTangentBlaschkeExtraction
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian-damped horizontal contour kernel and Jordan pair residue expansion

From the source-defined horizontal Blaschke boundary values `heatLowerBlaschkeBoundary t` and
`heatUpperBlaschkeBoundary t` extracted from `Φ_t(x) = Φ(x) e^{t x²}`, this module builds the
Hermitian dilation kernel `heatDilationKernel t : posUnits → ℂ` directly by Gaussian-damped
contour integration along `Im z = ∓1`:

* **Source-only contour definition**:
  * `heatForwardDilation t v = (2πi)⁻¹ ∫_ℝ (B_t^−(r) e^{−(r−i)² − i(r−i) log v} −
      B_t^+(r) e^{−(r+i)² − i(r+i) log v}) dr`,
  * `heatDilationKernel t v = heatForwardDilation t v + conj (heatForwardDilation t v⁻¹)`.
* **Time continuity on `(0, ∞)`** (`continuousOn_heatDilationKernel`): on every compact subinterval
  of `(0, ∞)`, `heatRightZeroMultiplicity s` is bounded by `nonrealZeroCount`-monotonicity, giving a
  uniform integrable Gaussian majorant `((3 : ℝ)^M + 1) e^{−r² + 1 + |log v|}`; dominated convergence
  and boundary continuity across real/off-axis collisions yield pointwise continuity in `t ∈ (0, ∞)`.
* **Exact Cauchy residue decomposition** (`heatDilationKernel_eq_sum_jordanPairKernel`): closing the
  strip `|Im z| ≤ 1` on `[-R, R] × [-1, 1]` and sending `R → +∞` evaluates `heatDilationKernel t` at
  every `t > 0` as a sum of Jordan pair kernels `∑_{u ∈ heatRightZeroSet t} J_{u, P_{t, u}}` with
  `P_{t, u} ≠ 0` and `deg P_{t, u} + 1 = zeroMult (riemannHeat t) u`.
-/

open Complex Polynomial Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate BigOperators Interval
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Source-defined Gaussian contour kernel on `ℚ_{>0}` -/

/-- The entire Gaussian-exponential test wave `e^{−z² − i z y}` (`y ∈ ℝ`). -/
def heatGaussianWave (y : ℝ) (z : ℂ) : ℂ :=
  cexp (-(z ^ 2) - I * z * (y : ℂ))

/-- Horizontal strip contour integrand built solely from the source-extracted boundary values
`heatLowerBlaschkeBoundary t` and `heatUpperBlaschkeBoundary t`. -/
def heatContourIntegrand (t y : ℝ) (r : ℝ) : ℂ :=
  heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I) -
    heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I)

/-- Forward dilation correlation on `ℚ_{>0}` obtained by integrating `heatContourIntegrand` over
`ℝ`. -/
def heatForwardDilation (t : ℝ) (v : posUnits) : ℂ :=
  (1 / (2 * Real.pi * I)) * ∫ r : ℝ, heatContourIntegrand t (logPos v) r

/-- The Hermitian dilation kernel `K_t(v) = F_t(v) + conj(F_t(v⁻¹))` built from source data of `H_t`
alone. -/
def heatDilationKernel (t : ℝ) (v : posUnits) : ℂ :=
  heatForwardDilation t v + conj (heatForwardDilation t v⁻¹)

theorem isHermKernel_heatDilationKernel (t : ℝ) :
    IsHermKernel (heatDilationKernel t) := fun v => by
  simp only [heatDilationKernel, inv_inv, map_add, conj_conj, add_comm]

/-! ### Gaussian strip estimates, integrability, and time continuity -/

private theorem re_heatGaussianWave_arg (y r τ : ℝ) :
    (-((((r : ℂ) + (τ : ℂ) * I)) ^ 2) - I * ((r : ℂ) + (τ : ℂ) * I) * (y : ℂ)).re =
      -(r ^ 2) + τ ^ 2 + τ * y := by
  simp [sq]
  ring

private theorem norm_heatGaussianWave_eq (y r τ : ℝ) :
    ‖heatGaussianWave y ((r : ℂ) + (τ : ℂ) * I)‖ =
      Real.exp (-(r ^ 2) + τ ^ 2 + τ * y) := by
  rw [heatGaussianWave, Complex.norm_exp, re_heatGaussianWave_arg]

private theorem norm_heatGaussianWave_le (y r τ : ℝ) (hτ : |τ| ≤ 1) :
    ‖heatGaussianWave y ((r : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.exp (-(r ^ 2) + 1 + |y|) := by
  rw [norm_heatGaussianWave_eq]
  refine Real.exp_le_exp.mpr ?_
  obtain ⟨h1, h2⟩ := abs_le.mp hτ
  have hsq : τ ^ 2 ≤ 1 := by nlinarith
  have hmul : τ * y ≤ |y| := by
    calc τ * y ≤ |τ * y| := le_abs_self _
      _ = |τ| * |y| := abs_mul τ y
      _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hτ (abs_nonneg y)
      _ = |y| := one_mul _
  linarith

private theorem norm_heatGaussianWave_sub_I_le (y r : ℝ) :
    ‖heatGaussianWave y ((r : ℂ) - I)‖ ≤ Real.exp (-(r ^ 2) + 1 + |y|) := by
  have heq : (r : ℂ) - I = (r : ℂ) + ((-1 : ℝ) : ℂ) * I := by push_cast; ring
  rw [heq]
  exact norm_heatGaussianWave_le y r (-1) (by norm_num)

private theorem norm_heatGaussianWave_add_I_le (y r : ℝ) :
    ‖heatGaussianWave y ((r : ℂ) + I)‖ ≤ Real.exp (-(r ^ 2) + 1 + |y|) := by
  have heq : (r : ℂ) + I = (r : ℂ) + ((1 : ℝ) : ℂ) * I := by push_cast; ring
  rw [heq]
  exact norm_heatGaussianWave_le y r 1 (by norm_num)

private theorem integrable_gaussianEnvelope (C y : ℝ) :
    Integrable (fun r : ℝ => C * Real.exp (-(r ^ 2) + 1 + |y|)) := by
  have hbase : Integrable (fun r : ℝ => Real.exp (-(1 : ℝ) * r ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  refine (hbase.const_mul (C * Real.exp (1 + |y|))).congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem continuous_heatContourIntegrand {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Continuous (heatContourIntegrand t y) := by
  unfold heatContourIntegrand heatGaussianWave
  refine Continuous.sub ?_ ?_
  · exact (continuous_heatLowerBlaschkeBoundary ht).mul (by fun_prop)
  · exact (continuous_heatUpperBlaschkeBoundary ht).mul (by fun_prop)

private theorem norm_heatContourIntegrand_le {t : ℝ} (ht : 0 < t) (y r : ℝ) :
    ‖heatContourIntegrand t y r‖ ≤
      ((3 : ℝ) ^ heatRightZeroMultiplicity t + 1) * Real.exp (-(r ^ 2) + 1 + |y|) := by
  unfold heatContourIntegrand
  calc ‖heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I) -
          heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I)‖
      ≤ ‖heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I)‖ +
          ‖heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I)‖ := norm_sub_le _ _
    _ = ‖heatLowerBlaschkeBoundary t r‖ * ‖heatGaussianWave y ((r : ℂ) - I)‖ +
          ‖heatUpperBlaschkeBoundary t r‖ * ‖heatGaussianWave y ((r : ℂ) + I)‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (3 : ℝ) ^ heatRightZeroMultiplicity t * Real.exp (-(r ^ 2) + 1 + |y|) +
          1 * Real.exp (-(r ^ 2) + 1 + |y|) :=
        add_le_add
          (mul_le_mul (norm_heatLowerBlaschkeBoundary_le ht r)
            (norm_heatGaussianWave_sub_I_le y r) (norm_nonneg _) (by positivity))
          (mul_le_mul (norm_heatUpperBlaschkeBoundary_le_one ht r)
            (norm_heatGaussianWave_add_I_le y r) (norm_nonneg _) zero_le_one)
    _ = ((3 : ℝ) ^ heatRightZeroMultiplicity t + 1) * Real.exp (-(r ^ 2) + 1 + |y|) := by ring

private theorem integrable_heatLowerTerm {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun r : ℝ =>
      heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I)) := by
  have hcont : Continuous (fun r : ℝ =>
      heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I)) := by
    unfold heatGaussianWave
    exact (continuous_heatLowerBlaschkeBoundary ht).mul (by fun_prop)
  refine (integrable_gaussianEnvelope ((3 : ℝ) ^ heatRightZeroMultiplicity t) y).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_heatLowerBlaschkeBoundary_le ht r)
    (norm_heatGaussianWave_sub_I_le y r) (norm_nonneg _) (by positivity)

private theorem integrable_heatUpperTerm {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Integrable (fun r : ℝ =>
      heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I)) := by
  have hcont : Continuous (fun r : ℝ =>
      heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I)) := by
    unfold heatGaussianWave
    exact (continuous_heatUpperBlaschkeBoundary ht).mul (by fun_prop)
  refine (integrable_gaussianEnvelope 1 y).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_heatUpperBlaschkeBoundary_le_one ht r)
    (norm_heatGaussianWave_add_I_le y r) (norm_nonneg _) zero_le_one

theorem tendsto_heatForwardDilation_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) (v : posUnits) :
    Tendsto (fun s => heatForwardDilation s v) (𝓝 t₁) (𝓝 (heatForwardDilation t₁ v)) := by
  set y : ℝ := logPos v
  set M₀ : ℕ := heatRightZeroMultiplicity (t₁ / 2)
  set bound : ℝ → ℝ := fun r => ((3 : ℝ) ^ M₀ + 1) * Real.exp (-(r ^ 2) + 1 + |y|)
  have hnhds : Ioo (t₁ / 2) (t₁ + 1) ∈ 𝓝 t₁ := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ s in 𝓝 t₁, AEStronglyMeasurable (heatContourIntegrand s y) volume := by
    filter_upwards [hnhds] with s hs
    exact (continuous_heatContourIntegrand (by linarith [hs.1]) y).aestronglyMeasurable
  have hdom : ∀ᶠ s in 𝓝 t₁, ∀ᵐ r : ℝ ∂volume, ‖heatContourIntegrand s y r‖ ≤ bound r := by
    filter_upwards [hnhds] with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hM_le : heatRightZeroMultiplicity s ≤ M₀ := by
      dsimp only [M₀]
      rw [heatRightZeroMultiplicity_eq_div, heatRightZeroMultiplicity_eq_div]
      exact Nat.div_le_div_right
        (nonrealZeroCount_antitoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hs0) hs.1.le)
    have hpow_le : (3 : ℝ) ^ heatRightZeroMultiplicity s ≤ (3 : ℝ) ^ M₀ :=
      pow_le_pow_right₀ (by norm_num) hM_le
    exact Eventually.of_forall fun r => (norm_heatContourIntegrand_le hs0 y r).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  have hlim : ∀ᵐ r : ℝ ∂volume,
      Tendsto (fun s => heatContourIntegrand s y r) (𝓝 t₁)
        (𝓝 (heatContourIntegrand t₁ y r)) :=
    Eventually.of_forall fun r =>
      ((tendsto_heatLowerBlaschkeBoundary_nhds ht₁ r).mul tendsto_const_nhds).sub
        ((tendsto_heatUpperBlaschkeBoundary_nhds ht₁ r).mul tendsto_const_nhds)
  have hint := MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound hmeas hdom
    (integrable_gaussianEnvelope ((3 : ℝ) ^ M₀ + 1) y) hlim
  exact hint.const_mul (1 / (2 * Real.pi * I))

theorem tendsto_heatDilationKernel_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) (v : posUnits) :
    Tendsto (fun s => heatDilationKernel s v) (𝓝 t₁) (𝓝 (heatDilationKernel t₁ v)) :=
  (tendsto_heatForwardDilation_nhds ht₁ v).add
    ((Complex.continuous_conj.tendsto _).comp (tendsto_heatForwardDilation_nhds ht₁ v⁻¹))

/-- **Pointwise time continuity of the source-defined dilation kernel** across `(0, ∞)`. -/
theorem continuousOn_heatDilationKernel (v : posUnits) :
    ContinuousOn (fun t => heatDilationKernel t v) (Ioi 0) :=
  fun _ ht => (tendsto_heatDilationKernel_nhds ht v).continuousWithinAt

/-! ### Cleared analytic germs, residue polynomials, and Laurent evaluation -/

/-- Cleared analytic germ at a lower-half-plane zero `u` of `H_t` (`y`-independent factor). -/
def heatBaseGerm (t : ℝ) (u : ℂ) (τ : ℂ) : ℂ :=
  (u + τ - conj u) ^ zeroMult (riemannHeat t) u *
    (∏ w ∈ (heatRightZeroSet t).erase u,
      ((u + τ - conj w) / (u + τ - w)) ^ zeroMult (riemannHeat t) w) *
    cexp (-((u + τ) ^ 2))

private theorem analyticAt_finset_prod {α : Type*} (S : Finset α) (F : α → ℂ → ℂ) (z₀ : ℂ)
    (hF : ∀ a ∈ S, AnalyticAt ℂ (F a) z₀) :
    AnalyticAt ℂ (fun z => ∏ a ∈ S, F a z) z₀ := by
  classical
  induction S using Finset.induction with
  | empty =>
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z₀)
  | insert a s ha ih =>
      have heq : (fun z => ∏ b ∈ insert a s, F b z) =
          fun z => F a z * ∏ b ∈ s, F b z := by
        funext z
        exact Finset.prod_insert ha
      rw [heq]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

private theorem analyticAt_heatBaseGerm (t : ℝ) (u : ℂ) :
    AnalyticAt ℂ (heatBaseGerm t u) 0 := by
  unfold heatBaseGerm
  have h1 : AnalyticAt ℂ (fun τ : ℂ => (u + τ - conj u) ^ zeroMult (riemannHeat t) u) 0 := by
    fun_prop
  have h2 : AnalyticAt ℂ (fun τ : ℂ => ∏ w ∈ (heatRightZeroSet t).erase u,
      ((u + τ - conj w) / (u + τ - w)) ^ zeroMult (riemannHeat t) w) 0 := by
    refine analyticAt_finset_prod _ _ 0 fun w hw => ?_
    have hwu : w ≠ u := Finset.ne_of_mem_erase hw
    have hden : u + (0 : ℂ) - w ≠ 0 := by
      rw [add_zero]
      exact sub_ne_zero.mpr hwu.symm
    exact AnalyticAt.pow (AnalyticAt.div (by fun_prop) (by fun_prop) hden) _
  have h3 : AnalyticAt ℂ (fun τ : ℂ => cexp (-((u + τ) ^ 2))) 0 := by fun_prop
  exact (h1.mul h2).mul h3

private theorem heatBaseGerm_zero_ne_zero {t : ℝ} (ht : 0 < t) {u : ℂ}
    (hu : u ∈ heatRightZeroSet t) :
    heatBaseGerm t u 0 ≠ 0 := by
  obtain ⟨_, huneg⟩ := (mem_heatRightZeroSet ht).mp hu
  unfold heatBaseGerm
  have h1 : (u + 0 - conj u) ^ zeroMult (riemannHeat t) u ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [add_zero]
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have h2 : (∏ w ∈ (heatRightZeroSet t).erase u,
      ((u + 0 - conj w) / (u + 0 - w)) ^ zeroMult (riemannHeat t) w) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ ?_
    have hwu : w ≠ u := Finset.ne_of_mem_erase hw
    have hwneg : w.im < 0 := ((mem_heatRightZeroSet ht).mp (Finset.mem_of_mem_erase hw)).2
    rw [add_zero, add_zero]
    refine div_ne_zero ?_ (sub_ne_zero.mpr hwu.symm)
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  exact mul_ne_zero (mul_ne_zero h1 h2) (Complex.exp_ne_zero _)

private theorem laurentShift_heatIntegrand_eq {t : ℝ} {u : ℂ} (hu : u ∈ heatRightZeroSet t)
    (y : ℝ) :
    laurentShift (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z) u
        (zeroMult (riemannHeat t) u + 1) =
      fun τ : ℂ => τ ^ 1 * (cexp (-I * u * (y : ℂ)) *
        (heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ))) := by
  funext τ
  set m := zeroMult (riemannHeat t) u
  by_cases hτ : τ = 0
  · subst hτ
    simp [laurentShift, zero_pow (Nat.succ_ne_zero m)]
  · simp only [laurentShift, pow_one]
    unfold heatBlaschkeMeromorphic heatBaseGerm heatGaussianWave
    rw [← Finset.mul_prod_erase (heatRightZeroSet t) _ hu]
    have hsub : u + τ - u = τ := by ring
    rw [hsub, div_pow]
    have hτm : τ ^ m ≠ 0 := pow_ne_zero m hτ
    have hclear : τ ^ (m + 1) * ((u + τ - conj u) ^ m / τ ^ m) =
        τ * (u + τ - conj u) ^ m := by
      rw [pow_succ', mul_assoc, mul_div_cancel₀ _ hτm]
    have hexp : cexp (-((u + τ) ^ 2) - I * (u + τ) * (y : ℂ)) =
        cexp (-((u + τ) ^ 2)) * cexp (-I * u * (y : ℂ)) * cexp ((-I * (y : ℂ)) * τ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [hexp]
    linear_combination (∏ w ∈ (heatRightZeroSet t).erase u,
      ((u + τ - conj w) / (u + τ - w)) ^ zeroMult (riemannHeat t) w) *
      cexp (-((u + τ) ^ 2)) * cexp (-I * u * (y : ℂ)) * cexp ((-I * (y : ℂ)) * τ) * hclear

private theorem iteratedDeriv_cexp_const_mul_zero (α : ℂ) (r : ℕ) :
    iteratedDeriv r (fun τ : ℂ => cexp (α * τ)) 0 = α ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hd : deriv (fun τ : ℂ => cexp (α * τ)) = fun τ : ℂ => α * cexp (α * τ) := by
        funext τ
        have h1 : HasDerivAt (fun z : ℂ => α * z) α τ := by
          simpa using (hasDerivAt_id τ).const_mul α
        have h2 := h1.cexp
        rw [mul_comm (cexp (α * τ)) α] at h2
        exact h2.deriv
      have hcont : ContDiffAt ℂ (r : ℕ) (fun τ : ℂ => cexp (α * τ)) 0 := by fun_prop
      rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul α hcont, ih, pow_succ']

/-- The residue polynomial `P_{t, u} ∈ ℂ[X]` of degree `m_t(u) − 1` produced by the Gaussian-damped
contour integral at a lower-half-plane zero `u` of `H_t`. -/
def heatResiduePoly (t : ℝ) (u : ℂ) : ℂ[X] :=
  let d := zeroMult (riemannHeat t) u - 1
  ∑ r ∈ Finset.range (d + 1),
    Polynomial.monomial r
      (((d.choose r : ℂ) * (-I) ^ r * iteratedDeriv (d - r) (heatBaseGerm t u) 0) /
        (d.factorial : ℂ))

private theorem coeff_finset_sum {α : Type*} (S : Finset α) (P : α → ℂ[X]) (k : ℕ) :
    (∑ a ∈ S, P a).coeff k = ∑ a ∈ S, (P a).coeff k := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.coeff_add, ih, Finset.sum_insert ha]

private theorem coeff_heatResiduePoly (t : ℝ) (u : ℂ) (k : ℕ) :
    (heatResiduePoly t u).coeff k =
      let d := zeroMult (riemannHeat t) u - 1
      if k ≤ d then
        (((d.choose k : ℂ) * (-I) ^ k * iteratedDeriv (d - k) (heatBaseGerm t u) 0) /
          (d.factorial : ℂ))
      else 0 := by
  dsimp only [heatResiduePoly]
  set d := zeroMult (riemannHeat t) u - 1
  rw [coeff_finset_sum]
  by_cases hk : k ≤ d
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro r _ hrk
      rw [Polynomial.coeff_monomial, if_neg hrk]
    · intro hk_mem
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk_mem
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hrk : r ≠ k := by
      have := Finset.mem_range.mp hr
      omega
    rw [Polynomial.coeff_monomial, if_neg hrk]

theorem heatResiduePoly_ne_zero {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : u ∈ heatRightZeroSet t) :
    heatResiduePoly t u ≠ 0 := by
  set d := zeroMult (riemannHeat t) u - 1
  have hlead : (heatResiduePoly t u).coeff d ≠ 0 := by
    rw [coeff_heatResiduePoly, if_pos le_rfl]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero]
    refine div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero))
      (heatBaseGerm_zero_ne_zero ht hu)) ?_
    exact Nat.cast_ne_zero.mpr d.factorial_ne_zero
  intro h0
  rw [h0, Polynomial.coeff_zero] at hlead
  exact hlead rfl

theorem natDegree_heatResiduePoly_add_one {t : ℝ} (ht : 0 < t) {u : ℂ}
    (hu : u ∈ heatRightZeroSet t) :
    (heatResiduePoly t u).natDegree + 1 = zeroMult (riemannHeat t) u := by
  have hm1 : 1 ≤ zeroMult (riemannHeat t) u :=
    one_le_zeroMult_riemannHeat ht.le ((mem_heatRightZeroSet ht).mp hu).1
  set d := zeroMult (riemannHeat t) u - 1
  have hlead : (heatResiduePoly t u).coeff d ≠ 0 := by
    rw [coeff_heatResiduePoly, if_pos le_rfl]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero]
    refine div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero))
      (heatBaseGerm_zero_ne_zero ht hu)) ?_
    exact Nat.cast_ne_zero.mpr d.factorial_ne_zero
  have hdeg_le : (heatResiduePoly t u).natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_heatResiduePoly, if_neg (not_le.mpr hN)]
  have hdeg_eq : (heatResiduePoly t u).natDegree = d :=
    le_antisymm hdeg_le (Polynomial.le_natDegree_of_ne_zero hlead)
  omega

/-- Exact Laurent residue evaluation at a lower-half-plane zero `u ∈ heatRightZeroSet t`. -/
theorem laurentCoeff_heatBlaschke_eq_jordanForward {t : ℝ} (ht : 0 < t) {u : ℂ}
    (hu : u ∈ heatRightZeroSet t) (v : posUnits) :
    laurentCoeff (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave (logPos v) z) u (-1) =
      jordanForward u (heatResiduePoly t u) v := by
  set y : ℝ := logPos v
  set m := zeroMult (riemannHeat t) u
  have hm1 : 1 ≤ m := one_le_zeroMult_riemannHeat ht.le ((mem_heatRightZeroSet ht).mp hu).1
  set d := m - 1
  have han_base : AnalyticAt ℂ (heatBaseGerm t u) 0 := analyticAt_heatBaseGerm t u
  have han_exp : AnalyticAt ℂ (fun τ : ℂ => cexp ((-I * (y : ℂ)) * τ)) 0 := by fun_prop
  have han_inner : AnalyticAt ℂ
      (fun τ : ℂ => cexp (-I * u * (y : ℂ)) *
        (heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ))) 0 :=
    analyticAt_const.mul (han_base.mul han_exp)
  have hshift := laurentShift_heatIntegrand_eq hu y
  have han_shift : AnalyticAt ℂ
      (laurentShift (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z) u (m + 1)) 0 := by
    rw [hshift]
    exact (by fun_prop : AnalyticAt ℂ (fun τ : ℂ => τ ^ 1) 0).mul han_inner
  have hidx : (-1 + ((m + 1 : ℕ) : ℤ)).toNat = m := by omega
  rw [laurentCoeff_eq_taylorCoeffZero han_shift (by omega), hidx, hshift,
    taylorCoeffZero_pow_mul han_inner 1 m, if_pos hm1]
  have hd_eq : m - 1 = d := rfl
  rw [hd_eq, taylorCoeffZero]
  have hconst_deriv : iteratedDeriv d
      (fun τ : ℂ => cexp (-I * u * (y : ℂ)) *
        (heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ))) 0 =
      cexp (-I * u * (y : ℂ)) *
        iteratedDeriv d (fun τ : ℂ => heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ)) 0 :=
    iteratedDeriv_const_mul_field _ _
  have hleibniz : iteratedDeriv d
      (fun τ : ℂ => heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ)) 0 =
      ∑ r ∈ Finset.range (d + 1),
        (d.choose r : ℂ) * iteratedDeriv r (fun τ : ℂ => cexp ((-I * (y : ℂ)) * τ)) 0 *
          iteratedDeriv (d - r) (heatBaseGerm t u) 0 := by
    have hfun : (fun τ : ℂ => heatBaseGerm t u τ * cexp ((-I * (y : ℂ)) * τ)) =
        fun τ : ℂ => cexp ((-I * (y : ℂ)) * τ) * heatBaseGerm t u τ := by
      funext τ; ring
    rw [hfun]
    have hL := iteratedDeriv_mul (n := d) (x := (0 : ℂ))
      (f := fun τ : ℂ => cexp ((-I * (y : ℂ)) * τ)) (g := heatBaseGerm t u)
      han_exp.contDiffAt han_base.contDiffAt
    simpa [Pi.mul_def] using hL
  rw [hconst_deriv, hleibniz]
  unfold jordanForward heatResiduePoly
  rw [eval_finsetSum, Finset.sum_mul, mul_div_assoc, Finset.sum_div]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_cexp_const_mul_zero, Polynomial.eval_monomial, mul_pow]
  dsimp only [y, d, m]
  ring

/-! ### Closing the horizontal strip contour and Jordan pair decomposition -/

private theorem meromorphicAt_heatIntegrand_of_mem {t : ℝ} {u : ℂ} (hu : u ∈ heatRightZeroSet t)
    (y : ℝ) :
    MeromorphicAt (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z) u := by
  rw [meromorphicAt_iff_exists_analyticAt_laurentShift]
  refine ⟨zeroMult (riemannHeat t) u + 1, ?_⟩
  rw [laurentShift_heatIntegrand_eq hu y]
  have han_base := analyticAt_heatBaseGerm t u
  have han_exp : AnalyticAt ℂ (fun τ : ℂ => cexp ((-I * (y : ℂ)) * τ)) 0 := by fun_prop
  exact (by fun_prop : AnalyticAt ℂ (fun τ : ℂ => τ ^ 1) 0).mul
    (analyticAt_const.mul (han_base.mul han_exp))

private theorem analyticAt_heatIntegrand_of_notMem (t y : ℝ) {s : ℂ}
    (hs : s ∉ heatRightZeroSet t) :
    AnalyticAt ℂ (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z) s := by
  have hB : AnalyticAt ℂ (heatBlaschkeMeromorphic t) s := by
    unfold heatBlaschkeMeromorphic
    refine analyticAt_finset_prod _ _ s fun u hu => ?_
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr fun heq => hs (heq ▸ hu)
    exact AnalyticAt.pow (AnalyticAt.div (by fun_prop) (by fun_prop) hsu) _
  have hG : AnalyticAt ℂ (heatGaussianWave y) s := by
    unfold heatGaussianWave; fun_prop
  exact hB.mul hG

private theorem tendsto_vIntegral_heatIntegrand_zero {t : ℝ} (ht : 0 < t) (y : ℝ) (sgn : ℝ)
    (hsgn : |sgn| = 1) :
    Tendsto (fun R : ℝ =>
      VIntegral (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z) (sgn * R) (-1) 1)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  set G : ℂ → ℂ := fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z
  set R₀ : ℝ := 1 + ∑ u ∈ heatRightZeroSet t, |u.re|
  have hsum_nn : 0 ≤ ∑ u ∈ heatRightZeroSet t, |u.re| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  set C : ℝ := 2 * ((3 : ℝ) ^ heatRightZeroMultiplicity t * Real.exp (1 + |y|))
  have hgauss_zero : Tendsto (fun R : ℝ => C * Real.exp (-(R ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => -(R ^ 2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hgauss_zero
  filter_upwards [eventually_ge_atTop R₀] with R hR
  have hR1 : 1 ≤ R := by linarith
  have hpoint : ∀ τ ∈ uIoc (-1 : ℝ) 1,
      ‖G (((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
        (3 : ℝ) ^ heatRightZeroMultiplicity t * Real.exp (-(R ^ 2) + 1 + |y|) := by
    intro τ hτ
    have hτ_Icc : τ ∈ Icc (-1 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hτ
      exact Ioc_subset_Icc_self hτ
    have hτ_abs : |τ| ≤ 1 := abs_le.mpr hτ_Icc
    have hdist : ∀ u ∈ heatRightZeroSet t,
        1 / 2 ≤ ‖(((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I) - u‖ := by
      intro u hu
      have hu_le : |u.re| ≤ ∑ w ∈ heatRightZeroSet t, |w.re| :=
        Finset.single_le_sum (fun _ _ => abs_nonneg _) hu
      have hre_abs : |sgn * R - u.re| ≥ 1 := by
        have h1 : |sgn * R| - |u.re| ≤ |sgn * R - u.re| := abs_sub_abs_le_abs_sub _ _
        rw [abs_mul, hsgn, one_mul, abs_of_pos (by linarith : 0 < R)] at h1
        linarith
      have hre_eq : ((((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I) - u).re = sgn * R - u.re := by simp
      have h2 : |((((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I) - u).re| ≤
          ‖(((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I) - u‖ := Complex.abs_re_le_norm _
      rw [hre_eq] at h2
      linarith
    have hsq_sgn : (sgn * R) ^ 2 = R ^ 2 := by
      calc (sgn * R) ^ 2 = |sgn * R| ^ 2 := (sq_abs _).symm
        _ = (|sgn| * |R|) ^ 2 := by rw [abs_mul]
        _ = |R| ^ 2 := by rw [hsgn, one_mul]
        _ = R ^ 2 := sq_abs R
    dsimp only [G]
    rw [norm_mul]
    have hB := norm_heatBlaschkeMeromorphic_le ht hdist
    have hW := norm_heatGaussianWave_le y (sgn * R) τ hτ_abs
    rw [hsq_sgn] at hW
    exact mul_le_mul hB hW (norm_nonneg _) (by positivity)
  rw [VIntegral, norm_smul, norm_I, one_mul]
  calc ‖∫ τ in (-1 : ℝ)..1, G (((sgn * R : ℝ) : ℂ) + (τ : ℂ) * I)‖
      ≤ ((3 : ℝ) ^ heatRightZeroMultiplicity t * Real.exp (-(R ^ 2) + 1 + |y|)) *
          |(1 : ℝ) - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = C * Real.exp (-(R ^ 2)) := by
        have habs2 : |(1 : ℝ) - (-1)| = 2 := by norm_num
        rw [habs2]
        dsimp only [C]
        rw [show -(R ^ 2) + 1 + |y| = (1 + |y|) + -(R ^ 2) by ring, Real.exp_add]
        ring

/-- Closing the horizontal strip contour `[-R, R] × [-1, 1]` evaluates `heatForwardDilation t v`
as the sum of the Laurent residues of `B_t(z) e^{−z² − i z log v}` at `heatRightZeroSet t`. -/
theorem heatForwardDilation_eq_sum_laurentCoeff {t : ℝ} (ht : 0 < t) (v : posUnits) :
    heatForwardDilation t v =
      ∑ u ∈ heatRightZeroSet t,
        laurentCoeff (fun z => heatBlaschkeMeromorphic t z * heatGaussianWave (logPos v) z)
          u (-1) := by
  set y : ℝ := logPos v
  set G : ℂ → ℂ := fun z => heatBlaschkeMeromorphic t z * heatGaussianWave y z
  set S : ℂ := ∑ u ∈ heatRightZeroSet t, laurentCoeff G u (-1)
  set R₀ : ℝ := 1 + ∑ u ∈ heatRightZeroSet t, |u.re|
  have hsum_nn : 0 ≤ ∑ u ∈ heatRightZeroSet t, |u.re| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrect_eq : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' G (((-R : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I)
        (((R : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I) = S := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hRpos : 0 < R := by linarith
    set zR : ℂ := ((-R : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I
    set wR : ℂ := ((R : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I
    have hzR_re : zR.re = -R := by simp [zR]
    have hwR_re : wR.re = R := by simp [wR]
    have hzR_im : zR.im = -1 := by simp [zR]
    have hwR_im : wR.im = 1 := by simp [wR]
    refine rectangleIntegral'_eq_sum_laurentCoeff (by rw [hzR_re, hwR_re]; linarith)
      (by rw [hzR_im, hwR_im]; norm_num) (fun u hu => ?_)
      (fun u hu => meromorphicAt_heatIntegrand_of_mem hu y)
      (fun s _ hs => analyticAt_heatIntegrand_of_notMem t y hs)
    rw [rectangle_mem_nhds_iff, hzR_re, hwR_re, hzR_im, hwR_im,
      Set.uIoo_of_lt (by linarith : -R < R), Set.uIoo_of_lt (by norm_num : (-1 : ℝ) < 1)]
    have hu_re : |u.re| ≤ ∑ w ∈ heatRightZeroSet t, |w.re| :=
      Finset.single_le_sum (fun _ _ => abs_nonneg _) hu
    have hu_im : |u.im| < 1 / 2 :=
      abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1
    obtain ⟨hre1, hre2⟩ := abs_le.mp hu_re
    obtain ⟨him1, him2⟩ := abs_lt.mp hu_im
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- Limit of bottom and top horizontal edges as `R → +∞`
  have hbot_eq : ∀ r : ℝ, G ((r : ℂ) + ((-1 : ℝ) : ℂ) * I) =
      heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I) := by
    intro r
    have hc : (r : ℂ) + ((-1 : ℝ) : ℂ) * I = (r : ℂ) - I := by push_cast; ring
    rw [hc, ← heatLowerBlaschkeBoundary_eq ht r]
  have htop_eq : ∀ r : ℝ, G ((r : ℂ) + ((1 : ℝ) : ℂ) * I) =
      heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I) := by
    intro r
    have hc : (r : ℂ) + ((1 : ℝ) : ℂ) * I = (r : ℂ) + I := by push_cast; ring
    rw [hc, ← heatUpperBlaschkeBoundary_eq ht r]
  have hbot_lim : Tendsto (fun R : ℝ => HIntegral G (-R) R (-1)) atTop
      (𝓝 (∫ r : ℝ, heatLowerBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) - I))) := by
    have h := intervalIntegral_tendsto_integral (integrable_heatLowerTerm ht y)
      tendsto_neg_atTop_atBot tendsto_id
    refine h.congr fun R => ?_
    simp only [HIntegral, hbot_eq]
  have htop_lim : Tendsto (fun R : ℝ => HIntegral G (-R) R 1) atTop
      (𝓝 (∫ r : ℝ, heatUpperBlaschkeBoundary t r * heatGaussianWave y ((r : ℂ) + I))) := by
    have h := intervalIntegral_tendsto_integral (integrable_heatUpperTerm ht y)
      tendsto_neg_atTop_atBot tendsto_id
    refine h.congr fun R => ?_
    simp only [HIntegral, htop_eq]
  have hvR_lim : Tendsto (fun R : ℝ => VIntegral G R (-1) 1) atTop (𝓝 0) := by
    simpa [one_mul] using tendsto_vIntegral_heatIntegrand_zero ht y 1 (by norm_num)
  have hvnR_lim : Tendsto (fun R : ℝ => VIntegral G (-R) (-1) 1) atTop (𝓝 0) := by
    simpa [neg_one_mul] using tendsto_vIntegral_heatIntegrand_zero ht y (-1) (by norm_num)
  have hrect_lim : Tendsto (fun R : ℝ =>
      RectangleIntegral' G (((-R : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I)
        (((R : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I)) atTop (𝓝 (heatForwardDilation t v)) := by
    have hcomb := ((hbot_lim.sub htop_lim).add hvR_lim).sub hvnR_lim
    rw [add_zero, sub_zero, ← integral_sub (integrable_heatLowerTerm ht y)
      (integrable_heatUpperTerm ht y)] at hcomb
    have hmul := hcomb.const_mul (1 / (2 * (Real.pi : ℂ) * I))
    refine hmul.congr fun R => ?_
    simp [RectangleIntegral', RectangleIntegral, smul_eq_mul]
  exact tendsto_nhds_unique hrect_lim (tendsto_const_nhds.congr' (hrect_eq.mono fun _ h => h.symm))

/-- **Forward residue identity**: for every `t > 0`, `heatForwardDilation t` equals the sum of
forward polynomial-exponential modes over `heatRightZeroSet t`. -/
theorem heatForwardDilation_eq_sum_jordanForward {t : ℝ} (ht : 0 < t) (v : posUnits) :
    heatForwardDilation t v =
      ∑ u ∈ heatRightZeroSet t, jordanForward u (heatResiduePoly t u) v := by
  rw [heatForwardDilation_eq_sum_laurentCoeff ht v]
  exact Finset.sum_congr rfl fun u hu => laurentCoeff_heatBlaschke_eq_jordanForward ht hu v

/-- **Jordan pair kernel decomposition of `heatDilationKernel`**: for every `t > 0`, the
source-defined dilation kernel `heatDilationKernel t` equals the sum of Jordan pair kernels over
`heatRightZeroSet t` with residue polynomials of exact degree `m_t(u) − 1`. -/
theorem heatDilationKernel_eq_sum_jordanPairKernel {t : ℝ} (ht : 0 < t) (v : posUnits) :
    heatDilationKernel t v =
      ∑ u ∈ heatRightZeroSet t, jordanPairKernel u (heatResiduePoly t u) v := by
  unfold heatDilationKernel jordanPairKernel
  rw [heatForwardDilation_eq_sum_jordanForward ht v,
    heatForwardDilation_eq_sum_jordanForward ht v⁻¹, map_sum, ← Finset.sum_add_distrib]

/-- Beyond the de Bruijn–Newman upper bound `t ≥ 1/8`, `H_t` has no nonreal zeros and the
source-defined dilation kernel vanishes identically. -/
theorem heatDilationKernel_eq_zero_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) (v : posUnits) :
    heatDilationKernel t v = 0 := by
  rw [heatDilationKernel_eq_sum_jordanPairKernel (by linarith : 0 < t),
    heatRightZeroSet_eq_empty_of_eighth_le ht, Finset.sum_empty]

end GaloisForLFunctions.AdelicKreinGeometry
