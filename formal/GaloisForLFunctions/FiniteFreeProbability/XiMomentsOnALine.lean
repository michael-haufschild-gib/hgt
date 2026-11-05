import GaloisForLFunctions.FiniteFreeProbability.JensenMassConvexity
import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeHalfPlaneCriterion
import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation
import GaloisForLFunctions.RHTower.IsingSlowFieldCriticality
import GaloisForLFunctions.RHTower.DeBruijnLaguerreEvolution
import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost

/-!
# The moments of the Riemann kernel on a vertical line, and their first-order law

For `σ ≥ 1/2` and `τ = σ − 1/2`, `ξ(σ + r) = ∫ Φ(x) e^{(τ + r)x} dx` with `Φ > 0` even, so
`c_k = ξ^{(k)}(σ) = ∫ Φ(x) x^k e^{τx} dx` are nonnegative (pair `x` with `−x`) and

`m_d(t) = Σ_k C(d,k) t^{d−k} c_k = ∫ Φ(x) (t + x)^d e^{τx} dx`.

**Theorem.** With `ℓ_d = ½ log d`, for every `θ > 0`:

`(1/d) log m_d(θ ℓ_d) − log ℓ_d → log(1 + θ)`.

The upper bound is a Cauchy estimate `m_d(t) r^d/d! ≤ e^{tr} ξ(σ + r)` at the saddle
`r = d/((1 + θ)ℓ_d)`, with the Gamma cap `ξ'/ξ(1/2 + w) ≤ 3 + ½ log w`. The lower bound restricts the
integral to `[v, v + 1]` with `v = ℓ_d − log ℓ_d`, where `Φ ≥ exp(−π e^{2(v+1)})` by the first term of
its cusp series. This is the only arithmetic-free input of the Cauchy limit law: the scale `½ log d`
is Stirling's.
-/

open Filter Topology Complex MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-- `c_k = ∫ Φ(x) x^k e^{(σ−1/2)x} dx`. -/
def xiMoment (σ : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ, riemannKernelReal x * x ^ k * Real.exp ((σ - 1 / 2) * x)

theorem integrable_kernel_pow_exp (τ : ℝ) (k : ℕ) :
    Integrable fun x : ℝ => riemannKernelReal x * x ^ k * Real.exp (τ * x) := by
  refine ((riemannKernel_superExp.integrable_mul_exp (1 + |τ|)).const_mul
    (k.factorial : ℝ)).mono' ((riemannKernel_superExp.continuous.mul (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hΦ := riemannKernel_superExp.nonneg x
  have hpow : |x| ^ k ≤ (k.factorial : ℝ) * Real.exp |x| := by
    have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  have hexp : Real.exp (τ * x) ≤ Real.exp (|τ| * |x|) := by
    apply Real.exp_le_exp.2
    simpa only [abs_mul] using le_abs_self (τ * x)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΦ, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hsplit : Real.exp ((1 + |τ|) * |x|) = Real.exp |x| * Real.exp (|τ| * |x|) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  calc riemannKernelReal x * |x| ^ k * Real.exp (τ * x)
      ≤ riemannKernelReal x * ((k.factorial : ℝ) * Real.exp |x|) * Real.exp (|τ| * |x|) := by
        gcongr
    _ = _ := by ring

/-- The Taylor coefficients on `Re s = σ` are moments of `Φ`: `ξ_σ^{[k]} = i^k c_k/k!`. -/
theorem xiShiftCoeff_eq_moment (σ : ℝ) (k : ℕ) :
    xiShiftCoeff σ k = I ^ k * (xiMoment σ k : ℂ) / (k.factorial : ℂ) := by
  set τ : ℝ := σ - 1 / 2
  have hfun : (fun w : ℂ => xi ((σ : ℂ) + I * w)) = fun w => riemannHeat 0 (-(I * τ) + w) := by
    funext w
    rw [riemannHeat_zero]
    congr 1
    simp only [τ]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hder : iteratedDeriv k (fun w : ℂ => xi ((σ : ℂ) + I * w)) 0 =
      I ^ k * (xiMoment σ k : ℂ) := by
    rw [hfun, _root_.iteratedDeriv_comp_const_add, iteratedDeriv_riemannHeat_eq le_rfl]
    beta_reduce
    rw [add_zero, expTransform, xiMoment, ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [heatWeight, mul_pow, zero_mul, Real.exp_zero, mul_one]
    have hexp : Complex.exp (I * (-(I * τ)) * x) = ((Real.exp (τ * x) : ℝ) : ℂ) := by
      rw [show I * (-(I * τ)) * x = ((τ * x : ℝ) : ℂ) by
        push_cast
        ring_nf
        rw [I_sq]
        ring, Complex.ofReal_exp]
    rw [hexp]
    simp only [τ]
    push_cast
    ring
  rw [xiShiftCoeff, hder]

theorem xi_ofReal_eq_moment (σ : ℝ) : xi (σ : ℂ) = (xiMoment σ 0 : ℂ) := by
  have h := xiShiftCoeff_eq_moment σ 0
  simpa [xiShiftCoeff] using h

theorem xiMoment_zero_pos (σ : ℝ) : 0 < xiMoment σ 0 := by
  have h0 : 0 ≤ xiMoment σ 0 := integral_nonneg fun x => by
    have := riemannKernel_superExp.nonneg x
    positivity
  refine lt_of_le_of_ne h0 fun h => xi_ne_zero_of_real σ ?_
  rw [xi_ofReal_eq_moment, ← h, Complex.ofReal_zero]

/-! ## Positivity by reflection -/

/-- `e^{τx}(t + x)^d + e^{−τx}(t − x)^d ≥ 0` for `t, τ ≥ 0`. -/
theorem reflected_pow_nonneg {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t) (d : ℕ) (x : ℝ) :
    0 ≤ Real.exp (τ * x) * (t + x) ^ d + Real.exp (-(τ * x)) * (t - x) ^ d := by
  have main : ∀ y : ℝ, 0 ≤ y → 0 ≤ Real.exp (τ * y) * (t + y) ^ d +
      Real.exp (-(τ * y)) * (t - y) ^ d := fun y hy => by
    have hA : 0 ≤ t + y := by linarith
    have hB : |t - y| ≤ t + y := abs_le.2 ⟨by linarith, by linarith⟩
    have h1 : -|t - y| ^ d ≤ (t - y) ^ d := by
      have := neg_abs_le ((t - y) ^ d)
      rwa [abs_pow] at this
    have h2 : |t - y| ^ d ≤ (t + y) ^ d := pow_le_pow_left₀ (abs_nonneg _) hB d
    have h3 : Real.exp (-(τ * y)) ≤ Real.exp (τ * y) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ hy])
    have h4 := Real.exp_pos (-(τ * y))
    have h5 : 0 ≤ (t + y) ^ d := pow_nonneg hA d
    nlinarith [mul_le_mul_of_nonneg_right h3 h5, mul_le_mul_of_nonneg_left h1 h4.le,
      mul_le_mul_of_nonneg_left h2 h4.le]
  rcases le_total 0 x with hx | hx
  · exact main x hx
  · have := main (-x) (by linarith)
    rw [show τ * -x = -(τ * x) by ring, neg_neg, show t + -x = t - x by ring,
      show t - -x = t + x by ring] at this
    linarith

/-- Reflection of the even kernel. -/
theorem integral_kernel_reflect (g : ℝ → ℝ) :
    ∫ x : ℝ, riemannKernelReal x * g (-x) = ∫ x : ℝ, riemannKernelReal x * g x := by
  have := integral_neg_eq_self (fun x : ℝ => riemannKernelReal x * g x) volume
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [riemannKernel_superExp.even x]

/-- The `d`-th moment of `t + V` as an integral. -/
theorem jensenMass_xiMoment (σ : ℝ) (d : ℕ) (t : ℝ) :
    jensenMass (xiMoment σ) d t =
      ∫ x : ℝ, riemannKernelReal x * ((t + x) ^ d * Real.exp ((σ - 1 / 2) * x)) := by
  have hexp : ∀ x : ℝ, riemannKernelReal x * ((t + x) ^ d * Real.exp ((σ - 1 / 2) * x)) =
      ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) * t ^ (d - k) *
        (riemannKernelReal x * x ^ k * Real.exp ((σ - 1 / 2) * x)) := fun x => by
    rw [add_comm t x, add_pow, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => (integrable_kernel_pow_exp _ k).const_mul _, jensenMass]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, xiMoment]

theorem integrable_kernel_add_pow_exp (τ t : ℝ) (d : ℕ) :
    Integrable fun x : ℝ => riemannKernelReal x * ((t + x) ^ d * Real.exp (τ * x)) := by
  have hexp : ∀ x : ℝ, riemannKernelReal x * ((t + x) ^ d * Real.exp (τ * x)) =
      ∑ k ∈ Finset.range (d + 1), (d.choose k : ℝ) * t ^ (d - k) *
        (riemannKernelReal x * x ^ k * Real.exp (τ * x)) := fun x => by
    rw [add_comm t x, add_pow, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ fun k _ => (integrable_kernel_pow_exp τ k).const_mul _

/-- Twice the mass is the integral of the reflected integrand. -/
theorem two_mul_jensenMass (σ : ℝ) (d : ℕ) (t : ℝ) :
    2 * jensenMass (xiMoment σ) d t = ∫ x : ℝ, riemannKernelReal x *
      (Real.exp ((σ - 1 / 2) * x) * (t + x) ^ d + Real.exp (-((σ - 1 / 2) * x)) * (t - x) ^ d) := by
  have h1 := jensenMass_xiMoment σ d t
  have h2 := integral_kernel_reflect (fun x => (t + x) ^ d * Real.exp ((σ - 1 / 2) * x))
  have hi1 := integrable_kernel_add_pow_exp (σ - 1 / 2) t d
  have hi2 : Integrable fun x : ℝ => riemannKernelReal x *
      ((t + -x) ^ d * Real.exp ((σ - 1 / 2) * -x)) := by
    have := hi1.comp_neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [riemannKernel_superExp.even x]
  have hsum : (fun x : ℝ => riemannKernelReal x * (Real.exp ((σ - 1 / 2) * x) * (t + x) ^ d +
      Real.exp (-((σ - 1 / 2) * x)) * (t - x) ^ d)) =
      fun x : ℝ => riemannKernelReal x * ((t + x) ^ d * Real.exp ((σ - 1 / 2) * x)) +
        riemannKernelReal x * ((t + -x) ^ d * Real.exp ((σ - 1 / 2) * -x)) := by
    funext x
    rw [show (σ - 1 / 2) * -x = -((σ - 1 / 2) * x) by ring, show t + -x = t - x by ring]
    ring
  rw [hsum, integral_add hi1 hi2, h2, ← h1]
  ring

theorem xiMoment_nonneg {σ : ℝ} (hσ : 1 / 2 ≤ σ) (k : ℕ) : 0 ≤ xiMoment σ k := by
  have hmass : jensenMass (xiMoment σ) k 0 = xiMoment σ k := by
    rw [jensenMass, Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => by
      have : k - j ≠ 0 := by have := Finset.mem_range.1 hj; omega
      rw [zero_pow this]
      ring]
    simp
  have h2 := two_mul_jensenMass σ k 0
  rw [hmass] at h2
  have hnn : 0 ≤ ∫ x : ℝ, riemannKernelReal x * (Real.exp ((σ - 1 / 2) * x) * (0 + x) ^ k +
      Real.exp (-((σ - 1 / 2) * x)) * (0 - x) ^ k) := integral_nonneg fun x =>
    mul_nonneg (riemannKernel_superExp.nonneg x)
      (reflected_pow_nonneg (by linarith) le_rfl k x)
  linarith

/-! ## The lower bound -/

/-- `Φ(x) ≥ exp(−π e^{2x})` for `x ≥ 1`: the first term of the cusp series. -/
theorem riemannKernelReal_ge {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-(Real.pi * Real.exp (2 * x))) ≤ riemannKernelReal x := by
  have hx0 : 0 ≤ x := by linarith
  have hle := (summable_cuspTerm riemannCuspPoly x).le_tsum 0
    (fun j _ => (cuspTerm_riemannCuspPoly_pos (by omega) hx0).le)
  have hk : riemannKernelReal x = cuspSeries riemannCuspPoly x := by
    rw [riemannKernelReal, abs_of_nonneg hx0]
  rw [hk]
  refine le_trans ?_ hle
  have hY : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  have hp := riemannCuspPoly_eval_ge hY
  have hπ := Real.pi_gt_three
  have hR : 1 ≤ riemannCuspPoly.eval (Real.exp (2 * x)) := by
    have hπ2 : 9 ≤ Real.pi ^ 2 := by nlinarith
    have hY2 : 1 ≤ Real.exp (2 * x) ^ 2 := one_le_pow₀ hY
    nlinarith
  have hE : 1 ≤ Real.exp (x / 2) := Real.one_le_exp (by linarith)
  simp only [cuspTerm, Nat.cast_one, zero_add, one_pow, one_mul]
  have hexp := Real.exp_pos (-Real.pi * Real.exp (2 * x))
  rw [show -(Real.pi * Real.exp (2 * x)) = -Real.pi * Real.exp (2 * x) by ring]
  exact le_mul_of_one_le_left hexp.le (one_le_mul_of_one_le_of_one_le hE hR)

/-- **Lower bound.** For `σ ≥ 1/2`, `t, v ≥ 1`: `m_{d+1}(t) ≥ (t + v)^d exp(−π e^{2(v+1)})`. -/
theorem jensenMass_ge {σ : ℝ} (hσ : 1 / 2 ≤ σ) (d : ℕ) {t v : ℝ} (ht : 1 ≤ t) (hv : 1 ≤ v) :
    (t + v) ^ d * Real.exp (-(Real.pi * Real.exp (2 * (v + 1)))) ≤
      jensenMass (xiMoment σ) (d + 1) t := by
  set τ : ℝ := σ - 1 / 2
  have hτ : 0 ≤ τ := by simp only [τ]; linarith
  set F : ℝ → ℝ := fun x => riemannKernelReal x *
    (Real.exp (τ * x) * (t + x) ^ (d + 1) + Real.exp (-(τ * x)) * (t - x) ^ (d + 1))
  have hF0 : ∀ x, 0 ≤ F x := fun x => mul_nonneg (riemannKernel_superExp.nonneg x)
    (reflected_pow_nonneg hτ (by linarith) _ x)
  have hFint : Integrable F := by
    have h1 := integrable_kernel_add_pow_exp τ t (d + 1)
    have h2 := h1.comp_neg
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [F, Pi.add_apply, riemannKernel_superExp.even x]
    rw [show τ * -x = -(τ * x) by ring, show t + -x = t - x by ring]
    ring
  set c₀ : ℝ := (t + v) ^ d * Real.exp (-(Real.pi * Real.exp (2 * (v + 1))))
  have hlower : ∀ x ∈ Set.Icc v (v + 1), 2 * c₀ ≤ F x := fun x hx => by
    have hx1 : 1 ≤ x := hv.trans hx.1
    have hΦ := riemannKernelReal_ge hx1
    have hexpΦ : Real.exp (-(Real.pi * Real.exp (2 * (v + 1)))) ≤ riemannKernelReal x := by
      refine le_trans (Real.exp_le_exp.2 ?_) hΦ
      have : Real.exp (2 * x) ≤ Real.exp (2 * (v + 1)) := Real.exp_le_exp.2 (by linarith [hx.2])
      nlinarith [Real.pi_pos]
    -- `(t + x)^{d+1} − |t − x|^{d+1} ≥ 2 (t + v)^d`
    have hA : 0 ≤ t + x := by linarith
    have hB : |t - x| ≤ t + x - 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hpow1 : (t + v) ^ d ≤ (t + x) ^ d := pow_le_pow_left₀ (by linarith) (by linarith [hx.1]) d
    have hbpow : |t - x| ^ (d + 1) ≤ (t + x) ^ d * (t + x - 2) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) d) hB (abs_nonneg _)
        (pow_nonneg hA d)
    have hneg : -|t - x| ^ (d + 1) ≤ (t - x) ^ (d + 1) := by
      have := neg_abs_le ((t - x) ^ (d + 1))
      rwa [abs_pow] at this
    have hexp1 : 1 ≤ Real.exp (τ * x) := Real.one_le_exp (by nlinarith)
    have hexp2 : Real.exp (-(τ * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hexp3 := Real.exp_pos (-(τ * x))
    have hTpos : 0 ≤ (t + x) ^ (d + 1) := pow_nonneg hA _
    have hS : 2 * (t + v) ^ d ≤
        Real.exp (τ * x) * (t + x) ^ (d + 1) + Real.exp (-(τ * x)) * (t - x) ^ (d + 1) := by
      have e1 : (t + x) ^ (d + 1) ≤ Real.exp (τ * x) * (t + x) ^ (d + 1) :=
        le_mul_of_one_le_left hTpos hexp1
      have habs : 0 ≤ |t - x| ^ (d + 1) := by positivity
      have e2 : -|t - x| ^ (d + 1) ≤ Real.exp (-(τ * x)) * (t - x) ^ (d + 1) := by
        calc -|t - x| ^ (d + 1) ≤ -(Real.exp (-(τ * x)) * |t - x| ^ (d + 1)) := by
              nlinarith [mul_le_mul_of_nonneg_right hexp2 habs]
          _ = Real.exp (-(τ * x)) * -|t - x| ^ (d + 1) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hneg hexp3.le
      have e3 : (t + x) ^ (d + 1) = (t + x) ^ d * (t + x) := pow_succ _ _
      nlinarith
    have hmul := mul_le_mul hexpΦ hS (by positivity) (riemannKernel_superExp.nonneg x)
    simp only [F, c₀]
    nlinarith [hmul]
  have hset : ∫ x in Set.Icc v (v + 1), 2 * c₀ ≤ ∫ x in Set.Icc v (v + 1), F x :=
    setIntegral_mono_on continuousOn_const.integrableOn_Icc hFint.integrableOn measurableSet_Icc
      hlower
  have hconst : ∫ _x in Set.Icc v (v + 1), 2 * c₀ = 2 * c₀ := by
    simp
  have hfull : ∫ x in Set.Icc v (v + 1), F x ≤ ∫ x, F x :=
    setIntegral_le_integral hFint (Eventually.of_forall hF0)
  have h2 := two_mul_jensenMass σ (d + 1) t
  simp only [τ] at *
  change _ ≤ _ at hfull
  have hF : ∫ x, F x = 2 * jensenMass (xiMoment σ) (d + 1) t := h2.symm
  rw [hconst] at hset
  linarith

/-! ## The upper bound -/

/-- The Taylor series of `ξ` at a real point, on the real axis. -/
theorem hasSum_xiMoment (σ r : ℝ) :
    HasSum (fun k => xiMoment σ k * r ^ k / (k.factorial : ℝ)) (xiMoment (σ + r) 0) := by
  have h := hasSum_xiShiftCoeff σ (-(I * r))
  have harg : (σ : ℂ) + I * -(I * r) = ((σ + r : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [harg, xi_ofReal_eq_moment] at h
  have hterm : ∀ k, xiShiftCoeff σ k * (-(I * r)) ^ k =
      ((xiMoment σ k * r ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := fun k => by
    rw [xiShiftCoeff_eq_moment, neg_pow, mul_pow]
    have hI : I ^ k * ((-1 : ℂ) ^ k * I ^ k) = 1 := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow, mul_neg_one, neg_mul, I_mul_I, neg_neg, one_pow]
    push_cast
    linear_combination ((xiMoment σ k : ℂ) * (r : ℂ) ^ k / (k.factorial : ℂ)) * hI
  simp_rw [hterm] at h
  exact Complex.hasSum_ofReal.1 h

/-- **Cauchy estimate.** `m_d(t) r^d/d! ≤ e^{tr} ξ(σ + r)` for `t, r ≥ 0`, `σ ≥ 1/2`. -/
theorem jensenMass_mul_pow_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (d : ℕ) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    jensenMass (xiMoment σ) d t * r ^ d / (d.factorial : ℝ) ≤
      Real.exp (t * r) * xiMoment (σ + r) 0 := by
  have hnn : ∀ k, 0 ≤ xiMoment σ k * r ^ k / (k.factorial : ℝ) := fun k => by
    have := xiMoment_nonneg hσ k
    positivity
  have hpart := sum_le_hasSum (Finset.range (d + 1)) (fun k _ => hnn k) (hasSum_xiMoment σ r)
  have hexpb : ∀ j : ℕ, (t * r) ^ j / (j.factorial : ℝ) ≤ Real.exp (t * r) := fun j =>
    Real.pow_div_factorial_le_exp _ (mul_nonneg ht hr) j
  have hsplit : jensenMass (xiMoment σ) d t * r ^ d / (d.factorial : ℝ) =
      ∑ k ∈ Finset.range (d + 1), ((t * r) ^ (d - k) / ((d - k).factorial : ℝ)) *
        (xiMoment σ k * r ^ k / (k.factorial : ℝ)) := by
    rw [jensenMass, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hch : (d.choose k : ℝ) * (k.factorial : ℝ) * ((d - k).factorial : ℝ) = d.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
    have hrp : r ^ d = r ^ (d - k) * r ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
    have h1 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have h2 : ((d - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have h3 : (d.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk').ne'
    rw [hrp, mul_pow, ← hch]
    field_simp
  rw [hsplit]
  calc _ ≤ ∑ k ∈ Finset.range (d + 1), Real.exp (t * r) *
        (xiMoment σ k * r ^ k / (k.factorial : ℝ)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hexpb _) (hnn k)
    _ = Real.exp (t * r) * ∑ k ∈ Finset.range (d + 1), xiMoment σ k * r ^ k / (k.factorial : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpart (Real.exp_pos _).le

/-- The Gamma cap on the real axis: `log ξ(1/2 + w) ≤ log ξ(3/2) + w (3 + ½ log w)` for `w ≥ 1`. -/
theorem log_xiMoment_le {w : ℝ} (hw : 1 ≤ w) :
    Real.log (xiMoment (1 / 2 + w) 0) ≤
      Real.log (xiMoment (1 / 2 + 1) 0) + w * (3 + Real.log w / 2) := by
  set f : ℝ → ℝ := fun u => Real.log (xiMoment (1 / 2 + u) 0)
  have hval : ∀ u : ℝ, xi (1 / 2 + (u : ℂ)) = (xiMoment (1 / 2 + u) 0 : ℂ) := fun u => by
    rw [← xi_ofReal_eq_moment]
    push_cast
    rfl
  have hd : ∀ u : ℝ, HasDerivAt f (xiRealLogDeriv u) u := fun u => by
    have h1 : HasDerivAt (fun z : ℂ => xi (1 / 2 + z)) (deriv xi (1 / 2 + (u : ℂ))) (u : ℂ) :=
      (xi_differentiable (1 / 2 + (u : ℂ))).hasDerivAt.comp_const_add (1 / 2) (u : ℂ)
    have h2 := h1.real_of_complex
    have hre : ∀ v : ℝ, (xi (1 / 2 + (v : ℂ))).re = xiMoment (1 / 2 + v) 0 := fun v => by
      rw [hval, ofReal_re]
    simp_rw [hre] at h2
    have h3 := h2.log (xiMoment_zero_pos (1 / 2 + u)).ne'
    have hrld : xiRealLogDeriv u = (deriv xi (1 / 2 + (u : ℂ))).re / xiMoment (1 / 2 + u) 0 := by
      rw [xiRealLogDeriv, logDeriv_apply, hval, Complex.div_ofReal_re]
    rw [hrld]
    exact h3
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  have hderiv : ∀ x ∈ interior (Set.Icc 1 w), deriv f x ≤ 3 + Real.log w / 2 := fun x hx => by
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have h := GriffithsSimon.xiRealLogDeriv_le_log hx.1.le
    have hmono : Real.log x ≤ Real.log w := Real.log_le_log (by linarith [hx.1]) hx.2.le
    linarith
  have hmvt := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc 1 w) hcont.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) hderiv 1
    (Set.left_mem_Icc.2 hw) w (Set.right_mem_Icc.2 hw) hw
  simp only [f] at hmvt
  have hC : 0 ≤ 3 + Real.log w / 2 := by linarith
  nlinarith

/-! ## The first-order law -/

theorem jensenMass_pos {σ : ℝ} (hσ : 1 / 2 ≤ σ) (d : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    0 < jensenMass (xiMoment σ) d t := by
  rcases d with _ | d
  · simpa [jensenMass] using xiMoment_zero_pos σ
  · refine lt_of_lt_of_le ?_ (jensenMass_ge hσ d ht le_rfl)
    have : 0 < t + 1 := by linarith
    positivity

/-- The scale `ℓ_d = ½ log d`. -/
def cauchyScale (d : ℕ) : ℝ := Real.log d / 2

theorem tendsto_cauchyScale : Tendsto cauchyScale atTop atTop :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)

theorem tendsto_cauchyScale_div : Tendsto (fun d : ℕ => cauchyScale d / d) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 two_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun d => ?_
  simp only [Function.comp_apply, cauchyScale, pow_one, add_zero]
  rw [div_div, mul_comm]

theorem tendsto_one_div_cauchyScale : Tendsto (fun d : ℕ => 1 / cauchyScale d) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_cauchyScale

theorem tendsto_log_cauchyScale_div :
    Tendsto (fun d : ℕ => Real.log (cauchyScale d) / cauchyScale d) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_cauchyScale
  refine h.congr fun d => ?_
  simp [Function.comp_apply]

/-- `log m_d(θℓ_d)/d − log ℓ_d − log(1 + θ)` is bounded above by a null sequence. -/
theorem log_jensenMass_div_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ d : ℕ in atTop,
      Real.log (jensenMass (xiMoment σ) d (θ * cauchyScale d)) / d - Real.log (cauchyScale d) -
          Real.log (1 + θ) ≤
        (σ - 1 / 2) * 3 / d + (σ - 1 / 2) * (cauchyScale d / d) + 3 / (1 + θ) * (1 / cauchyScale d) +
          (1 + Real.log (xiMoment (1 / 2 + 1) 0)) / d + cauchyScale d / d := by
  set τ : ℝ := σ - 1 / 2
  have hτ : 0 ≤ τ := by simp only [τ]; linarith
  set K := Real.log (xiMoment (1 / 2 + 1) 0)
  have h1θ : 0 < 1 + θ := by linarith
  filter_upwards [tendsto_cauchyScale.eventually_ge_atTop 1,
    tendsto_cauchyScale.eventually_ge_atTop (1 / θ),
    tendsto_cauchyScale_div.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (1 + θ))),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (τ * (1 + θ) / θ),
    eventually_ge_atTop 1] with d hℓ1 hℓθ hℓd hdτ hd1
  set ℓ := cauchyScale d
  have hℓ : 0 < ℓ := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have ht1 : 1 ≤ θ * ℓ := by
    rw [div_le_iff₀ hθ] at hℓθ
    linarith
  set r : ℝ := d / ((1 + θ) * ℓ)
  have hdenom : 0 < (1 + θ) * ℓ := by positivity
  have hr1 : 1 ≤ r := by
    rw [le_div_iff₀ hdenom]
    rw [div_lt_div_iff₀ hdR h1θ] at hℓd
    linarith
  set w : ℝ := τ + r
  have hw1 : 1 ≤ w := by simp only [w]; linarith
  have hwd : w ≤ d := by
    have hrle : r ≤ d / (1 + θ) := by
      simp only [r]
      refine div_le_div_of_nonneg_left hdR.le h1θ ?_
      nlinarith
    have hτle : τ ≤ d * (θ / (1 + θ)) := by
      rw [div_le_iff₀ hθ] at hdτ
      rw [mul_div_assoc', le_div_iff₀ h1θ]
      linarith
    have hsplit : d * (θ / (1 + θ)) + d / (1 + θ) = (d : ℝ) := by
      field_simp
      ring
    simp only [w]
    linarith
  have hσw : σ + r = 1 / 2 + w := by simp only [w, τ]; ring
  have hm := jensenMass_pos hσ d ht1
  set A := jensenMass (xiMoment σ) d (θ * ℓ)
  have hC := jensenMass_mul_pow_le hσ d (t := θ * ℓ) (r := r) (by positivity) (by linarith)
  rw [hσw] at hC
  have hξ := xiMoment_zero_pos (1 / 2 + w)
  have hfact : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  have hrpos : 0 < r := by linarith
  have hlog := Real.log_le_log (by positivity) hC
  rw [Real.log_div (by positivity) hfact.ne', Real.log_mul hm.ne' (by positivity), Real.log_pow,
    Real.log_mul (Real.exp_pos _).ne' hξ.ne', Real.log_exp] at hlog
  have hcap := log_xiMoment_le hw1
  have hlogw : Real.log w ≤ Real.log d := Real.log_le_log (by linarith) hwd
  have hcap2 : w * (3 + Real.log w / 2) ≤ w * (3 + ℓ) :=
    mul_le_mul_of_nonneg_left (by simp only [ℓ, cauchyScale]; linarith) (by linarith)
  have hfac := (GaloisForLFunctions.ArithmeticOfSquareRootPrecision.log_factorial_sub_bounds hd1).2
  have hlogr : Real.log r = Real.log d - Real.log (1 + θ) - Real.log ℓ := by
    simp only [r]
    rw [Real.log_div hdR.ne' hdenom.ne', Real.log_mul h1θ.ne' hℓ.ne']
    ring
  have e1 : θ * ℓ * r = d * (θ / (1 + θ)) := by
    simp only [r]
    field_simp
  have e2 : r * ℓ = d / (1 + θ) := by
    simp only [r]
    field_simp
  have e3 : d * (θ / (1 + θ)) + d / (1 + θ) = (d : ℝ) := by
    field_simp
    ring
  have e4 : w * (3 + ℓ) = τ * 3 + τ * ℓ + 3 * r + r * ℓ := by
    simp only [w]
    ring
  have hlogd : Real.log d / 2 = ℓ := rfl
  rw [hlogr] at hlog
  have hmain : Real.log A ≤ K + τ * 3 + τ * ℓ + 3 * r + 1 + ℓ +
      d * Real.log (1 + θ) + d * Real.log ℓ := by
    have e5 : (d : ℝ) * (Real.log d - Real.log (1 + θ) - Real.log ℓ) =
        d * Real.log d - d * Real.log (1 + θ) - d * Real.log ℓ := by ring
    rw [e5, e1] at hlog
    rw [e4, e2] at hcap2
    have hfac' : Real.log (d.factorial : ℝ) ≤ d * Real.log d - d + (1 + Real.log d / 2) := by
      linarith
    rw [hlogd] at hfac'
    linarith
  have hr3 : 3 * r / d = 3 / (1 + θ) * (1 / ℓ) := by
    simp only [r]
    field_simp
  have hfinal : Real.log A / d ≤ τ * 3 / d + τ * (ℓ / d) + 3 / (1 + θ) * (1 / ℓ) +
      (1 + K) / d + ℓ / d + Real.log ℓ + Real.log (1 + θ) := by
    rw [← hr3, div_le_iff₀ hdR]
    have hexpand : (τ * 3 / d + τ * (ℓ / d) + 3 * r / d + (1 + K) / d + ℓ / d + Real.log ℓ +
        Real.log (1 + θ)) * d = τ * 3 + τ * ℓ + 3 * r + (1 + K) + ℓ + d * Real.log ℓ +
          d * Real.log (1 + θ) := by
      field_simp
    rw [hexpand]
    linarith
  linarith

/-- `log m_d(θℓ_d)/d − log ℓ_d − log(1 + θ)` is bounded below by a null sequence. -/
theorem le_log_jensenMass_div {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ d : ℕ in atTop,
      Real.log (1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ)) -
          (1 + θ) * (cauchyScale d / d) - Real.pi * Real.exp 2 * (1 / cauchyScale d) ^ 2 ≤
        Real.log (jensenMass (xiMoment σ) d (θ * cauchyScale d)) / d - Real.log (cauchyScale d) -
          Real.log (1 + θ) := by
  have h1θ : 0 < 1 + θ := by linarith
  filter_upwards [tendsto_cauchyScale.eventually_ge_atTop 2,
    tendsto_cauchyScale.eventually_ge_atTop (1 / θ), eventually_ge_atTop 1] with d hℓ2 hℓθ hd1
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 1 := ⟨d - 1, by omega⟩
  set d := D + 1
  set ℓ := cauchyScale d
  have hℓ : 0 < ℓ := by linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by positivity
  have ht1 : 1 ≤ θ * ℓ := by
    rw [div_le_iff₀ hθ] at hℓθ
    linarith
  have hlogℓ : Real.log ℓ ≤ ℓ / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := ℓ / 2) (by positivity)
    rw [Real.log_div hℓ.ne' two_ne_zero] at h
    have := Real.log_two_lt_d9
    linarith
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  set v := ℓ - Real.log ℓ
  have hv1 : 1 ≤ v := by simp only [v]; linarith
  set X := θ * ℓ + v
  have hX : 0 < X := by simp only [X]; linarith
  have hge := jensenMass_ge hσ D ht1 hv1
  set A := jensenMass (xiMoment σ) (D + 1) (θ * ℓ)
  have hA := jensenMass_pos hσ (D + 1) ht1
  have hlog := Real.log_le_log (by positivity) hge
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at hlog
  -- `e^{2(v+1)} = e² d/ℓ²`
  have hexp : Real.exp (2 * (v + 1)) = Real.exp 2 * ((d : ℝ) * (1 / ℓ) ^ 2) := by
    have hd : Real.exp (2 * ℓ) = (d : ℝ) := by
      rw [show 2 * ℓ = Real.log d by simp only [ℓ, cauchyScale]; ring, Real.exp_log hdR]
    have hl : Real.exp (-(2 * Real.log ℓ)) = (1 / ℓ) ^ 2 := by
      rw [show -(2 * Real.log ℓ) = Real.log ((1 / ℓ) ^ 2) by
        rw [Real.log_pow, one_div, Real.log_inv]
        push_cast
        ring, Real.exp_log (by positivity)]
    rw [show 2 * (v + 1) = 2 + (2 * ℓ + -(2 * Real.log ℓ)) by simp only [v]; ring, Real.exp_add,
      Real.exp_add, hd, hl]
  rw [hexp] at hlog
  -- factor the base
  have hXeq : X = (1 + θ) * ℓ * (1 - Real.log ℓ / ℓ / (1 + θ)) := by
    simp only [X, v]
    field_simp
    ring
  have hu : 0 < 1 - Real.log ℓ / ℓ / (1 + θ) := by
    have h := hX
    rw [hXeq] at h
    exact (pos_iff_pos_of_mul_pos h).1 (by positivity)
  have hlogX : Real.log X = Real.log (1 + θ) + Real.log ℓ +
      Real.log (1 - Real.log ℓ / ℓ / (1 + θ)) := by
    rw [hXeq, Real.log_mul (by positivity) hu.ne', Real.log_mul h1θ.ne' hℓ.ne']
  have hlogXle : Real.log X ≤ (1 + θ) * ℓ := by
    have h := Real.log_le_sub_one_of_pos hX
    simp only [X, v] at h ⊢
    nlinarith
  have hcast : ((D : ℝ)) = (d : ℝ) - 1 := by
    simp only [d]
    push_cast
    ring
  rw [hcast] at hlog
  have hmain : Real.log X - (1 + θ) * (ℓ / d) - Real.pi * Real.exp 2 * (1 / ℓ) ^ 2 ≤
      Real.log A / d := by
    rw [le_div_iff₀ hdR]
    have hexpand : (Real.log X - (1 + θ) * (ℓ / d) - Real.pi * Real.exp 2 * (1 / ℓ) ^ 2) * d =
        d * Real.log X - (1 + θ) * ℓ - Real.pi * (Real.exp 2 * (d * (1 / ℓ) ^ 2)) := by
      field_simp
    rw [hexpand]
    nlinarith
  rw [hlogX] at hmain
  linarith

/-- **The first-order law.** For `σ ≥ 1/2` and `θ > 0`:
`(1/d) log m_d(θ ℓ_d) − log ℓ_d → log(1 + θ)`, with `ℓ_d = ½ log d`. -/
theorem tendsto_log_jensenMass {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun d : ℕ => Real.log (jensenMass (xiMoment σ) d (θ * cauchyScale d)) / d -
      Real.log (cauchyScale d)) atTop (𝓝 (Real.log (1 + θ))) := by
  have h1θ : 0 < 1 + θ := by linarith
  have hinv : Tendsto (fun d : ℕ => (1 : ℝ) / d) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hupper : Tendsto (fun d : ℕ => (σ - 1 / 2) * 3 / d + (σ - 1 / 2) * (cauchyScale d / d) +
      3 / (1 + θ) * (1 / cauchyScale d) + (1 + Real.log (xiMoment (1 / 2 + 1) 0)) / d +
        cauchyScale d / d) atTop (𝓝 0) := by
    have := (((tendsto_const_div_atTop_nhds_zero_nat ((σ - 1 / 2) * 3)).add
      (tendsto_cauchyScale_div.const_mul (σ - 1 / 2))).add
      (tendsto_one_div_cauchyScale.const_mul (3 / (1 + θ)))).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 + Real.log (xiMoment (1 / 2 + 1) 0))) |>.add
      tendsto_cauchyScale_div
    simpa using this
  have hlower : Tendsto (fun d : ℕ =>
      Real.log (1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ)) -
        (1 + θ) * (cauchyScale d / d) - Real.pi * Real.exp 2 * (1 / cauchyScale d) ^ 2)
      atTop (𝓝 0) := by
    have hu : Tendsto (fun d : ℕ => 1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ)) atTop
        (𝓝 1) := by
      have := (tendsto_log_cauchyScale_div.div_const (1 + θ)).const_sub 1
      simpa using this
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hu
    rw [Real.log_one] at hlog
    have := (hlog.sub (tendsto_cauchyScale_div.const_mul (1 + θ))).sub
      ((tendsto_one_div_cauchyScale.pow 2).const_mul (Real.pi * Real.exp 2))
    simpa [Function.comp_def] using this
  have hsq := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (le_log_jensenMass_div hσ hθ) (log_jensenMass_div_le hσ hθ)
  have := hsq.add_const (Real.log (1 + θ))
  simpa using this

/-- **The ratio law.** `ℓ_{d+1} m_d(θ ℓ_{d+1})/m_{d+1}(θ ℓ_{d+1}) → 1/(1 + θ)`. -/
theorem tendsto_cauchy_ratio {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun d : ℕ => cauchyScale (d + 1) *
      jensenMass (xiMoment σ) d (θ * cauchyScale (d + 1)) /
        jensenMass (xiMoment σ) (d + 1) (θ * cauchyScale (d + 1))) atTop (𝓝 (1 / (1 + θ))) := by
  refine tendsto_ratio_of_tendsto_log (xiMoment_nonneg hσ)
    (tendsto_cauchyScale.eventually_gt_atTop 0) (fun θ' hθ' => tendsto_log_jensenMass hσ hθ')
    (fun θ' hθ' => ?_) hθ
  filter_upwards [tendsto_cauchyScale.eventually_ge_atTop (1 / θ')] with d hd
  refine jensenMass_pos hσ d ?_
  rw [div_le_iff₀ hθ'] at hd
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.xiShiftCoeff_eq_moment
#print axioms FiniteFreeProbability.tendsto_log_jensenMass
#print axioms FiniteFreeProbability.tendsto_cauchy_ratio
