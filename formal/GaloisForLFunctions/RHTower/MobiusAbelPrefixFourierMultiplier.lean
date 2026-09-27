import GaloisForLFunctions.RHTower.MobiusAbelPrefixGramIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.ExpDecay
import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin

/-!
# Logarithmic Fourier multiplier of the Abel-prefix Gram

In logarithmic frequency coordinates the mixed Gram `G_δ` becomes a convolution kernel

`H_δ(r) = e^((a+1) r) G_δ(e^r, 1)`,   `a = (1+δ)/2`,

and the Möbius prefix becomes `b_N(u) = e^(-a u) P_N(e^u)` on `u ≥ 0`.  This module proves that
the finite source energy is the exact double integral of `b_N ⊗ b_N` against `H_δ(u - v)`, that
the Fourier transform of `H_δ` is the strictly positive multiplier
`(a² + τ²) |Γ(p/2 + iτ)|² / Γ(p)`, `p = 5+δ`, that the frozen prefix has transform
`(a + iτ)⁻¹ Σ_{n ≤ N} μ(n) n^(-a-iτ)`, and the Mellin--Plancherel identity for the energy.

The Fourier transform of `H_δ` is a combination of two Beta integrals over the real line, which
the logistic substitution `x = e^r/(1+e^r)` identifies with Euler's Beta integral on `(0,1)`.
-/

open MeasureTheory Filter Finset intervalIntegral Complex
open scoped ArithmeticFunction.Moebius ComplexConjugate

noncomputable section

namespace RHTower.CubicGamma

/-! ### Euler's Beta integral on the real line -/

/-- The logistic map `r ↦ e^r / (1 + e^r)`. -/
def logistic (r : ℝ) : ℝ := Real.exp r / (1 + Real.exp r)

theorem logistic_pos (r : ℝ) : 0 < logistic r := by
  unfold logistic; positivity

theorem one_sub_logistic (r : ℝ) : 1 - logistic r = (1 + Real.exp r)⁻¹ := by
  unfold logistic
  have : (0 : ℝ) < 1 + Real.exp r := by positivity
  field_simp
  ring

theorem logistic_lt_one (r : ℝ) : logistic r < 1 := by
  have h := one_sub_logistic r
  have : (0 : ℝ) < (1 + Real.exp r)⁻¹ := by positivity
  linarith

theorem hasDerivAt_logistic (r : ℝ) :
    HasDerivAt logistic (logistic r * (1 - logistic r)) r := by
  have h1 : (1 + Real.exp r) ≠ 0 := by positivity
  have h := (Real.hasDerivAt_exp r).div ((Real.hasDerivAt_exp r).const_add 1) h1
  refine h.congr_deriv ?_
  rw [one_sub_logistic]
  unfold logistic
  field_simp
  ring

theorem strictMono_logistic : StrictMono logistic := by
  refine strictMono_of_deriv_pos fun r => ?_
  rw [(hasDerivAt_logistic r).deriv]
  exact mul_pos (logistic_pos r) (by linarith [logistic_lt_one r])

theorem logistic_image_univ : logistic '' Set.univ = Set.Ioo 0 1 := by
  ext x
  simp only [Set.image_univ, Set.mem_range, Set.mem_Ioo]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨logistic_pos r, logistic_lt_one r⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (x / (1 - x)), ?_⟩
    unfold logistic
    have h1x : 0 < 1 - x := by linarith
    rw [Real.exp_log (div_pos h0 h1x)]
    field_simp
    ring

/-- Complex powers of a positive real through the real logarithm. -/
theorem cpow_ofReal_pos {w : ℝ} (hw : 0 < w) (u : ℂ) :
    (w : ℂ) ^ u = Complex.exp (Real.log w * u) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hw.ne'), Complex.ofReal_log hw.le]

/-- The logistic pull-back of Euler's Beta integrand. -/
theorem logistic_betaIntegrand (u v : ℂ) (r : ℝ) :
    |logistic r * (1 - logistic r)| •
        ((logistic r : ℂ) ^ (u - 1) * (1 - (logistic r : ℂ)) ^ (v - 1)) =
      Complex.exp (u * r) * ((1 + Real.exp r : ℝ) : ℂ) ^ (-(u + v)) := by
  have hσ := logistic_pos r
  have h1σ : 0 < 1 - logistic r := by linarith [logistic_lt_one r]
  have hE : 0 < 1 + Real.exp r := by positivity
  have hlogσ : Real.log (logistic r) = r - Real.log (1 + Real.exp r) := by
    unfold logistic
    rw [Real.log_div (Real.exp_pos r).ne' hE.ne', Real.log_exp]
  have hlog1 : Real.log (1 - logistic r) = -Real.log (1 + Real.exp r) := by
    rw [one_sub_logistic, Real.log_inv]
  rw [abs_of_pos (mul_pos hσ h1σ), real_smul]
  have hsub : (1 : ℂ) - (logistic r : ℂ) = ((1 - logistic r : ℝ) : ℂ) := by push_cast; ring
  rw [hsub, cpow_ofReal_pos hσ, cpow_ofReal_pos h1σ, cpow_ofReal_pos hE, hlogσ, hlog1]
  have hprod : ((logistic r * (1 - logistic r) : ℝ) : ℂ) =
      Complex.exp (((r - Real.log (1 + Real.exp r) : ℝ) : ℂ) +
        ((-Real.log (1 + Real.exp r) : ℝ) : ℂ)) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← hlogσ, ← hlog1,
      Real.exp_log hσ, Real.exp_log h1σ]
    push_cast
    ring
  rw [hprod, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Euler's Beta integral on the real line.**
`∫_ℝ e^(u r) (1 + e^r)^(-(u+v)) dr = B(u, v)`. -/
theorem integral_exp_mul_one_add_exp_cpow (u v : ℂ) :
    (∫ r : ℝ, Complex.exp (u * r) * ((1 + Real.exp r : ℝ) : ℂ) ^ (-(u + v))) =
      Complex.betaIntegral u v := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← logistic_image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun r _ => (hasDerivAt_logistic r).hasDerivWithinAt) strictMono_logistic.injective.injOn]
  rw [Measure.restrict_univ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  exact (logistic_betaIntegrand u v r).symm

/-- The real-line Beta integrand is integrable for `Re u, Re v > 0`. -/
theorem integrable_exp_mul_one_add_exp_cpow {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Integrable (fun r : ℝ => Complex.exp (u * r) * ((1 + Real.exp r : ℝ) : ℂ) ^ (-(u + v))) := by
  have hb := Complex.betaIntegral_convergent hu hv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo, ← logistic_image_univ,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun r _ => (hasDerivAt_logistic r).hasDerivWithinAt)
      strictMono_logistic.injective.injOn] at hb
  rw [← integrableOn_univ]
  refine hb.congr_fun (fun r _ => logistic_betaIntegrand u v r) MeasurableSet.univ

/-! ### The logarithmic Gram kernel -/

/-- The logarithmic kernel `H_δ(r) = e^((a+1) r) G_δ(e^r, 1)`, `a = (1+δ)/2`. -/
def abelLogKernel (δ r : ℝ) : ℝ :=
  Real.exp (((1 + δ) / 2 + 1) * r) * abelPrefixGramKernel δ (Real.exp r) 1

/-- `H_δ` as two Beta profiles, `p = 5+δ`. -/
theorem abelLogKernel_eq (δ r : ℝ) :
    abelLogKernel δ r =
      (4 - 2 * (5 + δ)) * (Real.exp ((5 + δ) / 2 * r) * (1 + Real.exp r) ^ (-(5 + δ))) +
        (5 + δ) * (6 + δ) *
          (Real.exp (((5 + δ) / 2 + 1) * r) * (1 + Real.exp r) ^ (-(5 + δ + 2))) := by
  have hE : 0 < 1 + Real.exp r := by positivity
  have hx := Real.exp_pos r
  unfold abelLogKernel abelPrefixGramKernel
  rw [abelPrefixGramNumerator_formula, add_comm (Real.exp r) 1]
  have e7 : (1 + Real.exp r) ^ (7 + δ) = (1 + Real.exp r) ^ (5 + δ) * (1 + Real.exp r) ^ 2 := by
    rw [show (7 + δ : ℝ) = (5 + δ) + 2 by ring, Real.rpow_add hE, Real.rpow_two]
  have hn5 : (1 + Real.exp r) ^ (-(5 + δ)) = ((1 + Real.exp r) ^ (5 + δ))⁻¹ :=
    Real.rpow_neg hE.le _
  have hn7 : (1 + Real.exp r) ^ (-(5 + δ + 2)) = ((1 + Real.exp r) ^ (5 + δ) * (1 + Real.exp r) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hE.le, show (5 + δ + 2 : ℝ) = 7 + δ by ring, e7]
  have ea : Real.exp (((1 + δ) / 2 + 1) * r) * Real.exp r = Real.exp ((5 + δ) / 2 * r) := by
    rw [← Real.exp_add]; congr 1; ring
  have eb : Real.exp (((1 + δ) / 2 + 1) * r) * (Real.exp r * Real.exp r) =
      Real.exp (((5 + δ) / 2 + 1) * r) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e7, hn5, hn7, ← ea, ← eb]
  have hP : 0 < (1 + Real.exp r) ^ (5 + δ) := Real.rpow_pos_of_pos hE _
  generalize Real.exp (((1 + δ) / 2 + 1) * r) = X
  generalize (1 + Real.exp r) ^ (5 + δ) = P at hP ⊢
  generalize Real.exp r = E at hE ⊢
  field_simp

/-- `H_δ` is bounded by `|4 - 2p| + p(p+1)`. -/
theorem abs_abelLogKernel_le {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) :
    |abelLogKernel δ r| ≤ |4 - 2 * (5 + δ)| + (5 + δ) * (6 + δ) := by
  have hE : 0 < 1 + Real.exp r := by positivity
  have hEx : Real.exp r ≤ 1 + Real.exp r := by linarith
  have b1 : Real.exp ((5 + δ) / 2 * r) * (1 + Real.exp r) ^ (-(5 + δ)) ≤ 1 := by
    rw [Real.rpow_neg hE.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hE _)]
    calc Real.exp ((5 + δ) / 2 * r) = Real.exp r ^ ((5 + δ) / 2) := by
          rw [← Real.exp_mul]; ring_nf
      _ ≤ (1 + Real.exp r) ^ ((5 + δ) / 2) :=
          Real.rpow_le_rpow (Real.exp_pos r).le hEx (by linarith)
      _ ≤ (1 + Real.exp r) ^ (5 + δ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.exp_pos r]) (by linarith)
  have b2 : Real.exp (((5 + δ) / 2 + 1) * r) * (1 + Real.exp r) ^ (-(5 + δ + 2)) ≤ 1 := by
    rw [Real.rpow_neg hE.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hE _)]
    calc Real.exp (((5 + δ) / 2 + 1) * r) = Real.exp r ^ ((5 + δ) / 2 + 1) := by
          rw [← Real.exp_mul]; ring_nf
      _ ≤ (1 + Real.exp r) ^ ((5 + δ) / 2 + 1) :=
          Real.rpow_le_rpow (Real.exp_pos r).le hEx (by linarith)
      _ ≤ (1 + Real.exp r) ^ (5 + δ + 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.exp_pos r]) (by linarith)
  have p1 : 0 ≤ Real.exp ((5 + δ) / 2 * r) * (1 + Real.exp r) ^ (-(5 + δ)) := by positivity
  have p2 : 0 ≤ Real.exp (((5 + δ) / 2 + 1) * r) * (1 + Real.exp r) ^ (-(5 + δ + 2)) := by
    positivity
  rw [abelLogKernel_eq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (4 - 2 * (5 + δ)), abs_mul ((5 + δ) * (6 + δ)), abs_of_nonneg p1,
    abs_of_nonneg p2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (5 + δ) * (6 + δ))]
  have h0 := abs_nonneg (4 - 2 * (5 + δ))
  have m1 := mul_le_mul_of_nonneg_left b1 h0
  have m2 := mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ (5 + δ) * (6 + δ))
  linarith

theorem continuous_abelLogKernel (δ : ℝ) : Continuous (abelLogKernel δ) := by
  have h : abelLogKernel δ = fun r =>
      (4 - 2 * (5 + δ)) * (Real.exp ((5 + δ) / 2 * r) * (1 + Real.exp r) ^ (-(5 + δ))) +
        (5 + δ) * (6 + δ) *
          (Real.exp (((5 + δ) / 2 + 1) * r) * (1 + Real.exp r) ^ (-(5 + δ + 2))) := by
    funext r; exact abelLogKernel_eq δ r
  rw [h]
  have hc : ∀ c : ℝ, Continuous fun r : ℝ => (1 + Real.exp r) ^ c := fun c =>
    Continuous.rpow_const (by fun_prop) (fun r => Or.inl (by positivity))
  have := hc (-(5 + δ))
  have := hc (-(5 + δ + 2))
  fun_prop

/-- The Fourier multiplier `(a² + τ²) |Γ(p/2 + iτ)|² / Γ(p)`. -/
def abelMultiplier (δ τ : ℝ) : ℝ :=
  (((1 + δ) / 2) ^ 2 + τ ^ 2) * Complex.normSq (Complex.Gamma ((5 + δ) / 2 + τ * I)) /
    Real.Gamma (5 + δ)

/-- The multiplier is strictly positive at every log-frequency. -/
theorem abelMultiplier_pos {δ : ℝ} (hδ : 0 ≤ δ) (τ : ℝ) : 0 < abelMultiplier δ τ := by
  unfold abelMultiplier
  have hΓ : Complex.Gamma ((5 + δ) / 2 + τ * I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h1 : 0 < ((1 + δ) / 2) ^ 2 + τ ^ 2 := by positivity
  have h2 : 0 < Complex.normSq (Complex.Gamma ((5 + δ) / 2 + τ * I)) :=
    Complex.normSq_pos.mpr hΓ
  have h3 : 0 < Real.Gamma (5 + δ) := Real.Gamma_pos_of_pos (by linarith)
  positivity

private theorem gamma_succ_complex (z : ℂ) (hz : z ≠ 0) : Complex.Gamma (z + 1) = z * Complex.Gamma z :=
  Complex.Gamma_add_one z hz

/-- **Card equation (8).**  `Ĥ_δ(τ) = ∫ H_δ(r) e^(-iτr) dr = (a² + τ²) |Γ(p/2 + iτ)|² / Γ(p)`. -/
theorem fourier_abelLogKernel {δ : ℝ} (hδ : 0 ≤ δ) (τ : ℝ) :
    (∫ r : ℝ, (abelLogKernel δ r : ℂ) * Complex.exp (-(τ * r) * I)) =
      (abelMultiplier δ τ : ℂ) := by
  set p : ℝ := 5 + δ with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  set u : ℂ := (p / 2 : ℝ) - τ * I with hu
  set v : ℂ := (p / 2 : ℝ) + τ * I with hv
  have hure : 0 < u.re := by simp [hu]; linarith
  have hvre : 0 < v.re := by simp [hv]; linarith
  have hure1 : 0 < (u + 1).re := by simp [hu]; linarith
  have hvre1 : 0 < (v + 1).re := by simp [hv]; linarith
  have huv : u + v = (p : ℂ) := by rw [hu, hv]; push_cast; ring
  have huv1 : (u + 1) + (v + 1) = ((p + 2 : ℝ) : ℂ) := by rw [hu, hv]; push_cast; ring
  have hpoint : ∀ r : ℝ, (abelLogKernel δ r : ℂ) * Complex.exp (-(τ * r) * I) =
      ((4 - 2 * p : ℝ) : ℂ) * (Complex.exp (u * r) * ((1 + Real.exp r : ℝ) : ℂ) ^ (-(u + v))) +
        ((p * (p + 1) : ℝ) : ℂ) *
          (Complex.exp ((u + 1) * r) * ((1 + Real.exp r : ℝ) : ℂ) ^ (-((u + 1) + (v + 1)))) := by
    intro r
    have hE : 0 < 1 + Real.exp r := by positivity
    rw [abelLogKernel_eq, huv, huv1]
    rw [show -(p : ℂ) = ((-p : ℝ) : ℂ) by push_cast; ring,
      show -((p + 2 : ℝ) : ℂ) = ((-(p + 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hE.le, ← Complex.ofReal_cpow hE.le]
    have e1 : Complex.exp (u * r) = (Real.exp (p / 2 * r) : ℂ) * Complex.exp (-(τ * r) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, hu]; congr 1; push_cast; ring
    have e2 : Complex.exp ((u + 1) * r) =
        (Real.exp ((p / 2 + 1) * r) : ℂ) * Complex.exp (-(τ * r) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, hu]; congr 1; push_cast; ring
    rw [e1, e2, ← hp, show p + 2 = 5 + δ + 2 by rw [hp]]
    push_cast
    rw [show (δ : ℂ) = (p : ℂ) - 5 by rw [hp]; push_cast; ring]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_add ((integrable_exp_mul_one_add_exp_cpow hure hvre).const_mul _)
      ((integrable_exp_mul_one_add_exp_cpow hure1 hvre1).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_exp_mul_one_add_exp_cpow,
    integral_exp_mul_one_add_exp_cpow,
    Complex.betaIntegral_eq_Gamma_mul_div u v hure hvre,
    Complex.betaIntegral_eq_Gamma_mul_div (u + 1) (v + 1) hure1 hvre1, huv, huv1]
  have hu0 : u ≠ 0 := fun h => by rw [h] at hure; simp at hure
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvre; simp at hvre
  rw [gamma_succ_complex u hu0, gamma_succ_complex v hv0]
  have hGp : Complex.Gamma ((p + 2 : ℝ) : ℂ) = ((p + 1) * p : ℝ) * Complex.Gamma (p : ℂ) := by
    rw [show ((p + 2 : ℝ) : ℂ) = ((p : ℂ) + 1) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (by exact_mod_cast (by linarith : p + 1 ≠ 0)),
      Complex.Gamma_add_one _ (by exact_mod_cast hp0.ne')]
    push_cast; ring
  have hGreal : Complex.Gamma (p : ℂ) = (Real.Gamma p : ℂ) := Complex.Gamma_ofReal p
  have hconj : Complex.Gamma u = conj (Complex.Gamma v) := by
    rw [← Complex.Gamma_conj]
    congr 1
    rw [hu, hv, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hnorm : Complex.Gamma u * Complex.Gamma v =
      (Complex.normSq (Complex.Gamma v) : ℂ) := by
    rw [hconj, Complex.normSq_eq_conj_mul_self]
  have hGp0 : (Real.Gamma p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos hp0).ne'
  have hp1 : ((p + 1) * p : ℂ) ≠ 0 := by
    have : (p + 1) * p ≠ 0 := by positivity
    exact_mod_cast this
  have huv' : u * v = (((p / 2) ^ 2 + τ ^ 2 : ℝ) : ℂ) := by
    rw [hu, hv]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hGp, hGreal,
    show u * Complex.Gamma u * (v * Complex.Gamma v) =
      (u * v) * (Complex.Gamma u * Complex.Gamma v) by ring, huv', hnorm]
  have hvdef : ((5 : ℂ) + (δ : ℂ)) / 2 + (τ : ℂ) * I = v := by rw [hv, hp]; push_cast; ring
  have hmult : abelMultiplier δ τ =
      ((4 - 2 * p) + ((p / 2) ^ 2 + τ ^ 2)) * Complex.normSq (Complex.Gamma v) /
        Real.Gamma p := by
    unfold abelMultiplier
    rw [hvdef, ← hp]
    congr 2
    rw [hp]
    ring
  rw [hmult]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpc1 : (p : ℂ) + 1 ≠ 0 := by
    have : p + 1 ≠ 0 := by linarith
    exact_mod_cast this
  push_cast
  field_simp

/-! ### The frozen prefix and its logarithmic transform -/

/-- The frozen Möbius prefix `P_N(x) = M(min(⌊x⌋, N))`. -/
def frozenPrefix (N : ℕ) (x : ℝ) : ℝ := abelMertens (min ⌊x⌋₊ N)

theorem frozenPrefix_eq_sum (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    frozenPrefix N x = ∑ n ∈ Icc 1 N, if (n : ℝ) ≤ x then ((μ n : ℤ) : ℝ) else 0 := by
  unfold frozenPrefix abelMertens prefixSum
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]
  rw [Nat.le_floor_iff hx]
  tauto

/-- The logarithmic atom `u ↦ e^(-a u) 1_{u ≥ c}`. -/
def logAtom (a c u : ℝ) : ℝ := Set.indicator (Set.Ici c) (fun u => Real.exp (-(a * u))) u

/-- The logarithmic frozen prefix `b_N(u) = e^(-a u) P_N(e^u)` on `u ≥ 0`, `0` for `u < 0`,
with `a = (1+δ)/2`. -/
def frozenPrefixLog (δ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  if 0 ≤ u then Real.exp (-((1 + δ) / 2 * u)) * frozenPrefix N (Real.exp u) else 0

theorem frozenPrefixLog_eq_sum (δ : ℝ) (N : ℕ) (u : ℝ) :
    frozenPrefixLog δ N u =
      ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) * logAtom ((1 + δ) / 2) (Real.log n) u := by
  unfold frozenPrefixLog logAtom
  split_ifs with hu
  · rw [frozenPrefix_eq_sum N (Real.exp_pos u).le, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
    simp only [Set.indicator, Set.mem_Ici]
    by_cases h : Real.log n ≤ u
    · rw [if_pos ((Real.log_le_iff_le_exp hn0).mp h), if_pos h]; ring
    · rw [if_neg (fun h' => h ((Real.log_le_iff_le_exp hn0).mpr h')), if_neg h]; ring
  · symm
    apply Finset.sum_eq_zero
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ici, not_le]; linarith), mul_zero]

theorem integrable_logAtom {a : ℝ} (ha : 0 < a) (c : ℝ) : Integrable (logAtom a c) := by
  unfold logAtom
  refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := exp_neg_integrableOn_Ioi c ha
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [neg_mul]

theorem abs_logAtom_le {a c u : ℝ} : |logAtom a c u| ≤ Real.exp (-(a * u)) := by
  unfold logAtom
  by_cases h : u ∈ Set.Ici c
  · rw [Set.indicator_of_mem h, abs_of_pos (Real.exp_pos _)]
  · rw [Set.indicator_of_notMem h, abs_zero]; exact (Real.exp_pos _).le

theorem measurable_logAtom (a c : ℝ) : Measurable (logAtom a c) := by
  unfold logAtom
  exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-(a * u))).indicator measurableSet_Ici

/-- `b_N` is integrable. -/
theorem integrable_frozenPrefixLog {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    Integrable (frozenPrefixLog δ N) := by
  have ha : 0 < (1 + δ) / 2 := by linarith
  have h : frozenPrefixLog δ N = fun u =>
      ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) * logAtom ((1 + δ) / 2) (Real.log n) u := by
    funext u; exact frozenPrefixLog_eq_sum δ N u
  rw [h]
  exact integrable_finsetSum _ fun n _ => (integrable_logAtom ha _).const_mul _

/-- `b_N` is square-integrable. -/
theorem memLp_two_frozenPrefixLog {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    MemLp (frozenPrefixLog δ N) 2 volume := by
  have ha : 0 < (1 + δ) / 2 := by linarith
  have h : frozenPrefixLog δ N = fun u =>
      ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) * logAtom ((1 + δ) / 2) (Real.log n) u := by
    funext u; exact frozenPrefixLog_eq_sum δ N u
  rw [h]
  refine memLp_finsetSum _ fun n _ => ?_
  refine MemLp.const_mul ?_ _
  have hb : MemLp (fun u : ℝ => Real.exp (-(((1 + δ) / 2) * u))) 2
      (volume.restrict (Set.Ici (Real.log n))) := by
    refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
    show IntegrableOn _ (Set.Ici (Real.log n)) _
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h2 := exp_neg_integrableOn_Ioi (Real.log n) (by linarith : (0 : ℝ) < 2 * ((1 + δ) / 2))
    refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [Real.norm_eq_abs, sq_abs, pow_two, ← Real.exp_add]
    ring_nf
  exact (memLp_indicator_iff_restrict measurableSet_Ici).mpr hb

/-- **Card equation (9).**  `b̂_N(τ) = (a + iτ)⁻¹ Σ_{n ≤ N} μ(n) n^(-a-iτ)`. -/
theorem fourier_frozenPrefixLog {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) (τ : ℝ) :
    (∫ u : ℝ, (frozenPrefixLog δ N u : ℂ) * Complex.exp (-(τ * u) * I)) =
      (((1 + δ) / 2 : ℝ) + τ * I)⁻¹ *
        ∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + τ * I)) := by
  set a : ℝ := (1 + δ) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set z : ℂ := (a : ℂ) + τ * I with hz
  have hzre : (-z).re < 0 := by simp [hz]; linarith
  have hz0 : z ≠ 0 := fun h => by
    have : z.re = a := by simp [hz]
    rw [h] at this; simp at this; linarith
  have hatom : ∀ c : ℝ, (∫ u : ℝ, (logAtom a c u : ℂ) * Complex.exp (-(τ * u) * I)) =
      Complex.exp (-z * c) / z := by
    intro c
    have hind : (fun u : ℝ => (logAtom a c u : ℂ) * Complex.exp (-(τ * u) * I)) =
        Set.indicator (Set.Ici c) (fun u : ℝ => Complex.exp (-z * u)) := by
      funext u
      unfold logAtom
      by_cases h : u ∈ Set.Ici c
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_exp,
          ← Complex.exp_add, hz]
        congr 1
        push_cast
        ring
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
        simp
    rw [hind, MeasureTheory.integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_complex_Ioi hzre]
    field_simp
  have hsplit : (fun u : ℝ => (frozenPrefixLog δ N u : ℂ) * Complex.exp (-(τ * u) * I)) =
      fun u => ∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) *
        ((logAtom a (Real.log n) u : ℂ) * Complex.exp (-(τ * u) * I)) := by
    funext u
    rw [frozenPrefixLog_eq_sum, ← ha_def]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hint : ∀ n ∈ Icc 1 N, Integrable (fun u : ℝ => (((μ n : ℤ) : ℝ) : ℂ) *
      ((logAtom a (Real.log n) u : ℂ) * Complex.exp (-(τ * u) * I))) := by
    intro n _
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' (integrable_logAtom ha (Real.log n)).abs
      ((Complex.measurable_ofReal.comp (measurable_logAtom a _)).aestronglyMeasurable.mul
        (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp
  rw [hsplit, integral_finsetSum _ hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  have hc := cpow_ofReal_pos hn0 (-z)
  rw [Complex.ofReal_natCast] at hc
  rw [MeasureTheory.integral_const_mul, hatom, hc,
    show -z * ((Real.log n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) * -z by ring]
  field_simp

/-! ### Homogeneity and the logarithmic potential -/

theorem abelPrefixGramNumerator_smul (δ l x y : ℝ) :
    abelPrefixGramNumerator δ (l * x) (l * y) = l ^ 2 * abelPrefixGramNumerator δ x y := by
  unfold abelPrefixGramNumerator abelPrefixGramCore
  ring

/-- `G_δ(λx, λy) = λ^(-3-δ) G_δ(x, y)`. -/
theorem abelPrefixGramKernel_smul {δ l x y : ℝ} (hl : 0 < l) (hx : 0 < x) (hy : 0 < y) :
    abelPrefixGramKernel δ (l * x) (l * y) = l ^ (-3 - δ) * abelPrefixGramKernel δ x y := by
  have hs : 0 < x + y := by linarith
  unfold abelPrefixGramKernel
  rw [abelPrefixGramNumerator_smul, show l * x + l * y = l * (x + y) by ring,
    Real.mul_rpow hl.le hs.le]
  have h1 : 0 < l ^ (7 + δ) := Real.rpow_pos_of_pos hl _
  have h2 : 0 < (x + y) ^ (7 + δ) := Real.rpow_pos_of_pos hs _
  have e : l ^ (-3 - δ) = l ^ (4 : ℝ) / l ^ (7 + δ) := by
    rw [← Real.rpow_sub hl]; ring_nf
  rw [e, Real.rpow_ofNat]
  field_simp

/-- The logarithmic integrand is the pull-back of the mixed Gram:
`e^(-a u) e^(-a v) H_δ(u - v) = e^u e^v G_δ(e^u, e^v)`. -/
theorem logAtom_integrand_eq (δ u v : ℝ) :
    Real.exp (-((1 + δ) / 2 * u)) * Real.exp (-((1 + δ) / 2 * v)) * abelLogKernel δ (u - v) =
      Real.exp u * Real.exp v * abelPrefixGramKernel δ (Real.exp u) (Real.exp v) := by
  have hsm := abelPrefixGramKernel_smul (δ := δ) (Real.exp_pos v) (Real.exp_pos (u - v))
    one_pos
  rw [← Real.exp_add, show v + (u - v) = u by ring, mul_one] at hsm
  rw [hsm]
  unfold abelLogKernel
  have hpow : Real.exp v ^ (-3 - δ) = Real.exp ((-3 - δ) * v) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hpow]
  set g := abelPrefixGramKernel δ (Real.exp (u - v)) 1
  calc Real.exp (-((1 + δ) / 2 * u)) * Real.exp (-((1 + δ) / 2 * v)) *
        (Real.exp (((1 + δ) / 2 + 1) * (u - v)) * g)
      = Real.exp (-((1 + δ) / 2 * u) + -((1 + δ) / 2 * v) + ((1 + δ) / 2 + 1) * (u - v)) * g := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ = Real.exp (u + v + (-3 - δ) * v) * g := by congr 2; ring
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-! ### The double integral of the logarithmic kernel -/

private theorem tendsto_rpow_neg_of_tendsto {f : ℝ → ℝ} (hf : Tendsto f atTop atTop) {c : ℝ}
    (hc : 0 < c) : Tendsto (fun v => f v ^ (-c)) atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hc).comp hf

private theorem sq_mul_rpow_neg_le {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    y ^ 2 * (x + y) ^ (-c) ≤ (x + y) ^ (2 - c) := by
  have hs : 0 < x + y := by linarith
  rw [Real.rpow_sub hs, Real.rpow_two, Real.rpow_neg hs.le, div_eq_mul_inv]
  have : y ^ 2 ≤ (x + y) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- `∂_x K_δ(x, y) → 0` as `y → ∞`. -/
theorem tendsto_sourceKernelX_snd {δ : ℝ} (hδ : 0 ≤ δ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun v => sourceKernelX δ x (Real.exp v)) atTop (nhds 0) := by
  have hT : Tendsto (fun v => x + Real.exp v) atTop atTop :=
    tendsto_atTop_add_const_left _ _ Real.tendsto_exp_atTop
  have h1 := tendsto_rpow_neg_of_tendsto hT (show (0 : ℝ) < 3 + δ by linarith)
  have h2 := tendsto_rpow_neg_of_tendsto hT (show (0 : ℝ) < 4 + δ by linarith)
  have hmaj : Tendsto (fun v => 2 * x * (x + Real.exp v) ^ (-(3 + δ)) +
      (5 + δ) * x ^ 2 * (x + Real.exp v) ^ (-(4 + δ))) atTop (nhds 0) := by
    simpa using (h1.const_mul (2 * x)).add (h2.const_mul ((5 + δ) * x ^ 2))
  refine squeeze_zero_norm (fun v => ?_) hmaj
  have hy := Real.exp_pos v
  have b1 := sq_mul_rpow_neg_le (c := 5 + δ) hx.le hy
  have b2 := sq_mul_rpow_neg_le (c := 6 + δ) hx.le hy
  rw [show (2 : ℝ) - (5 + δ) = -(3 + δ) by ring] at b1
  rw [show (2 : ℝ) - (6 + δ) = -(4 + δ) by ring] at b2
  have p1 : 0 ≤ Real.exp v ^ 2 * (x + Real.exp v) ^ (-(5 + δ)) := by positivity
  have p2 : 0 ≤ Real.exp v ^ 2 * (x + Real.exp v) ^ (-(6 + δ)) := by positivity
  unfold sourceKernelX
  rw [Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  have e1 : |2 * x * Real.exp v ^ 2 * (x + Real.exp v) ^ (-(5 + δ))| =
      2 * x * (Real.exp v ^ 2 * (x + Real.exp v) ^ (-(5 + δ))) := by
    rw [abs_of_nonneg (by positivity)]; ring
  have e2 : |(5 + δ) * x ^ 2 * Real.exp v ^ 2 * (x + Real.exp v) ^ (-(6 + δ))| =
      (5 + δ) * x ^ 2 * (Real.exp v ^ 2 * (x + Real.exp v) ^ (-(6 + δ))) := by
    rw [abs_of_nonneg (by positivity)]; ring
  rw [e1, e2]
  gcongr

/-- `K_δ(x, n) → 0` as `x → ∞`. -/
theorem tendsto_sourceKernel_fst {δ : ℝ} (hδ : 0 ≤ δ) {n : ℝ} (hn : 0 < n) :
    Tendsto (fun u => sourceKernel δ (Real.exp u) n) atTop (nhds 0) := by
  have hT : Tendsto (fun u => n + Real.exp u) atTop atTop :=
    tendsto_atTop_add_const_left _ _ Real.tendsto_exp_atTop
  have h1 := (tendsto_rpow_neg_of_tendsto hT (show (0 : ℝ) < 3 + δ by linarith)).const_mul (n ^ 2)
  rw [mul_zero] at h1
  refine squeeze_zero (fun u => (sourceKernel_pos (Real.exp_pos u) hn).le) (fun u => ?_) h1
  have b := sq_mul_rpow_neg_le (c := 5 + δ) hn.le (Real.exp_pos u)
  rw [show (2 : ℝ) - (5 + δ) = -(3 + δ) by ring] at b
  rw [sourceKernel_eq_mul_rpow_neg (by positivity), add_comm (Real.exp u) n]
  calc Real.exp u ^ 2 * n ^ 2 * (n + Real.exp u) ^ (-(5 + δ)) =
      n ^ 2 * (Real.exp u ^ 2 * (n + Real.exp u) ^ (-(5 + δ))) := by ring
    _ ≤ n ^ 2 * (n + Real.exp u) ^ (-(3 + δ)) := by gcongr

/-- `|∂_x K_δ(x, n)| ≤ (7+δ) n² x^(-(4+δ))`. -/
theorem abs_sourceKernelX_le {δ : ℝ} (hδ : 0 ≤ δ) {x n : ℝ} (hx : 0 < x) (hn : 0 < n) :
    |sourceKernelX δ x n| ≤ (7 + δ) * n ^ 2 * x ^ (-(4 + δ)) := by
  have hs : x ≤ x + n := by linarith
  have r5 : (x + n) ^ (-(5 + δ)) ≤ x ^ (-(5 + δ)) :=
    Real.rpow_le_rpow_of_nonpos hx hs (by linarith)
  have r6 : (x + n) ^ (-(6 + δ)) ≤ x ^ (-(6 + δ)) :=
    Real.rpow_le_rpow_of_nonpos hx hs (by linarith)
  have e5 : x * x ^ (-(5 + δ)) = x ^ (-(4 + δ)) := by
    rw [← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
  have e6 : x ^ 2 * x ^ (-(6 + δ)) = x ^ (-(4 + δ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hx]; ring_nf
  unfold sourceKernelX
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hp : 0 ≤ x ^ (-(4 + δ)) := by positivity
  calc 2 * x * n ^ 2 * (x + n) ^ (-(5 + δ)) + (5 + δ) * x ^ 2 * n ^ 2 * (x + n) ^ (-(6 + δ))
      ≤ 2 * x * n ^ 2 * x ^ (-(5 + δ)) + (5 + δ) * x ^ 2 * n ^ 2 * x ^ (-(6 + δ)) := by
        gcongr
    _ = (7 + δ) * n ^ 2 * x ^ (-(4 + δ)) := by
        rw [show 2 * x * n ^ 2 * x ^ (-(5 + δ)) = 2 * n ^ 2 * (x * x ^ (-(5 + δ))) by ring,
          show (5 + δ) * x ^ 2 * n ^ 2 * x ^ (-(6 + δ)) =
            (5 + δ) * n ^ 2 * (x ^ 2 * x ^ (-(6 + δ))) by ring, e5, e6]
        ring

/-- **Inner logarithmic integral.**
`∫_{v > log n} e^u e^v G_δ(e^u, e^v) dv = -e^u ∂_x K_δ(e^u, n)`. -/
theorem integral_Ioi_gram_inner {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) {n : ℝ} (hn : 0 < n) :
    (∫ v in Set.Ioi (Real.log n),
      Real.exp u * Real.exp v * abelPrefixGramKernel δ (Real.exp u) (Real.exp v)) =
      -(Real.exp u * sourceKernelX δ (Real.exp u) n) := by
  have ha : 0 < (1 + δ) / 2 := by linarith
  have hderiv : ∀ v ∈ Set.Ici (Real.log n), HasDerivAt
      (fun v => Real.exp u * sourceKernelX δ (Real.exp u) (Real.exp v))
      (Real.exp u * Real.exp v * abelPrefixGramKernel δ (Real.exp u) (Real.exp v)) v := by
    intro v _
    have h := ((hasDerivAt_sourceKernelX_snd δ (Real.exp_pos u) (Real.exp_pos v)).comp v
      (Real.hasDerivAt_exp v)).const_mul (Real.exp u)
    refine h.congr_deriv ?_
    ring
  have hint : IntegrableOn
      (fun v => Real.exp u * Real.exp v * abelPrefixGramKernel δ (Real.exp u) (Real.exp v))
      (Set.Ioi (Real.log n)) := by
    have hmaj := (exp_neg_integrableOn_Ioi (Real.log n) ha).const_mul
      (Real.exp (-((1 + δ) / 2 * u)) * (|4 - 2 * (5 + δ)| + (5 + δ) * (6 + δ)))
    refine hmaj.mono' ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_)
      have hc : Continuous fun v => Real.exp (-((1 + δ) / 2 * u)) *
          Real.exp (-((1 + δ) / 2 * v)) * abelLogKernel δ (u - v) :=
        by have := continuous_abelLogKernel δ; fun_prop
      refine hc.congr fun v => logAtom_integrand_eq δ u v
    · filter_upwards with v
      rw [← logAtom_integrand_eq, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have hk := abs_abelLogKernel_le hδ (u - v)
      calc Real.exp (-((1 + δ) / 2 * u)) * Real.exp (-((1 + δ) / 2 * v)) * |abelLogKernel δ (u - v)|
          ≤ Real.exp (-((1 + δ) / 2 * u)) * Real.exp (-((1 + δ) / 2 * v)) *
              (|4 - 2 * (5 + δ)| + (5 + δ) * (6 + δ)) := by gcongr
        _ = _ := by ring_nf
  have hlim : Tendsto (fun v => Real.exp u * sourceKernelX δ (Real.exp u) (Real.exp v)) atTop
      (nhds 0) := by
    simpa using (tendsto_sourceKernelX_snd hδ (Real.exp_pos u)).const_mul (Real.exp u)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim, Real.exp_log hn]
  ring

theorem continuous_sourceKernelX_exp {δ : ℝ} {n : ℝ} (hn : 0 < n) :
    Continuous fun u => sourceKernelX δ (Real.exp u) n := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hs : Real.exp u + n ≠ 0 := by positivity
  unfold sourceKernelX
  exact ContinuousAt.sub
    (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs)))
    (ContinuousAt.mul (by fun_prop) (ContinuousAt.rpow_const (by fun_prop) (Or.inl hs)))

/-- **Outer logarithmic integral.**
`∫_{u > log m} -e^u ∂_x K_δ(e^u, n) du = K_δ(m, n)`. -/
theorem integral_Ioi_gram_outer {δ : ℝ} (hδ : 0 ≤ δ) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (∫ u in Set.Ioi (Real.log m), -(Real.exp u * sourceKernelX δ (Real.exp u) n)) =
      sourceKernel δ m n := by
  have hderiv : ∀ u ∈ Set.Ici (Real.log m), HasDerivAt (fun u => sourceKernel δ (Real.exp u) n)
      (Real.exp u * sourceKernelX δ (Real.exp u) n) u := by
    intro u _
    have h := (hasDerivAt_sourceKernel_fst δ (Real.exp_pos u) hn).comp u (Real.hasDerivAt_exp u)
    refine h.congr_deriv ?_
    ring
  have hint : IntegrableOn (fun u => Real.exp u * sourceKernelX δ (Real.exp u) n)
      (Set.Ioi (Real.log m)) := by
    have hmaj := (exp_neg_integrableOn_Ioi (Real.log m) (show (0 : ℝ) < 3 + δ by linarith)).const_mul
      ((7 + δ) * n ^ 2)
    refine hmaj.mono' ?_ ?_
    · exact (Real.continuous_exp.mul (continuous_sourceKernelX_exp hn)).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hb := abs_sourceKernelX_le hδ (Real.exp_pos u) hn
      have hpow : Real.exp u ^ (-(4 + δ)) = Real.exp (-(4 + δ) * u) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hpow] at hb
      calc Real.exp u * |sourceKernelX δ (Real.exp u) n|
          ≤ Real.exp u * ((7 + δ) * n ^ 2 * Real.exp (-(4 + δ) * u)) := by gcongr
        _ = (7 + δ) * n ^ 2 * Real.exp (-(3 + δ) * u) := by
          rw [show Real.exp u * ((7 + δ) * n ^ 2 * Real.exp (-(4 + δ) * u)) =
            (7 + δ) * n ^ 2 * (Real.exp u * Real.exp (-(4 + δ) * u)) by ring, ← Real.exp_add]
          ring_nf
  rw [MeasureTheory.integral_neg, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint
    (tendsto_sourceKernel_fst hδ hn), Real.exp_log hm]
  ring

/-- The logarithmic prefix transform of one atom against `H_δ`. -/
def logAtomKernel (δ : ℝ) (c u : ℝ) : ℝ :=
  ∫ v, logAtom ((1 + δ) / 2) c v * abelLogKernel δ (u - v)

theorem integrable_logAtom_mul_kernel {δ : ℝ} (hδ : 0 ≤ δ) (c u : ℝ) :
    Integrable (fun v => logAtom ((1 + δ) / 2) c v * abelLogKernel δ (u - v)) := by
  have ha : 0 < (1 + δ) / 2 := by linarith
  refine Integrable.mono' ((integrable_logAtom ha c).abs.const_mul
    (|4 - 2 * (5 + δ)| + (5 + δ) * (6 + δ)))
    ((measurable_logAtom _ c).aestronglyMeasurable.mul
      ((continuous_abelLogKernel δ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := abs_abelLogKernel_le hδ (u - v)
  have h0 := abs_nonneg (logAtom ((1 + δ) / 2) c v)
  nlinarith

/-- The atom transform in closed form: `e^(a u) · (-e^u ∂_x K_δ(e^u, n))`. -/
theorem logAtomKernel_eq {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) {n : ℝ} (hn : 0 < n) :
    logAtomKernel δ (Real.log n) u =
      Real.exp ((1 + δ) / 2 * u) * -(Real.exp u * sourceKernelX δ (Real.exp u) n) := by
  unfold logAtomKernel logAtom
  have hind : (fun v => Set.indicator (Set.Ici (Real.log n))
      (fun v => Real.exp (-((1 + δ) / 2 * v))) v * abelLogKernel δ (u - v)) =
      Set.indicator (Set.Ici (Real.log n))
        (fun v => Real.exp (-((1 + δ) / 2 * v)) * abelLogKernel δ (u - v)) := by
    funext v
    by_cases h : v ∈ Set.Ici (Real.log n)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    ← integral_Ioi_gram_inner hδ u hn, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [← logAtom_integrand_eq, ← mul_assoc, ← mul_assoc, ← Real.exp_add,
    show (1 + δ) / 2 * u + -((1 + δ) / 2 * u) = 0 by ring, Real.exp_zero, one_mul]

/-- **The atom double integral.**  For `m, n > 0`,
`∫∫ e^(-a u) 1_{u ≥ log m} e^(-a v) 1_{v ≥ log n} H_δ(u - v) dv du = K_δ(m, n)`. -/
theorem integral_logAtom_mul_logAtomKernel {δ : ℝ} (hδ : 0 ≤ δ) {m n : ℝ} (hm : 0 < m)
    (hn : 0 < n) :
    (∫ u, logAtom ((1 + δ) / 2) (Real.log m) u * logAtomKernel δ (Real.log n) u) =
      sourceKernel δ m n := by
  have hind : (fun u => logAtom ((1 + δ) / 2) (Real.log m) u * logAtomKernel δ (Real.log n) u) =
      Set.indicator (Set.Ici (Real.log m))
        (fun u => -(Real.exp u * sourceKernelX δ (Real.exp u) n)) := by
    funext u
    unfold logAtom
    by_cases h : u ∈ Set.Ici (Real.log m)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, logAtomKernel_eq hδ u hn,
        ← mul_assoc, ← Real.exp_add, show -((1 + δ) / 2 * u) + (1 + δ) / 2 * u = 0 by ring,
        Real.exp_zero, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_Ioi_gram_outer hδ hm hn]

theorem integrable_logAtom_mul_logAtomKernel {δ : ℝ} (hδ : 0 ≤ δ) {m n : ℝ} (hn : 0 < n) :
    Integrable (fun u => logAtom ((1 + δ) / 2) (Real.log m) u * logAtomKernel δ (Real.log n) u) := by
  have ha : 0 < (1 + δ) / 2 := by linarith
  have hcont : Continuous (logAtomKernel δ (Real.log n)) := by
    have h : logAtomKernel δ (Real.log n) = fun u =>
        Real.exp ((1 + δ) / 2 * u) * -(Real.exp u * sourceKernelX δ (Real.exp u) n) := by
      funext u; exact logAtomKernel_eq hδ u hn
    rw [h]
    have := continuous_sourceKernelX_exp (δ := δ) hn
    fun_prop
  set C := (|4 - 2 * (5 + δ)| + (5 + δ) * (6 + δ)) *
    ∫ v, |logAtom ((1 + δ) / 2) (Real.log n) v| with hC
  have hbound : ∀ u, |logAtomKernel δ (Real.log n) u| ≤ C := by
    intro u
    unfold logAtomKernel
    rw [hC, ← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((integrable_logAtom ha _).abs.const_mul _)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_abelLogKernel_le hδ (u - v)
    have h0 := abs_nonneg (logAtom ((1 + δ) / 2) (Real.log n) v)
    nlinarith
  refine Integrable.mono' ((integrable_logAtom ha (Real.log m)).abs.mul_const C)
    ((measurable_logAtom _ _).aestronglyMeasurable.mul hcont.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound u) (abs_nonneg _)

/-- **Card equation (7).**  The full finite source energy is the double integral of the
logarithmic frozen prefixes against `H_δ(u - v)`. -/
theorem gammaEnergy_mobiusCubicSource_eq_logKernel {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    gammaEnergy δ (mobiusCubicSource N) =
      ∫ u, ∫ v, frozenPrefixLog δ N u * frozenPrefixLog δ N v * abelLogKernel δ (u - v) := by
  have hδ' : 0 < 5 + δ := by linarith
  have hpos : ∀ n ∈ Icc 1 N, (0 : ℝ) < n := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  set a : ℝ := (1 + δ) / 2 with ha_def
  -- the source side
  have hsrc : mobiusCubicSource N = fun t => ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) * atom n t := rfl
  have hL : gammaEnergy δ (mobiusCubicSource N) = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      ((μ m : ℤ) : ℝ) * ((μ n : ℤ) : ℝ) * sourceKernel δ m n := by
    rw [hsrc, gammaEnergy_sum hδ' (Icc 1 N) (fun n => ((μ n : ℤ) : ℝ))
      (fun n hn => gammaFinite_atom hδ' (hpos n hn))]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [gammaInner_atom hδ' (hpos m hm) (hpos n hn)]
  -- the inner integral for each `u`
  have hinner : ∀ u, (∫ v, frozenPrefixLog δ N u * frozenPrefixLog δ N v * abelLogKernel δ (u - v)) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ((μ m : ℤ) : ℝ) * ((μ n : ℤ) : ℝ) *
        (logAtom a (Real.log m) u * logAtomKernel δ (Real.log n) u) := by
    intro u
    have hpt : (fun v => frozenPrefixLog δ N u * frozenPrefixLog δ N v * abelLogKernel δ (u - v)) =
        fun v => frozenPrefixLog δ N u * ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) *
          (logAtom a (Real.log n) v * abelLogKernel δ (u - v)) := by
      funext v
      rw [frozenPrefixLog_eq_sum δ N v, ← ha_def, mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hpt, MeasureTheory.integral_const_mul,
      integral_finsetSum _ fun n _ => (integrable_logAtom_mul_kernel hδ _ u).const_mul _,
      frozenPrefixLog_eq_sum δ N u, ← ha_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [MeasureTheory.integral_const_mul]
    unfold logAtomKernel
    ring
  rw [hL, MeasureTheory.integral_congr_ae (Eventually.of_forall hinner)]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n hn =>
    (integrable_logAtom_mul_logAtomKernel hδ (hpos n hn)).const_mul _]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum _ fun n hn =>
    (integrable_logAtom_mul_logAtomKernel hδ (hpos n hn)).const_mul _]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_const_mul, integral_logAtom_mul_logAtomKernel hδ (hpos m hm) (hpos n hn)]

/-! ### The Abel integral of the full source -/

theorem integrableOn_pow_mul_exp_Ioi (k : ℕ) {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(t * x))) (Set.Ioi c) := by
  have h := integrableOn_rpow_mul_exp (s := (k : ℝ) + 1) (c := t) (by positivity) ht
  refine (h.congr_fun (fun x hx => ?_) measurableSet_Ioi).mono_set (Set.Ioi_subset_Ioi hc)
  simp only [add_sub_cancel_right, Real.rpow_natCast]

theorem integrableOn_atomJet_one_Ioi {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun x => atomJet 1 x t) (Set.Ioi c) := by
  have h : (fun x => atomJet 1 x t) =
      fun x => (-t) * (x ^ 2 * Real.exp (-(t * x))) + 2 * (x ^ 1 * Real.exp (-(t * x))) := by
    funext x; simp [atomJet]; ring_nf
  rw [h]
  exact ((integrableOn_pow_mul_exp_Ioi 2 ht hc).const_mul _).add
    ((integrableOn_pow_mul_exp_Ioi 1 ht hc).const_mul _)

theorem tendsto_atom_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => atom x t) atTop (nhds 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    (tendsto_id.const_mul_atTop ht)).const_mul (1 / t ^ 2)
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, id_eq, atom]
  field_simp

/-- `∫_{x > n} ∂_x f_x(t) dx = -f_n(t)`. -/
theorem integral_Ioi_atomJet_one {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in Set.Ioi c, atomJet 1 x t) = -atom c t := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (f := fun x => atom x t)
    (fun x _ => by simpa only [atomJet_zero] using hasDerivAt_atomJet 0 t x)
    (integrableOn_atomJet_one_Ioi ht hc) (tendsto_atom_atTop ht)]
  ring

/-- **Card equation (6).**  `S_N(t) = -∫_1^∞ P_N(x) ∂_x f_x(t) dx` for every `t > 0`. -/
theorem mobiusCubicSource_eq_neg_integral {t : ℝ} (ht : 0 < t) (N : ℕ) :
    mobiusCubicSource N t = -∫ x in Set.Ioi 1, frozenPrefix N x * atomJet 1 x t := by
  have hpos : ∀ n ∈ Icc 1 N, (1 : ℝ) ≤ n := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  have hpt : Set.EqOn (fun x => frozenPrefix N x * atomJet 1 x t)
      (fun x => ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℝ) *
        Set.indicator (Set.Ici (n : ℝ)) (fun x => atomJet 1 x t) x) (Set.Ioi 1) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by have : (1 : ℝ) < x := hx; linarith
    simp only
    rw [frozenPrefix_eq_sum N hx0, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : (n : ℝ) ≤ x
    · rw [if_pos h, Set.indicator_of_mem (Set.mem_Ici.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]; ring
  have hint : ∀ n ∈ Icc 1 N, IntegrableOn (fun x => ((μ n : ℤ) : ℝ) *
      Set.indicator (Set.Ici (n : ℝ)) (fun x => atomJet 1 x t) x) (Set.Ioi 1) := by
    intro n hn
    refine Integrable.const_mul ?_ _
    have hI : Integrable (Set.indicator (Set.Ici (n : ℝ)) (fun x => atomJet 1 x t)) :=
      (integrable_indicator_iff measurableSet_Ici).mpr
        ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
          (integrableOn_atomJet_one_Ioi ht (by linarith [hpos n hn])))
    exact hI.integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ hint, ← Finset.sum_neg_distrib]
  unfold mobiusCubicSource
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_const_mul, setIntegral_indicator measurableSet_Ici]
  have hset : (Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) : Set ℝ) =ᵐ[volume] (Set.Ioi (n : ℝ) : Set ℝ) := by
    have h1 : Set.Ioi (n : ℝ) ⊆ Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) := by
      intro x hx
      exact ⟨lt_of_le_of_lt (hpos n hn) hx, Set.mem_Ici.mpr (le_of_lt hx)⟩
    have h2 : Set.Ioi (1 : ℝ) ∩ Set.Ici (n : ℝ) ⊆ Set.Ici (n : ℝ) := Set.inter_subset_right
    exact (h1.eventuallyLE.antisymm (h2.eventuallyLE.trans
      (Ioi_ae_eq_Ici : Set.Ioi (n : ℝ) =ᵐ[volume] Set.Ici (n : ℝ)).symm.le)).symm
  rw [setIntegral_congr_set hset, integral_Ioi_atomJet_one ht (by linarith [hpos n hn])]
  ring

/-! ### The Mellin--Plancherel form of the energy -/

private theorem sum_Icc_eq_range_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ he
    omega
  · intro b hb
    have hb := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n _
    rfl

/-- The source is a finite real Laplace pencil with shifted cubic coefficients. -/
theorem mobiusCubicSource_eq_laplacePencil (N : ℕ) :
    mobiusCubicSource N =
      finiteRealLaplacePencil (fun n => ((μ (n + 1) : ℤ) : ℝ) * ((n : ℝ) + 1) ^ 2) N := by
  funext x
  unfold mobiusCubicSource finiteRealLaplacePencil
  rw [sum_Icc_eq_range_shift]
  apply Finset.sum_congr rfl
  intro n _
  unfold atom
  push_cast
  ring_nf

/-- `Γ(5+δ) ‖S_N‖_δ²` is the logarithmic `L²` energy on the line `Re s = (5+δ)/2`. -/
theorem integral_log_mobiusCubicSource_sq {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    (∫ u : ℝ, Real.exp (-(5 + δ) * u) * mobiusCubicSource N (Real.exp (-u)) ^ 2) =
      Real.Gamma (5 + δ) * gammaEnergy δ (mobiusCubicSource N) := by
  have hr : (0 : ℝ) < 5 + δ := by linarith
  rw [mobiusCubicSource_eq_laplacePencil, integral_log_finiteRealLaplacePencil_sq _ _ hr,
    ← integral_finiteRealLaplacePencil_sq _ _ hr, ← mobiusCubicSource_eq_laplacePencil]
  unfold gammaEnergy gammaInner
  rw [← mul_assoc, mul_inv_cancel₀ (Real.Gamma_pos_of_pos hr).ne', one_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  rw [show 5 + δ - 1 = 4 + δ by ring]
  simp only [pow_two]

/-- **Card equation (10).**  The full Mellin--Plancherel identity
`‖S_N‖_δ² = (2π Γ(p))⁻¹ ∫ |Γ(p/2 + iτ)|² |Σ_{n ≤ N} μ(n) n^(-a-iτ)|² dτ`. -/
theorem gammaEnergy_mobiusCubicSource_eq_mellin {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    gammaEnergy δ (mobiusCubicSource N) =
      (2 * Real.pi * Real.Gamma (5 + δ))⁻¹ * ∫ τ : ℝ,
        ‖Complex.Gamma (((5 + δ) / 2 : ℝ) + τ * I)‖ ^ 2 *
          ‖∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + τ * I))‖ ^ 2 := by
  set σ : ℝ := (5 + δ) / 2 with hσ_def
  have hσ : 0 < σ := by rw [hσ_def]; linarith
  set c : ℕ → ℝ := fun n => ((μ n : ℤ) : ℝ) * (n : ℝ) ^ 2 with hc
  set m : ℕ → ℝ := fun n => (n : ℝ) with hm
  set f : ℝ → ℂ := fun x => ((expDecaySum (Icc 1 N) c m x : ℝ) : ℂ) with hf
  have hfS : ∀ x, expDecaySum (Icc 1 N) c m x = mobiusCubicSource N x := by
    intro x
    unfold expDecaySum mobiusCubicSource atom
    apply Finset.sum_congr rfl
    intro n _
    rw [hc, hm]
    ring_nf
  have hm1 : ∀ n ∈ Icc 1 N, (1 : ℝ) ≤ m n := fun n hn => by
    simp only [hm]; exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hcont : Continuous f := by
    rw [hf]; exact Complex.continuous_ofReal.comp (continuous_expDecaySum _ _ _)
  have hbound : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ (∑ n ∈ Icc 1 N, |c n|) * Real.exp (-(1 * x)) := by
    intro x hx
    rw [hf, Complex.norm_real, Real.norm_eq_abs]
    exact abs_expDecaySum_le _ c m hm1 hx.le
  have h1 := integrable_logMellinLineSource_of_exp_bound hσ one_pos hcont hbound
  have h2 := memLp_two_logMellinLineSource_of_exp_bound hσ one_pos hcont hbound
  have hplan := integral_norm_sq_mellin_line_eq_logMellinLineSource h1 h2
  -- the vertical side
  have hline : ∀ τ : ℝ, ‖mellin f ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 =
      ‖Complex.Gamma ((σ : ℝ) + τ * I)‖ ^ 2 *
        ‖∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + τ * I))‖ ^ 2 := by
    intro τ
    have hre : 0 < ((σ : ℂ) + (τ : ℂ) * I).re := by simp; exact hσ
    have hsum : (∑ i ∈ Icc 1 N, (c i : ℂ) * (m i : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))) =
        ∑ n ∈ Icc 1 N, (((μ n : ℤ) : ℝ) : ℂ) * (n : ℂ) ^ (-(((1 + δ) / 2 : ℝ) + τ * I)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (by omega : n ≠ 0)
      simp only [hc, hm]
      push_cast
      rw [mul_assoc]
      congr 1
      rw [show ((n : ℂ)) ^ 2 = (n : ℂ) ^ (2 : ℂ) by norm_cast, ← Complex.cpow_add _ _ hn0]
      congr 1
      rw [hσ_def]
      push_cast
      ring
    rw [hf, mellin_expDecaySum _ c m (fun n hn => by linarith [hm1 n hn]) hre, norm_mul, mul_pow,
      hsum]
  -- the logarithmic side
  have hlog : (∫ u : ℝ, ‖logMellinLineSource f σ u‖ ^ 2) =
      Real.Gamma (5 + δ) * gammaEnergy δ (mobiusCubicSource N) := by
    rw [← integral_log_mobiusCubicSource_sq hδ N]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [logMellinLineSource, hf]
    dsimp only
    rw [hfS, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _),
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← Real.exp_nat_mul, hσ_def]
    congr 2
    push_cast
    ring
  simp_rw [hline] at hplan
  rw [hplan, hlog]
  have hG : 0 < Real.Gamma (5 + δ) := Real.Gamma_pos_of_pos (by linarith)
  field_simp

end RHTower.CubicGamma
