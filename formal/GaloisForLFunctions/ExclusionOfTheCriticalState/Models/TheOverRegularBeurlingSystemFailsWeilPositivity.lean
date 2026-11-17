import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TheBeurlingWeilFormIsACaratheodoryKernelOnProbes
import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros

/-!
# A Beurling system with positive primes and over-regular integers fails Weil positivity

The over-regular system of `RHTower.BeurlingOverRegularIntegers`: parameters `1/3 < μ < 1/2`,
`0 < ν < 3μ - 1`, any `γ`, with `p₁ = 3μ - 1 - ν`, `p₂ = 3μ - 1 + ν`, a nonnegative logarithmic prime
density `w`, integers counted by `N(x) = ρx + C + o(1)`, and
`ζ(s) = ((s - (1 - μ))² + γ²)(s + 4μ - 1)/((s - 1)(s + p₁)(s + p₂))`.

* **The von Mangoldt measure** (`overRegularMeasure`) is `t w(t) dt = E(t) dt` on `(0, ∞)`,
  `E(t) = e^t - 2e^{(1-μ)t} cos γt + e^{-p₁t} + e^{-p₂t} - e^{-(4μ-1)t} ≥ 0`: a Beurling measure
  (`isBeurlingMeasure_overRegularMeasure`). Its Laplace transform is
  `1/(s-1) - 1/(s-ρ) - 1/(s-ρ̄) + 1/(s+p₁) + 1/(s+p₂) - 1/(s+4μ-1)`, `ρ = 1 - μ + iγ`
  (`integral_cexp_overRegularMeasure`): six exponential modes of `E`.
* **The completed zeta** (`overRegularXi`): in the centred coordinate `s = ½ + w`,
  `Γℝ(s) s (s - ρ)(s - ρ̄)(s + 4μ - 1)/((s + p₁)(s + p₂))`, which is `s(s - 1)Γℝ(s)ζ(s)` off `s = 1`
  (`overRegularXi_eq`). It is holomorphic on `Re w > 0`, zero-free on `Re w > ½`, its logarithmic
  derivative there is the Beurling symbol `D_ν` (`logDeriv_overRegularXi`), and it vanishes at
  `w = ρ - ½`, `Re = ½ - μ > 0`.
* **Weil positivity fails** (`overRegular_exists_probe_form_neg`): on every node set accumulating in
  `(½, ∞)`, in particular on every interval, some real Pick matrix of the Beurling Weil form is not
  positive semidefinite, and the symbol has no Carathéodory extension.

A positive prime measure with an integer count whose error tends to a constant does not give Weil
positivity.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower _root_.RHTower.BeurlingOverRegularIntegers

/-! ### The von Mangoldt measure -/

theorem continuous_primeNumerator (μ ν γ : ℝ) : Continuous (primeNumerator μ ν γ) := by
  unfold primeNumerator
  fun_prop

theorem measurable_toNNReal_primeNumerator (μ ν γ : ℝ) :
    Measurable fun t => Real.toNNReal (primeNumerator μ ν γ t) :=
  (continuous_primeNumerator μ ν γ).measurable.real_toNNReal

/-- The von Mangoldt measure `E(t) dt = t w(t) dt` of the over-regular system. -/
def overRegularMeasure (μ ν γ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t =>
    ((Real.toNNReal (primeNumerator μ ν γ t) : ℝ≥0) : ℝ≥0∞)

/-- The density of `overRegularMeasure` is `t` times the logarithmic prime density. -/
theorem primeNumerator_eq_mul_primeDensity (μ ν γ : ℝ) {t : ℝ} (ht : 0 < t) :
    primeNumerator μ ν γ t = t * primeDensity μ ν γ t := by
  unfold primeDensity
  field_simp

/-- Coefficients of the six exponential modes of `E`. -/
def modeCoeff : Fin 6 → ℂ := ![1, -1, -1, 1, 1, -1]

/-- Rates of the six exponential modes of `E(t) e^{-st}`. -/
def modeRate (μ ν γ : ℝ) (s : ℂ) : Fin 6 → ℂ :=
  ![s - 1, s - (((1 - μ : ℝ) : ℂ) + γ * I), s - (((1 - μ : ℝ) : ℂ) - γ * I),
    s + ((3 * μ - 1 - ν : ℝ) : ℂ), s + ((3 * μ - 1 + ν : ℝ) : ℂ), s + ((4 * μ - 1 : ℝ) : ℂ)]

/-- `E(t) e^{-st}` is a sum of six exponentials. -/
theorem ofReal_primeNumerator_mul_cexp (μ ν γ : ℝ) (s : ℂ) (t : ℝ) :
    (primeNumerator μ ν γ t : ℂ) * cexp (-(s * t)) =
      ∑ k, modeCoeff k * cexp (-modeRate μ ν γ s k * t) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, modeCoeff, modeRate, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  have ecos : cexp (((γ : ℂ) * t) * I) + cexp (-(((γ : ℂ) * t) * I)) =
      2 * Complex.cos ((γ : ℂ) * t) := by
    rw [Complex.exp_mul_I, show -(((γ : ℂ) * t) * I) = (-((γ : ℂ) * t)) * I by ring,
      Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg]
    ring
  have hN : (primeNumerator μ ν γ t : ℂ) = cexp t - 2 * cexp ((1 - μ : ℂ) * t) *
      Complex.cos ((γ : ℂ) * t) + cexp (-((3 * μ - 1 - ν : ℂ) * t)) +
      cexp (-((3 * μ - 1 + ν : ℂ) * t)) - cexp (-((4 * μ - 1 : ℂ) * t)) := by
    unfold primeNumerator
    push_cast
    ring
  have e1 : cexp (-(s - 1) * t) = cexp (-(s * t)) * cexp t := by
    rw [← Complex.exp_add]; congr 1; ring
  have e : ∀ c : ℂ, cexp (-(s - c) * t) = cexp (-(s * t)) * cexp (c * t) := fun c => by
    rw [← Complex.exp_add]; congr 1; ring
  have e' : ∀ c : ℂ, cexp (-(s + c) * t) = cexp (-(s * t)) * cexp (-(c * t)) := fun c => by
    rw [← Complex.exp_add]; congr 1; ring
  have h1 : cexp ((((1 - μ : ℝ) : ℂ) + γ * I) * t) =
      cexp ((1 - μ : ℂ) * t) * cexp (((γ : ℂ) * t) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : cexp ((((1 - μ : ℝ) : ℂ) - γ * I) * t) =
      cexp ((1 - μ : ℂ) * t) * cexp (-(((γ : ℂ) * t) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e, e, e', e', e', h1, h2, hN]
  push_cast
  linear_combination (cexp (-(s * t)) * cexp ((1 - μ : ℂ) * t)) * ecos

theorem modeRate_re_pos {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν) (hhigh : 0 ≤ 3 * μ - 1 + ν)
    {s : ℂ} (hs : 1 < s.re) (k : Fin 6) :
    0 < (modeRate μ ν γ s k).re := by
  fin_cases k <;> simp [modeRate] <;> linarith

/-- Laplace transform on `(0, ∞)` of a finite sum of decaying exponentials. -/
theorem integral_Ioi_sum_cexp {ι : Type*} (S : Finset ι) (a c : ι → ℂ)
    (hc : ∀ k ∈ S, 0 < (c k).re) :
    (∫ t in Ioi (0 : ℝ), ∑ k ∈ S, a k * cexp (-c k * t)) = ∑ k ∈ S, a k / c k := by
  rw [integral_finsetSum S fun k hk => (integrableOn_cexp_neg_mul (hc k hk)).const_mul (a k)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, integral_cexp_neg_mul (hc k hk), mul_one_div]

/-- **The Laplace transform of the von Mangoldt measure**: the six modes of `E`. -/
theorem integral_cexp_overRegularMeasure {μ ν γ : ℝ} (hμ : 0 ≤ μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) {s : ℂ} (hs : 1 < s.re) :
    (∫ t, cexp (-(s * t)) ∂overRegularMeasure μ ν γ) =
      ∑ k, modeCoeff k / modeRate μ ν γ s k := by
  unfold overRegularMeasure
  rw [integral_withDensity_eq_integral_smul (measurable_toNNReal_primeNumerator μ ν γ),
    ← integral_Ioi_sum_cexp Finset.univ modeCoeff (modeRate μ ν γ s)
      fun k _ => modeRate_re_pos hlow hhigh hs k]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (primeNumerator_nonneg hμ (le_of_lt ht)),
    Complex.real_smul, ofReal_primeNumerator_mul_cexp]

theorem sum_modeCoeff_div (μ ν γ : ℝ) (s : ℂ) :
    ∑ k, modeCoeff k / modeRate μ ν γ s k =
      1 / (s - 1) - 1 / (s - (((1 - μ : ℝ) : ℂ) + γ * I)) -
        1 / (s - (((1 - μ : ℝ) : ℂ) - γ * I)) + 1 / (s + ((3 * μ - 1 - ν : ℝ) : ℂ)) +
        1 / (s + ((3 * μ - 1 + ν : ℝ) : ℂ)) - 1 / (s + ((4 * μ - 1 : ℝ) : ℂ)) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, modeCoeff, modeRate, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  ring

/-- **The von Mangoldt measure of the over-regular system is a Beurling measure.** -/
theorem isBeurlingMeasure_overRegularMeasure {μ ν γ : ℝ} (hμ : 0 ≤ μ)
    (hlow : 0 ≤ 3 * μ - 1 - ν) (hhigh : 0 ≤ 3 * μ - 1 + ν) :
    IsBeurlingMeasure (overRegularMeasure μ ν γ) where
  support := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply measurableSet_Ici.compl]
    have he : (Ici (0 : ℝ))ᶜ ∩ Ioi 0 = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => by
      simp only [mem_inter_iff, mem_compl_iff, mem_Ici, mem_Ioi] at hx
      exact hx.1 hx.2.le
    rw [he, measure_empty]
  integrable σ hσ := by
    unfold overRegularMeasure
    rw [integrable_withDensity_iff_integrable_smul (measurable_toNNReal_primeNumerator μ ν γ)]
    have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
    have hC : Integrable (fun t : ℝ => ∑ k, modeCoeff k * cexp (-modeRate μ ν γ σ k * t))
        (volume.restrict (Ioi 0)) :=
      integrable_finsetSum _ fun k _ =>
        (integrableOn_cexp_neg_mul (modeRate_re_pos hlow hhigh hs k)).const_mul _
    refine hC.mono (((continuous_real_toNNReal.comp (continuous_primeNumerator μ ν γ)).smul
      (by fun_prop : Continuous fun t : ℝ => Real.exp (-(σ * t)))).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [← ofReal_primeNumerator_mul_cexp, NNReal.smul_def,
      Real.coe_toNNReal _ (primeNumerator_nonneg hμ (le_of_lt ht)), smul_eq_mul, norm_mul,
      norm_mul, Complex.norm_real, Complex.norm_exp]
    refine le_of_eq (congrArg _ ?_)
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-! ### The completed zeta -/

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := fun hz => by
  rw [hz, Complex.zero_re] at h
  exact lt_irrefl 0 h

/-- The rational factor `s(s - ρ)(s - ρ̄)(s + 4μ - 1)/((s + p₁)(s + p₂))` at `s = ½ + w`. -/
def overRegularRational (μ ν γ : ℝ) (w : ℂ) : ℂ :=
  (w + 1 / 2) * ((w + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I))) *
    ((w + (1 / 2 - (((1 - μ : ℝ) : ℂ) - γ * I))) * (w + (1 / 2 + ((4 * μ - 1 : ℝ) : ℂ))))) /
  ((w + (1 / 2 + ((3 * μ - 1 - ν : ℝ) : ℂ))) * (w + (1 / 2 + ((3 * μ - 1 + ν : ℝ) : ℂ))))

/-- **The completed zeta** of the over-regular system, `Γℝ(s) × (rational factor)`, `s = ½ + w`. -/
def overRegularXi (μ ν γ : ℝ) (w : ℂ) : ℂ :=
  Gammaℝ (1 / 2 + w) * overRegularRational μ ν γ w

/-- Off `s = 1` the completed zeta is `s(s - 1)Γℝ(s)ζ(s)`. -/
theorem overRegularXi_eq {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν) (hhigh : 0 ≤ 3 * μ - 1 + ν)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1 / 2) :
    overRegularXi μ ν γ w =
      (1 / 2 + w) * (1 / 2 + w - 1) * Gammaℝ (1 / 2 + w) * overRegularZeta μ ν γ (1 / 2 + w) := by
  have hq1 : (1 / 2 + w) + (3 * μ - 1 - ν) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hq2 : (1 / 2 + w) + (3 * μ - 1 + ν) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hs1 : 1 / 2 + w - 1 ≠ 0 := fun h => hw1 (by linear_combination h)
  have hρ : (w + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I))) * (w + (1 / 2 - (((1 - μ : ℝ) : ℂ) - γ * I)))
      = ((1 / 2 + w) - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 := by
    push_cast
    linear_combination (-(γ : ℂ) ^ 2) * Complex.I_sq
  unfold overRegularXi overRegularRational overRegularZeta
  rw [← mul_assoc (w + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I))), hρ]
  have hq1' : w + (1 / 2 + ((3 * μ - 1 - ν : ℝ) : ℂ)) = (1 / 2 + w) + (3 * μ - 1 - ν) := by
    push_cast; ring
  have hq2' : w + (1 / 2 + ((3 * μ - 1 + ν : ℝ) : ℂ)) = (1 / 2 + w) + (3 * μ - 1 + ν) := by
    push_cast; ring
  have e0 : w + 1 / 2 = 1 / 2 + w := by ring
  have e3 : w + (1 / 2 + ((4 * μ - 1 : ℝ) : ℂ)) = 1 / 2 + w + (4 * μ - 1) := by push_cast; ring
  rw [hq1', hq2', e0, e3]
  generalize (1 : ℂ) / 2 + w = s at hq1 hq2 hs1 ⊢
  field_simp

theorem differentiableAt_overRegularRational {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (overRegularRational μ ν γ) w := by
  have hQ1 : w + (1 / 2 + ((3 * μ - 1 - ν : ℝ) : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hQ2 : w + (1 / 2 + ((3 * μ - 1 + ν : ℝ) : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  unfold overRegularRational
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero hQ1 hQ2)

/-- The completed zeta is holomorphic on `Re w > 0`. -/
theorem analyticOnNhd_overRegularXi {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) : AnalyticOnNhd ℂ (overRegularXi μ ν γ) {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.analyticOnNhd (fun w (hw : 0 < w.re) => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (1 / 2 + z)) w :=
    (differentiableAt_Gammaℝ_of_re_pos (by simp; linarith)).comp w
      ((differentiableAt_const _).add differentiableAt_id)
  exact (hΓ.mul (differentiableAt_overRegularRational hlow hhigh hw)).differentiableWithinAt

/-- The completed zeta has no zero on `Re w > ½`. -/
theorem overRegularXi_ne_zero {μ ν γ : ℝ} (hμ : 0 < μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) {w : ℂ} (hw : 1 / 2 < w.re) :
    overRegularXi μ ν γ w ≠ 0 := by
  unfold overRegularXi overRegularRational
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
    (div_ne_zero (mul_ne_zero ?_ (mul_ne_zero ?_ (mul_ne_zero ?_ ?_))) (mul_ne_zero ?_ ?_)) <;>
    exact ne_zero_of_re_pos (by simp; linarith)

/-- The completed zeta vanishes at `w = ρ - ½`, right of the critical line. -/
theorem overRegularXi_root (μ ν γ : ℝ) :
    overRegularXi μ ν γ ((((1 - μ : ℝ) : ℂ) + γ * I) - 1 / 2) = 0 := by
  unfold overRegularXi overRegularRational
  rw [show (((1 - μ : ℝ) : ℂ) + γ * I) - 1 / 2 + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I)) = 0 by ring,
    zero_mul, mul_zero, zero_div, mul_zero]

theorem logDeriv_add_const (b w : ℂ) : logDeriv (fun z : ℂ => z + b) w = 1 / (w + b) := by
  rw [logDeriv_apply, deriv_add_const, deriv_id'']

theorem logDeriv_linear_mul {g : ℂ → ℂ} {b w : ℂ} (hb : w + b ≠ 0) (hg : g w ≠ 0)
    (hdg : DifferentiableAt ℂ g w) :
    logDeriv (fun z => (z + b) * g z) w = 1 / (w + b) + logDeriv g w := by
  rw [logDeriv_mul (f := fun z : ℂ => z + b) w hb hg (differentiableAt_id.add_const b) hdg,
    logDeriv_add_const]

/-- Logarithmic derivative of a quotient of products of linear factors. -/
theorem logDeriv_four_div_two {b₀ b₁ b₂ b₃ b₄ b₅ w : ℂ} (n0 : w + b₀ ≠ 0) (n1 : w + b₁ ≠ 0)
    (n2 : w + b₂ ≠ 0) (n3 : w + b₃ ≠ 0) (n4 : w + b₄ ≠ 0) (n5 : w + b₅ ≠ 0) :
    logDeriv (fun z => (z + b₀) * ((z + b₁) * ((z + b₂) * (z + b₃))) / ((z + b₄) * (z + b₅))) w =
      1 / (w + b₀) + 1 / (w + b₁) + 1 / (w + b₂) + 1 / (w + b₃) -
        (1 / (w + b₄) + 1 / (w + b₅)) := by
  have hP : logDeriv (fun z => (z + b₀) * ((z + b₁) * ((z + b₂) * (z + b₃)))) w =
      1 / (w + b₀) + 1 / (w + b₁) + 1 / (w + b₂) + 1 / (w + b₃) := by
    rw [logDeriv_linear_mul (g := fun z => (z + b₁) * ((z + b₂) * (z + b₃))) n0
        (mul_ne_zero n1 (mul_ne_zero n2 n3)) (by fun_prop),
      logDeriv_linear_mul (g := fun z => (z + b₂) * (z + b₃)) n1 (mul_ne_zero n2 n3) (by fun_prop),
      logDeriv_linear_mul (g := fun z => z + b₃) n2 n3 (by fun_prop), logDeriv_add_const]
    ring
  have hQ : logDeriv (fun z => (z + b₄) * (z + b₅)) w = 1 / (w + b₄) + 1 / (w + b₅) := by
    rw [logDeriv_linear_mul (g := fun z => z + b₅) n4 n5 (by fun_prop), logDeriv_add_const]
  rw [← hP, ← hQ]
  exact logDeriv_div (f := fun z => (z + b₀) * ((z + b₁) * ((z + b₂) * (z + b₃))))
    (g := fun z => (z + b₄) * (z + b₅)) w
    (mul_ne_zero n0 (mul_ne_zero n1 (mul_ne_zero n2 n3))) (mul_ne_zero n4 n5)
    (by fun_prop) (by fun_prop)

/-- **The logarithmic derivative of the completed zeta is the Beurling symbol** on `Re w > ½`. -/
theorem logDeriv_overRegularXi {μ ν γ : ℝ} (hμ : 0 < μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) {w : ℂ} (hw : 1 / 2 < w.re) :
    logDeriv (overRegularXi μ ν γ) w = beurlingLogDeriv (overRegularMeasure μ ν γ) w := by
  have hs : 0 < ((1 : ℂ) / 2 + w).re := by simp; linarith
  have hs1 : 1 < ((1 : ℂ) / 2 + w).re := by simp; linarith
  have n0 : w + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have n1 : w + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have n2 : w + (1 / 2 - (((1 - μ : ℝ) : ℂ) - γ * I)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have n3 : w + (1 / 2 + ((4 * μ - 1 : ℝ) : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have n4 : w + (1 / 2 + ((3 * μ - 1 - ν : ℝ) : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have n5 : w + (1 / 2 + ((3 * μ - 1 + ν : ℝ) : ℂ)) ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hR : logDeriv (overRegularRational μ ν γ) w =
      1 / (w + 1 / 2) + 1 / (w + (1 / 2 - (((1 - μ : ℝ) : ℂ) + γ * I))) +
        1 / (w + (1 / 2 - (((1 - μ : ℝ) : ℂ) - γ * I))) + 1 / (w + (1 / 2 + ((4 * μ - 1 : ℝ) : ℂ))) -
        (1 / (w + (1 / 2 + ((3 * μ - 1 - ν : ℝ) : ℂ))) +
          1 / (w + (1 / 2 + ((3 * μ - 1 + ν : ℝ) : ℂ)))) :=
    logDeriv_four_div_two n0 n1 n2 n3 n4 n5
  have hΓd : DifferentiableAt ℂ Gammaℝ (1 / 2 + w) := differentiableAt_Gammaℝ_of_re_pos hs
  have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 / 2 + z) w :=
    (differentiableAt_const _).add differentiableAt_id
  have hΓ : logDeriv (fun z : ℂ => Gammaℝ (1 / 2 + z)) w = logDeriv Gammaℝ (1 / 2 + w) := by
    have h := logDeriv_comp (f := Gammaℝ) (g := fun z : ℂ => 1 / 2 + z) hΓd hlin
    rw [show (fun z : ℂ => Gammaℝ (1 / 2 + z)) = Gammaℝ ∘ fun z : ℂ => 1 / 2 + z from rfl, h,
      deriv_const_add, deriv_id'', mul_one]
  have hRne : overRegularRational μ ν γ w ≠ 0 :=
    div_ne_zero (mul_ne_zero n0 (mul_ne_zero n1 (mul_ne_zero n2 n3))) (mul_ne_zero n4 n5)
  have hL := integral_cexp_overRegularMeasure (μ := μ) (ν := ν) (γ := γ) hμ.le hlow hhigh hs1
  rw [sum_modeCoeff_div] at hL
  unfold overRegularXi
  rw [logDeriv_mul (f := fun z : ℂ => Gammaℝ (1 / 2 + z)) (g := overRegularRational μ ν γ) w
    (Gammaℝ_ne_zero_of_re_pos hs) hRne (hΓd.comp w hlin)
    (differentiableAt_overRegularRational hlow hhigh (by linarith)), hΓ, hR]
  unfold beurlingLogDeriv
  rw [hL]
  ring

/-! ### Weil positivity fails -/

/-- **The over-regular Beurling system fails Weil positivity.** On every node set in `(½, ∞)`
accumulating at a point of `(½, ∞)`, some real Pick matrix of its Weil form is not positive
semidefinite: the completed zeta vanishes at `ρ - ½`, right of the line. -/
theorem overRegular_exists_probe_form_neg {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν1 : ν < 3 * μ - 1)
    (hν0 : 0 ≤ ν) {S : Set ℝ} (hS : ∀ p ∈ S, 1 / 2 < p) {p₀ : ℝ} (hp₀ : 1 / 2 < p₀)
    (hacc : ∃ᶠ x in 𝓝[≠] p₀, x ∈ S) :
    ∃ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ S) ∧
      ∑ i, ∑ j, c i * c j *
        beurlingWeilForm (overRegularMeasure μ ν γ) (probe (p i)) (probe (p j)) < 0 := by
  have hμ : 0 < μ := by linarith
  have hlow : 0 ≤ 3 * μ - 1 - ν := by linarith
  have hhigh : 0 ≤ 3 * μ - 1 + ν := by linarith
  refine exists_beurling_probe_form_neg_of_zero (isBeurlingMeasure_overRegularMeasure hμ.le hlow
    hhigh) hS hp₀ hacc (analyticOnNhd_overRegularXi hlow hhigh)
    (fun w hw => overRegularXi_ne_zero hμ hlow hhigh hw)
    (fun w hw => logDeriv_overRegularXi hμ hlow hhigh hw) ?_ (overRegularXi_root μ ν γ)
  simp
  linarith

/-- Nodes in an open interval accumulate at its midpoint. -/
theorem frequently_mem_Ioo {a b : ℝ} (hab : a < b) :
    ∃ᶠ x in 𝓝[≠] ((a + b) / 2), x ∈ Ioo a b :=
  (eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds (by linarith) (by linarith))).frequently

/-- Weil positivity fails on every interval of nodes in `[½, ∞)`. -/
theorem overRegular_exists_probe_form_neg_Ioo {μ ν γ : ℝ} (hμ2 : μ < 1 / 2)
    (hν1 : ν < 3 * μ - 1) (hν0 : 0 ≤ ν) {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a < b) :
    ∃ (n : ℕ) (p c : Fin n → ℝ), (∀ i, p i ∈ Ioo a b) ∧
      ∑ i, ∑ j, c i * c j *
        beurlingWeilForm (overRegularMeasure μ ν γ) (probe (p i)) (probe (p j)) < 0 :=
  overRegular_exists_probe_form_neg hμ2 hν1 hν0 (fun _ hp => lt_of_le_of_lt ha hp.1)
    (by linarith) (frequently_mem_Ioo hab)

/-- No Carathéodory extension: the symbol of the over-regular system is not the restriction of a
holomorphic function of nonnegative real part on `Re w > 0`. -/
theorem overRegular_not_exists_caratheodory {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν1 : ν < 3 * μ - 1)
    (hν0 : 0 ≤ ν) :
    ¬∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | 0 < z.re} ∧
      (∀ z : ℂ, 0 < z.re → 0 ≤ (G z).re) ∧
      ∀ w : ℂ, 1 / 2 < w.re → G w = beurlingLogDeriv (overRegularMeasure μ ν γ) w := by
  rintro ⟨G, hGd, hGre, hGD⟩
  have hμ : 0 < μ := by linarith
  obtain ⟨n, p, c, hp, hneg⟩ := overRegular_exists_probe_form_neg_Ioo (γ := γ) hμ2 hν1 hν0
    (a := 1) (b := 2) (by norm_num) (by norm_num)
  have h := probe_forms_nonneg_of_caratheodory
    (isBeurlingMeasure_overRegularMeasure hμ.le (by linarith) (by linarith))
    hGd hGre hGD p c fun i => by linarith [(hp i).1]
  linarith


#print axioms beurlingWeilForm_vonMangoldtMeasure
#print axioms beurling_probe_forms_nonneg_iff
#print axioms beurling_ne_zero_of_probe_forms_nonneg
#print axioms beurlingConfinedForm_probe
#print axioms beurlingProbeSymbol_vonMangoldtMeasure
#print axioms overRegularXi_eq
#print axioms overRegular_exists_probe_form_neg_Ioo
#print axioms overRegular_not_exists_caratheodory

end GaloisForLFunctions.ExclusionOfTheCriticalState
