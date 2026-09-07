import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Montgomery's pair form is a log-scale mean square of the zero power sum

For a finite family `ρ_j` of complex numbers in the strip `0 < Re ρ < 1` and a scale `x > 0`,
Montgomery's pair-correlation form (in the unconditional normalisation of
Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, which does not assume the `ρ_j` lie on a line)

`F(x) = Σ_{j,k} x^{ρ_j + ρ̄_k − 1} · w(ρ_j + ρ̄_k − 1)`,  `w(u) = 4/(4 − u²)`,

equals the Lorentzian-weighted average over logarithmic scales of the squared zero power sum:

`F(x) = ∫_ℝ e^{−2|ξ|} |Σ_j (x e^{−ξ})^{ρ_j − 1/2}|² dξ`.

The identity is elementary: `(x e^{−ξ})^{ρ−1/2} = x^{ρ−1/2} e^{−(ρ−1/2)ξ}`, the modulus squared
expands into pairs, and `∫ e^{−2|ξ|} e^{−uξ} dξ = 1/(2+u) + 1/(2−u) = w(u)` for `|Re u| < 2`.
Consequently the form is real and nonnegative for every configuration, and any sub-family's
contribution is controlled by a genuine Hilbert-space mean square — the structural fact behind
every "isolated zeros are detected, periodic arrays are not" statement about the form.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Finset Filter

/-- Montgomery's weight `w(u) = 4/(4 − u²)`. -/
def montgomeryWeight (u : ℂ) : ℂ := 4 / (4 - u ^ 2)

/-- The zero power sum `Σ_j y^{ρ_j − 1/2}` of a finite family at the scale `y`. -/
def zeroPowerSum {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (y : ℝ) : ℂ :=
  ∑ j ∈ s, (y : ℂ) ^ (ρ j - 1 / 2)

/-- Montgomery's pair form of a finite family at the scale `x`. -/
def montgomeryForm {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ s, ∑ k ∈ s,
    (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) * montgomeryWeight (ρ j + (starRingEnd ℂ) (ρ k) - 1)

/-! ## The exponential integrals -/

theorem integrableOn_cexp_neg_mul_Ioi {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun ξ : ℝ => cexp (-(c * ξ))) (Ioi 0) := by
  have hg : IntegrableOn (fun ξ : ℝ => Real.exp (-c.re * ξ)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  refine hg.mono' ((by fun_prop : Continuous fun ξ : ℝ => cexp (-(c * ξ))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Complex.norm_exp]
  apply le_of_eq
  congr 1
  simp [Complex.mul_re]

theorem integral_cexp_neg_mul_Ioi_montgomery {c : ℂ} (hc : 0 < c.re) :
    ∫ ξ in Ioi (0 : ℝ), cexp (-(c * ξ)) = 1 / c := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hderiv : ∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => -cexp (-(c * ξ)) / c) (cexp (-(c * ξ))) ξ := by
    intro ξ
    have h1 : HasDerivAt (fun y : ℝ => -(c * (y : ℂ))) (-c) ξ := by
      have := (((hasDerivAt_id ξ).ofReal_comp).const_mul c).neg
      rw [show (fun y : ℝ => -(c * (y : ℂ))) = -(fun y : ℝ => c * (y : ℂ)) from rfl]
      simpa using this
    have h2 := (h1.cexp.neg).div_const c
    exact h2.congr_deriv (by rw [div_eq_iff hc0]; ring)
  have htend : Tendsto (fun ξ : ℝ => -cexp (-(c * ξ)) / c) atTop (nhds 0) := by
    have hexp : Tendsto (fun ξ : ℝ => Real.exp (-(c.re * ξ)) / ‖c‖) atTop (nhds 0) := by
      have h1 : Tendsto (fun ξ : ℝ => -(c.re * ξ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hc tendsto_id)
      simpa using (Real.tendsto_exp_atBot.comp h1).div_const ‖c‖
    refine squeeze_zero_norm (fun ξ => ?_) hexp
    rw [norm_div, norm_neg, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := 0)
    ((hderiv 0).continuousAt.continuousWithinAt) (fun ξ _ => hderiv ξ)
    (integrableOn_cexp_neg_mul_Ioi hc) htend
  rw [key]
  simp
  field_simp

/-- The pair integral `∫ e^{−2|ξ|} e^{−uξ} dξ = w(u)` for `|Re u| < 2`. -/
theorem integrable_exp_neg_two_abs_mul_cexp {u : ℂ} (hu : |u.re| < 2) :
    Integrable (fun ξ : ℝ => ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-(u * ξ))) := by
  set f : ℝ → ℂ := fun ξ => ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-(u * ξ)) with hf
  have hu' := abs_lt.mp hu
  have h1 : EqOn f (fun ξ : ℝ => cexp (-((2 + u) * ξ))) (Ioi 0) := by
    intro ξ hξ
    simp only [f]
    rw [abs_of_pos hξ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : EqOn (fun ξ : ℝ => f (-ξ)) (fun ξ : ℝ => cexp (-((2 - u) * ξ))) (Ioi 0) := by
    intro ξ hξ
    simp only [f]
    rw [abs_neg, abs_of_pos hξ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hI1 : IntegrableOn f (Ioi 0) :=
    (integrableOn_cexp_neg_mul_Ioi (c := 2 + u) (by simp; linarith)).congr_fun
      (fun ξ hξ => (h1 hξ).symm) measurableSet_Ioi
  have hI2 : IntegrableOn (fun ξ : ℝ => f (-ξ)) (Ioi 0) :=
    (integrableOn_cexp_neg_mul_Ioi (c := 2 - u) (by simp; linarith)).congr_fun
      (fun ξ hξ => (h2 hξ).symm) measurableSet_Ioi
  have hI3 : IntegrableOn f (Iio 0) := by
    have := hI2.comp_neg
    simpa [Set.neg_Ioi] using this
  have hI4 : IntegrableOn f (Ici 0) := (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr hI1
  have := hI3.union hI4
  rw [Set.Iio_union_Ici] at this
  exact integrableOn_univ.mp this

theorem integral_exp_neg_two_abs_mul_cexp {u : ℂ} (hu : |u.re| < 2) :
    ∫ ξ : ℝ, ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-(u * ξ)) = montgomeryWeight u := by
  set f : ℝ → ℂ := fun ξ => ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-(u * ξ)) with hf
  have hu' := abs_lt.mp hu
  have h1 : EqOn f (fun ξ : ℝ => cexp (-((2 + u) * ξ))) (Ioi 0) := by
    intro ξ hξ
    simp only [f]
    rw [abs_of_pos hξ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : EqOn (fun ξ : ℝ => f (-ξ)) (fun ξ : ℝ => cexp (-((2 - u) * ξ))) (Ioi 0) := by
    intro ξ hξ
    simp only [f]
    rw [abs_neg, abs_of_pos hξ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : Integrable f := integrable_exp_neg_two_abs_mul_cexp hu
  have hsplit := integral_add_compl (s := Iio (0 : ℝ)) measurableSet_Iio hint
  rw [Set.compl_Iio] at hsplit
  have hA : ∫ ξ in Ici (0 : ℝ), f ξ = 1 / (2 + u) := by
    rw [integral_Ici_eq_integral_Ioi, setIntegral_congr_fun measurableSet_Ioi h1]
    exact integral_cexp_neg_mul_Ioi_montgomery (by simp; linarith)
  have hB : ∫ ξ in Iio (0 : ℝ), f ξ = 1 / (2 - u) := by
    rw [← integral_Iic_eq_integral_Iio]
    have hcomp := integral_comp_neg_Iic (0 : ℝ) (fun ξ => f (-ξ))
    simp only [neg_neg, neg_zero] at hcomp
    rw [hcomp, setIntegral_congr_fun measurableSet_Ioi h2]
    exact integral_cexp_neg_mul_Ioi_montgomery (by simp; linarith)
  have h2u : (2 : ℂ) + u ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2u' : (2 : ℂ) - u ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h4 : (4 : ℂ) - u ^ 2 ≠ 0 := by
    have : (4 : ℂ) - u ^ 2 = (2 - u) * (2 + u) := by ring
    rw [this]
    exact mul_ne_zero h2u' h2u
  calc ∫ ξ : ℝ, f ξ = (∫ ξ in Iio (0 : ℝ), f ξ) + ∫ ξ in Ici (0 : ℝ), f ξ := hsplit.symm
    _ = 1 / (2 - u) + 1 / (2 + u) := by rw [hA, hB]
    _ = montgomeryWeight u := by
        unfold montgomeryWeight
        field_simp
        ring

/-! ## The mean-square identity -/

/-- `(x e^{−ξ})^{s} = x^{s} e^{−sξ}` for `x > 0`. -/
theorem cpow_mul_exp_neg {x : ℝ} (hx : 0 < x) (ξ : ℝ) (s : ℂ) :
    ((x * Real.exp (-ξ) : ℝ) : ℂ) ^ s = (x : ℂ) ^ s * cexp (-(s * ξ)) := by
  rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hx.le (Real.exp_pos _).le]
  congr 1
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'), Complex.ofReal_exp,
    Complex.log_exp (by simp; exact Real.pi_pos) (by simp; exact Real.pi_pos.le)]
  congr 1
  push_cast
  ring

/-- The pair term `a_j(ξ) · conj(a_k(ξ))` is `x^{u} e^{−uξ}` with `u = ρ_j + ρ̄_k − 1`. -/
theorem pair_term_eq {x : ℝ} (hx : 0 < x) (ξ : ℝ) (a b : ℂ) :
    ((x : ℂ) ^ (a - 1 / 2) * cexp (-((a - 1 / 2) * ξ))) *
        (starRingEnd ℂ) ((x : ℂ) ^ (b - 1 / 2) * cexp (-((b - 1 / 2) * ξ)))
      = (x : ℂ) ^ (a + (starRingEnd ℂ) b - 1) * cexp (-((a + (starRingEnd ℂ) b - 1) * ξ)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hconj : (starRingEnd ℂ) ((x : ℂ) ^ (b - 1 / 2)) = (x : ℂ) ^ ((starRingEnd ℂ) (b - 1 / 2)) := by
    rw [cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)]
    simp [Complex.conj_ofReal]
  rw [map_mul, hconj, ← Complex.exp_conj]
  have hsum : (a + (starRingEnd ℂ) b - 1) = (a - 1 / 2) + (starRingEnd ℂ) (b - 1 / 2) := by
    rw [map_sub, map_div₀, map_one, map_ofNat]
    ring
  rw [hsum, cpow_add _ _ hx0]
  have hexp : cexp (-((a - 1 / 2) * ξ)) * cexp ((starRingEnd ℂ) (-((b - 1 / 2) * ξ)))
      = cexp (-(((a - 1 / 2) + (starRingEnd ℂ) (b - 1 / 2)) * ξ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp [map_neg, map_mul, Complex.conj_ofReal]
    ring
  calc (x : ℂ) ^ (a - 1 / 2) * cexp (-((a - 1 / 2) * ξ)) *
        ((x : ℂ) ^ ((starRingEnd ℂ) (b - 1 / 2)) * cexp ((starRingEnd ℂ) (-((b - 1 / 2) * ξ))))
      = ((x : ℂ) ^ (a - 1 / 2) * (x : ℂ) ^ ((starRingEnd ℂ) (b - 1 / 2))) *
          (cexp (-((a - 1 / 2) * ξ)) * cexp ((starRingEnd ℂ) (-((b - 1 / 2) * ξ)))) := by ring
    _ = _ := by rw [hexp]

/-- **Montgomery's form is the log-scale mean square of the zero power sum.** -/
theorem montgomeryForm_eq_integral {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ} (hx : 0 < x)
    (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    montgomeryForm s ρ x
      = ∫ ξ : ℝ, ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) *
          ((‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ) := by
  classical
  -- the pair exponents lie in the admissible strip
  have hstrip : ∀ j ∈ s, ∀ k ∈ s, |(ρ j + (starRingEnd ℂ) (ρ k) - 1).re| < 2 := by
    intro j hj k hk
    obtain ⟨hj0, hj1⟩ := hρ j hj
    obtain ⟨hk0, hk1⟩ := hρ k hk
    rw [abs_lt]
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
    constructor <;> linarith
  -- rewrite the integrand as a double sum of pair terms
  have hpt : ∀ ξ : ℝ, ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) *
      ((‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
          (((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-((ρ j + (starRingEnd ℂ) (ρ k) - 1) * ξ))) := by
    intro ξ
    have hz : zeroPowerSum s ρ (x * Real.exp (-ξ))
        = ∑ j ∈ s, (x : ℂ) ^ (ρ j - 1 / 2) * cexp (-((ρ j - 1 / 2) * ξ)) := by
      unfold zeroPowerSum
      refine Finset.sum_congr rfl fun j _ => ?_
      exact cpow_mul_exp_neg hx ξ (ρ j - 1 / 2)
    have hnorm : ((‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ)
        = zeroPowerSum s ρ (x * Real.exp (-ξ)) *
            (starRingEnd ℂ) (zeroPowerSum s ρ (x * Real.exp (-ξ))) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hnorm, hz, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pair_term_eq hx ξ (ρ j) (ρ k)]
    ring
  simp_rw [hpt]
  -- interchange the finite sums with the integral
  have hint : ∀ j ∈ s, ∀ k ∈ s, Integrable (fun ξ : ℝ =>
      (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
        (((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-((ρ j + (starRingEnd ℂ) (ρ k) - 1) * ξ)))) :=
    fun j hj k hk => (integrable_exp_neg_two_abs_mul_cexp (hstrip j hj k hk)).const_mul _
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ (fun k hk => hint j hj k hk))]
  unfold montgomeryForm
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ (fun k hk => hint j hj k hk)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, integral_exp_neg_two_abs_mul_cexp (hstrip j hj k hk)]

/-- The form is the coercion of a real integral. -/
theorem montgomeryForm_eq_ofReal {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ} (hx : 0 < x)
    (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    montgomeryForm s ρ x
      = ((∫ ξ : ℝ, Real.exp (-2 * |ξ|) * ‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ) := by
  rw [montgomeryForm_eq_integral s ρ hx hρ]
  rw [show (fun ξ : ℝ => ((Real.exp (-2 * |ξ|) : ℝ) : ℂ) *
      ((‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ))
      = fun ξ : ℝ => ((Real.exp (-2 * |ξ|) * ‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ) from
    funext fun ξ => by push_cast; ring]
  exact_mod_cast (integral_ofReal (𝕜 := ℂ))

/-- **Nonnegativity of Montgomery's form for every finite configuration.** -/
theorem montgomeryForm_re_nonneg {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ} (hx : 0 < x)
    (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    0 ≤ (montgomeryForm s ρ x).re := by
  rw [montgomeryForm_eq_ofReal s ρ hx hρ, Complex.ofReal_re]
  exact integral_nonneg fun ξ => by positivity

theorem montgomeryForm_im {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) {x : ℝ} (hx : 0 < x)
    (hρ : ∀ j ∈ s, 0 < (ρ j).re ∧ (ρ j).re < 1) :
    (montgomeryForm s ρ x).im = 0 := by
  rw [montgomeryForm_eq_ofReal s ρ hx hρ, Complex.ofReal_im]

end RHTower
