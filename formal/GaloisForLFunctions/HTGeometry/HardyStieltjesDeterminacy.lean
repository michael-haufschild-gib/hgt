import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteCriterion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Hardy determinacy for the Stieltjes moment problem

This module formalizes the determinacy input cited as Theorem 2 of G. D. Lin,
*Recent developments on the moment problem* (2017), in Suzuki's proof of his Theorem 1.8.

The proof is measure-theoretic.  A Stieltjes measure is pushed through `sqrt` and symmetrized.
Its ordinary moments become the complete Hamburger moments of the symmetrization.  Hardy's
condition supplies a bilateral exponential window.  Equality of moments then identifies the
analytic moment-generating functions near zero, hence on their common vertical strip, and
uniqueness of characteristic functions identifies the measures.

The theorem includes singular and atomic measures.  No density, infinite-support, or strict
Hankel hypothesis is used.
-/

open Complex MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

namespace HTGeometry

noncomputable section

/-- Two analytic scalar germs with identical complete derivative jets agree locally. -/
theorem analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hder : ∀ n : ℕ, iteratedDeriv n f z = iteratedDeriv n g z) :
    f =ᶠ[𝓝 z] g := by
  have hd : AnalyticAt ℂ (f - g) z := hf.sub hg
  have hzero : ∀ n : ℕ, iteratedDeriv n (f - g) z = 0 := by
    intro n
    rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, hder n, sub_self]
  have htop : analyticOrderAt (f - g) z = ⊤ := by
    by_contra hfin
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (f - g) z := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd]
      intro i _hi
      exact hzero i
    rw [← hm] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  have hev : (f - g) =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
  filter_upwards [hev] with x hx
  exact sub_eq_zero.mp hx

/-- Two finite measures with bilateral exponential windows around zero are determined by all
their Hamburger moments. -/
theorem measure_eq_of_moments_eq_of_bilateral_exponential_window
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμzero : 0 ∈ interior (integrableExpSet id μ))
    (hνzero : 0 ∈ interior (integrableExpSet id ν))
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂μ = ∫ x : ℝ, x ^ n ∂ν) :
    μ = ν := by
  let U : Set ℂ :=
    {z | z.re ∈ interior (integrableExpSet id μ) ∩
      interior (integrableExpSet id ν)}
  have hμAnalytic : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro z hz
    exact analyticAt_complexMGF hz.1
  have hνAnalytic : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro z hz
    exact analyticAt_complexMGF hz.2
  have hUpre : IsPreconnected U := by
    exact (convex_integrableExpSet.interior.inter
      convex_integrableExpSet.interior).linear_preimage Complex.reLm |>.isPreconnected
  have hzeroU : (0 : ℂ) ∈ U := ⟨hμzero, hνzero⟩
  have hlocal : complexMGF id μ =ᶠ[𝓝 (0 : ℂ)] complexMGF id ν := by
    apply analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
    · exact analyticAt_complexMGF hμzero
    · exact analyticAt_complexMGF hνzero
    · intro n
      rw [iteratedDeriv_complexMGF hμzero n,
        iteratedDeriv_complexMGF hνzero n]
      simp only [id_eq, zero_mul, exp_zero, mul_one]
      exact_mod_cast hmom n
  have hstrip : Set.EqOn (complexMGF id μ) (complexMGF id ν) U :=
    hμAnalytic.eqOn_of_preconnected_of_eventuallyEq hνAnalytic hUpre hzeroU hlocal
  exact Measure.ext_of_charFun (funext fun t => by
    have hit : t * I ∈ U := by
      change (t * I).re ∈ interior (integrableExpSet id μ) ∩
        interior (integrableExpSet id ν)
      change (0 : ℝ) ∈ interior (integrableExpSet id μ) ∩
        interior (integrableExpSet id ν) at hzeroU
      simpa using hzeroU
    have h := hstrip hit
    simpa only [complexMGF_id_mul_I] using h)

/-- Symmetrized square-root lift of a measure on the nonnegative half-line.  The unnormalized
sum is convenient: its pushforward by squaring is `μ + μ`. -/
def sqrtSymmetrization (μ : Measure ℝ) : Measure ℝ :=
  μ.map Real.sqrt + μ.map (fun x => -Real.sqrt x)

instance sqrtSymmetrization.instIsFiniteMeasure
    (μ : Measure ℝ) [IsFiniteMeasure μ] : IsFiniteMeasure (sqrtSymmetrization μ) := by
  unfold sqrtSymmetrization
  infer_instance

/-- Every half-integral power needed by the square-root lift is integrable when all ordinary
moments are integrable and the measure is carried by `[0,∞)`. -/
theorem integrable_sqrt_pow_of_hasHamburgerMoments
    {s : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    (hsupport : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    Integrable (fun x : ℝ => Real.sqrt x ^ n) μ := by
  have hmajor : Integrable (fun x : ℝ => 1 + |x ^ (n + 1)|) μ :=
    (integrable_const 1).add (hmom (n + 1)).1.norm
  apply Integrable.mono' hmajor (by fun_prop)
  filter_upwards [hsupport] with x hx
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg x) n)]
  by_cases hxone : x ≤ 1
  · have hsqrt : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hxone
    have hpow : Real.sqrt x ^ n ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg x) hsqrt
    exact hpow.trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hxone' : 1 ≤ x := le_of_not_ge hxone
    have hsqrt : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hxone')
    have hpow₁ : Real.sqrt x ^ n ≤ x ^ n :=
      pow_le_pow_left₀ (Real.sqrt_nonneg x) hsqrt n
    have hpow₂ : x ^ n ≤ x ^ (n + 1) :=
      pow_le_pow_right₀ hxone' (Nat.le_succ n)
    calc
      Real.sqrt x ^ n ≤ x ^ (n + 1) := hpow₁.trans hpow₂
      _ ≤ 1 + |x ^ (n + 1)| := by
        rw [abs_of_nonneg (pow_nonneg hx _)]
        linarith

/-- Every monomial is integrable against the square-root symmetrization. -/
theorem integrable_pow_sqrtSymmetrization
    {s : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    (hsupport : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n) (sqrtSymmetrization μ) := by
  have hsqrt := integrable_sqrt_pow_of_hasHamburgerMoments hmom hsupport n
  have hpos : Integrable (fun y : ℝ => y ^ n) (μ.map Real.sqrt) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => Real.sqrt x ^ n) μ
    exact hsqrt
  have hnegComp : Integrable (fun x : ℝ => (-Real.sqrt x) ^ n) μ := by
    apply Integrable.mono' hsqrt (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_pow, abs_neg,
        abs_of_nonneg (Real.sqrt_nonneg x)])
  have hneg : Integrable (fun y : ℝ => y ^ n) (μ.map (fun x => -Real.sqrt x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => (-Real.sqrt x) ^ n) μ
    exact hnegComp
  simpa only [sqrtSymmetrization, integrable_add_measure] using ⟨hpos, hneg⟩

/-- The complete Hamburger moment sequence of the square-root symmetrization depends only on the
original Stieltjes moment sequence. -/
theorem integral_pow_sqrtSymmetrization_eq
    {s : ℕ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmom : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    (hsupport : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂sqrtSymmetrization μ =
      if Even n then 2 * s (n / 2) else 0 := by
  have hsqrt := integrable_sqrt_pow_of_hasHamburgerMoments hmom hsupport n
  have hpos : Integrable (fun y : ℝ => y ^ n) (μ.map Real.sqrt) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => Real.sqrt x ^ n) μ
    exact hsqrt
  have hnegComp : Integrable (fun x : ℝ => (-Real.sqrt x) ^ n) μ := by
    apply Integrable.mono' hsqrt (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_pow, abs_neg,
        abs_of_nonneg (Real.sqrt_nonneg x)])
  have hneg : Integrable (fun y : ℝ => y ^ n) (μ.map (fun x => -Real.sqrt x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => (-Real.sqrt x) ^ n) μ
    exact hnegComp
  rw [sqrtSymmetrization, integral_add_measure hpos hneg,
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · subst n
    simp only [even_two_mul, if_true]
    have hpoint : (fun x : ℝ => Real.sqrt x ^ (2 * k)) =ᵐ[μ]
        fun x => x ^ k := by
      filter_upwards [hsupport] with x hx
      rw [pow_mul, Real.sq_sqrt hx]
    have hpointNeg : (fun x : ℝ => (-Real.sqrt x) ^ (2 * k)) =ᵐ[μ]
        fun x => x ^ k := by
      filter_upwards [hsupport] with x hx
      rw [pow_mul, neg_sq, Real.sq_sqrt hx]
    rw [integral_congr_ae hpoint, integral_congr_ae hpointNeg, (hmom k).2]
    have hdiv : 2 * k / 2 = k := by omega
    rw [hdiv]
    ring
  · subst n
    simp only [Nat.not_even_two_mul_add_one, if_false]
    have hpoint : (fun x : ℝ =>
        Real.sqrt x ^ (2 * k + 1) + (-Real.sqrt x) ^ (2 * k + 1)) = 0 := by
      funext x
      simp [pow_add, pow_mul]
    rw [← integral_add hsqrt hnegComp, hpoint]
    simp

/-- Equal Stieltjes moments give equal complete Hamburger moments after square-root
symmetrization. -/
theorem sqrtSymmetrization_moments_eq
    {s : ℕ → ℝ} {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : HasStieltjesMoments s μ) (hν : HasStieltjesMoments s ν) (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂sqrtSymmetrization μ =
      ∫ y : ℝ, y ^ n ∂sqrtSymmetrization ν := by
  rw [integral_pow_sqrtSymmetrization_eq hμ.1 hμ.2 n,
    integral_pow_sqrtSymmetrization_eq hν.1 hν.2 n]

/-- Squaring the square-root symmetrization recovers two copies of the original measure. -/
theorem map_sq_sqrtSymmetrization
    {μ : Measure ℝ} (hsupport : ∀ᵐ x ∂μ, 0 ≤ x) :
    (sqrtSymmetrization μ).map (fun y : ℝ => y ^ 2) = μ + μ := by
  rw [sqrtSymmetrization, Measure.map_add _ _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hpos : μ.map ((fun y : ℝ => y ^ 2) ∘ Real.sqrt) = μ := by
    have hcomp : ((fun y : ℝ => y ^ 2) ∘ Real.sqrt) =ᵐ[μ] id := by
      filter_upwards [hsupport] with x hx
      simp only [Function.comp_apply, Real.sq_sqrt hx, id_eq]
    calc
      μ.map ((fun y : ℝ => y ^ 2) ∘ Real.sqrt) = μ.map id :=
        Measure.map_congr hcomp
      _ = μ := Measure.map_id
  have hneg : μ.map ((fun y : ℝ => y ^ 2) ∘ fun x => -Real.sqrt x) = μ := by
    have hcomp : ((fun y : ℝ => y ^ 2) ∘ fun x => -Real.sqrt x) =ᵐ[μ] id := by
      filter_upwards [hsupport] with x hx
      simp only [Function.comp_apply, neg_sq, Real.sq_sqrt hx, id_eq]
    calc
      μ.map ((fun y : ℝ => y ^ 2) ∘ fun x => -Real.sqrt x) = μ.map id :=
        Measure.map_congr hcomp
      _ = μ := Measure.map_id
  rw [hpos, hneg]

/-- Equality of square-root symmetrizations is faithful on finite measures carried by
`[0,∞)`. -/
theorem measure_eq_of_sqrtSymmetrization_eq
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμsupport : ∀ᵐ x ∂μ, 0 ≤ x) (hνsupport : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : sqrtSymmetrization μ = sqrtSymmetrization ν) :
    μ = ν := by
  have hadd : μ + μ = ν + ν := by
    rw [← map_sq_sqrtSymmetrization hμsupport,
      ← map_sq_sqrtSymmetrization hνsupport, h]
  ext A hA
  have hAeq := congrArg (fun ρ : Measure ℝ => ρ A) hadd
  simp only [Measure.add_apply] at hAeq
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp
  have hμtop : μ A ≠ ∞ := measure_ne_top μ A
  have hνtop : ν A ≠ ∞ := measure_ne_top ν A
  have hreal := congrArg ENNReal.toReal hAeq
  rw [ENNReal.toReal_add hμtop hμtop, ENNReal.toReal_add hνtop hνtop] at hreal
  linarith

/-! ## Hardy exponential transfer -/

/-- Tonelli expansion of `cosh (r x)` into its nonnegative even-power series. -/
theorem lintegral_cosh_mul_eq_tsum_lintegral
    (r : ℝ) (μ : Measure ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (r * x)) ∂μ =
      ∑' n : ℕ, ∫⁻ x : ℝ,
        ENNReal.ofReal ((r * x) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) ∂μ := by
  calc
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (r * x)) ∂μ =
        ∫⁻ x : ℝ, ∑' n : ℕ,
          ENNReal.ofReal ((r * x) ^ (2 * n) /
            (Nat.factorial (2 * n) : ℝ)) ∂μ := by
      apply lintegral_congr
      intro x
      rw [Real.cosh_eq_tsum, ENNReal.ofReal_tsum_of_nonneg]
      · intro n
        exact div_nonneg (pow_two_mul_nonneg n (r * x)) (by positivity)
      · exact (Real.hasSum_cosh (r * x)).summable
    _ = ∑' n : ℕ, ∫⁻ x : ℝ,
          ENNReal.ofReal ((r * x) ^ (2 * n) /
            (Nat.factorial (2 * n) : ℝ)) ∂μ := by
      rw [lintegral_tsum]
      intro n
      fun_prop

/-- Equality of even moments identifies every term in the Tonelli `cosh` expansion. -/
theorem lintegral_cosh_mul_eq_of_even_moments_eq
    {r : ℝ} {μ ν : Measure ℝ}
    (hμint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) μ)
    (hνint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ (2 * n) ∂μ = ∫ x : ℝ, x ^ (2 * n) ∂ν) :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (r * x)) ∂μ =
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (r * x)) ∂ν := by
  rw [lintegral_cosh_mul_eq_tsum_lintegral,
    lintegral_cosh_mul_eq_tsum_lintegral]
  apply tsum_congr
  intro n
  have hμterm : Integrable
      (fun x : ℝ => (r * x) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)) μ := by
    have h := (hμint n).const_mul
      (r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))
    convert h using 1
    ext x
    ring
  have hνterm : Integrable
      (fun x : ℝ => (r * x) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)) ν := by
    have h := (hνint n).const_mul
      (r ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))
    convert h using 1
    ext x
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hμterm,
    ← ofReal_integral_eq_lintegral_ofReal hνterm]
  · congr 1
    simp_rw [mul_pow]
    rw [integral_div, integral_div, integral_const_mul, integral_const_mul, hmom n]
  · exact Filter.Eventually.of_forall (fun x =>
      div_nonneg (pow_two_mul_nonneg n (r * x)) (by positivity))
  · exact Filter.Eventually.of_forall (fun x =>
      div_nonneg (pow_two_mul_nonneg n (r * x)) (by positivity))

/-- A two-sided exponential majorant yields an open MGF window around the origin. -/
theorem zero_mem_interior_integrableExpSet_of_integrable_exp_abs
    {μ : Measure ℝ} {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x : ℝ => Real.exp (r * |x|)) μ) :
    0 ∈ interior (integrableExpSet id μ) := by
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr hr) hr) ?_
  intro t ht
  change Integrable (fun x : ℝ => Real.exp (t * x)) μ
  apply Integrable.mono' hexp (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * x ≤ |t * x| := le_abs_self _
      _ = |t| * |x| := abs_mul t x
      _ ≤ r * |x| := mul_le_mul_of_nonneg_right
        (le_of_lt (abs_lt.mpr ht)) (abs_nonneg x))

/-- Hardy transfer: an exponential absolute moment for one finite measure, together with equality
of all even moments, forces a (smaller) exponential absolute moment for the competitor. -/
theorem integrable_exp_half_abs_of_even_moments_eq
    {μ ν : Measure ℝ} {c : ℝ} (hc : 0 < c)
    (hμexp : Integrable (fun x : ℝ => Real.exp (c * |x|)) μ)
    (hμint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) μ)
    (hνint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) ν)
    (hmom : ∀ n : ℕ, ∫ x : ℝ, x ^ (2 * n) ∂μ = ∫ x : ℝ, x ^ (2 * n) ∂ν) :
    Integrable (fun x : ℝ => Real.exp ((c / 2) * |x|)) ν := by
  have hcoshμ : Integrable (fun x : ℝ => Real.cosh ((c / 2) * x)) μ := by
    apply Integrable.mono' hμexp (by fun_prop)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
      calc
        Real.cosh ((c / 2) * x) ≤ Real.exp (|(c / 2) * x|) := by
          rw [← Real.cosh_abs, Real.cosh_eq]
          have hle := Real.exp_le_exp.mpr
            (neg_le_self (abs_nonneg ((c / 2) * x)))
          linarith
        _ ≤ Real.exp (c * |x|) := Real.exp_le_exp.mpr (by
          rw [abs_mul, abs_div, abs_of_pos hc,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          nlinarith [abs_nonneg x])
      )
  have hcoshEq :
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh ((c / 2) * x)) ∂μ =
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh ((c / 2) * x)) ∂ν :=
    lintegral_cosh_mul_eq_of_even_moments_eq hμint hνint hmom
  have hcoshν : Integrable (fun x : ℝ => Real.cosh ((c / 2) * x)) ν := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => (Real.cosh_pos _).le)), ← hcoshEq]
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun x => (Real.cosh_pos _).le))).mp hcoshμ.2
  apply Integrable.mono' (hcoshν.const_mul 2) (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.cosh_eq]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hnonneg : 0 ≤ Real.exp (-((c / 2) * x)) := (Real.exp_pos _).le
      linarith
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have hnonneg : 0 ≤ Real.exp ((c / 2) * x) := (Real.exp_pos _).le
      have heq : (c / 2) * -x = -((c / 2) * x) := by ring
      rw [heq]
      linarith)

/-- Hardy's Stieltjes condition becomes a bilateral exponential window after square-root
symmetrization. -/
theorem integrable_exp_abs_sqrtSymmetrization_of_hardy
    {μ : Measure ℝ} {c : ℝ}
    (hHardy : Integrable (fun x : ℝ => Real.exp (c * Real.sqrt x)) μ) :
    Integrable (fun y : ℝ => Real.exp (c * |y|)) (sqrtSymmetrization μ) := by
  have hpos : Integrable (fun y : ℝ => Real.exp (c * |y|))
      (μ.map Real.sqrt) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => Real.exp (c * |Real.sqrt x|)) μ
    convert hHardy using 1
    ext x
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
  have hneg : Integrable (fun y : ℝ => Real.exp (c * |y|))
      (μ.map (fun x => -Real.sqrt x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    change Integrable (fun x : ℝ => Real.exp (c * |-Real.sqrt x|)) μ
    convert hHardy using 1
    ext x
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg x)]
  simpa only [sqrtSymmetrization, integrable_add_measure] using ⟨hpos, hneg⟩

/-- **Lin's Hardy determinacy theorem for the Stieltjes moment problem.**

If one representing measure of a Stieltjes moment sequence satisfies Hardy's condition
`integrable (exp (c * sqrt x))` for some `c > 0`, then every finite Stieltjes representing
measure of that sequence is equal to it.  This is the determinacy implication `(s2) → (s7)`
used in Suzuki's Theorem 1.8. -/
theorem measure_eq_of_hasStieltjesMoments_of_hardy
    {s : ℕ → ℝ} {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : HasStieltjesMoments s μ) (hν : HasStieltjesMoments s ν)
    {c : ℝ} (hc : 0 < c)
    (hHardy : Integrable (fun x : ℝ => Real.exp (c * Real.sqrt x)) μ) :
    μ = ν := by
  have hμexp : Integrable (fun y : ℝ => Real.exp (c * |y|))
      (sqrtSymmetrization μ) :=
    integrable_exp_abs_sqrtSymmetrization_of_hardy hHardy
  have hμint : ∀ n : ℕ, Integrable (fun y : ℝ => y ^ (2 * n))
      (sqrtSymmetrization μ) := fun n =>
    integrable_pow_sqrtSymmetrization hμ.1 hμ.2 (2 * n)
  have hνint : ∀ n : ℕ, Integrable (fun y : ℝ => y ^ (2 * n))
      (sqrtSymmetrization ν) := fun n =>
    integrable_pow_sqrtSymmetrization hν.1 hν.2 (2 * n)
  have hmom : ∀ n : ℕ,
      ∫ y : ℝ, y ^ (2 * n) ∂sqrtSymmetrization μ =
        ∫ y : ℝ, y ^ (2 * n) ∂sqrtSymmetrization ν := fun n =>
    sqrtSymmetrization_moments_eq hμ hν (2 * n)
  have hνexp : Integrable (fun y : ℝ => Real.exp ((c / 2) * |y|))
      (sqrtSymmetrization ν) :=
    integrable_exp_half_abs_of_even_moments_eq hc hμexp hμint hνint hmom
  have hμzero : 0 ∈ interior (integrableExpSet id (sqrtSymmetrization μ)) :=
    zero_mem_interior_integrableExpSet_of_integrable_exp_abs hc hμexp
  have hcHalf : 0 < c / 2 := div_pos hc (by norm_num)
  have hνzero : 0 ∈ interior (integrableExpSet id (sqrtSymmetrization ν)) :=
    zero_mem_interior_integrableExpSet_of_integrable_exp_abs hcHalf hνexp
  have hsymm : sqrtSymmetrization μ = sqrtSymmetrization ν :=
    measure_eq_of_moments_eq_of_bilateral_exponential_window hμzero hνzero
      (sqrtSymmetrization_moments_eq hμ hν)
  exact measure_eq_of_sqrtSymmetrization_eq hμ.2 hν.2 hsymm

end

end HTGeometry
