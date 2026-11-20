import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The logarithmic kernel as a Gaussian mixture

Frullani's integral `∫_0^∞ (e^{-αs} - e^{-βs})/s ds = log(β/α)` (`0 < α ≤ β`), from
`(e^{-αs} - e^{-βs})/s = ∫_α^β e^{-ts} dt` and Tonelli, represents the logarithmic kernel on
`|x - y| ≤ 2` as

  `K(x,y) = ∫_0^∞ (e^{-s(x-y)²} - e^{-4s})/(2s) ds = log(2/|x - y|)`,  `K(x,x) = ∞`.

Each Gaussian kernel `e^{-s(x-y)²} = e^{-sx²} e^{-sy²} Σ (2s)^n x^n y^n / n!` is a sum of rank-one
positive kernels, so for finite measures on `[-1, 1]` the Gram form satisfies
`2 G_s(ν, μ) ≤ G_s(ν, ν) + G_s(μ, μ)`.  Integrating in `s`, the logarithmic energy
`E(ν, μ) = ∫∫ K dν dμ ∈ [0, ∞]` of probability measures on `[-1, 1]` satisfies

  `2 E(ν, μ) ≤ E(ν, ν) + E(μ, μ)`,

with no finiteness assumption.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal NNReal Nat

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Frullani's integral -/

theorem exp_neg_sub_exp_neg_div_eq_integral {α β s : ℝ} (hs : 0 < s) :
    (Real.exp (-(α * s)) - Real.exp (-(β * s))) / s = ∫ t in α..β, Real.exp (-(t * s)) := by
  have hderiv : ∀ t ∈ uIcc α β, HasDerivAt (fun t => -Real.exp (-(t * s)) / s)
      (Real.exp (-(t * s))) t := fun t _ => by
    have h1 : HasDerivAt (fun t : ℝ => -(t * s)) (-s) t := (hasDerivAt_mul_const s).neg
    have h3 := (h1.exp.neg).div_const s
    refine h3.congr_deriv ?_
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv ((by fun_prop : Continuous fun t =>
    Real.exp (-(t * s))).intervalIntegrable _ _)]
  ring

theorem lintegral_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(t * s))) = ENNReal.ofReal (1 / t) := by
  have hint : IntegrableOn (fun s => Real.exp (-(t * s))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
    simpa [neg_mul] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ =>
    (Real.exp_pos _).le)]
  have h := integral_exp_mul_Ioi (a := -t) (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at h
  rw [h]
  congr 1; field_simp

/-- **Frullani's integral** `∫_0^∞ (e^{-αs} - e^{-βs})/s ds = log(β/α)` for `0 < α ≤ β`. -/
theorem lintegral_frullani {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal ((Real.exp (-(α * s)) - Real.exp (-(β * s))) / s) =
      ENNReal.ofReal (Real.log (β / α)) := by
  have hβ : 0 < β := hα.trans_le hαβ
  -- the inner representation
  have hin : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal ((Real.exp (-(α * s)) - Real.exp (-(β * s))) / s) =
      ∫⁻ t in Ioc α β, ENNReal.ofReal (Real.exp (-(t * s))) := fun s hs => by
    rw [exp_neg_sub_exp_neg_div_eq_integral hs, intervalIntegral.integral_of_le hαβ,
      ofReal_integral_eq_lintegral_ofReal
        ((by fun_prop : Continuous fun t => Real.exp (-(t * s))).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self) (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hin]
  have hmeas : Measurable (Function.uncurry fun s t : ℝ => ENNReal.ofReal (Real.exp (-(t * s)))) :=
    (Real.measurable_exp.comp ((measurable_snd.mul measurable_fst).neg)).ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hout : ∀ t ∈ Ioc α β, ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-(t * s))) =
      ENNReal.ofReal (1 / t) := fun t ht => lintegral_exp_neg_mul_Ioi (hα.trans ht.1)
  rw [setLIntegral_congr_fun measurableSet_Ioc hout, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hαβ, integral_one_div_of_pos hα hβ]
  · exact (ContinuousOn.integrableOn_Icc (continuousOn_const.div continuousOn_id
      fun t ht => (hα.trans_le ht.1).ne')).mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
      (one_div_pos.mpr (hα.trans ht.1)).le

/-! ### The kernel -/

/-- The integrand `(e^{-s u²} - e^{-4s})/(2s)` of the logarithmic kernel at `u = x - y`. -/
def frullaniIntegrand (u s : ℝ) : ℝ := (Real.exp (-(u ^ 2 * s)) - Real.exp (-(4 * s))) / (2 * s)

/-- The logarithmic kernel `K(x,y) = ∫_0^∞ (e^{-s(x-y)²} - e^{-4s})/(2s) ds`. -/
def frullaniLogKernel (x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, ENNReal.ofReal (frullaniIntegrand (x - y) s)

theorem frullaniIntegrand_nonneg {u s : ℝ} (hu : |u| ≤ 2) (hs : 0 < s) :
    0 ≤ frullaniIntegrand u s := by
  unfold frullaniIntegrand
  refine div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr ?_)) (by positivity)
  have : u ^ 2 ≤ 4 := by nlinarith [abs_nonneg u, sq_abs u]
  nlinarith

theorem frullaniLogKernel_symm (x y : ℝ) : frullaniLogKernel x y = frullaniLogKernel y x := by
  have h : ∀ s, frullaniIntegrand (x - y) s = frullaniIntegrand (y - x) s := fun s => by
    unfold frullaniIntegrand; rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
  simp only [frullaniLogKernel, h]

/-- **`K(x,y) = log(2/|x - y|)`** for `0 < |x - y| ≤ 2`. -/
theorem frullaniLogKernel_eq {x y : ℝ} (h0 : x ≠ y) (h2 : |x - y| ≤ 2) :
    frullaniLogKernel x y = ENNReal.ofReal (Real.log 2 - Real.log |x - y|) := by
  have hu : 0 < (x - y) ^ 2 := by positivity
  have hu4 : (x - y) ^ 2 ≤ 4 := by nlinarith [abs_nonneg (x - y), sq_abs (x - y)]
  have e : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (frullaniIntegrand (x - y) s) =
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((Real.exp (-((x - y) ^ 2 * s)) -
        Real.exp (-(4 * s))) / s) := fun s hs => by
    rw [← ENNReal.ofReal_mul (by norm_num), frullaniIntegrand]
    congr 1; field_simp
  rw [frullaniLogKernel, setLIntegral_congr_fun measurableSet_Ioi e,
    lintegral_const_mul _ (Measurable.ennreal_ofReal (by fun_prop)), lintegral_frullani hu hu4,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [Real.log_div (by norm_num) hu.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
    ← sq_abs, Real.log_pow]
  push_cast; ring

/-- **The kernel is infinite on the diagonal.** -/
theorem frullaniLogKernel_self (x : ℝ) : frullaniLogKernel x x = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  -- compare with `α = 4 e^{-2r-2}`
  set α := 4 * Real.exp (-(2 * (r : ℝ) + 2)) with hα
  have hα0 : 0 < α := by positivity
  have hα4 : α ≤ 4 := by
    rw [hα]
    have : Real.exp (-(2 * (r : ℝ) + 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [NNReal.coe_nonneg r])
    linarith
  have hfr := lintegral_frullani hα0 hα4
  have hlog : Real.log (4 / α) = 2 * (r : ℝ) + 2 := by
    rw [hα, div_mul_cancel_left₀ (by norm_num : (4 : ℝ) ≠ 0), ← Real.exp_neg, neg_neg,
      Real.log_exp]
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.log (4 / α)) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hlog, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ∫⁻ s in Ioi 0, ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal ((Real.exp (-(α * s)) - Real.exp (-(4 * s))) / s) := by
        rw [lintegral_const_mul _ (Measurable.ennreal_ofReal (by fun_prop)), hfr]
    _ ≤ frullaniLogKernel x x := by
        refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
        rw [← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold frullaniIntegrand
        rw [sub_self, show ((0 : ℝ) ^ 2 * s) = 0 by ring, neg_zero, Real.exp_zero]
        have hs' : (0 : ℝ) < s := hs
        rw [show 1 / 2 * ((Real.exp (-(α * s)) - Real.exp (-(4 * s))) / s) =
          (Real.exp (-(α * s)) - Real.exp (-(4 * s))) / (2 * s) by field_simp]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : Real.exp (-(α * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith

theorem measurable_frullaniLogKernel :
    Measurable (Function.uncurry frullaniLogKernel) := by
  have h : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (frullaniIntegrand (q.1.1 - q.1.2) q.2) := by
    unfold frullaniIntegrand
    exact Measurable.ennreal_ofReal (by fun_prop)
  exact h.lintegral_prod_right'

/-! ### The Gaussian Gram form -/

/-- `G_s(ν, μ) = ∫∫ e^{-s(x-y)²} dν(x) dμ(y)`. -/
def gaussianGram (s : ℝ) (ν μ : Measure ℝ) : ℝ :=
  ∫ p, Real.exp (-((p.1 - p.2) ^ 2 * s)) ∂(ν.prod μ)

/-- The Gaussian moments `a_n = ∫ x^n e^{-s x²} dν`. -/
def gaussianMoment (s : ℝ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ x, x ^ n * Real.exp (-(x ^ 2 * s)) ∂ν

theorem ae_prod_abs_le_one {ν μ : Measure ℝ} [SFinite μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1)
    (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) : ∀ᵐ p ∂(ν.prod μ), |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  have hm : MeasurableSet {p : ℝ × ℝ | |p.1| ≤ 1 ∧ |p.2| ≤ 1} :=
    (measurableSet_le (by fun_prop : Measurable fun p : ℝ × ℝ => |p.1|) measurable_const).inter
      (measurableSet_le (by fun_prop : Measurable fun p : ℝ × ℝ => |p.2|) measurable_const)
  refine (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => |p.1| ≤ 1 ∧ |p.2| ≤ 1) hm).mpr ?_
  filter_upwards [hν] with x hx
  filter_upwards [hμ] with y hy
  exact ⟨hx, hy⟩

theorem abs_pow_mul_exp_le_one {x s : ℝ} (hx : |x| ≤ 1) (hs : 0 ≤ s) (n : ℕ) :
    |x ^ n * Real.exp (-(x ^ 2 * s))| ≤ 1 := by
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact mul_le_one₀ (pow_le_one₀ (abs_nonneg x) hx) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

/-- **The Gram series** `G_s(ν, μ) = Σ (2s)^n/n! a_n(ν) a_n(μ)` for finite measures on `[-1, 1]`. -/
theorem hasSum_gaussianGram {s : ℝ} (hs : 0 ≤ s) {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    HasSum (fun n : ℕ => (2 * s) ^ n / n ! * (gaussianMoment s ν n * gaussianMoment s μ n))
      (gaussianGram s ν μ) := by
  set F : ℕ → ℝ × ℝ → ℝ := fun n p => (2 * s) ^ n / n ! *
    ((p.1 ^ n * Real.exp (-(p.1 ^ 2 * s))) * (p.2 ^ n * Real.exp (-(p.2 ^ 2 * s)))) with hF
  have hpt : ∀ p : ℝ × ℝ, HasSum (fun n => F n p) (Real.exp (-((p.1 - p.2) ^ 2 * s))) := by
    intro p
    have h := NormedSpace.expSeries_div_hasSum_exp (2 * s * p.1 * p.2 : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    have h2 := h.mul_left (Real.exp (-(p.1 ^ 2 * s)) * Real.exp (-(p.2 ^ 2 * s)))
    have he : Real.exp (-(p.1 ^ 2 * s)) * Real.exp (-(p.2 ^ 2 * s)) *
        Real.exp (2 * s * p.1 * p.2) = Real.exp (-((p.1 - p.2) ^ 2 * s)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [he] at h2
    refine h2.congr_fun fun n => ?_
    simp only [hF]
    rw [mul_pow, mul_pow]
    ring
  have hae := ae_prod_abs_le_one hν hμ
  have hbound : ∀ n, ∀ᵐ p ∂(ν.prod μ), ‖F n p‖ ≤ (2 * s) ^ n / n ! := fun n => by
    filter_upwards [hae] with p hp
    simp only [hF, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * s) ^ n / n !)]
    have h1 := abs_pow_mul_exp_le_one hp.1 hs n
    have h2 := abs_pow_mul_exp_le_one hp.2 hs n
    calc (2 * s) ^ n / n ! * (|p.1 ^ n * Real.exp (-(p.1 ^ 2 * s))| *
          |p.2 ^ n * Real.exp (-(p.2 ^ 2 * s))|) ≤ (2 * s) ^ n / n ! * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) (by positivity)
      _ = (2 * s) ^ n / n ! := by ring
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (ν.prod μ) := fun n =>
    (by simp only [hF]; fun_prop : Continuous (F n)).aestronglyMeasurable
  have hint : ∀ n, Integrable (F n) (ν.prod μ) := fun n =>
    Integrable.of_bound (hmeas n) _ (hbound n)
  have hval : ∀ n, ∫ p, F n p ∂(ν.prod μ) =
      (2 * s) ^ n / n ! * (gaussianMoment s ν n * gaussianMoment s μ n) := fun n => by
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, integral_prod_mul (fun x => x ^ n * Real.exp (-(x ^ 2 * s)))
      (fun y => y ^ n * Real.exp (-(y ^ 2 * s)))]
    rfl
  set C := (ν.prod μ).real univ with hC
  have hsum : Summable fun n => ∫ p, ‖F n p‖ ∂(ν.prod μ) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((Real.summable_pow_div_factorial (2 * s)).mul_right C)
    calc ∫ p, ‖F n p‖ ∂(ν.prod μ) ≤ ∫ _p, (2 * s) ^ n / n ! ∂(ν.prod μ) :=
          integral_mono_ae (hint n).norm (integrable_const _) (hbound n)
      _ = (2 * s) ^ n / n ! * C := by rw [MeasureTheory.integral_const, smul_eq_mul, hC, mul_comm]
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' n, F n p = Real.exp (-((p.1 - p.2) ^ 2 * s)) :=
    fun p => (hpt p).tsum_eq
  simp only [htsum] at hswap
  have hsumm : Summable fun n => ∫ p, F n p ∂(ν.prod μ) :=
    Summable.of_norm_bounded hsum fun n => norm_integral_le_integral_norm _
  simp only [hval] at hswap hsumm
  rw [gaussianGram, ← hswap]
  exact hsumm.hasSum

/-- **Positive-definiteness of the Gaussian kernel**: `2 G_s(ν, μ) ≤ G_s(ν, ν) + G_s(μ, μ)`. -/
theorem two_mul_gaussianGram_le {s : ℝ} (hs : 0 ≤ s) {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    2 * gaussianGram s ν μ ≤ gaussianGram s ν ν + gaussianGram s μ μ := by
  have h := ((hasSum_gaussianGram hs hν hν).add (hasSum_gaussianGram hs hμ hμ)).sub
    ((hasSum_gaussianGram hs hν hμ).mul_left 2)
  have hnn := h.nonneg fun n => by
    have : 0 ≤ (2 * s) ^ n / n ! * (gaussianMoment s ν n - gaussianMoment s μ n) ^ 2 := by
      positivity
    nlinarith [this]
  linarith

/-! ### The logarithmic energy -/

/-- The logarithmic energy `E(ν, μ) = ∫∫ K(x,y) dμ(y) dν(x) ∈ [0, ∞]` with `K = log(2/|x-y|)`. -/
def frullaniEnergy (ν μ : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, frullaniLogKernel x y ∂μ ∂ν

theorem measurable_gaussianGram (ν μ : Measure ℝ) [SFinite ν] [SFinite μ] :
    Measurable fun s => gaussianGram s ν μ := by
  have h : StronglyMeasurable fun q : ℝ × (ℝ × ℝ) => Real.exp (-((q.2.1 - q.2.2) ^ 2 * q.1)) :=
    (by fun_prop : Continuous fun q : ℝ × (ℝ × ℝ) => Real.exp (-((q.2.1 - q.2.2) ^ 2 * q.1)))
      |>.stronglyMeasurable
  exact (h.integral_prod_right' (ν := ν.prod μ)).measurable

/-- **The energy through the Gram form**:
`E(ν, μ) = ∫_0^∞ (G_s(ν, μ) - e^{-4s})/(2s) ds` for probability measures on `[-1, 1]`. -/
theorem frullaniEnergy_eq_lintegral_gram {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    frullaniEnergy ν μ = ∫⁻ s in Ioi 0,
      ENNReal.ofReal ((gaussianGram s ν μ - Real.exp (-(4 * s))) / (2 * s)) := by
  have hmk : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (frullaniIntegrand (q.1.1 - q.1.2) q.2) := by
    unfold frullaniIntegrand
    exact Measurable.ennreal_ofReal (by fun_prop)
  have hprod := lintegral_prod (μ := ν) (ν := μ) (Function.uncurry frullaniLogKernel)
    measurable_frullaniLogKernel.aemeasurable
  simp only [Function.uncurry_apply_pair] at hprod
  rw [frullaniEnergy, ← hprod]
  change ∫⁻ p : ℝ × ℝ, (∫⁻ s in Ioi 0, ENNReal.ofReal (frullaniIntegrand (p.1 - p.2) s))
    ∂(ν.prod μ) = _
  rw [lintegral_lintegral_swap hmk.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  have hae := ae_prod_abs_le_one hν hμ
  have hexp1 : ∀ p : ℝ × ℝ, Real.exp (-((p.1 - p.2) ^ 2 * s)) ≤ 1 := fun p =>
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (p.1 - p.2)])
  have hexp4 : Real.exp (-(4 * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hgi : Integrable (fun p : ℝ × ℝ => Real.exp (-((p.1 - p.2) ^ 2 * s))) (ν.prod μ) :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp1 p)
  have hint : Integrable (fun p : ℝ × ℝ => frullaniIntegrand (p.1 - p.2) s) (ν.prod μ) := by
    unfold frullaniIntegrand
    exact (hgi.sub (integrable_const _)).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (hae.mono fun p hp =>
    frullaniIntegrand_nonneg ((abs_sub p.1 p.2).trans (by linarith [hp.1, hp.2])) hs')]
  congr 1
  unfold frullaniIntegrand
  rw [MeasureTheory.integral_div, integral_sub hgi (integrable_const _), MeasureTheory.integral_const,
    probReal_univ, one_smul, gaussianGram]

/-- **Positive-definiteness of the logarithmic energy**: for probability measures on `[-1, 1]`,
`2 E(ν, μ) ≤ E(ν, ν) + E(μ, μ)` in `[0, ∞]`. -/
theorem two_mul_frullaniEnergy_le {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    2 * frullaniEnergy ν μ ≤ frullaniEnergy ν ν + frullaniEnergy μ μ := by
  have hmeasB : Measurable fun s : ℝ =>
      ENNReal.ofReal ((gaussianGram s ν ν - Real.exp (-(4 * s))) / (2 * s)) :=
    Measurable.ennreal_ofReal (((measurable_gaussianGram ν ν).sub (by fun_prop)).div
      (by fun_prop))
  rw [frullaniEnergy_eq_lintegral_gram hν hμ, frullaniEnergy_eq_lintegral_gram hν hν,
    frullaniEnergy_eq_lintegral_gram hμ hμ, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    ← lintegral_add_left hmeasB]
  refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  have hpd := two_mul_gaussianGram_le hs'.le hν hμ
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  rw [← add_div, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  linarith

/-! ### The equality case -/

/-- The Gram defect `G_s(ν,ν) + G_s(μ,μ) - 2 G_s(ν,μ) = Σ (2s)^n/n! (a_n(ν) - a_n(μ))²`. -/
theorem hasSum_gaussianGram_defect {s : ℝ} (hs : 0 ≤ s) {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    HasSum (fun n : ℕ => (2 * s) ^ n / n ! * (gaussianMoment s ν n - gaussianMoment s μ n) ^ 2)
      (gaussianGram s ν ν + gaussianGram s μ μ - 2 * gaussianGram s ν μ) := by
  have h := ((hasSum_gaussianGram hs hν hν).add (hasSum_gaussianGram hs hμ hμ)).sub
    ((hasSum_gaussianGram hs hν hμ).mul_left 2)
  exact h.congr_fun fun n => by ring

theorem gaussianMoment_eq_of_defect_nonpos {s : ℝ} (hs : 0 < s) {ν μ : Measure ℝ}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1)
    (h : gaussianGram s ν ν + gaussianGram s μ μ - 2 * gaussianGram s ν μ ≤ 0) (n : ℕ) :
    gaussianMoment s ν n = gaussianMoment s μ n := by
  have hsum := hasSum_gaussianGram_defect hs.le hν hμ
  have hnn : ∀ n : ℕ, 0 ≤ (2 * s) ^ n / n ! * (gaussianMoment s ν n - gaussianMoment s μ n) ^ 2 :=
    fun n => by positivity
  have h0 : gaussianGram s ν ν + gaussianGram s μ μ - 2 * gaussianGram s ν μ = 0 :=
    le_antisymm h (hsum.nonneg hnn)
  rw [h0] at hsum
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hsum) n
  simp only [Pi.zero_apply] at hz
  have hc : 0 < (2 * s) ^ n / n ! := by positivity
  have hz' := (mul_eq_zero.mp hz).resolve_left hc.ne'
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz')

theorem exp_neg_four_le_gaussianGram {s : ℝ} (hs : 0 ≤ s) {ν μ : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1)
    (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) : Real.exp (-(4 * s)) ≤ gaussianGram s ν μ := by
  have hae := ae_prod_abs_le_one hν hμ
  have hgi : Integrable (fun p : ℝ × ℝ => Real.exp (-((p.1 - p.2) ^ 2 * s))) (ν.prod μ) :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (p.1 - p.2)]))
  have h := integral_mono_ae (integrable_const (Real.exp (-(4 * s)))) hgi (hae.mono fun p hp => by
    refine Real.exp_le_exp.mpr ?_
    have : (p.1 - p.2) ^ 2 ≤ 4 := by
      have := (abs_sub p.1 p.2).trans (by linarith [hp.1, hp.2] : |p.1| + |p.2| ≤ 2)
      nlinarith [abs_nonneg (p.1 - p.2), sq_abs (p.1 - p.2)]
    nlinarith)
  rwa [MeasureTheory.integral_const, probReal_univ, one_smul] at h

/-- Gaussian scale density of the logarithmic energy of a signed difference. -/
def gaussianEnergyDefectDensity (ν μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((gaussianGram s ν ν + gaussianGram s μ μ - 2 * gaussianGram s ν μ) / (2*s))

theorem measurable_gaussianEnergyDefectDensity (ν μ : Measure ℝ) [SFinite ν] [SFinite μ] :
    Measurable (gaussianEnergyDefectDensity ν μ) :=
  Measurable.ennreal_ofReal ((((measurable_gaussianGram ν ν).add (measurable_gaussianGram μ μ)).sub
    ((measurable_gaussianGram ν μ).const_mul 2)).div (by fun_prop))

/-- Exact polarization at all energies, including infinite self-energy. -/
theorem frullaniEnergy_polarization {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1) :
    frullaniEnergy ν ν + frullaniEnergy μ μ = 2*frullaniEnergy ν μ +
      ∫⁻ s in Ioi 0, gaussianEnergyDefectDensity ν μ s := by
  set Φ : ℝ → Measure ℝ → Measure ℝ → ℝ := fun s ρ₁ ρ₂ =>
    (gaussianGram s ρ₁ ρ₂ - Real.exp (-(4 * s))) / (2 * s) with hΦ
  let D := gaussianEnergyDefectDensity ν μ
  have hmΦ : ∀ ρ₁ ρ₂ : Measure ℝ, [SFinite ρ₁] → [SFinite ρ₂] →
      Measurable fun s => ENNReal.ofReal (Φ s ρ₁ ρ₂) := fun ρ₁ ρ₂ _ _ =>
    Measurable.ennreal_ofReal (((measurable_gaussianGram ρ₁ ρ₂).sub (by fun_prop)).div
      (by fun_prop))
  have hmD : Measurable D := measurable_gaussianEnergyDefectDensity ν μ
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (Φ s ν ν) + ENNReal.ofReal (Φ s μ μ) =
      2 * ENNReal.ofReal (Φ s ν μ) + D s := fun s hs => by
    have hs' : (0 : ℝ) < s := hs
    have h1 := exp_neg_four_le_gaussianGram hs'.le hν hμ
    have hpd := two_mul_gaussianGram_le hs'.le hν hμ
    have hΦ0 : 0 ≤ Φ s ν μ := div_nonneg (by linarith) (by positivity)
    have hD0 : 0 ≤ (gaussianGram s ν ν + gaussianGram s μ μ - 2 * gaussianGram s ν μ) /
        (2 * s) := div_nonneg (by linarith) (by positivity)
    have hΦνν : 0 ≤ Φ s ν ν := div_nonneg (by linarith [exp_neg_four_le_gaussianGram hs'.le hν hν])
      (by positivity)
    have hΦμμ : 0 ≤ Φ s μ μ := div_nonneg (by linarith [exp_neg_four_le_gaussianGram hs'.le hμ hμ])
      (by positivity)
    rw [← ENNReal.ofReal_add hΦνν hΦμμ, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), D, gaussianEnergyDefectDensity, ← ENNReal.ofReal_add (by positivity) hD0]
    congr 1
    simp only [hΦ]
    field_simp
    ring
  rw [frullaniEnergy_eq_lintegral_gram hν hν, frullaniEnergy_eq_lintegral_gram hμ hμ,
      frullaniEnergy_eq_lintegral_gram hν hμ, ← lintegral_add_left (hmΦ ν ν),
      setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_add_right _ hmD,
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

/-- **The equality case of positive-definiteness**: if `E(ν,ν) + E(μ,μ) ≤ 2 E(ν,μ)` with finite
energies, the Gaussian moments of `ν` and `μ` agree at some `s > 0`. -/
theorem exists_gaussianMoment_eq_of_energy_le {ν μ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1)
    (hfin : frullaniEnergy ν ν + frullaniEnergy μ μ ≠ ⊤)
    (hle : frullaniEnergy ν ν + frullaniEnergy μ μ ≤ 2 * frullaniEnergy ν μ) :
    ∃ s > 0, ∀ n, gaussianMoment s ν n = gaussianMoment s μ n := by
  let D := gaussianEnergyDefectDensity ν μ
  have hmD : Measurable D := measurable_gaussianEnergyDefectDensity ν μ
  have hsum := frullaniEnergy_polarization hν hμ
  have htop : 2 * frullaniEnergy ν μ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hsum ▸ le_self_add)
  have hD0 : ∫⁻ s in Ioi 0, D s = 0 := by
    have h := hsum ▸ hle
    have h' : 2 * frullaniEnergy ν μ + ∫⁻ s in Ioi 0, D s ≤ 2 * frullaniEnergy ν μ + 0 := by
      rwa [add_zero]
    exact le_antisymm ((ENNReal.add_le_add_iff_left htop).mp h') bot_le
  rw [lintegral_eq_zero_iff hmD] at hD0
  have hvol : (volume.restrict (Ioi (0 : ℝ))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioi]; exact ENNReal.top_ne_zero
  haveI : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot := ae_neBot.mpr hvol
  obtain ⟨s, hs, hDs⟩ := ((ae_restrict_mem measurableSet_Ioi).and hD0).exists
  refine ⟨s, hs, fun n => gaussianMoment_eq_of_defect_nonpos hs hν hμ ?_ n⟩
  have := hDs
  simp only [D, gaussianEnergyDefectDensity, Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
  have hs' : (0 : ℝ) < s := hs
  rw [div_nonpos_iff] at this
  rcases this with ⟨-, h2⟩ | ⟨h1, -⟩
  · linarith
  · exact h1

/-- The Gaussian moments of a polynomial: `∫ p(x) e^{-s x²} dν = Σ p_i a_i(ν)`. -/
theorem integral_polynomial_mul_exp {s : ℝ} (hs : 0 ≤ s) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (p : Polynomial ℝ) :
    ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂ν =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * gaussianMoment s ν i := by
  have hint : ∀ i, Integrable (fun x => x ^ i * Real.exp (-(x ^ 2 * s))) ν := fun i =>
    Integrable.of_bound (by fun_prop) 1 (hν.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact abs_pow_mul_exp_le_one hx hs i)
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul (p.coeff i) |>.congr
    (Eventually.of_forall fun x => by ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gaussianMoment, ← MeasureTheory.integral_const_mul]
  congr 1; ext x; ring

/-- **Moment determinacy**: finite measures on `[-1, 1]` with equal Gaussian moments at one
`s ≥ 0` are equal (Weierstrass approximation). -/
theorem eq_of_gaussianMoment_eq {s : ℝ} (hs : 0 ≤ s) {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hν : ∀ᵐ x ∂ν, |x| ≤ 1) (hμ : ∀ᵐ y ∂μ, |y| ≤ 1)
    (h : ∀ n, gaussianMoment s ν n = gaussianMoment s μ n) : ν = μ := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hpoly : ∀ p : Polynomial ℝ, ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂ν =
      ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂μ := fun p => by
    rw [integral_polynomial_mul_exp hs hν, integral_polynomial_mul_exp hs hμ]
    simp only [h]
  set g : ℝ → ℝ := fun x => f x * Real.exp (x ^ 2 * s) with hg
  have hgc : ContinuousOn g (Icc (-1) 1) := (f.continuous.mul (by fun_prop)).continuousOn
  have hfg : ∀ x, f x = g x * Real.exp (-(x ^ 2 * s)) := fun x => by
    simp only [hg]; rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  -- approximation estimate for one measure
  have happrox : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, |x| ≤ 1) →
      ∀ (p : Polynomial ℝ) (ε : ℝ), (∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x - g x| < ε) →
      |∫ x, f x ∂ρ - ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂ρ| ≤ ε * ρ.real univ := by
    intro ρ _ hρ p ε hp
    have hbound : ∀ᵐ x ∂ρ, ‖f x - p.eval x * Real.exp (-(x ^ 2 * s))‖ ≤ ε := by
      filter_upwards [hρ] with x hx
      have hmem : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      rw [hfg x, Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(x ^ 2 * s)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
      calc |g x - p.eval x| * Real.exp (-(x ^ 2 * s)) ≤ ε * 1 := by
            refine mul_le_mul ?_ he (Real.exp_pos _).le (le_trans (abs_nonneg _) (hp x hmem).le)
            rw [abs_sub_comm]; exact (hp x hmem).le
        _ = ε := mul_one ε
    have hpint : Integrable (fun x => p.eval x * Real.exp (-(x ^ 2 * s))) ρ := by
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (p.continuous.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (-(x ^ 2 * s)))).continuousOn
          (s := Icc (-1 : ℝ) 1)
      exact Integrable.of_bound (by fun_prop) M (hρ.mono fun x hx => hM x
        ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩)
    rw [← integral_sub (f.integrable ρ) hpint]
    calc |∫ x, f x - p.eval x * Real.exp (-(x ^ 2 * s)) ∂ρ|
        ≤ ∫ x, ‖f x - p.eval x * Real.exp (-(x ^ 2 * s))‖ ∂ρ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ _x, ε ∂ρ := integral_mono_ae ((f.integrable ρ).sub hpint).norm
          (integrable_const ε) hbound
      _ = ε * ρ.real univ := by rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm]
  -- conclude by letting `ε → 0`
  refine eq_of_forall_dist_le fun ε hε => ?_
  set T := ν.real univ + μ.real univ + 1 with hT
  have hTpos : 0 < T := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 g hgc (ε / T) (by positivity)
  have h1 := happrox ν hν p (ε / T) hp
  have h2 := happrox μ hμ p (ε / T) hp
  rw [hpoly p] at h1
  rw [Real.dist_eq]
  calc |∫ x, f x ∂ν - ∫ x, f x ∂μ|
      ≤ |∫ x, f x ∂ν - ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂μ| +
        |∫ x, f x ∂μ - ∫ x, p.eval x * Real.exp (-(x ^ 2 * s)) ∂μ| := by
        rw [abs_sub_comm (∫ x, f x ∂μ)]; exact abs_sub_le _ _ _
    _ ≤ ε / T * ν.real univ + ε / T * μ.real univ := add_le_add h1 h2
    _ ≤ ε := by
        rw [← mul_add, div_mul_eq_mul_div, div_le_iff₀ hTpos]
        nlinarith [measureReal_nonneg (μ := ν) (s := univ), measureReal_nonneg (μ := μ) (s := univ)]

end GaloisForLFunctions.HTGeometry
