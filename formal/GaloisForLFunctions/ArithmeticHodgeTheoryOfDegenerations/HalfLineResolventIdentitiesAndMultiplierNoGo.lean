import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance
import GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.HTGeometry.BlockWindowFubini
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Half-line resolvent identities, depleted kernel bounds, and universal multiplier no-go

This module proves three unconditional families of results on the half-line space `M₈(-∞, 0)` and
its spectral kernel:

1. **Physical-space half-line resolvent identities on `M₈(-∞, 0)`.**
   For `b > 4` and measurable `F : ℝ → ℝ` vanishing on `[0, ∞)` with
   `Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))`, the backward half-line resolvent
   `halfLineResolvent b F x := e^{b x} ∫_x^0 F(y) e^{-b y} dy` (`x < 0`) lies in `M₈(-∞, 0)` with
   Hardy norm bound `‖T_b F‖_{M₈}² ≤ (b - 4)⁻² ‖F‖_{M₈}²`, satisfies the exact cross-pairing law
   `(a + b - 8) ⟨T_a F, T_b F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}² + (a - 4) ‖T_a F‖_{M₈}²`, the diagonal
   pairing `⟨F, T_b F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}²`, the resolvent equation
   `(b - a) T_b(T_a F) = T_a F - T_b F`, the iterated `(15/2, 8)` pairing
   `⟨F, H₈⟩_{M₈} = -‖G‖_{M₈}² + 30 ‖H₈‖_{M₈}²` (`G = T_{15/2} F`, `H₈ = T₈ G`) with its `224 / 465`
   positive depletion identity, and the Laplace identity on `{s : ℂ | s.re < 4}`.

2. **Depleted resolvent kernel bounds and piecewise holomorphic square root.**
   The depleted spectral kernel `m(z) := 4 / (1/4 - z²) - 12 / (64 - z²)` satisfies `Re m(z) < 0`
   and the single-orbit ratio bound `25 ‖m(z)‖² < -Re m(z)` throughout
   `{z : ℂ | |z.re| < 1/2 ∧ 331/4 < z.im²}`, hence unconditionally at `z_q = ρ_q - 1/2` for every
   `q : RHTower.XiZeroCopy`. Its piecewise holomorphic square root `Φ̃(z) := ±i exp(log(-m(z)) / 2)`
   is analytic on both open half-strips, conjugate-symmetric (`Φ̃(z̄) = conj(Φ̃(z))`), and satisfies
   `Φ̃(z) Φ̃(-z) = -m(z)` identically across the strip.

3. **Universal holomorphic multiplier domination no-go.**
   No countable square-bounded family (nor any finite family) of holomorphic multipliers on
   `{s : ℂ | s.re < 4}` can dominate `m(z)` in the completely positive sense
   `Re((m(z) + ∑_n ψ_n(z) ψ_n(-z)) u v) ≤ 0` across the verified off-line strip
   `{z : ℂ | 0 < |z.re| < 1/2 ∧ 431/2 ≤ z.im²}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-! ## 1. Physical-space half-line resolvent identities on `M₈(-∞, 0)` -/

/-- The backward half-line resolvent `(T_b F)(x) = e^{b x} ∫_x^0 F(y) e^{-b y} dy` for `x < 0`,
extended by `0` on `[0, ∞)`. -/
def halfLineResolvent (b : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then Real.exp (b * x) * ∫ y in Ioc x 0, F y * Real.exp (-(b * y)) else 0

@[simp]
theorem halfLineResolvent_of_neg (b : ℝ) (F : ℝ → ℝ) {x : ℝ} (hx : x < 0) :
    halfLineResolvent b F x = Real.exp (b * x) * ∫ y in Ioc x 0, F y * Real.exp (-(b * y)) := by
  simp [halfLineResolvent, hx]

theorem halfLineResolvent_eq_zero_of_nonneg (b : ℝ) (F : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    halfLineResolvent b F x = 0 := by
  simp [halfLineResolvent, not_lt.mpr hx]

/-- `halfLineResolvent b F` preserves measurability. -/
theorem measurable_halfLineResolvent (b : ℝ) {F : ℝ → ℝ} (hFm : Measurable F) :
    Measurable (halfLineResolvent b F) := by
  let S : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 ≤ 0}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  let K : ℝ × ℝ → ℝ := S.indicator fun p => F p.2 * Real.exp (-(b * p.2))
  have hKm : StronglyMeasurable K :=
    ((hFm.comp measurable_snd).mul
      (Real.continuous_exp.measurable.comp (measurable_snd.const_mul b).neg)).stronglyMeasurable.indicator hS
  have hint_m : Measurable fun x : ℝ => ∫ y, K (x, y) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right' hKm).measurable
  have hcongr : ∀ x : ℝ, (∫ y in Ioc x 0, F y * Real.exp (-(b * y))) =
      ∫ y, K (x, y) := fun x => by
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ioc x 0
    · simp [K, S, mem_Ioc.mp hy, hy]
    · have hnot : (x, y) ∉ S := fun h => hy ⟨h.1, h.2⟩
      simp [K, hy, hnot]
  have heq_res : halfLineResolvent b F =
      fun x => if x < 0 then Real.exp (b * x) * ∫ y, K (x, y) else 0 := by
    funext x
    unfold halfLineResolvent
    rw [hcongr x]
  rw [heq_res]
  exact Measurable.ite measurableSet_Iio
    ((Real.continuous_exp.measurable.comp (measurable_id.const_mul b)).mul hint_m) measurable_const

private def halfLineGauge (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  F y * Real.exp (-(4 * y))

private theorem halfLineGauge_eq_zero_of_nonneg {F : ℝ → ℝ}
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {y : ℝ} (hy : 0 ≤ y) :
    halfLineGauge F y = 0 := by
  simp [halfLineGauge, hsupp y hy]

private theorem halfLineGauge_sq (F : ℝ → ℝ) (y : ℝ) :
    halfLineGauge F y ^ 2 = F y ^ 2 * Real.exp (-(8 * y)) := by
  unfold halfLineGauge
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

private theorem halfLineResolvent_mul_exp_neg_four (b : ℝ) (F : ℝ → ℝ) {x : ℝ} (hx : x < 0) :
    halfLineResolvent b F x * Real.exp (-(4 * x)) =
      ∫ y in Ioc x 0, halfLineGauge F y * Real.exp ((b - 4) * (x - y)) := by
  rw [halfLineResolvent_of_neg b F hx]
  calc
    (Real.exp (b * x) * ∫ y in Ioc x 0, F y * Real.exp (-(b * y))) * Real.exp (-(4 * x))
      = Real.exp ((b - 4) * x) * ∫ y in Ioc x 0, F y * Real.exp (-(b * y)) := by
          rw [mul_right_comm, ← Real.exp_add]
          congr 2
          ring
    _ = ∫ y in Ioc x 0, Real.exp ((b - 4) * x) * (F y * Real.exp (-(b * y))) := by
          rw [← integral_const_mul]
    _ = ∫ y in Ioc x 0, halfLineGauge F y * Real.exp ((b - 4) * (x - y)) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
          unfold halfLineGauge
          rw [mul_left_comm (Real.exp ((b - 4) * x)), mul_assoc, ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

private theorem integrableOn_exp_mul_Iio {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Iio c) :=
  (integrableOn_exp_mul_Iic ha c).mono_set Iio_subset_Iic_self

private theorem integral_exp_mul_Iio {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ x : ℝ in Iio c, Real.exp (a * x)) = Real.exp (a * c) / a := by
  rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic ha c]

private theorem integrableOn_exp_mul_complex_Iio {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Iio c) :=
  (integrableOn_exp_mul_complex_Iic ha c).mono_set Iio_subset_Iic_self

private theorem integral_exp_mul_complex_Iio {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    (∫ x : ℝ in Iio c, Complex.exp (a * x)) = Complex.exp (a * c) / a := by
  rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_complex_Iic ha c]

private theorem integral_exp_mul_Ioc {c a b : ℝ} (hc : c ≠ 0) (hab : a ≤ b) :
    (∫ y in Ioc a b, Real.exp (c * y)) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  rw [← intervalIntegral.integral_of_le hab, sub_div]
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => Real.exp (c * y) / c) (Real.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => c * y) (c * 1) x := (hasDerivAt_id' x).const_mul c
    have h2 := h1.exp.div_const c
    have hd : Real.exp (c * x) * (c * 1) / c = Real.exp (c * x) := by
      rw [mul_one, mul_div_cancel_right₀ _ hc]
    rwa [hd] at h2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) a b)

private theorem integral_exp_sub_Ioc_le {c x : ℝ} (hc : 0 < c) (hx : x < 0) :
    (∫ y in Ioc x 0, Real.exp (c * (x - y))) ≤ c⁻¹ := by
  have heq : (fun y : ℝ => Real.exp (c * (x - y))) =
      fun y : ℝ => Real.exp (c * x) * Real.exp ((-c) * y) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, integral_exp_mul_Ioc (neg_ne_zero.mpr hc.ne') hx.le]
  have hval : Real.exp (c * x) * ((Real.exp ((-c) * 0) - Real.exp ((-c) * x)) / (-c)) =
      (1 - Real.exp (c * x)) / c := by
    have hexp : Real.exp (c * x) * Real.exp ((-c) * x) = 1 := by
      rw [← Real.exp_add]
      have h0 : c * x + (-c) * x = 0 := by ring
      rw [h0, Real.exp_zero]
    have hnum : Real.exp (c * x) * (1 - Real.exp ((-c) * x)) = Real.exp (c * x) - 1 := by
      rw [mul_sub, mul_one, hexp]
    rw [mul_zero, Real.exp_zero, mul_div_assoc', hnum, div_neg, ← neg_div, neg_sub]
  rw [hval, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (c * x)]) hc.le

private def resolventRightMajorant (c : ℝ) (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 ∧ p.2 ≤ 0 then halfLineGauge F p.2 ^ 2 * Real.exp (c * (p.1 - p.2)) else 0

private theorem integrable_resolventRightMajorant {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    Integrable (resolventRightMajorant c F) (volume.prod volume) := by
  have hwm : Measurable (halfLineGauge F) :=
    hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  have hw2 : Integrable (fun y => halfLineGauge F y ^ 2) := by
    simpa only [halfLineGauge_sq] using hF8
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  have hm : Measurable (resolventRightMajorant c F) := by
    unfold resolventRightMajorant
    exact Measurable.ite hS
      (((hwm.comp measurable_snd).pow_const 2).mul
        (Real.continuous_exp.measurable.comp
          ((measurable_fst.sub measurable_snd).const_mul c)))
      measurable_const
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · by_cases hy : y ≤ 0
    · have heq : (fun x : ℝ => resolventRightMajorant c F (x, y)) =
          (Iio y).indicator (fun x => (halfLineGauge F y ^ 2 * Real.exp (-(c * y))) *
            Real.exp (c * x)) := by
        funext x
        by_cases hx : x < y
        · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
          unfold resolventRightMajorant
          rw [if_pos ⟨hx, hy⟩, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        · have hx' : x ∉ Iio y := hx
          rw [Set.indicator_of_notMem hx']
          unfold resolventRightMajorant
          rw [if_neg (fun h => hx h.1)]
      rw [heq, integrable_indicator_iff measurableSet_Iio]
      exact (integrableOn_exp_mul_Iio hc y).const_mul _
    · have heq : (fun x : ℝ => resolventRightMajorant c F (x, y)) = fun _ => 0 := by
        funext x
        unfold resolventRightMajorant
        rw [if_neg (fun h => hy h.2)]
      rw [heq]
      exact integrable_zero _ _ _
  · have hval : (fun y : ℝ => ∫ x, ‖resolventRightMajorant c F (x, y)‖) =
        fun y : ℝ => c⁻¹ * halfLineGauge F y ^ 2 := by
      funext y
      by_cases hy : y ≤ 0
      · have hnn : ∀ x, 0 ≤ resolventRightMajorant c F (x, y) := fun x => by
          unfold resolventRightMajorant
          split_ifs
          · positivity
          · exact le_rfl
        simp_rw [Real.norm_of_nonneg (hnn _)]
        have heq : (fun x : ℝ => resolventRightMajorant c F (x, y)) =
            (Iio y).indicator (fun x => (halfLineGauge F y ^ 2 * Real.exp (-(c * y))) *
              Real.exp (c * x)) := by
          funext x
          by_cases hx : x < y
          · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
            unfold resolventRightMajorant
            rw [if_pos ⟨hx, hy⟩, mul_assoc, ← Real.exp_add]
            congr 2
            ring
          · rw [Set.indicator_of_notMem (show x ∉ Iio y from hx)]
            unfold resolventRightMajorant
            rw [if_neg (fun h => hx h.1)]
        rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
          integral_exp_mul_Iio hc y]
        have hexp : Real.exp (-(c * y)) * (Real.exp (c * y) / c) = c⁻¹ := by
          rw [mul_div_assoc', ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_div]
        rw [mul_assoc, hexp, mul_comm]
      · have hy0 : 0 ≤ y := le_of_not_ge hy
        have heq : (fun x : ℝ => ‖resolventRightMajorant c F (x, y)‖) = fun _ => 0 := by
          funext x
          unfold resolventRightMajorant
          rw [if_neg (fun h => hy h.2), norm_zero]
        rw [heq, integral_zero, halfLineGauge_eq_zero_of_nonneg hsupp hy0]
        ring
    rw [hval]
    exact hw2.const_mul c⁻¹

private theorem halfLineResolvent_sq_mul_exp_neg_eight_le_majorant {b : ℝ} (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) (x : ℝ) :
    halfLineResolvent b F x ^ 2 * Real.exp (-(8 * x)) ≤
      (b - 4)⁻¹ * ∫ y, resolventRightMajorant (b - 4) F (x, y) := by
  have hc : 0 < b - 4 := sub_pos.mpr hb
  by_cases hx : x < 0
  · have hwm : Measurable (halfLineGauge F) :=
      hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
    have hw2 : Integrable (fun y => halfLineGauge F y ^ 2) := by
      simpa only [halfLineGauge_sq] using hF8
    have hsq : halfLineResolvent b F x ^ 2 * Real.exp (-(8 * x)) =
        (halfLineResolvent b F x * Real.exp (-(4 * x))) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [hsq, halfLineResolvent_mul_exp_neg_four b F hx]
    let ω : ℝ → ℝ := fun y => Real.exp ((b - 4) * (x - y))
    have hω_nn : ∀ y, 0 ≤ ω y := fun _ => (Real.exp_pos _).le
    have hω_cont : Continuous ω := by fun_prop
    have hω_int : Integrable ω (volume.restrict (Ioc x 0)) :=
      hω_cont.integrableOn_Ioc
    have hωw2_int : Integrable (fun y => ω y * halfLineGauge F y ^ 2)
        (volume.restrict (Ioc x 0)) := by
      refine Integrable.mono' hw2.restrict
        (hω_cont.aestronglyMeasurable.mul (hwm.pow_const 2).aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun y hy => by
        rw [Real.norm_of_nonneg (mul_nonneg (hω_nn y) (sq_nonneg _))]
        have hle1 : ω y ≤ 1 := by
          dsimp only [ω]
          exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith [hy.1]))
        exact mul_le_of_le_one_left (sq_nonneg _) hle1
    have hcs := HTGeometry.sq_integral_weighted_le (μ := volume.restrict (Ioc x 0))
      hω_nn hω_cont.aestronglyMeasurable hwm.aestronglyMeasurable hω_int hωw2_int
    have hrewrite : (∫ y in Ioc x 0, halfLineGauge F y * Real.exp ((b - 4) * (x - y))) =
        ∫ y in Ioc x 0, ω y * halfLineGauge F y :=
      setIntegral_congr_fun measurableSet_Ioc fun y _ => mul_comm _ _
    have hmaj_eq : (∫ y in Ioc x 0, ω y * halfLineGauge F y ^ 2) =
        ∫ y, resolventRightMajorant (b - 4) F (x, y) := by
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
      funext y
      by_cases hy : y ∈ Ioc x 0
      · rw [Set.indicator_of_mem hy]
        unfold resolventRightMajorant
        rw [if_pos ⟨hy.1, hy.2⟩, mul_comm]
      · rw [Set.indicator_of_notMem hy]
        unfold resolventRightMajorant
        rw [if_neg (fun h => hy ⟨h.1, h.2⟩)]
    rw [hrewrite]
    refine hcs.trans ?_
    rw [hmaj_eq]
    exact mul_le_mul_of_nonneg_right (integral_exp_sub_Ioc_le hc hx)
      (integral_nonneg fun y => by
        unfold resolventRightMajorant
        split_ifs
        · positivity
        · exact le_rfl)
  · rw [halfLineResolvent_eq_zero_of_nonneg b F (le_of_not_gt hx)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (integral_nonneg fun y => by
      unfold resolventRightMajorant
      split_ifs
      · positivity
      · exact le_rfl)

/-- For `b > 4`, `halfLineResolvent b F` retains finite eighth exponential mass. -/
theorem integrable_halfLineResolvent_sq_mul_exp_neg_eight {b : ℝ} (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    Integrable (fun u => halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) := by
  have hc : 0 < b - 4 := sub_pos.mpr hb
  have hK := integrable_resolventRightMajorant hc hFm hsupp hF8
  have hmaj : Integrable (fun x => (b - 4)⁻¹ * ∫ y, resolventRightMajorant (b - 4) F (x, y)) :=
    hK.integral_prod_left.const_mul (b - 4)⁻¹
  have hres_m : Measurable (fun u => halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) :=
    ((measurable_halfLineResolvent b hFm).pow_const 2).mul
      (Real.continuous_exp.measurable.comp (measurable_id.const_mul 8).neg)
  refine Integrable.mono' hmaj hres_m.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact halfLineResolvent_sq_mul_exp_neg_eight_le_majorant hb hFm hF8 x

/-- Hardy norm bound on `M₈(-∞, 0)`:
`∫_{u<0} (T_b F)(u)² e^{-8u} du ≤ (b - 4)⁻² ∫_{u<0} F(u)² e^{-8u} du`. -/
theorem integral_halfLineResolvent_sq_mul_exp_neg_eight_le {b : ℝ} (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) ≤
      (b - 4)⁻¹ ^ 2 * ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hc : 0 < b - 4 := sub_pos.mpr hb
  have hK := integrable_resolventRightMajorant hc hFm hsupp hF8
  have hres_int := integrable_halfLineResolvent_sq_mul_exp_neg_eight hb hFm hsupp hF8
  have hmaj : Integrable (fun x => (b - 4)⁻¹ * ∫ y, resolventRightMajorant (b - 4) F (x, y)) :=
    hK.integral_prod_left.const_mul (b - 4)⁻¹
  have hle1 : (∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) ≤
      ∫ u, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u)) :=
    setIntegral_le_integral (s := Iio (0 : ℝ)) hres_int (Eventually.of_forall fun _ => by positivity)
  have hle2 : (∫ u, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) ≤
      ∫ x, (b - 4)⁻¹ * ∫ y, resolventRightMajorant (b - 4) F (x, y) :=
    integral_mono hres_int hmaj (halfLineResolvent_sq_mul_exp_neg_eight_le_majorant hb hFm hF8)
  have hswap : (∫ x, (b - 4)⁻¹ * ∫ y, resolventRightMajorant (b - 4) F (x, y)) =
      (b - 4)⁻¹ * ∫ y, ∫ x, resolventRightMajorant (b - 4) F (x, y) := by
    rw [integral_const_mul,
      integral_integral_swap (f := fun x y => resolventRightMajorant (b - 4) F (x, y)) hK]
  have Dinner : (fun y : ℝ => ∫ x, resolventRightMajorant (b - 4) F (x, y)) =
      fun y : ℝ => (b - 4)⁻¹ * (F y ^ 2 * Real.exp (-(8 * y))) := by
    funext y
    by_cases hy : y ≤ 0
    · have heq : (fun x : ℝ => resolventRightMajorant (b - 4) F (x, y)) =
          (Iio y).indicator (fun x => (halfLineGauge F y ^ 2 * Real.exp (-((b - 4) * y))) *
            Real.exp ((b - 4) * x)) := by
        funext x
        by_cases hx : x < y
        · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
          unfold resolventRightMajorant
          rw [if_pos ⟨hx, hy⟩, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        · rw [Set.indicator_of_notMem (show x ∉ Iio y from hx)]
          unfold resolventRightMajorant
          rw [if_neg (fun h => hx h.1)]
      rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
        integral_exp_mul_Iio hc y, halfLineGauge_sq]
      have hexp : Real.exp (-((b - 4) * y)) * (Real.exp ((b - 4) * y) / (b - 4)) = (b - 4)⁻¹ := by
        rw [mul_div_assoc', ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_div]
      rw [mul_assoc, hexp, mul_comm]
    · have hy0 : 0 ≤ y := le_of_not_ge hy
      have heq : (fun x : ℝ => resolventRightMajorant (b - 4) F (x, y)) = fun _ => 0 := by
        funext x
        unfold resolventRightMajorant
        rw [if_neg (fun h => hy h.2)]
      rw [heq, integral_zero, hsupp y hy0]
      ring
  have hset_eq : (∫ y, F y ^ 2 * Real.exp (-(8 * y))) =
      ∫ y in Iio 0, F y ^ 2 * Real.exp (-(8 * y)) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    by_cases hy : y < 0
    · rw [Set.indicator_of_mem (mem_Iio.mpr hy)]
    · rw [Set.indicator_of_notMem (show y ∉ Iio 0 from hy), hsupp y (le_of_not_gt hy)]
      ring
  calc
    (∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u)))
      ≤ (b - 4)⁻¹ * ∫ y, ∫ x, resolventRightMajorant (b - 4) F (x, y) := by
          linarith only [hle1, hle2, hswap]
    _ = (b - 4)⁻¹ ^ 2 * ∫ u in Iio 0, F u ^ 2 * Real.exp (-(8 * u)) := by
          rw [Dinner, integral_const_mul, hset_eq, sq, mul_assoc]

private def resolventPairKernel (c : ℝ) (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 ∧ p.2 ≤ 0 then
    halfLineGauge F p.1 * halfLineGauge F p.2 * Real.exp (c * (p.1 - p.2))
  else 0

private theorem integrable_resolventPairKernel {c : ℝ} (hc : 0 < c)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    Integrable (resolventPairKernel c F) (volume.prod volume) := by
  have hwm : Measurable (halfLineGauge F) :=
    hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  have hw2 : Integrable (fun y => halfLineGauge F y ^ 2) := by
    simpa only [halfLineGauge_sq] using hF8
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  have hm : Measurable (resolventPairKernel c F) := by
    unfold resolventPairKernel
    exact Measurable.ite hS
      (((hwm.comp measurable_fst).mul (hwm.comp measurable_snd)).mul
        (Real.continuous_exp.measurable.comp
          ((measurable_fst.sub measurable_snd).const_mul c)))
      measurable_const
  let K_left : ℝ × ℝ → ℝ := fun p =>
    if p.1 < p.2 ∧ p.2 ≤ 0 then halfLineGauge F p.1 ^ 2 * Real.exp (c * (p.1 - p.2)) else 0
  have hKl_m : Measurable K_left := by
    dsimp only [K_left]
    exact Measurable.ite hS
      (((hwm.comp measurable_fst).pow_const 2).mul
        (Real.continuous_exp.measurable.comp
          ((measurable_fst.sub measurable_snd).const_mul c)))
      measurable_const
  have hKl_int : Integrable K_left (volume.prod volume) := by
    rw [integrable_prod_iff hKl_m.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · by_cases hx : x < 0
      · have heq : (fun y : ℝ => K_left (x, y)) =
            (Ioc x 0).indicator (fun y => halfLineGauge F x ^ 2 * Real.exp (c * (x - y))) := by
          funext y
          by_cases hy : y ∈ Ioc x 0
          · rw [Set.indicator_of_mem hy]
            dsimp only [K_left]
            rw [if_pos ⟨hy.1, hy.2⟩]
          · rw [Set.indicator_of_notMem hy]
            dsimp only [K_left]
            rw [if_neg (fun h => hy ⟨h.1, h.2⟩)]
        rw [heq, integrable_indicator_iff measurableSet_Ioc]
        exact Integrable.const_mul
          (Continuous.integrableOn_Ioc (by fun_prop : Continuous fun y : ℝ => Real.exp (c * (x - y))))
          (halfLineGauge F x ^ 2)
      · have heq : (fun y : ℝ => K_left (x, y)) = fun _ => 0 := by
          funext y
          dsimp only [K_left]
          rw [if_neg (fun h => hx (h.1.trans_le h.2))]
        rw [heq]
        exact integrable_zero _ _ _
    · refine Integrable.mono' (hw2.const_mul c⁻¹)
        (hKl_m.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      have hnn : ∀ y, 0 ≤ K_left (x, y) := fun y => by
        dsimp only [K_left]
        split_ifs
        · positivity
        · exact le_rfl
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simp_rw [Real.norm_of_nonneg (hnn _)]
      by_cases hx : x < 0
      · have heq : (fun y : ℝ => K_left (x, y)) =
            (Ioc x 0).indicator (fun y => halfLineGauge F x ^ 2 * Real.exp (c * (x - y))) := by
          funext y
          by_cases hy : y ∈ Ioc x 0
          · rw [Set.indicator_of_mem hy]
            dsimp only [K_left]
            rw [if_pos ⟨hy.1, hy.2⟩]
          · rw [Set.indicator_of_notMem hy]
            dsimp only [K_left]
            rw [if_neg (fun h => hy ⟨h.1, h.2⟩)]
        rw [heq, integral_indicator measurableSet_Ioc, integral_const_mul, mul_comm c⁻¹]
        exact mul_le_mul_of_nonneg_left (integral_exp_sub_Ioc_le hc hx) (sq_nonneg _)
      · have heq : (fun y : ℝ => K_left (x, y)) = fun _ => 0 := by
          funext y
          dsimp only [K_left]
          rw [if_neg (fun h => hx (h.1.trans_le h.2))]
        rw [heq, integral_zero]
        positivity
  have hKr_int := integrable_resolventRightMajorant hc hFm hsupp hF8
  refine Integrable.mono' ((hKl_int.add hKr_int).div_const 2) hm.aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  unfold resolventPairKernel resolventRightMajorant
  dsimp only [K_left, Pi.add_apply]
  by_cases hp : p.1 < p.2 ∧ p.2 ≤ 0
  · simp only [if_pos hp, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos (c * (p.1 - p.2)))]
    have hexp_pos : 0 ≤ Real.exp (c * (p.1 - p.2)) := (Real.exp_pos _).le
    have hab : |halfLineGauge F p.1| * |halfLineGauge F p.2| ≤
        (halfLineGauge F p.1 ^ 2 + halfLineGauge F p.2 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|halfLineGauge F p.1| - |halfLineGauge F p.2|),
        sq_abs (halfLineGauge F p.1), sq_abs (halfLineGauge F p.2)]
    calc
      |halfLineGauge F p.1| * |halfLineGauge F p.2| * Real.exp (c * (p.1 - p.2))
        ≤ ((halfLineGauge F p.1 ^ 2 + halfLineGauge F p.2 ^ 2) / 2) *
            Real.exp (c * (p.1 - p.2)) := mul_le_mul_of_nonneg_right hab hexp_pos
      _ = (halfLineGauge F p.1 ^ 2 * Real.exp (c * (p.1 - p.2)) +
            halfLineGauge F p.2 ^ 2 * Real.exp (c * (p.1 - p.2))) / 2 := by ring
  · simp [if_neg hp]

private theorem integral_resolventPairKernel_eq {b : ℝ} (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (∫ p, resolventPairKernel (b - 4) F p ∂(volume.prod volume)) =
      ∫ u in Iio 0, F u * halfLineResolvent b F u * Real.exp (-(8 * u)) := by
  have hc : 0 < b - 4 := sub_pos.mpr hb
  rw [integral_prod (resolventPairKernel (b - 4) F)
    (integrable_resolventPairKernel hc hFm hsupp hF8)]
  rw [← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases hx : x < 0
  · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
    have heq : (fun y : ℝ => resolventPairKernel (b - 4) F (x, y)) =
        (Ioc x 0).indicator
          (fun y => halfLineGauge F x * (halfLineGauge F y * Real.exp ((b - 4) * (x - y)))) := by
      funext y
      by_cases hy : y ∈ Ioc x 0
      · rw [Set.indicator_of_mem hy]
        unfold resolventPairKernel
        rw [if_pos ⟨hy.1, hy.2⟩, mul_assoc]
      · rw [Set.indicator_of_notMem hy]
        unfold resolventPairKernel
        rw [if_neg (fun h => hy ⟨h.1, h.2⟩)]
    rw [heq, integral_indicator measurableSet_Ioc, integral_const_mul,
      ← halfLineResolvent_mul_exp_neg_four b F hx]
    unfold halfLineGauge
    rw [mul_assoc, mul_left_comm (Real.exp (-(4 * x))), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Iio 0 from hx)]
    have heq : (fun y : ℝ => resolventPairKernel (b - 4) F (x, y)) = fun _ => 0 := by
      funext y
      unfold resolventPairKernel
      rw [if_neg (fun h => hx (h.1.trans_le h.2))]
    rw [heq, integral_zero]

private theorem volume_prod_diagonal_eq_zero :
    (volume.prod volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [Measure.prod_apply hm]
  simp

/-- Fundamental symmetric pairing relation for two half-line resolvents `T_a F` and `T_b F`
(`a, b > 4`) in `M₈(-∞, 0)`. -/
theorem mul_integral_halfLineResolvent_mul_eq_add_pairings {a b : ℝ} (ha : 4 < a) (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (a + b - 8) *
        (∫ u in Iio 0, halfLineResolvent a F u * halfLineResolvent b F u * Real.exp (-(8 * u))) =
      (∫ u in Iio 0, F u * halfLineResolvent b F u * Real.exp (-(8 * u))) +
        (∫ u in Iio 0, F u * halfLineResolvent a F u * Real.exp (-(8 * u))) := by
  set ca : ℝ := a - 4
  set cb : ℝ := b - 4
  have hca : 0 < ca := sub_pos.mpr ha
  have hcb : 0 < cb := sub_pos.mpr hb
  have hcab : 0 < ca + cb := add_pos hca hcb
  have hwm : Measurable (halfLineGauge F) :=
    hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  let T : ℝ × (ℝ × ℝ) → ℝ := fun q =>
    if q.1 < q.2.1 ∧ q.1 < q.2.2 ∧ q.2.1 ≤ 0 ∧ q.2.2 ≤ 0 then
      halfLineGauge F q.2.1 * halfLineGauge F q.2.2 *
        Real.exp (ca * (q.1 - q.2.1) + cb * (q.1 - q.2.2))
    else 0
  have hS : MeasurableSet {q : ℝ × (ℝ × ℝ) |
      q.1 < q.2.1 ∧ q.1 < q.2.2 ∧ q.2.1 ≤ 0 ∧ q.2.2 ≤ 0} :=
    (isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)).measurableSet.inter
      ((isOpen_lt continuous_fst (continuous_snd.comp continuous_snd)).measurableSet.inter
        ((isClosed_le (continuous_fst.comp continuous_snd)
            (continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ))).measurableSet.inter
          (isClosed_le (continuous_snd.comp continuous_snd)
            (continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ))).measurableSet))
  have hTm : Measurable T := by
    dsimp only [T]
    exact Measurable.ite hS
      (((hwm.comp (measurable_fst.comp measurable_snd)).mul
        (hwm.comp (measurable_snd.comp measurable_snd))).mul
        (Real.continuous_exp.measurable.comp
          (((measurable_fst.sub (measurable_fst.comp measurable_snd)).const_mul ca).add
            ((measurable_fst.sub (measurable_snd.comp measurable_snd)).const_mul cb))))
      measurable_const
  have hpa := integrable_resolventPairKernel hca hFm hsupp hF8
  have hpb := integrable_resolventPairKernel hcb hFm hsupp hF8
  have hae_ne : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using volume_prod_diagonal_eq_zero
  have hTint : Integrable T (volume.prod (volume.prod volume)) := by
    rw [integrable_prod_iff' hTm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · by_cases hp : p.1 ≤ 0 ∧ p.2 ≤ 0
      · have heq : (fun x : ℝ => T (x, p)) =
            (Iio (min p.1 p.2)).indicator (fun x =>
              (halfLineGauge F p.1 * halfLineGauge F p.2 *
                Real.exp (-(ca * p.1 + cb * p.2))) * Real.exp ((ca + cb) * x)) := by
          funext x
          by_cases hx : x < min p.1 p.2
          · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
            obtain ⟨hx1, hx2⟩ := lt_min_iff.mp hx
            dsimp only [T]
            rw [if_pos ⟨hx1, hx2, hp.1, hp.2⟩,
              mul_assoc (halfLineGauge F p.1 * halfLineGauge F p.2), ← Real.exp_add]
            congr 2
            ring
          · rw [Set.indicator_of_notMem (show x ∉ Iio (min p.1 p.2) from hx)]
            dsimp only [T]
            rw [if_neg (fun h => hx (lt_min h.1 h.2.1))]
        rw [heq, integrable_indicator_iff measurableSet_Iio]
        exact (integrableOn_exp_mul_Iio hcab (min p.1 p.2)).const_mul _
      · have heq : (fun x : ℝ => T (x, p)) = fun _ => 0 := by
          funext x
          dsimp only [T]
          rw [if_neg (fun h => hp ⟨h.2.2.1, h.2.2.2⟩)]
        rw [heq]
        exact integrable_zero _ _ _
    · have hmaj_int : Integrable (fun p : ℝ × ℝ =>
          (ca + cb)⁻¹ * (‖resolventPairKernel cb F p‖ +
            ‖resolventPairKernel ca F p.swap‖)) (volume.prod volume) :=
        (hpb.norm.add hpa.swap.norm).const_mul (ca + cb)⁻¹
      refine hmaj_int.congr ?_
      filter_upwards [hae_ne] with p hp_ne
      by_cases hp : p.1 ≤ 0 ∧ p.2 ≤ 0
      · have heq : (fun x : ℝ => ‖T (x, p)‖) =
            (Iio (min p.1 p.2)).indicator (fun x =>
              (|halfLineGauge F p.1 * halfLineGauge F p.2| *
                Real.exp (-(ca * p.1 + cb * p.2))) * Real.exp ((ca + cb) * x)) := by
          funext x
          by_cases hx : x < min p.1 p.2
          · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
            obtain ⟨hx1, hx2⟩ := lt_min_iff.mp hx
            dsimp only [T]
            rw [if_pos ⟨hx1, hx2, hp.1, hp.2⟩, Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
            congr 2
            ring
          · rw [Set.indicator_of_notMem (show x ∉ Iio (min p.1 p.2) from hx)]
            dsimp only [T]
            rw [if_neg (fun h => hx (lt_min h.1 h.2.1)), norm_zero]
        rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
          integral_exp_mul_Iio hcab (min p.1 p.2)]
        rcases lt_or_gt_of_ne hp_ne with hlt | hgt
        · have hmin : min p.1 p.2 = p.1 := min_eq_left hlt.le
          rw [hmin]
          have hcb_p : resolventPairKernel cb F p =
              halfLineGauge F p.1 * halfLineGauge F p.2 * Real.exp (cb * (p.1 - p.2)) := by
            unfold resolventPairKernel
            exact if_pos ⟨hlt, hp.2⟩
          have hca_p : resolventPairKernel ca F p.swap = 0 := by
            unfold resolventPairKernel
            exact if_neg (fun h => not_lt_of_gt hlt h.1)
          rw [hcb_p, hca_p, norm_zero, add_zero]
          have hexp : Real.exp (-(ca * p.1 + cb * p.2)) * (Real.exp ((ca + cb) * p.1) / (ca + cb)) =
              (ca + cb)⁻¹ * Real.exp (cb * (p.1 - p.2)) := by
            rw [mul_div_assoc', ← Real.exp_add, div_eq_inv_mul]
            congr 2
            ring
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (cb * (p.1 - p.2))),
            mul_assoc]
          rw [hexp]
          ring
        · have hmin : min p.1 p.2 = p.2 := min_eq_right hgt.le
          rw [hmin]
          have hcb_p : resolventPairKernel cb F p = 0 := by
            unfold resolventPairKernel
            exact if_neg (fun h => not_lt_of_gt hgt h.1)
          have hca_p : resolventPairKernel ca F p.swap =
              halfLineGauge F p.2 * halfLineGauge F p.1 * Real.exp (ca * (p.2 - p.1)) := by
            unfold resolventPairKernel
            exact if_pos ⟨hgt, hp.1⟩
          rw [hcb_p, hca_p, norm_zero, zero_add]
          have hexp : Real.exp (-(ca * p.1 + cb * p.2)) * (Real.exp ((ca + cb) * p.2) / (ca + cb)) =
              (ca + cb)⁻¹ * Real.exp (ca * (p.2 - p.1)) := by
            rw [mul_div_assoc', ← Real.exp_add, div_eq_inv_mul]
            congr 2
            ring
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (ca * (p.2 - p.1))),
            mul_assoc]
          rw [hexp]
          ring
      · have heq : (fun x : ℝ => ‖T (x, p)‖) = fun _ => 0 := by
          funext x
          dsimp only [T]
          rw [if_neg (fun h => hp ⟨h.2.2.1, h.2.2.2⟩), norm_zero]
        rw [heq, integral_zero]
        have h1 : resolventPairKernel cb F p = 0 := by
          unfold resolventPairKernel
          exact if_neg (fun h => hp ⟨(h.1.trans_le h.2).le, h.2⟩)
        have h2 : resolventPairKernel ca F p.swap = 0 := by
          unfold resolventPairKernel
          exact if_neg (fun h => hp ⟨h.2, (h.1.trans_le h.2).le⟩)
        simp [h1, h2]
  have hswap := integral_integral_swap (f := fun x p => T (x, p)) hTint
  have hlhs : (∫ x, ∫ p, T (x, p) ∂(volume.prod volume)) =
      ∫ u in Iio 0, halfLineResolvent a F u * halfLineResolvent b F u * Real.exp (-(8 * u)) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : x < 0
    · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
      let fa : ℝ → ℝ := (Ioc x 0).indicator fun y => halfLineGauge F y * Real.exp (ca * (x - y))
      let fb : ℝ → ℝ := (Ioc x 0).indicator fun z => halfLineGauge F z * Real.exp (cb * (x - z))
      have hprod : (fun p : ℝ × ℝ => T (x, p)) = fun p : ℝ × ℝ => fa p.1 * fb p.2 := by
        funext p
        by_cases hp : p.1 ∈ Ioc x 0 ∧ p.2 ∈ Ioc x 0
        · dsimp only [fa, fb, T]
          rw [Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2,
            if_pos ⟨hp.1.1, hp.2.1, hp.1.2, hp.2.2⟩,
            mul_mul_mul_comm, ← Real.exp_add]
        · dsimp only [fa, fb, T]
          rw [if_neg (fun h => hp ⟨⟨h.1, h.2.2.1⟩, ⟨h.2.1, h.2.2.2⟩⟩)]
          by_cases hp1 : p.1 ∈ Ioc x 0
          · have hp2 : p.2 ∉ Ioc x 0 := fun h2 => hp ⟨hp1, h2⟩
            rw [Set.indicator_of_notMem hp2, mul_zero]
          · rw [Set.indicator_of_notMem hp1, zero_mul]
      rw [hprod, integral_prod_mul, integral_indicator measurableSet_Ioc,
        integral_indicator measurableSet_Ioc,
        ← halfLineResolvent_mul_exp_neg_four a F hx,
        ← halfLineResolvent_mul_exp_neg_four b F hx]
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Iio 0 from hx)]
      have heq : (fun p : ℝ × ℝ => T (x, p)) = fun _ => 0 := by
        funext p
        dsimp only [T]
        rw [if_neg (fun h => hx (h.1.trans_le h.2.2.1))]
      rw [heq, integral_zero]
  have hrhs : (∫ p, (∫ x, T (x, p)) ∂(volume.prod volume)) =
      (ca + cb)⁻¹ *
        ((∫ p, resolventPairKernel cb F p ∂(volume.prod volume)) +
          ∫ p, resolventPairKernel ca F p ∂(volume.prod volume)) := by
    have hae_eq : (fun p : ℝ × ℝ => ∫ x, T (x, p)) =ᵐ[volume.prod volume]
        fun p : ℝ × ℝ => (ca + cb)⁻¹ *
          (resolventPairKernel cb F p + resolventPairKernel ca F p.swap) := by
      filter_upwards [hae_ne] with p hp_ne
      by_cases hp : p.1 ≤ 0 ∧ p.2 ≤ 0
      · have heq : (fun x : ℝ => T (x, p)) =
            (Iio (min p.1 p.2)).indicator (fun x =>
              (halfLineGauge F p.1 * halfLineGauge F p.2 *
                Real.exp (-(ca * p.1 + cb * p.2))) * Real.exp ((ca + cb) * x)) := by
          funext x
          by_cases hx : x < min p.1 p.2
          · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
            obtain ⟨hx1, hx2⟩ := lt_min_iff.mp hx
            dsimp only [T]
            rw [if_pos ⟨hx1, hx2, hp.1, hp.2⟩,
              mul_assoc (halfLineGauge F p.1 * halfLineGauge F p.2), ← Real.exp_add]
            congr 2
            ring
          · rw [Set.indicator_of_notMem (show x ∉ Iio (min p.1 p.2) from hx)]
            dsimp only [T]
            rw [if_neg (fun h => hx (lt_min h.1 h.2.1))]
        rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
          integral_exp_mul_Iio hcab (min p.1 p.2)]
        rcases lt_or_gt_of_ne hp_ne with hlt | hgt
        · rw [min_eq_left hlt.le]
          have hcb_p : resolventPairKernel cb F p =
              halfLineGauge F p.1 * halfLineGauge F p.2 * Real.exp (cb * (p.1 - p.2)) := by
            unfold resolventPairKernel
            exact if_pos ⟨hlt, hp.2⟩
          have hca_p : resolventPairKernel ca F p.swap = 0 := by
            unfold resolventPairKernel
            exact if_neg (fun h => not_lt_of_gt hlt h.1)
          rw [hcb_p, hca_p, add_zero]
          have hexp : Real.exp (-(ca * p.1 + cb * p.2)) * (Real.exp ((ca + cb) * p.1) / (ca + cb)) =
              (ca + cb)⁻¹ * Real.exp (cb * (p.1 - p.2)) := by
            rw [mul_div_assoc', ← Real.exp_add, div_eq_inv_mul]
            congr 2
            ring
          simp only [mul_assoc]
          rw [hexp]
          ring
        · rw [min_eq_right hgt.le]
          have hcb_p : resolventPairKernel cb F p = 0 := by
            unfold resolventPairKernel
            exact if_neg (fun h => not_lt_of_gt hgt h.1)
          have hca_p : resolventPairKernel ca F p.swap =
              halfLineGauge F p.2 * halfLineGauge F p.1 * Real.exp (ca * (p.2 - p.1)) := by
            unfold resolventPairKernel
            exact if_pos ⟨hgt, hp.1⟩
          rw [hcb_p, hca_p, zero_add]
          have hexp : Real.exp (-(ca * p.1 + cb * p.2)) * (Real.exp ((ca + cb) * p.2) / (ca + cb)) =
              (ca + cb)⁻¹ * Real.exp (ca * (p.2 - p.1)) := by
            rw [mul_div_assoc', ← Real.exp_add, div_eq_inv_mul]
            congr 2
            ring
          simp only [mul_assoc]
          rw [hexp]
          ring
      · have heq : (fun x : ℝ => T (x, p)) = fun _ => 0 := by
          funext x
          dsimp only [T]
          rw [if_neg (fun h => hp ⟨h.2.2.1, h.2.2.2⟩)]
        rw [heq, integral_zero]
        have h1 : resolventPairKernel cb F p = 0 := by
          unfold resolventPairKernel
          exact if_neg (fun h => hp ⟨(h.1.trans_le h.2).le, h.2⟩)
        have h2 : resolventPairKernel ca F p.swap = 0 := by
          unfold resolventPairKernel
          exact if_neg (fun h => hp ⟨h.2, (h.1.trans_le h.2).le⟩)
        simp [h1, h2]
    have hpa_swap : Integrable (fun p : ℝ × ℝ => resolventPairKernel ca F p.swap)
        (volume.prod volume) := hpa.swap
    rw [integral_congr_ae hae_eq, integral_const_mul, integral_add hpb hpa_swap,
      integral_prod_swap (resolventPairKernel ca F)]
  rw [hlhs, hrhs] at hswap
  dsimp only [ca, cb] at hswap
  rw [integral_resolventPairKernel_eq hb hFm hsupp hF8,
    integral_resolventPairKernel_eq ha hFm hsupp hF8] at hswap
  have hcab_eq : a - 4 + (b - 4) = a + b - 8 := by ring
  have hpos : 0 < a + b - 8 := by linarith
  rw [hcab_eq] at hswap
  rw [hswap, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- Exact diagonal `M₈` pairing of a profile `F` with its half-line resolvent `T_b F`:
`⟨F, T_b F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}²`. -/
theorem integral_mul_halfLineResolvent_exp_neg_eight {b : ℝ} (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (∫ u in Iio 0, F u * halfLineResolvent b F u * Real.exp (-(8 * u))) =
      (b - 4) * ∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u)) := by
  have h := mul_integral_halfLineResolvent_mul_eq_add_pairings hb hb hFm hsupp hF8
  have hsq : (∫ u in Iio 0, halfLineResolvent b F u * halfLineResolvent b F u *
      Real.exp (-(8 * u))) =
      ∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u)) :=
    setIntegral_congr_fun measurableSet_Iio fun u _ => by ring
  rw [hsq] at h
  linarith

/-- Exact cross-pairing law for two half-line resolvents on `M₈(-∞, 0)`:
`(a + b - 8) ⟨T_a F, T_b F⟩_{M₈} = (b - 4) ‖T_b F‖_{M₈}² + (a - 4) ‖T_a F‖_{M₈}²`. -/
theorem integral_halfLineResolvent_mul_halfLineResolvent_exp_neg_eight {a b : ℝ}
    (ha : 4 < a) (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (a + b - 8) *
        (∫ u in Iio 0, halfLineResolvent a F u * halfLineResolvent b F u * Real.exp (-(8 * u))) =
      (b - 4) * (∫ u in Iio 0, halfLineResolvent b F u ^ 2 * Real.exp (-(8 * u))) +
        (a - 4) * (∫ u in Iio 0, halfLineResolvent a F u ^ 2 * Real.exp (-(8 * u))) := by
  rw [mul_integral_halfLineResolvent_mul_eq_add_pairings ha hb hFm hsupp hF8,
    integral_mul_halfLineResolvent_exp_neg_eight hb hFm hsupp hF8,
    integral_mul_halfLineResolvent_exp_neg_eight ha hFm hsupp hF8]

/-- Pointwise resolvent identity on `M₈(-∞, 0)`:
`(b - a) T_b(T_a F)(x) = (T_a F)(x) - (T_b F)(x)`. -/
theorem halfLineResolvent_comp_sub {a b : ℝ} (ha : 4 < a) (hb : 4 < b)
    {F : ℝ → ℝ} (hFm : Measurable F)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) (x : ℝ) :
    (b - a) * halfLineResolvent b (halfLineResolvent a F) x =
      halfLineResolvent a F x - halfLineResolvent b F x := by
  by_cases hab : a = b
  · subst hab
    simp
  by_cases hx : x < 0
  · have hwm : Measurable (halfLineGauge F) :=
      hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
    have hw2 : Integrable (fun y => halfLineGauge F y ^ 2) := by
      simpa only [halfLineGauge_sq] using hF8
    have hF_Ioc : IntegrableOn F (Ioc x 0) := by
      have hg2 : IntegrableOn (fun y : ℝ => Real.exp (4 * y) ^ 2) (Ioc x 0) :=
        Continuous.integrableOn_Ioc (by fun_prop)
      have hmul := HTGeometry.integrable_mul_of_sq_integrable (μ := volume.restrict (Ioc x 0))
        hwm.aestronglyMeasurable (by fun_prop) hw2.restrict hg2
      refine hmul.congr (Eventually.of_forall fun y => ?_)
      dsimp only [halfLineGauge]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    let H : ℝ → ℝ → ℝ := fun t y =>
      if t < y then Real.exp ((a - b) * t) * (F y * Real.exp (-(a * y))) else 0
    have hHm : Measurable (Function.uncurry H) := by
      refine Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet ?_
        measurable_const
      exact (Real.continuous_exp.measurable.comp (measurable_fst.const_mul (a - b))).mul
        ((hFm.comp measurable_snd).mul
          (Real.continuous_exp.measurable.comp (measurable_snd.const_mul a).neg))
    have hw1 : Integrable (fun t : ℝ => Real.exp ((a - b) * t)) (volume.restrict (Ioc x 0)) :=
      Continuous.integrableOn_Ioc (by fun_prop)
    have hw2_dom : Integrable (fun y : ℝ => |F y| * Real.exp (-(a * y)))
        (volume.restrict (Ioc x 0)) := by
      refine Integrable.mono' (hF_Ioc.norm.const_mul (Real.exp (-(a * x))))
        (hF_Ioc.norm.aestronglyMeasurable.mul (by fun_prop)) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun y hy => by
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le), mul_comm]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith [hy.1, ha])) (abs_nonneg _)
    have hswap := HTGeometry.integral_swap_of_dominated_prod
      (μ := volume.restrict (Ioc x 0)) (ν := volume.restrict (Ioc x 0))
      hw1 hw2_dom hHm.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        dsimp only [Function.uncurry, H]
        split_ifs
        · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _)]
        · rw [norm_zero]
          exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    have hlhs : (∫ t in Ioc x 0, halfLineResolvent a F t * Real.exp (-(b * t))) =
        ∫ t in Ioc x 0, ∫ y in Ioc x 0, H t y := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have hTa : halfLineResolvent a F t =
          Real.exp (a * t) * ∫ y in Ioc t 0, F y * Real.exp (-(a * y)) := by
        rcases lt_or_eq_of_le ht.2 with ht0 | rfl
        · exact halfLineResolvent_of_neg a F ht0
        · rw [halfLineResolvent_eq_zero_of_nonneg a F le_rfl, Ioc_self, setIntegral_empty,
            mul_zero]
      rw [hTa, mul_right_comm, ← Real.exp_add]
      have hexp : a * t + -(b * t) = (a - b) * t := by ring
      rw [hexp, ← integral_const_mul]
      have hsub : Ioc t 0 ⊆ Ioc x 0 := Ioc_subset_Ioc_left ht.1.le
      rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
      congr 1
      funext y
      by_cases hty : y ∈ Ioc t 0
      · rw [Set.indicator_of_mem hty, Set.indicator_of_mem (hsub hty)]
        dsimp only [H]
        rw [if_pos hty.1]
      · rw [Set.indicator_of_notMem hty]
        by_cases hxy : y ∈ Ioc x 0
        · rw [Set.indicator_of_mem hxy]
          dsimp only [H]
          rw [if_neg (fun h => hty ⟨h, hxy.2⟩)]
        · rw [Set.indicator_of_notMem hxy]
    have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hrhs : (b - a) * Real.exp (b * x) * (∫ y in Ioc x 0, ∫ t in Ioc x 0, H t y) =
        halfLineResolvent a F x - halfLineResolvent b F x := by
      have hinner : (∫ y in Ioc x 0, ∫ t in Ioc x 0, H t y) =
          ∫ y in Ioc x 0,
            ((Real.exp ((a - b) * y) - Real.exp ((a - b) * x)) / (a - b)) *
              (F y * Real.exp (-(a * y))) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
        have hsub : Ioo x y ⊆ Ioc x 0 := fun t ht => ⟨ht.1, ht.2.le.trans hy.2⟩
        have heq_t : (∫ t in Ioc x 0, H t y) =
            ∫ t in Ioo x y, Real.exp ((a - b) * t) * (F y * Real.exp (-(a * y))) := by
          rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioo]
          congr 1
          funext t
          by_cases hty : t ∈ Ioo x y
          · rw [Set.indicator_of_mem hty, Set.indicator_of_mem (hsub hty)]
            dsimp only [H]
            rw [if_pos hty.2]
          · rw [Set.indicator_of_notMem hty]
            by_cases htx : t ∈ Ioc x 0
            · rw [Set.indicator_of_mem htx]
              dsimp only [H]
              rw [if_neg (fun h => hty ⟨htx.1, h⟩)]
            · rw [Set.indicator_of_notMem htx]
        rw [heq_t, ← integral_Ioc_eq_integral_Ioo, integral_mul_const,
          integral_exp_mul_Ioc hab' hy.1.le]
      rw [hinner, ← integral_const_mul]
      have hpoint : (fun y : ℝ => (b - a) * Real.exp (b * x) *
            (((Real.exp ((a - b) * y) - Real.exp ((a - b) * x)) / (a - b)) *
              (F y * Real.exp (-(a * y))))) =
          fun y : ℝ => Real.exp (a * x) * (F y * Real.exp (-(a * y))) -
            Real.exp (b * x) * (F y * Real.exp (-(b * y))) := by
        funext y
        have hba : (b - a) * ((Real.exp ((a - b) * y) - Real.exp ((a - b) * x)) / (a - b)) =
            Real.exp ((a - b) * x) - Real.exp ((a - b) * y) := by
          field_simp [hab']
          ring
        calc
          (b - a) * Real.exp (b * x) *
              (((Real.exp ((a - b) * y) - Real.exp ((a - b) * x)) / (a - b)) *
                (F y * Real.exp (-(a * y))))
            = Real.exp (b * x) * ((b - a) *
                ((Real.exp ((a - b) * y) - Real.exp ((a - b) * x)) / (a - b))) *
                (F y * Real.exp (-(a * y))) := by ring
          _ = Real.exp (b * x) * (Real.exp ((a - b) * x) - Real.exp ((a - b) * y)) *
                (F y * Real.exp (-(a * y))) := by rw [hba]
          _ = (Real.exp (b * x) * Real.exp ((a - b) * x)) * (F y * Real.exp (-(a * y))) -
                Real.exp (b * x) * (F y * (Real.exp ((a - b) * y) * Real.exp (-(a * y)))) := by ring
          _ = Real.exp (a * x) * (F y * Real.exp (-(a * y))) -
                Real.exp (b * x) * (F y * Real.exp (-(b * y))) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 3
              · ring
              · congr 2
                ring
      rw [hpoint]
      have hint_exp : ∀ c : ℝ, 0 < c →
          IntegrableOn (fun y => Real.exp (c * x) * (F y * Real.exp (-(c * y)))) (Ioc x 0) := by
        intro c hc0
        refine (Integrable.mono' (hF_Ioc.norm.const_mul (Real.exp (-(c * x))))
          ((hFm.mul (by fun_prop)).aestronglyMeasurable) ?_).const_mul (Real.exp (c * x))
        rw [ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun y hy => by
          dsimp only [Pi.mul_apply]
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (by nlinarith [hy.1, hc0])) (abs_nonneg _)
      rw [integral_sub (hint_exp a (by linarith)) (hint_exp b (by linarith)),
        integral_const_mul, integral_const_mul,
        ← halfLineResolvent_of_neg a F hx, ← halfLineResolvent_of_neg b F hx]
    rw [halfLineResolvent_of_neg b (halfLineResolvent a F) hx, hlhs, hswap, ← mul_assoc, hrhs]
  · rw [halfLineResolvent_eq_zero_of_nonneg _ _ (le_of_not_gt hx),
      halfLineResolvent_eq_zero_of_nonneg _ _ (le_of_not_gt hx),
      halfLineResolvent_eq_zero_of_nonneg _ _ (le_of_not_gt hx)]
    ring

private theorem integrable_mul_mul_exp_neg_eight {U V : ℝ → ℝ}
    (hUm : Measurable U) (hVm : Measurable V)
    (hU8 : Integrable (fun u => U u ^ 2 * Real.exp (-(8 * u))))
    (hV8 : Integrable (fun u => V u ^ 2 * Real.exp (-(8 * u)))) :
    Integrable (fun u => U u * V u * Real.exp (-(8 * u))) := by
  have h1m : Measurable (halfLineGauge U) :=
    hUm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  have h2m : Measurable (halfLineGauge V) :=
    hVm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  have h1i : Integrable (fun u => halfLineGauge U u ^ 2) := by
    simpa only [halfLineGauge_sq] using hU8
  have h2i : Integrable (fun u => halfLineGauge V u ^ 2) := by
    simpa only [halfLineGauge_sq] using hV8
  have hmul := HTGeometry.integrable_mul_of_sq_integrable
    h1m.aestronglyMeasurable h2m.aestronglyMeasurable h1i h2i
  refine hmul.congr (Eventually.of_forall fun u => ?_)
  dsimp only [halfLineGauge]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

/-- Iterated `(15/2, 8)` resolvent pairing on `M₈(-∞, 0)`: for `G = T_{15/2} F` and `H₈ = T₈ G`,
`⟨F, H₈⟩_{M₈} = -‖G‖_{M₈}² + 30 ‖H₈‖_{M₈}²`. -/
theorem integral_mul_iteratedResolvent_fifteen_halves_eight
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    let G := halfLineResolvent (15 / 2) F
    let H₈ := halfLineResolvent 8 G
    (∫ u in Iio 0, F u * H₈ u * Real.exp (-(8 * u))) =
      -(∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) +
        30 * (∫ u in Iio 0, H₈ u ^ 2 * Real.exp (-(8 * u))) := by
  intro G H₈
  have ha : (4 : ℝ) < 15 / 2 := by norm_num
  have hb : (4 : ℝ) < 8 := by norm_num
  have hGm : Measurable G := measurable_halfLineResolvent (15 / 2) hFm
  have hGsupp : ∀ u, 0 ≤ u → G u = 0 := fun _ hu => halfLineResolvent_eq_zero_of_nonneg _ _ hu
  have hG8 : Integrable (fun u => G u ^ 2 * Real.exp (-(8 * u))) :=
    integrable_halfLineResolvent_sq_mul_exp_neg_eight ha hFm hsupp hF8
  have hH8m : Measurable H₈ := measurable_halfLineResolvent 8 hGm
  have hH8_int : Integrable (fun u => H₈ u ^ 2 * Real.exp (-(8 * u))) :=
    integrable_halfLineResolvent_sq_mul_exp_neg_eight hb hGm hGsupp hG8
  have hT8_eq : ∀ u : ℝ, halfLineResolvent 8 F u = G u - (1 / 2) * H₈ u := fun u => by
    have hcomp := halfLineResolvent_comp_sub ha hb hFm hF8 u
    dsimp only [G, H₈] at hcomp ⊢
    linarith
  have hFG := integral_mul_halfLineResolvent_exp_neg_eight ha hFm hsupp hF8
  have hFT8 := integral_mul_halfLineResolvent_exp_neg_eight hb hFm hsupp hF8
  have hGH8 := integral_mul_halfLineResolvent_exp_neg_eight hb hGm hGsupp hG8
  have iFG : IntegrableOn (fun u => F u * G u * Real.exp (-(8 * u))) (Iio 0) :=
    (integrable_mul_mul_exp_neg_eight hFm hGm hF8 hG8).integrableOn
  have iFH8 : IntegrableOn (fun u => F u * H₈ u * Real.exp (-(8 * u))) (Iio 0) :=
    (integrable_mul_mul_exp_neg_eight hFm hH8m hF8 hH8_int).integrableOn
  have iGH8 : IntegrableOn (fun u => G u * H₈ u * Real.exp (-(8 * u))) (Iio 0) :=
    (integrable_mul_mul_exp_neg_eight hGm hH8m hG8 hH8_int).integrableOn
  have hFT8_split :
      (∫ u in Iio 0, F u * halfLineResolvent 8 F u * Real.exp (-(8 * u))) =
        (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) -
          (1 / 2) * (∫ u in Iio 0, F u * H₈ u * Real.exp (-(8 * u))) := by
    have hpt : (fun u : ℝ => F u * halfLineResolvent 8 F u * Real.exp (-(8 * u))) =
        fun u : ℝ => F u * G u * Real.exp (-(8 * u)) -
          (1 / 2) * (F u * H₈ u * Real.exp (-(8 * u))) := by
      funext u
      rw [hT8_eq u]
      ring
    rw [hpt, integral_sub iFG (iFH8.const_mul (1 / 2)), integral_const_mul]
  have hT8_sq :
      (∫ u in Iio 0, halfLineResolvent 8 F u ^ 2 * Real.exp (-(8 * u))) =
        (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) -
          (∫ u in Iio 0, G u * H₈ u * Real.exp (-(8 * u))) +
          (1 / 4) * (∫ u in Iio 0, H₈ u ^ 2 * Real.exp (-(8 * u))) := by
    have hpt : (fun u : ℝ => halfLineResolvent 8 F u ^ 2 * Real.exp (-(8 * u))) =
        fun u : ℝ => (G u ^ 2 * Real.exp (-(8 * u)) - G u * H₈ u * Real.exp (-(8 * u))) +
          (1 / 4) * (H₈ u ^ 2 * Real.exp (-(8 * u))) := by
      funext u
      rw [hT8_eq u]
      ring
    have iSub : IntegrableOn (fun u => G u ^ 2 * Real.exp (-(8 * u)) -
        G u * H₈ u * Real.exp (-(8 * u))) (Iio 0) := hG8.integrableOn.sub iGH8
    have iThird : IntegrableOn (fun u => (1 / 4) * (H₈ u ^ 2 * Real.exp (-(8 * u)))) (Iio 0) :=
      hH8_int.integrableOn.const_mul (1 / 4)
    rw [hpt, integral_add iSub iThird, integral_sub hG8.integrableOn iGH8, integral_const_mul]
  dsimp only [G, H₈] at hFG hGH8 hFT8_split hT8_sq ⊢
  linarith

/-- Exact `224 / 465` positive sum-of-squares depletion identity for the `(15/2, 8)` iterated
resolvent pair on `M₈(-∞, 0)`. -/
theorem iteratedResolvent_depletion_identity
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    let G := halfLineResolvent (15 / 2) F
    let H₈ := halfLineResolvent 8 G
    (8 / 15 : ℝ) * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) +
        (24 / 465 : ℝ) * (∫ u in Iio 0, F u * H₈ u * Real.exp (-(8 * u))) =
      (224 / 465 : ℝ) * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) +
        (48 / 31 : ℝ) * (∫ u in Iio 0, H₈ u ^ 2 * Real.exp (-(8 * u))) := by
  intro G H₈
  have h := integral_mul_iteratedResolvent_fifteen_halves_eight hFm hsupp hF8
  dsimp only [G, H₈] at h ⊢
  linarith

/-- Lower bound `(224 / 465) ‖G‖_{M₈}²` for the depleted `M₈` combination. -/
theorem iteratedResolvent_depletion_ge
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    let G := halfLineResolvent (15 / 2) F
    let H₈ := halfLineResolvent 8 G
    (224 / 465 : ℝ) * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) ≤
      (8 / 15 : ℝ) * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) +
        (24 / 465 : ℝ) * (∫ u in Iio 0, F u * H₈ u * Real.exp (-(8 * u))) := by
  intro G H₈
  have hid := iteratedResolvent_depletion_identity hFm hsupp hF8
  dsimp only [G, H₈] at hid ⊢
  have hnn : 0 ≤ ∫ u in Iio 0, H₈ u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => by positivity
  linarith

/-- Half-line Laplace identity for `T_b F` (`Re s < 4 < b`):
`∫_{x<0} (T_b F)(x) e^{-s x} dx = (b - s)⁻¹ ∫_{x<0} F(x) e^{-s x} dx`. -/
theorem laplace_halfLineResolvent {b : ℝ} (hb : 4 < b) {s : ℂ} (hs : s.re < 4)
    {F : ℝ → ℝ} (hFm : Measurable F) (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)))) :
    (∫ x in Iio 0, (halfLineResolvent b F x : ℂ) * Complex.exp (-s * (x : ℂ))) =
      ((b : ℂ) - s)⁻¹ * ∫ x in Iio 0, (F x : ℂ) * Complex.exp (-s * (x : ℂ)) := by
  have hwm : Measurable (halfLineGauge F) :=
    hFm.mul (Real.continuous_exp.measurable.comp (measurable_id.const_mul 4).neg)
  have hw2 : Integrable (fun y => halfLineGauge F y ^ 2) := by
    simpa only [halfLineGauge_sq] using hF8
  have hFs_norm_Iio : IntegrableOn (fun y : ℝ => |F y| * Real.exp (-s.re * y)) (Iio 0) := by
    have hg2 : IntegrableOn (fun y : ℝ => Real.exp ((4 - s.re) * y) ^ 2) (Iio 0) := by
      have heq : (fun y : ℝ => Real.exp ((4 - s.re) * y) ^ 2) =
          fun y : ℝ => Real.exp ((2 * (4 - s.re)) * y) := by
        funext y
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [heq]
      exact integrableOn_exp_mul_Iio (by linarith) 0
    have hw_abs2 : IntegrableOn (fun y : ℝ => |halfLineGauge F y| ^ 2) (Iio 0) := by
      simpa only [sq_abs] using hw2.integrableOn
    have hmul := HTGeometry.integrable_mul_of_sq_integrable (μ := volume.restrict (Iio 0))
      hwm.norm.aestronglyMeasurable (by fun_prop) hw_abs2 hg2
    refine hmul.congr (Eventually.of_forall fun y => ?_)
    dsimp only [halfLineGauge]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let M_s : ℝ → ℝ := (Iio 0).indicator fun y => |F y| * Real.exp (-s.re * y)
  have hMs_int : Integrable M_s := (integrable_indicator_iff measurableSet_Iio).mpr hFs_norm_Iio
  let L : ℝ × ℝ → ℂ := fun p =>
    if p.1 < p.2 ∧ p.2 ≤ 0 then
      ((F p.2 * Real.exp (-(b * p.2)) : ℝ) : ℂ) * Complex.exp (((b : ℂ) - s) * (p.1 : ℂ))
    else 0
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ 0} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  have hLm : Measurable L := by
    dsimp only [L]
    refine Measurable.ite hS ?_ measurable_const
    exact (Complex.continuous_ofReal.measurable.comp
      ((hFm.comp measurable_snd).mul
        (Real.continuous_exp.measurable.comp (measurable_snd.const_mul b).neg))).mul
      (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp measurable_fst).const_mul ((b : ℂ) - s)))
  have hbs_re : 0 < ((b : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hbs_ne : (b : ℂ) - s ≠ 0 := fun h0 => by
    rw [h0, Complex.zero_re] at hbs_re
    exact lt_irrefl 0 hbs_re
  have hLint : Integrable L (volume.prod volume) := by
    rw [integrable_prod_iff' hLm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · by_cases hy : y ≤ 0
      · have heq : (fun x : ℝ => L (x, y)) =
            (Iio y).indicator (fun x =>
              ((F y * Real.exp (-(b * y)) : ℝ) : ℂ) *
                Complex.exp (((b : ℂ) - s) * (x : ℂ))) := by
          funext x
          by_cases hx : x < y
          · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
            dsimp only [L]
            rw [if_pos ⟨hx, hy⟩]
          · rw [Set.indicator_of_notMem (show x ∉ Iio y from hx)]
            dsimp only [L]
            rw [if_neg (fun h => hx h.1)]
        rw [heq, integrable_indicator_iff measurableSet_Iio]
        exact (integrableOn_exp_mul_complex_Iio hbs_re y).const_mul _
      · have heq : (fun x : ℝ => L (x, y)) = fun _ => 0 := by
          funext x
          dsimp only [L]
          rw [if_neg (fun h => hy h.2)]
        rw [heq]
        exact integrable_zero _ _ _
    · have hval : (fun y : ℝ => ∫ x, ‖L (x, y)‖) =
          fun y : ℝ => (b - s.re)⁻¹ * M_s y := by
        funext y
        rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
        · have heq : (fun x : ℝ => ‖L (x, y)‖) =
              (Iio y).indicator (fun x =>
                (|F y| * Real.exp (-(b * y))) * Real.exp ((b - s.re) * x)) := by
            funext x
            by_cases hx : x < y
            · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
              dsimp only [L]
              rw [if_pos ⟨hx, hy_neg.le⟩, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_mul, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
              have hre : (((b : ℂ) - s) * (x : ℂ)).re = (b - s.re) * x := by
                simp [Complex.mul_re]
              rw [hre]
            · rw [Set.indicator_of_notMem (show x ∉ Iio y from hx)]
              dsimp only [L]
              rw [if_neg (fun h => hx h.1), norm_zero]
          rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
            integral_exp_mul_Iio (by linarith : 0 < b - s.re) y]
          dsimp only [M_s]
          rw [Set.indicator_of_mem (mem_Iio.mpr hy_neg)]
          have hexp : Real.exp (-(b * y)) * (Real.exp ((b - s.re) * y) / (b - s.re)) =
              (b - s.re)⁻¹ * Real.exp (-s.re * y) := by
            rw [mul_div_assoc', ← Real.exp_add, div_eq_inv_mul]
            congr 2
            ring
          simp only [mul_assoc]
          rw [hexp]
          ring
        · have heq : (fun x : ℝ => ‖L (x, 0)‖) = fun _ => 0 := by
            funext x
            dsimp only [L]
            split_ifs
            · simp [hsupp 0 le_rfl]
            · exact norm_zero
          rw [heq, integral_zero]
          dsimp only [M_s]
          simp
        · have heq : (fun x : ℝ => ‖L (x, y)‖) = fun _ => 0 := by
            funext x
            dsimp only [L]
            rw [if_neg (fun h => not_le_of_gt hy_pos h.2), norm_zero]
          rw [heq, integral_zero]
          dsimp only [M_s]
          rw [Set.indicator_of_notMem (show y ∉ Iio 0 from not_lt_of_gt hy_pos), mul_zero]
      rw [hval]
      exact hMs_int.const_mul _
  have hswap := integral_integral_swap (f := fun x y => L (x, y)) hLint
  have hlhs : (∫ x, ∫ y, L (x, y)) =
      ∫ x in Iio 0, (halfLineResolvent b F x : ℂ) * Complex.exp (-s * (x : ℂ)) := by
    rw [← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hx : x < 0
    · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
      have heq : (fun y : ℝ => L (x, y)) =
          (Ioc x 0).indicator (fun y =>
            ((F y * Real.exp (-(b * y)) : ℝ) : ℂ) *
              Complex.exp (((b : ℂ) - s) * (x : ℂ))) := by
        funext y
        by_cases hy : y ∈ Ioc x 0
        · rw [Set.indicator_of_mem hy]
          dsimp only [L]
          rw [if_pos ⟨hy.1, hy.2⟩]
        · rw [Set.indicator_of_notMem hy]
          dsimp only [L]
          rw [if_neg (fun h => hy ⟨h.1, h.2⟩)]
      have hofReal : (∫ y in Ioc x 0, ((F y * Real.exp (-(b * y)) : ℝ) : ℂ)) =
          ((∫ y in Ioc x 0, F y * Real.exp (-(b * y)) : ℝ) : ℂ) := by
        simp_rw [← Complex.coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal]
      have hexp : (b : ℂ) * (x : ℂ) + -s * (x : ℂ) = ((b : ℂ) - s) * (x : ℂ) := by ring
      rw [heq, integral_indicator measurableSet_Ioc, integral_mul_const, hofReal,
        halfLineResolvent_of_neg b F hx, Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.ofReal_mul, mul_right_comm, ← Complex.exp_add, hexp, mul_comm]
    · rw [Set.indicator_of_notMem (show x ∉ Iio 0 from hx)]
      have heq : (fun y : ℝ => L (x, y)) = fun _ => 0 := by
        funext y
        dsimp only [L]
        rw [if_neg (fun h => hx (h.1.trans_le h.2))]
      rw [heq, integral_zero]
  have hrhs : (∫ y, ∫ x, L (x, y)) =
      ((b : ℂ) - s)⁻¹ * ∫ y in Iio 0, (F y : ℂ) * Complex.exp (-s * (y : ℂ)) := by
    rw [← integral_const_mul, ← integral_indicator measurableSet_Iio]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
    · rw [Set.indicator_of_mem (mem_Iio.mpr hy_neg)]
      have heq : (fun x : ℝ => L (x, y)) =
          (Iio y).indicator (fun x =>
            ((F y * Real.exp (-(b * y)) : ℝ) : ℂ) *
              Complex.exp (((b : ℂ) - s) * (x : ℂ))) := by
        funext x
        by_cases hx : x < y
        · rw [Set.indicator_of_mem (mem_Iio.mpr hx)]
          dsimp only [L]
          rw [if_pos ⟨hx, hy_neg.le⟩]
        · rw [Set.indicator_of_notMem (show x ∉ Iio y from hx)]
          dsimp only [L]
          rw [if_neg (fun h => hx h.1)]
      rw [heq, integral_indicator measurableSet_Iio, integral_const_mul,
        integral_exp_mul_complex_Iio hbs_re y, Complex.ofReal_mul, Complex.ofReal_exp]
      have hexp : Complex.exp ((-(b * y) : ℝ) : ℂ) *
          (Complex.exp (((b : ℂ) - s) * (y : ℂ)) / ((b : ℂ) - s)) =
          ((b : ℂ) - s)⁻¹ * Complex.exp (-s * (y : ℂ)) := by
        rw [mul_div_assoc', ← Complex.exp_add, div_eq_inv_mul]
        congr 2
        push_cast
        ring
      simp only [mul_assoc]
      rw [hexp]
      ring
    · rw [Set.indicator_of_notMem (fun h : (0 : ℝ) ∈ Iio 0 => lt_irrefl (0 : ℝ) h)]
      have heq : (fun x : ℝ => L (x, 0)) = fun _ => 0 := by
        funext x
        dsimp only [L]
        split_ifs
        · simp [hsupp 0 le_rfl]
        · rfl
      rw [heq, integral_zero]
    · rw [Set.indicator_of_notMem (fun h : y ∈ Iio 0 => not_lt_of_gt hy_pos h)]
      have heq : (fun x : ℝ => L (x, y)) = fun _ => 0 := by
        funext x
        dsimp only [L]
        rw [if_neg (fun h => not_le_of_gt hy_pos h.2)]
      rw [heq, integral_zero]
  rw [← hlhs, hswap, hrhs]

/-! ## 2. Depleted resolvent kernel bounds and piecewise holomorphic square root -/

/-- The depleted spectral resolvent kernel `m(z) = 4 / (1/4 - z²) - 12 / (64 - z²)`. -/
def depletedResolventKernel (z : ℂ) : ℂ :=
  4 / (1 / 4 - z ^ 2) - 12 / (64 - z ^ 2)

@[simp]
theorem depletedResolventKernel_neg (z : ℂ) :
    depletedResolventKernel (-z) = depletedResolventKernel z := by
  simp [depletedResolventKernel]

theorem depletedResolventKernel_conj (z : ℂ) :
    depletedResolventKernel (starRingEnd ℂ z) = starRingEnd ℂ (depletedResolventKernel z) := by
  simp [depletedResolventKernel, map_ofNat]

private theorem sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero {c : ℝ} {z : ℂ}
    (hc : 0 ≤ c) (h : z.re ^ 2 < c ∨ z.im ≠ 0) : (c : ℂ) - z ^ 2 ≠ 0 := by
  intro h0
  have hsq : z ^ 2 = (c : ℂ) := (sub_eq_zero.mp h0).symm
  have him : 2 * z.re * z.im = 0 := by
    have := congrArg Complex.im hsq
    simp only [sq, Complex.mul_im, Complex.ofReal_im] at this
    linarith
  have hre : z.re ^ 2 - z.im ^ 2 = c := by
    have := congrArg Complex.re hsq
    simp only [sq, Complex.mul_re, Complex.ofReal_re] at this
    linarith
  rcases h with hlt | hne
  · nlinarith [sq_nonneg z.im]
  · have hre0 : z.re = 0 := by
      rcases mul_eq_zero.mp him with h2 | hne'
      · linarith
      · exact absurd hne' hne
    rw [hre0] at hre
    have him2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hne
    linarith

/-- Single rational fraction form of `depletedResolventKernel`. -/
theorem depletedResolventKernel_eq_div {z : ℂ}
    (h1 : (1 / 4 : ℂ) - z ^ 2 ≠ 0) (h2 : (64 : ℂ) - z ^ 2 ≠ 0) :
    depletedResolventKernel z = (253 + 8 * z ^ 2) / ((1 / 4 - z ^ 2) * (64 - z ^ 2)) := by
  unfold depletedResolventKernel
  rw [div_sub_div _ _ h1 h2]
  congr 1
  ring

private theorem re_ofReal_div_sub_sq (a c : ℝ) (z : ℂ) :
    ((a : ℂ) / ((c : ℂ) - z ^ 2)).re =
      a * (c - z.re ^ 2 + z.im ^ 2) / Complex.normSq ((c : ℂ) - z ^ 2) := by
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  congr 2
  simp only [sq, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]
  ring

private theorem normSq_sub_sq_eq (c : ℝ) (z : ℂ) :
    Complex.normSq ((c : ℂ) - z ^ 2) =
      (c - z.re ^ 2) ^ 2 + 2 * (c + z.re ^ 2) * z.im ^ 2 + (z.im ^ 2) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [sq, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im]
  ring

private theorem depletedResolventKernel_neg_re_lower_bound {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    (8 * (z.im ^ 2) ^ 3 + 248 * (z.im ^ 2) ^ 2 - 16513 * z.im ^ 2 - 4096) /
        ((z.im ^ 2) ^ 2 * ((z.im ^ 2) ^ 2 + 129 * z.im ^ 2 + 4096)) <
      -(depletedResolventKernel z).re := by
  set u : ℝ := z.re ^ 2
  set v : ℝ := z.im ^ 2
  have hu0 : 0 ≤ u := sq_nonneg z.re
  have hu : u < 1 / 4 := by
    have habs := abs_lt.mp hre
    dsimp only [u]
    nlinarith
  have hv_pos : 0 < v := by linarith
  set D₁ : ℝ := Complex.normSq ((1 / 4 : ℂ) - z ^ 2)
  set D₂ : ℝ := Complex.normSq ((64 : ℂ) - z ^ 2)
  have hD₁_eq : D₁ = (1 / 4 - u) ^ 2 + 2 * (1 / 4 + u) * v + v ^ 2 := by
    simpa [D₁, u, v] using normSq_sub_sq_eq (1 / 4) z
  have hD₂_eq : D₂ = (64 - u) ^ 2 + 2 * (64 + u) * v + v ^ 2 := by
    simpa [D₂, u, v] using normSq_sub_sq_eq 64 z
  have hD₁_gt : v ^ 2 < D₁ := by
    rw [hD₁_eq]
    have h1 : 0 ≤ (1 / 4 - u) ^ 2 := sq_nonneg _
    have h2 : 0 < 2 * (1 / 4 + u) * v := by positivity
    linarith
  have hD₂_pos : 0 < D₂ := by
    rw [hD₂_eq]
    positivity
  have hD₂_lt : D₂ < v ^ 2 + 129 * v + 4096 := by
    rw [hD₂_eq]
    have h1 : (64 - u) ^ 2 ≤ 4096 := by nlinarith
    have h2 : 2 * (64 + u) * v < 129 * v :=
      mul_lt_mul_of_pos_right (by linarith) hv_pos
    linarith
  have hterm1 : ((4 : ℂ) / ((1 / 4 : ℂ) - z ^ 2)).re ≤ 4 * (v + 1 / 4) / v ^ 2 := by
    have hre1 : ((4 : ℂ) / ((1 / 4 : ℂ) - z ^ 2)).re = 4 * (1 / 4 - u + v) / D₁ := by
      simpa [D₁, u, v] using re_ofReal_div_sub_sq 4 (1 / 4) z
    rw [hre1]
    have hnum : 4 * (1 / 4 - u + v) ≤ 4 * (v + 1 / 4) := by linarith
    have hden_pos : 0 < v ^ 2 := by positivity
    exact (div_le_div_of_nonneg_left (by positivity) hden_pos hD₁_gt.le).trans
      (div_le_div_of_nonneg_right hnum hden_pos.le)
  have hterm2 : 12 * (v + 255 / 4) / (v ^ 2 + 129 * v + 4096) <
      ((12 : ℂ) / ((64 : ℂ) - z ^ 2)).re := by
    have hre2 : ((12 : ℂ) / ((64 : ℂ) - z ^ 2)).re = 12 * (64 - u + v) / D₂ := by
      simpa [D₂, u, v] using re_ofReal_div_sub_sq 12 64 z
    rw [hre2]
    have hnum : 12 * (v + 255 / 4) < 12 * (64 - u + v) := by linarith
    have hden_ub_pos : 0 < v ^ 2 + 129 * v + 4096 := by positivity
    exact (div_lt_div_of_pos_left (by positivity) hD₂_pos hD₂_lt).trans
      (div_lt_div_of_pos_right hnum hD₂_pos)
  have hdiff_eq : 12 * (v + 255 / 4) / (v ^ 2 + 129 * v + 4096) - 4 * (v + 1 / 4) / v ^ 2 =
      (8 * v ^ 3 + 248 * v ^ 2 - 16513 * v - 4096) /
        (v ^ 2 * (v ^ 2 + 129 * v + 4096)) := by
    have hv2_ne : v ^ 2 ≠ 0 := by positivity
    have hden_ne : v ^ 2 + 129 * v + 4096 ≠ 0 := by positivity
    rw [div_sub_div _ _ hden_ne hv2_ne]
    field_simp [hv2_ne, hden_ne]
    ring
  have hker_re : -(depletedResolventKernel z).re =
      ((12 : ℂ) / ((64 : ℂ) - z ^ 2)).re - ((4 : ℂ) / ((1 / 4 : ℂ) - z ^ 2)).re := by
    unfold depletedResolventKernel
    rw [Complex.sub_re]
    ring
  dsimp only [v] at hdiff_eq hterm1 hterm2 ⊢
  linarith

/-- Strict negativity `Re m(z) < 0` on the centered strip `{|Re z| < 1/2, 331/4 < (Im z)²}`. -/
theorem re_depletedResolventKernel_neg_of_strip {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    (depletedResolventKernel z).re < 0 := by
  have hlb := depletedResolventKernel_neg_re_lower_bound hre him
  set t : ℝ := z.im ^ 2 - 331 / 4
  have ht : 0 < t := sub_pos.mpr him
  have hv_eq : z.im ^ 2 = 331 / 4 + t := by dsimp only [t]; ring
  have hnum_pos : 0 < 8 * (z.im ^ 2) ^ 3 + 248 * (z.im ^ 2) ^ 2 - 16513 * z.im ^ 2 - 4096 := by
    rw [hv_eq]
    have hpoly : 8 * (331 / 4 + t) ^ 3 + 248 * (331 / 4 + t) ^ 2 -
        16513 * (331 / 4 + t) - 4096 =
        8 * t ^ 3 + 2234 * t ^ 2 + (377745 / 2) * t + 38885881 / 8 := by ring
    rw [hpoly]
    positivity
  have hv_pos : 0 < z.im ^ 2 := by linarith
  have hdiv_pos : 0 < (8 * (z.im ^ 2) ^ 3 + 248 * (z.im ^ 2) ^ 2 - 16513 * z.im ^ 2 - 4096) /
      ((z.im ^ 2) ^ 2 * ((z.im ^ 2) ^ 2 + 129 * z.im ^ 2 + 4096)) :=
    div_pos hnum_pos (by positivity)
  linarith

/-- Single-orbit norm-to-real-part bound `25 ‖m(z)‖² < -Re m(z)` (hence
`‖m(z)‖² / (-Re m(z)) < 1 / 25 < 224 / 465`) throughout `{|Re z| < 1/2, 331/4 < (Im z)²}`. -/
theorem twenty_five_mul_norm_sq_depletedResolventKernel_lt_neg_re {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    25 * ‖depletedResolventKernel z‖ ^ 2 < -(depletedResolventKernel z).re := by
  have hu : z.re ^ 2 < 1 / 4 := by
    have habs := abs_lt.mp hre
    nlinarith
  have h1 : (1 / 4 : ℂ) - z ^ 2 ≠ 0 := by
    simpa using sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero (c := 1 / 4) (by norm_num) (Or.inl hu)
  have h2 : (64 : ℂ) - z ^ 2 ≠ 0 := by
    simpa using sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero (c := 64) (by norm_num)
      (Or.inl (by linarith))
  have hlb := depletedResolventKernel_neg_re_lower_bound hre him
  set u : ℝ := z.re ^ 2
  set v : ℝ := z.im ^ 2
  have hu0 : 0 ≤ u := sq_nonneg z.re
  have hv_pos : 0 < v := by dsimp only [v]; linarith
  have hnum_lt : Complex.normSq (253 + 8 * z ^ 2) < 64 * v ^ 2 - 4016 * v + 65025 := by
    have hexp : Complex.normSq (253 + 8 * z ^ 2) = (253 + 8 * u - 8 * v) ^ 2 + 256 * u * v := by
      rw [Complex.normSq_apply]
      simp only [sq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        u, v]
      norm_num
      ring
    rw [hexp]
    have hdiff : (64 * v ^ 2 - 4016 * v + 65025) - ((253 + 8 * u - 8 * v) ^ 2 + 256 * u * v) =
        8 * (1 - 4 * u) * (2 * u + 4 * v + 127) := by ring
    have h14 : 0 < 1 - 4 * u := by dsimp only [u]; linarith
    have hpos : 0 < 8 * (1 - 4 * u) * (2 * u + 4 * v + 127) := by positivity
    linarith
  have hD₁_gt : v ^ 2 < Complex.normSq ((1 / 4 : ℂ) - z ^ 2) := by
    have h1eq : Complex.normSq ((1 / 4 : ℂ) - z ^ 2) =
        (1 / 4 - u) ^ 2 + 2 * (1 / 4 + u) * v + v ^ 2 := by
      simpa [u, v] using normSq_sub_sq_eq (1 / 4) z
    rw [h1eq]
    have hsq1 : 0 ≤ (1 / 4 - u) ^ 2 := sq_nonneg _
    have hpos1 : 0 < 2 * (1 / 4 + u) * v := by positivity
    linarith
  have hD₂_gt : (v + 255 / 4) ^ 2 < Complex.normSq ((64 : ℂ) - z ^ 2) := by
    have h2eq : Complex.normSq ((64 : ℂ) - z ^ 2) =
        (64 - u) ^ 2 + 2 * (64 + u) * v + v ^ 2 := by
      simpa [u, v] using normSq_sub_sq_eq 64 z
    rw [h2eq]
    have hdiff : ((64 - u) ^ 2 + 2 * (64 + u) * v + v ^ 2) - (v + 255 / 4) ^ 2 =
        4 * u * v + (64 - u + v) ^ 2 - (v + 255 / 4) ^ 2 := by ring
    have hbase : v + 255 / 4 < 64 - u + v := by dsimp only [u]; linarith
    have hsq_lt : (v + 255 / 4) ^ 2 < (64 - u + v) ^ 2 := by nlinarith
    have huv : 0 ≤ 4 * u * v := by positivity
    linarith
  have hden_gt : v ^ 2 * (v + 255 / 4) ^ 2 <
      Complex.normSq (((1 / 4 : ℂ) - z ^ 2) * ((64 : ℂ) - z ^ 2)) := by
    rw [map_mul]
    exact mul_lt_mul'' hD₁_gt hD₂_gt (by positivity) (by positivity)
  have hnorm_lt : ‖depletedResolventKernel z‖ ^ 2 <
      (64 * v ^ 2 - 4016 * v + 65025) / (v ^ 2 * (v + 255 / 4) ^ 2) := by
    rw [Complex.sq_norm, depletedResolventKernel_eq_div h1 h2, map_div₀]
    have hden_pos : 0 < v ^ 2 * (v + 255 / 4) ^ 2 := by positivity
    have hden_c_pos : 0 < Complex.normSq (((1 / 4 : ℂ) - z ^ 2) * ((64 : ℂ) - z ^ 2)) :=
      hden_pos.trans hden_gt
    exact (div_lt_div_of_pos_right hnum_lt hden_c_pos).trans
      (div_lt_div_of_pos_left (by linarith [Complex.normSq_nonneg (253 + 8 * z ^ 2)])
        hden_pos hden_gt)
  set t : ℝ := v - 331 / 4
  have ht : 0 < t := sub_pos.mpr him
  have hv_eq : v = 331 / 4 + t := by dsimp only [t]; ring
  have hrat_lt : 25 * ((64 * v ^ 2 - 4016 * v + 65025) / (v ^ 2 * (v + 255 / 4) ^ 2)) <
      (8 * v ^ 3 + 248 * v ^ 2 - 16513 * v - 4096) /
        (v ^ 2 * (v ^ 2 + 129 * v + 4096)) := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    have hpoly : v ^ 2 * ((8 * v ^ 3 + 248 * v ^ 2 - 16513 * v - 4096) * (v + 255 / 4) ^ 2 -
        25 * (64 * v ^ 2 - 4016 * v + 65025) * (v ^ 2 + 129 * v + 4096)) =
        v ^ 2 * (8 * t ^ 5 + 2978 * t ^ 4 + (759065 / 2) * t ^ 3 +
          (166946553 / 8) * t ^ 2 + (2660764269 / 4) * t + 381880053719 / 32) := by
      rw [hv_eq]
      ring
    have hpos : 0 < v ^ 2 * (8 * t ^ 5 + 2978 * t ^ 4 + (759065 / 2) * t ^ 3 +
        (166946553 / 8) * t ^ 2 + (2660764269 / 4) * t + 381880053719 / 32) := by
      positivity
    linarith
  dsimp only [v] at hnorm_lt hrat_lt
  linarith

private theorem xiZeroCopy_centered_mem_strip (q : RHTower.XiZeroCopy) :
    |((q.1 : ℂ) - 1 / 2).re| < 1 / 2 ∧ 331 / 4 < ((q.1 : ℂ) - 1 / 2).im ^ 2 := by
  constructor
  · have hsq : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 :=
      RHTower.xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hre : ((q.1 : ℂ) - 1 / 2).re = (q.1 : ℂ).re - 1 / 2 := by
      simp [Complex.sub_re]
    rw [hre, abs_lt]
    constructor <;> nlinarith
  · have hfl := RHTower.xiSpectralPoint_re_sq_gt_floor q
    rw [RHTower.xiSpectralPoint_re_eq] at hfl
    have him : ((q.1 : ℂ) - 1 / 2).im = (q.1 : ℂ).im := by simp [Complex.sub_im]
    rwa [him]

/-- Unconditional strict negativity of `depletedResolventKernel` at every centered `ξ`-zero copy
`z_q = ρ_q - 1/2`. -/
theorem re_depletedResolventKernel_xiZeroCopy_neg (q : RHTower.XiZeroCopy) :
    (depletedResolventKernel ((q.1 : ℂ) - 1 / 2)).re < 0 := by
  obtain ⟨hre, him⟩ := xiZeroCopy_centered_mem_strip q
  exact re_depletedResolventKernel_neg_of_strip hre him

/-- Unconditional `1 / 25` norm-to-real-part bound at every centered `ξ`-zero copy
`z_q = ρ_q - 1/2` (strictly below the `224 / 465` single-resolvent depletion fraction). -/
theorem twenty_five_mul_norm_sq_depletedResolventKernel_xiZeroCopy_lt (q : RHTower.XiZeroCopy) :
    25 * ‖depletedResolventKernel ((q.1 : ℂ) - 1 / 2)‖ ^ 2 <
      -(depletedResolventKernel ((q.1 : ℂ) - 1 / 2)).re := by
  obtain ⟨hre, him⟩ := xiZeroCopy_centered_mem_strip q
  exact twenty_five_mul_norm_sq_depletedResolventKernel_lt_neg_re hre him

/-- Piecewise holomorphic square root `Φ̃(z) = ±i exp(log(-m(z)) / 2)` of `-m(z)`. -/
def depletedSquareRootFactor (z : ℂ) : ℂ :=
  (if 0 ≤ z.im then Complex.I else -Complex.I) *
    Complex.exp (Complex.log (-depletedResolventKernel z) / 2)

private theorem neg_depletedResolventKernel_mem_slitPlane {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    -depletedResolventKernel z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by
    rw [Complex.neg_re]
    exact neg_pos.mpr (re_depletedResolventKernel_neg_of_strip hre him)))

private theorem analyticAt_neg_depletedResolventKernel {z : ℂ} (hre : |z.re| < 1 / 2) :
    AnalyticAt ℂ (fun w => -depletedResolventKernel w) z := by
  have hu : z.re ^ 2 < 1 / 4 := by
    have habs := abs_lt.mp hre
    nlinarith
  have h1 : (1 / 4 : ℂ) - z ^ 2 ≠ 0 := by
    simpa using sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero (c := 1 / 4) (by norm_num) (Or.inl hu)
  have h2 : (64 : ℂ) - z ^ 2 ≠ 0 := by
    simpa using sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero (c := 64) (by norm_num)
      (Or.inl (by linarith))
  have ha1 : AnalyticAt ℂ (fun w : ℂ => (4 : ℂ) / ((1 / 4 : ℂ) - w ^ 2)) z :=
    analyticAt_const.div (analyticAt_const.sub (analyticAt_id.pow 2)) h1
  have ha2 : AnalyticAt ℂ (fun w : ℂ => (12 : ℂ) / ((64 : ℂ) - w ^ 2)) z :=
    analyticAt_const.div (analyticAt_const.sub (analyticAt_id.pow 2)) h2
  exact (ha1.sub ha2).neg

/-- `depletedSquareRootFactor` is complex-analytic on the upper open strip
`{z : ℂ | |z.re| < 1/2 ∧ √(331/4) < z.im}`. -/
theorem analyticOnNhd_depletedSquareRootFactor_upper :
    AnalyticOnNhd ℂ depletedSquareRootFactor
      {z : ℂ | |z.re| < 1 / 2 ∧ Real.sqrt (331 / 4) < z.im} := by
  have hopen : IsOpen {z : ℂ | |z.re| < 1 / 2 ∧ Real.sqrt (331 / 4) < z.im} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  intro z hz
  have him_pos : 0 < z.im := (Real.sqrt_pos.mpr (by norm_num)).trans hz.2
  have him_sq : 331 / 4 < z.im ^ 2 := by
    have hsq := pow_lt_pow_left₀ hz.2 (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (by norm_num)] at hsq
  have hslit := neg_depletedResolventKernel_mem_slitPlane hz.1 him_sq
  have hlog2 : AnalyticAt ℂ (fun w => Complex.log (-depletedResolventKernel w) / 2) z := by
    simpa only [div_eq_mul_inv] using
      ((analyticAt_neg_depletedResolventKernel hz.1).clog hslit).fun_mul
        (analyticAt_const : AnalyticAt ℂ (fun _ => (2⁻¹ : ℂ)) z)
  have hbase : AnalyticAt ℂ
      (fun w => Complex.I * Complex.exp (Complex.log (-depletedResolventKernel w) / 2)) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ => Complex.I) z).fun_mul hlog2.cexp
  refine hbase.congr ?_
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw_nn : 0 ≤ w.im := (Real.sqrt_nonneg _).trans hw.2.le
  simp [depletedSquareRootFactor, hw_nn]

/-- `depletedSquareRootFactor` is complex-analytic on the lower open strip
`{z : ℂ | |z.re| < 1/2 ∧ z.im < -√(331/4)}`. -/
theorem analyticOnNhd_depletedSquareRootFactor_lower :
    AnalyticOnNhd ℂ depletedSquareRootFactor
      {z : ℂ | |z.re| < 1 / 2 ∧ z.im < -Real.sqrt (331 / 4)} := by
  have hopen : IsOpen {z : ℂ | |z.re| < 1 / 2 ∧ z.im < -Real.sqrt (331 / 4)} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  intro z hz
  have him_sq : 331 / 4 < z.im ^ 2 := by
    have hlt : Real.sqrt (331 / 4) < -z.im := by linarith [hz.2]
    have hsq := pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (by norm_num), neg_sq] at hsq
  have hslit := neg_depletedResolventKernel_mem_slitPlane hz.1 him_sq
  have hlog2 : AnalyticAt ℂ (fun w => Complex.log (-depletedResolventKernel w) / 2) z := by
    simpa only [div_eq_mul_inv] using
      ((analyticAt_neg_depletedResolventKernel hz.1).clog hslit).fun_mul
        (analyticAt_const : AnalyticAt ℂ (fun _ => (2⁻¹ : ℂ)) z)
  have hbase : AnalyticAt ℂ
      (fun w => (-Complex.I) * Complex.exp (Complex.log (-depletedResolventKernel w) / 2)) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ => -Complex.I) z).fun_mul hlog2.cexp
  refine hbase.congr ?_
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw_neg : ¬ 0 ≤ w.im := not_le_of_gt (hw.2.trans_le (neg_nonpos.mpr (Real.sqrt_nonneg _)))
  simp [depletedSquareRootFactor, hw_neg]

/-- Schwarz reflection symmetry `Φ̃(z̄) = conj(Φ̃(z))` on `{|Re z| < 1/2, 331/4 < (Im z)²}`. -/
theorem depletedSquareRootFactor_conj {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    depletedSquareRootFactor (starRingEnd ℂ z) =
      starRingEnd ℂ (depletedSquareRootFactor z) := by
  have him_ne : z.im ≠ 0 := by
    intro h0
    rw [h0] at him
    norm_num at him
  have hslit := neg_depletedResolventKernel_mem_slitPlane hre him
  have harg : (-depletedResolventKernel z).arg ≠ Real.pi :=
    Complex.slitPlane_arg_ne_pi hslit
  have hlog : Complex.log (-depletedResolventKernel (starRingEnd ℂ z)) =
      starRingEnd ℂ (Complex.log (-depletedResolventKernel z)) := by
    rw [depletedResolventKernel_conj, ← map_neg, Complex.log_conj _ harg]
  unfold depletedSquareRootFactor
  rw [hlog, map_mul, ← Complex.exp_conj]
  have hdiv : starRingEnd ℂ (Complex.log (-depletedResolventKernel z)) / 2 =
      starRingEnd ℂ (Complex.log (-depletedResolventKernel z) / 2) := by
    simp [map_ofNat]
  rw [hdiv]
  congr 1
  rcases lt_or_gt_of_ne him_ne with hneg | hpos
  · rw [if_neg (not_le_of_gt hneg), if_pos (by simp [hneg.le] : 0 ≤ (starRingEnd ℂ z).im)]
    simp
  · rw [if_pos hpos.le, if_neg (by simp [hpos] : ¬ 0 ≤ (starRingEnd ℂ z).im)]
    simp

/-- Exact piecewise holomorphic factorization `Φ̃(z) Φ̃(-z) = -m(z)` throughout
`{|Re z| < 1/2, 331/4 < (Im z)²}`. -/
theorem depletedSquareRootFactor_mul_neg {z : ℂ}
    (hre : |z.re| < 1 / 2) (him : 331 / 4 < z.im ^ 2) :
    depletedSquareRootFactor z * depletedSquareRootFactor (-z) =
      -depletedResolventKernel z := by
  have him_ne : z.im ≠ 0 := by
    intro h0
    rw [h0] at him
    norm_num at him
  have hne : -depletedResolventKernel z ≠ 0 :=
    Complex.slitPlane_ne_zero (neg_depletedResolventKernel_mem_slitPlane hre him)
  unfold depletedSquareRootFactor
  rw [depletedResolventKernel_neg, mul_mul_mul_comm, ← Complex.exp_add, add_halves,
    Complex.exp_log hne]
  have hsign : (if 0 ≤ z.im then Complex.I else -Complex.I) *
      (if 0 ≤ (-z).im then Complex.I else -Complex.I) = 1 := by
    rcases lt_or_gt_of_ne him_ne with hneg | hpos
    · rw [if_neg (not_le_of_gt hneg), if_pos (by simp [hneg.le] : 0 ≤ (-z).im)]
      simp
    · rw [if_pos hpos.le, if_neg (by simp [hpos] : ¬ 0 ≤ (-z).im)]
      simp
  rw [hsign, one_mul]

/-- Unconditional specialization of `Φ̃(z_q) Φ̃(-z_q) = -m(z_q)` at every `q : RHTower.XiZeroCopy`. -/
theorem depletedSquareRootFactor_mul_neg_xiZeroCopy (q : RHTower.XiZeroCopy) :
    depletedSquareRootFactor ((q.1 : ℂ) - 1 / 2) *
        depletedSquareRootFactor (-((q.1 : ℂ) - 1 / 2)) =
      -depletedResolventKernel ((q.1 : ℂ) - 1 / 2) := by
  obtain ⟨hre, him⟩ := xiZeroCopy_centered_mem_strip q
  exact depletedSquareRootFactor_mul_neg hre him

/-! ## 3. Universal holomorphic multiplier domination no-go -/

/-- Every off-line `ξ`-zero copy lies in the verified off-line strip
`{z : ℂ | 0 < |z.re| ∧ |z.re| < 1/2 ∧ 431/2 ≤ z.im²}`. -/
theorem xiZeroCopy_centered_mem_verified_offLine_strip
    (q : RHTower.XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < |((q.1 : ℂ) - 1 / 2).re| ∧
      |((q.1 : ℂ) - 1 / 2).re| < 1 / 2 ∧
      431 / 2 ≤ ((q.1 : ℂ) - 1 / 2).im ^ 2 := by
  obtain ⟨hre_lt, _⟩ := xiZeroCopy_centered_mem_strip q
  refine ⟨?_, hre_lt, ?_⟩
  · rw [Complex.sub_re]
    have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [h12]
    exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  · have h431 := RHTower.fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hoff
    have him : ((q.1 : ℂ) - 1 / 2).im = (q.1 : ℂ).im := by simp [Complex.sub_im]
    rwa [him]

private theorem not_analyticOnNhd_domination_of_depletedResolventKernel
    {Ψ : ℂ → ℂ} (hΨ : AnalyticOnNhd ℂ Ψ {z : ℂ | |z.re| < 1})
    (hdom : ∀ z : ℂ, 0 < |z.re| → |z.re| < 1 / 2 → 431 / 2 ≤ z.im ^ 2 →
      ∀ u v : ℂ, ((depletedResolventKernel z + Ψ z) * u * v).re ≤ 0) :
    False := by
  let U : Set ℂ := {z : ℂ | |z.re| < 1 / 2}
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    simp only [U, mem_setOf_eq, abs_lt] at hx hy ⊢
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases ha.eq_or_lt with rfl | ha_pos
    · simp only [zero_add] at hab
      subst hab
      simp only [zero_mul, one_mul, zero_add]
      exact hy
    · have hsum_neg : a * (-(1 / 2)) + b * (-(1 / 2)) = -(1 / 2) := by
        linear_combination -(1 / 2) * hab
      have hsum_pos : a * (1 / 2) + b * (1 / 2) = 1 / 2 := by
        linear_combination (1 / 2) * hab
      exact ⟨by linarith [mul_lt_mul_of_pos_left hx.1 ha_pos,
          mul_le_mul_of_nonneg_left hy.1.le hb, hsum_neg],
        by linarith [mul_lt_mul_of_pos_left hx.2 ha_pos,
          mul_le_mul_of_nonneg_left hy.2.le hb, hsum_pos]⟩
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  let r : ℂ → ℂ := fun z => depletedResolventKernel z + Ψ z
  have hr_ana : AnalyticOnNhd ℂ r U := by
    intro z hz
    have hz' : |z.re| < 1 / 2 := hz
    have hm_ana : AnalyticAt ℂ depletedResolventKernel z := by
      have hneg := analyticAt_neg_depletedResolventKernel hz'
      simpa only [neg_neg] using hneg.fun_neg
    have hz1 : z ∈ {w : ℂ | |w.re| < 1} := lt_trans hz' (by norm_num)
    exact hm_ana.fun_add (hΨ z hz1)
  let z₀ : ℂ := (1 / 4 : ℂ) + 15 * Complex.I
  have hz₀_U : z₀ ∈ U := by
    simp only [U, z₀, mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
  let W : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1 / 2 ∧ (147 / 10 : ℝ) < z.im}
  have hW_open : IsOpen W :=
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (0 : ℝ)) Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re
          (continuous_const : Continuous fun _ : ℂ => (1 / 2 : ℝ))).inter
        (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (147 / 10 : ℝ))
          Complex.continuous_im))
  have hz₀_W : z₀ ∈ W := by
    simp only [W, z₀, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    norm_num
  have hr_ev0 : r =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hW_open.mem_nhds hz₀_W] with z hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have habs_pos : 0 < |z.re| := abs_pos.mpr (ne_of_gt hz1)
    have habs_lt : |z.re| < 1 / 2 := abs_lt.mpr ⟨by linarith, hz2⟩
    have him_ge : (431 / 2 : ℝ) ≤ z.im ^ 2 := by nlinarith
    have hle := hdom z habs_pos habs_lt him_ge (starRingEnd ℂ (r z)) 1
    have hprod : (r z * starRingEnd ℂ (r z) * 1).re = Complex.normSq (r z) := by
      rw [mul_one, Complex.mul_conj, Complex.ofReal_re]
    rw [hprod] at hle
    exact Complex.normSq_eq_zero.mp (le_antisymm hle (Complex.normSq_nonneg (r z)))
  have hr_zero : EqOn r 0 U :=
    hr_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_pre hz₀_U hr_ev0
  let x_seq : ℕ → ℝ := fun k => 1 / 2 - 1 / ((k : ℝ) + 3)
  let z_seq : ℕ → ℂ := fun k => (x_seq k : ℂ)
  have hz_mem : ∀ k : ℕ, z_seq k ∈ U := by
    intro k
    have hk_pos : 0 < (k : ℝ) + 3 := by positivity
    have hinv_pos : 0 < 1 / ((k : ℝ) + 3) := by positivity
    have hinv_le : 1 / ((k : ℝ) + 3) ≤ 1 / 3 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simp only [U, z_seq, x_seq, mem_setOf_eq, Complex.ofReal_re, abs_lt]
    constructor <;> linarith
  have hident : ∀ k : ℕ,
      (0 : ℂ) = 4 - 12 * ((1 / 4 : ℂ) - z_seq k ^ 2) / ((64 : ℂ) - z_seq k ^ 2) +
        ((1 / 4 : ℂ) - z_seq k ^ 2) * Ψ (z_seq k) := by
    intro k
    have hmem := hz_mem k
    have hrk : r (z_seq k) = 0 := hr_zero hmem
    have hu : (z_seq k).re ^ 2 < 1 / 4 := by
      have hmem' : |(z_seq k).re| < 1 / 2 := hmem
      have habs := abs_lt.mp hmem'
      nlinarith
    have h1 : (1 / 4 : ℂ) - z_seq k ^ 2 ≠ 0 := by
      simpa using sub_sq_ne_zero_of_re_sq_lt_or_im_ne_zero (c := 1 / 4) (by norm_num) (Or.inl hu)
    have hmul : ((1 / 4 : ℂ) - z_seq k ^ 2) * r (z_seq k) = 0 := by rw [hrk, mul_zero]
    rw [← hmul]
    dsimp only [r, depletedResolventKernel]
    rw [mul_add, mul_sub, mul_div_cancel₀ _ h1]
    ring
  have hx_tendsto : Tendsto x_seq atTop (𝓝 (1 / 2 : ℝ)) := by
    have hz : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) atTop (𝓝 0) := by
      have hshift := (tendsto_add_atTop_iff_nat 2).mpr
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine hshift.congr fun k => ?_
      push_cast
      ring
    simpa only [x_seq, sub_zero] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hz
  have hz_tendsto : Tendsto z_seq atTop (𝓝 (1 / 2 : ℂ)) := by
    have hc := (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp hx_tendsto
    simpa only [z_seq, Function.comp_def, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hc
  have hΨ_cont : ContinuousAt Ψ (1 / 2 : ℂ) := by
    refine (hΨ (1 / 2 : ℂ) ?_).continuousAt
    simp only [mem_setOf_eq]
    norm_num
  have hsub1 : Tendsto (fun k : ℕ => (1 / 4 : ℂ) - z_seq k ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 / 4 : ℂ))).sub (hz_tendsto.pow 2)
    have h0 : (1 / 4 : ℂ) - (1 / 2 : ℂ) ^ 2 = 0 := by norm_num
    rwa [h0] at h
  have hsub2 : Tendsto (fun k : ℕ => (64 : ℂ) - z_seq k ^ 2) atTop (𝓝 (255 / 4 : ℂ)) := by
    have h := (tendsto_const_nhds (x := (64 : ℂ))).sub (hz_tendsto.pow 2)
    have hc : (64 : ℂ) - (1 / 2 : ℂ) ^ 2 = 255 / 4 := by norm_num
    rwa [hc] at h
  have hrhs_tendsto : Tendsto
      (fun k : ℕ => 4 - 12 * ((1 / 4 : ℂ) - z_seq k ^ 2) / ((64 : ℂ) - z_seq k ^ 2) +
        ((1 / 4 : ℂ) - z_seq k ^ 2) * Ψ (z_seq k))
      atTop (𝓝 (4 : ℂ)) := by
    have hdiv := ((tendsto_const_nhds (x := (12 : ℂ))).mul hsub1).div hsub2 (by norm_num)
    have hprod := hsub1.mul (hΨ_cont.tendsto.comp hz_tendsto)
    have hall := ((tendsto_const_nhds (x := (4 : ℂ))).sub hdiv).add hprod
    have hval : (4 : ℂ) - 12 * 0 / (255 / 4) + 0 * Ψ (1 / 2) = 4 := by ring
    rwa [hval] at hall
  have hlhs_tendsto : Tendsto
      (fun k : ℕ => 4 - 12 * ((1 / 4 : ℂ) - z_seq k ^ 2) / ((64 : ℂ) - z_seq k ^ 2) +
        ((1 / 4 : ℂ) - z_seq k ^ 2) * Ψ (z_seq k))
      atTop (𝓝 (0 : ℂ)) :=
    (tendsto_const_nhds (x := (0 : ℂ))).congr hident
  have h04 : (0 : ℂ) = 4 := tendsto_nhds_unique hlhs_tendsto hrhs_tendsto
  norm_num at h04

/-- **Universal holomorphic multiplier CP domination no-go.**
No countable square-bounded family of multipliers `ψ_n` analytic on `{s : ℂ | s.re < 4}`
(`∑_n B_n < ∞`, `‖ψ_n(z)‖² ≤ B_n` on `|z.re| ≤ 1`) satisfies
`Re((m(z) + ∑_n ψ_n(z) ψ_n(-z)) u v) ≤ 0` for all `u, v ∈ ℂ` across the verified off-line strip
`{z : ℂ | 0 < |z.re| < 1/2 ∧ 431/2 ≤ z.im²}`. -/
theorem no_universal_holomorphic_multiplier_domination
    (ψ : ℕ → ℂ → ℂ) (B : ℕ → ℝ)
    (hψ : ∀ n, AnalyticOnNhd ℂ (ψ n) {s : ℂ | s.re < 4})
    (hB : Summable B)
    (hbd : ∀ n z, |z.re| ≤ 1 → ‖ψ n z‖ ^ 2 ≤ B n)
    (hdom : ∀ z : ℂ, 0 < |z.re| → |z.re| < 1 / 2 → 431 / 2 ≤ z.im ^ 2 →
      ∀ u v : ℂ, ((depletedResolventKernel z + ∑' n, ψ n z * ψ n (-z)) * u * v).re ≤ 0) :
    False := by
  let S₁ : Set ℂ := {z : ℂ | |z.re| < 1}
  have hS₁_open : IsOpen S₁ :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hF_diff : ∀ n : ℕ, DifferentiableOn ℂ (fun z => ψ n z * ψ n (-z)) S₁ := by
    intro n
    have hana : AnalyticOnNhd ℂ (fun z => ψ n z * ψ n (-z)) S₁ := by
      intro z hz
      have hz' : |z.re| < 1 := hz
      have habs := abs_lt.mp hz'
      have h1 : AnalyticAt ℂ (ψ n) z := hψ n z (by simp only [mem_setOf_eq]; linarith)
      have h2 : AnalyticAt ℂ (fun w => ψ n (-w)) z :=
        (hψ n (-z) (by simp only [mem_setOf_eq, Complex.neg_re]; linarith)).comp
          (analyticAt_id.fun_neg)
      exact h1.fun_mul h2
    exact hana.differentiableOn
  have hF_le : ∀ (n : ℕ) (z : ℂ), z ∈ S₁ → ‖ψ n z * ψ n (-z)‖ ≤ B n := by
    intro n z hz
    have hz_le : |z.re| ≤ 1 := le_of_lt hz
    have hnz_le : |(-z).re| ≤ 1 := by simpa only [Complex.neg_re, abs_neg] using hz_le
    have hb1 := hbd n z hz_le
    have hb2 := hbd n (-z) hnz_le
    rw [norm_mul]
    nlinarith [sq_nonneg (‖ψ n z‖ - ‖ψ n (-z)‖)]
  have htsum_diff : DifferentiableOn ℂ (fun z => ∑' n, ψ n z * ψ n (-z)) S₁ :=
    Complex.differentiableOn_tsum_of_summable_norm hB hF_diff hS₁_open hF_le
  exact not_analyticOnNhd_domination_of_depletedResolventKernel
    (htsum_diff.analyticOnNhd hS₁_open) hdom

private theorem analyticAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
    AnalyticAt ℂ (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (analyticAt_const : AnalyticAt ℂ (fun _ => (0 : ℂ)) z)
  | @insert a s ha ih =>
      have h1 : AnalyticAt ℂ (f a) z := hf a (Finset.mem_insert_self a s)
      have h2 : AnalyticAt ℂ (fun w => ∑ i ∈ s, f i w) z :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simpa only [Finset.sum_insert ha] using h1.fun_add h2

/-- Finite-family corollary (requiring no growth bound on `ψ`): no finite family of multipliers
`ψ : Fin m → ℂ → ℂ` analytic on `{s : ℂ | s.re < 4}` satisfies
`Re((m(z) + ∑_{i < m} ψ_i(z) ψ_i(-z)) u v) ≤ 0` across `{z : ℂ | 0 < |z.re| < 1/2 ∧ 431/2 ≤ z.im²}`. -/
theorem no_finite_universal_holomorphic_multiplier_domination
    {m : ℕ} (ψ : Fin m → ℂ → ℂ)
    (hψ : ∀ i, AnalyticOnNhd ℂ (ψ i) {s : ℂ | s.re < 4})
    (hdom : ∀ z : ℂ, 0 < |z.re| → |z.re| < 1 / 2 → 431 / 2 ≤ z.im ^ 2 →
      ∀ u v : ℂ,
        ((depletedResolventKernel z + ∑ i : Fin m, ψ i z * ψ i (-z)) * u * v).re ≤ 0) :
    False := by
  have hΨ : AnalyticOnNhd ℂ (fun z => ∑ i : Fin m, ψ i z * ψ i (-z))
      {z : ℂ | |z.re| < 1} := by
    intro z hz
    have hz' : |z.re| < 1 := hz
    have habs := abs_lt.mp hz'
    refine analyticAt_finset_sum Finset.univ fun i _ => ?_
    have h1 : AnalyticAt ℂ (ψ i) z := hψ i z (by simp only [mem_setOf_eq]; linarith)
    have h2 : AnalyticAt ℂ (fun w => ψ i (-w)) z :=
      (hψ i (-z) (by simp only [mem_setOf_eq, Complex.neg_re]; linarith)).comp
        (analyticAt_id.fun_neg)
    exact h1.fun_mul h2
  exact not_analyticOnNhd_domination_of_depletedResolventKernel hΨ hdom

#print axioms integrable_halfLineResolvent_sq_mul_exp_neg_eight
#print axioms integral_halfLineResolvent_sq_mul_exp_neg_eight_le
#print axioms integral_mul_halfLineResolvent_exp_neg_eight
#print axioms integral_halfLineResolvent_mul_halfLineResolvent_exp_neg_eight
#print axioms halfLineResolvent_comp_sub
#print axioms integral_mul_iteratedResolvent_fifteen_halves_eight
#print axioms iteratedResolvent_depletion_identity
#print axioms laplace_halfLineResolvent
#print axioms re_depletedResolventKernel_neg_of_strip
#print axioms twenty_five_mul_norm_sq_depletedResolventKernel_lt_neg_re
#print axioms re_depletedResolventKernel_xiZeroCopy_neg
#print axioms twenty_five_mul_norm_sq_depletedResolventKernel_xiZeroCopy_lt
#print axioms analyticOnNhd_depletedSquareRootFactor_upper
#print axioms analyticOnNhd_depletedSquareRootFactor_lower
#print axioms depletedSquareRootFactor_conj
#print axioms depletedSquareRootFactor_mul_neg
#print axioms depletedSquareRootFactor_mul_neg_xiZeroCopy
#print axioms no_universal_holomorphic_multiplier_domination
#print axioms no_finite_universal_holomorphic_multiplier_domination

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

