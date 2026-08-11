import GaloisForLFunctions.HTGeometry.MomentInnerProduct
import GaloisForLFunctions.HTGeometry.PoleUnitFormationMechanics

/-!
# The Gamma base law of a pole-unit formation

The pole-retaining response of a regular unit, read on the shifted ray `w = 1 + t`, is the
Laplace transform of the rescaled logarithmic clock attached to the pole.  As the base scale
degenerates the unit quotient tends to one, so the transform tends to the universal base
`(1 + t)^{-r}` — the Laplace transform of the Gamma law of shape `r`.

This module certifies that base law and its moment structure:

* the base limit of the corrected and pole-retaining responses;
* every derivative of the base transform, giving the ascending-factorial moments `(r)_n`;
* those moments as genuine integrals of the shape-`r` Gamma density, and strict positive
  definiteness of every finite Hankel section of the moment sequence;
* the exact cumulant slope and curvature laws of the response, whose values at the base scale are
  the mean and the variance of the clock.
-/

open MeasureTheory Set Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The universal Gamma base transform -/

/-- Laplace transform of the unit-rate Gamma law of shape `r`, in the shifted variable. -/
def gammaBaseTransform (r : ℕ) (t : ℂ) : ℂ := (1 + t) ^ (-(r : ℤ))

/-- The ascending factorial `(r)_n`, the `n`-th moment of the unit-rate Gamma law of shape `r`. -/
def gammaShapeMoment (r : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (r + i)

@[simp] theorem gammaShapeMoment_zero (r : ℝ) : gammaShapeMoment r 0 = 1 := by
  simp [gammaShapeMoment]

theorem gammaShapeMoment_succ (r : ℝ) (n : ℕ) :
    gammaShapeMoment r (n + 1) = gammaShapeMoment r n * (r + n) := by
  simp [gammaShapeMoment, Finset.prod_range_succ]

theorem gammaBaseTransform_eq_inv_pow (r : ℕ) (t : ℂ) :
    gammaBaseTransform r t = ((1 + t) ^ r)⁻¹ := by
  rw [gammaBaseTransform, zpow_neg, zpow_natCast]

/-- Reflecting the base of a descending product turns it into an ascending one up to sign. -/
theorem prod_range_neg_sub (a : ℂ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (-a - i) = (-1) ^ n * ∏ i ∈ Finset.range n, (a + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]; ring

/-- **Every derivative of the Gamma base transform.**  The `n`-th derivative carries the
ascending factorial `(r)_n` and shifts the shape by `n`. -/
theorem iteratedDeriv_gammaBaseTransform (r n : ℕ) (t : ℂ) :
    iteratedDeriv n (gammaBaseTransform r) t =
      (-1) ^ n * (∏ i ∈ Finset.range n, ((r : ℂ) + i)) * (1 + t) ^ (-((r : ℤ) + n)) := by
  have hkey : iteratedDeriv n (gammaBaseTransform r)
      = fun s : ℂ => iteratedDeriv n (fun y : ℂ => y ^ (-(r : ℤ))) (1 + s) :=
    iteratedDeriv_comp_const_add n (fun y : ℂ => y ^ (-(r : ℤ))) 1
  have hcast : (((-(r : ℤ)) : ℤ) : ℂ) = -(r : ℂ) := by push_cast; ring
  have hexp : (-(r : ℤ) - n) = -((r : ℤ) + n) := by ring
  rw [congrFun hkey t, iteratedDeriv_eq_iterate, iter_deriv_zpow, hcast, prod_range_neg_sub,
    hexp, mul_assoc]

/-! ## Base limit of the formation response -/

/-- The regular-unit response tends to one as the base scale degenerates. -/
theorem tendsto_correctedScaleResponse_one {U : ℂ → ℂ} (hU : ContinuousAt U 0) (hU0 : U 0 ≠ 0)
    (w : ℂ) : Tendsto (fun ε : ℂ => correctedScaleResponse U ε w) (𝓝 0) (𝓝 1) := by
  have hnum : Tendsto (fun ε : ℂ => U (ε * w)) (𝓝 0) (𝓝 (U 0)) := by
    have hcont : ContinuousAt (fun ε : ℂ => ε * w) 0 := by fun_prop
    have hinner : Tendsto (fun ε : ℂ => ε * w) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto
    exact hU.tendsto.comp hinner
  have hden : Tendsto (fun ε : ℂ => U ε) (𝓝 0) (𝓝 (U 0)) := hU.tendsto
  have hdiv : Tendsto (fun ε : ℂ => U (ε * w) / U ε) (𝓝 0) (𝓝 (U 0 / U 0)) :=
    Filter.Tendsto.div hnum hden hU0
  rw [div_self hU0] at hdiv
  exact hdiv

/-- **Universal Gamma base.**  On the shifted ray the pole-retaining response converges to the
Laplace transform of the Gamma law of shape `r`. -/
theorem tendsto_polarScaleResponse_gammaBase (r : ℕ) {U : ℂ → ℂ} (hU : ContinuousAt U 0)
    (hU0 : U 0 ≠ 0) (t : ℂ) :
    Tendsto (fun ε : ℂ => polarScaleResponse r U ε (1 + t)) (𝓝 0) (𝓝 (gammaBaseTransform r t)) := by
  have h := (tendsto_correctedScaleResponse_one hU hU0 (1 + t)).const_mul (((1 + t) ^ r)⁻¹)
  rw [gammaBaseTransform_eq_inv_pow r t]
  simpa [polarScaleResponse] using h

/-! ## Moments of the Gamma law -/

/-- Unnormalized density of the unit-rate Gamma law of shape `r`. -/
def gammaShapeWeight (r x : ℝ) : ℝ := Real.exp (-x) * x ^ (r - 1)

theorem gammaShapeWeight_pos {r x : ℝ} (hx : 0 < x) : 0 < gammaShapeWeight r x :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx _)

theorem pow_mul_gammaShapeWeight (r : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ k * gammaShapeWeight r x = gammaShapeWeight (r + k) x := by
  rw [gammaShapeWeight, gammaShapeWeight]
  have hsplit : x ^ (r + (k : ℝ) - 1) = x ^ (r - 1) * x ^ (k : ℝ) := by
    rw [← Real.rpow_add hx]
    ring_nf
  rw [hsplit, Real.rpow_natCast]
  ring

theorem integrableOn_gammaShapeWeight {r : ℝ} (hr : 0 < r) :
    IntegrableOn (gammaShapeWeight r) (Ioi 0) :=
  Real.GammaIntegral_convergent hr

theorem integrableOn_pow_mul_gammaShapeWeight {r : ℝ} (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * gammaShapeWeight r x) (Ioi 0) := by
  have hrk : (0 : ℝ) < r + k := by positivity
  refine (integrableOn_gammaShapeWeight hrk).congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact (pow_mul_gammaShapeWeight r k hx).symm

theorem integral_pow_mul_gammaShapeWeight {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ k * gammaShapeWeight r x = Real.Gamma (r + k) := by
  have hrk : (0 : ℝ) < r + k := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pow_mul_gammaShapeWeight r k hx)]
  exact (Real.Gamma_eq_integral hrk).symm

/-- The Gamma function shifted by a natural number factors through the ascending factorial. -/
theorem Gamma_add_natCast {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Real.Gamma (r + k) = gammaShapeMoment r k * Real.Gamma r := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hne : r + (k : ℝ) ≠ 0 := by positivity
      have hstep : Real.Gamma (r + (k : ℝ) + 1) = (r + k) * Real.Gamma (r + k) :=
        Real.Gamma_add_one hne
      have hcast : (r : ℝ) + ((k + 1 : ℕ) : ℝ) = r + (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, hstep, ih, gammaShapeMoment_succ]
      ring

/-- **Gamma moments.**  The `k`-th moment of the unit-rate Gamma law of shape `r` is `(r)_k`. -/
theorem gammaShapeLaw_moment {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * gammaShapeWeight r x) / Real.Gamma r = gammaShapeMoment r k := by
  rw [integral_pow_mul_gammaShapeWeight hr k, Gamma_add_natCast hr k]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hr)]

/-! ## Positive definiteness of the Gamma Hankel tower -/

theorem integrableOn_eval_mul_gammaShapeWeight {r : ℝ} (hr : 0 < r) (q : Polynomial ℝ) :
    IntegrableOn (fun x : ℝ => Polynomial.eval x q * gammaShapeWeight r x) (Ioi 0) := by
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ k ∈ q.support, q.coeff k * (x ^ k * gammaShapeWeight r x)) (Ioi 0) :=
    integrable_finsetSum _ (fun k _ =>
      (integrableOn_pow_mul_gammaShapeWeight hr k).const_mul _)
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro x _
  show ∑ k ∈ q.support, q.coeff k * (x ^ k * gammaShapeWeight r x)
      = Polynomial.eval x q * gammaShapeWeight r x
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem momentFunctional_gammaShapeMoment {r : ℝ} (hr : 0 < r) (q : Polynomial ℝ) :
    _root_.HTGeometry.momentFunctional (gammaShapeMoment r) q =
      (∫ x in Ioi (0 : ℝ), Polynomial.eval x q * gammaShapeWeight r x) / Real.Gamma r := by
  have hΓ : Real.Gamma r ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hr)
  have hrw : ∫ x in Ioi (0 : ℝ), Polynomial.eval x q * gammaShapeWeight r x
      = ∑ k ∈ q.support, q.coeff k * (gammaShapeMoment r k * Real.Gamma r) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (f := fun x : ℝ => Polynomial.eval x q * gammaShapeWeight r x)
      (g := fun x : ℝ => ∑ k ∈ q.support, q.coeff k * (x ^ k * gammaShapeWeight r x)) ?_]
    · rw [integral_finsetSum _
        (fun k _ => (integrableOn_pow_mul_gammaShapeWeight hr k).const_mul _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, integral_pow_mul_gammaShapeWeight hr k, Gamma_add_natCast hr k]
    · intro x _
      show Polynomial.eval x q * gammaShapeWeight r x
          = ∑ k ∈ q.support, q.coeff k * (x ^ k * gammaShapeWeight r x)
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrw, _root_.HTGeometry.momentFunctional_eq_support_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/-- The square integral of a nonzero polynomial against the Gamma density is strictly positive. -/
theorem integral_sq_mul_gammaShapeWeight_pos {r : ℝ} (hr : 0 < r) {p : Polynomial ℝ}
    (hp : p ≠ 0) :
    0 < ∫ x in Ioi (0 : ℝ), (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x := by
  have hint : IntegrableOn
      (fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x) (Ioi 0) := by
    refine (integrableOn_eval_mul_gammaShapeWeight hr (p ^ 2)).congr_fun ?_ measurableSet_Ioi
    intro x _
    show Polynomial.eval x (p ^ 2) * gammaShapeWeight r x
        = (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x
    rw [Polynomial.eval_pow]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    simpa using mul_nonneg (sq_nonneg (Polynomial.eval x p)) (gammaShapeWeight_pos hx).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  by_contra hzero
  have hmeas : volume (Function.support
      (fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x) ∩ Ioi 0) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hzero)
  have hroots : {x : ℝ | Polynomial.IsRoot p x}.Finite := Polynomial.finite_setOf_isRoot hp
  have hsub : Ioi (0 : ℝ) ⊆
      (Function.support (fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x) ∩ Ioi 0)
        ∪ {x : ℝ | Polynomial.IsRoot p x} := by
    intro x hx
    by_cases hroot : Polynomial.eval x p = 0
    · exact Or.inr hroot
    · refine Or.inl ⟨?_, hx⟩
      have : (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x ≠ 0 := by
        have h1 : (Polynomial.eval x p) ^ 2 ≠ 0 := pow_ne_zero _ hroot
        exact mul_ne_zero h1 (ne_of_gt (gammaShapeWeight_pos hx))
      simpa [Function.mem_support] using this
  have hle : volume (Ioi (0 : ℝ)) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc volume (Ioi (0 : ℝ))
        ≤ volume ((Function.support
            (fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x) ∩ Ioi 0)
            ∪ {x : ℝ | Polynomial.IsRoot p x}) := measure_mono hsub
      _ ≤ volume (Function.support
            (fun x : ℝ => (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x) ∩ Ioi 0)
            + volume {x : ℝ | Polynomial.IsRoot p x} := measure_union_le _ _
      _ = 0 := by rw [hmeas, hroots.measure_zero]; simp
  simp at hle

/-- **Positive definiteness of the Gamma moment form.** -/
theorem gammaShapeMoment_positiveMomentForm {r : ℝ} (hr : 0 < r) :
    _root_.HTGeometry.PositiveMomentForm (gammaShapeMoment r) := by
  refine ⟨fun p hp => ?_⟩
  rw [_root_.HTGeometry.momentInner_self, momentFunctional_gammaShapeMoment hr]
  have hcongr : ∫ x in Ioi (0 : ℝ), Polynomial.eval x (p ^ 2) * gammaShapeWeight r x
      = ∫ x in Ioi (0 : ℝ), (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    show Polynomial.eval x (p ^ 2) * gammaShapeWeight r x
        = (Polynomial.eval x p) ^ 2 * gammaShapeWeight r x
    rw [Polynomial.eval_pow]
  rw [hcongr]
  exact div_pos (integral_sq_mul_gammaShapeWeight_pos hr hp) (Real.Gamma_pos_of_pos hr)

/-- **The Gamma Hankel tower is strictly positive definite.**  Every finite Hankel section of the
ascending-factorial moment sequence is positive definite. -/
theorem gammaShapeMoment_momentHankelMatrix_posDef {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (_root_.HTGeometry.momentHankelMatrix (gammaShapeMoment r) n).PosDef :=
  _root_.HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp
    (gammaShapeMoment_positiveMomentForm hr) n

/-! ## Exact cumulant laws of the response -/

/-- **Cumulant slope law.**  The logarithmic derivative of the pole-retaining response splits into
the universal pole term and the transported logarithmic derivative of the unit. -/
theorem logDeriv_polarScaleResponse (r : ℕ) {U : ℂ → ℂ} {ε w : ℂ} (hw : w ≠ 0)
    (hU : DifferentiableAt ℂ U (ε * w)) (hUw : U (ε * w) ≠ 0) (hUε : U ε ≠ 0) :
    logDeriv (fun z => polarScaleResponse r U ε z) w =
      -(r : ℂ) / w + ε * logDeriv U (ε * w) := by
  have hpole : logDeriv (fun z : ℂ => (z ^ r)⁻¹) w = -(r : ℂ) / w := by
    have hfun : (fun z : ℂ => (z ^ r)⁻¹) = fun z : ℂ => z ^ (-(r : ℤ)) := by
      funext z
      rw [zpow_neg, zpow_natCast]
    rw [hfun, logDeriv_zpow]
    push_cast
    ring
  have hinner : DifferentiableAt ℂ (fun z : ℂ => ε * z) w := by fun_prop
  have hunit : logDeriv (fun z : ℂ => correctedScaleResponse U ε z) w = ε * logDeriv U (ε * w) := by
    have hcomp : logDeriv (U ∘ fun z : ℂ => ε * z) w = logDeriv U (ε * w) * ε := by
      have := logDeriv_comp (f := U) (g := fun z : ℂ => ε * z) (x := w) hU hinner
      simpa using this
    have hfun : (fun z : ℂ => correctedScaleResponse U ε z)
        = fun z : ℂ => (U ∘ fun y : ℂ => ε * y) z / U ε := rfl
    rw [hfun, logDeriv_div w (by simpa using hUw) hUε
      ((hU.comp w hinner)) (differentiableAt_const _), logDeriv_const]
    simp only [Pi.zero_apply, sub_zero]
    rw [hcomp]
    ring
  have hne1 : ((w : ℂ) ^ r)⁻¹ ≠ 0 := by
    simp [pow_ne_zero r hw]
  have hne2 : correctedScaleResponse U ε w ≠ 0 := by
    rw [correctedScaleResponse]
    exact div_ne_zero hUw hUε
  have hdiff1 : DifferentiableAt ℂ (fun z : ℂ => (z ^ r)⁻¹) w :=
    (differentiableAt_pow r).inv (pow_ne_zero r hw)
  have hdiff2 : DifferentiableAt ℂ (fun z : ℂ => correctedScaleResponse U ε z) w :=
    (hU.comp w hinner).div_const _
  have hfun : (fun z : ℂ => polarScaleResponse r U ε z)
      = fun z : ℂ => (z ^ r)⁻¹ * correctedScaleResponse U ε z := rfl
  rw [hfun, logDeriv_mul w hne1 hne2 hdiff1 hdiff2, hpole, hunit]

/-- **Cumulant curvature law.**  Differentiating the slope law once more produces the universal
pole curvature plus the transported curvature of the unit logarithm. -/
theorem deriv_logDeriv_polarScaleResponse (r : ℕ) {U : ℂ → ℂ} {ε w : ℂ} (hw : w ≠ 0)
    (hU : AnalyticAt ℂ U (ε * w)) (hUne : ∀ᶠ z in 𝓝 (ε * w), U z ≠ 0) (hUε : U ε ≠ 0) :
    deriv (fun z => logDeriv (fun y => polarScaleResponse r U ε y) z) w =
      (r : ℂ) / w ^ 2 + ε ^ 2 * deriv (logDeriv U) (ε * w) := by
  have hinnercont : ContinuousAt (fun z : ℂ => ε * z) w := by fun_prop
  have hpre : ∀ᶠ z in 𝓝 w, U (ε * z) ≠ 0 := hinnercont.eventually hUne
  have hzne : ∀ᶠ z in 𝓝 w, z ≠ 0 := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hw)] with z hz
    simpa using hz
  have hUana : ∀ᶠ z in 𝓝 w, AnalyticAt ℂ U (ε * z) := by
    have := hinnercont.eventually (hU.eventually_analyticAt)
    exact this
  have heq : (fun z => logDeriv (fun y => polarScaleResponse r U ε y) z)
      =ᶠ[𝓝 w] fun z => -(r : ℂ) / z + ε * logDeriv U (ε * z) := by
    filter_upwards [hpre, hzne, hUana] with z hz1 hz2 hz3
    exact logDeriv_polarScaleResponse r hz2 hz3.differentiableAt hz1 hUε
  rw [heq.deriv_eq]
  have hlogana : AnalyticAt ℂ (logDeriv U) (ε * w) := by
    have h1 : AnalyticAt ℂ (deriv U) (ε * w) := hU.deriv
    have h2 : U (ε * w) ≠ 0 := hUne.self_of_nhds
    exact h1.div hU h2
  have hd1 : HasDerivAt (fun z : ℂ => -(r : ℂ) / z) ((r : ℂ) / w ^ 2) w := by
    have := (hasDerivAt_id w).inv hw
    have h2 : HasDerivAt (fun z : ℂ => -(r : ℂ) * z⁻¹) (-(r : ℂ) * (-1 / w ^ 2)) w :=
      this.const_mul _
    have hrw : (fun z : ℂ => -(r : ℂ) / z) = fun z : ℂ => -(r : ℂ) * z⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [hrw]
    convert h2 using 1
    field_simp
  have hmul : HasDerivAt (fun z : ℂ => ε * z) ε w := by
    simpa using (hasDerivAt_id w).const_mul ε
  have hd2 : HasDerivAt (fun z : ℂ => ε * logDeriv U (ε * z))
      (ε * (deriv (logDeriv U) (ε * w) * ε)) w :=
    (HasDerivAt.comp w hlogana.differentiableAt.hasDerivAt hmul).const_mul _
  have hsum : HasDerivAt (fun z : ℂ => -(r : ℂ) / z + ε * logDeriv U (ε * z))
      ((r : ℂ) / w ^ 2 + ε * (deriv (logDeriv U) (ε * w) * ε)) w := hd1.add hd2
  rw [hsum.deriv]
  ring

/-- **Mean of the pole clock.**  The first cumulant of the response at the base scale is the pole
order corrected by the transported logarithmic derivative of the unit. -/
theorem polarScaleResponse_first_cumulant (r : ℕ) {U : ℂ → ℂ} {ε : ℂ}
    (hU : DifferentiableAt ℂ U ε) (hUε : U ε ≠ 0) :
    -logDeriv (fun z => polarScaleResponse r U ε z) 1 = (r : ℂ) - ε * logDeriv U ε := by
  have h := logDeriv_polarScaleResponse r (U := U) (ε := ε) (w := 1) one_ne_zero
    (by simpa using hU) (by simpa using hUε) hUε
  rw [h]
  simp
  ring

/-- **Variance of the pole clock.**  The second cumulant of the response at the base scale is the
pole order corrected by the transported curvature of the unit logarithm. -/
theorem polarScaleResponse_second_cumulant (r : ℕ) {U : ℂ → ℂ} {ε : ℂ}
    (hU : AnalyticAt ℂ U ε) (hUne : ∀ᶠ z in 𝓝 ε, U z ≠ 0) (hUε : U ε ≠ 0) :
    deriv (fun z => logDeriv (fun y => polarScaleResponse r U ε y) z) 1 =
      (r : ℂ) + ε ^ 2 * deriv (logDeriv U) ε := by
  have h := deriv_logDeriv_polarScaleResponse r (U := U) (ε := ε) (w := 1) one_ne_zero
    (by simpa using hU) (by simpa using hUne) hUε
  simpa using h

end

end GaloisForLFunctions.HTGeometry
