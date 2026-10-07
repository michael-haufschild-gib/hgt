import GaloisForLFunctions.RHTower.WeilLinearTwistPositivity
import GaloisForLFunctions.RHTower.WeilWorkQuantizationBoundaryPhase
import GaloisForLFunctions.RHTower.WeilBoundaryIntegerCountingRigidity
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual Weil producer has a measurable boundary trace

Full positivity supplies a normalized primitive and a completed producer on the
open critical half-plane. Its horizontal modulus is monotone. Canonical Poisson
inversion supplies the limiting argument at non-atomic endpoints. Neither
atomicity nor a spectral gap nor boundary continuity is assumed.

This constructs the source trace and its exact reflection phase. It does not
prove phase settlement or the contour rigidity theorem for this trace.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilWorkSettledPhase

open WeilSpectral WeilHerglotz IntegerMassRigidity PhaseLockRigidity AbelianTwist

private theorem exists_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ P : ℂ → ℂ, P 2 = 0 ∧
      ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (weilContinuation hW s) s :=
  (GaloisForLFunctions.HTGeometry.isExactOn_rightHalfPlane
    (differentiableOn_weilContinuation hW)).with_val_at 2 0

/-- The primitive of the actual Weil continuation, normalized to zero at two. -/
def sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ → ℂ :=
  Classical.choose (exists_sourcePrimitive hW)

@[simp] theorem sourcePrimitive_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    sourcePrimitive hW 2 = 0 := (Classical.choose_spec (exists_sourcePrimitive hW)).1

theorem hasDerivAt_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (sourcePrimitive hW) (weilContinuation hW s) s :=
  (Classical.choose_spec (exists_sourcePrimitive hW)).2 s hs

theorem sourcePrimitive_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    sourcePrimitive hW (conj s) = conj (sourcePrimitive hW s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re}
  set Q : ℂ → ℂ := conj ∘ sourcePrimitive hW ∘ conj
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hPd : ∀ z ∈ U, HasDerivAt (sourcePrimitive hW) (weilContinuation hW z) z :=
    fun z hz => hasDerivAt_sourcePrimitive hW hz
  have hQd : ∀ z ∈ U, HasDerivAt Q (weilContinuation hW z) z := by
    intro z hz
    have h := (hasDerivAt_sourcePrimitive hW
      (s := conj z) (by simpa [U] using hz)).conj_conj
    rw [weilContinuation_conj hW hz] at h
    simpa only [Complex.conj_conj] using h
  have heq := hUo.eqOn_of_deriv_eq (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (fun z hz => (hPd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hPd z hz).deriv, (hQd z hz).deriv])
    (show (2 : ℂ) ∈ U by norm_num [U])
    (show sourcePrimitive hW 2 = Q 2 by
      simp only [Q, Function.comp_apply, Complex.conj_ofNat, sourcePrimitive_two, map_zero])
  simpa [Q, Function.comp_def] using heq (show conj s ∈ U by simpa [U] using hs)

/-- The completed producer obtained from the original source. -/
def sourceCompletion {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  bigG lam 2 * cexp (sourcePrimitive hW s)

@[simp] theorem sourceCompletion_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    sourceCompletion hW 2 = bigG lam 2 := by simp [sourceCompletion]

theorem hasDerivAt_sourceCompletion {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (sourceCompletion hW)
      (weilContinuation hW s * sourceCompletion hW s) s := by
  exact ((hasDerivAt_sourcePrimitive hW hs).cexp.const_mul (bigG lam 2)).congr_deriv
    (by simp only [sourceCompletion]; ring)

theorem sourceCompletion_eq_bigG {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : sourceCompletion hW s = bigG lam s := by
  apply G_eq_bigG (fun σ hσ =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)
    (fun z hz => ?_) (fun z hz => hasDerivAt_sourceCompletion hW hz)
    (sourceCompletion_two hW) hs
  rw [weilContinuation_eq hW hz, weilFunction, zetaArchimedeanDatum]
  have hf : lamC lam = lamTwo lam := by
    funext n
    unfold lamC lamTwo
    split_ifs <;> simp
  rw [hf]

theorem sourceCompletion_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    sourceCompletion hW (conj s) = conj (sourceCompletion hW s) := by
  simp only [sourceCompletion, sourcePrimitive_conj hW hs, Complex.exp_conj, map_mul,
    bigG_two_conj]

/-- A point at positive horizontal distance from the critical line. -/
def tracePoint (x y : ℝ) : ℂ := ((1 / 2 + x : ℝ) : ℂ) + y * I

@[simp] theorem tracePoint_re (x y : ℝ) : (tracePoint x y).re = 1 / 2 + x := by
  simp [tracePoint]

@[simp] theorem tracePoint_conj (x y : ℝ) : conj (tracePoint x y) = tracePoint x (-y) := by
  simp only [tracePoint, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
    Complex.ofReal_neg]
  ring

private theorem hasDerivAt_tracePoint_fst (x y : ℝ) :
    HasDerivAt (fun u : ℝ => tracePoint u y) 1 x := by
  simpa [tracePoint] using (((hasDerivAt_id x).const_add (1 / 2 : ℝ)).ofReal_comp).add_const
    ((y : ℂ) * I)

private theorem hasDerivAt_tracePoint_snd (x y : ℝ) :
    HasDerivAt (tracePoint x) I y := by
  change HasDerivAt (fun t : ℝ => (((1 / 2 + x : ℝ) : ℂ)) + t * I) I y
  simpa only [Complex.ofReal_one, one_mul, id_eq] using! ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add
    (((1 / 2 + x : ℝ) : ℂ))

private theorem hasDerivAt_re_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun u : ℝ => (sourcePrimitive hW (tracePoint u y)).re)
      (weilContinuation hW (tracePoint x y)).re x := by
  have h := (hasDerivAt_sourcePrimitive hW (s := tracePoint x y) (by simp; linarith)).comp
    x (hasDerivAt_tracePoint_fst x y)
  simpa using! Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

private theorem hasDerivAt_im_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (fun t : ℝ => (sourcePrimitive hW (tracePoint x t)).im)
      (weilContinuation hW (tracePoint x y)).re y := by
  have h := (hasDerivAt_sourcePrimitive hW (s := tracePoint x y) (by simp; linarith)).comp
    y (hasDerivAt_tracePoint_snd x y)
  simpa using! Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h

theorem monotoneOn_exp_re_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    MonotoneOn (fun x : ℝ => Real.exp (sourcePrimitive hW (tracePoint x y)).re) (Ioi 0) := by
  have hm : MonotoneOn (fun x : ℝ => (sourcePrimitive hW (tracePoint x y)).re) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun x hx => (hasDerivAt_re_sourcePrimitive hW hx y).continuousAt.continuousWithinAt)
      (fun x hx => (hasDerivAt_re_sourcePrimitive hW (interior_subset hx) y).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)
    rw [(hasDerivAt_re_sourcePrimitive hW (interior_subset hx) y).deriv]
    exact re_weilContinuation_nonneg hW (by simp; exact interior_subset hx)
  exact fun a ha b hb hab => Real.exp_le_exp.mpr (hm ha hb hab)

/-- The source modulus at the boundary, before multiplication by `bigG lam 2`. -/
def traceModulus {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℝ :=
  sInf ((fun x : ℝ => Real.exp (sourcePrimitive hW (tracePoint x y)).re) '' Ioi 0)

private theorem traceModulus_bddBelow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    BddBelow ((fun x : ℝ => Real.exp (sourcePrimitive hW (tracePoint x y)).re) '' Ioi 0) :=
  ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact (Real.exp_pos _).le⟩

theorem traceModulus_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    0 ≤ traceModulus hW y := by
  exact le_csInf ⟨_, ⟨1, by norm_num, rfl⟩⟩ (by rintro _ ⟨x, hx, rfl⟩; positivity)

theorem tendsto_traceModulus {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (sourcePrimitive hW (tracePoint x y)).re)
      (𝓝[>] 0) (𝓝 (traceModulus hW y)) :=
  (monotoneOn_exp_re_sourcePrimitive hW y).tendsto_nhdsGT (traceModulus_bddBelow hW y)

theorem two_mul_im_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    2 * (sourcePrimitive hW (tracePoint x y)).im =
      ∫ t in Ioc (-y) y, (weilContinuation hW (tracePoint x t)).re := by
  have hc : Continuous fun t : ℝ => (weilContinuation hW (tracePoint x t)).re := by
    refine Complex.continuous_re.comp ?_
    exact (differentiableOn_weilContinuation hW).continuousOn.comp_continuous
      (by unfold tracePoint; fun_prop) (fun t => by simp; linarith)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_im_sourcePrimitive hW hx t) (hc.intervalIntegrable (-y) y)
  rw [intervalIntegral.integral_of_le (by linarith)] at hi
  have hs := sourcePrimitive_conj hW (s := tracePoint x y) (by simp; linarith)
  rw [tracePoint_conj] at hs
  have him := congrArg Complex.im hs
  simp only [Complex.conj_im] at him
  linarith

/-- Limiting argument at every positive non-atomic endpoint, retaining all central mass. -/
theorem tendsto_im_sourcePrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) (hμ : boundaryMeasure hW {y} = 0) :
    Tendsto (fun x : ℝ => (sourcePrimitive hW (tracePoint x y)).im)
      (𝓝[>] 0) (𝓝 (Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) / 2)) := by
  have hneg : boundaryMeasure hW {-y} = 0 := by rw [boundaryMeasure_singleton_neg hW, hμ]
  have hlim := (tendsto_re_weilContinuation_interval hW (by linarith : -y < y) hneg hμ).div_const 2
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  change (∫ t in Ioc (-y) y, (weilContinuation hW (tracePoint x t)).re) / 2 = _
  rw [← two_mul_im_sourcePrimitive hW hx hy.le]
  ring

/-- The explicit positive-height trace, using the whole symmetric interval. -/
def positiveTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  bigG lam 2 * (traceModulus hW y : ℂ) *
    cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) / 2 : ℝ) : ℂ) * I)

/-- A boundary representative; negative heights are defined by conjugation. -/
def sourceTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  if 0 ≤ y then positiveTrace hW y else conj (positiveTrace hW (-y))

theorem tendsto_positiveTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) (hμ : boundaryMeasure hW {y} = 0) :
    Tendsto (fun x : ℝ => sourceCompletion hW (tracePoint x y))
      (𝓝[>] 0) (𝓝 (positiveTrace hW y)) := by
  have hm := (Complex.continuous_ofReal.tendsto _).comp (tendsto_traceModulus hW y)
  have hp := Complex.continuous_exp.tendsto _ |>.comp
    (((Complex.continuous_ofReal.tendsto _).comp (tendsto_im_sourcePrimitive hW hy hμ)).mul_const I)
  refine ((tendsto_const_nhds.mul hm).mul hp).congr' ?_
  exact Eventually.of_forall fun x => by
    change bigG lam 2 * ((Real.exp (sourcePrimitive hW (tracePoint x y)).re : ℝ) : ℂ) *
      cexp (((sourcePrimitive hW (tracePoint x y)).im : ℂ) * I) =
      bigG lam 2 * cexp (sourcePrimitive hW (tracePoint x y))
    rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]

theorem tendsto_sourceTrace_of_nonatom {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : y ≠ 0) (hμ : boundaryMeasure hW {y} = 0) :
    Tendsto (fun x : ℝ => sourceCompletion hW (tracePoint x y))
      (𝓝[>] 0) (𝓝 (sourceTrace hW y)) := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · have hμneg : boundaryMeasure hW {-y} = 0 := by
      rw [boundaryMeasure_singleton_neg hW, hμ]
    have hlim := (Complex.continuous_conj.tendsto _).comp
      (tendsto_positiveTrace hW (by linarith : 0 < -y) hμneg)
    rw [sourceTrace, if_neg (by linarith : ¬0 ≤ y)]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    have h := sourceCompletion_conj hW (s := tracePoint x (-y)) (by simp; linarith)
    simpa only [Function.comp_apply, tracePoint_conj, neg_neg] using h.symm
  · simpa only [sourceTrace, if_pos hy.le] using tendsto_positiveTrace hW hy hμ

/-- The actual completed producer has a finite horizontal trace almost everywhere. -/
theorem tendsto_sourceTrace_ae {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ᵐ y : ℝ, Tendsto (fun x : ℝ => sourceCompletion hW (tracePoint x y))
      (𝓝[>] 0) (𝓝 (sourceTrace hW y)) := by
  haveI := sFinite_boundaryMeasure hW
  have hc : {y : ℝ | 0 < boundaryMeasure hW {y}}.Countable := by
    simpa using (Measure.countable_meas_level_set_pos (μ := boundaryMeasure hW)
      (g := fun r : ℝ => r) measurable_id)
  have hμ : ∀ᵐ y : ℝ, boundaryMeasure hW {y} = 0 := by
    rw [ae_iff]
    convert hc.measure_zero volume using 1
    congr 1
    ext y
    simp [pos_iff_ne_zero]
  have h0 : ∀ᵐ y : ℝ, y ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hμ, h0] with y hy hy0 using tendsto_sourceTrace_of_nonatom hW hy0 hy

/-- Exact reflection phase, with the central atom and diffuse mass retained. -/
theorem sourceTrace_reflection {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) :
    sourceTrace hW y =
      cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) *
        sourceTrace hW (-y) := by
  simp only [sourceTrace, if_pos hy.le, if_neg (by linarith : ¬0 ≤ -y), neg_neg,
    positiveTrace, map_mul, bigG_two_conj, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  rw [show (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) / 2 : ℝ) : ℂ) * -I) =
      -(((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) / 2 : ℝ) : ℂ) * I) by ring]
  set q : ℂ := (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) / 2 : ℝ) : ℂ) * I)
  have he : cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) *
      cexp (-q) = cexp q := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [q]
    push_cast
    ring
  calc bigG lam 2 * (traceModulus hW y : ℂ) * cexp q
      = bigG lam 2 * (traceModulus hW y : ℂ) *
          (cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) *
            cexp (-q)) := by rw [he]
    _ = _ := by ring

theorem continuous_sourceCompletion_slice {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) : Continuous fun y : ℝ => sourceCompletion hW (tracePoint x y) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  exact (hasDerivAt_sourceCompletion hW (s := tracePoint x y) (by simp; linarith)).continuousAt.comp
    (by unfold tracePoint; fun_prop)

theorem aestronglyMeasurable_sourceTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    AEStronglyMeasurable (sourceTrace hW) volume := by
  let F : ℝ → ℝ → ℂ := fun x y => if 0 < x then sourceCompletion hW (tracePoint x y) else 0
  have hF : ∀ x, AEStronglyMeasurable (F x) volume := by
    intro x
    by_cases hx : 0 < x
    · simpa only [F, if_pos hx] using (continuous_sourceCompletion_slice hW hx).aestronglyMeasurable
    · simp only [F, if_neg hx]
      exact aestronglyMeasurable_const
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ)) hF
  filter_upwards [tendsto_sourceTrace_ae hW] with y hy
  refine hy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp [F, hx]

theorem norm_sourceCompletion_le_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 3 / 2) (y : ℝ) :
    ‖sourceCompletion hW (tracePoint x y)‖ ≤
      ‖sourceCompletion hW (tracePoint (3 / 2) y)‖ := by
  simp only [sourceCompletion, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left
    (monotoneOn_exp_re_sourcePrimitive hW y hx (by norm_num) hx2) (norm_nonneg _)

theorem norm_sourceTrace_le_right_ae {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ᵐ y : ℝ, ‖sourceTrace hW y‖ ≤ ‖sourceCompletion hW (tracePoint (3 / 2) y)‖ := by
  filter_upwards [tendsto_sourceTrace_ae hW] with y hy
  apply le_of_tendsto hy.norm
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 2)).filter_mono nhdsWithin_le_nhds]
      with x (hx : 0 < x) hx2
  exact norm_sourceCompletion_le_right hW hx hx2.le y

/-- Horizontal convergence holds in L1 on every compact height interval, directly
from the original source. No boundary-continuity or atomicity premise occurs. -/
theorem tendsto_integral_norm_sourceTrace_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a b : ℝ) :
    Tendsto (fun x : ℝ => ∫ y in Icc a b,
      ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ᶠ x in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun y : ℝ => ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖)
      (volume.restrict (Icc a b)) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact ((continuous_sourceCompletion_slice hW hx).aestronglyMeasurable.sub
      (aestronglyMeasurable_sourceTrace hW)).norm.restrict
  have hbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂volume.restrict (Icc a b),
      ‖‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖‖ ≤
        2 * ‖sourceCompletion hW (tracePoint (3 / 2) y)‖ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 2)).filter_mono nhdsWithin_le_nhds]
        with x (hx : 0 < x) hx2
    filter_upwards [ae_restrict_of_ae (norm_sourceTrace_le_right_ae hW)] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by linarith [norm_sourceCompletion_le_right hW hx hx2.le y])
  have hint : IntegrableOn (fun y : ℝ =>
      2 * ‖sourceCompletion hW (tracePoint (3 / 2) y)‖) (Icc a b) :=
    (continuous_sourceCompletion_slice hW (by norm_num : (0 : ℝ) < 3 / 2)).norm.integrableOn_Icc.const_mul 2
  have hlim : ∀ᵐ y ∂volume.restrict (Icc a b),
      Tendsto (fun x : ℝ => ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖)
        (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae (tendsto_sourceTrace_ae hW)] with y hy
    have hc : Tendsto (fun _ : ℝ => sourceTrace hW y) (𝓝[>] (0 : ℝ))
        (𝓝 (sourceTrace hW y)) := tendsto_const_nhds
    simpa using (hy.sub hc).norm
  simpa using tendsto_integral_filter_of_dominated_convergence
    (fun y => 2 * ‖sourceCompletion hW (tracePoint (3 / 2) y)‖) hmeas hbound hint hlim

theorem integrable_sourceCompletion_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (fun y : ℝ => sourceCompletion hW (tracePoint (3 / 2) y)) := by
  obtain ⟨C, N, hC, hB⟩ := FractionalMassRigidity.exists_bound_bigG_two
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ)
  obtain ⟨K, _, hK⟩ := exists_bound_pow_mul_exp_neg (N + 2)
  refine (integrable_inv_one_add_sq.const_mul (C * K)).mono'
    (continuous_sourceCompletion_slice hW (by norm_num : (0 : ℝ) < 3 / 2)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => by
    have he : tracePoint (3 / 2) y = 2 + (y : ℂ) * I := by norm_num [tracePoint]
    rw [he, sourceCompletion_eq_bigG hW (by simp)]
    have hb := (hB y).trans
      (mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_div hK (abs_nonneg y)) hC)
    simpa only [sq_abs, div_eq_mul_inv, mul_assoc] using hb

theorem integrable_sourceTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (sourceTrace hW) :=
  (integrable_sourceCompletion_right hW).norm.mono'
    (aestronglyMeasurable_sourceTrace hW) (norm_sourceTrace_le_right_ae hW)

theorem integrable_sourceCompletion_slice {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 3 / 2) :
    Integrable (fun y : ℝ => sourceCompletion hW (tracePoint x y)) :=
  (integrable_sourceCompletion_right hW).norm.mono'
    (continuous_sourceCompletion_slice hW hx).aestronglyMeasurable
    (Eventually.of_forall (norm_sourceCompletion_le_right hW hx hx2))

/-- Global L1 convergence of the actual producer to its canonical trace. The
right-edge Gamma decay supplies an integrable bound over all heights. -/
theorem tendsto_integral_norm_sourceTrace_sub_global {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => ∫ y : ℝ,
      ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ᶠ x in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun y : ℝ => ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖) := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact ((continuous_sourceCompletion_slice hW hx).aestronglyMeasurable.sub
      (aestronglyMeasurable_sourceTrace hW)).norm
  have hbound : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ᵐ y : ℝ,
      ‖‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖‖ ≤
        2 * ‖sourceCompletion hW (tracePoint (3 / 2) y)‖ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 2)).filter_mono nhdsWithin_le_nhds]
        with x (hx : 0 < x) hx2
    filter_upwards [norm_sourceTrace_le_right_ae hW] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by linarith [norm_sourceCompletion_le_right hW hx hx2.le y])
  have hlim : ∀ᵐ y : ℝ,
      Tendsto (fun x : ℝ => ‖sourceCompletion hW (tracePoint x y) - sourceTrace hW y‖)
        (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [tendsto_sourceTrace_ae hW] with y hy
    have hc : Tendsto (fun _ : ℝ => sourceTrace hW y) (𝓝[>] (0 : ℝ))
        (𝓝 (sourceTrace hW y)) := tendsto_const_nhds
    simpa using (hy.sub hc).norm
  simpa using tendsto_integral_filter_of_dominated_convergence
    (fun y => 2 * ‖sourceCompletion hW (tracePoint (3 / 2) y)‖) hmeas hbound
    ((integrable_sourceCompletion_right hW).norm.const_mul 2) hlim

end RHTower.WeilWorkSettledPhase
