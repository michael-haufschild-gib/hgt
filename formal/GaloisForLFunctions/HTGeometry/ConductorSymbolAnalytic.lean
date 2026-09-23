import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The conductor symbol is an analytic symbol up to a bounded error

Stirling's formula gives the real-place conductor symbol as `log(2 + |ξ|)` up to a bounded error.
That symbol is not itself a boundary value of a function analytic in a half plane, but it differs
from one by a bounded function:

`log(2 + |ξ|) − Re Log(2 + iξ) ∈ [0, ½ log 2]`,

because `(2+|ξ|)²/(4+ξ²) = 1 + 4|ξ|/(4+ξ²) ∈ [1,2]`.  Since `2 + iξ` has positive real part, the
principal branch never meets the cut, and `2 + iz` is nonvanishing on `Im z > −2`, so `Log(2+iz)`
is analytic on a half plane containing the real axis.

A bounded symbol has a bounded commutator with any projection, so only the analytic part carries
the commutator, and its Hankel kernel is the one bounded in `ConductorHankelBound`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real-place conductor symbol, in its Stirling normal form. -/
def conductorSymbol (ξ : ℝ) : ℝ := Real.log (2 + |ξ|)

/-- The analytic symbol whose real part carries the conductor singularity. -/
def conductorAnalytic (ξ : ℝ) : ℂ := Complex.log (2 + Complex.I * ξ)

theorem conductorAnalytic_ne_zero (ξ : ℝ) : (2 : ℂ) + Complex.I * ξ ≠ 0 := by
  intro h
  have hre : ((2 : ℂ) + Complex.I * ξ).re = 0 := by rw [h]; simp
  simp at hre

theorem norm_two_add_I_mul (ξ : ℝ) : ‖(2 : ℂ) + Complex.I * ξ‖ = Real.sqrt (4 + ξ ^ (2 : ℕ)) := by
  have hre : ((2 : ℂ) + Complex.I * ξ).re = 2 := by simp
  have him : ((2 : ℂ) + Complex.I * ξ).im = ξ := by simp
  rw [Complex.norm_def, Complex.normSq_apply, hre, him]
  congr 1
  ring

theorem conductorAnalytic_re (ξ : ℝ) :
    (conductorAnalytic ξ).re = Real.log (Real.sqrt (4 + ξ ^ (2 : ℕ))) := by
  rw [conductorAnalytic, Complex.log_re, norm_two_add_I_mul]

/-! ## The bounded difference -/

theorem sq_bounds (ξ : ℝ) :
    4 + ξ ^ (2 : ℕ) ≤ (2 + |ξ|) ^ (2 : ℕ) ∧ (2 + |ξ|) ^ (2 : ℕ) ≤ 2 * (4 + ξ ^ (2 : ℕ)) := by
  have habs : |ξ| ^ (2 : ℕ) = ξ ^ (2 : ℕ) := sq_abs ξ
  have hnn : 0 ≤ |ξ| := abs_nonneg ξ
  constructor
  · nlinarith [habs, hnn]
  · nlinarith [habs, hnn, sq_nonneg (|ξ| - 2)]

theorem conductorSymbol_sub_analytic_nonneg (ξ : ℝ) :
    0 ≤ conductorSymbol ξ - (conductorAnalytic ξ).re := by
  have hpos : (0 : ℝ) < 4 + ξ ^ (2 : ℕ) := by positivity
  have hsq := (sq_bounds ξ).1
  have hs : Real.sqrt (4 + ξ ^ (2 : ℕ)) ≤ 2 + |ξ| := by
    rw [show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ (2 : ℕ)) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq
  have hspos : (0 : ℝ) < Real.sqrt (4 + ξ ^ (2 : ℕ)) := Real.sqrt_pos.mpr hpos
  rw [conductorSymbol, conductorAnalytic_re, sub_nonneg]
  exact Real.log_le_log hspos hs

theorem conductorSymbol_sub_analytic_le (ξ : ℝ) :
    conductorSymbol ξ - (conductorAnalytic ξ).re ≤ Real.log 2 / 2 := by
  have hpos : (0 : ℝ) < 4 + ξ ^ (2 : ℕ) := by positivity
  have hsq := (sq_bounds ξ).2
  have hspos : (0 : ℝ) < Real.sqrt (4 + ξ ^ (2 : ℕ)) := Real.sqrt_pos.mpr hpos
  have hs : (2 : ℝ) + |ξ| ≤ Real.sqrt 2 * Real.sqrt (4 + ξ ^ (2 : ℕ)) := by
    rw [← Real.sqrt_mul (by norm_num) (4 + ξ ^ (2 : ℕ)),
      show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ (2 : ℕ)) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : Real.log (2 + |ξ|) ≤ Real.log (Real.sqrt 2) + Real.log (Real.sqrt (4 + ξ ^ (2 : ℕ))) := by
    have h1 : Real.log (2 + |ξ|) ≤ Real.log (Real.sqrt 2 * Real.sqrt (4 + ξ ^ (2 : ℕ))) :=
      Real.log_le_log (by positivity) hs
    rwa [Real.log_mul (ne_of_gt hsqrt2) (ne_of_gt hspos)] at h1
  have hval : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hlog := Real.log_mul (ne_of_gt hsqrt2) (ne_of_gt hsqrt2)
    rw [h2] at hlog
    linarith
  rw [conductorSymbol, conductorAnalytic_re]
  rw [hval] at hlog
  linarith

/-- **The conductor symbol is analytic up to a bounded error.** -/
theorem abs_conductorSymbol_sub_analytic_le (ξ : ℝ) :
    |conductorSymbol ξ - (conductorAnalytic ξ).re| ≤ Real.log 2 / 2 := by
  rw [abs_le]
  have h1 := conductorSymbol_sub_analytic_nonneg ξ
  have h2 := conductorSymbol_sub_analytic_le ξ
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  constructor <;> linarith

/-! ## The resolvent representation -/

theorem mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl hz)

/-- The resolvent primitive of the conductor symbol. -/
def conductorResolventPrimitive (ξ : ℝ) (lam : ℝ) : ℂ :=
  Complex.log ((lam : ℂ) + 2) - Complex.log ((lam : ℂ) + 2 + Complex.I * ξ)

theorem hasDerivAt_conductorResolventPrimitive (ξ : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasDerivAt (conductorResolventPrimitive ξ)
      (1 / ((lam : ℂ) + 2) - 1 / ((lam : ℂ) + 2 + Complex.I * ξ)) lam := by
  have hre1 : (0 : ℝ) < ((lam : ℂ) + 2).re := by simp; linarith
  have hre2 : (0 : ℝ) < ((lam : ℂ) + 2 + Complex.I * ξ).re := by simp; linarith
  have hd1 : HasDerivAt (fun m : ℝ => Complex.log ((m : ℂ) + 2))
      (((lam : ℂ) + 2)⁻¹) lam := by
    have hz := (Complex.hasDerivAt_log (mem_slitPlane_of_re_pos hre1))
    have hin : HasDerivAt (fun z : ℂ => z + 2) 1 ((lam : ℂ)) := (hasDerivAt_id _).add_const 2
    have := (hz.comp (lam : ℂ) hin)
    simpa using this.comp_ofReal
  have hd2 : HasDerivAt (fun m : ℝ => Complex.log ((m : ℂ) + 2 + Complex.I * ξ))
      (((lam : ℂ) + 2 + Complex.I * ξ)⁻¹) lam := by
    have hz := (Complex.hasDerivAt_log (mem_slitPlane_of_re_pos hre2))
    have hin : HasDerivAt (fun z : ℂ => z + 2 + Complex.I * ξ) 1 ((lam : ℂ)) :=
      ((hasDerivAt_id _).add_const 2).add_const _
    have := (hz.comp (lam : ℂ) hin)
    simpa using this.comp_ofReal
  have := hd1.sub hd2
  refine this.congr_deriv ?_
  rw [one_div, one_div]

theorem tendsto_norm_shift (ξ : ℝ) :
    Tendsto (fun lam : ℝ => ‖(lam : ℂ) + 2 + Complex.I * ξ‖) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam _
  have hre : ((lam : ℂ) + 2 + Complex.I * ξ).re = lam + 2 := by simp
  calc lam + 2 = ((lam : ℂ) + 2 + Complex.I * ξ).re := hre.symm
    _ ≤ ‖(lam : ℂ) + 2 + Complex.I * ξ‖ := Complex.re_le_norm _

theorem tendsto_conductorResolventPrimitive (ξ : ℝ) :
    Tendsto (conductorResolventPrimitive ξ) atTop (𝓝 0) := by
  have hnorm := tendsto_norm_shift ξ
  -- the imaginary part
  have him : Tendsto (fun lam : ℝ => (conductorResolventPrimitive ξ lam).im) atTop (𝓝 0) := by
    have harc : Tendsto (fun lam : ℝ =>
        Real.arcsin (((lam : ℂ) + 2 + Complex.I * ξ).im / ‖(lam : ℂ) + 2 + Complex.I * ξ‖))
        atTop (𝓝 0) := by
      have hquot : Tendsto (fun lam : ℝ =>
          ((lam : ℂ) + 2 + Complex.I * ξ).im / ‖(lam : ℂ) + 2 + Complex.I * ξ‖) atTop (𝓝 0) := by
        have hconst : ∀ lam : ℝ, ((lam : ℂ) + 2 + Complex.I * ξ).im = ξ := by
          intro lam; simp
        simp only [hconst]
        exact Tendsto.div_atTop tendsto_const_nhds hnorm
      have hcont : ContinuousAt Real.arcsin 0 := Real.continuous_arcsin.continuousAt
      have := hcont.tendsto.comp hquot
      simpa [Function.comp_def] using this
    refine Tendsto.congr' ?_ (by simpa using harc.neg)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    have hre1 : (0 : ℝ) ≤ ((lam : ℂ) + 2).re := by simp; linarith
    have hre2 : (0 : ℝ) ≤ ((lam : ℂ) + 2 + Complex.I * ξ).re := by simp; linarith
    have hz1 : ((lam : ℂ) + 2).im = 0 := by simp
    rw [conductorResolventPrimitive, Complex.sub_im, Complex.log_im, Complex.log_im,
      Complex.arg, if_pos hre1, Complex.arg, if_pos hre2, hz1]
    simp
  -- the real part
  have hre : Tendsto (fun lam : ℝ => (conductorResolventPrimitive ξ lam).re) atTop (𝓝 0) := by
    have hratio : Tendsto (fun lam : ℝ => (lam + 2) / ‖(lam : ℂ) + 2 + Complex.I * ξ‖)
        atTop (𝓝 1) := by
      have hsq : ∀ lam : ℝ, 0 < lam →
          (lam + 2) / ‖(lam : ℂ) + 2 + Complex.I * ξ‖
            = 1 / Real.sqrt (1 + (ξ / (lam + 2)) ^ (2 : ℕ)) := by
        intro lam hlam
        have hl2 : (0 : ℝ) < lam + 2 := by linarith
        have hnn : ‖(lam : ℂ) + 2 + Complex.I * ξ‖ = Real.sqrt ((lam + 2) ^ (2 : ℕ) + ξ ^ (2 : ℕ)) := by
          rw [Complex.norm_def, Complex.normSq_apply]
          congr 1
          simp
          ring
        rw [hnn]
        have hfac : (lam + 2) ^ (2 : ℕ) + ξ ^ (2 : ℕ) = (lam + 2) ^ (2 : ℕ) * (1 + (ξ / (lam + 2)) ^ (2 : ℕ)) := by
          field_simp
        rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq hl2.le]
        field_simp
      have hinner : Tendsto (fun lam : ℝ => 1 + (ξ / (lam + 2)) ^ (2 : ℕ)) atTop (𝓝 1) := by
        have hd : Tendsto (fun lam : ℝ => ξ / (lam + 2)) atTop (𝓝 0) :=
          Tendsto.div_atTop tendsto_const_nhds
            (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)
        simpa using (tendsto_const_nhds (x := (1:ℝ))).add (hd.pow 2)
      have hsqrt : Tendsto (fun lam : ℝ => Real.sqrt (1 + (ξ / (lam + 2)) ^ (2 : ℕ))) atTop (𝓝 1) := by
        have := (Real.continuous_sqrt.continuousAt (x := (1:ℝ))).tendsto.comp hinner
        simpa [Function.comp_def] using this
      have hinv : Tendsto (fun lam : ℝ => 1 / Real.sqrt (1 + (ξ / (lam + 2)) ^ (2 : ℕ))) atTop (𝓝 1) := by
        simpa using hsqrt.inv₀ (by norm_num)
      refine Tendsto.congr' ?_ hinv
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
      exact (hsq lam hlam).symm
    have hlog : Tendsto (fun lam : ℝ =>
        Real.log ((lam + 2) / ‖(lam : ℂ) + 2 + Complex.I * ξ‖)) atTop (𝓝 0) := by
      have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
      have := hcont.tendsto.comp hratio
      simpa [Function.comp_def] using this
    refine Tendsto.congr' ?_ hlog
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    have hl2 : (0 : ℝ) < lam + 2 := by linarith
    have hnpos : (0 : ℝ) < ‖(lam : ℂ) + 2 + Complex.I * ξ‖ := by
      refine norm_pos_iff.mpr ?_
      intro h
      have : ((lam : ℂ) + 2 + Complex.I * ξ).re = 0 := by rw [h]; simp
      simp at this
      linarith
    have hn1 : ‖(lam : ℂ) + 2‖ = lam + 2 := by
      rw [show ((lam : ℂ) + 2) = ((lam + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hl2.le]
    rw [conductorResolventPrimitive, Complex.sub_re, Complex.log_re, Complex.log_re, hn1,
      Real.log_div (ne_of_gt hl2) (ne_of_gt hnpos)]
  refine squeeze_zero_norm' ?_
    (?_ : Tendsto (fun lam : ℝ => |(conductorResolventPrimitive ξ lam).re|
      + |(conductorResolventPrimitive ξ lam).im|) atTop (𝓝 0))
  · filter_upwards with lam
    exact Complex.norm_le_abs_re_add_abs_im _
  · simpa using (hre.abs).add (him.abs)

/-- **The resolvent representation of the conductor symbol.** -/
theorem conductorAnalytic_eq_resolvent (ξ : ℝ) :
    conductorAnalytic ξ - (Real.log 2 : ℂ)
      = ∫ lam in Set.Ioi (0:ℝ),
          (1 / ((lam : ℂ) + 2) - 1 / ((lam : ℂ) + 2 + Complex.I * ξ)) := by
  have hint : IntegrableOn
      (fun lam : ℝ => 1 / ((lam : ℂ) + 2) - 1 / ((lam : ℂ) + 2 + Complex.I * ξ))
      (Set.Ioi 0) volume := by
    have hmajor : IntegrableOn (fun lam : ℝ => |ξ| * ((lam + 2) ^ (2 : ℕ))⁻¹)
        (Set.Ioi (0:ℝ)) volume := by
      have hb : IntegrableOn (fun lam : ℝ => ((lam + 2) ^ (2 : ℕ))⁻¹) (Set.Ioi (0:ℝ)) volume := by
        refine integrableOn_Ioi_deriv_of_nonneg (g := fun m : ℝ => -(m + 2)⁻¹) (l := 0)
          ?_ ?_ ?_ ?_
        · refine ContinuousAt.continuousWithinAt ?_
          exact ((continuousAt_id.add continuousAt_const).inv₀ (by norm_num)).neg
        · intro m hm
          have hm2 : (m : ℝ) + 2 ≠ 0 := by
            have : (0 : ℝ) < m := hm
            linarith
          have h := ((hasDerivAt_id m).add_const (2 : ℝ)).inv hm2
          have h2 := h.neg
          refine h2.congr_deriv ?_
          simp only [id_eq]
          field_simp
        · intro m hm
          positivity
        · have hd : Tendsto (fun m : ℝ => (m + 2)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_id)
          simpa using hd.neg
      exact hb.const_mul _
    refine Integrable.mono' hmajor ?_ ?_
    · refine (Measurable.sub ?_ ?_).aestronglyMeasurable.restrict
      · exact (measurable_const.div ((Complex.measurable_ofReal).add measurable_const))
      · exact (measurable_const.div
          (((Complex.measurable_ofReal).add measurable_const).add measurable_const))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with lam hlam
      have hlam0 : (0 : ℝ) < lam := hlam
      have hl2 : (0 : ℝ) < lam + 2 := by linarith
      have hne1 : ((lam : ℂ) + 2) ≠ 0 := by
        intro h
        have : ((lam : ℂ) + 2).re = 0 := by rw [h]; simp
        simp at this; linarith
      have hne2 : ((lam : ℂ) + 2 + Complex.I * ξ) ≠ 0 := by
        intro h
        have : ((lam : ℂ) + 2 + Complex.I * ξ).re = 0 := by rw [h]; simp
        simp at this; linarith
      have hdiff : 1 / ((lam : ℂ) + 2) - 1 / ((lam : ℂ) + 2 + Complex.I * ξ)
          = (Complex.I * ξ) / (((lam : ℂ) + 2) * ((lam : ℂ) + 2 + Complex.I * ξ)) := by
        field_simp
        ring
      rw [hdiff, norm_div, norm_mul, norm_mul]
      have hn1 : ‖(lam : ℂ) + 2‖ = lam + 2 := by
        rw [show ((lam : ℂ) + 2) = ((lam + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg hl2.le]
      have hn2 : (lam + 2) ≤ ‖(lam : ℂ) + 2 + Complex.I * ξ‖ := by
        have hre : ((lam : ℂ) + 2 + Complex.I * ξ).re = lam + 2 := by simp
        calc lam + 2 = ((lam : ℂ) + 2 + Complex.I * ξ).re := hre.symm
          _ ≤ _ := Complex.re_le_norm _
      rw [hn1, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [div_le_iff₀ (by positivity)]
      have hstep : (lam + 2) * (lam + 2) ≤ (lam + 2) * ‖(lam : ℂ) + 2 + Complex.I * ξ‖ :=
        mul_le_mul_of_nonneg_left hn2 hl2.le
      have hmul : |ξ| * ((lam + 2) * (lam + 2))
          ≤ |ξ| * ((lam + 2) * ‖(lam : ℂ) + 2 + Complex.I * ξ‖) :=
        mul_le_mul_of_nonneg_left hstep (abs_nonneg ξ)
      have hinv : (0 : ℝ) < ((lam + 2) ^ (2 : ℕ))⁻¹ := by positivity
      calc |ξ| = |ξ| * ((lam + 2) * (lam + 2)) * ((lam + 2) ^ (2 : ℕ))⁻¹ := by
            field_simp
        _ ≤ |ξ| * ((lam + 2) * ‖(lam : ℂ) + 2 + Complex.I * ξ‖) * ((lam + 2) ^ (2 : ℕ))⁻¹ :=
            mul_le_mul_of_nonneg_right hmul hinv.le
        _ = |ξ| * ((lam + 2) ^ (2 : ℕ))⁻¹ * ((lam + 2) * ‖(lam : ℂ) + 2 + Complex.I * ξ‖) := by ring
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := conductorResolventPrimitive ξ)
    (f' := fun lam : ℝ => 1 / ((lam : ℂ) + 2) - 1 / ((lam : ℂ) + 2 + Complex.I * ξ))
    ((hasDerivAt_conductorResolventPrimitive ξ le_rfl).continuousAt.continuousWithinAt)
    (fun lam hlam => hasDerivAt_conductorResolventPrimitive ξ (le_of_lt hlam))
    hint (tendsto_conductorResolventPrimitive ξ)
  rw [hval, conductorResolventPrimitive]
  have hlog2 : Complex.log ((0 : ℝ) + 2 : ℂ) = (Real.log 2 : ℂ) := by
    rw [show ((0 : ℝ) : ℂ) + 2 = ((2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by norm_num)]
  have hcond : Complex.log (((0 : ℝ) : ℂ) + 2 + Complex.I * ξ) = conductorAnalytic ξ := by
    rw [conductorAnalytic]
    congr 1
    push_cast
    ring
  rw [hlog2, hcond]
  ring

end

end GaloisForLFunctions.HTGeometry
