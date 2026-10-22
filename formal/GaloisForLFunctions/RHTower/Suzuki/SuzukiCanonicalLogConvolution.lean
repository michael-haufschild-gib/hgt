import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalLogKernelW1One
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Differentiating Suzuki's logarithmic cusp convolution

This module supplies the analytic step missing from the printed proof of Suzuki (2012), Lemma
`lem_ad1`.  It does not assume a pointwise dominator for moving cusp derivatives.  Instead it uses
the exact local fundamental theorem for the kernel, Fubini, and dominated convergence after moving
translation onto a bounded profile with at most one jump.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Additive convolution in the orientation arising from `xy = exp (log x + log y)`. -/
def suzukiLogConvolution (W H : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t : ℝ, W t * H (s - t)

/-- A translated product with an `L¹` field is continuously integrable when the other factor is
bounded and continuous away from one point.  This is the exact continuity mechanism needed for
the derivative convolution; the exceptional translated point is null. -/
theorem continuous_suzukiLogConvolution_of_integrable_right
    {W D : ℝ → ℂ} {c C : ℝ}
    (hD : Integrable D) (hWmeas : Measurable W)
    (hWbound : ∀ t, ‖W t‖ ≤ C)
    (hWcont : ∀ t, t ≠ c → ContinuousAt W t) :
    Continuous (suzukiLogConvolution W D) := by
  let alt : ℝ → ℂ := fun s => ∫ v : ℝ, D v * W (s - v)
  have halt : Continuous alt := by
    rw [continuous_iff_continuousAt]
    intro s₀
    apply MeasureTheory.continuousAt_of_dominated
        (bound := fun v => C * ‖D v‖)
    · exact Eventually.of_forall fun s =>
        hD.aestronglyMeasurable.mul
          ((hWmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    · exact Eventually.of_forall fun s => Eventually.of_forall fun v => by
        rw [norm_mul]
        calc
          ‖D v‖ * ‖W (s - v)‖ ≤ ‖D v‖ * C :=
            mul_le_mul_of_nonneg_left (hWbound _) (norm_nonneg _)
          _ = C * ‖D v‖ := mul_comm _ _
    · simpa only [mul_comm] using hD.norm.const_mul C
    · filter_upwards [volume.ae_ne (s₀ - c)] with v hv
      have harg : s₀ - v ≠ c := by
        intro h
        apply hv
        linarith
      have haff : ContinuousAt (fun s : ℝ => s - v) s₀ :=
        continuousAt_id.sub continuousAt_const
      exact continuousAt_const.mul
        ((hWcont (s₀ - v) harg).comp_of_eq haff rfl)
  have heq : suzukiLogConvolution W D = alt := by
    funext s
    rw [suzukiLogConvolution]
    have hchange := MeasureTheory.integral_sub_left_eq_self
      (fun v : ℝ => W (s - v) * D v) volume s
    rw [show (∫ t : ℝ, W t * D (s - t)) =
        ∫ v : ℝ, W (s - v) * D v by
      simpa only [sub_sub_cancel] using hchange]
    apply integral_congr_ae
    filter_upwards with v
    rw [mul_comm]
  rw [heq]
  exact halt

/-- Fubini plus the kernel FTC: convolution increments equal the integral of the derivative
convolution.  The profile is only required to vanish below `-c`; no differentiability of the
profile is used. -/
theorem suzukiLogConvolution_sub_eq_integral
    {W H D : ℝ → ℂ} {B c p q : ℝ}
    (hW : Integrable W) (hD : Integrable D)
    (hWH : ∀ s, Integrable (fun t => W t * H (s - t)))
    (hWzero : ∀ t, t < -c → W t = 0)
    (hFTC : ∀ u v, u < B → v < B →
      (∫ r in u..v, D r) = H v - H u)
    (hpB : p + c < B) (hqB : q + c < B) :
    suzukiLogConvolution W H q - suzukiLogConvolution W H p =
      ∫ s in p..q, suzukiLogConvolution W D s := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  have hprodFull : Integrable
      (fun z : ℝ × ℝ => W z.2 * D (z.1 - z.2)) (volume.prod volume) := by
    have h := hW.convolution_integrand L hD
    change Integrable
      (fun z : ℝ × ℝ => W z.2 * D (z.1 - z.2)) (volume.prod volume) at h
    exact h
  have hprod : Integrable
      (Function.uncurry fun s t : ℝ => W t * D (s - t))
      ((volume.restrict (uIoc p q)).prod volume) := by
    apply hprodFull.mono_measure
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  calc
    suzukiLogConvolution W H q - suzukiLogConvolution W H p =
        ∫ t : ℝ, W t * H (q - t) - W t * H (p - t) := by
      rw [suzukiLogConvolution, suzukiLogConvolution,
        integral_sub (hWH q) (hWH p)]
    _ = ∫ t : ℝ, (∫ s in p..q, W t * D (s - t)) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases hWt : W t = 0
      · simp [hWt]
      · have ht : -c ≤ t := by
          by_contra h
          exact hWt (hWzero t (lt_of_not_ge h))
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right,
          hFTC (p - t) (q - t)]
        · ring
        · linarith
        · linarith
    _ = ∫ s in p..q, ∫ t : ℝ, W t * D (s - t) := by
      exact (MeasureTheory.intervalIntegral_integral_swap hprod).symm
    _ = ∫ s in p..q, suzukiLogConvolution W D s := by
      rfl

/-- If the derivative convolution is continuous, the preceding increment identity upgrades the
kernel convolution to a genuine continuously differentiable function. -/
theorem hasDerivAt_suzukiLogConvolution
    {W H D : ℝ → ℂ} {B c x : ℝ}
    (hW : Integrable W) (hD : Integrable D)
    (hWH : ∀ s, Integrable (fun t => W t * H (s - t)))
    (hWzero : ∀ t, t < -c → W t = 0)
    (hFTC : ∀ u v, u < B → v < B →
      (∫ r in u..v, D r) = H v - H u)
    (hJ : Continuous (suzukiLogConvolution W D))
    (hxB : x + c < B) :
    HasDerivAt (suzukiLogConvolution W H)
      (suzukiLogConvolution W D x) x := by
  let J := suzukiLogConvolution W D
  let P : ℝ → ℂ := fun s => suzukiLogConvolution W H x + ∫ u in x..s, J u
  have hP : HasDerivAt P (J x) x := by
    have hprim := intervalIntegral.integral_hasDerivAt_right
      (hJ.intervalIntegrable x x)
      (hJ.stronglyMeasurableAtFilter volume (nhds x)) hJ.continuousAt
    exact hprim.const_add _
  have hev : suzukiLogConvolution W H =ᶠ[nhds x] P := by
    have hnhds : Iio (B - c) ∈ nhds x := Iio_mem_nhds (by linarith)
    filter_upwards [hnhds] with s hs
    have hsB : s + c < B := by
      change s < B - c at hs
      linarith
    have hinc := suzukiLogConvolution_sub_eq_integral hW hD hWH hWzero hFTC
      (p := x) (q := s) hxB hsB
    dsimp only [P, J]
    calc
      suzukiLogConvolution W H s =
          (∫ u in x..s, suzukiLogConvolution W D u) +
            suzukiLogConvolution W H x := (sub_eq_iff_eq_add).mp hinc
      _ = suzukiLogConvolution W H x +
          ∫ u in x..s, suzukiLogConvolution W D u := add_comm _ _
  exact hP.congr_of_eventuallyEq hev

/-- The convolution is genuinely `C¹` below the FTC horizon, not merely pointwise
differentiable.  Continuity of its derivative is exactly `hJ`. -/
theorem contDiffAt_one_suzukiLogConvolution
    {W H D : ℝ → ℂ} {B c x : ℝ}
    (hW : Integrable W) (hD : Integrable D)
    (hWH : ∀ s, Integrable (fun t => W t * H (s - t)))
    (hWzero : ∀ t, t < -c → W t = 0)
    (hFTC : ∀ u v, u < B → v < B →
      (∫ r in u..v, D r) = H v - H u)
    (hJ : Continuous (suzukiLogConvolution W D))
    (hxB : x + c < B) :
    ContDiffAt ℝ 1 (suzukiLogConvolution W H) x := by
  rw [contDiffAt_one_iff]
  refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ
      (suzukiLogConvolution W D s), Iio (B - c),
    Iio_mem_nhds (by linarith), ?_, ?_⟩
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
        ℂ ≃L[ℝ] ℝ →L[ℝ] ℂ).continuous.comp hJ).continuousOn
  · intro s hs
    exact (hasDerivAt_suzukiLogConvolution hW hD hWH hWzero hFTC hJ
      (by change s < B - c at hs; linarith)).hasFDerivAt

/-- Zero extension of a continuous function on `[0,a]`, expressed through the continuous nearest
point projection so measurability is explicit. -/
def suzukiClosedIntervalZeroExtension
    (a : ℝ) (ha : 0 ≤ a) (phi : C(ClosedInterval 0 a, ℂ)) (y : ℝ) : ℂ :=
  (Icc 0 a).indicator (fun z => phi (Set.projIcc 0 a ha z)) y

theorem suzukiClosedIntervalZeroExtension_apply_of_mem
    {a : ℝ} (ha : 0 ≤ a) (phi : C(ClosedInterval 0 a, ℂ))
    {y : ℝ} (hy : y ∈ Icc 0 a) :
    suzukiClosedIntervalZeroExtension a ha phi y = phi ⟨y, hy⟩ := by
  rw [suzukiClosedIntervalZeroExtension, Set.indicator_of_mem hy,
    Set.projIcc_of_mem ha hy]

theorem measurable_suzukiClosedIntervalZeroExtension
    {a : ℝ} (ha : 0 ≤ a) (phi : C(ClosedInterval 0 a, ℂ)) :
    Measurable (suzukiClosedIntervalZeroExtension a ha phi) := by
  unfold suzukiClosedIntervalZeroExtension
  exact (phi.continuous.measurable.comp continuous_projIcc.measurable).indicator measurableSet_Icc

/-- Reflected logarithmic profile corresponding to `phi(y) dy` under `y = exp(-t)`. -/
def suzukiReflectedLogProfile
    (a : ℝ) (ha : 0 ≤ a) (phi : C(ClosedInterval 0 a, ℂ)) (t : ℝ) : ℂ :=
  ((Real.exp (-t) : ℝ) : ℂ) *
    suzukiClosedIntervalZeroExtension a ha phi (Real.exp (-t))

theorem measurable_suzukiReflectedLogProfile
    {a : ℝ} (ha : 0 ≤ a) (phi : C(ClosedInterval 0 a, ℂ)) :
    Measurable (suzukiReflectedLogProfile a ha phi) := by
  unfold suzukiReflectedLogProfile
  exact (Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul
    ((measurable_suzukiClosedIntervalZeroExtension ha phi).comp (by fun_prop))

theorem suzukiReflectedLogProfile_eq_zero_of_lt_neg_log
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ))
    {t : ℝ} (ht : t < -Real.log a) :
    suzukiReflectedLogProfile a ha.le phi t = 0 := by
  have harg : a < Real.exp (-t) := by
    rw [← Real.exp_log ha]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [suzukiReflectedLogProfile, suzukiClosedIntervalZeroExtension,
    Set.indicator_of_notMem (fun h => (not_le_of_gt harg) h.2)]
  ring

theorem norm_suzukiReflectedLogProfile_le
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ)) (t : ℝ) :
    ‖suzukiReflectedLogProfile a ha.le phi t‖ ≤ a * ‖phi‖ := by
  by_cases ht : t < -Real.log a
  · rw [suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi ht, norm_zero]
    positivity
  · have hargPos : 0 < Real.exp (-t) := Real.exp_pos _
    have hargLe : Real.exp (-t) ≤ a := by
      rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [suzukiReflectedLogProfile,
      suzukiClosedIntervalZeroExtension_apply_of_mem ha.le phi ⟨hargPos.le, hargLe⟩,
      norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg hargPos.le]
    calc
      Real.exp (-t) * ‖phi ⟨Real.exp (-t), ⟨hargPos.le, hargLe⟩⟩‖ ≤
          Real.exp (-t) * ‖phi‖ :=
        mul_le_mul_of_nonneg_left (phi.norm_coe_le_norm _) hargPos.le
      _ ≤ a * ‖phi‖ := mul_le_mul_of_nonneg_right hargLe (norm_nonneg _)

theorem continuousAt_suzukiReflectedLogProfile_of_ne_neg_log
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ))
    {t : ℝ} (ht : t ≠ -Real.log a) :
    ContinuousAt (suzukiReflectedLogProfile a ha.le phi) t := by
  let base : ℝ → ℂ := fun u =>
    ((Real.exp (-u) : ℝ) : ℂ) * phi (Set.projIcc 0 a ha.le (Real.exp (-u)))
  have hbase : Continuous base := by
    dsimp only [base]
    fun_prop
  rcases lt_or_gt_of_ne ht with htlt | htgt
  · have hev : suzukiReflectedLogProfile a ha.le phi =ᶠ[nhds t] fun _ => 0 := by
      have harg : a < Real.exp (-t) := by
        rw [← Real.exp_log ha]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hevent : ∀ᶠ u in nhds t, a < Real.exp (-u) :=
        (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))).continuousAt.eventually
          (Ioi_mem_nhds harg)
      filter_upwards [hevent] with u hu
      exact suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi (by
        rw [← Real.exp_log ha] at hu
        have hlog := Real.exp_lt_exp.mp hu
        linarith)
    exact continuousAt_const.congr_of_eventuallyEq hev
  · have hev : suzukiReflectedLogProfile a ha.le phi =ᶠ[nhds t] base := by
      have harg : Real.exp (-t) < a := by
        rw [← Real.exp_log ha]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hevent : ∀ᶠ u in nhds t, Real.exp (-u) < a :=
        (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))).continuousAt.eventually
          (Iio_mem_nhds harg)
      filter_upwards [hevent] with u hu
      rw [suzukiReflectedLogProfile,
        suzukiClosedIntervalZeroExtension_apply_of_mem ha.le phi
          ⟨(Real.exp_pos _).le, hu.le⟩]
      dsimp only [base]
      rw [Set.projIcc_of_mem ha.le ⟨(Real.exp_pos _).le, hu.le⟩]
    exact hbase.continuousAt.congr_of_eventuallyEq hev

/-- The reflected logarithmic profile is globally integrable; exponential Jacobian decay is the
integrable majorant. -/
theorem integrable_suzukiReflectedLogProfile
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ)) :
    Integrable (suzukiReflectedLogProfile a ha.le phi) := by
  let c := -Real.log a
  let g : ℝ → ℝ := (Ioi c).indicator fun t => ‖phi‖ * Real.exp (-t)
  have hgOn : IntegrableOn (fun t : ℝ => ‖phi‖ * Real.exp (-t)) (Ioi c) := by
    exact (integrableOn_exp_neg_Ioi c).const_mul ‖phi‖
  have hg : Integrable g := hgOn.integrable_indicator measurableSet_Ioi
  apply Integrable.mono' hg
    (measurable_suzukiReflectedLogProfile ha.le phi).aestronglyMeasurable
  filter_upwards [volume.ae_ne c] with t htc
  change ‖suzukiReflectedLogProfile a ha.le phi t‖ ≤
    (Ioi c).indicator (fun u => ‖phi‖ * Real.exp (-u)) t
  by_cases ht : t < c
  · rw [suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi ht,
      norm_zero, Set.indicator_of_notMem (by simpa only [mem_Ioi, not_lt] using ht.le)]
  · have hct : c < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm htc)
    have hargLe : Real.exp (-t) ≤ a := by
      dsimp only [c] at hct
      rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr (by linarith)
    have hind : (Ioi c).indicator (fun u => ‖phi‖ * Real.exp (-u)) t =
        ‖phi‖ * Real.exp (-t) := Set.indicator_of_mem hct _
    rw [hind, suzukiReflectedLogProfile,
      suzukiClosedIntervalZeroExtension_apply_of_mem ha.le phi
        ⟨(Real.exp_pos _).le, hargLe⟩,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-t) * ‖phi ⟨Real.exp (-t), ⟨(Real.exp_pos _).le, hargLe⟩⟩‖ ≤
          Real.exp (-t) * ‖phi‖ :=
        mul_le_mul_of_nonneg_left (phi.norm_coe_le_norm _) (Real.exp_pos _).le
      _ = ‖phi‖ * Real.exp (-t) := mul_comm _ _

/-- Exact logarithmic change of variables from the reflected profile convolution back to the
physical interval.  This is the measure-theoretic identity `y = exp(-t)`, including the Jacobian
factor already built into `suzukiReflectedLogProfile`. -/
theorem suzukiLogConvolution_reflectedProfile_eq_interval
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ))
    (F : ℝ → ℂ) (s : ℝ) :
    suzukiLogConvolution (suzukiReflectedLogProfile a ha.le phi) F s =
      ∫ y : ClosedInterval 0 a, F (s + Real.log (y : ℝ)) * phi y := by
  let c : ℝ := -Real.log a
  let f : ℝ → ℝ := fun t => Real.exp (-t)
  let f' : ℝ → ℝ := fun t => -Real.exp (-t)
  let G : ℝ → ℂ := fun y =>
    F (s + Real.log y) * suzukiClosedIntervalZeroExtension a ha.le phi y
  have hf' : ∀ t ∈ Ici c, HasDerivWithinAt f (f' t) (Ici c) t := by
    intro t _
    have hder : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-t)) t := by
      convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t) using 1 <;>
        first | rfl | ring
    exact hder.hasDerivWithinAt
  have hanti : AntitoneOn f (Ici c) := by
    intro u _ v _ huv
    dsimp only [f]
    exact Real.exp_le_exp.mpr (neg_le_neg huv)
  have himage : f '' Ici c = Ioc 0 a := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : c ≤ t := ht
      constructor
      · exact Real.exp_pos _
      · dsimp only [c] at ht'
        rw [← Real.exp_log ha]
        exact Real.exp_le_exp.mpr (by linarith)
    · intro hy
      refine ⟨-Real.log y, ?_, ?_⟩
      · change c ≤ -Real.log y
        dsimp only [c]
        have hlog : Real.log y ≤ Real.log a :=
          Real.strictMonoOn_log.monotoneOn hy.1 ha hy.2
        linarith
      · change Real.exp (-(-Real.log y)) = y
        rw [neg_neg, Real.exp_log hy.1]
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitoneOn
    measurableSet_Ici hf' hanti G
  rw [himage] at hcov
  dsimp only [f, f', G] at hcov
  simp only [neg_neg, Real.log_exp, Complex.real_smul] at hcov
  calc
    suzukiLogConvolution (suzukiReflectedLogProfile a ha.le phi) F s =
        ∫ t in Ici c, suzukiReflectedLogProfile a ha.le phi t * F (s - t) := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      · rfl
      · intro t ht
        rw [suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi]
        · simp
        · dsimp only [c] at ht
          exact lt_of_not_ge ht
    _ = ∫ t in Ici c, ((Real.exp (-t) : ℝ) : ℂ) *
          (F (s - t) * suzukiClosedIntervalZeroExtension a ha.le phi
            (Real.exp (-t))) := by
      refine setIntegral_congr_fun measurableSet_Ici fun t _ => ?_
      rw [suzukiReflectedLogProfile]
      ring
    _ = ∫ y in Ioc 0 a,
          F (s + Real.log y) * suzukiClosedIntervalZeroExtension a ha.le phi y :=
      hcov.symm
    _ = ∫ y in Icc 0 a,
          F (s + Real.log y) * suzukiClosedIntervalZeroExtension a ha.le phi y :=
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
    _ = ∫ y in Icc 0 a,
          F (s + Real.log y) * phi (Set.projIcc 0 a ha.le y) := by
      refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
      rw [suzukiClosedIntervalZeroExtension_apply_of_mem ha.le phi hy,
        Set.projIcc_of_mem ha.le hy]
    _ = ∫ y : ClosedInterval 0 a,
          F (s + Real.log (y : ℝ)) * phi (Set.projIcc 0 a ha.le (y : ℝ)) := by
      exact (MeasureTheory.integral_subtype measurableSet_Icc
        (fun y : ℝ => F (s + Real.log y) * phi (Set.projIcc 0 a ha.le y))).symm
    _ = ∫ y : ClosedInterval 0 a, F (s + Real.log (y : ℝ)) * phi y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Set.projIcc_of_mem ha.le y.property]

/-- Literal Suzuki kernel paired with a continuous function on the compact physical interval. -/
def suzukiSourceHIntervalIntegral
    (omega a : ℝ) (phi : C(ClosedInterval 0 a, ℂ)) (x : ℝ) : ℂ :=
  ∫ y : ClosedInterval 0 a,
    suzukiSourceHFinite omega (x * (y : ℝ)) * phi y

/-- Below a fixed logarithmic horizon, reflected convolution by the compact `W^{1,1}` truncation
is exactly the physical Suzuki kernel integral.  The endpoint `y = 0` is discarded only as a null
set; no value of `log 0` is used in the mathematical identity. -/
theorem suzukiLogConvolution_reflectedProfile_sourceHLogTrunc_eq_interval
    {a : ℝ} (ha : 0 < a) (phi : C(ClosedInterval 0 a, ℂ))
    (omega : ℝ) {B s : ℝ} (hsB : s + Real.log a ≤ B) :
    suzukiLogConvolution (suzukiReflectedLogProfile a ha.le phi)
        (suzukiSourceHLogTrunc omega B) s =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (Real.exp s * (y : ℝ)) * phi y := by
  rw [suzukiLogConvolution_reflectedProfile_eq_interval ha phi]
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  apply integral_congr_ae
  filter_upwards [hne] with y hy
  have hypos : 0 < (y : ℝ) :=
    lt_of_le_of_ne y.property.1 (Ne.symm hy)
  have hyLog : Real.log (y : ℝ) ≤ Real.log a :=
    Real.strictMonoOn_log.monotoneOn hypos ha y.property.2
  rw [suzukiSourceHLogTrunc_eq_sourceHFinite_exp omega (by linarith),
    Real.exp_add, Real.exp_log hypos]

/-- Pairing Suzuki's literal moving-cusp kernel against any continuous compact profile is `C¹` at
every positive physical point.  This closes the analytic gap in the printed dominated-convergence
argument by using exact logarithmic `W^{1,1}` translation instead of a false pointwise dominator. -/
theorem contDiffAt_one_suzukiSourceHIntervalIntegral
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x)
    (phi : C(ClosedInterval 0 a, ℂ)) :
    ContDiffAt ℝ 1 (suzukiSourceHIntervalIntegral omega a phi) x := by
  let B : ℝ := max 0 (Real.log x + Real.log a) + 1
  let W : ℝ → ℂ := suzukiReflectedLogProfile a ha.le phi
  let H : ℝ → ℂ := suzukiSourceHLogTrunc omega B
  let D : ℝ → ℂ := suzukiSourceHLogDerivativeTrunc omega B
  have hB : 0 ≤ B := by
    dsimp only [B]
    linarith [le_max_left 0 (Real.log x + Real.log a)]
  have hxB : Real.log x + Real.log a < B := by
    dsimp only [B]
    linarith [le_max_right 0 (Real.log x + Real.log a)]
  have hW : Integrable W := integrable_suzukiReflectedLogProfile ha phi
  have hD : Integrable D := integrable_suzukiSourceHLogDerivativeTrunc homega hB
  have hH : Integrable H := integrable_suzukiSourceHLogTrunc homega hB
  have hWmeas : Measurable W := measurable_suzukiReflectedLogProfile ha.le phi
  have hWH : ∀ s, Integrable (fun t => W t * H (s - t)) := by
    intro s
    exact (hH.comp_sub_left s).bdd_mul hWmeas.aestronglyMeasurable
      (Eventually.of_forall fun t => norm_suzukiReflectedLogProfile_le ha phi t)
  have hWzero : ∀ t, t < -Real.log a → W t = 0 := by
    intro t ht
    exact suzukiReflectedLogProfile_eq_zero_of_lt_neg_log ha phi ht
  have hFTC : ∀ u v, u < B → v < B →
      (∫ r in u..v, D r) = H v - H u := by
    intro u v huB hvB
    change (∫ r in u..v, suzukiSourceHLogDerivativeTrunc omega B r) =
      suzukiSourceHLogTrunc omega B v - suzukiSourceHLogTrunc omega B u
    calc
      (∫ r in u..v, suzukiSourceHLogDerivativeTrunc omega B r) =
          suzukiSourceHFinite omega (Real.exp v) -
            suzukiSourceHFinite omega (Real.exp u) :=
        integral_suzukiSourceHLogDerivativeTrunc_eq_sub homega huB hvB
      _ = suzukiSourceHLogTrunc omega B v - suzukiSourceHLogTrunc omega B u := by
        rw [suzukiSourceHLogTrunc_eq_sourceHFinite_exp omega hvB.le,
          suzukiSourceHLogTrunc_eq_sourceHFinite_exp omega huB.le]
  have hJ : Continuous (suzukiLogConvolution W D) := by
    exact continuous_suzukiLogConvolution_of_integrable_right hD hWmeas
      (fun t => norm_suzukiReflectedLogProfile_le ha phi t)
      (fun t ht => continuousAt_suzukiReflectedLogProfile_of_ne_neg_log ha phi ht)
  have hconv : ContDiffAt ℝ 1 (suzukiLogConvolution W H) (Real.log x) :=
    contDiffAt_one_suzukiLogConvolution hW hD hWH hWzero hFTC hJ hxB
  have hcomp : ContDiffAt ℝ 1
      (fun z : ℝ => suzukiLogConvolution W H (Real.log z)) x :=
    hconv.comp x (Real.contDiffAt_log.2 hx.ne')
  have hlogEvent : ∀ᶠ z : ℝ in nhds x, Real.log z < B - Real.log a :=
    (Real.continuousAt_log hx.ne').eventually
      (Iio_mem_nhds (by linarith : Real.log x < B - Real.log a))
  have hev : suzukiSourceHIntervalIntegral omega a phi =ᶠ[nhds x]
      fun z : ℝ => suzukiLogConvolution W H (Real.log z) := by
    filter_upwards [Ioi_mem_nhds hx, hlogEvent] with z hz hzB
    change (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (z * (y : ℝ)) * phi y) =
      suzukiLogConvolution (suzukiReflectedLogProfile a ha.le phi)
        (suzukiSourceHLogTrunc omega B) (Real.log z)
    rw [suzukiLogConvolution_reflectedProfile_sourceHLogTrunc_eq_interval
      ha phi omega (by linarith : Real.log z + Real.log a ≤ B),
      Real.exp_log hz]
  exact hcomp.congr_of_eventuallyEq hev

end RHTower
