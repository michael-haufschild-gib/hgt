import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import GaloisForLFunctions.HTGeometry.BesselK1SectorialPoincare

/-!
# The right Mellin transform of a tail datum is a half-plane Laplace transform

The substitution `t = a e^x` carries the tail `(a, ∞)` onto the half-line `(0, ∞)` and turns a
square-integrable datum `f` there into `φ(x) = √a e^{x/2} f(a e^x)`, with the same mass.  The right
Mellin transform of `f` over the tail becomes `a^{1/2-s}` times the half-line Laplace transform of
`φ` at `s - 1/2`.  This is the dictionary in which Burnol's `A^s H²` description of the Sonine
spaces is stated (arXiv:math/0203120, §4).

## Main results

* `logChart`
* `integral_norm_sq_logChart`
* `mellinTail_eq_laplaceRay`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential scaling `x ↦ a e^x` carries the positive half-line onto the tail `(a, ∞)`. -/
theorem image_Ioi_expScale {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ => a * Real.exp x) '' Ioi (0 : ℝ) = Ioi a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : (0 : ℝ) < x := hx
    have h1 : (1 : ℝ) < Real.exp x := by
      have h2 := Real.add_one_le_exp x
      linarith
    show a < a * Real.exp x
    nlinarith
  · intro hy
    refine ⟨Real.log (y / a), ?_, ?_⟩
    · refine Real.log_pos ?_
      rw [lt_div_iff₀ ha, one_mul]
      exact hy
    · have hy0 : (0 : ℝ) < y := lt_trans ha hy
      show a * Real.exp (Real.log (y / a)) = y
      rw [Real.exp_log (div_pos hy0 ha)]
      field_simp

theorem hasDerivWithinAt_expScale {a : ℝ} (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => a * Real.exp y) (a * Real.exp x) (Ioi (0 : ℝ)) x :=
  ((Real.hasDerivAt_exp x).const_mul a).hasDerivWithinAt

theorem injOn_expScale {a : ℝ} (ha : 0 < a) :
    Set.InjOn (fun y : ℝ => a * Real.exp y) (Ioi (0 : ℝ)) := fun _ _ _ _ huv =>
  Real.exp_injective (mul_left_cancel₀ (ne_of_gt ha) huv)

/-- **The change of variables `t = a e^x` from the tail to the half-line.** -/
theorem integral_Ioi_expScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (g : ℝ → E) :
    (∫ t in Ioi a, g t)
      = ∫ x in Ioi (0 : ℝ), (a * Real.exp x) • g (a * Real.exp x) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => hasDerivWithinAt_expScale (a := a) x) (injOn_expScale ha) g
  rw [image_Ioi_expScale ha] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  show |a * Real.exp x| • g (a * Real.exp x) = (a * Real.exp x) • g (a * Real.exp x)
  rw [abs_of_pos (by positivity : (0:ℝ) < a * Real.exp x)]

/-- Integrability along the change of variables. -/
theorem integrableOn_Ioi_expScale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (g : ℝ → E) :
    IntegrableOn g (Ioi a) ↔
      IntegrableOn (fun x : ℝ => (a * Real.exp x) • g (a * Real.exp x)) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x _ => hasDerivWithinAt_expScale (a := a) x) (injOn_expScale ha) g
  rw [image_Ioi_expScale ha] at h
  rw [h]
  constructor
  · intro hI
    refine hI.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show |a * Real.exp x| • g (a * Real.exp x) = (a * Real.exp x) • g (a * Real.exp x)
    rw [abs_of_pos (by positivity : (0:ℝ) < a * Real.exp x)]
  · intro hI
    refine hI.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show (a * Real.exp x) • g (a * Real.exp x) = |a * Real.exp x| • g (a * Real.exp x)
    rw [abs_of_pos (by positivity : (0:ℝ) < a * Real.exp x)]

/-- The exponential scaling pulls null sets of the tail back to null sets of the half-line. -/
theorem quasiMeasurePreserving_expScale {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => a * Real.exp x)
      (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioi a)) := by
  have hmeas : Measurable fun x : ℝ => a * Real.exp x := by fun_prop
  refine ⟨hmeas, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [Measure.map_apply hmeas hs]
  rw [Measure.restrict_apply hs] at hzero
  rw [Measure.restrict_apply (hmeas hs)]
  -- reduce to a null subset of the tail
  set N : Set ℝ := s ∩ Ioi a with hN
  have hNmeas : MeasurableSet N := hs.inter measurableSet_Ioi
  have hNzero : volume N = 0 := hzero
  have hpre : (fun x : ℝ => a * Real.exp x) ⁻¹' s ∩ Ioi (0 : ℝ)
      = (fun x : ℝ => a * Real.exp x) ⁻¹' N ∩ Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨⟨hx, ?_⟩, hx0⟩
      have hx0' : (0 : ℝ) < x := hx0
      have h1 : (1 : ℝ) < Real.exp x := by
        have h2 := Real.add_one_le_exp x
        linarith
      show a < a * Real.exp x
      nlinarith
    · rintro ⟨hx, hx0⟩
      exact ⟨hx.1, hx0⟩
  rw [hpre]
  -- the indicator of `N` transported to the half-line
  set g : ℝ → ℝ := N.indicator (fun _ => (1 : ℝ)) with hg
  have hgae : g =ᵐ[volume] 0 := by
    refine (Filter.EventuallyEq.symm ?_)
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hNzero
    by_contra hxN
    exact hx (by simp [hg, Set.indicator_of_notMem hxN])
  have hgint : IntegrableOn g (Ioi a) := by
    refine (integrable_zero ℝ ℝ volume).integrableOn.congr ?_
    exact (hgae.restrict).symm
  have hgzero : (∫ t in Ioi a, g t) = 0 := by
    refine integral_eq_zero_of_ae ?_
    exact hgae.restrict
  have htrans : IntegrableOn (fun x : ℝ => (a * Real.exp x) * g (a * Real.exp x))
      (Ioi (0 : ℝ)) := by
    have := (integrableOn_Ioi_expScale ha g).1 hgint
    simpa [smul_eq_mul] using this
  have htransZero : (∫ x in Ioi (0 : ℝ), (a * Real.exp x) * g (a * Real.exp x)) = 0 := by
    have hcongr : (∫ x in Ioi (0 : ℝ), (a * Real.exp x) * g (a * Real.exp x))
        = ∫ x in Ioi (0 : ℝ), (a * Real.exp x) • g (a * Real.exp x) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [smul_eq_mul]
    rw [hcongr, ← integral_Ioi_expScale ha g, hgzero]
  have hae0 : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      (a * Real.exp x) * g (a * Real.exp x) = 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ htrans).1 htransZero
    filter_upwards with x
    have h1 : (0 : ℝ) ≤ g (a * Real.exp x) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    positivity
  have hnot : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      x ∉ ((fun x : ℝ => a * Real.exp x) ⁻¹' N) := by
    filter_upwards [hae0] with x hx hmem
    have hpos : (0 : ℝ) < a * Real.exp x := by positivity
    have : g (a * Real.exp x) = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    have hmem' : a * Real.exp x ∈ N := hmem
    rw [hg, Set.indicator_of_mem hmem'] at this
    exact one_ne_zero this
  have hfin := (ae_iff).1 hnot
  simp only [not_not, Set.setOf_mem_eq] at hfin
  rw [Measure.restrict_apply (hmeas hNmeas)] at hfin
  exact hfin

/-! ### The logarithmic chart -/

/-- The logarithmic chart of a tail datum at aperture `a`:  `φ(x) = √a e^{x/2} f(a e^x)`. -/
def logChart (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ((Real.sqrt a * Real.exp (x / 2) : ℝ) : ℂ) * f (a * Real.exp x)

theorem norm_sq_logChart {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) (x : ℝ) :
    ‖logChart a f x‖ ^ 2 = (a * Real.exp x) * ‖f (a * Real.exp x)‖ ^ 2 := by
  rw [logChart, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt a * Real.exp (x / 2)), mul_pow,
    Real.sq_sqrt ha]
  congr 2
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **The chart preserves the mass.** -/
theorem integral_norm_sq_logChart {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), ‖logChart a f x‖ ^ 2) = ∫ t in Ioi a, ‖f t‖ ^ 2 := by
  rw [integral_Ioi_expScale ha (fun t : ℝ => ‖f t‖ ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [norm_sq_logChart ha.le, smul_eq_mul]

theorem aestronglyMeasurable_logChart {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a))) :
    AEStronglyMeasurable (logChart a f) (volume.restrict (Ioi (0 : ℝ))) := by
  refine AEStronglyMeasurable.mul ?_ (hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_expScale ha))
  exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable

/-- **The chart of a square-integrable tail datum is square-integrable on the half-line.** -/
theorem memLp_two_logChart {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi a))) :
    MemLp (logChart a f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logChart ha
    hf.aestronglyMeasurable)).2 ?_
  have hbase : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Ioi a) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have htrans := (integrableOn_Ioi_expScale ha (fun t : ℝ => ‖f t‖ ^ 2)).1 hbase
  refine htrans.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show (a * Real.exp x) • ‖f (a * Real.exp x)‖ ^ 2 = ‖logChart a f x‖ ^ 2
  rw [norm_sq_logChart ha.le, smul_eq_mul]

/-- **The right Mellin transform over the tail is a half-plane Laplace transform.** -/
theorem mellinTail_eq_laplaceRay {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (s : ℂ) :
    (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * f t)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * laplaceRay (logChart a f) (s - 1 / 2) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hene : ∀ y : ℝ, ((Real.exp y : ℝ) : ℂ) ≠ 0 := by
    intro y
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.exp_pos y)
  rw [integral_Ioi_expScale ha (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * f t), laplaceRay,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have hsqrt : ((Real.sqrt a : ℝ) : ℂ) = ((a : ℝ) : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_cpow ha.le]
  have hbase : ((a * Real.exp x : ℝ) : ℂ) ^ (-s)
      = ((a : ℝ) : ℂ) ^ (-s) * ((Real.exp x : ℝ) : ℂ) ^ (-s) := by
    have hpush : ((a * Real.exp x : ℝ) : ℂ) = ((a : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hpush, GaloisForLFunctions.HTGeometry.ofReal_mul_cpow ha (hene x)]
  have hA : ((a : ℝ) : ℂ) * ((a : ℝ) : ℂ) ^ (-s)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((Real.sqrt a : ℝ) : ℂ) := by
    rw [hsqrt, ← Complex.cpow_add _ _ hane]
    have hsum : ((1 : ℂ) / 2 - s) + (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 - s := by
      push_cast
      ring
    rw [hsum, Complex.cpow_sub _ _ hane, Complex.cpow_one, Complex.cpow_neg]
    field_simp
  have hE : ((Real.exp x : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) ^ (-s)
      = ((Real.exp (x / 2) : ℝ) : ℂ) * Complex.exp (-((s - 1 / 2) * ((x : ℝ) : ℂ))) := by
    have h1 : ((Real.exp x : ℝ) : ℂ) ^ (-s) = Complex.exp (((x : ℝ) : ℂ) * (-s)) :=
      GaloisForLFunctions.cpow_ofReal_exp x (-s)
    have h2 : ((Real.exp x : ℝ) : ℂ) = Complex.exp (((x : ℝ) : ℂ)) := Complex.ofReal_exp x
    have h3 : ((Real.exp (x / 2) : ℝ) : ℂ) = Complex.exp (((x / 2 : ℝ) : ℂ)) :=
      Complex.ofReal_exp (x / 2)
    rw [h1, h2, h3, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  show ((a * Real.exp x : ℝ)) • (((a * Real.exp x : ℝ) : ℂ) ^ (-s) * f (a * Real.exp x))
    = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * (logChart a f x * expRay (s - 1 / 2) x)
  rw [Complex.real_smul, hbase, logChart, expRay]
  have hcast2 : ((a * Real.exp x : ℝ) : ℂ) = ((a : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) := by
    push_cast
    ring
  have hcast3 : ((Real.sqrt a * Real.exp (x / 2) : ℝ) : ℂ)
      = ((Real.sqrt a : ℝ) : ℂ) * ((Real.exp (x / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast2, hcast3]
  linear_combination (((Real.exp x : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) ^ (-s)
      * f (a * Real.exp x)) * hA
    + ((((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((Real.sqrt a : ℝ) : ℂ))
      * f (a * Real.exp x)) * hE

/-! ### The inverse chart -/

theorem logScale_expScale {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.log ((a * Real.exp x) / a) = x := by
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt ha), mul_one, Real.log_exp]

theorem sqrt_expScale {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    Real.sqrt (a * Real.exp x) = Real.sqrt a * Real.exp (x / 2) := by
  have hexp : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    have h : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [Real.sqrt_mul ha, hexp]

/-- The inverse substitution pulls null sets of the half-line back to null sets of the tail. -/
theorem quasiMeasurePreserving_logScale {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => Real.log (t / a))
      (volume.restrict (Ioi a)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : Measurable fun t : ℝ => Real.log (t / a) := by fun_prop
  refine ⟨hmeas, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [Measure.map_apply hmeas hs]
  rw [Measure.restrict_apply hs] at hzero
  rw [Measure.restrict_apply (hmeas hs)]
  set S : Set ℝ := (fun t : ℝ => Real.log (t / a)) ⁻¹' s with hS
  set g : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ)) with hg
  have hpull : ∀ x : ℝ, g (a * Real.exp x) = (s.indicator (fun _ => (1 : ℝ))) x := by
    intro x
    by_cases hx : x ∈ s
    · have hmem : a * Real.exp x ∈ S := by
        rw [hS, Set.mem_preimage, logScale_expScale ha x]
        exact hx
      rw [hg, Set.indicator_of_mem hmem, Set.indicator_of_mem hx]
    · have hmem : a * Real.exp x ∉ S := by
        rw [hS, Set.mem_preimage, logScale_expScale ha x]
        exact hx
      rw [hg, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hx]
  have hsz : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      (s.indicator (fun _ => (1 : ℝ))) x = 0 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hzero
    by_contra hcon
    refine hx (fun hx0 => ?_)
    have hxs : x ∉ s := fun h => hcon ⟨h, hx0⟩
    simp [Set.indicator_of_notMem hxs]
  have hzae : (fun x : ℝ => (a * Real.exp x) • g (a * Real.exp x))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hsz] with x hx
    show (a * Real.exp x) • g (a * Real.exp x) = 0
    rw [hpull x, hx, smul_zero]
  have htrans : IntegrableOn (fun x : ℝ => (a * Real.exp x) • g (a * Real.exp x))
      (Ioi (0 : ℝ)) := (integrable_zero ℝ ℝ _).congr hzae.symm
  have hgint : IntegrableOn g (Ioi a) := (integrableOn_Ioi_expScale ha g).2 htrans
  have hgzero : (∫ t in Ioi a, g t) = 0 := by
    rw [integral_Ioi_expScale ha g]
    exact integral_eq_zero_of_ae hzae
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] g := by
    filter_upwards with t
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hgint).1 hgzero
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioi a)), t ∉ S := by
    filter_upwards [hae] with t ht hmem
    rw [hg, Set.indicator_of_mem hmem] at ht
    exact one_ne_zero ht
  have h2 := ae_iff.1 h1
  simp only [not_not, Set.setOf_mem_eq] at h2
  rwa [Measure.restrict_apply (hmeas hs)] at h2

/-- The inverse of the logarithmic chart. -/
def logChartInv (a : ℝ) (φ : ℝ → ℂ) : ℝ → ℂ :=
  fun t => (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * φ (Real.log (t / a))

@[simp] theorem logChart_logChartInv {a : ℝ} (ha : 0 < a) (φ : ℝ → ℂ) (x : ℝ) :
    logChart a (logChartInv a φ) x = φ x := by
  rw [logChart, logChartInv, logScale_expScale ha x, sqrt_expScale ha.le x]
  have hne : (Real.sqrt a * Real.exp (x / 2)) ≠ 0 := by
    have h1 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    positivity
  have hone : ((Real.sqrt a * Real.exp (x / 2) : ℝ) : ℂ)
      * (((Real.sqrt a * Real.exp (x / 2))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one]
  calc ((Real.sqrt a * Real.exp (x / 2) : ℝ) : ℂ)
        * ((((Real.sqrt a * Real.exp (x / 2))⁻¹ : ℝ) : ℂ) * φ x)
      = (((Real.sqrt a * Real.exp (x / 2) : ℝ) : ℂ)
          * (((Real.sqrt a * Real.exp (x / 2))⁻¹ : ℝ) : ℂ)) * φ x := by ring
    _ = φ x := by rw [hone, one_mul]

theorem aestronglyMeasurable_logChartInv {a : ℝ} (ha : 0 < a) {φ : ℝ → ℂ}
    (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (logChartInv a φ) (volume.restrict (Ioi a)) := by
  refine AEStronglyMeasurable.mul ?_ (hφ.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_logScale ha))
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ContinuousOn.mono (s := Ioi (0 : ℝ)) ?_ (Ioi_subset_Ioi ha.le)
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) (fun t ht => ?_)
  exact ne_of_gt (Real.sqrt_pos.2 ht)

/-- **The inverse chart of a square-integrable half-line datum is square-integrable on the
tail.** -/
theorem memLp_two_logChartInv {a : ℝ} (ha : 0 < a) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (logChartInv a φ) 2 (volume.restrict (Ioi a)) := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logChartInv ha
    hφ.aestronglyMeasurable)).2 ?_
  have hbase : IntegrableOn (fun x : ℝ => ‖φ x‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable).1 hφ
  refine (integrableOn_Ioi_expScale ha (fun t : ℝ => ‖logChartInv a φ t‖ ^ 2)).2 ?_
  refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show ‖φ x‖ ^ 2 = (a * Real.exp x) • ‖logChartInv a φ (a * Real.exp x)‖ ^ 2
  rw [smul_eq_mul, ← norm_sq_logChart ha.le, logChart_logChartInv ha]

/-! ### The dictionary -/

/-- **The Mellin transform of a tail datum lies in the Hardy space of the half-plane.** -/
theorem isHalfPlaneHardy_mellinTail {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi a))) :
    IsHalfPlaneHardy (laplaceRay (logChart a f)) (∫ t in Ioi a, ‖f t‖ ^ 2) := by
  have h := isHalfPlaneHardy_laplaceRay (memLp_two_logChart ha hf)
  rwa [integral_norm_sq_logChart ha] at h

/-- **Every element of the Hardy space of the half-plane is the Mellin transform of a tail
datum.** -/
theorem exists_tail_datum_of_isHalfPlaneHardy {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) :
    ∃ f : ℝ → ℂ, MemLp f 2 (volume.restrict (Ioi a)) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * f t)
          = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * F (s - 1 / 2) := by
  refine ⟨logChartInv a (hardyDatum F hF), memLp_two_logChartInv ha (memLp_two_hardyDatum hF),
    fun s hs => ?_⟩
  have hre : 0 < (s - 1 / 2).re := by
    simp only [Complex.sub_re, Complex.div_re]
    norm_num
    linarith
  have hval : F (s - 1 / 2) = laplaceRay (hardyDatum F hF) (s - 1 / 2) :=
    isHalfPlaneHardy_eq_laplaceRay hF hre
  rw [mellinTail_eq_laplaceRay ha _ s, hval]
  congr 2
  funext x
  exact logChart_logChartInv ha _ x


end

end RHTower
