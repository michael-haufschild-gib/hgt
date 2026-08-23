import GaloisForLFunctions.RHTower.MellinHardyBridge

/-!
# The right Mellin transform of a head datum is a half-plane Laplace transform

Mirror of `MellinHardyBridge` on the other side of the aperture.  The substitution `t = a e^{-x}`
carries the head `(0, a)` onto the half-line `(0, ∞)` and turns a square-integrable datum `f`
there into `φ(x) = √a e^{-x/2} f(a e^{-x})`, with the same mass.  The right Mellin transform of `f`
over the head becomes `a^{1/2-s}` times the half-line Laplace transform of `φ` at `1/2 - s`.

Note the reversal: the tail chart is a Laplace transform at `s - 1/2`, convergent for `Re s > 1/2`;
the head chart is one at `1/2 - s`, convergent for `Re s < 1/2`.  The two half-planes of the
`w = s - 1/2` variable are exactly the two sides of `TwoSidedLaplaceVanishing`.

## Main results

* `logChartHead`, `integral_norm_sq_logChartHead`, `memLp_two_logChartHead`
* `mellinHead_eq_laplaceRay`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The reflected exponential chart -/

/-- The exponential scaling `x ↦ a e^{-x}` carries the positive half-line onto the head `(0, a)`. -/
theorem image_Ioi_expScaleNeg {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ => a * Real.exp (-x)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : (0 : ℝ) < x := hx
    have h1 : Real.exp (-x) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have h2 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    constructor
    · positivity
    · nlinarith
  · rintro ⟨hy0, hya⟩
    refine ⟨Real.log (a / y), ?_, ?_⟩
    · refine Real.log_pos ?_
      rw [lt_div_iff₀ hy0, one_mul]
      exact hya
    · show a * Real.exp (-Real.log (a / y)) = y
      rw [Real.exp_neg, Real.exp_log (div_pos ha hy0)]
      field_simp

theorem hasDerivWithinAt_expScaleNeg {a : ℝ} (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => a * Real.exp (-y)) (-(a * Real.exp (-x))) (Ioi (0 : ℝ)) x := by
  have h : HasDerivAt (fun y : ℝ => a * Real.exp (-y)) (a * (Real.exp (-x) * -1)) x :=
    (((Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg))).const_mul a
  have h2 : a * (Real.exp (-x) * -1) = -(a * Real.exp (-x)) := by ring
  rw [h2] at h
  exact h.hasDerivWithinAt

theorem injOn_expScaleNeg {a : ℝ} (ha : 0 < a) :
    Set.InjOn (fun y : ℝ => a * Real.exp (-y)) (Ioi (0 : ℝ)) := by
  intro u _ v _ huv
  have := Real.exp_injective (mul_left_cancel₀ (ne_of_gt ha) huv)
  linarith [neg_injective this]

/-- **The change of variables `t = a e^{-x}` from the head to the half-line.** -/
theorem integral_Ioo_expScaleNeg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (g : ℝ → E) :
    (∫ t in Ioo (0 : ℝ) a, g t)
      = ∫ x in Ioi (0 : ℝ), (a * Real.exp (-x)) • g (a * Real.exp (-x)) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => hasDerivWithinAt_expScaleNeg (a := a) x) (injOn_expScaleNeg ha) g
  rw [image_Ioi_expScaleNeg ha] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  show |(-(a * Real.exp (-x)))| • g (a * Real.exp (-x)) = (a * Real.exp (-x)) • g (a * Real.exp (-x))
  rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < a * Real.exp (-x))]

theorem integrableOn_Ioo_expScaleNeg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (g : ℝ → E) :
    IntegrableOn g (Ioo (0 : ℝ) a) ↔
      IntegrableOn (fun x : ℝ => (a * Real.exp (-x)) • g (a * Real.exp (-x))) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x _ => hasDerivWithinAt_expScaleNeg (a := a) x) (injOn_expScaleNeg ha) g
  rw [image_Ioi_expScaleNeg ha] at h
  rw [h]
  constructor
  · intro hI
    refine hI.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show |(-(a * Real.exp (-x)))| • g (a * Real.exp (-x))
      = (a * Real.exp (-x)) • g (a * Real.exp (-x))
    rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < a * Real.exp (-x))]
  · intro hI
    refine hI.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show (a * Real.exp (-x)) • g (a * Real.exp (-x))
      = |(-(a * Real.exp (-x)))| • g (a * Real.exp (-x))
    rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < a * Real.exp (-x))]

/-! ### The logarithmic chart of a head datum -/

/-- The logarithmic chart of a head datum at aperture `a`:  `φ(x) = √a e^{-x/2} f(a e^{-x})`. -/
def logChartHead (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ((Real.sqrt a * Real.exp (-x / 2) : ℝ) : ℂ) * f (a * Real.exp (-x))

theorem norm_sq_logChartHead {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) (x : ℝ) :
    ‖logChartHead a f x‖ ^ 2 = (a * Real.exp (-x)) * ‖f (a * Real.exp (-x))‖ ^ 2 := by
  rw [logChartHead, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt a * Real.exp (-x / 2)), mul_pow,
    Real.sq_sqrt ha]
  congr 2
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **The head chart preserves the mass.** -/
theorem integral_norm_sq_logChartHead {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), ‖logChartHead a f x‖ ^ 2) = ∫ t in Ioo (0 : ℝ) a, ‖f t‖ ^ 2 := by
  rw [integral_Ioo_expScaleNeg ha (fun t : ℝ => ‖f t‖ ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [norm_sq_logChartHead ha.le, smul_eq_mul]

theorem quasiMeasurePreserving_expScaleNeg {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => a * Real.exp (-x))
      (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioo (0 : ℝ) a)) := by
  have hmeas : Measurable fun x : ℝ => a * Real.exp (-x) := by fun_prop
  refine ⟨hmeas, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [Measure.map_apply hmeas hs]
  rw [Measure.restrict_apply hs] at hzero
  rw [Measure.restrict_apply (hmeas hs)]
  set N : Set ℝ := s ∩ Ioo (0 : ℝ) a with hN
  have hNmeas : MeasurableSet N := hs.inter measurableSet_Ioo
  have hNzero : volume N = 0 := hzero
  have hpre : (fun x : ℝ => a * Real.exp (-x)) ⁻¹' s ∩ Ioi (0 : ℝ)
      = (fun x : ℝ => a * Real.exp (-x)) ⁻¹' N ∩ Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨⟨hx, ?_, ?_⟩, hx0⟩
      · have : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
        show (0 : ℝ) < a * Real.exp (-x)
        positivity
      · have hx0' : (0 : ℝ) < x := hx0
        have h1 : Real.exp (-x) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        show a * Real.exp (-x) < a
        nlinarith [Real.exp_pos (-x)]
    · rintro ⟨hx, hx0⟩
      exact ⟨hx.1, hx0⟩
  rw [hpre]
  set g : ℝ → ℝ := N.indicator (fun _ => (1 : ℝ)) with hg
  have hgae : g =ᵐ[volume] 0 := by
    refine (Filter.EventuallyEq.symm ?_)
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hNzero
    by_contra hxN
    exact hx (by simp [hg, Set.indicator_of_notMem hxN])
  have hgint : IntegrableOn g (Ioo (0 : ℝ) a) := by
    refine (integrable_zero ℝ ℝ volume).integrableOn.congr ?_
    exact (hgae.restrict).symm
  have hgzero : (∫ t in Ioo (0 : ℝ) a, g t) = 0 := by
    refine integral_eq_zero_of_ae ?_
    exact hgae.restrict
  have htrans : IntegrableOn (fun x : ℝ => (a * Real.exp (-x)) * g (a * Real.exp (-x)))
      (Ioi (0 : ℝ)) := by
    have := (integrableOn_Ioo_expScaleNeg ha g).1 hgint
    simpa [smul_eq_mul] using this
  have htransZero :
      (∫ x in Ioi (0 : ℝ), (a * Real.exp (-x)) * g (a * Real.exp (-x))) = 0 := by
    have hcongr : (∫ x in Ioi (0 : ℝ), (a * Real.exp (-x)) * g (a * Real.exp (-x)))
        = ∫ x in Ioi (0 : ℝ), (a * Real.exp (-x)) • g (a * Real.exp (-x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [smul_eq_mul]
    rw [hcongr, ← integral_Ioo_expScaleNeg ha g, hgzero]
  have hae0 : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      (a * Real.exp (-x)) * g (a * Real.exp (-x)) = 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ htrans).1 htransZero
    filter_upwards with x
    have h1 : (0 : ℝ) ≤ g (a * Real.exp (-x)) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    positivity
  have hnot : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      x ∉ ((fun x : ℝ => a * Real.exp (-x)) ⁻¹' N) := by
    filter_upwards [hae0] with x hx hmem
    have hpos : (0 : ℝ) < a * Real.exp (-x) := by
      have : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
      positivity
    have hz : g (a * Real.exp (-x)) = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    have hmem' : a * Real.exp (-x) ∈ N := hmem
    rw [hg, Set.indicator_of_mem hmem'] at hz
    exact one_ne_zero hz
  have hfin := (ae_iff).1 hnot
  simp only [not_not, Set.setOf_mem_eq] at hfin
  rw [Measure.restrict_apply (hmeas hNmeas)] at hfin
  exact hfin

theorem aestronglyMeasurable_logChartHead {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo (0 : ℝ) a))) :
    AEStronglyMeasurable (logChartHead a f) (volume.restrict (Ioi (0 : ℝ))) := by
  refine AEStronglyMeasurable.mul ?_ (hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_expScaleNeg ha))
  exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable

/-- **The chart of a square-integrable head datum is square-integrable on the half-line.** -/
theorem memLp_two_logChartHead {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) a))) :
    MemLp (logChartHead a f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_logChartHead ha
    hf.aestronglyMeasurable)).2 ?_
  have hbase : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Ioo (0 : ℝ) a) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have htrans := (integrableOn_Ioo_expScaleNeg ha (fun t : ℝ => ‖f t‖ ^ 2)).1 hbase
  refine htrans.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show (a * Real.exp (-x)) • ‖f (a * Real.exp (-x))‖ ^ 2 = ‖logChartHead a f x‖ ^ 2
  rw [norm_sq_logChartHead ha.le, smul_eq_mul]

/-- **The right Mellin transform over the head is a half-plane Laplace transform**, at the
*reflected* spectral parameter `1/2 - s`. -/
theorem mellinHead_eq_laplaceRay {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (s : ℂ) :
    (∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * f t)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * laplaceRay (logChartHead a f) (1 / 2 - s) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hene : ∀ y : ℝ, ((Real.exp y : ℝ) : ℂ) ≠ 0 := by
    intro y
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.exp_pos y)
  rw [integral_Ioo_expScaleNeg ha (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * f t), laplaceRay,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have hsqrt : ((Real.sqrt a : ℝ) : ℂ) = ((a : ℝ) : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_cpow ha.le]
  have hbase : ((a * Real.exp (-x) : ℝ) : ℂ) ^ (-s)
      = ((a : ℝ) : ℂ) ^ (-s) * ((Real.exp (-x) : ℝ) : ℂ) ^ (-s) := by
    have hpush : ((a * Real.exp (-x) : ℝ) : ℂ)
        = ((a : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hpush, GaloisForLFunctions.HTGeometry.ofReal_mul_cpow ha (hene (-x))]
  have hA : ((a : ℝ) : ℂ) * ((a : ℝ) : ℂ) ^ (-s)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((Real.sqrt a : ℝ) : ℂ) := by
    rw [hsqrt, ← Complex.cpow_add _ _ hane]
    have hsum : ((1 : ℂ) / 2 - s) + (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 - s := by
      push_cast
      ring
    rw [hsum, Complex.cpow_sub _ _ hane, Complex.cpow_one, Complex.cpow_neg]
    field_simp
  have hE : ((Real.exp (-x) : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ) ^ (-s)
      = ((Real.exp (-x / 2) : ℝ) : ℂ) * Complex.exp (-((1 / 2 - s) * ((x : ℝ) : ℂ))) := by
    have h1 : ((Real.exp (-x) : ℝ) : ℂ) ^ (-s) = Complex.exp (((-x : ℝ) : ℂ) * (-s)) :=
      GaloisForLFunctions.cpow_ofReal_exp (-x) (-s)
    have h2 : ((Real.exp (-x) : ℝ) : ℂ) = Complex.exp (((-x : ℝ) : ℂ)) := Complex.ofReal_exp (-x)
    have h3 : ((Real.exp (-x / 2) : ℝ) : ℂ) = Complex.exp (((-x / 2 : ℝ) : ℂ)) :=
      Complex.ofReal_exp (-x / 2)
    rw [h1, h2, h3, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  show ((a * Real.exp (-x) : ℝ)) • (((a * Real.exp (-x) : ℝ) : ℂ) ^ (-s) * f (a * Real.exp (-x)))
    = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * (logChartHead a f x * expRay (1 / 2 - s) x)
  rw [Complex.real_smul, hbase, logChartHead, expRay]
  have hcast2 : ((a * Real.exp (-x) : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcast3 : ((Real.sqrt a * Real.exp (-x / 2) : ℝ) : ℂ)
      = ((Real.sqrt a : ℝ) : ℂ) * ((Real.exp (-x / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast2, hcast3]
  linear_combination (((Real.exp (-x) : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ) ^ (-s)
      * f (a * Real.exp (-x))) * hA
    + ((((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) * ((Real.sqrt a : ℝ) : ℂ))
      * f (a * Real.exp (-x))) * hE

end

end RHTower
