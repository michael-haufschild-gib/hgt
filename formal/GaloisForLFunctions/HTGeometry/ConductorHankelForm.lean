import GaloisForLFunctions.HTGeometry.ConductorCausalSuperposition
import GaloisForLFunctions.HTGeometry.ConductorKernelFubini

/-!
# From the causal pair form to the Hankel form

On a core of anticausal sources and causal readers the convolution pairing against a one-sided
exponential is literally a Hankel form: the reflection `s = -v` turns the difference `t - s` into
the sum `t + v`, and the one-sided support makes the two half lines the whole domain.

Integrating the rank-one Hankel kernels over the rate then produces the conductor kernel, whose
form is bounded by the Carleman/Hilbert inequality.
-/

open Complex Real Set Filter Topology MeasureTheory ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem causalFourierExponential_eval {a r : ℝ} (hr : 0 < r) :
    RHTower.causalFourierExponential a r
      = (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * r) := by
  rw [RHTower.causalFourierExponential, Set.indicator_of_mem (Set.mem_Ioi.mpr hr)]

theorem causalFourierExponential_eval_nonpos {a r : ℝ} (hr : r ≤ 0) :
    RHTower.causalFourierExponential a r = 0 := by
  rw [RHTower.causalFourierExponential,
    Set.indicator_of_notMem (by simpa using not_lt.mpr hr)]

/-- Reflecting the half line. -/
theorem setIntegral_Iio_neg (f : ℝ → ℂ) :
    (∫ s in Iio (0:ℝ), f s) = ∫ v in Ioi (0:ℝ), f (-v) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f (Iio 0)
  simpa [show (fun v : ℝ => -v) ⁻¹' (Iio (0:ℝ)) = Ioi (0:ℝ) by ext v; simp] using h.symm

/-- **The reflection turns a difference kernel into a sum kernel.** -/
theorem hankel_substitution (a : ℝ) (φ ψ : ℝ → ℂ) :
    (∫ t in Ioi (0:ℝ), ∫ s in Iio (0:ℝ),
        RHTower.causalFourierExponential a (t - s) * φ s * (starRingEnd ℂ) (ψ t))
      = ∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          RHTower.causalFourierExponential a (t + v) * φ (-v) * (starRingEnd ℂ) (ψ t) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [setIntegral_Iio_neg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  congr 3
  ring

/-- **The causal pair form is a Hankel form.**  On the core, the kernel value is the explicit
rank-one exponential in the sum variable. -/
theorem hankel_substitution_eval (a : ℝ) (φ ψ : ℝ → ℂ) :
    (∫ t in Ioi (0:ℝ), ∫ s in Iio (0:ℝ),
        RHTower.causalFourierExponential a (t - s) * φ s * (starRingEnd ℂ) (ψ t))
      = ∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * (t + v))
            * φ (-v) * (starRingEnd ℂ) (ψ t) := by
  rw [hankel_substitution]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have ht0 : (0 : ℝ) < t := ht
  have hv0 : (0 : ℝ) < v := hv
  rw [causalFourierExponential_eval (by linarith : (0:ℝ) < t + v)]
  push_cast
  ring

/-! ## The rate integral in the causal normalization -/

/-- The conductor kernel in the causal Fourier normalization. -/
def conductorKernelPi (r : ℝ) : ℝ := Real.exp (-2 * Real.pi * r) / r

theorem conductorKernelPi_eq {r : ℝ} (hr : 0 < r) :
    conductorKernelPi r = Real.pi * conductorKernelBase (Real.pi * r) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [conductorKernelPi, conductorKernelBase]
  field_simp

theorem conductorKernelPi_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ conductorKernelPi r := by
  rw [conductorKernelPi]
  positivity

theorem conductorKernelPi_le {r : ℝ} (hr : 0 < r) : conductorKernelPi r ≤ 1 / r := by
  rw [conductorKernelPi, div_le_div_iff₀ hr hr]
  have hexp : Real.exp (-2 * Real.pi * r) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith
  nlinarith

/-- **The rate integral of the causal rank-one kernels.**  `∫_0^∞ π e^{-π(λ+2)r} dλ = e^{-2πr}/r`. -/
theorem integral_lam_rankOnePi {r : ℝ} (hr : 0 < r) :
    (∫ lam in Ioi (0:ℝ), Real.pi * Real.exp (-(Real.pi * (lam + 2)) * r))
      = conductorKernelPi r := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpr : (0 : ℝ) < Real.pi * r := by positivity
  have hcongr : ∀ lam : ℝ, Real.pi * Real.exp (-(Real.pi * (lam + 2)) * r)
      = Real.pi * Real.exp (-(lam + 2) * (Real.pi * r)) := by
    intro lam
    congr 2
    ring
  simp only [hcongr]
  rw [MeasureTheory.integral_const_mul, integral_lam_rankOne hpr, conductorKernelPi_eq hr]

/-! ## The bounded conductor form -/

theorem measurable_conductorKernelPi : Measurable conductorKernelPi := by
  refine Measurable.div ?_ measurable_id
  exact Real.measurable_exp.comp (measurable_const.mul measurable_id)

/-- **The conductor Hankel form is bounded with the Hilbert constant.** -/
theorem lintegral_conductorPi_form_le {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ u in Ioi (0:ℝ),
        G u * ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorKernelPi (u + v)) * F v)
      ≤ ENNReal.ofReal Real.pi
        * ((∫⁻ u in Ioi (0:ℝ), G u ^ 2) ^ ((1 : ℝ) / 2)
          * (∫⁻ v in Ioi (0:ℝ), F v ^ 2) ^ ((1 : ℝ) / 2)) :=
  lintegral_dominatedHankel_form_le measurable_conductorKernelPi
    (fun _ hr => conductorKernelPi_le hr) hF hG

theorem enorm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  simp

/-- **The complex conductor form is bounded.**  The sesquilinear pairing of an anticausal source
against a causal reader through the conductor kernel obeys the Hilbert bound. -/
theorem enorm_conductorForm_le {φ ψ : ℝ → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ‖∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        (conductorKernelPi (u + v) : ℂ) * φ (-v) * (starRingEnd ℂ) (ψ u)‖ₑ
      ≤ ENNReal.ofReal Real.pi
        * ((∫⁻ u in Ioi (0:ℝ), ‖ψ u‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
          * (∫⁻ v in Ioi (0:ℝ), ‖φ (-v)‖ₑ ^ 2) ^ ((1 : ℝ) / 2)) := by
  have houter : ‖∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      (conductorKernelPi (u + v) : ℂ) * φ (-v) * (starRingEnd ℂ) (ψ u)‖ₑ
      ≤ ∫⁻ u in Ioi (0:ℝ), ‖∫ v in Ioi (0:ℝ),
          (conductorKernelPi (u + v) : ℂ) * φ (-v) * (starRingEnd ℂ) (ψ u)‖ₑ :=
    MeasureTheory.enorm_integral_le_lintegral_enorm _
  have hinner : ∀ u : ℝ, u ∈ Ioi (0:ℝ) →
      ‖∫ v in Ioi (0:ℝ), (conductorKernelPi (u + v) : ℂ) * φ (-v) * (starRingEnd ℂ) (ψ u)‖ₑ
        ≤ ‖ψ u‖ₑ * ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorKernelPi (u + v)) * ‖φ (-v)‖ₑ := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp)]
    refine setLIntegral_mono' measurableSet_Ioi (fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have hk : (0 : ℝ) ≤ conductorKernelPi (u + v) := conductorKernelPi_nonneg (by linarith)
    rw [enorm_mul, enorm_mul, enorm_ofReal_complex, RCLike.enorm_conj,
      Real.enorm_of_nonneg hk]
    ring_nf
    exact le_rfl
  refine le_trans houter ?_
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hinner) ?_
  exact lintegral_conductorPi_form_le
    ((hφ.comp measurable_neg).enorm) hψ.enorm

/-! ## The superposed pairing is bounded -/

theorem integrableOn_rankOnePi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun lam : ℝ => Real.pi * Real.exp (-(Real.pi * (lam + 2)) * r))
      (Ioi 0) volume := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpr : (0 : ℝ) < Real.pi * r := by positivity
  have hb : IntegrableOn (fun lam : ℝ => Real.pi * Real.exp (-(lam + 2) * (Real.pi * r)))
      (Ioi 0) volume := (integrableOn_rankOne hpr).const_mul Real.pi
  have heq : (fun lam : ℝ => Real.pi * Real.exp (-(lam + 2) * (Real.pi * r)))
      = fun lam : ℝ => Real.pi * Real.exp (-(Real.pi * (lam + 2)) * r) := by
    funext lam
    congr 2
    ring
  rwa [heq] at hb

theorem lintegral_lam_rankOnePi {r : ℝ} (hr : 0 < r) :
    (∫⁻ lam in Ioi (0:ℝ), ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * r)))
      = ENNReal.ofReal (conductorKernelPi r) := by
  rw [← integral_lam_rankOnePi hr,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_rankOnePi hr)]
  filter_upwards with lam
  positivity

/-- **The superposed conductor pairing is bounded.**  Tonelli in the rate variable turns the
family of rank-one Hankel pairings into the conductor kernel pairing, which the Carleman bound
controls.  No integrability hypotheses are needed: every step is a nonnegative interchange. -/
theorem enorm_lam_resolvent_pairing_le {φ ψ : ℝ → ℂ}
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫⁻ lam in Ioi (0:ℝ), ‖∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        RHTower.causalFourierExponential (lam + 2) (t + v) * φ (-v) * (starRingEnd ℂ) (ψ t)‖ₑ)
      ≤ ENNReal.ofReal Real.pi
        * ((∫⁻ t in Ioi (0:ℝ), ‖ψ t‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
          * (∫⁻ v in Ioi (0:ℝ), ‖φ (-v)‖ₑ ^ 2) ^ ((1 : ℝ) / 2)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep : ∀ lam ∈ Ioi (0:ℝ),
      ‖∫ t in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
          RHTower.causalFourierExponential (lam + 2) (t + v) * φ (-v) * (starRingEnd ℂ) (ψ t)‖ₑ
        ≤ ∫⁻ t in Ioi (0:ℝ), ‖ψ t‖ₑ * ∫⁻ v in Ioi (0:ℝ),
            ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v)))
              * ‖φ (-v)‖ₑ := by
    intro lam _
    refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
    refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp)]
    refine setLIntegral_mono' measurableSet_Ioi (fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    rw [causalFourierExponential_eval (by linarith : (0:ℝ) < t + v)]
    have hk : (0 : ℝ) ≤ Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v)) := by positivity
    rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
    have hcast : (Real.pi : ℂ) * Complex.exp (-((Real.pi * (lam + 2) : ℝ) : ℂ) * ((t + v : ℝ) : ℂ))
        = ((Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v)) : ℝ) : ℂ) := by
      push_cast
      ring_nf
    have hval : ‖(Real.pi : ℂ) * Complex.exp (-((Real.pi * (lam + 2) : ℝ) : ℂ) * ((t + v : ℝ) : ℂ))‖ₑ
        = ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v))) := by
      rw [hcast, enorm_ofReal_complex, Real.enorm_of_nonneg hk]
    rw [hval]
    ring_nf
    exact le_rfl
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hstep) ?_
  have hkmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (p.1 + 2)) * p.2)) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    exact Real.measurable_exp.comp
      ((measurable_const.mul (measurable_fst.add measurable_const)).neg.mul measurable_snd)
  have hinner : ∀ t : ℝ, 0 < t →
      (∫⁻ lam in Ioi (0:ℝ), ∫⁻ v in Ioi (0:ℝ),
          ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v))) * ‖φ (-v)‖ₑ)
        = ∫⁻ v in Ioi (0:ℝ), ENNReal.ofReal (conductorKernelPi (t + v)) * ‖φ (-v)‖ₑ := by
    intro t ht0
    have hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (p.1 + 2)) * (t + p.2))) * ‖φ (-p.2)‖ₑ)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
      have h1 : Measurable fun p : ℝ × ℝ =>
          ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (p.1 + 2)) * (t + p.2))) := by
        refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
        exact Real.measurable_exp.comp
          ((measurable_const.mul (measurable_fst.add measurable_const)).neg.mul
            (measurable_const.add measurable_snd))
      have h2 : Measurable fun p : ℝ × ℝ => ‖φ (-p.2)‖ₑ :=
        ((hφ.comp measurable_neg).comp measurable_snd).enorm
      exact (h1.mul h2).aemeasurable
    rw [lintegral_lintegral_swap hmeas]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv0 : (0 : ℝ) < v := hv
    have hm : Measurable fun lam : ℝ =>
        ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v))) := by
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
      exact Real.measurable_exp.comp
        ((measurable_const.mul (measurable_id.add measurable_const)).neg.mul measurable_const)
    rw [lintegral_mul_const _ hm, lintegral_lam_rankOnePi (by linarith : (0:ℝ) < t + v)]
  have hswap : (∫⁻ lam in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), ‖ψ t‖ₑ * ∫⁻ v in Ioi (0:ℝ),
        ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (lam + 2)) * (t + v))) * ‖φ (-v)‖ₑ)
      = ∫⁻ t in Ioi (0:ℝ), ‖ψ t‖ₑ * ∫⁻ v in Ioi (0:ℝ),
          ENNReal.ofReal (conductorKernelPi (t + v)) * ‖φ (-v)‖ₑ := by
    have hmeas2 : AEMeasurable (fun p : ℝ × ℝ => ‖ψ p.2‖ₑ * ∫⁻ v in Ioi (0:ℝ),
        ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (p.1 + 2)) * (p.2 + v))) * ‖φ (-v)‖ₑ)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
      refine Measurable.aemeasurable (Measurable.mul (hψ.comp measurable_snd).enorm ?_)
      refine Measurable.lintegral_prod_right' (f := fun q : (ℝ × ℝ) × ℝ =>
        ENNReal.ofReal (Real.pi * Real.exp (-(Real.pi * (q.1.1 + 2)) * (q.1.2 + q.2)))
          * ‖φ (-q.2)‖ₑ) ?_
      refine Measurable.mul ?_ (((hφ.comp measurable_neg).comp measurable_snd).enorm)
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
      exact Real.measurable_exp.comp
        ((measurable_const.mul ((measurable_fst.comp measurable_fst).add measurable_const)).neg.mul
          ((measurable_snd.comp measurable_fst).add measurable_snd))
    rw [lintegral_lintegral_swap hmeas2]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [lintegral_const_mul' _ _ (by simp : ‖ψ t‖ₑ ≠ ⊤), hinner t ht0]
  rw [hswap]
  exact lintegral_conductorPi_form_le ((hφ.comp measurable_neg).enorm) hψ.enorm

end GaloisForLFunctions.HTGeometry
