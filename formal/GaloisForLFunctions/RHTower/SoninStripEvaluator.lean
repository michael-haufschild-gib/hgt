import GaloisForLFunctions.RHTower.MellinApertureIndependence
import GaloisForLFunctions.RHTower.MellinRealDecay
import GaloisForLFunctions.RHTower.ExtendedMellinHeadHardy
import GaloisForLFunctions.RHTower.BurnolLemmaSevenFive
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The evaluator functionals on `L_a`

Burnol's evaluators are the Riesz vectors of the functionals `f ↦ M(f)^{(k)}(w)` on the extended
Sonine space.  Right of the critical line the functional is bounded by an explicit head/tail
estimate.  **On the critical line itself the estimate blows up**, and this is where the corpus so
far stopped; but the functionals converge *pointwise* there (the continued Mellin transform of a
fixed vector is analytic), so the Banach–Steinhaus theorem hands over boundedness for free.  Left of
the line the functional is the reflected one composed with the cosine transform.

## Main results

* `soninBandConst`, `norm_soninBandConst_le`
* `soninEvaluatorRight` — the evaluator for `1/2 < Re w < 1`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The extended Sonine space as a Hilbert space -/

/-- The even part of `L_a`, as a submodule of `L²(ℝ)`. -/
def soninEvenExtended (a : ℝ) : Submodule ℂ SoninL2 :=
  centralSoninExtendedCarrier a ⊓ evenSubspace

theorem isClosed_soninEvenExtended (a : ℝ) :
    IsClosed (soninEvenExtended a : Set SoninL2) := by
  have h1 : IsClosed (centralSoninExtendedCarrier a : Set SoninL2) := by
    show IsClosed (((meanZeroBand a ⊔ centralMeanZeroFourier a)ᗮ : Submodule ℂ SoninL2) :
      Set SoninL2)
    exact (meanZeroBand a ⊔ centralMeanZeroFourier a).isClosed_orthogonal
  have h2 : IsClosed (evenSubspace : Set SoninL2) := by
    have := (ContinuousLinearMap.IsIdempotentElem.isClosed_range evenProjection_idempotent)
    exact this
  exact h1.inter h2

instance soninEvenExtended_completeSpace (a : ℝ) : CompleteSpace (soninEvenExtended a) :=
  (isClosed_soninEvenExtended a).completeSpace_coe

/-! ## The band constant as a bounded functional -/

/-- The average of `f` over the aperture band; on `L_a` it is the physical aperture constant. -/
def soninBandConst (a : ℝ) (f : SoninL2) : ℂ :=
  (1 / (2 * a) : ℂ) * ∫ t in centralInterval a, (f : ℝ → ℂ) t

theorem integrableOn_centralInterval (a : ℝ) (f : SoninL2) :
    IntegrableOn ((f : ℝ → ℂ)) (centralInterval a) volume := by
  have hmem : MemLp ((f : ℝ → ℂ)) 2 (volume.restrict (centralInterval a)) :=
    (Lp.memLp f).restrict (centralInterval a)
  haveI : IsFiniteMeasure (volume.restrict (centralInterval a)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, centralInterval]
    exact measure_Icc_lt_top
  exact hmem.integrable (by norm_num)

theorem soninBandConst_eq {a : ℝ} (ha : 0 < a) {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    soninBandConst a f = d := by
  have hval : (∫ t in centralInterval a, (f : ℝ → ℂ) t) = (2 * a : ℝ) • d := by
    have hcongr : (∫ t in centralInterval a, (f : ℝ → ℂ) t)
        = ∫ _t in centralInterval a, d := by
      refine setIntegral_congr_ae (measurableSet_centralInterval a) ?_
      filter_upwards [hd] with t ht hmem
      exact ht hmem
    rw [hcongr, setIntegral_const, centralInterval, Real.volume_real_Icc,
      max_eq_left (by linarith : (0:ℝ) ≤ a - -a)]
    congr 1
    ring
  rw [soninBandConst, hval, Complex.real_smul]
  have hane : ((2 * a : ℝ) : ℂ) ≠ 0 := by
    have h2a : (0 : ℝ) < 2 * a := by linarith
    exact_mod_cast ne_of_gt h2a
  have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  push_cast at hane ⊢
  field_simp

theorem integral_norm_le_sqrt_measure {a : ℝ} (ha : 0 < a) (f : SoninL2) :
    (∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖) ≤ Real.sqrt (2 * a) * ‖f‖ := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  haveI : IsFiniteMeasure (volume.restrict (centralInterval a)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, centralInterval]
    exact measure_Icc_lt_top
  have hmem : MemLp ((f : ℝ → ℂ)) 2 (volume.restrict (centralInterval a)) :=
    (Lp.memLp f).restrict (centralInterval a)
  have hsq : (∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖ ^ 2) ≤ ‖f‖ ^ 2 :=
    integral_norm_sq_le_norm_sq f (centralInterval a)
  have hone : Integrable (fun _ : ℝ => ((1 : ℝ)) ^ 2) (volume.restrict (centralInterval a)) := by
    simpa using (integrable_const (1 : ℝ) (μ := volume.restrict (centralInterval a)))
  have hcs : (∫ t in centralInterval a, (1 : ℝ) * ‖(f : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ _t in centralInterval a, ((1 : ℝ)) ^ 2)
        * ∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖ ^ 2 :=
    sq_integral_mul_le aestronglyMeasurable_const hmem.1.norm hone
      ((memLp_two_iff_integrable_sq_norm hmem.1).1 hmem)
  have hmeas : (∫ _t in centralInterval a, ((1 : ℝ)) ^ 2) = 2 * a := by
    simp only [one_pow]
    rw [setIntegral_const, centralInterval, Real.volume_real_Icc,
      max_eq_left (by linarith : (0:ℝ) ≤ a - -a)]
    simp
    ring
  have hone_mul : (∫ t in centralInterval a, (1 : ℝ) * ‖(f : ℝ → ℂ) t‖)
      = ∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖ := by
    refine setIntegral_congr_fun (measurableSet_centralInterval a) fun t _ => ?_
    ring
  rw [hone_mul, hmeas] at hcs
  have hnn : (0 : ℝ) ≤ ∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖ :=
    setIntegral_nonneg (measurableSet_centralInterval a) fun t _ => norm_nonneg _
  have hrhs : (Real.sqrt (2 * a) * ‖f‖) ^ 2 = (2 * a) * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h2a.le]
  have hX2 : (∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖) ^ 2
      ≤ (Real.sqrt (2 * a) * ‖f‖) ^ 2 := by
    rw [hrhs]
    calc (∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖) ^ 2
        ≤ (2 * a) * ∫ t in centralInterval a, ‖(f : ℝ → ℂ) t‖ ^ 2 := hcs
      _ ≤ (2 * a) * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left hsq h2a.le
  have hR0 : (0 : ℝ) ≤ Real.sqrt (2 * a) * ‖f‖ := by positivity
  nlinarith [hX2, hnn, hR0]

theorem norm_soninBandConst_le {a : ℝ} (ha : 0 < a) (f : SoninL2) :
    ‖soninBandConst a f‖ ≤ (1 / (2 * a)) * (Real.sqrt (2 * a) * ‖f‖) := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have hnorm : ‖(1 / (2 * a) : ℂ)‖ = 1 / (2 * a) := by
    rw [show ((1 : ℂ) / (2 * a)) = (((1 / (2 * a) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [soninBandConst, norm_mul, hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_integral_le_integral_norm _) ?_
  exact integral_norm_le_sqrt_measure ha f

/-! ## The evaluator right of the critical line -/

theorem norm_tail_cpow_le {b : ℝ} (hb : 0 < b) (g : SoninL2) {w : ℂ} (hw : 1 / 2 < w.re) :
    ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-w) * (g : ℝ → ℂ) t‖
      ≤ Real.sqrt (b ^ (1 - 2 * w.re) / (2 * w.re - 1)) * ‖g‖ := by
  have h2σ : (0 : ℝ) < 2 * w.re - 1 := by linarith
  have hg2 : Integrable (fun t : ℝ => ‖(g : ℝ → ℂ) t‖ ^ 2) (volume.restrict (Ioi b)) := by
    have h := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).1 (Lp.memLp g)
    exact h.restrict
  have hsqeq : ∀ t : ℝ, 0 < t → (t ^ (-w.re)) ^ 2 = t ^ (-(2 * w.re)) := by
    intro t ht0
    rw [← Real.rpow_natCast (t ^ (-w.re)) 2, ← Real.rpow_mul ht0.le]
    norm_num
    ring_nf
  have hwsq : Integrable (fun t : ℝ => (t ^ (-w.re)) ^ 2) (volume.restrict (Ioi b)) := by
    have hrw : (fun t : ℝ => (t ^ (-w.re)) ^ 2)
        =ᵐ[volume.restrict (Ioi b)] fun t : ℝ => t ^ (-(2 * w.re)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hsqeq t (lt_trans hb ht)
    refine Integrable.congr ?_ hrw.symm
    exact integrableOn_Ioi_rpow_of_lt (a := -(2 * w.re)) (by linarith) hb
  have hcontOn : ContinuousOn (fun t : ℝ => t ^ (-w.re)) (Ioi b) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    exact (Real.continuousAt_rpow_const t (-w.re) (Or.inl (ne_of_gt ht0))).continuousWithinAt
  have hval : (∫ t in Ioi b, (t ^ (-w.re)) ^ 2) = b ^ (1 - 2 * w.re) / (2 * w.re - 1) := by
    have hrw : (∫ t in Ioi b, (t ^ (-w.re)) ^ 2) = ∫ t in Ioi b, t ^ (-(2 * w.re)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      exact hsqeq t (lt_trans hb ht)
    rw [hrw, integral_Ioi_rpow_of_lt (by linarith) hb,
      show -(2 * w.re) + 1 = 1 - 2 * w.re from by ring]
    have h1 : (1 : ℝ) - 2 * w.re ≠ 0 := by intro h; linarith
    have h2 : (2 : ℝ) * w.re - 1 ≠ 0 := by intro h; linarith
    field_simp
    ring
  set K : ℝ := b ^ (1 - 2 * w.re) / (2 * w.re - 1) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  have hcs : (∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ t in Ioi b, (t ^ (-w.re)) ^ 2) * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 :=
    sq_integral_mul_le (hcontOn.aestronglyMeasurable measurableSet_Ioi)
      (((Lp.memLp g).1.norm).restrict) hwsq hg2
  have hX0 : 0 ≤ ∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖ := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    positivity
  have hbound : (∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖) ≤ Real.sqrt K * ‖g‖ := by
    have hsq : (∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖) ^ 2 ≤ (Real.sqrt K * ‖g‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0]
      calc (∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖) ^ 2
          ≤ K * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 := by rw [hval] at hcs; exact hcs
        _ ≤ K * ‖g‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (integral_norm_sq_le_norm_sq g (Ioi b)) hK0
    have hrhs0 : (0 : ℝ) ≤ Real.sqrt K * ‖g‖ := by positivity
    nlinarith [hsq, hX0, hrhs0]
  have hpt : ∀ t ∈ Ioi b, ‖((t : ℝ) : ℂ) ^ (-w) * (g : ℝ → ℂ) t‖
      = t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    congr 2
  calc ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-w) * (g : ℝ → ℂ) t‖
      ≤ ∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-w) * (g : ℝ → ℂ) t‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t in Ioi b, t ^ (-w.re) * ‖(g : ℝ → ℂ) t‖ :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ ≤ Real.sqrt K * ‖g‖ := hbound

/-! ## The evaluator as a bounded functional -/

theorem ae_eq_soninBandConst {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a →
      (f : ℝ → ℂ) t = soninBandConst a f := by
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hf
  rw [soninBandConst_eq ha hd]
  exact hd

theorem integrableOn_full_of_mem {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t) (Ioi (0 : ℝ)) volume :=
  integrableOn_cpow_mul_Ioi_zero ha (ae_eq_soninBandConst ha hf) hw1 hw2

theorem soninMellinIntegral_split {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    soninMellinIntegral f w
      = soninBandConst a f * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - w) / (1 - w)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t := by
  have hhead : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)),
      (f : ℝ → ℂ) t = soninBandConst a f := by
    filter_upwards [ae_restrict_of_ae (ae_eq_soninBandConst ha hf),
      self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := a))] with t ht hmem
    refine ht ?_
    rcases hmem with ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩
  have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t)
      (Ioc (0 : ℝ) a) volume := by
    refine (integrableOn_head_cpow ha hw2 (soninBandConst a f)).congr_fun_ae ?_
    filter_upwards [hhead] with t ht
    rw [ht]
  have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t)
      (Ioi a) volume := integrableOn_cpow_mul_Ioi ha f hw1
  have hsplit : soninMellinIntegral f w
      = (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t := by
    rw [soninMellinIntegral, ← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2
  have hheadval : (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t)
      = soninBandConst a f * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - w) / (1 - w) := by
    rw [← integral_head_cpow_Ioc ha hw2 (soninBandConst a f)]
    refine integral_congr_ae ?_
    filter_upwards [hhead] with t ht
    rw [ht]
  rw [hsplit, hheadval]

/-- **The evaluator is bounded right of the critical line.** -/
theorem norm_soninMellinIntegral_le {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier a) {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    ‖soninMellinIntegral f w‖
      ≤ (a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a))
          + Real.sqrt (a ^ (1 - 2 * w.re) / (2 * w.re - 1))) * ‖f‖ := by
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw0 : (0 : ℝ) < ‖(1 : ℂ) - w‖ := by
    rw [norm_pos_iff]
    exact h1w
  rw [soninMellinIntegral_split ha hf hw1 hw2]
  refine le_trans (norm_add_le _ _) ?_
  have hhead : ‖soninBandConst a f * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - w) / (1 - w)‖
      ≤ a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a)) * ‖f‖ := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
    have hre : ((1 : ℂ) - w).re = 1 - w.re := by
      rw [Complex.sub_re]
      simp
    rw [hre, div_le_iff₀ hw0]
    have hb := norm_soninBandConst_le ha f
    have hpow : (0 : ℝ) < a ^ (1 - w.re) := Real.rpow_pos_of_pos ha _
    have hcancel : a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a)) * ‖f‖
          * ‖(1 : ℂ) - w‖
        = a ^ (1 - w.re) * ((1 / (2 * a)) * (Real.sqrt (2 * a) * ‖f‖)) := by
      field_simp
    rw [hcancel]
    calc ‖soninBandConst a f‖ * a ^ (1 - w.re)
        ≤ ((1 / (2 * a)) * (Real.sqrt (2 * a) * ‖f‖)) * a ^ (1 - w.re) :=
          mul_le_mul_of_nonneg_right hb hpow.le
      _ = a ^ (1 - w.re) * ((1 / (2 * a)) * (Real.sqrt (2 * a) * ‖f‖)) := by ring
  have htail := norm_tail_cpow_le ha f hw1
  have hpow0 : (0 : ℝ) ≤ a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a)) := by
    have : (0 : ℝ) < a ^ (1 - w.re) := Real.rpow_pos_of_pos ha _
    positivity
  have hexpand : (a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a))
        + Real.sqrt (a ^ (1 - 2 * w.re) / (2 * w.re - 1))) * ‖f‖
      = a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a)) * ‖f‖
        + Real.sqrt (a ^ (1 - 2 * w.re) / (2 * w.re - 1)) * ‖f‖ := by ring
  rw [hexpand]
  exact add_le_add hhead htail

/-! ## The evaluator as a continuous linear functional -/

/-- The cosine-side aperture constant. -/
def soninFourierBandConst (a : ℝ) (f : SoninL2) : ℂ := soninBandConst a (fourierUnitary f)

/-- The continued Mellin transform of a vector of `L_a`, with the aperture constants read off the
vector itself. -/
def soninEval (a : ℝ) (f : SoninL2) (w : ℂ) : ℂ :=
  extendedMellinContinuation a (soninFourierBandConst a f) (soninBandConst a f) f w

theorem soninEval_eq_soninMellinIntegral {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hmem : f ∈ centralSoninExtendedCarrier a) (hev : f ∈ evenSubspace)
    {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    soninEval a f w = soninMellinIntegral f w := by
  have hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = soninFourierBandConst a f := by
    obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hmem
    have : soninFourierBandConst a f = c := by
      rw [soninFourierBandConst]
      exact soninBandConst_eq ha hc
    rw [this]
    exact hc
  exact extendedMellinContinuation_eq_soninMellinIntegral ha hev hc
    (ae_eq_soninBandConst ha hmem) hw1 hw2

theorem soninEval_analyticAt {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hmem : f ∈ centralSoninExtendedCarrier a) (hev : f ∈ evenSubspace)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    AnalyticAt ℂ (soninEval a f) w := by
  have hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = soninFourierBandConst a f := by
    obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hmem
    have hcc : soninFourierBandConst a f = c := by
      rw [soninFourierBandConst]
      exact soninBandConst_eq ha hc
    rw [hcc]
    exact hc
  have hw0' : w ≠ 0 := by intro h; rw [h] at hw0; norm_num at hw0
  have hw1' : w ≠ 1 := by intro h; rw [h] at hw1; norm_num at hw1
  exact analyticAt_extendedMellinContinuation_of_ne ha hev hc
    (ae_eq_soninBandConst ha hmem) hw0' hw1'

/-- The evaluator right of the critical line, as a linear functional. -/
def soninEvaluatorRightLinear {a : ℝ} (ha : 0 < a) {w : ℂ} (hw1 : 1 / 2 < w.re)
    (hw2 : w.re < 1) : soninEvenExtended a →ₗ[ℂ] ℂ where
  toFun f := soninMellinIntegral ((f : SoninL2)) w
  map_add' f g := by
    have hf := integrableOn_full_of_mem ha f.property.1 hw1 hw2
    have hg := integrableOn_full_of_mem ha g.property.1 hw1 hw2
    show soninMellinIntegral ((f + g : soninEvenExtended a) : SoninL2) w
      = soninMellinIntegral ((f : SoninL2)) w + soninMellinIntegral ((g : SoninL2)) w
    rw [soninMellinIntegral, soninMellinIntegral, soninMellinIntegral,
      ← MeasureTheory.integral_add hf hg]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [Lp.coeFn_add ((f : SoninL2)) ((g : SoninL2))] with t ht _
    show ((t : ℝ) : ℂ) ^ (-w) * (((f : SoninL2) + (g : SoninL2) : SoninL2) : ℝ → ℂ) t = _
    rw [ht, Pi.add_apply]
    ring
  map_smul' k f := by
    have hf := integrableOn_full_of_mem ha f.property.1 hw1 hw2
    show soninMellinIntegral ((k • f : soninEvenExtended a) : SoninL2) w
      = k * soninMellinIntegral ((f : SoninL2)) w
    rw [soninMellinIntegral, soninMellinIntegral, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [Lp.coeFn_smul k ((f : SoninL2))] with t ht _
    show ((t : ℝ) : ℂ) ^ (-w) * ((k • (f : SoninL2) : SoninL2) : ℝ → ℂ) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The evaluator is a bounded functional right of the critical line.** -/
def soninEvaluatorRight {a : ℝ} (ha : 0 < a) {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    soninEvenExtended a →L[ℂ] ℂ :=
  (soninEvaluatorRightLinear ha hw1 hw2).mkContinuous
    (a ^ (1 - w.re) / ‖(1 : ℂ) - w‖ * ((1 / (2 * a)) * Real.sqrt (2 * a))
      + Real.sqrt (a ^ (1 - 2 * w.re) / (2 * w.re - 1)))
    (fun f => by
      have h := norm_soninMellinIntegral_le ha f.property.1 hw1 hw2
      exact h)

@[simp] theorem soninEvaluatorRight_apply {a : ℝ} (ha : 0 < a) {w : ℂ} (hw1 : 1 / 2 < w.re)
    (hw2 : w.re < 1) (f : soninEvenExtended a) :
    soninEvaluatorRight ha hw1 hw2 f = soninMellinIntegral ((f : SoninL2)) w := rfl

theorem soninEvaluatorRight_eq_soninEval {a : ℝ} (ha : 0 < a) {w : ℂ} (hw1 : 1 / 2 < w.re)
    (hw2 : w.re < 1) (f : soninEvenExtended a) :
    soninEvaluatorRight ha hw1 hw2 f = soninEval a (f : SoninL2) w :=
  (soninEval_eq_soninMellinIntegral ha f.property.1 f.property.2 hw1 hw2).symm

/-! ## Across the critical line, by Banach–Steinhaus -/

/-- **The evaluator on the closed right half of the strip.**  On the critical line the head/tail
bound degenerates; Banach–Steinhaus supplies boundedness from the pointwise limit. -/
theorem exists_soninEvaluator_mid {a : ℝ} (ha : 0 < a) {w : ℂ} (hw1 : 1 / 2 ≤ w.re)
    (hw2 : w.re < 1) :
    ∃ Λ : soninEvenExtended a →L[ℂ] ℂ,
      ∀ f : soninEvenExtended a, Λ f = soninEval a ((f : SoninL2)) w := by
  classical
  set δ : ℝ := 1 - w.re with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set wn : ℕ → ℂ := fun n => w + ((δ / ((n : ℝ) + 2) : ℝ) : ℂ) with hwn
  have hre : ∀ n : ℕ, (wn n).re = w.re + δ / ((n : ℝ) + 2) := by
    intro n
    simp only [hwn, Complex.add_re, Complex.ofReal_re]
  have hpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact div_pos hδ0 this
  have hlt : ∀ n : ℕ, δ / ((n : ℝ) + 2) < δ := by
    intro n
    have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hn1 : ∀ n : ℕ, 1 / 2 < (wn n).re := by
    intro n
    rw [hre]
    linarith [hpos n]
  have hn2 : ∀ n : ℕ, (wn n).re < 1 := by
    intro n
    rw [hre, hδ] at *
    linarith [hlt n]
  have hwlim : Filter.Tendsto wn Filter.atTop (𝓝 w) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ)) Filter.atTop (𝓝 0) := by
      have hr : Filter.Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact (Complex.continuous_ofReal.tendsto 0).comp hr
    have h2 := tendsto_const_nhds (x := w) (f := Filter.atTop (α := ℕ)) |>.add h1
    simpa [hwn] using h2
  have hlim : Filter.Tendsto
      (fun n : ℕ => ((soninEvaluatorRight ha (hn1 n) (hn2 n) : soninEvenExtended a →L[ℂ] ℂ) :
        soninEvenExtended a → ℂ)) Filter.atTop
      (𝓝 (fun f : soninEvenExtended a => soninEval a ((f : SoninL2)) w)) := by
    refine tendsto_pi_nhds.2 fun f => ?_
    have hcont : ContinuousAt (soninEval a ((f : SoninL2))) w :=
      (soninEval_analyticAt ha f.property.1 f.property.2 (by linarith) hw2).continuousAt
    have hcomp := hcont.tendsto.comp hwlim
    refine hcomp.congr fun n => ?_
    exact (soninEvaluatorRight_eq_soninEval ha (hn1 n) (hn2 n) f).symm
  exact ⟨continuousLinearMapOfTendsto _ hlim, fun f => rfl⟩

/-! ## Left of the critical line, by the functional equation -/

theorem fourierUnitary_mem_soninEvenExtended {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ soninEvenExtended a) : fourierUnitary f ∈ soninEvenExtended a := by
  obtain ⟨hmem, hev⟩ := hf
  refine ⟨?_, fourierUnitary_mem_evenSubspace hev⟩
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hmem
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hmem
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  refine (mem_centralSoninExtendedCarrier_iff _).2 ⟨⟨c, hc⟩, ⟨d, ?_⟩⟩
  rw [hff]
  exact hd

/-- The cosine transform as an operator on the even part of `L_a`. -/
def soninFourierCLM {a : ℝ} (ha : 0 < a) : soninEvenExtended a →L[ℂ] soninEvenExtended a :=
  ContinuousLinearMap.codRestrict
    ((fourierUnitary.toLinearIsometry.toContinuousLinearMap).comp
      (soninEvenExtended a).subtypeL)
    (soninEvenExtended a) (fun f => fourierUnitary_mem_soninEvenExtended ha f.property)

@[simp] theorem soninFourierCLM_apply {a : ℝ} (ha : 0 < a) (f : soninEvenExtended a) :
    ((soninFourierCLM ha f : soninEvenExtended a) : SoninL2) = fourierUnitary ((f : SoninL2)) :=
  rfl

theorem soninEval_reflect {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hmem : f ∈ centralSoninExtendedCarrier a) (hev : f ∈ evenSubspace)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolChiFactor (1 - w) * soninEval a f w
      = soninEval a (fourierUnitary f) (1 - w) := by
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hcf : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = soninFourierBandConst a f := by
    obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hmem
    have hcc : soninFourierBandConst a f = c := by
      rw [soninFourierBandConst]
      exact soninBandConst_eq ha hc
    rw [hcc]
    exact hc
  have hdf := ae_eq_soninBandConst ha hmem
  have hre : ((1 : ℂ) - w).re = 1 - w.re := by
    rw [Complex.sub_re]
    simp
  have hs1 : 0 < ((1 : ℂ) - w).re := by rw [hre]; linarith
  have hs2 : ((1 : ℂ) - w).re < 1 := by rw [hre]; linarith
  have hkey := chi_mul_extendedMellinContinuation_one_sub ha hev hcf hdf hs1 hs2
  rw [show (1 : ℂ) - ((1 : ℂ) - w) = w from by ring] at hkey
  -- identify the two aperture constants of the cosine transform
  have hc' : soninFourierBandConst a (fourierUnitary f) = soninBandConst a f := by
    rw [soninFourierBandConst, hff]
  have hd' : soninBandConst a (fourierUnitary f) = soninFourierBandConst a f := by
    rw [soninFourierBandConst]
  rw [soninEval, soninEval, hc', hd']
  exact hkey

/-- **The evaluator exists and is bounded at every point of the open critical strip.**  This is the
continuity of Burnol's evaluations (Theorem 2.1) in the extended space. -/
theorem exists_soninEvaluator {a : ℝ} (ha : 0 < a) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    ∃ Λ : soninEvenExtended a →L[ℂ] ℂ,
      ∀ f : soninEvenExtended a, Λ f = soninEval a ((f : SoninL2)) w := by
  by_cases hmid : 1 / 2 ≤ w.re
  · exact exists_soninEvaluator_mid ha hmid hw1
  · push Not at hmid
    have hre : ((1 : ℂ) - w).re = 1 - w.re := by
      rw [Complex.sub_re]
      simp
    have hs1 : 1 / 2 ≤ ((1 : ℂ) - w).re := by rw [hre]; linarith
    have hs2 : ((1 : ℂ) - w).re < 1 := by rw [hre]; linarith
    obtain ⟨Λ₁, hΛ₁⟩ := exists_soninEvaluator_mid ha hs1 hs2
    have hchi : burnolChiFactor ((1 : ℂ) - w) ≠ 0 := by
      refine burnolChiFactor_ne_zero ?_
      intro m hm
      have hrew : ((1 : ℂ) - w).re = (m : ℝ) := by rw [hm]; simp
      rw [hre] at hrew
      have hm0 : (0 : ℤ) < m := by
        have : (0 : ℝ) < (m : ℝ) := by rw [← hrew]; linarith
        exact_mod_cast this
      have hm1 : m < (1 : ℤ) := by
        have : ((m : ℝ)) < 1 := by rw [← hrew]; linarith
        exact_mod_cast this
      omega
    refine ⟨(burnolChiFactor ((1 : ℂ) - w))⁻¹ • (Λ₁.comp (soninFourierCLM ha)), fun f => ?_⟩
    have hval : Λ₁ (soninFourierCLM ha f) = soninEval a (fourierUnitary ((f : SoninL2))) (1 - w) :=
      hΛ₁ _
    have hrefl := soninEval_reflect ha f.property.1 f.property.2 hw0 hw1
    show (burnolChiFactor ((1 : ℂ) - w))⁻¹ * Λ₁ (soninFourierCLM ha f) = _
    rw [hval, ← hrefl, ← mul_assoc, inv_mul_cancel₀ hchi, one_mul]

/-! ## The jet evaluators -/

theorem analyticOnNhd_iteratedDeriv_soninEval {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hmem : f ∈ centralSoninExtendedCarrier a) (hev : f ∈ evenSubspace) (k : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv k (soninEval a f)) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  induction k with
  | zero =>
      intro z hz
      simpa using soninEval_analyticAt ha hmem hev hz.1 hz.2
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- **The jet evaluators are bounded at every point of the open critical strip.**  Each is the
Banach–Steinhaus limit of the difference quotients of the previous one. -/
theorem exists_soninEvaluatorJet {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∀ {w : ℂ}, 0 < w.re → w.re < 1 →
      ∃ Λ : soninEvenExtended a →L[ℂ] ℂ,
        ∀ f : soninEvenExtended a,
          Λ f = iteratedDeriv k (soninEval a ((f : SoninL2))) w := by
  induction k with
  | zero =>
      intro w hw0 hw1
      obtain ⟨Λ, hΛ⟩ := exists_soninEvaluator ha hw0 hw1
      refine ⟨Λ, fun f => ?_⟩
      simpa using hΛ f
  | succ k ih =>
      intro w hw0 hw1
      classical
      set δ : ℝ := 1 - w.re with hδ
      have hδ0 : 0 < δ := by rw [hδ]; linarith
      set h : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2) with hhdef
      have hpos : ∀ n : ℕ, 0 < h n := by
        intro n
        rw [hhdef]
        have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        exact div_pos hδ0 this
      have hlt : ∀ n : ℕ, h n < δ := by
        intro n
        rw [hhdef, div_lt_iff₀ (by positivity)]
        have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith
      have hn0 : ∀ n : ℕ, 0 < (w + ((h n : ℝ) : ℂ)).re := by
        intro n
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hpos n]
      have hn1 : ∀ n : ℕ, (w + ((h n : ℝ) : ℂ)).re < 1 := by
        intro n
        simp only [Complex.add_re, Complex.ofReal_re]
        have := hlt n
        rw [hδ] at this
        linarith
      choose Λn hΛn using fun n : ℕ => ih (hn0 n) (hn1 n)
      obtain ⟨Λ0, hΛ0⟩ := ih hw0 hw1
      set G : ℕ → (soninEvenExtended a →L[ℂ] ℂ) :=
        fun n => (((h n : ℝ) : ℂ))⁻¹ • (Λn n - Λ0) with hGdef
      have hzero : ∀ n : ℕ, ((h n : ℝ) : ℂ) ≠ 0 := by
        intro n
        exact_mod_cast ne_of_gt (hpos n)
      have hlim : Filter.Tendsto (fun n : ℕ => ((G n : soninEvenExtended a →L[ℂ] ℂ) :
          soninEvenExtended a → ℂ)) Filter.atTop
          (𝓝 (fun f : soninEvenExtended a =>
            iteratedDeriv (k + 1) (soninEval a ((f : SoninL2))) w)) := by
        refine tendsto_pi_nhds.2 fun f => ?_
        set g : ℂ → ℂ := iteratedDeriv k (soninEval a ((f : SoninL2))) with hg
        have hana : AnalyticAt ℂ g w :=
          analyticOnNhd_iteratedDeriv_soninEval ha f.property.1 f.property.2 k w ⟨hw0, hw1⟩
        have hderiv : HasDerivAt g (deriv g w) w := hana.differentiableAt.hasDerivAt
        have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
        have hstep : Filter.Tendsto (fun n : ℕ => w + ((h n : ℝ) : ℂ))
            Filter.atTop (𝓝[≠] w) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · have hr : Filter.Tendsto (fun n : ℕ => ((h n : ℝ) : ℂ)) Filter.atTop (𝓝 0) := by
              have hreal : Filter.Tendsto h Filter.atTop (𝓝 0) := by
                rw [hhdef]
                refine tendsto_const_nhds.div_atTop ?_
                exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
              exact (Complex.continuous_ofReal.tendsto 0).comp hreal
            have := tendsto_const_nhds (x := w) (f := Filter.atTop (α := ℕ)) |>.add hr
            simpa using this
          · filter_upwards with n
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro hcon
            exact hzero n (by linear_combination hcon)
        have hcomp := hslope.comp hstep
        rw [iteratedDeriv_succ]
        refine hcomp.congr fun n => ?_
        show slope g w (w + ((h n : ℝ) : ℂ)) = (G n) f
        rw [slope_def_field]
        simp only [hGdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
          smul_eq_mul, hΛn n f, hΛ0 f]
        rw [show (w + ((h n : ℝ) : ℂ)) - w = ((h n : ℝ) : ℂ) from by ring, div_eq_inv_mul]
      exact ⟨continuousLinearMapOfTendsto _ hlim, fun f => rfl⟩

/-! ## Jets of a multiplied transform -/

theorem analyticOnNhd_iteratedDeriv_mul {a : ℝ} (ha : 0 < a) {U : Set ℂ}
    (hUsub : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1}) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h U)
    {f : SoninL2} (hmem : f ∈ centralSoninExtendedCarrier a) (hev : f ∈ evenSubspace) (k : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv k (fun s : ℂ => soninEval a f s * h s)) U := by
  induction k with
  | zero =>
      intro z hz
      have hz' := hUsub hz
      have hprod : AnalyticAt ℂ (fun s : ℂ => soninEval a f s * h s) z :=
        AnalyticAt.mul (soninEval_analyticAt ha hmem hev hz'.1 hz'.2) (hh z hz)
      rw [iteratedDeriv_zero]
      exact hprod
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- **The jet evaluators of a multiplied transform.**  For any multiplier analytic on an open
subset `U` of the strip, `f ↦ (M(f)·h)^{(k)}(w)` is a bounded functional at every `w ∈ U`. -/
theorem exists_soninEvaluatorJetMul {a : ℝ} (ha : 0 < a) {U : Set ℂ} (hU : IsOpen U)
    (hUsub : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1}) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h U) (k : ℕ) :
    ∀ {w : ℂ}, w ∈ U →
      ∃ Λ : soninEvenExtended a →L[ℂ] ℂ,
        ∀ f : soninEvenExtended a,
          Λ f = iteratedDeriv k (fun s : ℂ => soninEval a ((f : SoninL2)) s * h s) w := by
  induction k with
  | zero =>
      intro w hw
      obtain ⟨hw0, hw1⟩ := hUsub hw
      obtain ⟨Λ, hΛ⟩ := exists_soninEvaluator ha hw0 hw1
      refine ⟨h w • Λ, fun f => ?_⟩
      show h w * Λ f = _
      rw [hΛ f]
      simp [mul_comm]
  | succ k ih =>
      intro w hw
      classical
      obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.1 hU w hw
      set hs : ℕ → ℝ := fun n => ε / ((n : ℝ) + 2) with hsdef
      have hpos : ∀ n : ℕ, 0 < hs n := by
        intro n
        rw [hsdef]
        exact div_pos hε0 (by positivity)
      have hlt : ∀ n : ℕ, hs n < ε := by
        intro n
        rw [hsdef, div_lt_iff₀ (by positivity)]
        have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith
      have hmemU : ∀ n : ℕ, w + ((hs n : ℝ) : ℂ) ∈ U := by
        intro n
        refine hball ?_
        rw [Metric.mem_ball, dist_eq_norm]
        have : w + ((hs n : ℝ) : ℂ) - w = ((hs n : ℝ) : ℂ) := by ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
        exact hlt n
      choose Λn hΛn using fun n : ℕ => ih (hmemU n)
      obtain ⟨Λ0, hΛ0⟩ := ih hw
      set G : ℕ → (soninEvenExtended a →L[ℂ] ℂ) :=
        fun n => (((hs n : ℝ) : ℂ))⁻¹ • (Λn n - Λ0) with hGdef
      have hzero : ∀ n : ℕ, ((hs n : ℝ) : ℂ) ≠ 0 := by
        intro n
        exact_mod_cast ne_of_gt (hpos n)
      have hlim : Filter.Tendsto (fun n : ℕ => ((G n : soninEvenExtended a →L[ℂ] ℂ) :
          soninEvenExtended a → ℂ)) Filter.atTop
          (𝓝 (fun f : soninEvenExtended a =>
            iteratedDeriv (k + 1) (fun s : ℂ => soninEval a ((f : SoninL2)) s * h s) w)) := by
        refine tendsto_pi_nhds.2 fun f => ?_
        set g : ℂ → ℂ :=
          iteratedDeriv k (fun s : ℂ => soninEval a ((f : SoninL2)) s * h s) with hg
        have hana : AnalyticAt ℂ g w :=
          analyticOnNhd_iteratedDeriv_mul ha hUsub hh f.property.1 f.property.2 k w hw
        have hderiv : HasDerivAt g (deriv g w) w := hana.differentiableAt.hasDerivAt
        have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
        have hstep : Filter.Tendsto (fun n : ℕ => w + ((hs n : ℝ) : ℂ))
            Filter.atTop (𝓝[≠] w) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · have hr : Filter.Tendsto (fun n : ℕ => ((hs n : ℝ) : ℂ)) Filter.atTop (𝓝 0) := by
              have hreal : Filter.Tendsto hs Filter.atTop (𝓝 0) := by
                rw [hsdef]
                refine tendsto_const_nhds.div_atTop ?_
                exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
              exact (Complex.continuous_ofReal.tendsto 0).comp hreal
            have := tendsto_const_nhds (x := w) (f := Filter.atTop (α := ℕ)) |>.add hr
            simpa using this
          · filter_upwards with n
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro hcon
            exact hzero n (by linear_combination hcon)
        have hcomp := hslope.comp hstep
        rw [iteratedDeriv_succ]
        refine hcomp.congr fun n => ?_
        show slope g w (w + ((hs n : ℝ) : ℂ)) = (G n) f
        rw [slope_def_field]
        simp only [hGdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
          smul_eq_mul, hΛn n f, hΛ0 f]
        rw [show (w + ((hs n : ℝ) : ℂ)) - w = ((hs n : ℝ) : ℂ) from by ring, div_eq_inv_mul]
      exact ⟨continuousLinearMapOfTendsto _ hlim, fun f => rfl⟩

end

end RHTower
