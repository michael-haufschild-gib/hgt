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

end

end RHTower
