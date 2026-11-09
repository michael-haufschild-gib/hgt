import GaloisForLFunctions.EulerFETransportTheory.TheGaussianRateMeasureIsLocallyVisible
import GaloisForLFunctions.EulerFETransportTheory.TheCausalGaussianDefect

/-!
# Recovery of full causal measures from the Gaussian differential defect

Gaussian damping admits sources of infinite total mass, including infinite
atomic Euler operators. The exact rate chart turns their literal Gaussian
responses into finite-measure Laplace transforms. Local differential data
recover the original measure away from zero; the only invisible direction is
the scalar identity atom.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

/-- The Gaussian weight making the complete causal source finite. -/
def gaussianSourceWeight (t : ℝ) : ℝ := Real.exp (t / 2 - gaussianCausalRate t)

@[fun_prop] theorem continuous_gaussianSourceWeight : Continuous gaussianSourceWeight := by
  unfold gaussianSourceWeight
  fun_prop

theorem gaussianSourceWeight_pos (t : ℝ) : 0 < gaussianSourceWeight t := Real.exp_pos _

/-- Gaussian-damped source pushed into the rate coordinate. -/
def gaussianSourceMeasure (μ : Measure ℝ) : Measure ℝ :=
  Measure.map gaussianCausalRate
    (μ.withDensity (fun t => ENNReal.ofReal (gaussianSourceWeight t)))

/-- Literal outward translation by a possibly infinite causal measure. -/
def causalGaussianMeasureResponse (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, _root_.RHTower.thetaGaussBase (x + t) ∂μ

/-- The first-order Gaussian equation applied to the actual response. -/
def causalGaussianMeasureDefect (μ : Measure ℝ) (x : ℝ) : ℝ :=
  deriv (causalGaussianMeasureResponse μ) x -
    _root_.RHTower.gaussBaseCoeff x * causalGaussianMeasureResponse μ x

theorem gaussianWeightedSource_finite {μ : Measure ℝ}
    (hμ : Integrable gaussianSourceWeight μ) :
    IsFiniteMeasure (μ.withDensity (fun t => ENNReal.ofReal (gaussianSourceWeight t))) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  have hf : ∫⁻ t, ‖gaussianSourceWeight t‖ₑ ∂μ < ⊤ := hμ.2
  simpa only [Real.enorm_eq_ofReal_abs,
    abs_of_pos (gaussianSourceWeight_pos _)] using hf

theorem gaussianSourceMeasure_finite {μ : Measure ℝ}
    (hμ : Integrable gaussianSourceWeight μ) : IsFiniteMeasure (gaussianSourceMeasure μ) := by
  letI := gaussianWeightedSource_finite hμ
  exact Measure.isFiniteMeasure_map _ _

theorem gaussianCausalRate_nonneg_iff (t : ℝ) : 0 ≤ gaussianCausalRate t ↔ 0 ≤ t := by
  rw [gaussianCausalRate, sub_nonneg, Real.one_le_exp_iff]
  constructor <;> intro h <;> linarith

theorem gaussianCausalRate_pos_iff (t : ℝ) : 0 < gaussianCausalRate t ↔ 0 < t := by
  rw [gaussianCausalRate, sub_pos, Real.one_lt_exp_iff]
  constructor <;> intro h <;> linarith

theorem gaussianSourceMeasure_causal {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) : gaussianSourceMeasure μ (Ici (0 : ℝ))ᶜ = 0 := by
  rw [gaussianSourceMeasure,
    Measure.map_apply continuous_gaussianCausalRate.measurable measurableSet_Ici.compl]
  have he : gaussianCausalRate ⁻¹' (Ici (0 : ℝ))ᶜ = (Ici (0 : ℝ))ᶜ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_Ici, gaussianCausalRate_nonneg_iff]
  rw [he]
  exact withDensity_absolutelyContinuous _ _ hμ

theorem gaussianSourceWeight_translation (x t : ℝ) :
    gaussianSourceWeight t * Real.exp (-(Real.pi * Real.exp (2 * x) - 1) *
      gaussianCausalRate t) * _root_.RHTower.thetaGaussBase x =
        _root_.RHTower.thetaGaussBase (x + t) := by
  rw [_root_.RHTower.thetaGaussBase_add, gaussianSourceWeight, ← Real.exp_add]
  congr 2
  unfold gaussianCausalRate
  ring

/-- Exact full-measure transport; no truncation or absolute mass bound. -/
theorem causalGaussianMeasureResponse_eq_laplace (μ : Measure ℝ) (x : ℝ) :
    causalGaussianMeasureResponse μ x = _root_.RHTower.thetaGaussBase x *
      gaussianMeasureLaplace (gaussianSourceMeasure μ) (Real.pi * Real.exp (2 * x) - 1) := by
  rw [gaussianMeasureLaplace, gaussianSourceMeasure,
    integral_map continuous_gaussianCausalRate.measurable.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (gaussianSourceWeight_pos t).le, smul_eq_mul]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (gaussianSourceWeight_translation x t).symm

theorem integrable_causalGaussianMeasureResponse {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hw : Integrable gaussianSourceWeight μ)
    {x : ℝ} (hx : 1 < Real.pi * Real.exp (2 * x)) :
    Integrable (fun t => _root_.RHTower.thetaGaussBase (x + t)) μ := by
  letI := gaussianSourceMeasure_finite hw
  have hi := integrable_gaussianMeasureLaplace (gaussianSourceMeasure μ)
    (gaussianSourceMeasure_causal hμ) (sub_pos.2 hx).le
  rw [gaussianSourceMeasure] at hi
  have hm := (integrable_map_measure (by fun_prop)
    continuous_gaussianCausalRate.measurable.aemeasurable).1 hi
  have hd := (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hm
  refine (hd.const_mul (_root_.RHTower.thetaGaussBase x)).congr ?_
  filter_upwards with t
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (gaussianSourceWeight_pos t).le]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using gaussianSourceWeight_translation x t

/-- The derivative is obtained from the finite rate measure, so no undamped
moment or finite total source mass is required. -/
theorem hasDerivAt_causalGaussianMeasureResponse {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hw : Integrable gaussianSourceWeight μ)
    {x : ℝ} (hx : 1 < Real.pi * Real.exp (2 * x)) :
    HasDerivAt (causalGaussianMeasureResponse μ)
      (_root_.RHTower.gaussBaseCoeff x * causalGaussianMeasureResponse μ x -
        2 * Real.pi * Real.exp (2 * x) * _root_.RHTower.thetaGaussBase x *
          gaussianMeasureMoment (gaussianSourceMeasure μ) (Real.pi * Real.exp (2 * x) - 1)) x := by
  letI := gaussianSourceMeasure_finite hw
  have hr : HasDerivAt (fun y : ℝ => Real.pi * Real.exp (2 * y) - 1)
      (2 * Real.pi * Real.exp (2 * x)) x :=
    (((_root_.RHTower.hasDerivAt_exp_two_mul x).const_mul Real.pi).sub_const 1).congr_deriv
      (by ring)
  have hl := (hasDerivAt_gaussianMeasureLaplace (gaussianSourceMeasure μ)
    (gaussianSourceMeasure_causal hμ) (sub_pos.2 hx)).comp x hr
  have hp := (_root_.RHTower.hasDerivAt_thetaGaussBase x).mul hl
  have he : causalGaussianMeasureResponse μ = fun y => _root_.RHTower.thetaGaussBase y *
      gaussianMeasureLaplace (gaussianSourceMeasure μ) (Real.pi * Real.exp (2 * y) - 1) :=
    funext (causalGaussianMeasureResponse_eq_laplace μ)
  rw [he]
  exact hp.congr_deriv (by simp only [Function.comp_apply]; ring)

theorem causalGaussianMeasureDefect_eq_moment {μ : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hw : Integrable gaussianSourceWeight μ)
    {x : ℝ} (hx : 1 < Real.pi * Real.exp (2 * x)) :
    causalGaussianMeasureDefect μ x =
      -(2 * Real.pi * Real.exp (2 * x) * _root_.RHTower.thetaGaussBase x) *
        gaussianMeasureMoment (gaussianSourceMeasure μ) (Real.pi * Real.exp (2 * x) - 1) := by
  rw [causalGaussianMeasureDefect, (hasDerivAt_causalGaussianMeasureResponse hμ hw hx).deriv]
  ring

/-- Pulling back the rate measure and removing its positive weight loses no
information away from the scalar atom. -/
theorem restrict_Ioi_eq_of_gaussianSourceMeasure_restrict_eq {μ ν : Measure ℝ}
    (heq : (gaussianSourceMeasure μ).restrict (Ioi 0) =
      (gaussianSourceMeasure ν).restrict (Ioi 0)) :
    μ.restrict (Ioi 0) = ν.restrict (Ioi 0) := by
  have he : gaussianCausalRate ⁻¹' Ioi 0 = Ioi 0 := by
    ext t
    exact gaussianCausalRate_pos_iff t
  have hm := continuous_gaussianCausalRate.measurableEmbedding injective_gaussianCausalRate
  simp only [gaussianSourceMeasure, hm.restrict_map, he,
    restrict_withDensity measurableSet_Ioi] at heq
  have hd := hm.map_injective heq
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (gaussianSourceWeight t)
  have hr (ρ : Measure ℝ) :
      ((ρ.restrict (Ioi 0)).withDensity w).withDensity (fun t => (w t)⁻¹) =
          ρ.restrict (Ioi 0) :=
    withDensity_inv_same (by fun_prop)
      (Eventually.of_forall fun t => ENNReal.ofReal_ne_zero_iff.2 (gaussianSourceWeight_pos t))
      (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  rw [← hr μ, ← hr ν, hd]

/-- One open interval of the literal differential defect determines a complete
causal measure off zero, even when its undamped mass is infinite. -/
theorem restrict_Ioi_eq_of_causalGaussianMeasureDefect_local {μ ν : Measure ℝ}
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0)
    (hwμ : Integrable gaussianSourceWeight μ) (hwν : Integrable gaussianSourceWeight ν)
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b, causalGaussianMeasureDefect μ x = causalGaussianMeasureDefect ν x) :
    μ.restrict (Ioi 0) = ν.restrict (Ioi 0) := by
  letI := gaussianSourceMeasure_finite hwμ
  letI := gaussianSourceMeasure_finite hwν
  apply restrict_Ioi_eq_of_gaussianSourceMeasure_restrict_eq
  have hpq : Real.pi * Real.exp (2 * a) - 1 < Real.pi * Real.exp (2 * b) - 1 := by
    have := mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by linarith : 2 * a < 2 * b)) Real.pi_pos
    linarith
  apply restrict_Ioi_eq_of_gaussianMeasureMoment_local
    (gaussianSourceMeasure_causal hμ) (gaussianSourceMeasure_causal hν)
    (by linarith : 0 < Real.pi * Real.exp (2 * a) - 1) hpq
  intro r hr
  let x := Real.log ((r + 1) / Real.pi) / 2
  have hr0 : 0 < r := (by linarith : 0 < Real.pi * Real.exp (2 * a) - 1).trans hr.1
  have hxe : Real.pi * Real.exp (2 * x) - 1 = r := by
    dsimp [x]
    rw [show 2 * (Real.log ((r + 1) / Real.pi) / 2) = Real.log ((r + 1) / Real.pi) by ring,
      Real.exp_log (div_pos (by linarith) Real.pi_pos)]
    field_simp
    ring
  have hxa : a < x := by
    have hh : Real.exp (2 * a) < Real.exp (2 * x) :=
      (mul_lt_mul_iff_right₀ Real.pi_pos).1 (by linarith [hr.1])
    linarith [Real.exp_lt_exp.1 hh]
  have hxb : x < b := by
    have hh : Real.exp (2 * x) < Real.exp (2 * b) :=
      (mul_lt_mul_iff_right₀ Real.pi_pos).1 (by linarith [hr.2])
    linarith [Real.exp_lt_exp.1 hh]
  have hx : 1 < Real.pi * Real.exp (2 * x) := by linarith
  have hd := heq x ⟨hxa, hxb⟩
  rw [causalGaussianMeasureDefect_eq_moment hμ hwμ hx,
    causalGaussianMeasureDefect_eq_moment hν hwν hx] at hd
  have hn : -(2 * Real.pi * Real.exp (2 * x) * _root_.RHTower.thetaGaussBase x) ≠ 0 :=
    neg_ne_zero.2 (ne_of_gt (by positivity [_root_.RHTower.thetaGaussBase_pos x]))
  simpa only [hxe] using mul_left_cancel₀ hn hd

/-- Gaussian weights are submultiplicative on the causal semigroup. The extra
rate product supplies damping when two outward translations are composed. -/
theorem gaussianSourceWeight_add_le_mul {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    gaussianSourceWeight (t + u) ≤ gaussianSourceWeight t * gaussianSourceWeight u := by
  have ht' : 0 ≤ gaussianCausalRate t := (gaussianCausalRate_nonneg_iff t).2 ht
  have hu' : 0 ≤ gaussianCausalRate u := (gaussianCausalRate_nonneg_iff u).2 hu
  have hr : gaussianCausalRate (t + u) = gaussianCausalRate t + gaussianCausalRate u +
      gaussianCausalRate t * gaussianCausalRate u := by
    unfold gaussianCausalRate
    rw [show 2 * (t + u) = 2 * t + 2 * u by ring, Real.exp_add]
    ring
  unfold gaussianSourceWeight
  rw [← Real.exp_add, hr]
  apply Real.exp_le_exp.2
  linarith [mul_nonneg ht' hu']

private theorem separate_countable_carrier {A B K H : Measure ℝ} {S : Set ℝ}
    (hS : S.Countable) (hA : A Sᶜ = 0) (hB : B Sᶜ = 0)
    (hK : K ≪ volume) (hH : H ≪ volume)
    (he : (A + K).restrict (Ioi 0) = (B + H).restrict (Ioi 0)) :
    A.restrict (Ioi 0) = B.restrict (Ioi 0) ∧
      K.restrict (Ioi 0) = H.restrict (Ioi 0) := by
  have hKS : K S = 0 := hK (hS.measure_zero volume)
  have hHS : H S = 0 := hH (hS.measure_zero volume)
  have part (D C : Measure ℝ) (hD : D Sᶜ = 0) (hC : C S = 0) :
      (D + C).restrict S = D ∧ (D + C).restrict Sᶜ = C := by
    constructor
    · rw [Measure.restrict_add, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hD),
        Measure.restrict_eq_zero.2 hC, add_zero]
    · rw [Measure.restrict_add, Measure.restrict_eq_zero.2 hD, zero_add]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by
        change C Sᶜᶜ = 0
        simpa only [compl_compl] using hC))
  have hAK := part A K hA hKS
  have hBH := part B H hB hHS
  have comm (ρ : Measure ℝ) (T : Set ℝ) (hT : MeasurableSet T) :
      (ρ.restrict (Ioi 0)).restrict T = (ρ.restrict T).restrict (Ioi 0) := by
    rw [Measure.restrict_restrict hT, Measure.restrict_restrict measurableSet_Ioi, inter_comm]
  constructor
  · have hh := congrArg (fun ρ : Measure ℝ => ρ.restrict S) he
    simpa only [comm _ S hS.measurableSet, hAK.1, hBH.1] using hh
  · have hh := congrArg (fun ρ : Measure ℝ => ρ.restrict Sᶜ) he
    simpa only [comm _ Sᶜ hS.measurableSet.compl, hAK.2, hBH.2] using hh

private theorem restrict_positive_eq_of_causal_absolutelyContinuous {K : Measure ℝ}
    (hK : K (Ici (0 : ℝ))ᶜ = 0) (habs : K ≪ volume) : K.restrict (Ioi 0) = K := by
  apply Measure.restrict_eq_self_of_ae_mem
  have hz : ∀ᵐ t ∂K, t ≠ 0 := by
    apply ae_iff.2
    simpa using habs (show (volume : Measure ℝ) {0} = 0 by simp)
  filter_upwards [ae_iff.2 hK, hz] with t ht hne
  exact lt_of_le_of_ne ht hne.symm

/-- Infinite atomic corrections and continuous corrections are separately
visible in one local Gaussian defect. Thus a signed atomic Euler correction
cannot cancel a nonzero continuous surgery kernel. -/
theorem atomic_and_continuous_parts_eq_of_gaussianDefect_local
    {A B K H : Measure ℝ} {S : Set ℝ} (hS : S.Countable)
    (hA : A Sᶜ = 0) (hB : B Sᶜ = 0) (hK : K ≪ volume) (hH : H ≪ volume)
    (hAK : (A + K) (Ici (0 : ℝ))ᶜ = 0) (hBH : (B + H) (Ici (0 : ℝ))ᶜ = 0)
    (hwAK : Integrable gaussianSourceWeight (A + K))
    (hwBH : Integrable gaussianSourceWeight (B + H))
    {a b : ℝ} (ha : 1 < Real.pi * Real.exp (2 * a)) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      causalGaussianMeasureDefect (A + K) x = causalGaussianMeasureDefect (B + H) x) :
    A.restrict (Ioi 0) = B.restrict (Ioi 0) ∧ K = H := by
  have he := restrict_Ioi_eq_of_causalGaussianMeasureDefect_local hAK hBH hwAK hwBH ha hab heq
  have hp := separate_countable_carrier hS hA hB hK hH he
  have hKc : K (Ici (0 : ℝ))ᶜ = 0 := by
    rw [Measure.add_apply] at hAK
    exact (add_eq_zero.1 hAK).2
  have hHc : H (Ici (0 : ℝ))ᶜ = 0 := by
    rw [Measure.add_apply] at hBH
    exact (add_eq_zero.1 hBH).2
  exact ⟨hp.1, by simpa only [restrict_positive_eq_of_causal_absolutelyContinuous hKc hK,
    restrict_positive_eq_of_causal_absolutelyContinuous hHc hH] using hp.2⟩

#print axioms restrict_Ioi_eq_of_causalGaussianMeasureDefect_local
#print axioms gaussianSourceWeight_add_le_mul
#print axioms atomic_and_continuous_parts_eq_of_gaussianDefect_local

end

end GaloisForLFunctions.EulerFETransportTheory
