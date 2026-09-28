import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleChamberLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# The withheld positive exchange cost of the socle intervention

For chamber states `P_0 = P_{σ,τ}` and `P_u = P_{σ,τ+u}` the fugacity translation is the
exponential family `dP_u/dP_0 = C(u)⁻¹ e^{-uQ}` in the socle observable.  Consequently the reflected
Jeffreys work is

  `J(P_0, P_u) = u (E_0 Q - E_u Q) = u ∫_0^u Var_{σ,τ+t}(Q) dt ≥ 0`,

strictly positive for `u ≠ 0`, because the socle observable is not almost surely constant.  The mean
and variance along the family are the first and second derivatives of the cumulant generating
function of `-Q`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

namespace GasChamber

variable (c : GasChamber)

theorem law_congr {c c' : GasChamber} (hσ : c.sigma = c'.sigma) (hτ : c.tau = c'.tau) :
    c.law = c'.law := by
  cases c
  cases c'
  simp only at hσ hτ
  subst hσ hτ
  rfl

/-- Every exponential moment `E_{σ,τ} exp(uQ)` with `u < σ + τ - 1` is finite. -/
theorem integrable_law_exp_socle {u : ℝ} (hu : 1 < c.sigma + c.tau - u) :
    Integrable (fun A => Real.exp (u * socleLog A)) c.law := by
  rw [law, integrable_withDensity_iff measurable_from_top
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hb := integrable_classLaw_exp_socle c.base (u := u - c.shift) (by
    have := c.base_tau_add_shift
    simp only [base_sigma] at *
    linarith)
  refine (hb.div_const c.normalizer).congr (Eventually.of_forall fun A => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le c.normalizer_pos.le), mul_div_assoc',
    ← Real.exp_add]
  congr 2
  ring

theorem integrable_socleLog_law : Integrable socleLog c.law := by
  set δ : ℝ := (c.sigma + c.tau - 1) / 2 with hδdef
  have hδ : 0 < δ := by linarith [c.firstDepth]
  refine ((c.integrable_law_exp_socle (u := δ) (by linarith [c.firstDepth])).div_const δ).mono'
    measurable_from_top.aestronglyMeasurable (Eventually.of_forall fun A => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (socleLog_nonneg A), le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * socleLog A)
  nlinarith [socleLog_nonneg A]

/-- The exponential moments of `-Q` are the socle moment generating function. -/
theorem integral_law_exp_neg_socle {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    ∫ A, Real.exp (t * -socleLog A) ∂c.law = (c.translate t ht).partition / c.partition := by
  have h := c.integral_law_cexp_socle (z := (t : ℂ)) (by simpa using ht)
  rw [← c.ofReal_partition_div t ht] at h
  have h' : ((∫ A, Real.exp (t * -socleLog A) ∂c.law : ℝ) : ℂ) =
      (((c.translate t ht).partition / c.partition : ℝ) : ℂ) := by
    rw [← h, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    simp only [Complex.ofReal_exp]
    push_cast
    ring_nf
  exact_mod_cast h'

/-- The fugacity family `P_{σ,τ+t}`, as the exponential tilt of `P_{σ,τ}` by `-tQ`. -/
def fugacityLaw (t : ℝ) : Measure AbelianZetaGroupClass :=
  c.law.tilted fun A => t * -socleLog A

/-- Admissible fugacity tilts are the translated chamber laws. -/
theorem fugacityLaw_eq {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    c.fugacityLaw t = (c.translate t ht).law := by
  rw [translate_law c t ht, fugacityLaw, Measure.tilted, integral_law_exp_neg_socle c ht]
  congr 1
  funext A
  rw [neg_mul, mul_neg]

theorem fugacityLaw_zero : c.fugacityLaw 0 = c.law := by
  have h : (fun A : AbelianZetaGroupClass => (0 : ℝ) * -socleLog A) = 0 := by
    funext A
    simp
  rw [fugacityLaw, h, tilted_zero]

theorem mem_interior_integrableExpSet {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    t ∈ interior (integrableExpSet (fun A => -socleLog A) c.law) := by
  refine mem_interior.mpr ⟨Ioi (1 - c.sigma - c.tau), fun s hs => ?_, isOpen_Ioi, by
    simp only [mem_Ioi]; linarith⟩
  simp only [mem_Ioi] at hs
  have h := c.integrable_law_exp_socle (u := -s) (by linarith)
  refine h.congr (Eventually.of_forall fun A => ?_)
  simp only
  congr 1
  ring

/-- The mean of the socle along the fugacity family is minus the derivative of the cumulant
generating function of `-Q`. -/
theorem integral_socleLog_fugacityLaw {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    ∫ A, socleLog A ∂c.fugacityLaw t = -deriv (cgf (fun A => -socleLog A) c.law) t := by
  have h := integral_tilted_mul_self (c.mem_interior_integrableExpSet ht)
  rw [← h, fugacityLaw, integral_neg, neg_neg]

/-- The variance of the socle along the fugacity family is the second derivative of the cumulant
generating function of `-Q`. -/
theorem variance_socleLog_fugacityLaw {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    Var[socleLog; c.fugacityLaw t] = iteratedDeriv 2 (cgf (fun A => -socleLog A) c.law) t := by
  have h := variance_tilted_mul (c.mem_interior_integrableExpSet ht)
  rw [← h, fugacityLaw]
  exact (variance_neg (X := socleLog)).symm

/-- `(AZC.15)`  The socle variance is strictly positive throughout the chamber. -/
theorem variance_socleLog_pos : 0 < Var[socleLog; c.law] := by
  have hmem : MemLp socleLog 2 c.law := by
    have h := memLp_tilted_mul (c.mem_interior_integrableExpSet (t := 0)
      (by linarith [c.firstDepth])) 2
    rw [show (fun A : AbelianZetaGroupClass => (0 : ℝ) * -socleLog A) = 0 by funext A; simp,
      tilted_zero] at h
    have h' := h.neg
    convert h' using 1
    all_goals first
      | (funext A; simp)
      | norm_num
  unfold variance
  exact ENNReal.toReal_pos (fun h0 => c.not_ae_const_socleLog ⟨∫ A, socleLog A ∂c.law,
    (evariance_eq_zero_iff measurable_from_top.aemeasurable).mp h0⟩) (evariance_lt_top hmem).ne

theorem variance_socleLog_fugacityLaw_pos {t : ℝ} (ht : 1 < c.sigma + c.tau + t) :
    0 < Var[socleLog; c.fugacityLaw t] := by
  rw [c.fugacityLaw_eq ht]
  exact (c.translate t ht).variance_socleLog_pos

/-! ## Relative entropy of the fugacity translation -/

theorem partition_congr {c c' : GasChamber} (hσ : c.sigma = c'.sigma) (hτ : c.tau = c'.tau) :
    c.partition = c'.partition := by
  simp only [partition, hσ, hτ]

theorem translate_absolutelyContinuous (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    (c.translate u hu).law ≪ c.law := by
  rw [translate_law c u hu]
  exact withDensity_absolutelyContinuous _ _

theorem llr_translate_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    llr (c.translate u hu).law c.law =ᵐ[c.law] fun A =>
      -u * socleLog A - Real.log ((c.translate u hu).partition / c.partition) := by
  have hK : 0 < (c.translate u hu).partition / c.partition :=
    div_pos (c.translate u hu).partition_pos c.partition_pos
  filter_upwards [c.rnDeriv_translate_law u hu] with A hA
  change Real.log (((c.translate u hu).law.rnDeriv c.law A).toReal) = _
  rw [hA, ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK.le),
    Real.log_div (Real.exp_pos _).ne' hK.ne', Real.log_exp]

theorem integral_llr_translate_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    Integrable (llr (c.translate u hu).law c.law) (c.translate u hu).law ∧
      ∫ A, llr (c.translate u hu).law c.law A ∂(c.translate u hu).law =
        -u * ∫ A, socleLog A ∂(c.translate u hu).law -
          Real.log ((c.translate u hu).partition / c.partition) := by
  have hae : llr (c.translate u hu).law c.law =ᵐ[(c.translate u hu).law] fun A =>
      -u * socleLog A - Real.log ((c.translate u hu).partition / c.partition) :=
    (c.translate_absolutelyContinuous u hu).ae_le (c.llr_translate_law u hu)
  have hQ := (c.translate u hu).integrable_socleLog_law
  have hint : Integrable (fun A => -u * socleLog A -
      Real.log ((c.translate u hu).partition / c.partition)) (c.translate u hu).law :=
    (hQ.const_mul (-u)).sub (integrable_const _)
  refine ⟨hint.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub (hQ.const_mul (-u)) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul]

theorem integral_llr_nonneg {μ ν : Measure AbelianZetaGroupClass} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ) :
    0 ≤ ∫ A, llr μ ν A ∂μ := by
  have h := integral_llr_add_sub_measure_univ_nonneg hac hint
  rwa [probReal_univ, probReal_univ, add_sub_cancel_right] at h

/-- `D(P_u ‖ P_0) = -u E_u Q - log C(u)`. -/
theorem klDiv_translate_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    klDiv (c.translate u hu).law c.law =
      ENNReal.ofReal (-u * ∫ A, socleLog A ∂(c.translate u hu).law -
        Real.log ((c.translate u hu).partition / c.partition)) := by
  obtain ⟨hint, hval⟩ := c.integral_llr_translate_law u hu
  rw [klDiv_of_ac_of_integrable (c.translate_absolutelyContinuous u hu) hint, probReal_univ,
    probReal_univ, add_sub_cancel_right, hval]

/-- The reverse translation returns to the original chamber point. -/
theorem translate_translate_neg_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u)
    (hu' : 1 < (c.translate u hu).sigma + (c.translate u hu).tau + -u) :
    ((c.translate u hu).translate (-u) hu').law = c.law :=
  law_congr rfl (by simp [translate])

/-- `D(P_0 ‖ P_u) = u E_0 Q + log C(u)`. -/
theorem klDiv_law_translate (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    klDiv c.law (c.translate u hu).law =
      ENNReal.ofReal (u * ∫ A, socleLog A ∂c.law +
        Real.log ((c.translate u hu).partition / c.partition)) := by
  set c' := c.translate u hu with hc'
  have hu' : 1 < c'.sigma + c'.tau + -u := by
    simp only [hc', translate]
    linarith [c.firstDepth]
  have hlaw := c.translate_translate_neg_law u hu hu'
  have hpart : (c'.translate (-u) hu').partition = c.partition :=
    partition_congr rfl (by simp [hc', translate])
  have h := c'.klDiv_translate_law (-u) hu'
  rw [hlaw, hpart] at h
  rw [h]
  congr 1
  have hK : 0 < c'.partition := c'.partition_pos
  rw [Real.log_div c.partition_pos.ne' hK.ne', Real.log_div hK.ne' c.partition_pos.ne']
  ring

/-- `(AZC.14)–(AZC.15)`  **Jeffreys work of the socle intervention.**
`J(P_0, P_u) = u (E_0 Q - E_u Q)`. -/
theorem formationJeffreys_translate (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    formationJeffreys c.law (c.translate u hu).law =
      ENNReal.ofReal (u * (∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law)) := by
  set c' := c.translate u hu with hc'
  have hu' : 1 < c'.sigma + c'.tau + -u := by
    simp only [hc', translate]
    linarith [c.firstDepth]
  obtain ⟨hint, hval⟩ := c.integral_llr_translate_law u hu
  have hnn1 : 0 ≤ -u * ∫ A, socleLog A ∂c'.law - Real.log (c'.partition / c.partition) := by
    rw [← hval]
    exact integral_llr_nonneg (c.translate_absolutelyContinuous u hu) hint
  obtain ⟨hint', hval'⟩ := c'.integral_llr_translate_law (-u) hu'
  have hnn2' := integral_llr_nonneg (c'.translate_absolutelyContinuous (-u) hu') hint'
  rw [hval', c.translate_translate_neg_law u hu hu',
    partition_congr (c := c'.translate (-u) hu') (c' := c) rfl (by simp [hc', translate])] at hnn2'
  have hK : 0 < c'.partition := c'.partition_pos
  have hnn2 : 0 ≤ u * ∫ A, socleLog A ∂c.law + Real.log (c'.partition / c.partition) := by
    rw [Real.log_div c.partition_pos.ne' hK.ne'] at hnn2'
    rw [Real.log_div hK.ne' c.partition_pos.ne']
    linarith
  rw [formationJeffreys, c.klDiv_law_translate u hu, c.klDiv_translate_law u hu,
    ← ENNReal.ofReal_add hnn2 hnn1]
  congr 1
  ring

/-! ## The variance integral -/

theorem admissible_of_mem_uIcc {u t : ℝ} (hu : 1 < c.sigma + c.tau + u)
    (ht : t ∈ uIcc (0 : ℝ) u) : 1 < c.sigma + c.tau + t := by
  rcases le_total 0 u with h | h
  · rw [uIcc_of_le h] at ht
    linarith [ht.1, c.firstDepth]
  · rw [uIcc_of_ge h] at ht
    linarith [ht.1]

theorem continuousOn_variance_fugacityLaw {u : ℝ} (hu : 1 < c.sigma + c.tau + u) :
    ContinuousOn (fun t => Var[socleLog; c.fugacityLaw t]) (uIcc (0 : ℝ) u) := by
  refine ContinuousOn.congr (f := iteratedDeriv 2 (cgf (fun A => -socleLog A) c.law))
    (fun t ht => ?_) fun t ht =>
      c.variance_socleLog_fugacityLaw (c.admissible_of_mem_uIcc hu ht)
  have hmem := c.mem_interior_integrableExpSet (c.admissible_of_mem_uIcc hu ht)
  have ha := (analyticAt_cgf hmem).deriv.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ha.continuousAt.continuousWithinAt

/-- `(AZC.15)`  `E_0 Q - E_u Q = ∫_0^u Var_{σ,τ+t}(Q) dt`. -/
theorem integral_variance_fugacityLaw (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    ∫ t in (0 : ℝ)..u, Var[socleLog; c.fugacityLaw t] =
      ∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law := by
  set g := cgf (fun A => -socleLog A) c.law with hg
  have hcongr : ∫ t in (0 : ℝ)..u, Var[socleLog; c.fugacityLaw t] =
      ∫ t in (0 : ℝ)..u, iteratedDeriv 2 g t :=
    intervalIntegral.integral_congr fun t ht =>
      c.variance_socleLog_fugacityLaw (c.admissible_of_mem_uIcc hu ht)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) u, HasDerivAt (deriv g) (iteratedDeriv 2 g t) t := by
    intro t ht
    have hmem := c.mem_interior_integrableExpSet (c.admissible_of_mem_uIcc hu ht)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (analyticAt_cgf hmem).deriv.differentiableAt.hasDerivAt
  have hint : IntervalIntegrable (iteratedDeriv 2 g) volume 0 u := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have hmem := c.mem_interior_integrableExpSet (c.admissible_of_mem_uIcc hu ht)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (analyticAt_cgf hmem).deriv.deriv.continuousAt.continuousWithinAt
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 := c.integral_socleLog_fugacityLaw (t := 0) (by linarith [c.firstDepth])
  have hu' := c.integral_socleLog_fugacityLaw hu
  rw [c.fugacityLaw_zero] at h0
  rw [c.fugacityLaw_eq hu] at hu'
  rw [h0, hu']
  ring

theorem intervalIntegrable_variance_fugacityLaw {u : ℝ} (hu : 1 < c.sigma + c.tau + u) :
    IntervalIntegrable (fun t => Var[socleLog; c.fugacityLaw t]) volume 0 u :=
  (c.continuousOn_variance_fugacityLaw hu).intervalIntegrable

/-- `(AZC.15)`  **Commutator work law.**  `J(P_0,P_u) = u (E_0 Q - E_u Q) =
u ∫_0^u Var_{σ,τ+t}(Q) dt ≥ 0`. -/
theorem exchangeWork (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    formationJeffreys c.law (c.translate u hu).law =
        ENNReal.ofReal (u * (∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law)) ∧
      u * (∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law) =
        u * ∫ t in (0 : ℝ)..u, Var[socleLog; c.fugacityLaw t] ∧
      0 ≤ u * (∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law) := by
  refine ⟨c.formationJeffreys_translate u hu, by rw [c.integral_variance_fugacityLaw u hu], ?_⟩
  rw [← c.integral_variance_fugacityLaw u hu]
  rcases le_total 0 u with h | h
  · exact mul_nonneg h (intervalIntegral.integral_nonneg (μ := volume) h fun t _ =>
      variance_nonneg _ _)
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_nonneg (μ := volume) h fun t _ =>
      variance_nonneg socleLog (c.fugacityLaw t)
    nlinarith

/-- `(AZC.15)`  **Strict exchange cost.**  For `u ≠ 0` the work is strictly positive. -/
theorem exchangeWork_pos (u : ℝ) (hu : 1 < c.sigma + c.tau + u) (hu0 : u ≠ 0) :
    0 < u * (∫ A, socleLog A ∂c.law - ∫ A, socleLog A ∂(c.translate u hu).law) ∧
      0 < formationJeffreys c.law (c.translate u hu).law := by
  have hpos : 0 < u * ∫ t in (0 : ℝ)..u, Var[socleLog; c.fugacityLaw t] := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · rw [intervalIntegral.integral_symm]
      have := intervalIntegral.intervalIntegral_pos_of_pos_on
        (c.intervalIntegrable_variance_fugacityLaw hu).symm (fun t ht =>
          c.variance_socleLog_fugacityLaw_pos (c.admissible_of_mem_uIcc hu
            (Ioo_subset_Icc_self.trans (by rw [uIcc_of_ge h.le]) ht))) h
      nlinarith
    · have := intervalIntegral.intervalIntegral_pos_of_pos_on
        (c.intervalIntegrable_variance_fugacityLaw hu) (fun t ht =>
          c.variance_socleLog_fugacityLaw_pos (c.admissible_of_mem_uIcc hu
            (Ioo_subset_Icc_self.trans (by rw [uIcc_of_le h.le]) ht))) h
      exact mul_pos h this
  obtain ⟨hJ, heq, -⟩ := c.exchangeWork u hu
  rw [heq]
  exact ⟨hpos, by rw [hJ, heq]; exact ENNReal.ofReal_pos.mpr hpos⟩

end GasChamber

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
