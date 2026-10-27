import GaloisForLFunctions.ArithmeticPositiveDuality.AContinuousArchimedeanSpectrumIsSeenByTheSuccessor
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Every square-integrable wave has a visible successor

The real affine vector state is defined for every L² wave. Hölder's inequality
makes its Gram products integrable. A nonzero wave gives a successor which is
not constant on the nonzero rationals: constancy would force every rational
phase to be one almost everywhere on its energy support, which is impossible
at a positive translation frequency.
-/

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate Real

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality


/-- Translation and unimodular multiplication preserve square integrability. -/
theorem memLp_realAffVec {H : ℝ → ℂ} (hH : MemLp H 2 volume) (g : AffineGroupQ) :
    MemLp (realAffVec H g) 2 volume := by
  have hs : MemLp (fun x : ℝ => H (x + Real.log (affSlope g))) 2 volume :=
    hH.comp_measurePreserving (measurePreserving_add_right volume (Real.log (affSlope g)))
  have hp : Continuous (fun x : ℝ =>
      cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ))) := by fun_prop
  apply hs.of_le (hp.aestronglyMeasurable.mul hs.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  rw [Pi.mul_apply, norm_mul]
  have he : ‖cexp (I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ))‖ = 1 := by
    rw [show I * ((affShift g : ℝ) : ℂ) * (Real.exp x : ℂ) =
      (((affShift g : ℝ) * Real.exp x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [he, one_mul]

/-- The affine Gram identity remains positive for arbitrary L² waves. -/
theorem isPosDefOnGroup_realAffState_of_memLp {H : ℝ → ℂ} (hH : MemLp H 2 volume) :
    IsPosDefOnGroup fun g : posAffine => realAffState H g := by
  intro N x c
  have hv (a : Fin N) := memLp_realAffVec hH (x a)
  have hvc (a : Fin N) : MemLp (fun t => conj (realAffVec H (x a) t)) 2 volume :=
    (hv a).of_le
      (Complex.continuous_conj.comp_aestronglyMeasurable (hv a).aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [Complex.norm_conj])
  have hint (a b : Fin N) : Integrable (fun t =>
      star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b) :=
    (((hvc a).integrable_mul (hv b)).const_mul _).mul_const _
  let V : ℝ → ℂ := fun t => ∑ b, c b * realAffVec H (x b) t
  refine ⟨∫ t, ‖V t‖ ^ 2, integral_nonneg fun t => sq_nonneg _, ?_⟩
  calc ∑ a, ∑ b, star (c a) * realAffState H (((x a)⁻¹ * x b : posAffine) : AffineGroupQ) * c b
      = ∑ a, ∑ b, ∫ t, star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [integral_mul_const, integral_const_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          realAffState_inv_mul (x a).2 (x b).2]
    _ = ∫ t, ∑ a, ∑ b, star (c a) * (conj (realAffVec H (x a) t) * realAffVec H (x b) t) * c b := by
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
        exact Finset.sum_congr rfl fun a _ => (integral_finsetSum _ fun b _ => hint a b).symm
    _ = ∫ t, ((‖V t‖ ^ 2 : ℝ) : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp only
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        simp only [V, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, Complex.star_def]
        ring
    _ = ((∫ t, ‖V t‖ ^ 2 : ℝ) : ℂ) := integral_ofReal

/-- Extension by zero across the positive-slope subgroup preserves positivity. -/
theorem isPosDefOnGroup_realAffPosDef_of_memLp {H : ℝ → ℂ} (hH : MemLp H 2 volume) :
    IsPosDefOnGroup (realAffPosDef H) :=
  isPosDefOnGroup_extendFromSubgroup (isPosDefOnGroup_realAffState_of_memLp hH)

/-- Every nonzero square-integrable wave has a nonconstant successor. -/
theorem realAffPosDef_nonblind_of_memLp {H : ℝ → ℂ} (hH : MemLp H 2 volume)
    (hmass : 0 < ∫ x, ‖H x‖ ^ 2) :
    ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → realAffPosDef H (translation b) = α := by
  rintro ⟨α, hα⟩
  let w : ℝ → ℝ := fun x => ‖H x‖ ^ 2
  have hwi : Integrable w := (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH
  have hw0 (x : ℝ) : 0 ≤ w x := sq_nonneg _
  let S : ℝ → ℂ := fun β => ∫ x,
    cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)
  have hSb (b : ℚ) (hb : b ≠ 0) : S b = α := by
    rw [← hα b hb, realAffPosDef_translation]
  have hbound (β x : ℝ) :
      ‖cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)‖ = w x := by
    rw [norm_mul, show I * (β : ℂ) * (Real.exp x : ℂ) =
      ((β * Real.exp x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (hw0 x)]
  have hSi (β : ℝ) : Integrable (fun x =>
      cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)) := by
    apply hwi.mono'
    · exact (by fun_prop : Continuous fun x : ℝ =>
        cexp (I * (β : ℂ) * (Real.exp x : ℂ))).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.aestronglyMeasurable)
    · exact Eventually.of_forall fun x => (hbound β x).le
  have hlim : Tendsto (fun n : ℕ => S ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 (S 0)) := by
    simp only [S]
    refine tendsto_integral_of_dominated_convergence w
      (fun n => (hSi _).aestronglyMeasurable) hwi
      (fun n => Eventually.of_forall fun x => (hbound _ x).le)
      (Eventually.of_forall fun x => ?_)
    have hc : Continuous fun β : ℝ =>
        cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ) := by fun_prop
    exact (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hα0 : S 0 = α := by
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => ?_)
    have hb : ((1 : ℚ) / ((n : ℚ) + 1)) ≠ 0 := by positivity
    rw [← hSb _ hb]
    exact congrArg S (by simp)
  have hre (β : ℝ) : (S β).re = ∫ x, Real.cos (β * Real.exp x) * w x := by
    show (∫ x, cexp (I * (β : ℂ) * (Real.exp x : ℂ)) * (w x : ℂ)).re = _
    rw [← RCLike.re_eq_complex_re, ← integral_re (hSi β)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [RCLike.re_eq_complex_re, show I * (β : ℂ) * (Real.exp x : ℂ) =
      ((β * Real.exp x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  -- Equality in every cosine bound forces all rational phases to coincide.
  have hcos (b : ℚ) : ∀ᵐ x, b ≠ 0 →
      (1 - Real.cos ((b : ℝ) * Real.exp x)) * w x = 0 := by
    by_cases hb : b = 0
    · exact Eventually.of_forall fun _ h => (h hb).elim
    have hcosi : Integrable (fun x => Real.cos ((b : ℝ) * Real.exp x) * w x) := by
      apply hwi.mono'
      · exact (by fun_prop : Continuous fun x : ℝ =>
          Real.cos ((b : ℝ) * Real.exp x)).aestronglyMeasurable.mul hwi.aestronglyMeasurable
      · exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
          exact mul_le_of_le_one_left (hw0 x) (Real.abs_cos_le_one _)
    have hi : Integrable (fun x => (1 - Real.cos ((b : ℝ) * Real.exp x)) * w x) := by
      convert hwi.sub hcosi using 1
      funext x
      simp only [Pi.sub_apply, sub_mul, one_mul]
    have heq : (S b).re = (S 0).re := by rw [hSb b hb, hα0]
    rw [hre, hre] at heq
    simp only [zero_mul, Real.cos_zero, one_mul] at heq
    have hz : (∫ x, (1 - Real.cos ((b : ℝ) * Real.exp x)) * w x) = 0 := by
      simp only [sub_mul, one_mul]
      rw [integral_sub hwi hcosi, heq, sub_self]
    have hae := (integral_eq_zero_iff_of_nonneg (fun x =>
      mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (hw0 x)) hi).mp hz
    exact hae.mono fun x hx _ => hx
  -- Countability permits choosing one common full-measure set of phase identities.
  have hall : ∀ᵐ x, ∀ b : ℚ, b ≠ 0 →
      (1 - Real.cos ((b : ℝ) * Real.exp x)) * w x = 0 := ae_all_iff.mpr hcos
  have hwzero : w =ᵐ[volume] 0 := by
    filter_upwards [hall] with x hx
    by_contra hw
    have hcosx (b : ℚ) (hb : b ≠ 0) : Real.cos ((b : ℝ) * Real.exp x) = 1 :=
      (sub_eq_zero.mp ((mul_eq_zero.mp (hx b hb)).resolve_right hw)).symm
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp (by simpa using hcosx 1 one_ne_zero)
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hk
      exact (Real.exp_pos x).ne' hk.symm
    have h4 : ((1 : ℚ) / (4 * k)) ≠ 0 := by
      have : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
      exact div_ne_zero one_ne_zero (mul_ne_zero four_ne_zero this)
    have hh := hcosx _ h4
    rw [show (((1 : ℚ) / (4 * k) : ℚ) : ℝ) * Real.exp x = Real.pi / 2 by
      rw [← hk]; push_cast; field_simp; ring, Real.cos_pi_div_two] at hh
    exact zero_ne_one hh
  have hz : (∫ x, w x) = 0 := by
    rw [integral_congr_ae hwzero]
    simp
  exact (ne_of_gt hmass) hz

/-- The autocorrelation of every nonzero L² wave admits a visible affine extension. -/
theorem successor_sees_L2_autocorrelation {H : ℝ → ℂ} (hH : MemLp H 2 volume)
    (hmass : 0 < ∫ x, ‖H x‖ ^ 2) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, H (x + Real.log (u : ℚ)) * conj (H x)) ∧
      ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α :=
  ⟨realAffPosDef H, isPosDefOnGroup_realAffPosDef_of_memLp hH,
    fun u hu => realAffPosDef_dilation u hu, realAffPosDef_nonblind_of_memLp hH hmass⟩

#print axioms successor_sees_L2_autocorrelation

end GaloisForLFunctions.ArithmeticPositiveDuality
