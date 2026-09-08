import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative spectral comparison of the uniformized equation

The free phase has a global Lipschitz bound in spectral frequency. Conjugating
the effective potential by the phase costs one spatial moment. Every such
moment is integrable for the arbitrary Schwartz coefficient profiles already
used by the paper's uniformized scattering construction. These estimates feed
an integrable-coefficient Grönwall comparison on both spatial half-lines.
-/

open Complex Matrix MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Frequency changes in the free phase cost at most one spatial factor. -/
theorem staggerPhase_parameter_bound (z w x : ℝ) :
    ‖FDNLS.staggerPhase z x-FDNLS.staggerPhase w x‖ ≤ |x| *|z-w| := by
  have he : FDNLS.staggerPhase z x-FDNLS.staggerPhase w x =
      FDNLS.staggerPhase w x*(FDNLS.staggerPhase (z-w) x-1) := by
    unfold FDNLS.staggerPhase
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hf : FDNLS.staggerPhase (z-w) x = Complex.exp (I*((-(z-w)*x : ℝ) : ℂ)) := by
    unfold FDNLS.staggerPhase
    congr 1
    push_cast
    ring
  rw [he,norm_mul,FDNLS.norm_staggerPhase,one_mul,hf]
  simpa only [Real.norm_eq_abs,abs_mul,abs_neg,mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(z-w)*x))

theorem rotatingFrame_sub (z x : ℝ) (u v : SpectralVector) :
    rotatingFrame z x (u-v) = rotatingFrame z x u-rotatingFrame z x v := by
  apply Prod.ext <;> simp only [rotatingFrame,Prod.fst_sub,Prod.snd_sub,mul_sub]

/-- The diagonal rotation is uniformly Lipschitz in frequency on each spatial fiber. -/
theorem rotatingFrame_parameter_bound (z w x : ℝ) (v : SpectralVector) :
    ‖rotatingFrame z x v-rotatingFrame w x v‖ ≤ |x| *|z-w| *‖v‖ := by
  have h0 := staggerPhase_parameter_bound z w x
  have h1 : ‖FDNLS.staggerPhase (-z) x-FDNLS.staggerPhase (-w) x‖ ≤ |x| *|z-w| := by
    simpa only [neg_sub_neg,abs_sub_comm] using staggerPhase_parameter_bound (-z) (-w) x
  change max ‖FDNLS.staggerPhase z x*v.1-FDNLS.staggerPhase w x*v.1‖
    ‖FDNLS.staggerPhase (-z) x*v.2-FDNLS.staggerPhase (-w) x*v.2‖ ≤ _
  rw [← sub_mul,← sub_mul,norm_mul,norm_mul]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right h0 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le v) (mul_nonneg (abs_nonneg x) (abs_nonneg (z-w))))
  · exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le v) (mul_nonneg (abs_nonneg x) (abs_nonneg (z-w))))

theorem uniformizedInteractionRate_sub (f g h : SchwartzMap ℝ ℂ) (z x : ℝ) (u v : SpectralVector) :
    uniformizedInteractionRate f g h z x (u-v) =
      uniformizedInteractionRate f g h z x u-uniformizedInteractionRate f g h z x v := by
  unfold uniformizedInteractionRate
  rw [rotatingFrame_sub,map_sub,rotatingFrame_sub]

/-- The effective interaction is Lipschitz in its vector argument with the integrable potential density. -/
theorem uniformizedInteractionRate_vector_bound (f g h : SchwartzMap ℝ ℂ)
    (z x : ℝ) (u v : SpectralVector) :
    ‖uniformizedInteractionRate f g h z x u-uniformizedInteractionRate f g h z x v‖ ≤
      effectiveDensity f g h x*‖u-v‖ := by
  rw [← uniformizedInteractionRate_sub]
  exact uniformizedInteractionRate_bound f g h z x (u-v)

/-- Conjugating the potential costs two phase differences and exactly one spatial moment. -/
theorem uniformizedInteractionRate_parameter_bound (f g h : SchwartzMap ℝ ℂ)
    (z w x : ℝ) (v : SpectralVector) :
    ‖uniformizedInteractionRate f g h z x v-uniformizedInteractionRate f g h w x v‖ ≤
      2*|x| *|z-w| *effectiveDensity f g h x*‖v‖ := by
  let D := effectiveDensity f g h x
  let K := |x| *|z-w|
  have hD : 0 ≤ D := effectiveDensity_nonneg f g h x
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg x) (abs_nonneg (z-w))
  have hr : ‖rotatingFrame (-z) x v-rotatingFrame (-w) x v‖ ≤ K*‖v‖ := by
    simpa only [neg_sub_neg,abs_sub_comm] using rotatingFrame_parameter_bound (-z) (-w) x v
  have he : uniformizedInteractionRate f g h z x v-uniformizedInteractionRate f g h w x v =
      rotatingFrame z x (effectiveOperator f g h x (rotatingFrame (-z) x v-rotatingFrame (-w) x v))+
        (rotatingFrame z x (effectiveOperator f g h x (rotatingFrame (-w) x v))-
         rotatingFrame w x (effectiveOperator f g h x (rotatingFrame (-w) x v))) := by
    unfold uniformizedInteractionRate
    rw [map_sub,rotatingFrame_sub]
    abel
  have h0 : ‖rotatingFrame z x (effectiveOperator f g h x
      (rotatingFrame (-z) x v-rotatingFrame (-w) x v))‖ ≤ D*(K*‖v‖) := by
    rw [rotatingFrame_norm]
    exact (effectiveOperator_bound f g h x _).trans (mul_le_mul_of_nonneg_left hr hD)
  have h1 : ‖rotatingFrame z x (effectiveOperator f g h x (rotatingFrame (-w) x v))-
      rotatingFrame w x (effectiveOperator f g h x (rotatingFrame (-w) x v))‖ ≤ K*(D*‖v‖) := by
    apply (rotatingFrame_parameter_bound z w x _).trans
    apply mul_le_mul_of_nonneg_left _ hK
    simpa only [rotatingFrame_norm] using effectiveOperator_bound f g h x (rotatingFrame (-w) x v)
  calc
    _ ≤ D*(K*‖v‖)+K*(D*‖v‖) := by rw [he]; exact (norm_add_le _ _).trans (add_le_add h0 h1)
    _ = _ := by dsimp [D,K]; ring

/-- Joint vector and spectral changes split into an integrable homogeneous term and a first-moment source. -/
theorem uniformizedInteractionRate_joint_bound (f g h : SchwartzMap ℝ ℂ)
    (z w x : ℝ) (u v : SpectralVector) :
    ‖uniformizedInteractionRate f g h z x u-uniformizedInteractionRate f g h w x v‖ ≤
      effectiveDensity f g h x*‖u-v‖+2*|x| *|z-w| *effectiveDensity f g h x*‖v‖ := by
  calc
    _ ≤ ‖uniformizedInteractionRate f g h z x u-uniformizedInteractionRate f g h z x v‖+
        ‖uniformizedInteractionRate f g h z x v-uniformizedInteractionRate f g h w x v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (uniformizedInteractionRate_vector_bound f g h z x u v)
      (uniformizedInteractionRate_parameter_bound f g h z w x v)

/-- Every polynomial spatial moment of the effective density is finite. -/
theorem effectiveDensity_moment_integrable (f g h : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n*effectiveDensity f g h x) := by
  have hi := (((effectiveSchwartzEntries f g h 0 0).integrable_pow_mul volume n).add
    ((effectiveSchwartzEntries f g h 0 1).integrable_pow_mul volume n)).add
    (((effectiveSchwartzEntries f g h 1 0).integrable_pow_mul volume n).add
      ((effectiveSchwartzEntries f g h 1 1).integrable_pow_mul volume n))
  apply hi.congr
  filter_upwards with x
  simp only [Pi.add_apply,effectiveDensity,Real.norm_eq_abs,mul_add,add_assoc]

/-- Spatial moments of arbitrary order are available to later spectral differentiation. -/
def effectiveMoment (f g h : SchwartzMap ℝ ℂ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, |x|^n*effectiveDensity f g h x

theorem effectiveMoment_nonneg (f g h : SchwartzMap ℝ ℂ) (n : ℕ) :
    0 ≤ effectiveMoment f g h n :=
  integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) n) (effectiveDensity_nonneg f g h x)

theorem orientedEffectiveDensity_moment_continuous (f g h : SchwartzMap ℝ ℂ) (b : Bool) (n : ℕ) :
    Continuous (fun x : ℝ => |x|^n*orientedEffectiveDensity f g h b x) :=
  (continuous_abs.pow n).mul (orientedEffectiveDensity_continuous f g h b)

theorem orientedEffectiveDensity_moment_integrable (f g h : SchwartzMap ℝ ℂ) (b : Bool) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n*orientedEffectiveDensity f g h b x) := by
  cases b
  · exact effectiveDensity_moment_integrable f g h n
  · change Integrable (fun x : ℝ => |x|^n*effectiveDensity f g h (-x))
    simpa only [abs_neg] using (effectiveDensity_moment_integrable f g h n).comp_neg

/-- Reversing the spatial ray preserves each total absolute moment. -/
theorem orientedEffectiveDensity_moment_integral (f g h : SchwartzMap ℝ ℂ) (b : Bool) (n : ℕ) :
    ∫ x : ℝ, |x|^n*orientedEffectiveDensity f g h b x = effectiveMoment f g h n := by
  cases b
  · rfl
  · change ∫ x : ℝ, |x|^n*effectiveDensity f g h (-x) = ∫ x : ℝ, |x|^n*effectiveDensity f g h x
    simpa only [abs_neg] using integral_neg_eq_self (fun x : ℝ => |x|^n*effectiveDensity f g h x) volume

end
end GaloisForLFunctions.HTGeometry.FokasLenells
