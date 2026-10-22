import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaAdjointSourceTest
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaAdjointCutoffContact
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Admitted logarithmic pairing of the actual adjoint contact

The scaled reciprocal map preserves the Gamma-mode cross-density with
its actual Jacobian. An exponential majorant admits its logarithmic
moment. Change of variables then identifies the `2 * log x` pairing
with the complete source-mode adjoint defect. This is a mode-level
identity, not a full cutoff transposition or a closed operator domain.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaReversibleModeLogMoment (n : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), Real.log x*pwGammaReversibleModeCross n x

def pwGammaModeReciprocal (n : ℕ) (x : ℝ) : ℝ := ((n:ℝ)*x)⁻¹

theorem pwGammaReversibleModeCross_eq (n : ℕ) (x : ℝ) :
    pwGammaReversibleModeCross n x = Real.sqrt (n:ℝ)*Real.exp (-((n:ℝ)*x)-x⁻¹)/x := by
  unfold pwGammaReversibleModeCross pwGammaReversibleDensity pwGammaNormalizedRayMode
  calc
    _ = Real.sqrt (n:ℝ)*(Real.exp (-x-x⁻¹)*Real.exp (-(((n:ℝ)-1)*x)))/x := by ring
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

theorem pwGammaModeReciprocal_pos {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    0 < pwGammaModeReciprocal n x := inv_pos.mpr (mul_pos (by exact_mod_cast hn) hx)

theorem pwGammaModeReciprocal_involutive {n : ℕ} (hn : 0<n) :
    Function.Involutive (pwGammaModeReciprocal n) := by
  intro x
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold pwGammaModeReciprocal
  simp only [mul_inv_rev, inv_inv]
  field_simp

theorem pwGammaModeReciprocal_image {n : ℕ} (hn : 0<n) :
    pwGammaModeReciprocal n '' Ioi (0:ℝ) = Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact pwGammaModeReciprocal_pos hn hx
  · intro x hx
    exact ⟨pwGammaModeReciprocal n x,pwGammaModeReciprocal_pos hn hx,
      pwGammaModeReciprocal_involutive hn x⟩

theorem pwGammaModeReciprocal_hasDerivAt {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    HasDerivAt (pwGammaModeReciprocal n) (-(n:ℝ)/((n:ℝ)*x)^(2 : ℕ)) x := by
  change HasDerivAt (fun y : ℝ => ((n:ℝ)*y)⁻¹) _ x
  simpa only [Pi.inv_def, id_eq, mul_one] using
    ((hasDerivAt_id x).const_mul (n:ℝ)).inv (mul_ne_zero (by exact_mod_cast hn.ne') hx.ne')

theorem pwGammaReversibleModeCross_reciprocal {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    ((n:ℝ)/((n:ℝ)*x)^(2 : ℕ))*pwGammaReversibleModeCross n (pwGammaModeReciprocal n x) =
      pwGammaReversibleModeCross n x := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [pwGammaReversibleModeCross_eq, pwGammaReversibleModeCross_eq]
  unfold pwGammaModeReciprocal
  have he : -((n:ℝ)*((n:ℝ)*x)⁻¹)-(((n:ℝ)*x)⁻¹)⁻¹ = -((n:ℝ)*x)-x⁻¹ := by
    field_simp
    ring
  rw [he]
  field_simp

private theorem pwGammaLogDensity_bound {x : ℝ} (hx : 0<x) :
    |Real.log x| * pwGammaReversibleDensity x ≤
      (1+((2:ℕ).factorial:ℝ))*Real.exp (-x) := by
  have hl : |Real.log x| ≤ x+x⁻¹ := by
    apply abs_le.mpr
    constructor
    · linarith [Real.neg_inv_le_log hx.le]
    · linarith [Real.log_le_self hx.le, inv_pos.mpr hx]
  have hr : 0<x⁻¹ := inv_pos.mpr hx
  have hp := Real.pow_div_factorial_le_exp x⁻¹ hr.le 2
  have hf : (0:ℝ)<(2:ℕ).factorial := by positivity
  have hpow : (x⁻¹)^(2 : ℕ)*Real.exp (-x⁻¹) ≤ ((2:ℕ).factorial:ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hf).mp hp
  calc
    _ ≤ (x+x⁻¹)*pwGammaReversibleDensity x :=
      mul_le_mul_of_nonneg_right hl (pwGammaReversibleDensity_pos hx).le
    _ = Real.exp (-x)*(Real.exp (-x⁻¹)+(x⁻¹)^(2 : ℕ)*Real.exp (-x⁻¹)) := by
      unfold pwGammaReversibleDensity
      rw [sub_eq_add_neg, Real.exp_add]
      field_simp
    _ ≤ Real.exp (-x)*(1+((2:ℕ).factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.le)) hpow
    _ = _ := mul_comm _ _

theorem pwGammaReversibleModeLogMoment_integrable {n : ℕ} (hn : 0<n) :
    IntegrableOn (fun x => Real.log x*pwGammaReversibleModeCross n x) (Ioi 0) := by
  have hm : Measurable (fun x => Real.log x*pwGammaReversibleModeCross n x) := by
    unfold pwGammaReversibleModeCross pwGammaReversibleDensity pwGammaNormalizedRayMode
    fun_prop
  apply ((integrableOn_exp_neg_Ioi 0).const_mul
    (Real.sqrt (n:ℝ)*(1+((2:ℕ).factorial:ℝ)))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pwGammaReversibleModeCross_pos hn hx).le]
  calc
    _ = (|Real.log x| * pwGammaReversibleDensity x)*pwGammaNormalizedRayMode n x := by
      unfold pwGammaReversibleModeCross
      ring
    _ ≤ ((1+((2:ℕ).factorial:ℝ))*Real.exp (-x))*Real.sqrt (n:ℝ) := by
      exact mul_le_mul (pwGammaLogDensity_bound hx) (pwGammaNormalizedRayMode_le hn hx)
        (pwGammaNormalizedRayMode_pos hn x).le (by positivity)
    _ = _ := by ring

theorem pwGammaReversibleModeLogMoment_eq {n : ℕ} (hn : 0<n) :
    pwGammaReversibleModeLogMoment n =
      -(Real.log (n:ℝ)/2)*pwGammaReversibleModeMass n := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hs := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) =>
      (pwGammaModeReciprocal_hasDerivAt hn hx).hasDerivWithinAt)
    (pwGammaModeReciprocal_involutive hn).injective.injOn
    (fun x => Real.log x*pwGammaReversibleModeCross n x)
  rw [pwGammaModeReciprocal_image hn] at hs
  have hr : (∫ x in Ioi (0:ℝ), |-(n:ℝ)/((n:ℝ)*x)^(2 : ℕ)| •
      (Real.log (pwGammaModeReciprocal n x)*pwGammaReversibleModeCross n (pwGammaModeReciprocal n x))) =
      ∫ x in Ioi (0:ℝ), -Real.log (n:ℝ)*pwGammaReversibleModeCross n x -
        Real.log x*pwGammaReversibleModeCross n x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [smul_eq_mul, neg_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ)≤n/((n:ℝ)*x)^(2 : ℕ))]
    calc
      _ = Real.log (pwGammaModeReciprocal n x)*
          (((n:ℝ)/((n:ℝ)*x)^(2 : ℕ))*pwGammaReversibleModeCross n (pwGammaModeReciprocal n x)) := by ring
      _ = _ := by
        rw [pwGammaReversibleModeCross_reciprocal hn hx, pwGammaModeReciprocal,
          Real.log_inv, Real.log_mul hn0 (ne_of_gt hx)]
        ring
  rw [hr, integral_sub ((pwGammaReversibleModeCross_integrable hn).const_mul _)
    (pwGammaReversibleModeLogMoment_integrable hn), integral_const_mul] at hs
  change pwGammaReversibleModeLogMoment n =
    -Real.log (n:ℝ)*pwGammaReversibleModeMass n-pwGammaReversibleModeLogMoment n at hs
  linarith

theorem pwGammaReversibleMode_contact_pair {n : ℕ} (hn : 0<n) :
    (∫ x in Ioi (0:ℝ), (2*Real.log x)*pwGammaReversibleModeCross n x) =
      pwGammaReversibleForwardModePair n-pwGammaReversibleBackwardGroundPair n := by
  rw [pwGammaReversibleMode_adjoint_defect hn]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  change 2*pwGammaReversibleModeLogMoment n = _
  rw [pwGammaReversibleModeLogMoment_eq hn]
  ring

end
end RHTower
