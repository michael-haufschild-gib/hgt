import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplacePowerLimits
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedSmoothCurrentLaplace
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSourceRemainderCore

/-! The original mixed source in the true radial coordinate, with its full
angular coefficients and fixed smooth-onset factor retained. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def sourceProfile (s w a J K T : ℂ) (z : ℝ) : ℂ :=
  power (w/2) z*sourceRemainder s w a J K T z

/-- The entire radial remainder is continuous across both physical endpoints. -/
theorem sourceRemainder_continuous (s w a J K T : ℂ) :
    Continuous (sourceRemainder s w a J K T) := by
  have hp : Continuous (fun z : ℝ => power (2*s-w) (1+Real.sqrt (1-z))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hpos : 0 < 1+Real.sqrt (1-z) := by positivity
    have hc : ContinuousAt (fun t : ℝ => 1+Real.sqrt (1-t)) z := by fun_prop
    have ht := (continuousAt_ofReal_cpow_const (1+Real.sqrt (1-z)) (2*s-w) (Or.inr (ne_of_gt hpos))).comp_of_eq hc rfl
    exact ht
  unfold sourceRemainder
  fun_prop

/-- A proved uniform bound on the actual source remainder, including arbitrary
fixed complex angular amplitudes and the onset-transform factor. -/
theorem sourceRemainder_bound (s w a J K T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Icc 0 1 → ‖sourceRemainder s w a J K T z‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.image (sourceRemainder_continuous s w a J K T)).isBounded.exists_norm_le
  exact ⟨max C 0,le_max_right _ _,fun z hz => (hC _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

private theorem tortoise_log {r : ℝ} (hr : 1 < r) :
    D4BMIngoingCoordinates.tortoise r = Real.log (1-r⁻¹^(2 : ℕ))/2-Real.log (1+r⁻¹) := by
  have h0 : r ≠ 0 := by linarith
  have hm : r-1 ≠ 0 := by linarith
  have hp : r+1 ≠ 0 := by linarith
  rw [show 1-r⁻¹^(2 : ℕ)=(r-1)*(r+1)/r^(2 : ℕ) by field_simp; ring,
    Real.log_div (mul_ne_zero hm hp) (pow_ne_zero 2 h0),Real.log_mul hm hp,Real.log_pow,
    show 1+r⁻¹=(r+1)/r by field_simp,Real.log_div hp h0]
  dsimp [D4BMIngoingCoordinates.tortoise]
  ring

private theorem radial_sqrt {r : ℝ} (hr : 1 < r) : Real.sqrt (1-(1-r⁻¹^(2 : ℕ)))=r⁻¹ := by
  rw [sub_sub_cancel,Real.sqrt_sq (le_of_lt (inv_pos.mpr (by linarith)))]

/-- Exact retained current profile: the transform frequency w is independent
of the fixed physical source rate 2s; both original angular covectors survive. -/
theorem sourceProfile_original (s w a J K T : ℂ) {r : ℝ} (hr : 1 < r) :
    sourceProfile s w a J K T (1-r⁻¹^(2 : ℕ)) =
      Complex.exp (w*(D4BMIngoingCoordinates.tortoise r:ℂ))*
        D4BMQuadraticMixedSource.current s r
          (D4BMIngoingCoordinates.compactEnvelope s a 0 (r:ℂ)⁻¹) J K*T := by
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0<r by linarith))
  have hi : 0 < r⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : r⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hr
  have hz : 0 < 1-r⁻¹^(2 : ℕ) := by nlinarith
  have hu : 0 < 1+r⁻¹ := by positivity
  have hz0 : ((1-r⁻¹^(2 : ℕ):ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  have hu0 : ((1+r⁻¹:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  unfold sourceProfile sourceRemainder power
  rw [radial_sqrt hr,Complex.cpow_def_of_ne_zero hz0,Complex.cpow_def_of_ne_zero hu0,
    ← Complex.ofReal_log hz.le,← Complex.ofReal_log hu.le,tortoise_log hr]
  dsimp [D4BMQuadraticMixedSource.current,D4BMIngoingCoordinates.compactEnvelope]
  rw [show 1+(r:ℂ)⁻¹=((1+r⁻¹:ℝ):ℂ) by push_cast; rfl,← Complex.ofReal_log hu.le]
  push_cast
  simp only [zero_add]
  have he : Complex.exp ((Real.log (1-r⁻¹^(2 : ℕ)):ℂ)*(w/2))*
      Complex.exp ((Real.log (1+r⁻¹):ℂ)*(2*s-w)) =
      Complex.exp (w*((Real.log (1-r⁻¹^(2 : ℕ)):ℂ)/2-(Real.log (1+r⁻¹):ℂ)))*
        (Complex.exp (s*(Real.log (1+r⁻¹):ℂ)))^(2 : ℕ) := by
    have hex : (Complex.exp (s*(Real.log (1+r⁻¹):ℂ)))^(2 : ℕ) =
        Complex.exp (s*(Real.log (1+r⁻¹):ℂ)+s*(Real.log (1+r⁻¹):ℂ)) := by
      rw [pow_two,← Complex.exp_add]
    rw [hex,← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  have he' := he
  field_simp [hr0] at he' ⊢
  linear_combination (a^(2 : ℕ)*((5*s^(2 : ℕ)+15*s+4)*J*(r:ℂ)^(2 : ℕ)+s*(s-1)*((s+2)^(2 : ℕ)*J-K))*T)*he'

end
end RHTower.D4BMLaplaceRadial
