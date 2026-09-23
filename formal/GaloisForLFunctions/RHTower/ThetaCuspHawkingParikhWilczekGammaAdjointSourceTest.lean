import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaReversibleDensity

/-!
# Actual Gamma-source test of the uncorrected adjoint

The normalized source modes have finite weighted squared norm and positive,
integrable cross-density. Their literal forward and reflected-ground
responses have admitted integrals. The paired difference is exactly
`-log n` times the positive cross-mass, hence is negative for every n > 1.
This excludes the uncorrected pairing identity on these actual modes;
it constructs no closed operator and asserts no Xi spectral occurrence.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaNormalizedRayMode (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n:ℝ)*Real.exp (-(((n:ℝ)-1)*x))
def pwGammaReversibleModeCross (n : ℕ) (x : ℝ) : ℝ :=
  pwGammaReversibleDensity x*pwGammaNormalizedRayMode n x
def pwGammaReversibleModeMass (n : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), pwGammaReversibleModeCross n x

theorem pwGammaNormalizedRayMode_pos {n : ℕ} (hn : 0<n) (x : ℝ) :
    0 < pwGammaNormalizedRayMode n x := by
  exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn)) (Real.exp_pos _)

theorem pwGammaNormalizedRayMode_one (x : ℝ) : pwGammaNormalizedRayMode 1 x = 1 := by
  simp [pwGammaNormalizedRayMode]

theorem pwGammaNormalizedRayMode_source_ratio {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    pwGammaRaySource ((n:ℝ)*x)/pwGammaRaySource x = (pwGammaNormalizedRayMode n x:ℂ) := by
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  rw [pwGammaRaySource_eq (mul_pos hnr hx), pwGammaRaySource_eq hx, ← Complex.ofReal_div]
  congr 1
  have he : Real.exp (-((n:ℝ)*x)) = Real.exp (-x)*Real.exp (-(((n:ℝ)-1)*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.sqrt_mul hnr.le, he, pwGammaNormalizedRayMode]
  field_simp [(Real.sqrt_pos.mpr hx).ne', Real.exp_ne_zero]

theorem pwGammaNormalizedRayMode_le {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    pwGammaNormalizedRayMode n x ≤ Real.sqrt (n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hn1) hx.le)))

theorem pwGammaReversibleModeCross_pos {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    0 < pwGammaReversibleModeCross n x :=
  mul_pos (pwGammaReversibleDensity_pos hx) (pwGammaNormalizedRayMode_pos hn x)

theorem pwGammaReversibleModeCross_integrable {n : ℕ} (hn : 0<n) :
    IntegrableOn (pwGammaReversibleModeCross n) (Ioi 0) := by
  have hm : Measurable (pwGammaReversibleModeCross n) := by
    unfold pwGammaReversibleModeCross pwGammaReversibleDensity pwGammaNormalizedRayMode
    fun_prop
  apply (pwGammaReversibleDensity_integrable.mul_const (Real.sqrt (n:ℝ))).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (pwGammaReversibleModeCross_pos hn hx).le]
  exact mul_le_mul_of_nonneg_left (pwGammaNormalizedRayMode_le hn hx)
    (pwGammaReversibleDensity_pos hx).le

theorem pwGammaReversibleModeMass_pos {n : ℕ} (hn : 0<n) :
    0 < pwGammaReversibleModeMass n := by
  have hp : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] pwGammaReversibleModeCross n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (pwGammaReversibleModeCross_pos hn hx).le
  rw [pwGammaReversibleModeMass, setIntegral_pos_iff_support_of_nonneg_ae hp
    (pwGammaReversibleModeCross_integrable hn)]
  have hs : Function.support (pwGammaReversibleModeCross n) ∩ Ioi (0:ℝ) = Ioi 0 := by
    apply inter_eq_right.mpr
    intro x hx
    exact (pwGammaReversibleModeCross_pos hn hx).ne'
  rw [hs]
  simp

theorem pwGammaNormalizedRayMode_square_integrable {n : ℕ} (hn : 0<n) :
    IntegrableOn (fun x => pwGammaReversibleDensity x*(pwGammaNormalizedRayMode n x)^(2 : ℕ)) (Ioi 0) := by
  have hm : Measurable (fun x => pwGammaReversibleDensity x*(pwGammaNormalizedRayMode n x)^(2 : ℕ)) := by
    unfold pwGammaReversibleDensity pwGammaNormalizedRayMode
    fun_prop
  apply (pwGammaReversibleDensity_integrable.mul_const (n:ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (pwGammaReversibleDensity_pos hx).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (pwGammaReversibleDensity_pos hx).le
  have hb := pwGammaNormalizedRayMode_le hn hx
  have hp := pwGammaNormalizedRayMode_pos hn x
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n:ℝ)]

/-- The original half-density source response divided by its actual source Q. -/
def pwGammaForwardModeResponse (n : ℕ) (x h : ℝ) : ℂ :=
  (pwGammaWeightedTranslation h (fun y => pwGammaRaySource ((n:ℝ)*y)) x -
    (Real.exp (-h):ℂ)*pwGammaRaySource ((n:ℝ)*x))/((h:ℂ)*pwGammaRaySource x)

def pwGammaBackwardGroundResponse (x h : ℝ) : ℂ :=
  (pwGammaReflectedTranslation h pwGammaRaySource x -
    (Real.exp (-h):ℂ)*pwGammaRaySource x)/((h:ℂ)*pwGammaRaySource x)

theorem pwGammaForwardModeResponse_eq {n : ℕ} (hn : 0<n) {x h : ℝ}
    (hx : 0<x) (hh : 0<h) :
    pwGammaForwardModeResponse n x h =
      (pwGammaNormalizedRayMode n x:ℂ)*pwGammaFrullaniKernel n h := by
  rw [pwGammaForwardModeResponse, pwGammaWeightedTranslation_ray_atom hn hh.le hx,
    ← pwGammaNormalizedRayMode_source_ratio hn hx, pwGammaFrullaniKernel_eq_real]
  push_cast
  field_simp [pwGammaRaySource_ne_zero x, Complex.ofReal_ne_zero.mpr hh.ne']

theorem pwGammaForwardModeResponse_integrable {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    IntegrableOn (pwGammaForwardModeResponse n x) (Ioi 0) := by
  exact IntegrableOn.congr_fun ((pwGammaFrullaniKernel_integrable hn).const_mul
    (pwGammaNormalizedRayMode n x:ℂ))
    (fun h hh => (pwGammaForwardModeResponse_eq hn hx hh).symm) measurableSet_Ioi

theorem pwGammaForwardModeResponse_integral {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    (∫ h in Ioi (0:ℝ), pwGammaForwardModeResponse n x h) =
      ((-Real.log (n:ℝ)*pwGammaNormalizedRayMode n x:ℝ):ℂ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaForwardModeResponse_eq hn hx hh),
    integral_const_mul, pwGammaFrullaniKernel_integral hn]
  push_cast
  ring

theorem pwGammaBackwardGroundResponse_zero {x h : ℝ} (hx : 0<x) (hh : 0≤h) :
    pwGammaBackwardGroundResponse x h = 0 := by
  rw [pwGammaBackwardGroundResponse, pwGammaReflectedTranslation_eq _ hh hx,
    div_self (pwGammaRaySource_ne_zero _), mul_one, sub_self, zero_div]

theorem pwGammaBackwardGroundResponse_integrable {x : ℝ} (hx : 0<x) :
    IntegrableOn (pwGammaBackwardGroundResponse x) (Ioi 0) := by
  exact IntegrableOn.congr_fun (integrable_zero _ _ _)
    (fun h hh => (pwGammaBackwardGroundResponse_zero hx hh.le).symm) measurableSet_Ioi

theorem pwGammaBackwardGroundResponse_integral {x : ℝ} (hx : 0<x) :
    (∫ h in Ioi (0:ℝ), pwGammaBackwardGroundResponse x h) = 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun h hh => pwGammaBackwardGroundResponse_zero hx hh.le), integral_zero]

def pwGammaReversibleForwardModePair (n : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), pwGammaReversibleDensity x *
    (∫ h in Ioi (0:ℝ), pwGammaForwardModeResponse n x h).re

def pwGammaReversibleBackwardGroundPair (n : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), pwGammaReversibleDensity x *
    (∫ h in Ioi (0:ℝ), pwGammaBackwardGroundResponse x h).re * pwGammaNormalizedRayMode n x

theorem pwGammaReversibleForwardModePair_integrand {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x * (∫ h in Ioi (0:ℝ), pwGammaForwardModeResponse n x h).re =
      -Real.log (n:ℝ)*pwGammaReversibleModeCross n x := by
  rw [pwGammaForwardModeResponse_integral hn hx, Complex.ofReal_re, pwGammaReversibleModeCross]
  ring

theorem pwGammaReversibleForwardModePair_integrable {n : ℕ} (hn : 0<n) :
    IntegrableOn (fun x => pwGammaReversibleDensity x *
      (∫ h in Ioi (0:ℝ), pwGammaForwardModeResponse n x h).re) (Ioi 0) := by
  exact IntegrableOn.congr_fun ((pwGammaReversibleModeCross_integrable hn).const_mul
    (-Real.log (n:ℝ)))
    (fun x hx => (pwGammaReversibleForwardModePair_integrand hn hx).symm) measurableSet_Ioi

theorem pwGammaReversibleForwardModePair_eq {n : ℕ} (hn : 0<n) :
    pwGammaReversibleForwardModePair n = -Real.log (n:ℝ)*pwGammaReversibleModeMass n := by
  rw [pwGammaReversibleForwardModePair, setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pwGammaReversibleForwardModePair_integrand hn hx), integral_const_mul]
  rfl

theorem pwGammaReversibleBackwardGroundPair_integrable (n : ℕ) :
    IntegrableOn (fun x => pwGammaReversibleDensity x *
      (∫ h in Ioi (0:ℝ), pwGammaBackwardGroundResponse x h).re * pwGammaNormalizedRayMode n x)
      (Ioi 0) := by
  apply IntegrableOn.congr_fun (integrable_zero _ _ _) _ measurableSet_Ioi
  intro x hx
  simp [pwGammaBackwardGroundResponse_integral hx]

theorem pwGammaReversibleBackwardGroundPair_zero (n : ℕ) :
    pwGammaReversibleBackwardGroundPair n = 0 := by
  rw [pwGammaReversibleBackwardGroundPair]
  trans ∫ x in Ioi (0:ℝ), (0:ℝ)
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [pwGammaBackwardGroundResponse_integral hx]
  · exact integral_zero _ _

theorem pwGammaReversibleMode_adjoint_defect {n : ℕ} (hn : 0<n) :
    pwGammaReversibleForwardModePair n-pwGammaReversibleBackwardGroundPair n =
      -Real.log (n:ℝ)*pwGammaReversibleModeMass n := by
  rw [pwGammaReversibleForwardModePair_eq hn, pwGammaReversibleBackwardGroundPair_zero, sub_zero]

theorem pwGammaReversibleMode_adjoint_defect_neg {n : ℕ} (hn : 1<n) :
    pwGammaReversibleForwardModePair n-pwGammaReversibleBackwardGroundPair n < 0 := by
  rw [pwGammaReversibleMode_adjoint_defect (Nat.zero_lt_of_lt hn)]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by exact_mod_cast hn)))
    (pwGammaReversibleModeMass_pos (Nat.zero_lt_of_lt hn))

end
end RHTower
