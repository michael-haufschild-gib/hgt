import GaloisForLFunctions.RHTower.HedenmalmThetaRootEndpoints
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Hedenmalm root flux is a faithful modular-charge reader

At every zero of the completed theta transform in its natural strip, the quantile-root energy is
strictly positive. The proof uses the exact forced root ODE: zero energy would make the continuous
root mode vanish throughout the open quantile interval, while its derivative there has the
nonzero forcing term `-1`.

The ordered-correlation flux is therefore a lossless reading of the same transverse charge carried
by reflected prime-tail entropy and the Riemann source Cayley rate. At a centered point
`s = 1/2 + i z`, reflected source entropy is `2 Im z`, and the root flux is minus one half of this
entropy times the strictly positive root energy. Hence flux neutrality, entropy neutrality, and
`Im z = 0` are equivalent at every completed-transform zero.

All results are unconditional. In particular, the module proves faithfulness of the charge reader,
not neutrality of the charge.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation

namespace HedenmalmThetaSource

/-- Quantile energy of the actual Hedenmalm theta root mode. -/
def thetaRootEnergy (z : ℂ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1,
    quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ 2

/-- **Strict root-energy law.** At a zero of the completed theta transform, the actual quantile
root mode has strictly positive energy. Zero energy would force the continuous mode to vanish on
the whole open interval, contradicting the constant `-1` forcing in its exact ODE. -/
theorem thetaRootEnergy_pos {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    0 < thetaRootEnergy z := by
  let f : ℝ → ℝ := fun t =>
    quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ 2
  have he := rootModeEndpoints_thetaSource hz hzero
  have hf_nonneg : ∀ t : ℝ, 0 ≤ f t := by
    intro t
    exact mul_nonneg (quantileSpeed_pos thetaSource t).le (sq_nonneg _)
  have hE_nonneg : 0 ≤ thetaRootEnergy z := by
    exact integral_nonneg_of_ae (ae_restrict_of_forall fun t _ => hf_nonneg t)
  by_contra hE_not_pos
  have hE_zero : thetaRootEnergy z = 0 :=
    le_antisymm (not_lt.mp hE_not_pos) hE_nonneg
  have hf_ae : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
    apply (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall fun t _ => hf_nonneg t) he.integrableEnergy).mp
    simpa [thetaRootEnergy, f] using hE_zero
  have hf_cont : ContinuousOn f (Ioo (0 : ℝ) 1) :=
    (continuousOn_quantileSpeed thetaSource).mul
      ((continuousOn_rootH thetaSource (hasShiftedTail_thetaSource hz)).norm.pow 2)
  have hf_eq_zero : EqOn f 0 (Ioo (0 : ℝ) 1) := by
    apply MeasureTheory.eqOn_of_ae_eq hf_ae hf_cont continuousOn_const
    simpa [isOpen_Ioo.interior_eq] using
      (subset_closure : Ioo (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1))
  have hroot_zero : ∀ t ∈ Ioo (0 : ℝ) 1, rootH thetaSource z t = 0 := by
    intro t ht
    have hprod : quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ 2 = 0 :=
      hf_eq_zero ht
    have hsq : ‖rootH thetaSource z t‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (quantileSpeed_pos thetaSource t).ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  let t0 : ℝ := 1 / 2
  have ht0 : t0 ∈ Ioo (0 : ℝ) 1 := by
    dsimp [t0]
    norm_num
  have hlocal : rootH thetaSource z =ᶠ[𝓝 t0] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhds ht0.1 ht0.2] with t ht
    exact hroot_zero t ht
  have hderiv_zero : HasDerivAt (rootH thetaSource z) 0 t0 := by
    exact (hasDerivAt_const t0 (0 : ℂ)).congr_of_eventuallyEq hlocal.symm
  have hode := hasDerivAt_rootH_ode thetaSource (hasShiftedTail_thetaSource hz) ht0
  have hroot_t0 : rootH thetaSource z t0 = 0 := hroot_zero t0 ht0
  have hderiv_neg_one : HasDerivAt (rootH thetaSource z) (-1) t0 := by
    convert hode using 1
    rw [hroot_t0, mul_zero, zero_sub]
  have : (-1 : ℂ) = 0 := hderiv_neg_one.unique hderiv_zero
  norm_num at this

/-- At the centered spectral point `1/2 + i z`, reflected Riemann source entropy is exactly twice
the imaginary part of the Hedenmalm spectral parameter. -/
theorem reflectedEntropy_centered_eq_two_im (z : ℂ) :
    riemannReflectedSourceEntropy ((1 / 2 : ℂ) + z * Complex.I) = 2 * z.im := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp [sourceCayleyTransverseRate, Complex.mul_re]
  ring

/-- Reflected source entropy is neutral at the centered point exactly when the Hedenmalm spectral
parameter is real. -/
theorem reflectedEntropy_centered_eq_zero_iff (z : ℂ) :
    riemannReflectedSourceEntropy ((1 / 2 : ℂ) + z * Complex.I) = 0 ↔ z.im = 0 := by
  rw [reflectedEntropy_centered_eq_two_im]
  constructor
  · exact fun h => (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h, mul_zero]

/-- **Flux--entropy identity.** At every completed-transform zero, the ordered-correlation flux is
minus one half of the reflected modular charge times the actual root energy. -/
theorem thetaRootFlux_eq_neg_half_entropy_mul_energy {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    (∫ t in Ioo (0 : ℝ) 1, -(rootH thetaSource z t)).re =
      -(1 / 2 : ℝ) *
        riemannReflectedSourceEntropy ((1 / 2 : ℂ) + z * Complex.I) *
          thetaRootEnergy z := by
  rw [rootFlux_identity_thetaSource hz hzero,
    reflectedEntropy_centered_eq_two_im]
  simp [thetaRootEnergy]
  ring

/-- **Faithful flux law.** At every completed-transform zero, ordered-correlation flux neutrality
is exactly reality of the Hedenmalm spectral parameter. -/
theorem thetaRootFlux_eq_zero_iff_im_eq_zero {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    (∫ t in Ioo (0 : ℝ) 1, -(rootH thetaSource z t)).re = 0 ↔ z.im = 0 := by
  rw [thetaRootFlux_eq_neg_half_entropy_mul_energy hz hzero,
    reflectedEntropy_centered_eq_two_im]
  have hE := thetaRootEnergy_pos hz hzero
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with hhalf | him
      · norm_num at hhalf
      · exact (mul_eq_zero.mp him).resolve_left (by norm_num)
    · exact False.elim (hE.ne' h)
  · intro him
    rw [him]
    ring

/-- Flux neutrality and reflected source-entropy neutrality are the same condition on every actual
theta root mode. -/
theorem thetaRootFlux_eq_zero_iff_reflectedEntropy_eq_zero {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    ((∫ t in Ioo (0 : ℝ) 1, -(rootH thetaSource z t)).re = 0) ↔
      riemannReflectedSourceEntropy ((1 / 2 : ℂ) + z * Complex.I) = 0 := by
  rw [thetaRootFlux_eq_zero_iff_im_eq_zero hz hzero,
    reflectedEntropy_centered_eq_zero_iff]

end HedenmalmThetaSource

end

end RHTower

#print axioms RHTower.HedenmalmThetaSource.thetaRootEnergy_pos
#print axioms RHTower.HedenmalmThetaSource.reflectedEntropy_centered_eq_two_im
#print axioms RHTower.HedenmalmThetaSource.reflectedEntropy_centered_eq_zero_iff
#print axioms RHTower.HedenmalmThetaSource.thetaRootFlux_eq_neg_half_entropy_mul_energy
#print axioms RHTower.HedenmalmThetaSource.thetaRootFlux_eq_zero_iff_im_eq_zero
#print axioms RHTower.HedenmalmThetaSource.thetaRootFlux_eq_zero_iff_reflectedEntropy_eq_zero
