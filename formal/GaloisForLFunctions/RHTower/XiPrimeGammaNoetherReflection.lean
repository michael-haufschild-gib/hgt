import GaloisForLFunctions.RHTower.ThetaNoetherAdjointEscape
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Reflected arithmetic source and the positive pairing balance

The reflected theta transform is the complex conjugate of the forward
transform. Its positive pairing obeys a balance law with the literal
prime--Gamma coefficient. Vertical decay forces strictly negative rates
at arbitrarily large heights. Thus the natural positive reflected pairing
cannot supply a conserved Noether charge for this canonical system.
-/

noncomputable section

namespace RHTower.ThetaSourceWard

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

theorem xiPrimeGammaNoetherPath_fst_neg (t : ℝ) :
    (xiPrimeGammaNoetherPath (-t)).1 = conj ((xiPrimeGammaNoetherPath t).1) := by
  simp only [xiPrimeGammaNoetherPath, bilateralLaplace_conj,
    xiPrimeGammaNoetherCoordinate, map_add, map_mul, map_one,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

/-- The pairing with the reflected arithmetic source is positive. -/
def xiPrimeGammaReflectedEnergy (t : ℝ) : ℝ :=
  Complex.normSq ((xiPrimeGammaNoetherPath t).1)

theorem xiPrimeGammaReflectedCharge (t : ℝ) :
    reciprocalScaleCharge ((xiPrimeGammaNoetherPath t).1,
      (xiPrimeGammaNoetherPath (-t)).1) = (xiPrimeGammaReflectedEnergy t : ℂ) := by
  rw [reciprocalScaleCharge, xiPrimeGammaNoetherPath_fst_neg, Complex.mul_conj]
  rfl

theorem xiPrimeGammaReflectedEnergy_pos (t : ℝ) :
    0 < xiPrimeGammaReflectedEnergy t :=
  Complex.normSq_pos.mpr (xiPrimeGammaNoetherPath_fst_ne_zero t)

/-- Exact arithmetic balance of the natural positive pairing. -/
theorem hasDerivAt_xiPrimeGammaReflectedEnergy (t : ℝ) :
    HasDerivAt xiPrimeGammaReflectedEnergy
      (2 * (xiPrimeGammaNoetherRate t).re * xiPrimeGammaReflectedEnergy t) t := by
  have hq := hasDerivAt_xiPrimeGammaNoetherPath_fst t
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hq
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hq
  convert! (hr.mul hr).add (hi.mul hi) using 1
  simp only [xiPrimeGammaReflectedEnergy, Complex.normSq_apply,
    Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem tendsto_xiPrimeGammaReflectedEnergy :
    Tendsto xiPrimeGammaReflectedEnergy atTop (𝓝 0) := by
  change Tendsto (fun t => Complex.normSq ((xiPrimeGammaNoetherPath t).1)) atTop (𝓝 0)
  simpa only [Complex.normSq_eq_norm_sq, norm_zero, zero_pow two_ne_zero] using
    tendsto_xiPrimeGammaNoetherPath_fst.norm.pow 2

/-- The reflected source has a nonzero adjoint residual unless the rate has zero real part. -/
theorem xiPrimeGammaReflectedAdjoint_residual (t : ℝ) :
    deriv (fun u => (xiPrimeGammaNoetherPath (-u)).1) t +
        xiPrimeGammaNoetherRate t * (xiPrimeGammaNoetherPath (-t)).1 =
      (2 * ((xiPrimeGammaNoetherRate t).re : ℂ)) *
        (xiPrimeGammaNoetherPath (-t)).1 := by
  simp only [xiPrimeGammaNoetherPath_fst_neg]
  have h := (hasDerivAt_xiPrimeGammaNoetherPath_fst t).star.deriv
  change deriv (fun u => conj ((xiPrimeGammaNoetherPath u).1)) t =
    conj (xiPrimeGammaNoetherRate t * (xiPrimeGammaNoetherPath t).1) at h
  rw [h, map_mul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Dissipation occurs beyond every height, without a zero-location premise. -/
theorem exists_xiPrimeGammaNoetherRate_re_neg_after (T : ℝ) :
    ∃ t : ℝ, T < t ∧ (xiPrimeGammaNoetherRate t).re < 0 := by
  obtain ⟨b, hTb, hb⟩ := ((eventually_gt_atTop T).and
    (tendsto_xiPrimeGammaReflectedEnergy.eventually_lt_const
      (xiPrimeGammaReflectedEnergy_pos T))).exists
  have hd : Differentiable ℝ xiPrimeGammaReflectedEnergy :=
    fun t => (hasDerivAt_xiPrimeGammaReflectedEnergy t).differentiableAt
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope xiPrimeGammaReflectedEnergy hTb
    hd.continuous.continuousOn hd.differentiableOn
  rw [(hasDerivAt_xiPrimeGammaReflectedEnergy t).deriv] at he
  have hn : (xiPrimeGammaReflectedEnergy b - xiPrimeGammaReflectedEnergy T) /
      (b - T) < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hb) (sub_pos.mpr hTb)
  refine ⟨t, ht.1, ?_⟩
  have hp := xiPrimeGammaReflectedEnergy_pos t
  nlinarith

/-- The positive source pairing is not a conserved charge. -/
theorem xiPrimeGammaReflectedEnergy_not_constant :
    ¬ ∃ c : ℝ, ∀ t : ℝ, xiPrimeGammaReflectedEnergy t = c := by
  rintro ⟨c, hc⟩
  have he : xiPrimeGammaReflectedEnergy = fun _ => c := funext hc
  have hz : c = 0 := tendsto_nhds_unique tendsto_const_nhds
    (he ▸ tendsto_xiPrimeGammaReflectedEnergy)
  have hp := xiPrimeGammaReflectedEnergy_pos 0
  rw [hc, hz] at hp
  exact (lt_irrefl 0) hp

end RHTower.ThetaSourceWard
