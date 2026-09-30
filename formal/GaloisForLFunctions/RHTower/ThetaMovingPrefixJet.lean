import GaloisForLFunctions.RHTower.ThetaMovingShellTailJet
import GaloisForLFunctions.RHTower.ThetaFiniteShellFrequencyJet
import GaloisForLFunctions.RHTower.XiMovingShellJetDecay
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi

/-!
# Joint cutoff/height limits of literal theta-prefix frequency jets
-/

open Real Complex MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace RHTower
noncomputable section

def thetaFullHalfFrequencyJet (k : ℕ) (b : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, (thetaCuspFullSource x : ℂ) * (Complex.I * (x : ℂ))^k *
    Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))

theorem integrable_thetaFullFrequencyJetIntegrand (k : ℕ) (b : ℝ) :
    Integrable (fun x : ℝ => (thetaCuspFullSource x : ℂ) * (Complex.I * (x : ℂ))^k *
      Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))) := by
  have h := integrable_thetaCuspFourierLaplaceJetIntegrand k
    (w := (b : ℂ)) (by simp)
  apply Integrable.mono h.norm
  · exact (by
      have hc := contDiff_thetaCuspFullSource.continuous
      fun_prop : Continuous (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
        (Complex.I * (x : ℂ))^k * Complex.exp (Complex.I * (b : ℂ) * (x : ℂ)))).aestronglyMeasurable
  · filter_upwards with x
    simp [thetaCuspFourierLaplaceJetIntegrand, thetaCuspFourierLaplaceIntegrand,
      norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, mul_comm]

theorem XiC_jet_eq_fullHalfFrequencyJet_add_conj (k : ℕ) (b : ℝ) :
    iteratedDeriv k XiC (b : ℂ) =
      thetaFullHalfFrequencyJet k b + conj (thetaFullHalfFrequencyJet k b) := by
  let p : ℝ → ℂ := fun x => (thetaCuspFullSource x : ℂ) * (Complex.I * (x : ℂ))^k *
    Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))
  have hp := integrable_thetaFullFrequencyJetIntegrand k b
  have hm := integrable_thetaCuspFourierLaplaceJetIntegrand k (w := (b : ℂ)) (by simp)
  rw [iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k (by
    simp [thetaCuspFourierLaplaceStrip]), integral_eq_integral_Ioi_add_reflect hm]
  have hpoint (x : ℝ) :
      thetaCuspFourierLaplaceJetIntegrand k (b : ℂ) x +
        thetaCuspFourierLaplaceJetIntegrand k (b : ℂ) (-x) = p x + conj (p x) := by
    have hneg : thetaCuspFourierLaplaceJetIntegrand k (b : ℂ) (-x) = p x := by
      simp only [thetaCuspFourierLaplaceJetIntegrand, thetaCuspFourierLaplaceIntegrand,
        Complex.ofReal_neg, thetaCuspFullSource_neg]
      have h1 : -I * -(x : ℂ) = I * (x : ℂ) := by ring
      have h2 : -I * (b : ℂ) * -(x : ℂ) = I * (b : ℂ) * (x : ℂ) := by ring
      rw [h1, h2]
      dsimp [p]
      ring
    have hconj : thetaCuspFourierLaplaceJetIntegrand k (b : ℂ) x = conj (p x) := by
      simp only [p, map_mul, map_pow, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I,
        thetaCuspFourierLaplaceJetIntegrand, thetaCuspFourierLaplaceIntegrand]
      ring
    rw [hneg, hconj, add_comm]
  calc
    _ = ∫ x : ℝ in Ioi 0, (p x + conj (p x)) := by
      apply integral_congr_ae
      exact Eventually.of_forall hpoint
    _ = (∫ x : ℝ in Ioi 0, p x) + ∫ x : ℝ in Ioi 0, conj (p x) :=
      integral_add hp.integrableOn
        (Complex.conjCLE.toContinuousLinearMap.integrable_comp hp).integrableOn
    _ = _ := by rw [integral_conj]; rfl

theorem thetaFullHalfFrequencyJet_re (k : ℕ) (b : ℝ) :
    (thetaFullHalfFrequencyJet k b).re = (iteratedDeriv k XiC (b : ℂ)).re / 2 := by
  rw [XiC_jet_eq_fullHalfFrequencyJet_add_conj]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem hasSum_thetaShellFrequencyJet (k : ℕ) (b : ℝ) :
    HasSum (fun n => thetaShellFrequencyJet n k b) (thetaFullHalfFrequencyJet k b) := by
  let P : ℝ → ℂ := fun x => (Complex.I * (x : ℂ))^k *
    Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hi : IntegrableOn (fun x => (thetaCuspFullSource x : ℂ) * P x) (Ioi 0) := by
    simpa only [P, mul_assoc] using (integrable_thetaFullFrequencyJetIntegrand k b).integrableOn
  have hs := hasSum_thetaCuspShellHalfLineTransform P hP hi
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, thetaCuspShellHalfLineTransform_zero, sub_zero] at ht
  simpa only [thetaShellFrequencyJet, thetaCuspShellHalfLineTransform, P,
    thetaFullHalfFrequencyJet, mul_assoc] using ht

theorem thetaShellPrefixFrequencyJet_add_tail (N k : ℕ) (b : ℝ) :
    thetaShellPrefixFrequencyJet N k b + thetaShellTailFrequencyJet N k b =
      thetaFullHalfFrequencyJet k b := by
  have hs := hasSum_thetaShellFrequencyJet k b
  calc
    _ = ∑' n : ℕ, thetaShellFrequencyJet n k b := by
      simpa only [thetaShellPrefixFrequencyJet, thetaShellTailFrequencyJet, Nat.add_comm] using
        hs.summable.sum_add_tsum_nat_add N
    _ = _ := hs.tsum_eq

theorem tendsto_normalized_thetaShellPrefixRealJet (k : ℕ) {lambda : ℝ} (hlambda : 4 < lambda) :
    Tendsto (fun N =>
      (Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
        thetaMovingShellScale N^k) *
          (thetaShellPrefixFrequencyJet N k (lambda * thetaMovingShellScale N)).re) atTop
      (𝓝 (-(((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
        ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1))).re)) := by
  have hfull := (Complex.continuous_re.tendsto 0).comp (tendsto_normalized_XiC_jet k hlambda)
  have htail := (Complex.continuous_re.tendsto _).comp
    (tendsto_normalized_thetaShellTailFrequencyJet k lambda)
  have hlim := (hfull.div_const 2).sub htail
  convert hlim using 1
  · funext N
    have heq := congrArg Complex.re (thetaShellPrefixFrequencyJet_add_tail N k
      (lambda * thetaMovingShellScale N))
    rw [Complex.add_re, thetaFullHalfFrequencyJet_re] at heq
    simp only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    linear_combination (Real.exp (Real.pi * thetaMovingShellScale N) /
      thetaMovingShellScale N * thetaMovingShellScale N^k) * heq
  · simp

end
end RHTower
