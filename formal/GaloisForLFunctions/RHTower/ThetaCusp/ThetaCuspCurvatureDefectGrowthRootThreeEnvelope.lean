import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthStableComponents
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthLossCooling
/-!
# Growth-transfer envelope retaining the dominant spectral edge

On q >= 3/2, t >= 8 the kernel lies below C(q)*t^7*(t-3).
For the literal deep source the loss is D8-3D7, a nonnegative quantity
whose exp(8q)-weighted value is antitone. This preserves the source
edge cancellation and its support-gap transport. Complete pair-versus-tail
absorption remains a separate sign problem.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory Set Filter Topology
noncomputable section
/-- The envelope retains the literal dominant spectral edge. -/
theorem growthTransferKernel_rootThree_shift (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    growthTransferKernel (3/2+y) (8+v) ≤
      growthTransferLeadingCoefficient (3/2+y)*(8+v)^7*(5+v) := by
  unfold growthTransferLeadingCoefficient growthTransferKernel growthScore growthScoreJet
    growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  apply sub_nonneg.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity
theorem growthTransferKernel_le_rootThree {q t : ℝ} (hq : 3/2 ≤ q) (ht : 8 ≤ t) :
    growthTransferKernel q t ≤ growthTransferLeadingCoefficient q*t^7*(t-3) := by
  have h := growthTransferKernel_rootThree_shift (q-3/2) (t-8) (by linarith) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring,show (8:ℝ)+(t-8)=t by ring,
    show (5:ℝ)+(t-8)=t-3 by ring] using h

theorem measureTransfer_rootThree_upper {q : ℝ} (hq : 3/2 ≤ q) (μ : Measure ℝ)
    (hi : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ) (hs : ∀ᵐ t ∂μ, (8:ℝ) ≤ t) :
    growthTransferFunctional q (measureMoment μ) ≤
      growthTransferLeadingCoefficient q*(measureMoment μ 8-3*measureMoment μ 7) := by
  rw [←integral_growthTransferKernel q μ hi]
  calc
    _ ≤ ∫ t : ℝ, growthTransferLeadingCoefficient q*(t^8-3*t^7) ∂μ := by
      apply integral_mono_ae (integrable_growthTransferKernel q μ hi)
        (((hi 8).sub ((hi 7).const_mul 3)).const_mul _)
      filter_upwards [hs] with t ht
      change growthTransferKernel q t ≤ growthTransferLeadingCoefficient q*(t^8-3*t^7)
      calc
        _ ≤ growthTransferLeadingCoefficient q*t^7*(t-3) := growthTransferKernel_le_rootThree hq ht
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul,integral_sub (hi 8) ((hi 7).const_mul 3),integral_const_mul]
      rfl

def deepRootThreeMoment (q : ℝ) : ℝ := thetaCuspDeepTailMoment q 8-3*thetaCuspDeepTailMoment q 7

theorem deepTransfer_rootThree_bounds {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ growthTransferFunctional q (thetaCuspDeepTailMoment q) ∧
      growthTransferFunctional q (thetaCuspDeepTailMoment q) ≤
        growthTransferLeadingCoefficient q*deepRootThreeMoment q := by
  have hq0 : 0 < q := by linarith
  have h := measureTransfer_rootThree_upper hq (componentTilt q thetaCuspDeepTailSpectralMeasure)
    (integrable_pow_componentTilt q thetaCuspDeepTailSpectralMeasure
      (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0))
    (ae_lower_componentTilt q _ ae_eight_le_thetaCuspDeepTailSpectralMeasure)
  have hm : measureMoment (componentTilt q thetaCuspDeepTailSpectralMeasure)=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  rw [hm] at h
  exact ⟨(deepTransfer_bounds hq).1,h⟩

theorem deepRootThreeMoment_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ deepRootThreeMoment q := by
  unfold deepRootThreeMoment
  linarith [deepMoment_gap hq 7,thetaCuspDeepTailMoment_nonneg q 7]

theorem deepRootThreeMoment_gap {q : ℝ} (hq : 0 < q) :
    8*deepRootThreeMoment q ≤ thetaCuspDeepTailMoment q 9-3*thetaCuspDeepTailMoment q 8 := by
  let f : ℕ → ℝ → ℝ := fun j t => t^j*Real.exp (-q*t)
  have hi (j : ℕ) : Integrable (f j) thetaCuspDeepTailSpectralMeasure :=
    integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq
  have h : 0 ≤ ∫ t : ℝ, f 9 t-11*f 8 t+24*f 7 t ∂thetaCuspDeepTailSpectralMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have h3 : 0 ≤ t-3 := by linarith
    have h8 : 0 ≤ t-8 := by linarith
    have ht0 : 0 ≤ t := by linarith
    calc
      0 ≤ t^7*(t-3)*(t-8)*Real.exp (-q*t) := by positivity
      _ = _ := by dsimp only [f]; ring
  have hsub : Integrable (fun t => f 9 t-11*f 8 t) thetaCuspDeepTailSpectralMeasure :=
    (hi 9).sub ((hi 8).const_mul 11)
  have hadd := integral_add hsub ((hi 7).const_mul 24)
  have hdiff := integral_sub (hi 9) ((hi 8).const_mul 11)
  rw [hadd,hdiff,integral_const_mul,integral_const_mul] at h
  change 0 ≤ thetaCuspDeepTailMoment q 9-11*thetaCuspDeepTailMoment q 8+24*thetaCuspDeepTailMoment q 7 at h
  unfold deepRootThreeMoment
  linarith

theorem hasDerivAt_deepRootThreeMoment {q : ℝ} (hq : 0 < q) :
    HasDerivAt deepRootThreeMoment
      (-thetaCuspDeepTailMoment q 9+3*thetaCuspDeepTailMoment q 8) q := by
  exact ((hasDerivAt_thetaCuspDeepTailMoment 8 hq).sub
    ((hasDerivAt_thetaCuspDeepTailMoment 7 hq).const_mul 3)).congr_deriv (by ring)

private theorem hasDerivAt_weightedDeepRootThreeMoment {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun t => Real.exp (8*t)*deepRootThreeMoment t)
      (Real.exp (8*q)*(8*deepRootThreeMoment q-thetaCuspDeepTailMoment q 9+
        3*thetaCuspDeepTailMoment q 8)) q := by
  have hi : HasDerivAt (fun t : ℝ => 8*t) 8 q := by
    simpa only [mul_one,one_mul,id_eq,mul_comm] using (hasDerivAt_id q).const_mul 8
  exact (hi.exp.mul (hasDerivAt_deepRootThreeMoment hq)).congr_deriv (by ring)

theorem weightedDeepRootThreeMoment_antitone :
    AntitoneOn (fun q => Real.exp (8*q)*deepRootThreeMoment q) (Ici (3/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_weightedDeepRootThreeMoment (by change 3/2 ≤ q at hq; linarith)).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    exact (hasDerivAt_weightedDeepRootThreeMoment (by linarith)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    have hq0 : 0 < q := by linarith
    rw [(hasDerivAt_weightedDeepRootThreeMoment hq0).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    linarith [deepRootThreeMoment_gap hq0]

end
end RHTower.ThetaCuspDefect
