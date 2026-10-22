import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedLikelihoodCumulantObstruction
/-!
# Strict cooling of the complete ordinary curvature-defect ratio

The ratio derivative is exactly the negative complete spectral cooling
functional. Its positivity gives strict decrease on the entire source
coordinate domain. The nonlinear logarithmic ratio is a separate target.
-/

namespace RHTower.ThetaCuspDefect
open Set
noncomputable section

def ordinaryDefectRatio (q : ℝ) : ℝ :=
  q^5/(27*(q+3))*((q+3/2)^3*thetaCuspHigherLikelihoodSpectralMoment q 5-
    10*(q+3/2)^2*thetaCuspHigherLikelihoodSpectralMoment q 4+
    24*(q+3/2)*thetaCuspHigherLikelihoodSpectralMoment q 3-
    12*thetaCuspHigherLikelihoodSpectralMoment q 2)

theorem hasDerivAt_ordinaryDefectRatio {q : ℝ} (hq : 0 < q) :
    HasDerivAt ordinaryDefectRatio
      (-q^4/(27*(q+3)^2)*coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)) q := by
  have ha := (hasDerivAt_id q).add_const (3/2:ℝ)
  have hm (j : ℕ) := hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment j hq
  have h0 := ((ha.pow 3).mul (hm 5)).sub (((ha.pow 2).mul (hm 4)).const_mul 10)
  have h1 := h0.add ((ha.mul (hm 3)).const_mul 24)
  have hk := h1.sub ((hm 2).const_mul 12)
  have hq3 : 27*(q+3) ≠ 0 := by positivity
  have hw := ((hasDerivAt_id q).pow 5).div
    (((hasDerivAt_id q).add_const (3:ℝ)).const_mul 27) hq3
  convert! hw.mul hk using 1
  · funext y
    dsimp [ordinaryDefectRatio]
    ring
  · simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, id_eq,Nat.reduceAdd,Nat.cast_ofNat,
      Nat.reduceSub,pow_one,mul_one]
    simp only [coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    norm_num only [Nat.reduceAdd,coolingCoefficient]
    have hn : q+3 ≠ 0 := by positivity
    field_simp [hn]
    ring

theorem ordinaryDefectRatio_deriv_neg {q : ℝ} (hq : 3/2 ≤ q) :
    deriv ordinaryDefectRatio q < 0 := by
  have hq0 : 0 < q := by linarith
  rw [(hasDerivAt_ordinaryDefectRatio hq0).deriv]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos hq0 4))
    (by positivity)) (full_coolingFunctional_pos hq)

theorem ordinaryDefectRatio_strictAntiOn : StrictAntiOn ordinaryDefectRatio (Ici (3/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_ordinaryDefectRatio (by have h := mem_Ici.mp hq; linarith)).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    exact ordinaryDefectRatio_deriv_neg hq'.le
end
end RHTower.ThetaCuspDefect
