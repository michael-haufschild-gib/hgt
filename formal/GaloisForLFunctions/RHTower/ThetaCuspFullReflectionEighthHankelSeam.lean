import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam
import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet

/-!
# Strict rank-three reflected eighth-jet curvature at the theta seam

The self-dual modular ODE eliminates the complete theta-source jet through order eight. Its
signed `3 × 3` reflected Hankel determinant is a positive sixth power times a degree-twelve
polynomial. After shifting the squared modular scale by `191/10`, every coefficient is strictly
positive, giving an exact non-interval seam certificate.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- Signed rank-three reflected even-jet Hankel curvature of the complete theta source. -/
def thetaCuspFullSourceReflectionEighthHankelCurvature (x : ℝ) : ℝ :=
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
  HilbertMetric.signedEvenHankelThreeDet
    (f 0 ^ (2 : ℕ))
    (HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2))
    (HilbertMetric.reflectedProductFourthJet (f 0) (f 1) (f 2) (f 3) (f 4))
    (HilbertMetric.reflectedProductSixthJet
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
    (HilbertMetric.reflectedProductEighthJet
      (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8))

/-- The native rank-three reflected source seam equals its modular closure value. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_zero_eq_modularClosure :
    thetaCuspFullSourceReflectionEighthHankelCurvature 0 =
      thetaCuspReflectedEighthSeamModularClosureValue := by
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd
    (m := 1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd
    (m := 3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd
    (m := 5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd
    (m := 7) (by norm_num : Odd 7)
  have h := thetaCuspFullSource_reflectedEighthHankelSeam_eq_modularClosure
  dsimp only at h
  unfold thetaCuspFullSourceReflectionEighthHankelCurvature
  dsimp only
  rw [h1, h3, h5, h7]
  unfold HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet
    HilbertMetric.reflectedProductSixthJet
    HilbertMetric.reflectedProductEighthJet
  norm_num
  rw [iteratedDeriv_zero] at h
  simpa only [mul_assoc] using h

/-- The rank-three modular polynomial is positive on the entire source lower chamber. -/
theorem thetaCuspReflectedEighthSeamModularPolynomial_pos_of_lower
    {X : ℝ} (hX : (191 / 10 : ℝ) ≤ X) :
    0 < thetaCuspReflectedEighthSeamModularPolynomial X := by
  let y := X - (191 / 10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hshift : X = (191 / 10 : ℝ) + y := by dsimp [y]; ring
  rw [hshift]
  rw [show thetaCuspReflectedEighthSeamModularPolynomial
      ((191 / 10 : ℝ) + y) =
      4075547277524906301332145380433 / 343597383680000000000 +
        y * (48657767906672334213535260501 / 8589934592000000000) +
        y ^ (2 : ℕ) * (2058454591589504228738468673 / 1717986918400000000) +
        y ^ (3 : ℕ) * (2570296295059853406891357 / 17179869184000000) +
        y ^ (4 : ℕ) * (86519286078761293715763 / 6871947673600000) +
        y ^ (5 : ℕ) * (340888644173348221077 / 429496729600000) +
        y ^ (6 : ℕ) * (3552536624066274087 / 85899345920000) +
        y ^ (7 : ℕ) * (7979356617267429 / 4294967296000) +
        y ^ (8 : ℕ) * (46868665912083 / 687194767360) +
        y ^ (9 : ℕ) * (31741202637 / 17179869184) +
        y ^ (10 : ℕ) * (571238529 / 17179869184) +
        y ^ (11 : ℕ) * (1501305 / 4294967296) +
        y ^ (12 : ℕ) * (14025 / 8589934592) by
      unfold thetaCuspReflectedEighthSeamModularPolynomial
      ring]
  positivity

/-- The actual self-dual theta scale lies in the strict rank-three chamber. -/
theorem thetaCuspReflectedEighthSeamModularPolynomial_source_pos :
    0 < thetaCuspReflectedEighthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ (2 : ℕ)) :=
  thetaCuspReflectedEighthSeamModularPolynomial_pos_of_lower
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le

/-- The source-specialized rank-three modular closure value is strictly positive. -/
theorem thetaCuspReflectedEighthSeamModularClosureValue_pos :
    0 < thetaCuspReflectedEighthSeamModularClosureValue := by
  rw [thetaCuspReflectedEighthSeamModularClosureValue]
  have hm : 0 < thetaCuspSelfDualThetaMass := by
    linarith [
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand]
  exact mul_pos (pow_pos hm 6)
    thetaCuspReflectedEighthSeamModularPolynomial_source_pos

/-- Strict rank-three reflected eighth-jet curvature at the theta modular seam. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_zero_pos :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature 0 := by
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_zero_eq_modularClosure]
  exact thetaCuspReflectedEighthSeamModularClosureValue_pos

/-- Rank-three reflected eighth curvature varies continuously with source coordinate. -/
theorem continuous_thetaCuspFullSourceReflectionEighthHankelCurvature :
    Continuous thetaCuspFullSourceReflectionEighthHankelCurvature := by
  have hj (n : ℕ) : Continuous (iteratedDeriv n thetaCuspFullSource) := by
    rw [iteratedDeriv_thetaCuspFullSource]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspFullDerivative n x).continuousAt
  unfold thetaCuspFullSourceReflectionEighthHankelCurvature
    HilbertMetric.signedEvenHankelThreeDet
    HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet
    HilbertMetric.reflectedProductSixthJet
    HilbertMetric.reflectedProductEighthJet
  fun_prop

/-- Nontrivial open theta-source chamber with strict rank-three reflected eighth curvature. -/
theorem exists_thetaCuspFullSourceReflectionEighthHankelCurvature_pos_near_zero :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : ℝ, |x| < delta →
      0 < thetaCuspFullSourceReflectionEighthHankelCurvature x := by
  have hev : ∀ᶠ x : ℝ in 𝓝 0,
      0 < thetaCuspFullSourceReflectionEighthHankelCurvature x :=
    continuous_thetaCuspFullSourceReflectionEighthHankelCurvature.continuousAt.eventually
      (eventually_gt_nhds thetaCuspFullSourceReflectionEighthHankelCurvature_zero_pos)
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨delta, hdelta, fun x hx => hball ?_⟩
  simpa [Real.dist_eq] using hx

end


end RHTower
