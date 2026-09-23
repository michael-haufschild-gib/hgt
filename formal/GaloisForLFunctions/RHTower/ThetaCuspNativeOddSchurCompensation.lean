import GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationFlux

/-!
# Exact Schur compensation at the native rank-six boundary

A canonical source coefficient repairs the negative seam determinant on a nontrivial
center interval. The same correction has zero integrated contribution. A global
comparison is still required to close the sixth mixed rank.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The strictly positive leading odd minor. -/
def thetaCuspNativeOddHeadDet (x : ℝ) : ℝ :=
  (-thetaCuspNativeReflectionJet 2 x)*(-thetaCuspNativeReflectionJet 6 x) -
    (thetaCuspNativeReflectionJet 4 x)^(2 : ℕ)

/-- Aperture-independent contribution of the exact center-flux derivative. -/
def thetaCuspCenterCompensationSource (x : ℝ) : ℝ :=
  3*thetaCuspFullSource x^(2 : ℕ) + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x

/-- The source determinant after the lower center-flux correction. -/
def thetaCuspNativeOddCompensatedDet (C x : ℝ) : ℝ :=
  thetaCuspNativeOddHankelThreeDet x +
    C*thetaCuspNativeOddHeadDet x*thetaCuspCenterCompensationSource x

/-- Canonical source-selected coefficient, fixed independently of the aperture. -/
def thetaCuspNativeOddCompensationCoefficient : ℝ :=
  -thetaCuspNativeOddHankelThreeDet 0 /
    (thetaCuspNativeOddHeadDet 0 * thetaCuspFullSource 0^(2 : ℕ))

theorem thetaCuspNativeOddHeadDet_pos (x : ℝ) :
    0 < thetaCuspNativeOddHeadDet x := (thetaCuspNativeOddHankelThree_head_pos x).2

/-- The fixed source-selected correction coefficient is strictly positive. -/
theorem thetaCuspNativeOddCompensationCoefficient_pos :
    0 < thetaCuspNativeOddCompensationCoefficient := by
  exact div_pos (neg_pos.mpr thetaCuspNativeOddHankelThreeDet_zero_neg)
    (mul_pos (thetaCuspNativeOddHeadDet_pos 0) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0)))

/-- The canonical correction reverses the seam determinant with an exact positive margin. -/
theorem thetaCuspNativeOddCompensatedDet_zero :
    thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient 0 =
      -2*thetaCuspNativeOddHankelThreeDet 0 := by
  have hd := (thetaCuspNativeOddHeadDet_pos 0).ne'
  have hp := (thetaCuspFullSource_pos_all 0).ne'
  unfold thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient
    thetaCuspCenterCompensationSource
  simp only [mul_zero, zero_mul, add_zero]
  field_simp
  ring

/-- The actual source correction repairs the native seam obstruction on an open center interval. -/
theorem exists_thetaCuspNativeOddCompensatedDet_pos_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  have hc : Continuous (thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient) := by
    have hd : Continuous (deriv thetaCuspFullSource) :=
      (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
    have hn := continuous_thetaCuspNativeReflectionJet
    have hp := thetaCuspSchwartzReal.continuous
    change Continuous thetaCuspFullSource at hp
    unfold thetaCuspNativeOddCompensatedDet thetaCuspNativeOddHeadDet
      thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
      thetaCuspCenterCompensationSource
    fun_prop
  have hz : 0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient 0 := by
    rw [thetaCuspNativeOddCompensatedDet_zero]
    linarith [thetaCuspNativeOddHankelThreeDet_zero_neg]
  have he := hc.continuousAt.eventually (eventually_gt_nhds hz)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- Corrected weighted tenth odd entry, with no changed integrated moment. -/
def thetaCuspCenterCorrectedOddLastEntry (a C r : ℝ) : ℝ :=
  r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 10 (r/2)) +
    C*deriv (thetaCuspCenterCompensationFlux a) r

/-- The corrected odd rank-three determinant retains the complete center weight. -/
def thetaCuspCenterCorrectedOddDet (a C r : ℝ) : ℝ :=
  HilbertMetric.signedEvenHankelThreeDet
    (r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 2 (r/2)))
    (r*Real.sinh (a*r)*thetaCuspNativeReflectionJet 4 (r/2))
    (r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 6 (r/2)))
    (r*Real.sinh (a*r)*thetaCuspNativeReflectionJet 8 (r/2))
    (thetaCuspCenterCorrectedOddLastEntry a C r)

/-- One scalar source inequality controls every positive aperture at the same center. -/
theorem thetaCuspCenterCorrectedOddDet_lower
    {a C r : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    (r*Real.sinh (a*r))^(3 : ℕ)*thetaCuspNativeOddCompensatedDet C (r/2) ≤
      thetaCuspCenterCorrectedOddDet a C r := by
  have hb := deriv_thetaCuspCenterCompensationFlux_lower ha hr
  have hd := thetaCuspNativeOddHeadDet_pos (r/2)
  have hscale : 0 ≤ (r*Real.sinh (a*r))^(2 : ℕ)*C*thetaCuspNativeOddHeadDet (r/2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hb hscale
  unfold thetaCuspCenterCorrectedOddDet thetaCuspCenterCorrectedOddLastEntry
    thetaCuspNativeOddCompensatedDet thetaCuspNativeOddHankelThreeDet
    thetaCuspCenterCompensationSource thetaCuspNativeOddHeadDet
    HilbertMetric.signedEvenHankelThreeDet at *
  nlinarith only [hm]

/-- The source-selected correction is strictly positive near the seam for every positive aperture. -/
theorem exists_thetaCuspCenterCorrectedOddDet_pos_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a r : ℝ), 0 < a → 0 < r → r < δ →
      0 < thetaCuspCenterCorrectedOddDet a thetaCuspNativeOddCompensationCoefficient r := by
  obtain ⟨δ, hδ, hb⟩ := exists_thetaCuspNativeOddCompensatedDet_pos_near_zero
  refine ⟨2*δ, by positivity, fun a r ha hr hrd => ?_⟩
  have hx : |r/2| < δ := by rw [abs_of_pos (by positivity : 0 < r/2)]; linarith
  have hw : 0 < r*Real.sinh (a*r) := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  exact (mul_pos (pow_pos hw 3) (hb (r/2) hx)).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le thetaCuspNativeOddCompensationCoefficient_pos.le hr.le)

/-- The corrected final entry is absolutely integrable at every critical aperture. -/
theorem integrableOn_thetaCuspCenterCorrectedOddLastEntry
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (C : ℝ) :
    IntegrableOn (thetaCuspCenterCorrectedOddLastEntry a C) (Ioi 0) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  have hn := (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha 10).neg
  apply (hn.add ((integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul C)).congr
  filter_upwards with r
  simp only [thetaCuspCenterCorrectedOddLastEntry, Pi.add_apply, Pi.neg_apply, mul_neg]

/-- Correcting the failing native entry leaves the literal tenth center-mixed moment unchanged. -/
theorem integral_thetaCuspCenterCorrectedOddLastEntry
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (C : ℝ) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterCorrectedOddLastEntry a C r) =
      -iteratedDeriv 10 (thetaCuspCenterMixedDensity a) 0 := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  have hbase : IntegrableOn (fun r : ℝ =>
      r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 10 (r/2))) (Ioi 0) := by
    apply (integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha 10).neg.congr
    filter_upwards with r
    simp only [Pi.neg_apply, mul_neg]
  unfold thetaCuspCenterCorrectedOddLastEntry
  rw [integral_add hbase ((integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul C),
    integral_const_mul, integral_deriv_thetaCuspCenterCompensationFlux habs, mul_zero, add_zero]
  simp_rw [mul_neg]
  rw [integral_neg, iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha]

private theorem nativeSignedJet_even (x : ℝ) (n : ℕ) :
    thetaCuspNativeSignedJet x (2*n) =
      (-1 : ℝ)^n*thetaCuspNativeReflectionJet (2*n) x := by
  have hI : (-Complex.I : ℂ)^(2 : ℕ) = ((-1 : ℝ) : ℂ) := by norm_num
  simp only [thetaCuspNativeSignedJet, pow_mul, hI, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- A global corrected source sign suffices for the actual missing odd rank-three moment block.
The global sign is an explicit remaining source comparison, not an established premise. -/
theorem thetaCuspCenterMixed_oddHankelThree_pos_of_compensatedSource
    {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ x : ℝ, 0 < x → 0 < thetaCuspNativeOddCompensatedDet C x)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 < HilbertMetric.signedEvenHankelThreeDet
      (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)
      (-iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 8 (thetaCuspCenterMixedDensity a) 0)
      (-iteratedDeriv 10 (thetaCuspCenterMixedDensity a) 0) := by
  let p (k : ℕ) (r : ℝ) := r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) k
  have hi (k : ℕ) : IntegrableOn (p k) (Ioi 0) :=
    integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha k
  have hp (k : ℕ) : (∫ r : ℝ in Ioi 0, p k r) = thetaCuspCenterMixedSignedJet a k :=
    (thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0.le ha k).symm
  have hp2 (r : ℝ) : p 2 r = r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 2 (r/2)) := by
    dsimp only [p]; rw [show 2 = 2*1 by norm_num, nativeSignedJet_even]; norm_num
  have hp4 (r : ℝ) : p 4 r = r*Real.sinh (a*r)*thetaCuspNativeReflectionJet 4 (r/2) := by
    dsimp only [p]; rw [show 4 = 2*2 by norm_num, nativeSignedJet_even]; norm_num
  have hp6 (r : ℝ) : p 6 r = r*Real.sinh (a*r)*(-thetaCuspNativeReflectionJet 6 (r/2)) := by
    dsimp only [p]; rw [show 6 = 2*3 by norm_num, nativeSignedJet_even]; norm_num
  have hp8 (r : ℝ) : p 8 r = r*Real.sinh (a*r)*thetaCuspNativeReflectionJet 8 (r/2) := by
    dsimp only [p]; rw [show 8 = 2*4 by norm_num, nativeSignedJet_even]; norm_num
  have hmass : 0 < ∫ r : ℝ in Ioi 0, p 2 r := by
    rw [hp, show 2 = 2*1 by norm_num, thetaCuspCenterMixedSignedJet_even]
    norm_num only [pow_one, Nat.reduceMul, neg_one_mul]
    rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact neg_pos.mpr (thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha)
  have hpoint : ∀ᵐ r ∂(volume.restrict (Ioi 0)),
      0 < p 2 r ∧ 0 < p 2 r*p 6 r-(p 4 r)^(2 : ℕ) ∧
        0 < HilbertMetric.signedEvenHankelThreeDet (p 2 r) (p 4 r) (p 6 r) (p 8 r)
          (thetaCuspCenterCorrectedOddLastEntry a C r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hw : 0 < r*Real.sinh (a*r) :=
      mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    have hx : 0 < r/2 := div_pos hr (by norm_num)
    rw [hp2, hp4, hp6, hp8]
    refine ⟨mul_pos hw (thetaCuspNativeOddHankelThree_head_pos (r/2)).1, ?_, ?_⟩
    · have hh := mul_pos (sq_pos_of_pos hw) (thetaCuspNativeOddHeadDet_pos (r/2))
      unfold thetaCuspNativeOddHeadDet at hh
      nlinarith only [hh]
    · exact (mul_pos (pow_pos hw 3) (hsource (r/2) hx)).trans_le
        (thetaCuspCenterCorrectedOddDet_lower ha0.le hC hr.le)
  have h := integral_threeByThree_det_pos (p 2) (p 4) (p 6) (p 8)
    (thetaCuspCenterCorrectedOddLastEntry a C) (hi 2) (hi 4) (hi 6) (hi 8)
    (integrableOn_thetaCuspCenterCorrectedOddLastEntry ha0.le ha C) hmass hpoint
  rw [hp, hp, hp, hp, integral_thetaCuspCenterCorrectedOddLastEntry ha0.le ha C] at h
  rw [show 2 = 2*1 by norm_num, thetaCuspCenterMixedSignedJet_even,
    show 4 = 2*2 by norm_num, thetaCuspCenterMixedSignedJet_even,
    show 6 = 2*3 by norm_num, thetaCuspCenterMixedSignedJet_even,
    show 8 = 2*4 by norm_num, thetaCuspCenterMixedSignedJet_even] at h
  norm_num at h ⊢
  exact h

end
end RHTower
