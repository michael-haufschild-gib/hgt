import GaloisForLFunctions.RHTower.InfiniteMobiusSignedChannel
import GaloisForLFunctions.RHTower.XiThetaSquareRateCausalSource

open Complex MeasureTheory Set Filter

noncomputable section
namespace RHTower

theorem additiveTranslationUnitary_hasAELowerSupport_zero
    {h : ℝ} (hh : 0 ≤ h) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    HasAELowerSupport
      (fun t : ℝ => MellinL2.additiveTranslationUnitary (-h) f t) 0 := by
  have hcoe := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving (-h))
  have htrans :
      (fun t : ℝ => MellinL2.additiveTranslationUnitary (-h) f t) =ᵐ[volume]
        fun t : ℝ => f (t - h) := by
    simpa [MellinL2.additiveTranslationUnitary,
      MellinL2.lpCompMeasurePreservingEquiv, Function.comp_apply,
      MellinL2.realTranslationEquiv] using hcoe
  have hfshift :=
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.ae hf
  filter_upwards [htrans, hfshift] with t ht hsupp
  intro ht0
  rw [ht]
  have hsupp' : t - h < 0 → f (t - h) = 0 := by
    simpa [MellinL2.realTranslationEquiv] using hsupp
  exact hsupp' (by linarith)

theorem infiniteMobiusShiftTerm_hasAELowerSupport_zero
    {sigma : ℝ} (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    HasAELowerSupport (fun t : ℝ => infiniteMobiusShiftTerm sigma n f t) 0 := by
  by_cases hn0 : n = 0
  · subst n
    have hterm : infiniteMobiusShiftTerm sigma 0 f = 0 := by
      simp [infiniteMobiusShiftTerm, signedMobiusProbability]
    rw [hterm]
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with t ht
    intro _
    exact ht
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hnpos)
    have hshift := additiveTranslationUnitary_hasAELowerSupport_zero hlog f hf
    have hsmul := Lp.coeFn_smul (signedMobiusProbability sigma n)
      (MellinL2.additiveTranslationUnitary (-Real.log n) f)
    filter_upwards [hsmul, hshift] with t ht hs
    intro ht0
    rw [infiniteMobiusShiftTerm, ht]
    simp only [Pi.smul_apply]
    rw [hs ht0, smul_zero]

theorem infiniteMobiusShiftAverage_hasAELowerSupport_zero
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    HasAELowerSupport (fun t : ℝ => infiniteMobiusShiftAverage sigma f t) 0 := by
  apply (hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero _).mpr
  rw [infiniteMobiusShiftAverage]
  have hsum := summable_infiniteMobiusShiftTerm hsigma f
  rw [negativeHalfLineRestrictionL2.map_tsum hsum]
  have hzero : ∀ n : ℕ,
      negativeHalfLineRestrictionL2 (infiniteMobiusShiftTerm sigma n f) = 0 := by
    intro n
    exact (hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero _).mp
      (infiniteMobiusShiftTerm_hasAELowerSupport_zero n f hf)
  simp only [hzero, tsum_zero]

end RHTower
