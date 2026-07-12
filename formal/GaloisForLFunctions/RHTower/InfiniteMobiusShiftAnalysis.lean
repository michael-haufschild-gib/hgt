import GaloisForLFunctions.RHTower.InfiniteMobiusCausalShift

open Complex MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

abbrev InfiniteMobiusShiftChannel :=
  lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2

def infiniteMobiusShiftAnalysisValue
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : InfiniteMobiusShiftChannel :=
  ⟨fun n => infiniteMobiusSignedWeight sigma n •
      MellinL2.additiveTranslationUnitary (-Real.log n) f,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul,
        LinearIsometryEquiv.norm_map, mul_pow,
        norm_infiniteMobiusSignedWeight_sq hsigma] using
        (summable_squarefreeMobiusProbability hsigma).mul_right (‖f‖ ^ 2))⟩

theorem infiniteMobiusShiftAnalysisValue_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    infiniteMobiusShiftAnalysisValue sigma hsigma f n =
      infiniteMobiusSignedWeight sigma n •
        MellinL2.additiveTranslationUnitary (-Real.log n) f := rfl

theorem norm_infiniteMobiusShiftAnalysisValue_sq
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftAnalysisValue sigma hsigma f‖ ^ 2 = ‖f‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (p := (2 : ENNReal)) (by norm_num : 0 < (2 : ENNReal).toReal)
    (infiniteMobiusShiftAnalysisValue sigma hsigma f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
  rw [hnorm]
  simp only [infiniteMobiusShiftAnalysisValue_apply, norm_smul,
    LinearIsometryEquiv.norm_map, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma]
  rw [tsum_mul_right, tsum_squarefreeMobiusProbability hsigma, one_mul]

theorem norm_infiniteMobiusShiftAnalysisValue
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftAnalysisValue sigma hsigma f‖ = ‖f‖ := by
  nlinarith [norm_infiniteMobiusShiftAnalysisValue_sq sigma hsigma f,
    norm_nonneg (infiniteMobiusShiftAnalysisValue sigma hsigma f), norm_nonneg f]

def infiniteMobiusShiftAnalysis
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] InfiniteMobiusShiftChannel where
  toFun := infiniteMobiusShiftAnalysisValue sigma hsigma
  map_add' f g := by
    apply lp.ext
    funext n
    simp only [infiniteMobiusShiftAnalysisValue_apply, map_add, smul_add,
      lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [infiniteMobiusShiftAnalysisValue_apply, map_smul,
      lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    rw [smul_smul, mul_comm, ← smul_smul]
  norm_map' := norm_infiniteMobiusShiftAnalysisValue sigma hsigma

theorem infiniteMobiusShiftAnalysis_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    infiniteMobiusShiftAnalysis sigma hsigma f n =
      infiniteMobiusSignedWeight sigma n •
        MellinL2.additiveTranslationUnitary (-Real.log n) f := rfl

end RHTower
