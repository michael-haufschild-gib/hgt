import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactModel
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompactCorrection
import GaloisForLFunctions.RHTower.ThetaCuspEvenSeamDeterminant

/-! # Exact complete-source incidence of the coupled compact even matrix -/
namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear
private abbrev M := Bottcher.completedThetaProfile

private theorem compactState_eq (x : ℝ) :
    (fun j => thetaCuspModularLyapunovState j x) =
      HTGeometry.oddCompactState (u x) (a x) (w x) := by
  funext j
  cases j <;> simp [thetaCuspModularLyapunovState, HTGeometry.oddCompactState,
    u, a, w, thetaCuspModularMassDrift]

private theorem reflected_eq_of_scalar (n : ℕ) (F : ℝ → ℝ → ℝ → ℝ)
    (hF : ∀ u a w : ℝ, MvPolynomial.eval (HTGeometry.oddCompactState u a w)
      (HTGeometry.oddCompactReflectedJetPolynomial n) = (F u a w : ℂ)) (x : ℝ) :
    thetaCuspNativeReflectionJet n x = M x^(2 : ℕ)*F (u x) (a x) (w x) := by
  have hc := thetaCuspNativeReflectionJet_eq_lyapunovPolynomial n x
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile, compactState_eq, hF] at hc
  have hr := congrArg Complex.re hc
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- Every signed compact moment is the corresponding literal complete-source derivative. -/
theorem thetaCuspNativeEvenJet_eq_compactScalar (k : Fin 7) (x : ℝ) :
    (-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x =
      M x^(2 : ℕ)*HTGeometry.evenCompactSignedMoment k (u x) (a x) (w x) := by
  fin_cases k
  · norm_num [HTGeometry.evenCompactSignedMoment, thetaCuspNativeReflectionJet_eq,
      thetaCuspFullSource_eq_compactSourceZero]
    dsimp only [M, u, a, thetaCuspModularMassDrift]
    ring
  · have h := reflected_eq_of_scalar 2 HTGeometry.oddCompactReflectedScalar2 HTGeometry.oddCompactReflectedScalar2_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]
  · have h := reflected_eq_of_scalar 4 HTGeometry.oddCompactReflectedScalar4 HTGeometry.oddCompactReflectedScalar4_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]
  · have h := reflected_eq_of_scalar 6 HTGeometry.oddCompactReflectedScalar6 HTGeometry.oddCompactReflectedScalar6_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]
  · have h := reflected_eq_of_scalar 8 HTGeometry.oddCompactReflectedScalar8 HTGeometry.oddCompactReflectedScalar8_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]
  · have h := reflected_eq_of_scalar 10 HTGeometry.oddCompactReflectedScalar10 HTGeometry.oddCompactReflectedScalar10_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]
  · have h := reflected_eq_of_scalar 12 HTGeometry.evenCompactReflectedScalar12 HTGeometry.evenCompactReflectedScalar12_eq x
    norm_num [HTGeometry.evenCompactSignedMoment]
    rw [h]

/-- Fixed balancing and coupled substitution keep the actual mass and every native moment. -/
theorem thetaCuspNativeEvenJet_unit_eq {x t v : ℝ}
    (ha : a x = HTGeometry.evenCompactUnitGap (u x^(2 : ℕ)) t)
    (hw : w x = u x*(1+v/4)) (k : Fin 7) :
    (-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) x =
      M x^(2 : ℕ)*(100 : ℝ)^k.val*HTGeometry.evenCompactUnitMoment k (u x^(2 : ℕ)) t v := by
  have h := HTGeometry.evenCompactSignedMoment_unit_eq k (u x) t v
  rw [← ha, ← hw] at h
  have hm := (div_eq_iff (by positivity : (100 : ℝ)^k.val ≠ 0)).mp h
  rw [thetaCuspNativeEvenJet_eq_compactScalar, hm]
  ring

private theorem head_det_eq (x : ℝ) :
    (thetaCuspNativeEvenHead x).det =
      thetaCuspNativeReflectionJet 0 x*thetaCuspNativeReflectionJet 4 x*thetaCuspNativeReflectionJet 8 x-
      thetaCuspNativeReflectionJet 0 x*(-thetaCuspNativeReflectionJet 6 x)^(2 : ℕ)-
      (-thetaCuspNativeReflectionJet 2 x)^(2 : ℕ)*thetaCuspNativeReflectionJet 8 x+
      2*(-thetaCuspNativeReflectionJet 2 x)*thetaCuspNativeReflectionJet 4 x*(-thetaCuspNativeReflectionJet 6 x)-
      thetaCuspNativeReflectionJet 4 x^(3 : ℕ) := by
  norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, Matrix.det_fin_three]
  ring

/-- The exact determinant normalization retains the complete-source head cofactor of the correction. -/
theorem thetaCuspEvenCompactUnitDet_eq_source_ratio {x t v : ℝ}
    (ha : a x = HTGeometry.evenCompactUnitGap (u x^(2 : ℕ)) t)
    (hw : w x = u x*(1+v/4)) :
    HTGeometry.evenCompactUnitDet (u x^(2 : ℕ)) t v =
      (thetaCuspNativeEvenFourDet x+
        1000000000000*M x^(2 : ℕ)*HTGeometry.evenCompactUnitCorrection (u x^(2 : ℕ)) t*
          (thetaCuspNativeEvenHead x).det) / ((100 : ℝ)^(12 : ℕ)*M x^(8 : ℕ)) := by
  have h0 := thetaCuspNativeEvenJet_unit_eq ha hw 0
  have h1 := thetaCuspNativeEvenJet_unit_eq ha hw 1
  have h2 := thetaCuspNativeEvenJet_unit_eq ha hw 2
  have h3 := thetaCuspNativeEvenJet_unit_eq ha hw 3
  have h4 := thetaCuspNativeEvenJet_unit_eq ha hw 4
  have h5 := thetaCuspNativeEvenJet_unit_eq ha hw 5
  have h6 := thetaCuspNativeEvenJet_unit_eq ha hw 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  rw [thetaCuspNativeEvenFourDet_eq, head_det_eq, h0, h1, h2, h3, h4, h5, h6]
  unfold HTGeometry.evenCompactUnitDet hankelFourDet
  field_simp [(thetaCuspCompletedThetaProfile_pos x).ne']
  ring

end
end RHTower
