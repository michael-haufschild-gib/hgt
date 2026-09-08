import GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularLaplacian

/-!
# Integral cusp transport for actual C² Maass eigenforms

The holomorphic Möbius second chain rule gives covariance of the actual positive
hyperbolic Laplacian at the source's C² regularity. Integral conjugation preserves
principal congruence invariance; inverse translation preserves nonvanishing;
composition of scaling matrices preserves decay at every integral cusp.

These constructions transport the exact physical cusp quarter-energy and Bessel
boundary identity to every integral scaling matrix. The period used is the
principal congruence level, without a claim of minimal cusp width. The compact
quotient-core estimate is not asserted.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
open RHTower.D4BMModularCore

namespace GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
noncomputable section

private theorem chart_contDiffAt {f : ℍ → ℂ} (hf : IsRealSmoothUpperHalfPlane f) (z : ℍ) :
    ContDiffAt ℝ 2 (f ∘ ofComplex) (z : ℂ) :=
  hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

private theorem chart_laplacian_pullback (A : SL2Z) (f : ℍ → ℂ)
    (hf : IsRealSmoothUpperHalfPlane f) (z : ℍ) :
    chartLaplacian (fun w => f (A • w)) z = chartLaplacian f (A • z) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : ℍ) : ℂ)
  have hdet : 0 < (A : GL (Fin 2) ℝ).val.det := by
    change 0 < (A : GL (Fin 2) ℝ).det.val
    simp
  have hG : ContDiffAt ℂ 2 G (z : ℂ) :=
    (UpperHalfPlane.analyticAt_smul (g := (A : GL (Fin 2) ℝ)) hdet z).contDiffAt
  have hF : ContDiffAt ℝ 2 (f ∘ ofComplex) (G (z : ℂ)) := by
    simpa only [G, ofComplex_apply, sl_moeb] using chart_contDiffAt hf (A • z)
  have hc := planarLaplacian_holomorphic_comp hF hG
  have hfun : (f ∘ ofComplex) ∘ G = (fun w : ℍ => f (A • w)) ∘ ofComplex := by
    funext w
    simp only [G, Function.comp_apply, ofComplex_apply]
  rw [hfun] at hc
  have hd : deriv G (z : ℂ) = 1 / (denom A z) ^ 2 := by
    have hdetone : (A : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A).det_coe
    simpa only [G, hdetone, Complex.ofReal_one, sl_moeb] using
      UpperHalfPlane.deriv_smul (g := (A : GL (Fin 2) ℝ)) hdet z
  simp only [G, ofComplex_apply] at hc
  unfold chartLaplacian
  rw [hc, hd, ← mul_assoc]
  congr 1
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.ofReal_div, div_pow,
    Complex.normSq_div, Complex.normSq_one, map_pow]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow]
  ring

private theorem positive_eq_neg_chart (f : ℍ → ℂ) (z : ℍ) :
    positiveHyperbolicLaplacian f z = -chartLaplacian f z := by
  simp only [positiveHyperbolicLaplacian, chartLaplacian, planarLaplacian,
    Fin.sum_univ_two, direction, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul]

/-- The positive hyperbolic Laplacian commutes with each integral Möbius pullback at real C² regularity. -/
theorem positive_laplacian_pullback (A : SL2Z) (f : ℍ → ℂ)
    (hf : IsRealSmoothUpperHalfPlane f) (z : ℍ) :
    positiveHyperbolicLaplacian (fun w => f (A • w)) z =
      positiveHyperbolicLaplacian f (A • z) := by
  rw [positive_eq_neg_chart, chart_laplacian_pullback A f hf, positive_eq_neg_chart]

/-- An integral Möbius pullback retains the actual real C² chart regularity. -/
theorem smooth_pullback (A : SL2Z) (f : ℍ → ℂ)
    (hf : IsRealSmoothUpperHalfPlane f) :
    IsRealSmoothUpperHalfPlane (fun w => f (A • w)) := by
  intro w hw
  let z : ℍ := ⟨w, hw⟩
  have hG : ContDiffAt ℝ 2 (fun v : ℂ => ((A • ofComplex v : ℍ) : ℂ)) (z : ℂ) :=
    ((UpperHalfPlane.analyticAt_smul (g := (A : GL (Fin 2) ℝ))
      (by change 0 < (A : GL (Fin 2) ℝ).det.val; simp) z).contDiffAt).restrict_scalars ℝ
  have hF : ContDiffAt ℝ 2 (f ∘ ofComplex) ((A • ofComplex (z : ℂ) : ℍ) : ℂ) := by
    simpa only [ofComplex_apply] using chart_contDiffAt hf (A • z)
  have h := (hF.comp (z : ℂ) hG).contDiffWithinAt (s := {v : ℂ | 0 < v.im})
  simpa only [Function.comp_def, ofComplex_apply] using h

@[simp]theorem integral_action (A : SL2Z) (z : ℍ) :
    integralSL2ToReal A • z = A • z := rfl

/-- The actual C² eigenfunction equation is preserved with the same eigenvalue. -/
theorem eigenfunction_pullback (A : SL2Z) (lam : ℝ) (f : ℍ → ℂ)
    (hf : IsMaassEigenfunction lam f) :
    IsMaassEigenfunction lam (fun w => f (A • w)) :=
  ⟨smooth_pullback A f hf.1, fun z => by
    rw [positive_laplacian_pullback A f hf.1 z]
    exact hf.2 (A • z)⟩

/-- All integral cusp decay conditions are preserved by composing scaling matrices. -/
theorem cuspidal_pullback (A : SL2Z) (f : ℍ → ℂ)
    (hf : IsCuspidalAtIntegralCusps f) :
    IsCuspidalAtIntegralCusps (fun w => f (A • w)) := by
  intro B
  simpa only [integral_action, mul_smul] using hf (A * B)

/-- Pullback on principal-congruence invariant functions, constructed from integral normality. -/
def invariantPullback (N : ℕ) (A : SL2Z)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N))) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N)) :=
  ⟨fun z => f.1 (A • z), by
    intro γ z
    obtain ⟨g, hg, he⟩ := γ.2
    have hconj := (CongruenceSubgroup.Gamma_normal N).conj_mem g hg A
    have hr : integralSL2ToReal (A * g * A⁻¹) ∈ realImage (CongruenceSubgroup.Gamma N) :=
      ⟨A * g * A⁻¹, hconj, rfl⟩
    have h := f.2 ⟨_, hr⟩ (A • z)
    simpa only [← he, integral_action, mul_smul, inv_smul_smul] using h⟩

@[simp]theorem invariantPullback_apply (N : ℕ) (A : SL2Z)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N))) (z : ℍ) :
    (invariantPullback N A f).1 z = f.1 (A • z) := rfl

/-- An integral pullback of a nonzero invariant function remains nonzero. -/
theorem invariantPullback_nonzero (N : ℕ) (A : SL2Z)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N)))
    (hf : f ≠ 0) : invariantPullback N A f ≠ 0 := by
  intro h
  apply hf
  apply Subtype.ext
  funext z
  have hv := congrArg (fun g => g.1 (A⁻¹ • z)) h
  simpa only [invariantPullback_apply, smul_inv_smul, ZeroMemClass.coe_zero, Pi.zero_apply] using hv

/-- The actual translated Maass cusp eigenform at the same principal congruence level and eigenvalue. -/
def translate (N : ℕ) (A : SL2Z) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam :=
  ⟨invariantPullback N A f.1,
    invariantPullback_nonzero N A f.1 f.2.1,
    eigenfunction_pullback A lam f.1.1 f.2.2.1,
    cuspidal_pullback A f.1.1 f.2.2.2⟩

@[simp]theorem translate_apply (N : ℕ) (A : SL2Z) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) (z : ℍ) :
    (translate N A f).1.1 z = f.1.1 (A • z) := rfl

/-- Successive pullbacks compose in the order of the original scaling matrices. -/
theorem translate_mul (N : ℕ) (A B : SL2Z) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) :
    translate N B (translate N A f) = translate N (A * B) f := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  simp only [translate_apply, mul_smul]

@[simp]theorem translate_one (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) :
    translate N 1 f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  simp only [translate_apply, one_smul]

/-- Integral pullback is an equivalence of actual Maass cusp eigenforms. -/
def translateEquiv (N : ℕ) (A : SL2Z) (lam : ℝ) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam ≃
      MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam where
  toFun := translate N A
  invFun := translate N A⁻¹
  left_inv f := by rw [translate_mul, mul_inv_cancel, translate_one]
  right_inv f := by rw [translate_mul, inv_mul_cancel, translate_one]

/-- A scaling matrix in the principal congruence subgroup acts trivially. -/
theorem translate_congruence (N : ℕ) (A : SL2Z) (hA : A ∈ CongruenceSubgroup.Gamma N)
    {lam : ℝ} (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) :
    translate N A f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  exact f.1.2 ⟨integralSL2ToReal A, ⟨A, hA, rfl⟩⟩ z

open MeasureTheory SelbergMaassFourier SelbergMaassTrace SelbergBoundaryOperator
  SelbergMaassParseval SelbergMaassFlux SelbergMaassBoundaryForm

/-- The actual constant Fourier coefficient vanishes at every integral cusp in the exceptional interval. -/
theorem cusp_constant_coefficient_zero (N : ℕ) (A : SL2Z)
    (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) :
    maassCoefficient N (translate (N + 1) A f) 0 y = 0 :=
  SelbergMaassBessel.constant_mode_zero N lam (translate (N + 1) A f) hy

/-- At every integral cusp, physical quarter-energy equals its actual Bessel boundary form plus convergent squares. -/
theorem cusp_boundary_square_identity (N : ℕ) (A : SL2Z)
    (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * (∫ y in Ioi (Real.exp T),
        quarterSlice N (translate (N + 1) A f) y) =
      boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N (translate (N + 1) A f) T) +
        ∑' n : ℤ, modeSquareTail N (translate (N + 1) A f) T n :=
  maass_boundary_square_identity N lam (translate (N + 1) A f) T

/-- The actual Bessel form bounds the physical quarter-energy below at every integral cusp. -/
theorem cusp_boundary_form_lower_bound (N : ℕ) (A : SL2Z)
    (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N (translate (N + 1) A f) T) ≤
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ y in Ioi (Real.exp T),
        quarterSlice N (translate (N + 1) A f) y :=
  maass_boundary_form_lower_bound N lam (translate (N + 1) A f) T

/-- At every integral cusp, actual outgoing flux and spectral tail mass equal the boundary form plus squares. -/
theorem cusp_flux_boundary_identity (N : ℕ) (A : SL2Z)
    (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    -flux N (translate (N + 1) A f) (Real.exp T) + ((lam : ℝ) - 1 / 4) *
        (∫ y in Ioi (Real.exp T), mass N (translate (N + 1) A f) y / y ^ 2) =
      boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N (translate (N + 1) A f) T) +
        ∑' n : ℤ, modeSquareTail N (translate (N + 1) A f) T n :=
  maass_flux_boundary_identity N lam (translate (N + 1) A f) T

end
end GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
