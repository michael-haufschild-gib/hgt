import GaloisForLFunctions.RHTower.ProlateSmallApertureMomentFlagSturm
import GaloisForLFunctions.RHTower.ProlateIndexedSeparationSpectrum
import GaloisForLFunctions.RHTower.ProlateFourierBandEigen

/-!
# Indexed prolate separation from the moment flag

This module closes the representation seam between canonical indexed Slepian
singular modes and their radial prolate separation values.  Polynomial test
vectors intertwine the finite Fourier synthesis with the full prolate action,
so every indexed output mode satisfies the exact weak Sturm equation carrying
the canonical `signedModeRadialData.chi`.

Combining that identity with the intrinsic zero-band moment-flag eigenline and
the already established projective output-line limit forces, for every fixed
even index `n`,

`chi_n(a) → -(2n)(2n+1)` as `a → 0+`.

No explicit Legendre formula, numerical computation, asymptotic expansion, or
spectral-label premise is used.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem integral_unitPhysicalInterval_eq_intervalIntegral
    (F : ℝ → ℂ) :
    (∫ x : UnitPhysicalInterval, F (x : ℝ) ∂volume) =
      ∫ x in (-1 : ℝ)..1, F x := by
  calc
    (∫ x : UnitPhysicalInterval, F (x : ℝ) ∂volume) =
        ∫ x in Icc (-1 : ℝ) 1, F x := by
      exact MeasureTheory.integral_subtype measurableSet_Icc F
    _ = ∫ x in Ioc (-1 : ℝ) 1, F x :=
      MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in (-1 : ℝ)..1, F x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]

theorem inner_apertureMomentFourierSynthesis_ofReal_bandClass
    (p : Polynomial ℂ) (c : ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    inner ℂ (apertureCpolyToL2 1 p)
        (apertureMomentFourierSynthesis 0 c
          (GaloisForLFunctions.HTGeometry.ofRealLp (bandClass Φ hΦ))) =
      ∫ x in (-1 : ℝ)..1, ((Φ x : ℝ) : ℂ) *
        inner ℂ (apertureCpolyToL2 1 p)
          (apertureFourierL2 1 (c * x)) := by
  rw [apertureMomentFourierSynthesis, apertureMomentSynthesisMap_apply,
    l2Synthesis_apply]
  have hint : Integrable (fun x : UnitPhysicalInterval =>
      GaloisForLFunctions.HTGeometry.ofRealLp (bandClass Φ hΦ) x •
        apertureMomentFourierFieldL2 0 c x) volume := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (apertureMomentFourierFieldL2 0 c)).smul
        (Lp.memLp (GaloisForLFunctions.HTGeometry.ofRealLp (bandClass Φ hΦ))))
  have hinner := (innerSL ℂ (apertureCpolyToL2 1 p)).integral_comp_comm hint
  simp only [coe_innerSL_apply] at hinner
  calc
    inner ℂ (apertureCpolyToL2 1 p)
        (∫ x : UnitPhysicalInterval,
          GaloisForLFunctions.HTGeometry.ofRealLp (bandClass Φ hΦ) x •
            apertureMomentFourierFieldL2 0 c x ∂volume) =
      ∫ x : UnitPhysicalInterval,
        inner ℂ (apertureCpolyToL2 1 p)
          (GaloisForLFunctions.HTGeometry.ofRealLp (bandClass Φ hΦ) x •
            apertureMomentFourierFieldL2 0 c x) ∂volume := hinner.symm
    _ =
        ∫ x : UnitPhysicalInterval, (((Φ (x : ℝ) : ℝ) : ℂ) *
          inner ℂ (apertureCpolyToL2 1 p)
            (apertureFourierL2 1 (c * (x : ℝ)))) ∂volume := by
      apply integral_congr_ae
      filter_upwards [apertureMomentFourierFieldL2_zero_coeFn c,
        GaloisForLFunctions.HTGeometry.coeFn_ofRealLp (bandClass Φ hΦ),
        coeFn_bandClass Φ hΦ] with x hfield hof hband
      rw [hfield, hof, hband, inner_smul_right]
    _ = _ := integral_unitPhysicalInterval_eq_intervalIntegral
      (fun x : ℝ => ((Φ x : ℝ) : ℂ) *
        inner ℂ (apertureCpolyToL2 1 p)
          (apertureFourierL2 1 (c * x)))

def prolatePolynomialAction (c : ℝ) (p : Polynomial ℂ) : Polynomial ℂ :=
  zeroBandPolynomialAction p -
    ((c ^ 2 : ℝ) : ℂ) • (Polynomial.X ^ 2 * p)

theorem prolatePolynomialAction_eval (c : ℝ) (p : Polynomial ℂ) (x : ℝ) :
    Polynomial.eval (x : ℂ) (prolatePolynomialAction c p) =
      complexProlateSLAction c (fun y : ℝ => Polynomial.eval (y : ℂ) p) x := by
  rw [prolatePolynomialAction, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    zeroBandPolynomialAction_eval]
  simp [complexProlateSLAction]
  ring

theorem coefficientConjugatePolynomial_prolatePolynomialAction
    (c : ℝ) (p : Polynomial ℂ) :
    coefficientConjugatePolynomial (prolatePolynomialAction c p) =
      prolatePolynomialAction c (coefficientConjugatePolynomial p) := by
  unfold prolatePolynomialAction
  change Polynomial.map (starRingEnd ℂ)
      (zeroBandPolynomialAction p -
        ((c ^ 2 : ℝ) : ℂ) • (Polynomial.X ^ 2 * p)) =
    zeroBandPolynomialAction (coefficientConjugatePolynomial p) -
      ((c ^ 2 : ℝ) : ℂ) •
        (Polynomial.X ^ 2 * coefficientConjugatePolynomial p)
  rw [Polynomial.map_sub, ← coefficientConjugatePolynomial,
    coefficientConjugatePolynomial_zeroBandPolynomialAction]
  congr 1
  simp [coefficientConjugatePolynomial, Polynomial.map_smul,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

theorem inner_apertureCpolyToL2_apertureFourierL2_eq_fourierBandTransform
    (p : Polynomial ℂ) (c x : ℝ) :
    inner ℂ (apertureCpolyToL2 1 p) (apertureFourierL2 1 (c * x)) =
      fourierBandTransform (-c)
        (fun t : ℝ => Polynomial.eval (t : ℂ)
          (coefficientConjugatePolynomial p)) x := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ t : ℝ, inner ℂ
        ((apertureCpolyToL2 1 p : UnitApertureL2) t)
        ((apertureFourierL2 1 (c * x) : UnitApertureL2) t)
          ∂apertureMeasure 1) =
        ∫ t : ℝ,
          Polynomial.eval (t : ℂ) (coefficientConjugatePolynomial p) *
            Complex.exp (-((c * x : ℝ) : ℂ) * Complex.I * (t : ℂ))
          ∂apertureMeasure 1 := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_apertureCpoly 1 p).coeFn_toLp,
        (memLp_apertureFourier 1 (c * x)).coeFn_toLp] with t hp ht
      change inner ℂ
        (((memLp_apertureCpoly 1 p).toLp _ : UnitApertureL2) t)
        (((memLp_apertureFourier 1 (c * x)).toLp _ : UnitApertureL2) t) = _
      rw [hp, ht, RCLike.inner_apply,
        ← coefficientConjugatePolynomial_eval_real]
      ring
    _ = ∫ t in (-1 : ℝ)..1,
          Polynomial.eval (t : ℂ) (coefficientConjugatePolynomial p) *
            Complex.exp (-((c * x : ℝ) : ℂ) * Complex.I * (t : ℂ)) := by
      rw [apertureMeasure, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num)]
    _ = fourierBandTransform (-c)
          (fun t : ℝ => Polynomial.eval (t : ℂ)
            (coefficientConjugatePolynomial p)) x := by
      rw [fourierBandTransform]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      unfold bandKernel
      rw [mul_comm]
      congr 1
      push_cast
      ring_nf

theorem deriv_fourierBandTransform_complex
    (c : ℝ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    deriv (fourierBandTransform c f) = fun x : ℝ =>
      ∫ t in (-1 : ℝ)..1,
        bandKernel c x t * (Complex.I * ((c * t : ℝ) : ℂ)) * f t := by
  funext x
  exact (hasDerivAt_bandKernelTransform hf x).deriv

theorem deriv2_fourierBandTransform_complex
    (c : ℝ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    deriv (deriv (fourierBandTransform c f)) = fun x : ℝ =>
      ∫ t in (-1 : ℝ)..1,
        bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t := by
  rw [deriv_fourierBandTransform_complex c f hf]
  funext x
  exact (hasDerivAt_bandTransformDeriv hf x).deriv

theorem differentiable_fourierBandTransform_complex
    (c : ℝ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    Differentiable ℝ (fourierBandTransform c f) :=
  fun x => (hasDerivAt_bandKernelTransform hf x).differentiableAt

theorem differentiable_deriv_fourierBandTransform_complex
    (c : ℝ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    Differentiable ℝ (deriv (fourierBandTransform c f)) := by
  rw [deriv_fourierBandTransform_complex c f hf]
  exact fun x => (hasDerivAt_bandTransformDeriv hf x).differentiableAt

theorem continuous_deriv2_fourierBandTransform_complex
    (c : ℝ) (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    Continuous (deriv (deriv (fourierBandTransform c f))) := by
  rw [deriv2_fourierBandTransform_complex c f hf]
  let g : ℝ → ℂ := fun t => -(((c * t : ℝ) : ℂ)) ^ 2 * f t
  have hg : IntervalIntegrable g volume (-1) 1 := by
    have hpow := intervalIntegrable_kernelPow_mul (c := c) hf 2
    refine hpow.congr ?_
    intro t _
    dsimp only [g]
    have hI : Complex.I ^ 2 = -1 := by
      rw [pow_two, Complex.I_mul_I]
    rw [mul_pow, hI]
    ring
  have hfun :
      (fun x : ℝ => ∫ t in (-1 : ℝ)..1,
        bandKernel c x t * (-(((c * t : ℝ) : ℂ)) ^ 2) * f t) =
      fun x : ℝ => ∫ t in (-1 : ℝ)..1, bandKernel c x t * g t := by
    funext x
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g]
    ring
  rw [hfun]
  exact (show Differentiable ℝ
      (fun x : ℝ => ∫ t in (-1 : ℝ)..1, bandKernel c x t * g t) from
    fun x =>
      (hasDerivAt_bandKernelTransform (c := c) hg x).differentiableAt).continuous

theorem complexProlateSLAction_fourierBandTransform_polynomial
    (c : ℝ) (p : Polynomial ℂ) (x : ℝ) :
    complexProlateSLAction c
        (fourierBandTransform (-c)
          (fun t : ℝ => Polynomial.eval (t : ℂ) p)) x =
      fourierBandTransform (-c)
        (fun t : ℝ => Polynomial.eval (t : ℂ)
          (prolatePolynomialAction c p)) x := by
  let f : ℝ → ℂ := fun t => Polynomial.eval (t : ℂ) p
  let Df : ℝ → ℂ := fun t => Polynomial.eval (t : ℂ) p.derivative
  let DDf : ℝ → ℂ := fun t => Polynomial.eval (t : ℂ) p.derivative.derivative
  change complexProlateSLAction c (fourierBandTransform (-c) f) x =
    fourierBandTransform (-c)
      (fun t : ℝ => Polynomial.eval (t : ℂ)
        (prolatePolynomialAction c p)) x
  have hf : IntervalIntegrable f volume (-1) 1 :=
    (continuous_cpoly p).intervalIntegrable _ _
  have hfd : ∀ y ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (Df y) y := by
    intro y _
    exact (p.hasDerivAt (y : ℂ)).comp_ofReal
  have hfd2 : ∀ y ∈ uIcc (-1 : ℝ) 1, HasDerivAt Df (DDf y) y := by
    intro y _
    exact (p.derivative.hasDerivAt (y : ℂ)).comp_ofReal
  have hleft : IntervalIntegrable
      (fun t : ℝ => prolateActionC (-c)
          (fun s => bandKernel (-c) x s)
          (fun s => bandKernel (-c) x s *
            (Complex.I * (((-c) * x : ℝ) : ℂ)))
          (fun s => bandKernel (-c) x s *
            (-((((-c) * x : ℝ) : ℂ)) ^ 2)) t * f t)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [f]
    unfold prolateActionC bandKernel
    fun_prop
  have hright : IntervalIntegrable
      (fun t : ℝ => bandKernel (-c) x t *
        prolateActionC (-c) f Df DDf t) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [f, Df, DDf]
    unfold prolateActionC bandKernel
    fun_prop
  have hcomm := prolateAction_bandTransform_commutes
    (c := -c) (f := f) (Df := Df) (DDf := DDf)
    x hf hfd hfd2 hleft hright
  have hD1 := deriv_fourierBandTransform_complex (-c) f hf
  have hD2 := deriv2_fourierBandTransform_complex (-c) f hf
  have haction : ∀ t : ℝ,
      prolateActionC (-c) f Df DDf t =
        Polynomial.eval (t : ℂ) (prolatePolynomialAction c p) := by
    intro t
    rw [prolatePolynomialAction_eval]
    dsimp only [f, Df, DDf]
    have hd1 := deriv_polynomial_eval_ofReal p t
    have hd2 := deriv_polynomial_eval_ofReal p.derivative t
    have hfun : deriv (fun y : ℝ => Polynomial.eval (y : ℂ) p) =
        fun y : ℝ => Polynomial.eval (y : ℂ) p.derivative := by
      funext y
      exact deriv_polynomial_eval_ofReal p y
    rw [complexProlateSLAction, prolateActionC, hd1, hfun, hd2]
    push_cast
    ring
  rw [fourierBandTransform]
  rw [complexProlateSLAction, hD2, hD1]
  change _ = ∫ t in (-1 : ℝ)..1,
    bandKernel (-c) x t *
      Polynomial.eval (t : ℂ) (prolatePolynomialAction c p)
  simp_rw [← haction]
  rw [← hcomm]
  unfold fourierBandTransform
  push_cast
  ring

theorem inner_prolatePolynomialAction_apertureFourierL2
    (p : Polynomial ℂ) (c x : ℝ) :
    inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p))
        (apertureFourierL2 1 (c * x)) =
      complexProlateSLAction c
        (fun y : ℝ => inner ℂ (apertureCpolyToL2 1 p)
          (apertureFourierL2 1 (c * y))) x := by
  calc
    inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p))
        (apertureFourierL2 1 (c * x)) =
      fourierBandTransform (-c)
        (fun t : ℝ => Polynomial.eval (t : ℂ)
          (coefficientConjugatePolynomial
            (prolatePolynomialAction c p))) x :=
        inner_apertureCpolyToL2_apertureFourierL2_eq_fourierBandTransform
          (prolatePolynomialAction c p) c x
    _ = fourierBandTransform (-c)
        (fun t : ℝ => Polynomial.eval (t : ℂ)
          (prolatePolynomialAction c (coefficientConjugatePolynomial p))) x := by
      rw [coefficientConjugatePolynomial_prolatePolynomialAction]
    _ = complexProlateSLAction c
        (fourierBandTransform (-c)
          (fun t : ℝ => Polynomial.eval (t : ℂ)
            (coefficientConjugatePolynomial p))) x :=
      (complexProlateSLAction_fourierBandTransform_polynomial c
        (coefficientConjugatePolynomial p) x).symm
    _ = complexProlateSLAction c
        (fun y : ℝ => inner ℂ (apertureCpolyToL2 1 p)
          (apertureFourierL2 1 (c * y))) x := by
      congr 1
      funext y
      exact
        (inner_apertureCpolyToL2_apertureFourierL2_eq_fourierBandTransform
          p c y).symm

theorem inner_apertureMomentFourierSynthesis_ofReal_prolate_eigen
    (p : Polynomial ℂ) (c chi : ℝ) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ x : ℝ, prolateSLAction c Φ x = chi * Φ x) :
    inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p))
        (apertureMomentFourierSynthesis 0 c
          (GaloisForLFunctions.HTGeometry.ofRealLp
            (bandClass Φ hΦ.continuous))) =
      (chi : ℂ) *
        inner ℂ (apertureCpolyToL2 1 p)
          (apertureMomentFourierSynthesis 0 c
            (GaloisForLFunctions.HTGeometry.ofRealLp
              (bandClass Φ hΦ.continuous))) := by
  let q : Polynomial ℂ := coefficientConjugatePolynomial p
  let f : ℝ → ℂ := fun t => Polynomial.eval (t : ℂ) q
  let psi : ℝ → ℂ := fun x => inner ℂ (apertureCpolyToL2 1 p)
    (apertureFourierL2 1 (c * x))
  have hf : IntervalIntegrable f volume (-1) 1 :=
    (continuous_cpoly q).intervalIntegrable _ _
  have hpsi : psi = fourierBandTransform (-c) f := by
    funext x
    exact inner_apertureCpolyToL2_apertureFourierL2_eq_fourierBandTransform
      p c x
  have hpsi1 : Differentiable ℝ psi := by
    rw [hpsi]
    exact differentiable_fourierBandTransform_complex (-c) f hf
  have hpsi2 : Differentiable ℝ (deriv psi) := by
    rw [hpsi]
    exact differentiable_deriv_fourierBandTransform_complex (-c) f hf
  have hpsi2c : Continuous (deriv (deriv psi)) := by
    rw [hpsi]
    exact continuous_deriv2_fourierBandTransform_complex (-c) f hf
  have hΦ1 : Differentiable ℝ Φ :=
    (contDiff_infty_iff_deriv.mp hΦ).1
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp hΦ).2
  have hΦ2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp hΦd).1
  have hΦ2c : Continuous (deriv (deriv Φ)) :=
    (contDiff_infty_iff_deriv.mp hΦd).2.continuous
  let PhiC : ℝ → ℂ := fun x => ((Φ x : ℝ) : ℂ)
  have hPhiC1 : Differentiable ℝ PhiC := by
    dsimp only [PhiC]
    exact fun x =>
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hΦ1 x).hasDerivAt).differentiableAt
  have hPhiCDeriv : deriv PhiC = fun x => ((deriv Φ x : ℝ) : ℂ) := by
    funext x
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (hΦ1 x).hasDerivAt).deriv
  have hPhiC2 : Differentiable ℝ (deriv PhiC) := by
    rw [hPhiCDeriv]
    exact fun x =>
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hΦ2 x).hasDerivAt).differentiableAt
  have hPhiCDeriv2 : deriv (deriv PhiC) =
      fun x => ((deriv (deriv Φ) x : ℝ) : ℂ) := by
    rw [hPhiCDeriv]
    funext x
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (hΦ2 x).hasDerivAt).deriv
  have hPhiC2c : Continuous (deriv (deriv PhiC)) := by
    rw [hPhiCDeriv2]
    exact Complex.continuous_ofReal.comp hΦ2c
  have hPhiCAction : ∀ x : ℝ,
      complexProlateSLAction c PhiC x =
        (chi : ℂ) * PhiC x := by
    intro x
    rw [complexProlateSLAction, hPhiCDeriv2, hPhiCDeriv]
    dsimp only [PhiC]
    have hx := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (heig x)
    rw [prolateSLAction] at hx
    push_cast at hx ⊢
    exact hx
  have hbil := complexProlateSLAction_band_bilinear_symmetric
    (f := psi) (g := PhiC) hpsi1 hpsi2 hpsi2c
    hPhiC1 hPhiC2 hPhiC2c c
  rw [inner_apertureMomentFourierSynthesis_ofReal_bandClass,
    inner_apertureMomentFourierSynthesis_ofReal_bandClass]
  simp_rw [inner_prolatePolynomialAction_apertureFourierL2]
  change (∫ x in (-1 : ℝ)..1,
      PhiC x * complexProlateSLAction c psi x) =
    (chi : ℂ) * ∫ x in (-1 : ℝ)..1, PhiC x * psi x
  calc
    (∫ x in (-1 : ℝ)..1,
        PhiC x * complexProlateSLAction c psi x) =
      ∫ x in (-1 : ℝ)..1,
        psi x * complexProlateSLAction c PhiC x := hbil
    _ = ∫ x in (-1 : ℝ)..1,
        psi x * ((chi : ℂ) * PhiC x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change psi x * complexProlateSLAction c PhiC x =
        psi x * ((chi : ℂ) * PhiC x)
      rw [hPhiCAction]
    _ = (chi : ℂ) * ∫ x in (-1 : ℝ)..1, PhiC x * psi x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring

/-- Canonical indexed even output modes carry the exact canonical prolate
separation value in weak Sturm form on the polynomial core. -/
theorem indexedEvenSlepianOutputMode_weak_prolate_eigen
    {a : ℝ} (ha : 0 < a) (n : ℕ) (p : Polynomial ℂ) :
    let c := signedModeRadialBandwidth a
    let chi := (signedModeRadialData a n).chi
    inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p))
        (indexedEvenSlepianOutputMode c n) =
      (chi : ℂ) * inner ℂ (apertureCpolyToL2 1 p)
        (indexedEvenSlepianOutputMode c n) := by
  dsimp only
  let c : ℝ := signedModeRadialBandwidth a
  let D := signedModeRadialData a n
  have hc : 0 < c := by
    dsimp only [c, signedModeRadialBandwidth]
    positivity
  have hD := signedModeRadialData_isExact_of_pos ha n
  rcases hD with ⟨_hPhiSmooth, _hPhiNe, _hPhiEven, _hPhiOne,
    hRdef, hRSmooth, _hREven, hROne, hBand, hProlate,
    _hsdef, _hsnonneg, _hend, _hode⟩
  have hRNe : D.R ≠ 0 := by
    intro hzero
    have h := congrFun hzero 1
    exact one_ne_zero (hROne.symm.trans h)
  have hvalueNe : evenProlateSignedValue a n ^ 2 ≠ 0 :=
    pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n)
  have hRBand : ∀ x : ℝ,
      bandTransform c D.R x = evenProlateSignedValue a n ^ 2 * D.R x := by
    intro x
    change bandTransform (signedModeRadialBandwidth a)
      (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x
    rw [hRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hBand x
  let fr : RealIntervalL2 (-1 : ℝ) 1 := bandClass D.R hRSmooth.continuous
  have hfrNe : fr ≠ 0 :=
    bandClass_ne_zero_of_global_band_eigen hRSmooth.continuous
      hvalueNe hRNe hRBand
  have hfrEig : bandOperatorL2 c fr =
      (evenProlateSignedValue a n ^ 2) • fr :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hRSmooth.continuous hRBand
  let q : ComplexUnitIntervalL2 :=
    GaloisForLFunctions.HTGeometry.ofRealLp fr
  have hqNe : q ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [GaloisForLFunctions.HTGeometry.norm_ofRealLp, norm_zero] at hnorm
    exact hfrNe (norm_eq_zero.mp hnorm)
  have hqEig : complexBandOperatorL2 c q =
      ((evenProlateSignedValue a n ^ 2 : ℝ) : ℂ) • q := by
    rw [complexBandOperatorL2_ofRealLp, hfrEig,
      ofRealLp_real_smul]
  let xe : ComplexUnitIntervalL2 :=
    ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
      ComplexUnitIntervalL2)
  have hxeNe : xe ≠ 0 := by
    have hinNe : indexedEvenSlepianInputMode c n ≠ 0 := by
      intro hzero
      have hnorm := congrArg norm hzero
      rw [indexedEvenSlepianInputMode_norm hc n, norm_zero] at hnorm
      norm_num at hnorm
    intro hzero
    apply hinNe
    apply Subtype.ext
    exact hzero
  have hvalue : complexUnitBandEvenValue c n =
      evenProlateSignedValue a n ^ 2 := by
    dsimp only [c, signedModeRadialBandwidth]
    exact complexUnitBandEvenValue_eq_evenProlateSignedValue_sq ha n
  have hxeEig : complexBandOperatorL2 c xe =
      ((evenProlateSignedValue a n ^ 2 : ℝ) : ℂ) • xe := by
    have hblock := indexedEvenSlepianInputMode_eigen hc n
    have h := congrArg
      (fun w : complexUnitBandEvenSubspace => (w : ComplexUnitIntervalL2)) hblock
    have h' : complexBandOperatorL2 c xe =
        (complexUnitBandEvenValue c n : ℂ) • xe := by
      calc
        complexBandOperatorL2 c xe =
          (((complexUnitBandEvenValue c n : ℂ) •
            indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
              ComplexUnitIntervalL2) := by
            simpa only [xe, coe_complexUnitBandEvenBlock_apply] using h
        _ = _ := rfl
    rw [hvalue] at h'
    exact h'
  obtain ⟨z, hz⟩ := complexBandOperatorL2_eigenvectors_proportional
    hc hvalueNe hqNe hqEig hxeEig
  let alpha : ℂ :=
    ((indexedEvenSlepianSingularValue c n : ℝ) : ℂ)⁻¹ * z
  have hout : indexedEvenSlepianOutputMode c n =
      alpha • apertureMomentFourierSynthesis 0 c q := by
    rw [indexedEvenSlepianOutputMode]
    change ((indexedEvenSlepianSingularValue c n : ℝ) : ℂ)⁻¹ •
        apertureMomentFourierSynthesis 0 c xe = _
    rw [hz, map_smul, smul_smul]
  have hweak := inner_apertureMomentFourierSynthesis_ofReal_prolate_eigen
    p c D.chi D.R hRSmooth hProlate
  change inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p))
      (indexedEvenSlepianOutputMode c n) =
    (D.chi : ℂ) * inner ℂ (apertureCpolyToL2 1 p)
      (indexedEvenSlepianOutputMode c n)
  rw [hout, inner_smul_right, inner_smul_right, hweak]
  ring

theorem indexedEvenSlepianOutputMode_separation_defect_identity
    {a : ℝ} (ha : 0 < a) (n : ℕ) (p : Polynomial ℂ) (K : ℝ)
    (hp : zeroBandPolynomialAction p = -(K : ℂ) • p) :
    let c := signedModeRadialBandwidth a
    let D := signedModeRadialData a n
    let y := indexedEvenSlepianOutputMode c n
    ((D.chi : ℂ) + (K : ℂ)) *
        inner ℂ (apertureCpolyToL2 1 p) y =
      -((c ^ 2 : ℝ) : ℂ) *
        inner ℂ (apertureCpolyToL2 1 (Polynomial.X ^ 2 * p)) y := by
  dsimp only
  let c : ℝ := signedModeRadialBandwidth a
  let D := signedModeRadialData a n
  let y := indexedEvenSlepianOutputMode c n
  have haction : prolatePolynomialAction c p =
      -(K : ℂ) • p -
        ((c ^ 2 : ℝ) : ℂ) • (Polynomial.X ^ 2 * p) := by
    rw [prolatePolynomialAction, hp]
  have hA : apertureCpolyToL2 1 (prolatePolynomialAction c p) =
      -(K : ℂ) • apertureCpolyToL2 1 p -
        ((c ^ 2 : ℝ) : ℂ) •
          apertureCpolyToL2 1 (Polynomial.X ^ 2 * p) := by
    rw [haction, map_sub, map_smul, map_smul]
  have hweak := indexedEvenSlepianOutputMode_weak_prolate_eigen
    ha n p
  change inner ℂ (apertureCpolyToL2 1 (prolatePolynomialAction c p)) y =
    (D.chi : ℂ) * inner ℂ (apertureCpolyToL2 1 p) y at hweak
  rw [hA, inner_sub_left, inner_smul_left, inner_smul_left] at hweak
  simp only [map_neg, Complex.conj_ofReal] at hweak
  exact by
    linear_combination -hweak

theorem tendsto_norm_inner_apertureMomentFlagVector_indexedEvenOutput
    (n : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖inner ℂ (apertureMomentFlagVector (2 * n))
        (indexedEvenSlepianOutputMode c n)‖)
      (𝓝[>] (0 : ℝ))
      (nhds ‖apertureMomentFlagVector (2 * n)‖) := by
  let L := 𝓝[>] (0 : ℝ)
  let v : UnitApertureL2 := apertureMomentFlagVector (2 * n)
  let y : ℝ → UnitApertureL2 := fun c => indexedEvenSlepianOutputMode c n
  let z : ℝ → ℂ := fun c => indexedEvenMomentAlignmentCoeff c n
  have hvne : v ≠ 0 := apertureMomentFlagVector_ne_zero (2 * n)
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
  have hprojNorm : Tendsto (fun c : ℝ => ‖y c - z c • v‖) L (nhds 0) := by
    exact indexedEvenSlepianOutputMode_projective_flag n
  have hprojVec : Tendsto (fun c : ℝ => y c - z c • v) L (nhds 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa using hprojNorm
  have hres : Tendsto (fun c : ℝ => inner ℂ v (y c - z c • v))
      L (nhds 0) := by
    simpa using tendsto_const_nhds.inner hprojVec
  have hresNorm : Tendsto
      (fun c : ℝ => ‖inner ℂ v (y c - z c • v)‖) L (nhds 0) := by
    simpa using hres.norm
  have hzNorm : Tendsto (fun c : ℝ => ‖z c‖) L (nhds ‖v‖⁻¹) := by
    exact tendsto_norm_indexedEvenMomentAlignmentCoeff n
  have happroxNorm : Tendsto (fun c : ℝ => ‖inner ℂ v (z c • v)‖)
      L (nhds ‖v‖) := by
    have hmul := hzNorm.mul_const (‖v‖ ^ 2)
    have hlimit : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by
      field_simp
    rw [hlimit] at hmul
    exact hmul.congr' (Filter.Eventually.of_forall fun c => by
      have hself : ‖inner ℂ v v‖ = ‖v‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow]
        exact congrArg (fun r : ℝ => r ^ 2)
          (Complex.norm_of_nonneg (norm_nonneg v))
      change ‖z c‖ * ‖v‖ ^ 2 = ‖inner ℂ v (z c • v)‖
      rw [inner_smul_right, norm_mul, hself])
  have hlow : ∀ c : ℝ,
      ‖inner ℂ v (z c • v)‖ - ‖inner ℂ v (y c - z c • v)‖ ≤
        ‖inner ℂ v (y c)‖ := by
    intro c
    have hnorm := norm_sub_norm_le
      (inner ℂ v (z c • v)) (inner ℂ v (y c))
    have hdiff : inner ℂ v (z c • v) - inner ℂ v (y c) =
        -inner ℂ v (y c - z c • v) := by
      rw [inner_sub_right]
      ring
    rw [hdiff, norm_neg] at hnorm
    linarith
  have hupp : ∀ c : ℝ,
      ‖inner ℂ v (y c)‖ ≤
        ‖inner ℂ v (z c • v)‖ + ‖inner ℂ v (y c - z c • v)‖ := by
    intro c
    have hdecomp : inner ℂ v (y c) =
        inner ℂ v (z c • v) + inner ℂ v (y c - z c • v) := by
      rw [inner_sub_right]
      ring
    rw [hdecomp]
    exact norm_add_le _ _
  have hlowT := happroxNorm.sub hresNorm
  have huppT := happroxNorm.add hresNorm
  have hlowT' : Tendsto (fun c : ℝ =>
      ‖inner ℂ v (z c • v)‖ - ‖inner ℂ v (y c - z c • v)‖)
      L (nhds ‖v‖) := by simpa using hlowT
  have huppT' : Tendsto (fun c : ℝ =>
      ‖inner ℂ v (z c • v)‖ + ‖inner ℂ v (y c - z c • v)‖)
      L (nhds ‖v‖) := by simpa using huppT
  change Tendsto (fun c : ℝ => ‖inner ℂ v (y c)‖) L (nhds ‖v‖)
  exact Filter.Tendsto.squeeze hlowT' huppT' hlow hupp

theorem tendsto_signedModeRadialBandwidth_zero :
    Tendsto signedModeRadialBandwidth
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hzero : Tendsto signedModeRadialBandwidth
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      change Tendsto (fun a : ℝ => 2 * Real.pi * a ^ 2)
        (𝓝 (0 : ℝ)) (𝓝 0)
      have hconst : Tendsto (fun _ : ℝ => (2 * Real.pi : ℝ))
          (𝓝 (0 : ℝ)) (𝓝 (2 * Real.pi)) := tendsto_const_nhds
      simpa using hconst.mul (tendsto_id.pow 2)
    exact hzero.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    dsimp only [signedModeRadialBandwidth]
    exact Set.mem_Ioi.mpr (mul_pos (by positivity) (pow_pos ha 2))

/-- All canonical even prolate separation values have their exact zero-band
Sturm limits.  The proof uses no special-function asymptotic: indexed output
line convergence, the exact weak Sturm bridge, and the intrinsic polynomial
moment-flag eigenline force the limit. -/
theorem tendsto_signedModeRadialData_chi_smallAperture (n : ℕ) :
    Tendsto (fun a : ℝ => (signedModeRadialData a n).chi)
      (𝓝[>] (0 : ℝ))
      (nhds (-(((2 * n) * (2 * n + 1) : ℕ) : ℝ))) := by
  let L := 𝓝[>] (0 : ℝ)
  let k : ℕ := 2 * n
  let K : ℝ := ((k * (k + 1) : ℕ) : ℝ)
  obtain ⟨p, _hpSpan, hpFlag, _hpNe, hpEig⟩ :=
    exists_apertureMomentFlagPolynomial_zeroBand_eigen k
  have hpEig' : zeroBandPolynomialAction p = -(K : ℂ) • p := by
    convert hpEig using 1
    norm_num [K]
  let v : UnitApertureL2 := apertureMomentFlagVector k
  let w : UnitApertureL2 :=
    apertureCpolyToL2 1 (Polynomial.X ^ 2 * p)
  have hvNe : v ≠ 0 := apertureMomentFlagVector_ne_zero k
  have hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hvNe
  have hbw : Tendsto signedModeRadialBandwidth L L :=
    tendsto_signedModeRadialBandwidth_zero
  have hden : Tendsto (fun a : ℝ =>
      ‖inner ℂ v
        (indexedEvenSlepianOutputMode (signedModeRadialBandwidth a) n)‖)
      L (nhds ‖v‖) := by
    change Tendsto (fun a : ℝ =>
      ‖inner ℂ (apertureMomentFlagVector (2 * n))
        (indexedEvenSlepianOutputMode (signedModeRadialBandwidth a) n)‖)
      L (nhds ‖apertureMomentFlagVector (2 * n)‖)
    exact (tendsto_norm_inner_apertureMomentFlagVector_indexedEvenOutput n).comp hbw
  have hdenPos : ∀ᶠ a : ℝ in L,
      ‖v‖ / 2 <
        ‖inner ℂ v
          (indexedEvenSlepianOutputMode (signedModeRadialBandwidth a) n)‖ := by
    exact hden.eventually (Ioi_mem_nhds (by linarith))
  let C : ℝ := 2 * ‖w‖ / ‖v‖
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hCdelta : C * (‖v‖ / 2) = ‖w‖ := by
    dsimp only [C]
    field_simp
  have hbound : ∀ᶠ a : ℝ in L,
      ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ ≤
        C * signedModeRadialBandwidth a ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hdenPos] with a ha hdenLower
    have haPos : 0 < a := ha
    let c : ℝ := signedModeRadialBandwidth a
    let y : UnitApertureL2 := indexedEvenSlepianOutputMode c n
    have hcPos : 0 < c := by
      dsimp only [c, signedModeRadialBandwidth]
      positivity
    have hyNorm : ‖y‖ = 1 := indexedEvenSlepianOutputMode_norm hcPos n
    have hident := indexedEvenSlepianOutputMode_separation_defect_identity
      haPos n p K hpEig'
    change (((signedModeRadialData a n).chi : ℂ) + (K : ℂ)) *
        inner ℂ (apertureCpolyToL2 1 p) y =
      -((c ^ 2 : ℝ) : ℂ) * inner ℂ w y at hident
    rw [hpFlag] at hident
    have hidentNorm := congrArg norm hident
    have hcNorm : ‖((c ^ 2 : ℝ) : ℂ)‖ = c ^ 2 :=
      Complex.norm_of_nonneg (sq_nonneg c)
    rw [norm_mul, norm_mul, norm_neg, hcNorm] at hidentNorm
    have hinnerLe : ‖inner ℂ w y‖ ≤ ‖w‖ := by
      calc
        ‖inner ℂ w y‖ ≤ ‖w‖ * ‖y‖ := norm_inner_le_norm _ _
        _ = ‖w‖ := by rw [hyNorm, mul_one]
    have hprod :
        ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ *
            (‖v‖ / 2) ≤ c ^ 2 * ‖w‖ := by
      calc
        ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ *
            (‖v‖ / 2) ≤
          ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ *
            ‖inner ℂ v y‖ :=
          mul_le_mul_of_nonneg_left hdenLower.le (norm_nonneg _)
        _ = c ^ 2 * ‖inner ℂ w y‖ := hidentNorm
        _ ≤ c ^ 2 * ‖w‖ :=
          mul_le_mul_of_nonneg_left hinnerLe (sq_nonneg c)
    change ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ ≤ C * c ^ 2
    have hdelta : 0 < ‖v‖ / 2 := by positivity
    nlinarith [sq_nonneg c,
      norm_nonneg (((signedModeRadialData a n).chi : ℂ) + (K : ℂ))]
  have hbw0 : Tendsto signedModeRadialBandwidth L (nhds 0) :=
    hbw.mono_right nhdsWithin_le_nhds
  have hmajor : Tendsto (fun a : ℝ => C * signedModeRadialBandwidth a ^ 2)
      L (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hbw0.pow 2)
  have hchiNorm : Tendsto (fun a : ℝ =>
      ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖)
      L (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hK : K = (((2 * n) * (2 * n + 1) : ℕ) : ℝ) := by
    dsimp only [K, k]
  rw [← hK]
  exact hchiNorm.congr' (Filter.Eventually.of_forall fun a => by
    change ‖(((signedModeRadialData a n).chi : ℂ) + (K : ℂ))‖ =
      ‖(signedModeRadialData a n).chi - -K‖
    rw [Real.norm_eq_abs, sub_neg_eq_add, ← ofReal_add,
      Complex.norm_real, Real.norm_eq_abs])

end GaloisForLFunctions.RHTower
