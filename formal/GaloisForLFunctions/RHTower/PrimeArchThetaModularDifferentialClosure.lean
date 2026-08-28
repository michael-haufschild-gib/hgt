import GaloisForLFunctions.Bottcher.ModularLambdaCovering
import GaloisForLFunctions.Bottcher.ThetaDiscriminant
import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeClosure
import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveClosure
import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet
import GaloisForLFunctions.HTGeometry.SchwartzSpectralQuadraticSeparation
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureSixthSeamChamber
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets
import GaloisForLFunctions.Bottcher.Ramanujan

/-!
# Modular differential closure of the theta sixth seam

The completed real theta profile is the real-axis restriction of a holomorphic theta
nullwert.  Its four modular state variables obey an autonomous polynomial differential
system.  This file instantiates the generic jet elimination in `HTGeometry` and identifies
the resulting closed value with the actual RHTower source seam.
-/

open Complex Real HurwitzZeta
open UpperHalfPlane hiding I
open scoped ContDiff

namespace RHTower

noncomputable section

private def thetaModularTau (x : ℝ) : ℂ :=
  I * Complex.exp (2 * (x : ℂ))

private def thetaModularTauC (w : ℂ) : ℂ :=
  I * Complex.exp (2 * w)

private def thetaModularH (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) / 2) * Bottcher.thetaThree (thetaModularTau x)

private def thetaModularHC (w : ℂ) : ℂ :=
  Complex.exp (w / 2) * Bottcher.thetaThree (thetaModularTauC w)

private def thetaModularZ (x : ℝ) : ℂ :=
  2 * Bottcher.modularLambda (thetaModularTau x) - 1

private def thetaModularZC (w : ℂ) : ℂ :=
  2 * Bottcher.modularLambda (thetaModularTauC w) - 1

private def thetaModularR (x : ℝ) : ℂ :=
  (Real.pi : ℂ) * thetaModularH x ^ 4

private def thetaModularP (x : ℝ) : ℂ :=
  (Real.pi : ℂ) * Complex.exp (2 * (x : ℂ)) *
      EisensteinSeries.E2 (UpperHalfPlane.ofComplex (thetaModularTau x)) -
    3

private def thetaModularPC (w : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.exp (2 * w) *
      (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (thetaModularTauC w) -
    3

private theorem thetaModularTau_eq_tauC (x : ℝ) :
    thetaModularTau x = thetaModularTauC (x : ℂ) := rfl

private theorem thetaModularTau_im_pos (x : ℝ) :
    0 < (thetaModularTau x).im := by
  simp only [thetaModularTau, mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul]
  rw [show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by norm_num,
    Complex.exp_ofReal_re]
  simpa using Real.exp_pos (2 * x)

private theorem analyticAt_thetaModularTauC (w : ℂ) :
    AnalyticAt ℂ thetaModularTauC w := by
  unfold thetaModularTauC
  fun_prop

private theorem analyticAt_thetaThree_of_im_pos
    {τ : ℂ} (hτ : 0 < τ.im) :
    AnalyticAt ℂ Bottcher.thetaThree τ := by
  have hdiff : DifferentiableOn ℂ Bottcher.thetaThree {z : ℂ | 0 < z.im} :=
    fun z hz => (Bottcher.differentiableAt_thetaThree hz).differentiableWithinAt
  exact hdiff.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ)

private theorem analyticAt_eisensteinSeries_E2_comp_ofComplex
    {τ : ℂ} (hτ : 0 < τ.im) :
    AnalyticAt ℂ (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) τ := by
  have hdiff : DifferentiableOn ℂ
      (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  exact hdiff.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ)

private theorem analyticAt_thetaModularHC (x : ℝ) :
    AnalyticAt ℂ thetaModularHC (x : ℂ) := by
  unfold thetaModularHC
  have hexp :
      AnalyticAt ℂ (fun w : ℂ => Complex.exp (w / 2)) (x : ℂ) := by
    fun_prop
  have htheta :
      AnalyticAt ℂ
        (fun w : ℂ => Bottcher.thetaThree (thetaModularTauC w))
        (x : ℂ) := by
    have hout :
        AnalyticAt ℂ Bottcher.thetaThree
          (thetaModularTauC (x : ℂ)) := by
      simpa [thetaModularTau_eq_tauC] using
        analyticAt_thetaThree_of_im_pos (thetaModularTau_im_pos x)
    exact hout.comp (analyticAt_thetaModularTauC (x : ℂ))
  exact hexp.mul htheta

private theorem analyticAt_thetaModularZC (x : ℝ) :
    AnalyticAt ℂ thetaModularZC (x : ℂ) := by
  unfold thetaModularZC
  have hout :
      AnalyticAt ℂ Bottcher.modularLambda
        (thetaModularTauC (x : ℂ)) := by
    simpa [thetaModularTau_eq_tauC] using
      Bottcher.analyticAt_modularLambda (thetaModularTau_im_pos x)
  have hlambda := hout.comp (analyticAt_thetaModularTauC (x : ℂ))
  exact (analyticAt_const.mul hlambda).sub analyticAt_const

private theorem analyticAt_thetaModularPC (x : ℝ) :
    AnalyticAt ℂ thetaModularPC (x : ℂ) := by
  unfold thetaModularPC
  have hout :
      AnalyticAt ℂ
        (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
        (thetaModularTauC (x : ℂ)) := by
    simpa [thetaModularTau_eq_tauC] using
      analyticAt_eisensteinSeries_E2_comp_ofComplex
        (thetaModularTau_im_pos x)
  have hE := hout.comp (analyticAt_thetaModularTauC (x : ℂ))
  have hexp :
      AnalyticAt ℂ (fun w : ℂ => Complex.exp (2 * w)) (x : ℂ) := by
    fun_prop
  exact ((analyticAt_const.mul hexp).mul hE).sub analyticAt_const

private theorem contDiff_thetaModularH :
    ContDiff ℝ ∞ thetaModularH := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hC : ContDiffAt ℂ ∞ thetaModularHC (x : ℂ) :=
    (analyticAt_thetaModularHC x).contDiffAt
  have hR : ContDiffAt ℝ ∞ thetaModularHC (x : ℂ) :=
    hC.restrict_scalars ℝ
  have hc := hR.comp x (Complex.ofRealCLM.contDiff.contDiffAt)
  exact hc

private theorem contDiff_thetaModularZ :
    ContDiff ℝ ∞ thetaModularZ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hC : ContDiffAt ℂ ∞ thetaModularZC (x : ℂ) :=
    (analyticAt_thetaModularZC x).contDiffAt
  have hR : ContDiffAt ℝ ∞ thetaModularZC (x : ℂ) :=
    hC.restrict_scalars ℝ
  have hc := hR.comp x (Complex.ofRealCLM.contDiff.contDiffAt)
  exact hc

private theorem contDiff_thetaModularR :
    ContDiff ℝ ∞ thetaModularR := by
  unfold thetaModularR
  exact contDiff_const.mul (contDiff_thetaModularH.pow 4)

private theorem contDiff_thetaModularP :
    ContDiff ℝ ∞ thetaModularP := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hC : ContDiffAt ℂ ∞ thetaModularPC (x : ℂ) :=
    (analyticAt_thetaModularPC x).contDiffAt
  have hR : ContDiffAt ℝ ∞ thetaModularPC (x : ℂ) :=
    hC.restrict_scalars ℝ
  have hc := hR.comp x (Complex.ofRealCLM.contDiff.contDiffAt)
  exact hc

private theorem hasDerivAt_thetaModularTauC (w : ℂ) :
    HasDerivAt thetaModularTauC (2 * thetaModularTauC w) w := by
  have hlin :
      HasDerivAt (fun u : ℂ => 2 * u) 2 w := by
    have h := (hasDerivAt_id w).const_mul (2 : ℂ)
    rw [mul_one] at h
    exact h
  have hexp :=
    (Complex.hasDerivAt_exp (2 * w)).scomp w hlin
  have h := hexp.const_mul I
  simp only [smul_eq_mul] at h
  have hval : I * (2 * Complex.exp (2 * w)) = 2 * thetaModularTauC w := by
    unfold thetaModularTauC
    ring
  rw [hval] at h
  exact h

private theorem hasDerivAt_thetaModularHC (x : ℝ) :
    HasDerivAt thetaModularHC
      (Complex.exp ((x : ℂ) / 2) / 2 *
          Bottcher.thetaThree (thetaModularTau x) +
        Complex.exp ((x : ℂ) / 2) *
          (deriv Bottcher.thetaThree (thetaModularTau x) *
            (2 * thetaModularTau x)))
      (x : ℂ) := by
  have hexp :
      HasDerivAt (fun w : ℂ => Complex.exp (w / 2))
        (Complex.exp ((x : ℂ) / 2) / 2) (x : ℂ) := by
    have h := (Complex.hasDerivAt_exp ((x : ℂ) / 2)).scomp
      (x : ℂ) ((hasDerivAt_id (x : ℂ)).div_const 2)
    simp only [smul_eq_mul] at h
    have hval : 1 / 2 * Complex.exp ((x : ℂ) / 2) =
        Complex.exp ((x : ℂ) / 2) / 2 := by
      ring
    rw [hval] at h
    exact h
  have htheta :
      HasDerivAt
        (fun w : ℂ => Bottcher.thetaThree (thetaModularTauC w))
        (deriv Bottcher.thetaThree (thetaModularTau x) *
          (2 * thetaModularTau x)) (x : ℂ) := by
    have hbase :
        HasDerivAt Bottcher.thetaThree
          (deriv Bottcher.thetaThree (thetaModularTau x))
          (thetaModularTau x) :=
      (analyticAt_thetaThree_of_im_pos
        (thetaModularTau_im_pos x)).differentiableAt.hasDerivAt
    have hcomp := hbase.scomp (x : ℂ)
      (hasDerivAt_thetaModularTauC (x : ℂ))
    simp only [smul_eq_mul] at hcomp
    have hval : 2 * thetaModularTauC (x : ℂ) *
        deriv Bottcher.thetaThree (thetaModularTau x) =
        deriv Bottcher.thetaThree (thetaModularTau x) *
          (2 * thetaModularTau x) := by
      rw [thetaModularTau_eq_tauC]
      ring
    rw [hval] at hcomp
    exact hcomp
  exact hexp.mul htheta

private theorem hasDerivAt_thetaModularH_raw (x : ℝ) :
    HasDerivAt thetaModularH
      (Complex.exp ((x : ℂ) / 2) / 2 *
          Bottcher.thetaThree (thetaModularTau x) +
        Complex.exp ((x : ℂ) / 2) *
          (deriv Bottcher.thetaThree (thetaModularTau x) *
            (2 * thetaModularTau x))) x := by
  exact (hasDerivAt_thetaModularHC x).comp_ofReal

private theorem thetaModularH_pow_four (x : ℝ) :
    thetaModularH x ^ 4 =
      Complex.exp (2 * (x : ℂ)) *
        Bottcher.thetaThree (thetaModularTau x) ^ 4 := by
  rw [thetaModularH, mul_pow, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  congr 1
  ring

private theorem thetaModularE2_ofComplex (x : ℝ) :
    EisensteinSeries.E2 (UpperHalfPlane.ofComplex (thetaModularTau x)) =
      EisensteinSeries.E2
        ⟨thetaModularTau x, thetaModularTau_im_pos x⟩ := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos
    (thetaModularTau_im_pos x)]

private theorem thetaModularR_mul_Z (x : ℝ) :
    thetaModularR x * thetaModularZ x =
      (Real.pi : ℂ) * Complex.exp (2 * (x : ℂ)) *
        (Bottcher.thetaTwo (thetaModularTau x) ^ 4 -
          Bottcher.thetaFour (thetaModularTau x) ^ 4) := by
  let τ := thetaModularTau x
  have hτ : 0 < τ.im := thetaModularTau_im_pos x
  have h3ne := Bottcher.thetaThree_ne_zero_of_im_pos hτ
  have hQ := Bottcher.pow4_jacobi hτ
  have htheta :
      Bottcher.thetaThree τ ^ 4 *
          (2 * Bottcher.modularLambda τ - 1) =
        Bottcher.thetaTwo τ ^ 4 - Bottcher.thetaFour τ ^ 4 := by
    rw [Bottcher.modularLambda, div_pow]
    field_simp [h3ne]
    rw [hQ]
    ring
  rw [thetaModularR, thetaModularZ, thetaModularH_pow_four]
  change
    (Real.pi : ℂ) *
          (Complex.exp (2 * (x : ℂ)) *
            Bottcher.thetaThree τ ^ 4) *
        (2 * Bottcher.modularLambda τ - 1) =
      _
  rw [← htheta]
  ring

private theorem deriv_thetaModularH (x : ℝ) :
    deriv thetaModularH x =
      -(1 / 6 : ℂ) *
        (thetaModularH x *
          (thetaModularP x + thetaModularR x * thetaModularZ x)) := by
  let τ := thetaModularTau x
  have hτ : 0 < τ.im := thetaModularTau_im_pos x
  have h3ne := Bottcher.thetaThree_ne_zero_of_im_pos hτ
  have hlog := Bottcher.thetaThree_logDeriv_eq_E2 hτ
  have hder :
      deriv Bottcher.thetaThree τ =
        Bottcher.thetaThree τ *
          ((Real.pi : ℂ) * I / 12 *
            (EisensteinSeries.E2 ⟨τ, hτ⟩ +
              Bottcher.thetaTwo τ ^ 4 -
              Bottcher.thetaFour τ ^ 4)) := by
    apply (div_eq_iff h3ne).mp at hlog
    linear_combination hlog
  rw [(hasDerivAt_thetaModularH_raw x).deriv]
  rw [show deriv Bottcher.thetaThree (thetaModularTau x) =
      Bottcher.thetaThree τ *
        ((Real.pi : ℂ) * I / 12 *
          (EisensteinSeries.E2 ⟨τ, hτ⟩ +
            Bottcher.thetaTwo τ ^ 4 -
            Bottcher.thetaFour τ ^ 4)) by exact hder]
  rw [thetaModularP, thetaModularR_mul_Z,
    thetaModularE2_ofComplex]
  unfold thetaModularH thetaModularTau
  dsimp [τ, thetaModularTau]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem hasDerivAt_thetaModularZ_raw (x : ℝ) :
    HasDerivAt thetaModularZ
      (2 * (deriv Bottcher.modularLambda (thetaModularTau x) *
        (2 * thetaModularTau x))) x := by
  have hbase :
      HasDerivAt Bottcher.modularLambda
        (deriv Bottcher.modularLambda (thetaModularTau x))
        (thetaModularTau x) :=
    (Bottcher.analyticAt_modularLambda
      (thetaModularTau_im_pos x)).differentiableAt.hasDerivAt
  have hcomp := hbase.scomp (x : ℂ)
    (hasDerivAt_thetaModularTauC (x : ℂ))
  have hreal := hcomp.comp_ofReal
  simp only [smul_eq_mul] at hreal
  have hlin := (hreal.const_mul (2 : ℂ)).sub_const (1 : ℂ)
  have hval : 2 * (2 * thetaModularTauC (x : ℂ) *
      deriv Bottcher.modularLambda (thetaModularTau x)) =
      2 * (deriv Bottcher.modularLambda (thetaModularTau x) *
        (2 * thetaModularTau x)) := by
    rw [thetaModularTau_eq_tauC]
    ring
  rw [hval] at hlin
  exact hlin

private theorem deriv_thetaModularZ (x : ℝ) :
    deriv thetaModularZ x =
      -(thetaModularR x *
        (1 - thetaModularZ x * thetaModularZ x)) := by
  let τ := thetaModularTau x
  have hτ : 0 < τ.im := thetaModularTau_im_pos x
  have hlam := Bottcher.deriv_modularLambda_eq_lambda' hτ
  rw [(hasDerivAt_thetaModularZ_raw x).deriv]
  rw [show deriv Bottcher.modularLambda (thetaModularTau x) =
      (Real.pi : ℂ) * I * Bottcher.thetaThree τ ^ 4 *
        Bottcher.modularLambda τ * (1 - Bottcher.modularLambda τ) by
      exact hlam]
  rw [thetaModularR, thetaModularH_pow_four]
  unfold thetaModularZ thetaModularTau
  dsimp [τ, thetaModularTau]
  ring_nf
  simp [Complex.I_sq]

private theorem deriv_thetaModularR (x : ℝ) :
    deriv thetaModularR x =
      -(2 / 3 : ℂ) *
        (thetaModularR x *
          (thetaModularP x + thetaModularR x * thetaModularZ x)) := by
  have hH :
      HasDerivAt thetaModularH (deriv thetaModularH x) x :=
    (contDiff_thetaModularH.differentiable (by simp)).differentiableAt.hasDerivAt
  have hR := (hH.pow 4).const_mul (Real.pi : ℂ)
  have hR' :
      HasDerivAt thetaModularR
        ((Real.pi : ℂ) *
          (4 * thetaModularH x ^ 3 * deriv thetaModularH x)) x := by
    exact hR
  rw [hR'.deriv]
  rw [deriv_thetaModularH]
  unfold thetaModularR
  ring

private theorem thetaModularE4_eq_state (x : ℝ) :
    ModularForm.E₄
        ⟨thetaModularTau x, thetaModularTau_im_pos x⟩ =
      Bottcher.thetaThree (thetaModularTau x) ^ 8 *
        (3 + thetaModularZ x ^ 2) / 4 := by
  let τ := thetaModularTau x
  have hτ : 0 < τ.im := thetaModularTau_im_pos x
  have h3ne := Bottcher.thetaThree_ne_zero_of_im_pos hτ
  have hQ := Bottcher.pow4_jacobi hτ
  have hQ8 :
      Bottcher.thetaThree τ ^ 8 =
        (Bottcher.thetaTwo τ ^ 4 +
          Bottcher.thetaFour τ ^ 4) ^ 2 := by
    rw [show Bottcher.thetaThree τ ^ 8 =
        (Bottcher.thetaThree τ ^ 4) ^ 2 by ring, hQ]
  rw [Bottcher.eisensteinSeries_E4_eq_theta_nullwerte]
  unfold thetaModularZ
  change
    (Bottcher.thetaTwo τ ^ 8 + Bottcher.thetaThree τ ^ 8 +
          Bottcher.thetaFour τ ^ 8) /
        2 =
      Bottcher.thetaThree τ ^ 8 *
        (3 + (2 * Bottcher.modularLambda τ - 1) ^ 2) / 4
  rw [Bottcher.modularLambda, div_pow]
  field_simp [h3ne]
  rw [hQ8, hQ]
  ring

private theorem thetaModularR_sq_state (x : ℝ) :
    (thetaModularR x * thetaModularR x) *
        (3 + thetaModularZ x * thetaModularZ x) =
      4 * (Real.pi : ℂ) ^ 2 * Complex.exp (4 * (x : ℂ)) *
        ModularForm.E₄
          ⟨thetaModularTau x, thetaModularTau_im_pos x⟩ := by
  rw [thetaModularR, thetaModularH_pow_four,
    thetaModularE4_eq_state]
  rw [show Complex.exp (4 * (x : ℂ)) =
      Complex.exp (2 * (x : ℂ)) *
        Complex.exp (2 * (x : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

private theorem hasDerivAt_thetaModularPC (x : ℝ) :
    HasDerivAt thetaModularPC
      ((Real.pi : ℂ) *
        (2 * Complex.exp (2 * (x : ℂ)) *
            (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
              (thetaModularTau x) +
          Complex.exp (2 * (x : ℂ)) *
            (deriv
                (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
                (thetaModularTau x) *
              (2 * thetaModularTau x)))) (x : ℂ) := by
  have hexp :
      HasDerivAt (fun w : ℂ => Complex.exp (2 * w))
        (2 * Complex.exp (2 * (x : ℂ))) (x : ℂ) := by
    have hlin :
        HasDerivAt (fun w : ℂ => 2 * w) 2 (x : ℂ) := by
      have h := (hasDerivAt_id (x : ℂ)).const_mul (2 : ℂ)
      rw [mul_one] at h
      exact h
    have h := (Complex.hasDerivAt_exp (2 * (x : ℂ))).scomp
      (x : ℂ) hlin
    simp only [smul_eq_mul] at h
    exact h
  have hEbase :
      HasDerivAt
        (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
        (deriv
          (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
          (thetaModularTau x))
        (thetaModularTau x) :=
    (analyticAt_eisensteinSeries_E2_comp_ofComplex
      (thetaModularTau_im_pos x)).differentiableAt.hasDerivAt
  have hEcomp := hEbase.scomp (x : ℂ)
    (hasDerivAt_thetaModularTauC (x : ℂ))
  simp only [smul_eq_mul] at hEcomp
  have hprod := hexp.mul hEcomp
  have hfull :=
    (hprod.const_mul (Real.pi : ℂ)).sub_const (3 : ℂ)
  have hfn : thetaModularPC = fun y : ℂ =>
      (Real.pi : ℂ) * (Complex.exp (2 * y) *
        (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
          (thetaModularTauC y)) - 3 := by
    funext y
    simp only [thetaModularPC, Function.comp_apply]
    ring
  rw [hfn]
  have hval : (Real.pi : ℂ) *
      (2 * Complex.exp (2 * (x : ℂ)) *
          ((EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) ∘
            thetaModularTauC) (x : ℂ) +
        Complex.exp (2 * (x : ℂ)) *
          (2 * thetaModularTauC (x : ℂ) *
            deriv (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
              (thetaModularTau x))) =
      (Real.pi : ℂ) *
        (2 * Complex.exp (2 * (x : ℂ)) *
            (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
              (thetaModularTau x) +
          Complex.exp (2 * (x : ℂ)) *
            (deriv
                (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
                (thetaModularTau x) *
              (2 * thetaModularTau x))) := by
    rw [thetaModularTau_eq_tauC]
    simp only [Function.comp_apply]
    ring
  rw [hval] at hfull
  exact hfull

private theorem hasDerivAt_thetaModularP_raw (x : ℝ) :
    HasDerivAt thetaModularP
      ((Real.pi : ℂ) *
        (2 * Complex.exp (2 * (x : ℂ)) *
            (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
              (thetaModularTau x) +
          Complex.exp (2 * (x : ℂ)) *
            (deriv
                (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
                (thetaModularTau x) *
              (2 * thetaModularTau x)))) x := by
  have heq :
      thetaModularP =
        fun y : ℝ => thetaModularPC (y : ℂ) := by
    funext y
    rfl
  rw [heq]
  exact (hasDerivAt_thetaModularPC x).comp_ofReal

private theorem deriv_thetaModularP (x : ℝ) :
    deriv thetaModularP x =
      3 - (1 / 3 : ℂ) *
          (thetaModularP x * thetaModularP x) +
        (1 / 12 : ℂ) *
          ((thetaModularR x * thetaModularR x) *
            (3 + thetaModularZ x * thetaModularZ x)) := by
  let τ := thetaModularTau x
  have hτ : 0 < τ.im := thetaModularTau_im_pos x
  have hRam :=
    Bottcher.deriv_eisensteinSeries_E2_comp_ofComplex
      ⟨τ, hτ⟩
  rw [(hasDerivAt_thetaModularP_raw x).deriv]
  rw [show deriv
      (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex)
        (thetaModularTau x) =
      (Real.pi : ℂ) * I / 6 *
      (EisensteinSeries.E2 ⟨τ, hτ⟩ ^ 2 -
          ModularForm.E₄ ⟨τ, hτ⟩) by exact hRam]
  simp only [Function.comp_apply]
  rw [thetaModularR_sq_state]
  unfold thetaModularP
  rw [thetaModularE2_ofComplex]
  unfold thetaModularTau
  dsimp [τ, thetaModularTau]
  rw [show Complex.exp (4 * (x : ℂ)) =
      Complex.exp (2 * (x : ℂ)) *
        Complex.exp (2 * (x : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem thetaModularH_zero :
    thetaModularH 0 = (thetaCuspSelfDualThetaMass : ℂ) := by
  have h := Bottcher.ofReal_evenKernel_zero_eq_thetaThree 1
  simpa [thetaModularH, thetaModularTau,
    thetaCuspSelfDualThetaMass] using h.symm

private theorem thetaModularZ_zero :
    thetaModularZ 0 = 0 := by
  rw [thetaModularZ, thetaModularTau]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [Bottcher.modularLambda_at_I']
  norm_num

private theorem thetaModularR_zero :
    thetaModularR 0 = (thetaCuspSelfDualModularScale : ℂ) := by
  rw [thetaModularR, thetaModularH_zero]
  simp [thetaCuspSelfDualModularScale]

private theorem thetaModularP_zero :
    thetaModularP 0 = 0 := by
  rw [thetaModularP, thetaModularTau]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos
    (show (0 : ℝ) < I.im by simp)]
  rw [Bottcher.eisensteinSeries_E2_at_I]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- Real degree-eight polynomial selected by reflected second--sixth seam elimination. -/
def thetaCuspReflectedSixthSeamModularPolynomial (X : ℝ) : ℝ :=
  127575 / 4096 - 1828575 / 16384 * X + 6333795 / 65536 * X ^ 2 -
    7447545 / 262144 * X ^ 3 + 397305 / 262144 * X ^ 4 -
    48411 / 262144 * X ^ 5 + 229545 / 8388608 * X ^ 6 +
    225 / 1048576 * X ^ 7 - 375 / 33554432 * X ^ 8

/-- Source-specialized modular value of the reflected second--sixth seam invariant. -/
def thetaCuspReflectedSixthSeamModularClosureValue : ℝ :=
  thetaCuspSelfDualThetaMass ^ 4 *
    thetaCuspReflectedSixthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ 2)

/-- Real degree-eight polynomial selected by the first transverse action-velocity seam minor. -/
def thetaCuspActionVelocitySeamMinorModularPolynomial (X : ℝ) : ℝ :=
  2025 / 2048 - 57375 / 8192 * X - 240075 / 32768 * X ^ 2 -
    159525 / 131072 * X ^ 3 + 467169 / 262144 * X ^ 4 -
    4125 / 524288 * X ^ 5 + 15589 / 2097152 * X ^ 6 -
    1677 / 8388608 * X ^ 7 - 387 / 16777216 * X ^ 8

/-- Source-specialized modular value of the first transverse action-velocity seam minor. -/
def thetaCuspActionVelocitySeamMinorModularClosureValue : ℝ :=
  thetaCuspSelfDualThetaMass ^ 4 *
    thetaCuspActionVelocitySeamMinorModularPolynomial
      (thetaCuspSelfDualModularScale ^ 2)

/-- Exact modular closure of the completed theta profile's sixth seam. -/
theorem completedThetaProfile_sixthSeam_modularClosure :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) thetaModularH 0 -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH 0) / 2
    f 0 ^ 2 * f 6 - 15 * f 0 * f 2 * f 4 + 30 * f 2 ^ 3 =
      (thetaCuspGaussianApertureSixthSeamModularClosureValue : ℂ) := by
  have h := HTGeometry.modularThetaSixthSeamClosure_of_ode
    (thetaCuspSelfDualThetaMass : ℂ)
    (thetaCuspSelfDualModularScale : ℂ)
    thetaModularH thetaModularZ thetaModularR thetaModularP
    contDiff_thetaModularH contDiff_thetaModularZ
    contDiff_thetaModularR contDiff_thetaModularP
    thetaModularH_zero thetaModularZ_zero
    thetaModularR_zero thetaModularP_zero
    deriv_thetaModularH deriv_thetaModularZ
    deriv_thetaModularR deriv_thetaModularP
  simpa [thetaCuspGaussianApertureSixthSeamModularClosureValue,
    thetaCuspGaussianApertureSixthSeamModularPolynomial] using h

/-- Exact modular closure of the completed theta profile's reflected second--sixth seam. -/
theorem completedThetaProfile_reflectedSixthSeam_modularClosure :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) thetaModularH 0 -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH 0) / 2
    f 0 ^ 2 * (f 2 * f 6 - f 4 ^ 2) +
        9 * f 0 * f 2 ^ 2 * f 4 - 9 * f 2 ^ 4 =
      (thetaCuspReflectedSixthSeamModularClosureValue : ℂ) := by
  have h := HTGeometry.modularThetaReflectedSixthSeamClosure_of_ode
    (thetaCuspSelfDualThetaMass : ℂ)
    (thetaCuspSelfDualModularScale : ℂ)
    thetaModularH thetaModularZ thetaModularR thetaModularP
    contDiff_thetaModularH contDiff_thetaModularZ
    contDiff_thetaModularR contDiff_thetaModularP
    thetaModularH_zero thetaModularZ_zero
    thetaModularR_zero thetaModularP_zero
    deriv_thetaModularH deriv_thetaModularZ
    deriv_thetaModularR deriv_thetaModularP
  simpa [thetaCuspReflectedSixthSeamModularClosureValue,
    thetaCuspReflectedSixthSeamModularPolynomial,
    HTGeometry.modularThetaReflectedSixthSeamPolynomial] using h

/-- Exact modular closure of the completed theta profile's first transverse action-velocity
seam minor. -/
theorem completedThetaProfile_actionVelocitySeamMinor_modularClosure :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) thetaModularH 0 -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH 0) / 2
    f 0 ^ 2 * f 2 * f 6 - 3 * f 0 * f 2 ^ 2 * f 4 +
        12 * f 2 ^ 4 - 2 * f 0 ^ 2 * f 4 ^ 2 =
      (thetaCuspActionVelocitySeamMinorModularClosureValue : ℂ) := by
  have h := HTGeometry.modularThetaActionVelocitySeamMinorClosure_of_ode
    (thetaCuspSelfDualThetaMass : ℂ)
    (thetaCuspSelfDualModularScale : ℂ)
    thetaModularH thetaModularZ thetaModularR thetaModularP
    contDiff_thetaModularH contDiff_thetaModularZ
    contDiff_thetaModularR contDiff_thetaModularP
    thetaModularH_zero thetaModularZ_zero
    thetaModularR_zero thetaModularP_zero
    deriv_thetaModularH deriv_thetaModularZ
    deriv_thetaModularR deriv_thetaModularP
  simpa [thetaCuspActionVelocitySeamMinorModularClosureValue,
    thetaCuspActionVelocitySeamMinorModularPolynomial,
    HTGeometry.modularThetaActionVelocitySeamMinorPolynomial] using h

private theorem thetaModularH_eq_completedThetaProfile (x : ℝ) :
    thetaModularH x = (Bottcher.completedThetaProfile x : ℂ) := by
  have h := Bottcher.ofReal_completedThetaProfile_eq_thetaThree x
  rw [thetaModularH, thetaModularTau]
  simpa only [Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using h.symm

private theorem completedThetaProfile_eq_tail (x : ℝ) :
    Bottcher.completedThetaProfile x =
      2 * thetaCuspTailDerivative 0 x +
        Real.exp ((1 / 2 : ℝ) * x) := by
  rw [Bottcher.completedThetaProfile,
    thetaCuspTailDerivative_zero_eq_evenKernel]
  rw [show x / 2 = (1 / 2 : ℝ) * x by ring]
  ring

private theorem contDiff_completedThetaProfile :
    ContDiff ℝ ∞ Bottcher.completedThetaProfile := by
  have htail : ContDiff ℝ ∞ (thetaCuspTailDerivative 0) :=
    contDiff_infty.mpr fun n =>
      contDiff_thetaCuspTailDerivative 0 n
  have hexp : ContDiff ℝ ∞
      (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x)) := by
    fun_prop
  rw [show Bottcher.completedThetaProfile =
      fun x : ℝ =>
        2 * thetaCuspTailDerivative 0 x +
          Real.exp ((1 / 2 : ℝ) * x) by
    funext x
    exact completedThetaProfile_eq_tail x]
  exact (contDiff_const.mul htail).add hexp

private theorem iteratedDeriv_completedThetaProfile
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n Bottcher.completedThetaProfile x =
      2 * thetaCuspTailDerivative n x +
        (1 / 2 : ℝ) ^ n * Real.exp ((1 / 2 : ℝ) * x) := by
  rw [show Bottcher.completedThetaProfile =
      fun y : ℝ =>
        2 * thetaCuspTailDerivative 0 y +
          Real.exp ((1 / 2 : ℝ) * y) by
    funext y
    exact completedThetaProfile_eq_tail y]
  change
    iteratedDeriv n
        ((fun y : ℝ => 2 * thetaCuspTailDerivative 0 y) +
          fun y : ℝ => Real.exp ((1 / 2 : ℝ) * y)) x =
      _
  have htail : ContDiffAt ℝ n (thetaCuspTailDerivative 0) x :=
    (contDiff_thetaCuspTailDerivative 0 n).contDiffAt
  have hexp : ContDiffAt ℝ n
      (fun y : ℝ => Real.exp ((1 / 2 : ℝ) * y)) x := by
    fun_prop
  rw [iteratedDeriv_add (contDiffAt_const.mul htail) hexp,
    iteratedDeriv_const_mul (2 : ℝ) htail,
    iteratedDeriv_thetaCuspTailDerivative,
    congrFun (iteratedDeriv_exp_const_mul n (1 / 2 : ℝ)) x]
  simp

private theorem iteratedDeriv_thetaCuspFullSource_eq_tail
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n thetaCuspFullSource x =
      thetaCuspTailDerivative (n + 2) x -
        (1 / 4 : ℝ) * thetaCuspTailDerivative n x := by
  rw [show thetaCuspFullSource =
      fun y : ℝ =>
        thetaCuspTailDerivative 2 y -
          (1 / 4 : ℝ) * thetaCuspTailDerivative 0 y by
    funext y
    exact thetaCuspFullSource_eq_tail_second_sub y]
  change
    iteratedDeriv n
      (thetaCuspTailDerivative 2 -
        fun y => (1 / 4 : ℝ) * thetaCuspTailDerivative 0 y) x = _
  have hT2 : ContDiffAt ℝ n (thetaCuspTailDerivative 2) x :=
    (contDiff_thetaCuspTailDerivative 2 n).contDiffAt
  have hT0 : ContDiffAt ℝ n (thetaCuspTailDerivative 0) x :=
    (contDiff_thetaCuspTailDerivative 0 n).contDiffAt
  rw [iteratedDeriv_sub hT2 (contDiffAt_const.mul hT0),
    iteratedDeriv_const_mul (1 / 4 : ℝ) hT0,
    iteratedDeriv_thetaCuspTailDerivative,
    iteratedDeriv_thetaCuspTailDerivative]
  simp [add_comm]

private theorem iteratedDeriv_thetaModularH (n : ℕ) (x : ℝ) :
    iteratedDeriv n thetaModularH x =
      ((iteratedDeriv n Bottcher.completedThetaProfile x : ℝ) : ℂ) := by
  rw [show thetaModularH =
      fun y : ℝ => (Bottcher.completedThetaProfile y : ℂ) by
    funext y
    exact thetaModularH_eq_completedThetaProfile y]
  exact SchwartzMap.iteratedDeriv_ofReal
    Bottcher.completedThetaProfile contDiff_completedThetaProfile n x

private theorem completedThetaProfile_sourceJet (n : ℕ) :
    (iteratedDeriv (n + 2) thetaModularH 0 -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH 0) / 2 =
      ((iteratedDeriv n thetaCuspFullSource 0 : ℝ) : ℂ) := by
  rw [iteratedDeriv_thetaModularH, iteratedDeriv_thetaModularH]
  have hreal :
      (iteratedDeriv (n + 2) Bottcher.completedThetaProfile 0 -
          (1 / 4 : ℝ) *
            iteratedDeriv n Bottcher.completedThetaProfile 0) / 2 =
        iteratedDeriv n thetaCuspFullSource 0 := by
    rw [iteratedDeriv_completedThetaProfile,
      iteratedDeriv_completedThetaProfile,
      iteratedDeriv_thetaCuspFullSource_eq_tail]
    have hp :
        (1 / 2 : ℝ) ^ (n + 2) =
          (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [pow_add]
      norm_num
      ring
    rw [hp]
    norm_num
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  norm_num at hc ⊢
  exact hc

/-- The native full-theta source invariant is exactly the reflected modular-closure value. -/
theorem thetaCuspFullSource_reflectedSixthSeam_eq_modularClosure :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
    f 0 ^ 2 * (f 2 * f 6 - f 4 ^ 2) +
        9 * f 0 * f 2 ^ 2 * f 4 - 9 * f 2 ^ 4 =
      thetaCuspReflectedSixthSeamModularClosureValue := by
  apply Complex.ofReal_injective
  have h := completedThetaProfile_reflectedSixthSeam_modularClosure
  dsimp only at h ⊢
  rw [completedThetaProfile_sourceJet 0,
    completedThetaProfile_sourceJet 2,
    completedThetaProfile_sourceJet 4,
    completedThetaProfile_sourceJet 6] at h
  simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat] using h

/-- The native full-theta source action-velocity seam minor is exactly its modular-closure
value. -/
theorem thetaCuspFullSource_actionVelocitySeamMinor_eq_modularClosure :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
    f 0 ^ 2 * f 2 * f 6 - 3 * f 0 * f 2 ^ 2 * f 4 +
        12 * f 2 ^ 4 - 2 * f 0 ^ 2 * f 4 ^ 2 =
      thetaCuspActionVelocitySeamMinorModularClosureValue := by
  apply Complex.ofReal_injective
  have h := completedThetaProfile_actionVelocitySeamMinor_modularClosure
  dsimp only at h ⊢
  rw [completedThetaProfile_sourceJet 0,
    completedThetaProfile_sourceJet 2,
    completedThetaProfile_sourceJet 4,
    completedThetaProfile_sourceJet 6] at h
  simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat] using h

/-- The source-defined sixth seam is exactly its modular-closure value. -/
theorem thetaCuspGaussianApertureSixthSeamNumerator_eq_modularClosure :
    thetaCuspGaussianApertureSixthSeamNumerator =
      thetaCuspGaussianApertureSixthSeamModularClosureValue := by
  apply Complex.ofReal_injective
  have h := completedThetaProfile_sixthSeam_modularClosure
  dsimp only at h
  rw [completedThetaProfile_sourceJet 0,
    completedThetaProfile_sourceJet 2,
    completedThetaProfile_sourceJet 4,
    completedThetaProfile_sourceJet 6] at h
  simpa only [thetaCuspGaussianApertureSixthSeamNumerator, iteratedDeriv_zero,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat] using h

/-- Hedenmalm's theta-specific center-mixed sixth-seam kernel is strictly positive from the
source definition alone. -/
theorem thetaCuspGaussianApertureSixthSeamNumerator_pos :
    0 < thetaCuspGaussianApertureSixthSeamNumerator := by
  rw [thetaCuspGaussianApertureSixthSeamNumerator_eq_modularClosure]
  exact thetaCuspGaussianApertureSixthSeamModularClosureValue_pos

/-! ## Rank-three reflected eighth-jet closure -/

/-- Real degree-twelve polynomial selected by the rank-three reflected eighth-jet seam. -/
def thetaCuspReflectedEighthSeamModularPolynomial (X : ℝ) : ℝ :=
  3444525 / 512 - 80754975 / 2048 * X + 4194195795 / 65536 * X ^ 2 -
    2646917595 / 65536 * X ^ 3 + 5201727255 / 524288 * X ^ 4 -
    1723813569 / 1048576 * X ^ 5 + 4581650223 / 16777216 * X ^ 6 -
    612571059 / 16777216 * X ^ 7 + 35927199 / 16777216 * X ^ 8 +
    1999197 / 268435456 * X ^ 9 - 117855 / 134217728 * X ^ 10 -
    13245 / 536870912 * X ^ 11 + 14025 / 8589934592 * X ^ 12

/-- Source-specialized modular value of rank-three reflected eighth-jet curvature. -/
def thetaCuspReflectedEighthSeamModularClosureValue : ℝ :=
  thetaCuspSelfDualThetaMass ^ 6 *
    thetaCuspReflectedEighthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ 2)

/-- Exact modular closure of the completed theta profile's rank-three reflected seam. -/
theorem completedThetaProfile_reflectedEighthSeam_modularClosure :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) thetaModularH 0 -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH 0) / 2
    HTGeometry.signedEvenHankelThreeDetC
      (f 0 ^ 2)
      (2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ 2)
      (2 * f 0 * f 6 + 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ 2) =
      (thetaCuspReflectedEighthSeamModularClosureValue : ℂ) := by
  have h := HTGeometry.modularThetaReflectedEighthSeamClosure_of_ode
    (thetaCuspSelfDualThetaMass : ℂ)
    (thetaCuspSelfDualModularScale : ℂ)
    thetaModularH thetaModularZ thetaModularR thetaModularP
    contDiff_thetaModularH contDiff_thetaModularZ
    contDiff_thetaModularR contDiff_thetaModularP
    thetaModularH_zero thetaModularZ_zero
    thetaModularR_zero thetaModularP_zero
    deriv_thetaModularH deriv_thetaModularZ
    deriv_thetaModularR deriv_thetaModularP
  simpa [thetaCuspReflectedEighthSeamModularClosureValue,
    thetaCuspReflectedEighthSeamModularPolynomial,
    HTGeometry.modularThetaReflectedEighthSeamPolynomial] using h

/-- Native full-source rank-three reflected seam equals its modular closure value. -/
theorem thetaCuspFullSource_reflectedEighthHankelSeam_eq_modularClosure :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource 0
    HilbertMetric.signedEvenHankelThreeDet
      (f 0 ^ 2)
      (2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ 2)
      (2 * f 0 * f 6 + 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ 2) =
      thetaCuspReflectedEighthSeamModularClosureValue := by
  apply Complex.ofReal_injective
  have h := completedThetaProfile_reflectedEighthSeam_modularClosure
  dsimp only at h ⊢
  rw [completedThetaProfile_sourceJet 0,
    completedThetaProfile_sourceJet 2,
    completedThetaProfile_sourceJet 4,
    completedThetaProfile_sourceJet 6,
    completedThetaProfile_sourceJet 8] at h
  simpa only [HilbertMetric.signedEvenHankelThreeDet,
    HTGeometry.signedEvenHankelThreeDetC, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using h

/-! ## Arbitrary-basepoint rank-three modular closure -/

/-- Actual completed-theta trajectory in the universal four-state ODE coordinates. -/
def thetaCuspModularODEState
    (i : HTGeometry.ModularThetaODEState) : ℝ → ℂ :=
  match i with
  | .H => thetaModularH
  | .Z => thetaModularZ
  | .R => thetaModularR
  | .P => thetaModularP

/-- Riccati drift obtained by absorbing the mixed modular coordinate `RZ` into `P`. -/
def thetaCuspModularDrift (x : ℝ) : ℂ :=
  thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x +
    thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x

/-- Positive discriminant gap of the real modular trajectory. -/
def thetaCuspModularGapAmplitude (x : ℝ) : ℝ :=
  (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
    (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)

/-- Transverse shear coupling the Riccati drift to the modular-lambda direction. -/
def thetaCuspModularTransverseShear (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * (thetaCuspModularDrift x).re -
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re

/-- Scale-free transverse shear. -/
def thetaCuspModularNormalizedShear (x : ℝ) : ℝ :=
  thetaCuspModularTransverseShear x /
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re

/-- Quasimodular drift recovered from the Lyapunov coordinates. -/
def thetaCuspModularQuasimodularDrift (x : ℝ) : ℝ :=
  (thetaCuspModularDrift x).re / 3 + thetaCuspModularTransverseShear x

/-- Scale-free quasimodular drift. -/
def thetaCuspModularNormalizedQuasimodularDrift (x : ℝ) : ℝ :=
  thetaCuspModularQuasimodularDrift x /
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re

/-- Actual theta trajectory in the genuine reduced `(Z,R,S)` state space. -/
def thetaCuspModularReducedState
    (i : HTGeometry.ModularThetaReducedState) : ℝ → ℂ :=
  match i with
  | .Z => thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z
  | .R => thetaCuspModularODEState HTGeometry.ModularThetaODEState.R
  | .S => thetaCuspModularDrift

/-- Actual theta trajectory in the physical Lyapunov `(S,A,W)` state space. -/
def thetaCuspModularLyapunovState
    (i : HTGeometry.ModularThetaLyapunovState) : ℝ → ℂ :=
  match i with
  | .S => fun x => ((thetaCuspModularDrift x).re : ℂ)
  | .A => fun x => (thetaCuspModularGapAmplitude x : ℂ)
  | .W => fun x => (thetaCuspModularTransverseShear x : ℂ)

/-- Actual theta trajectory in positive-chamber `(U,B,C)` coordinates. -/
def thetaCuspModularPositiveState
    (i : HTGeometry.ModularThetaPositiveState) : ℝ → ℂ :=
  match i with
  | .U => fun x => (thetaCuspModularQuasimodularDrift x : ℂ)
  | .B => fun x => ((-(thetaCuspModularDrift x).re / 3 : ℝ) : ℂ)
  | .C => fun x =>
      (((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
        (1 +
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) : ℝ) : ℂ)

/-- Actual theta trajectory in source-positive `(U,B,Q)` coordinates. -/
def thetaCuspModularSourcePositiveState
    (i : HTGeometry.ModularThetaSourcePositiveState) : ℝ → ℂ :=
  match i with
  | .U => fun x => (thetaCuspModularQuasimodularDrift x : ℂ)
  | .B => fun x => ((-(thetaCuspModularDrift x).re / 3 : ℝ) : ℂ)
  | .Q => fun x =>
      (((6 * (-(thetaCuspModularDrift x).re / 3) ^ 2 +
        thetaCuspModularGapAmplitude x - 6) / 16 : ℝ) : ℂ)

/-- The mass coordinate is the real completed-theta profile. -/
theorem thetaCuspModularODEState_H_eq_completedThetaProfile (x : ℝ) :
    thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x =
      (Bottcher.completedThetaProfile x : ℂ) := by
  exact thetaModularH_eq_completedThetaProfile x

/-- The completed-theta profile is strictly positive on the full real line. -/
theorem thetaCuspCompletedThetaProfile_pos (x : ℝ) :
    0 < Bottcher.completedThetaProfile x := by
  have hk := evenKernel_zero_sub_one_pos (Real.exp_pos (2 * x))
  rw [Bottcher.completedThetaProfile]
  exact mul_pos (Real.exp_pos _) (by linarith)

/-- The physical theta-mass coordinate is strictly positive. -/
theorem thetaCuspModularODEState_H_re_pos (x : ℝ) :
    0 < (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x).re := by
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile]
  simp only [Complex.ofReal_re]
  exact thetaCuspCompletedThetaProfile_pos x

/-- The completed-theta mass coordinate is real. -/
theorem thetaCuspModularODEState_H_im_eq_zero (x : ℝ) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x).im = 0 := by
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile]
  simp

/-- The modular scale coordinate is the positive real number `π H⁴`. -/
theorem thetaCuspModularODEState_R_eq_completedThetaProfile (x : ℝ) :
    thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x =
      (Real.pi * Bottcher.completedThetaProfile x ^ 4 : ℝ) := by
  dsimp only [thetaCuspModularODEState, thetaModularR]
  rw [thetaModularH_eq_completedThetaProfile]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- The modular scale coordinate is real. -/
theorem thetaCuspModularODEState_R_im_eq_zero (x : ℝ) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).im = 0 := by
  have h := congrArg Complex.im
    (thetaCuspModularODEState_R_eq_completedThetaProfile x)
  simpa only [Complex.ofReal_im] using h

/-- The modular scale coordinate is strictly positive. -/
theorem thetaCuspModularODEState_R_re_pos (x : ℝ) :
    0 < (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re := by
  rw [thetaCuspModularODEState_R_eq_completedThetaProfile]
  simp only [Complex.ofReal_re]
  exact mul_pos Real.pi_pos (pow_pos (thetaCuspCompletedThetaProfile_pos x) 4)

/-- The modular-lambda coordinate is real on the physical imaginary-axis trajectory. -/
theorem thetaCuspModularODEState_Z_im_eq_zero (x : ℝ) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).im = 0 := by
  dsimp only [thetaCuspModularODEState, thetaModularZ, thetaModularTau]
  have h := Bottcher.modularLambda_im_axis_real
    (t := Real.exp (2 * x))
  have hexp : Complex.exp (2 * (x : ℂ)) = (Real.exp (2 * x) : ℂ) := by
    rw [show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_exp]
  have htau : Complex.I * Complex.exp (2 * (x : ℂ)) =
      (Real.exp (2 * x) : ℂ) * Complex.I := by
    rw [hexp]
    ring
  have hlam :
      (Bottcher.modularLambda
        (Complex.I * Complex.exp (2 * (x : ℂ)))).im =
      (Bottcher.modularLambda
        ((Real.exp (2 * x) : ℂ) * Complex.I)).im :=
    congrArg Complex.im (congrArg Bottcher.modularLambda htau)
  have hzero :
      (Bottcher.modularLambda
        (Complex.I * Complex.exp (2 * (x : ℂ)))).im = 0 := hlam.trans h
  simp [Complex.mul_im, Complex.sub_im, hzero]

/-- The quasimodular coordinate is real, forced by the real `H,R,Z` trajectory and the `H` ODE. -/
theorem thetaCuspModularODEState_P_im_eq_zero (x : ℝ) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).im = 0 := by
  have hleft : (deriv thetaModularH x).im = 0 := by
    rw [← iteratedDeriv_one, iteratedDeriv_thetaModularH]
    simp
  have hHim : (thetaModularH x).im = 0 := by
    rw [thetaModularH_eq_completedThetaProfile]
    simp
  have hHre : (thetaModularH x).re = Bottcher.completedThetaProfile x := by
    rw [thetaModularH_eq_completedThetaProfile]
    simp
  have hRim : (thetaModularR x).im = 0 := by
    simpa only [thetaCuspModularODEState] using
      thetaCuspModularODEState_R_im_eq_zero x
  have hZim : (thetaModularZ x).im = 0 := by
    simpa only [thetaCuspModularODEState] using
      thetaCuspModularODEState_Z_im_eq_zero x
  have him := congrArg Complex.im (deriv_thetaModularH x)
  rw [hleft] at him
  simp only [Complex.mul_im, Complex.add_im, Complex.neg_re, Complex.neg_im] at him
  rw [hHim, hHre, hRim, hZim] at him
  norm_num at him
  have hm := thetaCuspCompletedThetaProfile_pos x
  dsimp only [thetaCuspModularODEState]
  exact him.resolve_left hm.ne'

/-- The reduced Riccati drift is real on the physical theta trajectory. -/
theorem thetaCuspModularDrift_im_eq_zero (x : ℝ) :
    (thetaCuspModularDrift x).im = 0 := by
  have hP := thetaCuspModularODEState_P_im_eq_zero x
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularDrift
  simp only [Complex.add_im, Complex.mul_im, hP, hR, hZ, mul_zero,
    zero_mul, add_zero]

/-- The Lyapunov combination `S/3+W` is exactly the real quasimodular coordinate `P`. -/
theorem thetaCuspModularQuasimodularDrift_eq_P_re (x : ℝ) :
    thetaCuspModularQuasimodularDrift x =
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).re := by
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularQuasimodularDrift thetaCuspModularTransverseShear
    thetaCuspModularDrift
  simp only [Complex.add_re, Complex.mul_re, hR, hZ, mul_zero, sub_zero]
  ring

/-- Self-duality is the zero of the reduced Riccati drift. -/
theorem thetaCuspModularDrift_re_zero :
    (thetaCuspModularDrift 0).re = 0 := by
  unfold thetaCuspModularDrift
  dsimp only [thetaCuspModularODEState]
  rw [thetaModularP_zero, thetaModularZ_zero]
  norm_num

private theorem mem_Ioo_of_continuous_zero_avoids_endpoints
    (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 = 0)
    (hneg : ∀ x, f x ≠ -1) (hpos : ∀ x, f x ≠ 1) (x : ℝ) :
    f x ∈ Set.Ioo (-1) 1 := by
  constructor
  · by_contra h
    have hx : f x ≤ -1 := le_of_not_gt h
    have hmem : (-1 : ℝ) ∈ Set.Icc (f x) (f 0) := by
      rw [h0]
      exact ⟨hx, by norm_num⟩
    obtain ⟨y, hfy⟩ := (intermediate_value_univ x 0 hf) hmem
    exact hneg y hfy
  · by_contra h
    have hx : 1 ≤ f x := le_of_not_gt h
    have hmem : (1 : ℝ) ∈ Set.Icc (f 0) (f x) := by
      rw [h0]
      exact ⟨by norm_num, hx⟩
    obtain ⟨y, hfy⟩ := (intermediate_value_univ 0 x hf) hmem
    exact hpos y hfy

/-- The real modular-lambda coordinate stays strictly between its two omitted boundary values. -/
theorem thetaCuspModularODEState_Z_re_mem_Ioo (x : ℝ) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ∈
      Set.Ioo (-1) 1 := by
  let f : ℝ → ℝ := fun y =>
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re
  have hf : Continuous f := by
    dsimp only [f, thetaCuspModularODEState]
    exact Complex.continuous_re.comp contDiff_thetaModularZ.continuous
  have h0 : f 0 = 0 := by
    dsimp only [f, thetaCuspModularODEState]
    rw [thetaModularZ_zero]
    simp
  have hneg : ∀ y, f y ≠ -1 := by
    intro y hy
    dsimp only [f, thetaCuspModularODEState] at hy
    have hcomplex : thetaModularZ y = (-1 : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.neg_re, Complex.one_re] using hy
      · rw [show (thetaModularZ y).im = 0 by
          simpa only [thetaCuspModularODEState] using
            thetaCuspModularODEState_Z_im_eq_zero y]
        simp
    unfold thetaModularZ at hcomplex
    have hlam : Bottcher.modularLambda (thetaModularTau y) = 0 := by
      linear_combination (1 / 2 : ℂ) * hcomplex
    exact Bottcher.modularLambda_ne_zero_of_im_pos
      (thetaModularTau_im_pos y) hlam
  have hpos : ∀ y, f y ≠ 1 := by
    intro y hy
    dsimp only [f, thetaCuspModularODEState] at hy
    have hcomplex : thetaModularZ y = (1 : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.one_re] using hy
      · rw [show (thetaModularZ y).im = 0 by
          simpa only [thetaCuspModularODEState] using
            thetaCuspModularODEState_Z_im_eq_zero y]
        simp
    unfold thetaModularZ at hcomplex
    have hlam : Bottcher.modularLambda (thetaModularTau y) = 1 := by
      linear_combination (1 / 2 : ℂ) * hcomplex
    exact Bottcher.modularLambda_ne_one (thetaModularTau_im_pos y) hlam
  exact mem_Ioo_of_continuous_zero_avoids_endpoints f hf h0 hneg hpos x

/-- The modular discriminant gap is strictly positive everywhere on the real trajectory. -/
theorem thetaCuspModularGapAmplitude_pos (x : ℝ) :
    0 < thetaCuspModularGapAmplitude x := by
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo x
  have hgap : 0 <
      1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2 := by
    have hprod : 0 <
        (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) *
          (1 + (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) :=
      mul_pos (sub_pos.mpr hZ.2) (by linarith [hZ.1])
    nlinarith
  unfold thetaCuspModularGapAmplitude
  exact mul_pos (pow_pos (thetaCuspModularODEState_R_re_pos x) 2) hgap

/-- Exact real ODE for the modular-lambda coordinate. -/
theorem hasDerivAt_thetaCuspModularODEState_Z_re (x : ℝ) :
    HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re)
      (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
        (1 -
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)) x := by
  have hcomplex : HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z)
      (-thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
        (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) x := by
    have h := (contDiff_thetaModularZ.differentiable (by simp) x).hasDerivAt
    rw [deriv_thetaModularZ] at h
    simpa only [thetaCuspModularODEState, pow_two, neg_mul] using h
  have hre : HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re)
      ((-thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
        (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)).re) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomplex
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  have hcoef :
      (-thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
          (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)).re =
        -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) := by
    simp only [pow_two, Complex.neg_re, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.neg_im]
    simp only [hR, hZ, neg_zero, zero_mul, sub_zero]
  rw [hcoef] at hre
  exact hre

/-- The physical modular-lambda coordinate decreases strictly along the source clock. -/
theorem strictAnti_thetaCuspModularODEState_Z_re :
    StrictAnti (fun x =>
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_thetaCuspModularODEState_Z_re
  intro x
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo x
  have hgap : 0 <
      1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2 := by
    have hprod : 0 <
        (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) *
          (1 + (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) :=
      mul_pos (sub_pos.mpr hZ.2) (by linarith [hZ.1])
    nlinarith
  have hprod := mul_pos (thetaCuspModularODEState_R_re_pos x) hgap
  nlinarith

/-- On the positive physical half-line the modular-lambda coordinate lies in `(-1,0)`. -/
theorem thetaCuspModularODEState_Z_re_mem_Ioo_neg_zero
    {x : ℝ} (hx : 0 < x) :
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ∈
      Set.Ioo (-1) 0 := by
  refine ⟨(thetaCuspModularODEState_Z_re_mem_Ioo x).1, ?_⟩
  have h := strictAnti_thetaCuspModularODEState_Z_re hx
  simpa only [thetaCuspModularODEState, thetaModularZ_zero, Complex.zero_re] using h

/-- The actual theta modular trajectory follows the universal polynomial vector field. -/
theorem hasDerivAt_thetaCuspModularODEState
    (x : ℝ) (i : HTGeometry.ModularThetaODEState) :
    HasDerivAt (thetaCuspModularODEState i)
      (MvPolynomial.eval (fun j => thetaCuspModularODEState j x)
        (HTGeometry.modularThetaODEVectorField i)) x := by
  cases i with
  | H =>
      have h := (contDiff_thetaModularH.differentiable (by simp) x).hasDerivAt
      rw [deriv_thetaModularH] at h
      have heq :
          MvPolynomial.eval (fun j => thetaCuspModularODEState j x)
              (HTGeometry.modularThetaODEVectorField
                HTGeometry.ModularThetaODEState.H) =
            -(1 / 6 : ℂ) *
              (thetaModularH x * (thetaModularP x +
                thetaModularR x * thetaModularZ x)) := by
        simp [thetaCuspModularODEState,
          HTGeometry.modularThetaODEVectorField]
        ring
      change HasDerivAt thetaModularH _ x
      rw [heq]
      exact h
  | Z =>
      have h := (contDiff_thetaModularZ.differentiable (by simp) x).hasDerivAt
      rw [deriv_thetaModularZ] at h
      simpa [thetaCuspModularODEState,
        HTGeometry.modularThetaODEVectorField, pow_two] using h
  | R =>
      have h := (contDiff_thetaModularR.differentiable (by simp) x).hasDerivAt
      rw [deriv_thetaModularR] at h
      have heq :
          MvPolynomial.eval (fun j => thetaCuspModularODEState j x)
              (HTGeometry.modularThetaODEVectorField
                HTGeometry.ModularThetaODEState.R) =
            -(2 / 3 : ℂ) *
              (thetaModularR x * (thetaModularP x +
                thetaModularR x * thetaModularZ x)) := by
        simp [thetaCuspModularODEState,
          HTGeometry.modularThetaODEVectorField]
        ring
      change HasDerivAt thetaModularR _ x
      rw [heq]
      exact h
  | P =>
      have h := (contDiff_thetaModularP.differentiable (by simp) x).hasDerivAt
      rw [deriv_thetaModularP] at h
      have heq :
          MvPolynomial.eval (fun j => thetaCuspModularODEState j x)
              (HTGeometry.modularThetaODEVectorField
                HTGeometry.ModularThetaODEState.P) =
            3 - (1 / 3 : ℂ) * (thetaModularP x * thetaModularP x) +
              (1 / 12 : ℂ) * ((thetaModularR x * thetaModularR x) *
                (3 + thetaModularZ x * thetaModularZ x)) := by
        simp [thetaCuspModularODEState,
          HTGeometry.modularThetaODEVectorField]
        ring
      change HasDerivAt thetaModularP _ x
      rw [heq]
      exact h

/-- The four-state modular system descends to an autonomous three-state Riccati system
in `(Z,R,S)`, where `S = P + RZ`. -/
theorem hasDerivAt_thetaCuspModularDrift (x : ℝ) :
    HasDerivAt thetaCuspModularDrift
      (3 - thetaCuspModularDrift x ^ 2 / 3 -
        (3 / 4 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
          (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) x := by
  have hP : HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P)
      (3 - (1 / 3 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x ^ 2 +
        (1 / 12 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
          (3 + thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) x := by
    simpa [HTGeometry.modularThetaODEVectorField] using
      hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.P
  have hR : HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R)
      (-(2 / 3 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x +
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
            thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x)) x := by
    simpa [HTGeometry.modularThetaODEVectorField] using
      hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.R
  have hZ : HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z)
      (-thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
        (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) x := by
    simpa [HTGeometry.modularThetaODEVectorField] using
      hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.Z
  have hsum := hP.add (hR.mul hZ)
  have hcoef :
      3 - thetaCuspModularDrift x ^ 2 / 3 -
          (3 / 4 : ℂ) *
            thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
            (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2) =
        (3 - (1 / 3 : ℂ) *
            thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x ^ 2 +
          (1 / 12 : ℂ) *
            thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
            (3 + thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) +
          (-(2 / 3 : ℂ) *
                thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x +
                  thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
                    thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x) *
              thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x +
            thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
              (-thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
                (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2))) := by
    unfold thetaCuspModularDrift
    ring
  rw [hcoef]
  have hfun : thetaCuspModularDrift =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.P +
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.R *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z := by
    funext y
    rfl
  rw [hfun]
  exact hsum

/-- The actual theta orbit follows the autonomous reduced three-state vector field. -/
theorem hasDerivAt_thetaCuspModularReducedState
    (x : ℝ) (i : HTGeometry.ModularThetaReducedState) :
    HasDerivAt (thetaCuspModularReducedState i)
      (MvPolynomial.eval (fun j => thetaCuspModularReducedState j x)
        (HTGeometry.modularThetaReducedVectorField i)) x := by
  cases i with
  | Z =>
      simpa [thetaCuspModularReducedState,
        HTGeometry.modularThetaReducedVectorField,
        HTGeometry.modularThetaODEVectorField, pow_two] using
        hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.Z
  | R =>
      simpa [thetaCuspModularReducedState, thetaCuspModularDrift,
        HTGeometry.modularThetaReducedVectorField,
        HTGeometry.modularThetaODEVectorField] using
        hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.R
  | S =>
      have h := hasDerivAt_thetaCuspModularDrift x
      have hcoef :
          3 - thetaCuspModularDrift x ^ 2 / 3 -
              (3 / 4 : ℂ) *
                thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
                (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2) =
            3 - (1 / 3 : ℂ) * thetaCuspModularDrift x ^ 2 -
              (3 / 4 : ℂ) *
                thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
                (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2) := by
        ring
      rw [hcoef] at h
      simpa only [thetaCuspModularReducedState,
        HTGeometry.modularThetaReducedVectorField, map_sub, map_mul, map_pow,
        MvPolynomial.eval_C, MvPolynomial.eval_X] using h

/-- The theta-mass equation is the covariant scalar leg of the reduced system. -/
theorem hasDerivAt_thetaCuspModularMass_reduced (x : ℝ) :
    HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
      (-(1 / 6 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
          thetaCuspModularReducedState HTGeometry.ModularThetaReducedState.S x) x := by
  simpa [thetaCuspModularReducedState, thetaCuspModularDrift,
    HTGeometry.modularThetaODEVectorField] using
    hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.H

/-- Real form of the reduced three-state Riccati equation on the physical trajectory. -/
theorem hasDerivAt_thetaCuspModularDrift_re (x : ℝ) :
    HasDerivAt (fun y => (thetaCuspModularDrift y).re)
      (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
        (3 / 4 : ℝ) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)) x := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_thetaCuspModularDrift x)
  have hS := thetaCuspModularDrift_im_eq_zero x
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  have hfun : (fun y => (thetaCuspModularDrift y).re) =
      Complex.reCLM ∘ thetaCuspModularDrift := by
    funext y
    rfl
  rw [hfun]
  have hcoef :
      3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
          (3 / 4 : ℝ) *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
            (1 -
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) =
        Complex.reCLM
          (3 - thetaCuspModularDrift x ^ 2 / 3 -
            (3 / 4 : ℂ) *
              thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
              (1 -
                thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)) := by
    change _ =
      (3 - thetaCuspModularDrift x ^ 2 / 3 -
        (3 / 4 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
          (1 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2)).re
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, hS, hR, hZ]
  rw [hcoef]
  exact hre

/-- Real scale equation in reduced drift coordinates. -/
theorem hasDerivAt_thetaCuspModularODEState_R_re (x : ℝ) :
    HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re)
      (-(2 / 3 : ℝ) *
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (thetaCuspModularDrift x).re) x := by
  have hcomplex : HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R)
      (-(2 / 3 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
          thetaCuspModularDrift x) x := by
    simpa [HTGeometry.modularThetaODEVectorField, thetaCuspModularDrift] using
      hasDerivAt_thetaCuspModularODEState x HTGeometry.ModularThetaODEState.R
  have hre : HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re)
      ((-(2 / 3 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
          thetaCuspModularDrift x).re) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomplex
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hS := thetaCuspModularDrift_im_eq_zero x
  have hcoef :
      (-(2 / 3 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
          thetaCuspModularDrift x).re =
        -(2 / 3 : ℝ) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (thetaCuspModularDrift x).re := by
    norm_num [Complex.mul_re, hR, hS]
  rw [hcoef] at hre
  exact hre

/-- The transverse shear satisfies a linear equation with strictly positive forcing. -/
theorem hasDerivAt_thetaCuspModularTransverseShear (x : ℝ) :
    HasDerivAt thetaCuspModularTransverseShear
      (2 + thetaCuspModularGapAmplitude x / 2 +
        (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2 -
        (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
          thetaCuspModularTransverseShear x) x := by
  have hS := hasDerivAt_thetaCuspModularDrift_re x
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hZ := hasDerivAt_thetaCuspModularODEState_Z_re x
  have hraw := (hS.const_mul (2 / 3 : ℝ)).sub (hR.mul hZ)
  have hcoef :
      (2 / 3 : ℝ) *
          (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
            (3 / 4 : ℝ) *
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
              (1 -
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)) -
        (-(2 / 3 : ℝ) *
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                (thetaCuspModularDrift x).re *
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re +
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
              (1 -
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2))) =
      2 + thetaCuspModularGapAmplitude x / 2 +
        (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2 -
        (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
          thetaCuspModularTransverseShear x := by
    unfold thetaCuspModularGapAmplitude thetaCuspModularTransverseShear
    ring
  rw [← hcoef]
  have hfun : thetaCuspModularTransverseShear =
      (fun y =>
        (2 / 3 : ℝ) * (thetaCuspModularDrift y).re -
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re) := by
    rfl
  rw [hfun]
  exact hraw

/-- The recovered quasimodular coordinate satisfies a forced linear drift equation. -/
theorem hasDerivAt_thetaCuspModularQuasimodularDrift (x : ℝ) :
    HasDerivAt thetaCuspModularQuasimodularDrift
      (3 + thetaCuspModularGapAmplitude x / 4 +
        (thetaCuspModularDrift x).re ^ 2 / 3 -
        (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
          thetaCuspModularQuasimodularDrift x) x := by
  have hS : HasDerivAt (fun y => (thetaCuspModularDrift y).re)
      (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
        (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x) x := by
    convert hasDerivAt_thetaCuspModularDrift_re x using 1
    unfold thetaCuspModularGapAmplitude
    ring
  have hW := hasDerivAt_thetaCuspModularTransverseShear x
  have hraw := (hS.const_mul (1 / 3 : ℝ)).add hW
  have hcoef :
      (1 / 3 : ℝ) *
          (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
            (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x) +
        (2 + thetaCuspModularGapAmplitude x / 2 +
          (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2 -
          (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
            thetaCuspModularTransverseShear x) =
      3 + thetaCuspModularGapAmplitude x / 4 +
        (thetaCuspModularDrift x).re ^ 2 / 3 -
        (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
          thetaCuspModularQuasimodularDrift x := by
    unfold thetaCuspModularQuasimodularDrift
    ring
  rw [← hcoef]
  have hfun : thetaCuspModularQuasimodularDrift =
      (fun y =>
        (1 / 3 : ℝ) * (thetaCuspModularDrift y).re +
          thetaCuspModularTransverseShear y) := by
    funext y
    unfold thetaCuspModularQuasimodularDrift
    ring
  rw [hfun]
  exact hraw

/-- Scale normalization cancels the full linear drift of the quasimodular coordinate. -/
theorem hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift (x : ℝ) :
    HasDerivAt thetaCuspModularNormalizedQuasimodularDrift
      ((3 + thetaCuspModularGapAmplitude x / 4 +
          (thetaCuspModularDrift x).re ^ 2 / 3) /
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  have hU := hasDerivAt_thetaCuspModularQuasimodularDrift x
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hRne :
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ≠ 0 :=
    (thetaCuspModularODEState_R_re_pos x).ne'
  have hraw := hU.div hR hRne
  have hcoef :
      ((3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ 2 / 3 -
            (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
              thetaCuspModularQuasimodularDrift x) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re -
        thetaCuspModularQuasimodularDrift x *
          (-(2 / 3 : ℝ) *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
              (thetaCuspModularDrift x).re)) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 =
        (3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ 2 / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re := by
    field_simp [hRne]
    ring
  rw [← hcoef]
  have hfun : thetaCuspModularNormalizedQuasimodularDrift =
      (fun y =>
        thetaCuspModularQuasimodularDrift y /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re) := by
    rfl
  rw [hfun]
  exact hraw

/-- Scale-free quasimodular drift is a second global strict Lyapunov coordinate. -/
theorem strictMono_thetaCuspModularNormalizedQuasimodularDrift :
    StrictMono thetaCuspModularNormalizedQuasimodularDrift := by
  apply strictMono_of_hasDerivAt_pos
    hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift
  intro x
  have hA := thetaCuspModularGapAmplitude_pos x
  exact div_pos (by nlinarith [sq_nonneg (thetaCuspModularDrift x).re])
    (thetaCuspModularODEState_R_re_pos x)

/-- Normalized quasimodular drift vanishes at self-duality. -/
theorem thetaCuspModularNormalizedQuasimodularDrift_zero :
    thetaCuspModularNormalizedQuasimodularDrift 0 = 0 := by
  unfold thetaCuspModularNormalizedQuasimodularDrift
  rw [thetaCuspModularQuasimodularDrift_eq_P_re]
  dsimp only [thetaCuspModularODEState]
  rw [thetaModularP_zero]
  simp

/-- Recovered quasimodular drift is positive on the positive physical half-line. -/
theorem thetaCuspModularQuasimodularDrift_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularQuasimodularDrift x := by
  have hmono := strictMono_thetaCuspModularNormalizedQuasimodularDrift hx
  rw [thetaCuspModularNormalizedQuasimodularDrift_zero] at hmono
  unfold thetaCuspModularNormalizedQuasimodularDrift at hmono
  have hR := thetaCuspModularODEState_R_re_pos x
  rcases div_pos_iff.mp hmono with h | h
  · exact h.1
  · linarith [h.2, hR]

/-- The transverse shear stays strictly above the opposite one-third drift ray. -/
theorem neg_one_third_mul_thetaCuspModularDrift_re_lt_transverseShear
    {x : ℝ} (hx : 0 < x) :
    -(1 / 3 : ℝ) * (thetaCuspModularDrift x).re <
      thetaCuspModularTransverseShear x := by
  have hU := thetaCuspModularQuasimodularDrift_pos_of_pos hx
  unfold thetaCuspModularQuasimodularDrift at hU
  linarith

/-- Difference of the two scale-free clocks is exactly normalized Riccati drift. -/
theorem thetaCuspModularNormalizedQuasimodularDrift_sub_normalizedShear
    (x : ℝ) :
    thetaCuspModularNormalizedQuasimodularDrift x -
        thetaCuspModularNormalizedShear x =
      (thetaCuspModularDrift x).re /
        (3 *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) := by
  have hRne :
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ≠ 0 :=
    (thetaCuspModularODEState_R_re_pos x).ne'
  unfold thetaCuspModularNormalizedQuasimodularDrift
    thetaCuspModularQuasimodularDrift thetaCuspModularNormalizedShear
  field_simp [hRne]
  ring

/-- The modular-lambda coordinate is the exact skew combination of the two strict clocks. -/
theorem three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift
    (x : ℝ) :
    3 * thetaCuspModularNormalizedShear x -
        2 * thetaCuspModularNormalizedQuasimodularDrift x =
      -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re := by
  have hRne :
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ≠ 0 :=
    (thetaCuspModularODEState_R_re_pos x).ne'
  have hRim := thetaCuspModularODEState_R_im_eq_zero x
  have hZim := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularNormalizedShear
    thetaCuspModularNormalizedQuasimodularDrift
    thetaCuspModularQuasimodularDrift thetaCuspModularTransverseShear
    thetaCuspModularDrift
  simp only [Complex.add_re, Complex.mul_re, hRim, hZim, mul_zero,
    sub_zero]
  field_simp [hRne]
  ring

/-- Dividing transverse shear by modular scale cancels its linear drift exactly. -/
theorem hasDerivAt_thetaCuspModularNormalizedShear (x : ℝ) :
    HasDerivAt thetaCuspModularNormalizedShear
      ((2 + thetaCuspModularGapAmplitude x / 2 +
          (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2) /
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  have hW := hasDerivAt_thetaCuspModularTransverseShear x
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hRne :
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ≠ 0 :=
    (thetaCuspModularODEState_R_re_pos x).ne'
  have hraw := hW.div hR hRne
  have hcoef :
      ((2 + thetaCuspModularGapAmplitude x / 2 +
            (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2 -
            (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
              thetaCuspModularTransverseShear x) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re -
        thetaCuspModularTransverseShear x *
          (-(2 / 3 : ℝ) *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
              (thetaCuspModularDrift x).re)) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 =
        (2 + thetaCuspModularGapAmplitude x / 2 +
            (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re := by
    field_simp [hRne]
    ring
  rw [← hcoef]
  have hfun : thetaCuspModularNormalizedShear =
      (fun y =>
        thetaCuspModularTransverseShear y /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re) := by
    rfl
  rw [hfun]
  exact hraw

/-- Scale-free transverse shear is a global strict Lyapunov coordinate. -/
theorem strictMono_thetaCuspModularNormalizedShear :
    StrictMono thetaCuspModularNormalizedShear := by
  apply strictMono_of_hasDerivAt_pos hasDerivAt_thetaCuspModularNormalizedShear
  intro x
  have hR := thetaCuspModularODEState_R_re_pos x
  have hA := thetaCuspModularGapAmplitude_pos x
  exact div_pos (by positivity) hR

/-- Normalized transverse shear vanishes at the self-dual center. -/
theorem thetaCuspModularNormalizedShear_zero :
    thetaCuspModularNormalizedShear 0 = 0 := by
  unfold thetaCuspModularNormalizedShear thetaCuspModularTransverseShear
  rw [thetaCuspModularDrift_re_zero]
  dsimp only [thetaCuspModularODEState]
  rw [thetaModularZ_zero]
  norm_num

/-- Normalized transverse shear is positive on the positive physical half-line. -/
theorem thetaCuspModularNormalizedShear_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularNormalizedShear x := by
  have h := strictMono_thetaCuspModularNormalizedShear hx
  rwa [thetaCuspModularNormalizedShear_zero] at h

/-- Transverse shear itself is positive on the positive physical half-line. -/
theorem thetaCuspModularTransverseShear_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularTransverseShear x := by
  have hT := thetaCuspModularNormalizedShear_pos_of_pos hx
  unfold thetaCuspModularNormalizedShear at hT
  have hR := thetaCuspModularODEState_R_re_pos x
  rcases div_pos_iff.mp hT with h | h
  · exact h.1
  · linarith [h.2, hR]

/-- The discriminant gap decays by twice the transverse shear. -/
theorem hasDerivAt_thetaCuspModularGapAmplitude (x : ℝ) :
    HasDerivAt thetaCuspModularGapAmplitude
      (-2 * thetaCuspModularGapAmplitude x *
        thetaCuspModularTransverseShear x) x := by
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hZ := hasDerivAt_thetaCuspModularODEState_Z_re x
  have hR2 : HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re ^ 2)
      (2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
        (-(2 / 3 : ℝ) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (thetaCuspModularDrift x).re)) x := by
    convert hR.pow 2 using 1 <;> first | rfl | ring
  have hZ2 : HasDerivAt
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re ^ 2)
      (2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re *
        (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2))) x := by
    convert hZ.pow 2 using 1 <;> first | rfl | ring
  have hgap := (hasDerivAt_const x (1 : ℝ)).sub hZ2
  have hraw := hR2.mul hgap
  have hcoef :
      (2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (-(2 / 3 : ℝ) *
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                (thetaCuspModularDrift x).re)) *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) +
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
          (0 -
            2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re *
              (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                (1 -
                  (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2))) =
      -2 * thetaCuspModularGapAmplitude x *
        thetaCuspModularTransverseShear x := by
    unfold thetaCuspModularGapAmplitude thetaCuspModularTransverseShear
    ring
  rw [← hcoef]
  have hfun : thetaCuspModularGapAmplitude =
      (fun y =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re ^ 2 *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re ^ 2)) := by
    rfl
  rw [hfun]
  exact hraw

/-- The modular gap is a product of two positive-chamber linear factors. -/
theorem thetaCuspModularGapAmplitude_eq_positiveChamberFactors (x : ℝ) :
    thetaCuspModularGapAmplitude x =
      ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (1 +
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re)) *
        (2 * thetaCuspModularQuasimodularDrift x -
          2 * (thetaCuspModularDrift x).re +
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 +
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re)) := by
  rw [thetaCuspModularQuasimodularDrift_eq_P_re]
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularGapAmplitude thetaCuspModularDrift
  simp only [Complex.add_re, Complex.mul_re, hR, hZ, mul_zero, sub_zero]
  ring

/-- The actual theta orbit follows the autonomous Lyapunov `(S,A,W)` vector field. -/
theorem hasDerivAt_thetaCuspModularLyapunovState
    (x : ℝ) (i : HTGeometry.ModularThetaLyapunovState) :
    HasDerivAt (thetaCuspModularLyapunovState i)
      (MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
        (HTGeometry.modularThetaLyapunovVectorField i)) x := by
  cases i with
  | S =>
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_thetaCuspModularDrift_re x)
      have hfun :
          thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S =
            Complex.ofRealCLM ∘ (fun y => (thetaCuspModularDrift y).re) := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
              (HTGeometry.modularThetaLyapunovVectorField
                HTGeometry.ModularThetaLyapunovState.S) =
            Complex.ofRealCLM
              (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
                (3 / 4 : ℝ) *
                  (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
                  (1 -
                    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)) := by
        simp [thetaCuspModularLyapunovState,
          HTGeometry.modularThetaLyapunovVectorField,
          thetaCuspModularGapAmplitude]
        ring
      rw [hcoef]
      exact h
  | A =>
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_thetaCuspModularGapAmplitude x)
      have hfun :
          thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.A =
            Complex.ofRealCLM ∘ thetaCuspModularGapAmplitude := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
              (HTGeometry.modularThetaLyapunovVectorField
                HTGeometry.ModularThetaLyapunovState.A) =
            Complex.ofRealCLM
              (-2 * thetaCuspModularGapAmplitude x *
                thetaCuspModularTransverseShear x) := by
        simp [thetaCuspModularLyapunovState,
          HTGeometry.modularThetaLyapunovVectorField]
      rw [hcoef]
      exact h
  | W =>
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_thetaCuspModularTransverseShear x)
      have hfun :
          thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.W =
            Complex.ofRealCLM ∘ thetaCuspModularTransverseShear := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularLyapunovState j x)
              (HTGeometry.modularThetaLyapunovVectorField
                HTGeometry.ModularThetaLyapunovState.W) =
            Complex.ofRealCLM
              (2 + thetaCuspModularGapAmplitude x / 2 +
                (2 / 9 : ℝ) * (thetaCuspModularDrift x).re ^ 2 -
                (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
                  thetaCuspModularTransverseShear x) := by
        simp [thetaCuspModularLyapunovState,
          HTGeometry.modularThetaLyapunovVectorField]
        ring
      rw [hcoef]
      exact h

/-- The theta mass is the covariant scalar leg of the physical Lyapunov system. -/
theorem hasDerivAt_thetaCuspModularMass_lyapunov (x : ℝ) :
    HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
      (-(1 / 6 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
          thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S x) x := by
  have h := hasDerivAt_thetaCuspModularMass_reduced x
  change HasDerivAt
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    (-(1 / 6 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        thetaCuspModularDrift x) x at h
  have hS :
      thetaCuspModularDrift x = ((thetaCuspModularDrift x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [thetaCuspModularDrift_im_eq_zero]
  rw [hS] at h
  change HasDerivAt
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    (-(1 / 6 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        ((thetaCuspModularDrift x).re : ℂ)) x
  exact h

/-- The actual theta orbit follows the positive-chamber polynomial vector field. -/
theorem hasDerivAt_thetaCuspModularPositiveState
    (x : ℝ) (i : HTGeometry.ModularThetaPositiveState) :
    HasDerivAt (thetaCuspModularPositiveState i)
      (MvPolynomial.eval (fun j => thetaCuspModularPositiveState j x)
        (HTGeometry.modularThetaPositiveVectorField i)) x := by
  cases i with
  | U =>
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_thetaCuspModularQuasimodularDrift x)
      have hfun :
          thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.U =
            Complex.ofRealCLM ∘ thetaCuspModularQuasimodularDrift := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularPositiveState j x)
              (HTGeometry.modularThetaPositiveVectorField
                HTGeometry.ModularThetaPositiveState.U) =
            Complex.ofRealCLM
              (3 + thetaCuspModularGapAmplitude x / 4 +
                (thetaCuspModularDrift x).re ^ 2 / 3 -
                (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
                  thetaCuspModularQuasimodularDrift x) := by
        rw [thetaCuspModularGapAmplitude_eq_positiveChamberFactors x]
        simp [thetaCuspModularPositiveState,
          HTGeometry.modularThetaPositiveVectorField,
          HTGeometry.modularThetaPositiveGap]
        ring
      rw [hcoef]
      exact h
  | B =>
      have hS : HasDerivAt (fun y => (thetaCuspModularDrift y).re)
          (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
            (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x) x := by
        convert hasDerivAt_thetaCuspModularDrift_re x using 1
        unfold thetaCuspModularGapAmplitude
        ring
      have hreal := hS.const_mul (-(1 / 3 : ℝ))
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hreal
      have hfun :
          thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B =
            Complex.ofRealCLM ∘
              (fun y => -(1 / 3 : ℝ) * (thetaCuspModularDrift y).re) := by
        funext y
        simp [thetaCuspModularPositiveState]
        ring
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularPositiveState j x)
              (HTGeometry.modularThetaPositiveVectorField
                HTGeometry.ModularThetaPositiveState.B) =
            Complex.ofRealCLM
              (-(1 / 3 : ℝ) *
                (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
                  (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x)) := by
        rw [thetaCuspModularGapAmplitude_eq_positiveChamberFactors x]
        simp [thetaCuspModularPositiveState,
          HTGeometry.modularThetaPositiveVectorField,
          HTGeometry.modularThetaPositiveGap]
        ring
      rw [hcoef]
      exact h
  | C =>
      have hR := hasDerivAt_thetaCuspModularODEState_R_re x
      have hZ := hasDerivAt_thetaCuspModularODEState_Z_re x
      have honePlusZ := (hasDerivAt_const x (1 : ℝ)).add hZ
      have hreal : HasDerivAt
          (fun y =>
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re *
              (1 +
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re))
          ((-(2 / 3 : ℝ) *
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                  (thetaCuspModularDrift x).re) *
              (1 +
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) +
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
              (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                  (1 -
                  (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2))) x := by
        have hraw := hR.mul honePlusZ
        have hfunReal :
            (fun y =>
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re *
                (1 +
                  (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re)) =
              (fun y =>
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re) *
                ((fun _ => (1 : ℝ)) +
                  fun y =>
                    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re) := by
          funext y
          rfl
        rw [hfunReal]
        simpa only [Pi.add_apply, zero_add] using hraw
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hreal
      have hfun :
          thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.C =
            Complex.ofRealCLM ∘
              (fun y =>
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re *
                  (1 +
                    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re)) := by
        funext y
        simp [thetaCuspModularPositiveState]
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularPositiveState j x)
              (HTGeometry.modularThetaPositiveVectorField
                HTGeometry.ModularThetaPositiveState.C) =
            Complex.ofRealCLM
              ((-(2 / 3 : ℝ) *
                    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                      (thetaCuspModularDrift x).re) *
                  (1 +
                    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) +
                (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                  (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
                    (1 -
                      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2))) := by
        have hRim := thetaCuspModularODEState_R_im_eq_zero x
        have hZim := thetaCuspModularODEState_Z_im_eq_zero x
        simp [thetaCuspModularPositiveState,
          HTGeometry.modularThetaPositiveVectorField,
          thetaCuspModularDrift, hRim, hZim]
        rw [thetaCuspModularQuasimodularDrift_eq_P_re]
        ring
      rw [hcoef]
      exact h

/-- Theta mass is the covariant scalar leg of the positive-chamber system. -/
theorem hasDerivAt_thetaCuspModularMass_positive (x : ℝ) :
    HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
      ((1 / 2 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
          thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B x) x := by
  have h := hasDerivAt_thetaCuspModularMass_lyapunov x
  change HasDerivAt
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    (-(1 / 6 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        ((thetaCuspModularDrift x).re : ℂ)) x at h
  have hcoef :
      (1 / 2 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
            thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B x =
        -(1 / 6 : ℂ) *
          thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
            ((thetaCuspModularDrift x).re : ℂ) := by
    simp [thetaCuspModularPositiveState]
    ring
  rw [hcoef]
  exact h

/-- The actual theta orbit follows the source-positive polynomial vector field. -/
theorem hasDerivAt_thetaCuspModularSourcePositiveState
    (x : ℝ) (i : HTGeometry.ModularThetaSourcePositiveState) :
    HasDerivAt (thetaCuspModularSourcePositiveState i)
      (MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
        (HTGeometry.modularThetaSourcePositiveVectorField i)) x := by
  cases i with
  | U =>
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
        (hasDerivAt_thetaCuspModularQuasimodularDrift x)
      have hfun :
          thetaCuspModularSourcePositiveState
              HTGeometry.ModularThetaSourcePositiveState.U =
            Complex.ofRealCLM ∘ thetaCuspModularQuasimodularDrift := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
              (HTGeometry.modularThetaSourcePositiveVectorField
                HTGeometry.ModularThetaSourcePositiveState.U) =
            Complex.ofRealCLM
              (3 + thetaCuspModularGapAmplitude x / 4 +
                (thetaCuspModularDrift x).re ^ 2 / 3 -
                (2 / 3 : ℝ) * (thetaCuspModularDrift x).re *
                  thetaCuspModularQuasimodularDrift x) := by
        simp [thetaCuspModularSourcePositiveState,
          HTGeometry.modularThetaSourcePositiveVectorField]
        ring
      rw [hcoef]
      exact h
  | B =>
      have hS : HasDerivAt (fun y => (thetaCuspModularDrift y).re)
          (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
            (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x) x := by
        convert hasDerivAt_thetaCuspModularDrift_re x using 1
        unfold thetaCuspModularGapAmplitude
        ring
      have hreal := hS.const_mul (-(1 / 3 : ℝ))
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hreal
      have hfun :
          thetaCuspModularSourcePositiveState
              HTGeometry.ModularThetaSourcePositiveState.B =
            Complex.ofRealCLM ∘
              (fun y => -(1 / 3 : ℝ) * (thetaCuspModularDrift y).re) := by
        funext y
        simp [thetaCuspModularSourcePositiveState]
        ring
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
              (HTGeometry.modularThetaSourcePositiveVectorField
                HTGeometry.ModularThetaSourcePositiveState.B) =
            Complex.ofRealCLM
              (-(1 / 3 : ℝ) *
                (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
                  (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x)) := by
        simp [thetaCuspModularSourcePositiveState,
          HTGeometry.modularThetaSourcePositiveVectorField]
        ring
      rw [hcoef]
      exact h
  | Q =>
      have hS : HasDerivAt (fun y => (thetaCuspModularDrift y).re)
          (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
            (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x) x := by
        convert hasDerivAt_thetaCuspModularDrift_re x using 1
        unfold thetaCuspModularGapAmplitude
        ring
      have hB : HasDerivAt
          (fun y => -(thetaCuspModularDrift y).re / 3)
          (-(1 / 3 : ℝ) *
            (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
              (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x)) x := by
        have hB0 := hS.const_mul (-(1 / 3 : ℝ))
        have hfunB :
            (fun y => -(1 / 3 : ℝ) * (thetaCuspModularDrift y).re) =
              (fun y => -(thetaCuspModularDrift y).re / 3) := by
          funext y
          ring
        rw [← hfunB]
        exact hB0
      have hA := hasDerivAt_thetaCuspModularGapAmplitude x
      have hraw :=
        ((((hB.pow 2).const_mul (6 : ℝ)).add hA).sub_const 6).div_const 16
      have hreal : HasDerivAt
          (fun y =>
            (6 * (-(thetaCuspModularDrift y).re / 3) ^ 2 +
              thetaCuspModularGapAmplitude y - 6) / 16)
          ((6 *
                (2 * (-(thetaCuspModularDrift x).re / 3) *
                  (-(1 / 3 : ℝ) *
                    (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
                      (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x))) +
              (-2 * thetaCuspModularGapAmplitude x *
                thetaCuspModularTransverseShear x)) / 16) x := by
        simpa only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
          Nat.cast_ofNat, pow_one] using! hraw.congr_deriv (by ring)
      have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hreal
      have hfun :
          thetaCuspModularSourcePositiveState
              HTGeometry.ModularThetaSourcePositiveState.Q =
            Complex.ofRealCLM ∘
              (fun y =>
                (6 * (-(thetaCuspModularDrift y).re / 3) ^ 2 +
                  thetaCuspModularGapAmplitude y - 6) / 16) := by
        funext y
        rfl
      rw [hfun]
      have hcoef :
          MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
              (HTGeometry.modularThetaSourcePositiveVectorField
                HTGeometry.ModularThetaSourcePositiveState.Q) =
            Complex.ofRealCLM
              ((6 *
                    (2 * (-(thetaCuspModularDrift x).re / 3) *
                      (-(1 / 3 : ℝ) *
                        (3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
                          (3 / 4 : ℝ) * thetaCuspModularGapAmplitude x))) +
                  (-2 * thetaCuspModularGapAmplitude x *
                    thetaCuspModularTransverseShear x)) / 16) := by
        simp [thetaCuspModularSourcePositiveState,
          HTGeometry.modularThetaSourcePositiveVectorField,
          HTGeometry.modularThetaSourcePositiveGap,
          thetaCuspModularQuasimodularDrift]
        ring
      rw [hcoef]
      exact h

/-- Theta mass is the covariant scalar leg of the source-positive system. -/
theorem hasDerivAt_thetaCuspModularMass_sourcePositive (x : ℝ) :
    HasDerivAt
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
      ((1 / 2 : ℂ) *
        thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
          thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.B x) x := by
  simpa [thetaCuspModularSourcePositiveState,
    thetaCuspModularPositiveState] using
    hasDerivAt_thetaCuspModularMass_positive x

/-- The modular discriminant gap decreases strictly on the positive physical half-line. -/
theorem strictAntiOn_thetaCuspModularGapAmplitude :
    StrictAntiOn thetaCuspModularGapAmplitude (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspModularGapAmplitude x).continuousAt).continuousOn
  · intro x hx
    rw [(hasDerivAt_thetaCuspModularGapAmplitude x).deriv]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (thetaCuspModularGapAmplitude_pos x))
      (thetaCuspModularTransverseShear_pos_of_pos (by simpa using hx))

/-- Exact self-dual value of the modular discriminant gap. -/
theorem thetaCuspModularGapAmplitude_zero :
    thetaCuspModularGapAmplitude 0 = thetaCuspSelfDualModularScale ^ 2 := by
  unfold thetaCuspModularGapAmplitude
  dsimp only [thetaCuspModularODEState]
  rw [thetaModularR_zero, thetaModularZ_zero]
  norm_num

/-- The modular discriminant gap is strictly below its self-dual value for `x > 0`. -/
theorem thetaCuspModularGapAmplitude_lt_selfDual_of_pos {x : ℝ} (hx : 0 < x) :
    thetaCuspModularGapAmplitude x < thetaCuspSelfDualModularScale ^ 2 := by
  have hanti : StrictAntiOn thetaCuspModularGapAmplitude (Set.Icc 0 x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularGapAmplitude y).continuousAt).continuousOn
    · intro y hy
      have hypos : 0 < y := by
        have hy' : y ∈ Set.Ioo 0 x := by
          simpa only [interior_Icc] using hy
        exact hy'.1
      rw [(hasDerivAt_thetaCuspModularGapAmplitude y).deriv]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (thetaCuspModularGapAmplitude_pos y))
        (thetaCuspModularTransverseShear_pos_of_pos hypos)
  have h := hanti (by exact ⟨le_rfl, hx.le⟩) (by exact ⟨hx.le, le_rfl⟩) hx
  rwa [thetaCuspModularGapAmplitude_zero] at h

private theorem completedThetaProfile_sourceJet_at
    (n : ℕ) (x : ℝ) :
    (iteratedDeriv (n + 2) thetaModularH x -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH x) / 2 =
      ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [iteratedDeriv_thetaModularH, iteratedDeriv_thetaModularH]
  have hreal :
      (iteratedDeriv (n + 2) Bottcher.completedThetaProfile x -
          (1 / 4 : ℝ) *
            iteratedDeriv n Bottcher.completedThetaProfile x) / 2 =
        iteratedDeriv n thetaCuspFullSource x := by
    rw [iteratedDeriv_completedThetaProfile,
      iteratedDeriv_completedThetaProfile,
      iteratedDeriv_thetaCuspFullSource_eq_tail]
    have hp :
        (1 / 2 : ℝ) ^ (n + 2) =
          (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [pow_add]
      norm_num
      ring
    rw [hp]
    norm_num
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  norm_num at hc ⊢
  exact hc

/-- Universal modular polynomial evaluated on the actual theta trajectory. -/
def thetaCuspReflectedEighthGeneralModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularODEState i x)
    HTGeometry.modularThetaReflectedEighthGeneralPolynomial

/-- Universal rank-three polynomial after removing the completed-theta mass factor. -/
def thetaCuspReflectedEighthNormalizedModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularODEState i x)
    HTGeometry.modularThetaReflectedEighthNormalizedPolynomial

/-- Genuine three-state reduced modular D1 value on the actual theta orbit. -/
def thetaCuspReflectedEighthReducedModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularReducedState i x)
    HTGeometry.modularThetaReducedReflectedEighthPolynomial

/-- Rank-three modular D1 value in the physical Lyapunov `(S,A,W)` chart. -/
def thetaCuspReflectedEighthLyapunovModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularLyapunovState i x)
    HTGeometry.modularThetaLyapunovReflectedEighthPolynomial

/-- Rank-three modular D1 value in the strict positive-chamber `(U,B,C)` chart. -/
def thetaCuspReflectedEighthPositiveModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularPositiveState i x)
    HTGeometry.modularThetaPositiveReflectedEighthPolynomial

/-- Rank-three modular D1 value in source-positive `(U,B,Q)` coordinates. -/
def thetaCuspReflectedEighthSourcePositiveModularValue (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun i => thetaCuspModularSourcePositiveState i x)
    HTGeometry.modularThetaSourcePositiveReflectedEighthPolynomial

/-- Mass-normalized theta-cusp source factor in the three non-mass modular coordinates. -/
def thetaCuspModularSourceFactor (x : ℝ) : ℂ :=
  (1 / 24 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x ^ 2 +
    (1 / 12 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x +
    (1 / 48 : ℂ) *
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x ^ 2 *
        (3 - thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x ^ 2) -
    3 / 8

/-- Exact mass-normalized theta-cusp source in the three non-mass modular coordinates. -/
theorem ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor
    (x : ℝ) :
    (thetaCuspFullSource x : ℂ) =
      (Bottcher.completedThetaProfile x : ℂ) *
        thetaCuspModularSourceFactor x := by
  unfold thetaCuspModularSourceFactor
  have hpoly := HTGeometry.eval_modularThetaODESourceJet_eq
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState 0 x
  change MvPolynomial.eval (fun j => thetaCuspModularODEState j x)
      (HTGeometry.modularThetaODESourceJet 0) =
    (iteratedDeriv (0 + 2) thetaModularH x -
      (1 / 4 : ℂ) * iteratedDeriv 0 thetaModularH x) / 2 at hpoly
  rw [completedThetaProfile_sourceJet_at 0 x] at hpoly
  rw [iteratedDeriv_zero] at hpoly
  rw [← hpoly, HTGeometry.modularThetaODESourceJet_eq_X_H_mul_normalized]
  simp only [map_mul, MvPolynomial.eval_X]
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile,
    HTGeometry.eval_modularThetaODENormalizedSourceJet_zero]

/-- The mass-normalized theta-cusp source factor is real on the physical trajectory. -/
theorem thetaCuspModularSourceFactor_im_eq_zero (x : ℝ) :
    (thetaCuspModularSourceFactor x).im = 0 := by
  have h := congrArg Complex.im
    (ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor x)
  simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul, add_zero] at h
  have hm := thetaCuspCompletedThetaProfile_pos x
  nlinarith

private theorem thetaCuspFullSource_zero_pos_from_modularFactor :
    0 < thetaCuspFullSource 0 := by
  have h := congrArg Complex.re
    (ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor 0)
  unfold thetaCuspModularSourceFactor at h
  dsimp only [thetaCuspModularODEState] at h
  rw [thetaModularP_zero, thetaModularZ_zero, thetaModularR_zero] at h
  norm_num [Complex.mul_re] at h
  rw [h]
  have hm := thetaCuspCompletedThetaProfile_pos 0
  have hR := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hpRe : (((thetaCuspSelfDualModularScale : ℂ) ^ 2).re) =
      thetaCuspSelfDualModularScale ^ 2 := by norm_cast
  rw [hpRe]
  exact mul_pos hm (by nlinarith)

/-- The full theta-cusp source is strictly positive on the complete real line. -/
theorem thetaCuspFullSource_pos (x : ℝ) :
    0 < thetaCuspFullSource x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hneg := thetaCuspFullSource_pos_of_pos (show 0 < -x by linarith)
    rwa [thetaCuspFullSource_neg x] at hneg
  · exact thetaCuspFullSource_zero_pos_from_modularFactor
  · exact thetaCuspFullSource_pos_of_pos hx

/-- Positivity of the theta-cusp source makes the completed theta profile strictly convex. -/
theorem completedThetaProfile_secondDerivative_pos (x : ℝ) :
    0 < iteratedDeriv 2 Bottcher.completedThetaProfile x := by
  have hcomplex := completedThetaProfile_sourceJet_at 0 x
  rw [iteratedDeriv_thetaModularH, iteratedDeriv_thetaModularH] at hcomplex
  simp only [Nat.zero_add, iteratedDeriv_zero] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  norm_num at hreal
  have hs := thetaCuspFullSource_pos x
  have hm := thetaCuspCompletedThetaProfile_pos x
  nlinarith

/-- The ordinary derivative of the completed theta profile differentiates to its second jet. -/
theorem hasDerivAt_deriv_completedThetaProfile (x : ℝ) :
    HasDerivAt (deriv Bottcher.completedThetaProfile)
      (iteratedDeriv 2 Bottcher.completedThetaProfile x) x := by
  have hd := contDiff_completedThetaProfile.differentiable_iteratedDeriv 1 (by norm_num)
  have h := (hd x).hasDerivAt
  have hfun : iteratedDeriv 1 Bottcher.completedThetaProfile =
      deriv Bottcher.completedThetaProfile := iteratedDeriv_one
  rw [hfun] at h
  have hcoef : iteratedDeriv 2 Bottcher.completedThetaProfile x =
      deriv (deriv Bottcher.completedThetaProfile) x := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, hfun]
  rw [hcoef]
  exact h

/-- The first derivative of the completed theta profile is strictly increasing. -/
theorem strictMono_deriv_completedThetaProfile :
    StrictMono (deriv Bottcher.completedThetaProfile) := by
  exact strictMono_of_hasDerivAt_pos hasDerivAt_deriv_completedThetaProfile
    completedThetaProfile_secondDerivative_pos

/-- Self-duality forces the completed theta profile's first derivative to vanish at the center. -/
theorem deriv_completedThetaProfile_zero :
    deriv Bottcher.completedThetaProfile 0 = 0 := by
  have hzero : deriv thetaModularH 0 = 0 := by
    rw [deriv_thetaModularH, thetaModularP_zero, thetaModularZ_zero]
    ring
  have hrel := iteratedDeriv_thetaModularH 1 0
  simp only [iteratedDeriv_one, hzero] at hrel
  have hre := congrArg Complex.re hrel
  exact (by simpa only [Complex.zero_re, Complex.ofReal_re] using hre.symm)

/-- Strict convexity and the self-dual center force positive mass slope for `x > 0`. -/
theorem deriv_completedThetaProfile_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv Bottcher.completedThetaProfile x := by
  have h := strictMono_deriv_completedThetaProfile hx
  rwa [deriv_completedThetaProfile_zero] at h

/-- On the positive physical half-line the reduced Riccati drift is strictly negative. -/
theorem thetaCuspModularDrift_re_neg_of_pos {x : ℝ} (hx : 0 < x) :
    (thetaCuspModularDrift x).re < 0 := by
  have hrel := iteratedDeriv_thetaModularH 1 x
  simp only [iteratedDeriv_one] at hrel
  rw [deriv_thetaModularH] at hrel
  change
    -(1 / 6 : ℂ) *
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
          thetaCuspModularDrift x) =
      ((deriv Bottcher.completedThetaProfile x : ℝ) : ℂ) at hrel
  have hre := congrArg Complex.re hrel
  have hHim := thetaCuspModularODEState_H_im_eq_zero x
  have hSim := thetaCuspModularDrift_im_eq_zero x
  norm_num [Complex.mul_re, hHim, hSim] at hre
  have hHpos := thetaCuspModularODEState_H_re_pos x
  have hdpos := deriv_completedThetaProfile_pos_of_pos hx
  nlinarith

/-- On the positive half-line the quasimodular clock stays strictly below transverse shear. -/
theorem thetaCuspModularNormalizedQuasimodularDrift_lt_normalizedShear
    {x : ℝ} (hx : 0 < x) :
    thetaCuspModularNormalizedQuasimodularDrift x <
      thetaCuspModularNormalizedShear x := by
  have hdiff :=
    thetaCuspModularNormalizedQuasimodularDrift_sub_normalizedShear x
  have hS := thetaCuspModularDrift_re_neg_of_pos hx
  have hR := thetaCuspModularODEState_R_re_pos x
  rw [sub_eq_iff_eq_add] at hdiff
  have hfrac :
      (thetaCuspModularDrift x).re /
          (3 *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) < 0 :=
    div_neg_of_neg_of_pos hS (mul_pos (by norm_num) hR)
  linarith

/-- The two scale-free clocks occupy the strict modular simplex on the positive half-line. -/
theorem thetaCuspModularNormalizedClocks_mem_strictSimplex
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularNormalizedQuasimodularDrift x ∧
      thetaCuspModularNormalizedQuasimodularDrift x <
        thetaCuspModularNormalizedShear x ∧
      0 < 3 * thetaCuspModularNormalizedShear x -
        2 * thetaCuspModularNormalizedQuasimodularDrift x ∧
      3 * thetaCuspModularNormalizedShear x -
          2 * thetaCuspModularNormalizedQuasimodularDrift x < 1 := by
  have hVmono := strictMono_thetaCuspModularNormalizedQuasimodularDrift hx
  rw [thetaCuspModularNormalizedQuasimodularDrift_zero] at hVmono
  have hVT :=
    thetaCuspModularNormalizedQuasimodularDrift_lt_normalizedShear hx
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo_neg_zero hx
  rw [three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift]
  exact ⟨hVmono, hVT, by linarith [hZ.2], by linarith [hZ.1]⟩

/-- Positive-chamber coordinates reconstruct the Lyapunov state polynomially. -/
theorem thetaCuspModularLyapunovState_eq_positiveCoordinates (x : ℝ) :
    (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.S x).re =
        -3 * (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B x).re ∧
      (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.A x).re =
        (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.C x).re *
          (2 * (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.U x).re +
            6 * (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B x).re +
            (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.C x).re) ∧
      (thetaCuspModularLyapunovState HTGeometry.ModularThetaLyapunovState.W x).re =
        (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.U x).re +
          (thetaCuspModularPositiveState HTGeometry.ModularThetaPositiveState.B x).re := by
  constructor
  · simp [thetaCuspModularLyapunovState, thetaCuspModularPositiveState]
    ring
  constructor
  · simp only [thetaCuspModularLyapunovState, thetaCuspModularPositiveState,
      Complex.ofReal_re]
    rw [thetaCuspModularGapAmplitude_eq_positiveChamberFactors]
    ring
  · simp [thetaCuspModularLyapunovState, thetaCuspModularPositiveState,
      thetaCuspModularQuasimodularDrift]
    ring

/-- The actual positive-half theta orbit lies in the strict `(U,B,C)` positive orthant. -/
theorem thetaCuspModularPositiveState_re_pos
    {x : ℝ} (hx : 0 < x) (i : HTGeometry.ModularThetaPositiveState) :
    0 < (thetaCuspModularPositiveState i x).re := by
  cases i with
  | U =>
      simpa [thetaCuspModularPositiveState] using
        thetaCuspModularQuasimodularDrift_pos_of_pos hx
  | B =>
      have hS := thetaCuspModularDrift_re_neg_of_pos hx
      simp [thetaCuspModularPositiveState]
      linarith
  | C =>
      have hR := thetaCuspModularODEState_R_re_pos x
      have hZ := thetaCuspModularODEState_Z_re_mem_Ioo_neg_zero hx
      simp [thetaCuspModularPositiveState]
      exact mul_pos hR (by linarith [hZ.1])

/-- The exact three-coordinate modular source factor is strictly positive everywhere. -/
theorem thetaCuspModularSourceFactor_re_pos (x : ℝ) :
    0 < (thetaCuspModularSourceFactor x).re := by
  have h := congrArg Complex.re
    (ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor x)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  have hs := thetaCuspFullSource_pos x
  have hm := thetaCuspCompletedThetaProfile_pos x
  nlinarith

/-- Real-coordinate form of the exact mass-normalized theta-cusp source factor. -/
theorem thetaCuspModularSourceFactor_re_eq_realCone (x : ℝ) :
    (thetaCuspModularSourceFactor x).re =
      (2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).re ^ 2 +
        4 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).re *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re +
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
          (3 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) -
        18) / 48 := by
  have hP := thetaCuspModularODEState_P_im_eq_zero x
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularSourceFactor
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re]
  simp only [hP, hR, hZ, mul_zero]
  norm_num
  simp only [hR, hZ, mul_zero, zero_mul, add_zero, neg_zero, sub_zero]
  ring

/-- In reduced `(Z,R,S)` coordinates the source cone has no mixed term. -/
theorem thetaCuspModularSourceFactor_re_eq_driftCone (x : ℝ) :
    (thetaCuspModularSourceFactor x).re =
      (2 * (thetaCuspModularDrift x).re ^ 2 +
        3 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
          (1 -
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) -
        18) / 48 := by
  rw [thetaCuspModularSourceFactor_re_eq_realCone]
  have hR := thetaCuspModularODEState_R_im_eq_zero x
  have hZ := thetaCuspModularODEState_Z_im_eq_zero x
  unfold thetaCuspModularDrift
  simp only [Complex.add_re, Complex.mul_re, hR, hZ, mul_zero, sub_zero]
  ring

/-- The source-positive coordinate `Q` is the literal mass-normalized theta source. -/
theorem thetaCuspModularSourcePositiveState_Q_eq_sourceFactor (x : ℝ) :
    thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.Q x =
      thetaCuspModularSourceFactor x := by
  apply Complex.ext
  · simp only [thetaCuspModularSourcePositiveState, Complex.ofReal_re]
    rw [thetaCuspModularSourceFactor_re_eq_driftCone]
    unfold thetaCuspModularGapAmplitude
    ring
  · change (((6 * (-(thetaCuspModularDrift x).re / 3) ^ 2 +
        thetaCuspModularGapAmplitude x - 6) / 16 : ℝ) : ℂ).im =
      (thetaCuspModularSourceFactor x).im
    rw [Complex.ofReal_im, thetaCuspModularSourceFactor_im_eq_zero]

/-- The real theta source is mass times the source-positive `Q` coordinate. -/
theorem ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ (x : ℝ) :
    (thetaCuspFullSource x : ℂ) =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x := by
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile,
    thetaCuspModularSourcePositiveState_Q_eq_sourceFactor]
  exact ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor x

/-- Evaluating reconstructed gap in source-positive coordinates recovers physical gap `A`. -/
theorem eval_modularThetaSourcePositiveGap_eq_gapAmplitude (x : ℝ) :
    MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
        HTGeometry.modularThetaSourcePositiveGap =
      (thetaCuspModularGapAmplitude x : ℂ) := by
  simp [HTGeometry.modularThetaSourcePositiveGap,
    thetaCuspModularSourcePositiveState]
  ring

private theorem iteratedDeriv_thetaModularSourceCombination
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n
        (fun y =>
          (iteratedDeriv 2 thetaModularH y -
            (1 / 4 : ℂ) * thetaModularH y) / 2) x =
      (iteratedDeriv (n + 2) thetaModularH x -
        (1 / 4 : ℂ) * iteratedDeriv n thetaModularH x) / 2 := by
  have hshift : iteratedDeriv n (iteratedDeriv 2 thetaModularH) =
      iteratedDeriv (2 + n) thetaModularH := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ]
        simp only [Nat.add_assoc, Nat.add_comm n 1]
  have hH2 : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 thetaModularH) := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    exact contDiff_thetaModularH.deriv'.deriv'
  rw [show
      (fun y =>
        (iteratedDeriv 2 thetaModularH y -
          (1 / 4 : ℂ) * thetaModularH y) / 2) =
        fun y => (1 / 2 : ℂ) *
          (iteratedDeriv 2 thetaModularH y -
            (1 / 4 : ℂ) * thetaModularH y) by
      funext y
      ring]
  rw [iteratedDeriv_const_mul_field]
  have hsub :
      (fun y => iteratedDeriv 2 thetaModularH y -
        (1 / 4 : ℂ) * thetaModularH y) =
        iteratedDeriv 2 thetaModularH -
          fun y => (1 / 4 : ℂ) * thetaModularH y := rfl
  have hcH : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (1 / 4 : ℂ) * thetaModularH y) :=
    contDiff_const.mul contDiff_thetaModularH
  rw [hsub, iteratedDeriv_sub
    (hH2.contDiffAt.of_le (by exact_mod_cast le_top))
    (hcH.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [iteratedDeriv_const_mul_field]
  rw [hshift]
  ring

/-- On positive half-line all source-positive coordinates are strictly positive. -/
theorem thetaCuspModularSourcePositiveState_re_pos
    {x : ℝ} (hx : 0 < x) (i : HTGeometry.ModularThetaSourcePositiveState) :
    0 < (thetaCuspModularSourcePositiveState i x).re := by
  cases i with
  | U =>
      simpa [thetaCuspModularSourcePositiveState] using
        thetaCuspModularQuasimodularDrift_pos_of_pos hx
  | B =>
      have hS := thetaCuspModularDrift_re_neg_of_pos hx
      simp [thetaCuspModularSourcePositiveState]
      linarith
  | Q =>
      rw [thetaCuspModularSourcePositiveState_Q_eq_sourceFactor]
      exact thetaCuspModularSourceFactor_re_pos x

/-- Every source-positive coordinate is real on physical theta orbit. -/
theorem thetaCuspModularSourcePositiveState_im_eq_zero
    (x : ℝ) (i : HTGeometry.ModularThetaSourcePositiveState) :
    (thetaCuspModularSourcePositiveState i x).im = 0 := by
  cases i with
  | U => simp [thetaCuspModularSourcePositiveState]
  | B => simp [thetaCuspModularSourcePositiveState]
  | Q =>
      change (((6 * (-(thetaCuspModularDrift x).re / 3) ^ 2 +
        thetaCuspModularGapAmplitude x - 6) / 16 : ℝ) : ℂ).im = 0
      exact Complex.ofReal_im _

/-- Real `U` coordinate obeys source-positive vector field's first equation. -/
theorem hasDerivAt_thetaCuspModularSourcePositiveState_U_re (x : ℝ) :
    HasDerivAt
      (fun y => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.U y).re)
      ((9 / 2 : ℝ) +
        4 * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x).re +
        (3 / 2 : ℝ) * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.B x).re ^ 2 +
        2 * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.B x).re *
          (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.U x).re) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_thetaCuspModularSourcePositiveState x
      HTGeometry.ModularThetaSourcePositiveState.U)
  have hB := thetaCuspModularSourcePositiveState_im_eq_zero x
    HTGeometry.ModularThetaSourcePositiveState.B
  have hU := thetaCuspModularSourcePositiveState_im_eq_zero x
    HTGeometry.ModularThetaSourcePositiveState.U
  have hfun :
      (fun y => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.U y).re) =
        Complex.reCLM ∘ thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.U := by
    funext y
    rfl
  rw [hfun]
  have hcoef :
      (MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
        (HTGeometry.modularThetaSourcePositiveVectorField
          HTGeometry.ModularThetaSourcePositiveState.U)).re =
        (9 / 2 : ℝ) +
          4 * (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.Q x).re +
          (3 / 2 : ℝ) * (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.B x).re ^ 2 +
          2 * (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.B x).re *
            (thetaCuspModularSourcePositiveState
              HTGeometry.ModularThetaSourcePositiveState.U x).re := by
    simp [HTGeometry.modularThetaSourcePositiveVectorField, pow_two,
      Complex.mul_re, hB, hU]
  rw [← hcoef]
  exact h

/-- Real `B` coordinate obeys source-positive vector field's second equation. -/
theorem hasDerivAt_thetaCuspModularSourcePositiveState_B_re (x : ℝ) :
    HasDerivAt
      (fun y => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.B y).re)
      ((1 / 2 : ℝ) +
        4 * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x).re -
        (1 / 2 : ℝ) * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.B x).re ^ 2) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_thetaCuspModularSourcePositiveState x
      HTGeometry.ModularThetaSourcePositiveState.B)
  have hB := thetaCuspModularSourcePositiveState_im_eq_zero x
    HTGeometry.ModularThetaSourcePositiveState.B
  have hfun :
      (fun y => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.B y).re) =
        Complex.reCLM ∘ thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.B := by
    funext y
    rfl
  rw [hfun]
  have hcoef :
      (MvPolynomial.eval (fun j => thetaCuspModularSourcePositiveState j x)
        (HTGeometry.modularThetaSourcePositiveVectorField
          HTGeometry.ModularThetaSourcePositiveState.B)).re =
        (1 / 2 : ℝ) +
          4 * (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.Q x).re -
          (1 / 2 : ℝ) * (thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.B x).re ^ 2 := by
    simp [HTGeometry.modularThetaSourcePositiveVectorField, pow_two,
      Complex.mul_re, hB]
  rw [← hcoef]
  exact h

/-- Source-positive quasimodular clock `U` increases strictly on positive half-orbit. -/
theorem strictMonoOn_thetaCuspModularSourcePositiveState_U_re :
    StrictMonoOn
      (fun x => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.U x).re) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspModularSourcePositiveState_U_re x).continuousAt).continuousOn
  · intro x hx
    rw [(hasDerivAt_thetaCuspModularSourcePositiveState_U_re x).deriv]
    have hU := thetaCuspModularSourcePositiveState_re_pos
      (by simpa using hx) HTGeometry.ModularThetaSourcePositiveState.U
    have hB := thetaCuspModularSourcePositiveState_re_pos
      (by simpa using hx) HTGeometry.ModularThetaSourcePositiveState.B
    have hQ := thetaCuspModularSourcePositiveState_re_pos
      (by simpa using hx) HTGeometry.ModularThetaSourcePositiveState.Q
    nlinarith [sq_nonneg
      (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.B x).re]

/-- Source-positive Riccati clock `B` increases strictly; gap supplies exact reserve. -/
theorem strictMonoOn_thetaCuspModularSourcePositiveState_B_re :
    StrictMonoOn
      (fun x => (thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.B x).re) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspModularSourcePositiveState_B_re x).continuousAt).continuousOn
  · intro x hx
    rw [(hasDerivAt_thetaCuspModularSourcePositiveState_B_re x).deriv]
    have hQ := thetaCuspModularSourcePositiveState_re_pos
      (by simpa using hx) HTGeometry.ModularThetaSourcePositiveState.Q
    have hA := thetaCuspModularGapAmplitude_pos x
    have hgap := congrArg Complex.re
      (eval_modularThetaSourcePositiveGap_eq_gapAmplitude x)
    have hBim := thetaCuspModularSourcePositiveState_im_eq_zero x
      HTGeometry.ModularThetaSourcePositiveState.B
    simp [HTGeometry.modularThetaSourcePositiveGap, pow_two,
      Complex.mul_re, hBim] at hgap
    nlinarith

/-- Source positivity is exactly strict dissipation of Riccati drift beyond one quarter of
the discriminant gap. -/
theorem hasDerivAt_thetaCuspModularDrift_re_eq_sourceDissipation (x : ℝ) :
    HasDerivAt (fun y => (thetaCuspModularDrift y).re)
      (-(8 * (thetaCuspModularSourceFactor x).re +
        thetaCuspModularGapAmplitude x / 4)) x := by
  have h := hasDerivAt_thetaCuspModularDrift_re x
  have hfactor := thetaCuspModularSourceFactor_re_eq_driftCone x
  have hcoef :
      3 - (thetaCuspModularDrift x).re ^ 2 / 3 -
          (3 / 4 : ℝ) *
            (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
            (1 -
              (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) =
        -(8 * (thetaCuspModularSourceFactor x).re +
          thetaCuspModularGapAmplitude x / 4) := by
    rw [hfactor]
    unfold thetaCuspModularGapAmplitude
    ring
  rw [← hcoef]
  exact h

/-- The physical modular trajectory lies strictly inside the source cone in `(Z,R,P)`. -/
theorem thetaCuspModularSourceRealCone_pos (x : ℝ) :
    0 <
      2 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).re ^ 2 +
        4 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.P x).re *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re +
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
          (3 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) -
        18 := by
  have hpos := thetaCuspModularSourceFactor_re_pos x
  rw [thetaCuspModularSourceFactor_re_eq_realCone] at hpos
  nlinarith

/-- The physical reduced trajectory lies strictly inside the diagonal source cone. -/
theorem thetaCuspModularSourceDriftCone_pos (x : ℝ) :
    0 < 2 * (thetaCuspModularDrift x).re ^ 2 +
      3 * (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
        (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) -
      18 := by
  have hpos := thetaCuspModularSourceFactor_re_pos x
  rw [thetaCuspModularSourceFactor_re_eq_driftCone] at hpos
  nlinarith

/-- The reduced Riccati drift decreases strictly along the full physical trajectory. -/
theorem strictAnti_thetaCuspModularDrift_re :
    StrictAnti (fun x => (thetaCuspModularDrift x).re) := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_thetaCuspModularDrift_re
  intro x
  have hZ := thetaCuspModularODEState_Z_re_mem_Ioo x
  have hgap : 0 <
      1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2 := by
    have hprod : 0 <
        (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) *
          (1 + (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) :=
      mul_pos (sub_pos.mpr hZ.2) (by linarith [hZ.1])
    nlinarith
  have hA : 0 <
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 *
        (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2) :=
    mul_pos (pow_pos (thetaCuspModularODEState_R_re_pos x) 2) hgap
  have hcone := thetaCuspModularSourceDriftCone_pos x
  nlinarith

/-- Exact factorization of physical modular D1 by the positive sixth power of theta mass. -/
theorem thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized
    (x : ℝ) :
    thetaCuspReflectedEighthGeneralModularValue x =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 *
        thetaCuspReflectedEighthNormalizedModularValue x := by
  exact HTGeometry.eval_modularThetaReflectedEighthGeneralPolynomial_eq_H_pow_six_mul_normalized
    (fun i => thetaCuspModularODEState i x)

/-- The arbitrary-basepoint D1 closure factors through the genuine three-state polynomial. -/
theorem thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_reduced
    (x : ℝ) :
    thetaCuspReflectedEighthGeneralModularValue x =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 *
        thetaCuspReflectedEighthReducedModularValue x := by
  have hgeneral := HTGeometry.modularThetaReflectedEighthGeneralClosure_of_ode
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState x
  have hreduce := HTGeometry.modularThetaReducedReflectedEighthClosure_of_ode
    thetaCuspModularReducedState hasDerivAt_thetaCuspModularReducedState
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    hasDerivAt_thetaCuspModularMass_reduced x
  exact hgeneral.symm.trans hreduce

/-- The arbitrary-basepoint D1 closure factors through the physical Lyapunov polynomial. -/
theorem thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_lyapunov
    (x : ℝ) :
    thetaCuspReflectedEighthGeneralModularValue x =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 *
        thetaCuspReflectedEighthLyapunovModularValue x := by
  have hgeneral := HTGeometry.modularThetaReflectedEighthGeneralClosure_of_ode
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState x
  have hlyapunov := HTGeometry.modularThetaLyapunovReflectedEighthClosure_of_ode
    thetaCuspModularLyapunovState hasDerivAt_thetaCuspModularLyapunovState
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    hasDerivAt_thetaCuspModularMass_lyapunov x
  exact hgeneral.symm.trans hlyapunov

/-- The arbitrary-basepoint D1 closure factors through the positive-chamber polynomial. -/
theorem thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_positive
    (x : ℝ) :
    thetaCuspReflectedEighthGeneralModularValue x =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 *
        thetaCuspReflectedEighthPositiveModularValue x := by
  have hgeneral := HTGeometry.modularThetaReflectedEighthGeneralClosure_of_ode
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState x
  have hpositive := HTGeometry.modularThetaPositiveReflectedEighthClosure_of_ode
    thetaCuspModularPositiveState hasDerivAt_thetaCuspModularPositiveState
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    hasDerivAt_thetaCuspModularMass_positive x
  exact hgeneral.symm.trans hpositive

/-- The arbitrary-basepoint D1 closure factors through source-positive `(U,B,Q)` coordinates. -/
theorem thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_sourcePositive
    (x : ℝ) :
    thetaCuspReflectedEighthGeneralModularValue x =
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 *
        thetaCuspReflectedEighthSourcePositiveModularValue x := by
  let H : ℝ → ℂ :=
    thetaCuspModularODEState HTGeometry.ModularThetaODEState.H
  let F : ℝ → ℂ := fun y =>
    (iteratedDeriv 2 H y - (1 / 4 : ℂ) * H y) / 2
  have hF : ∀ y, F y = H y *
      thetaCuspModularSourcePositiveState
        HTGeometry.ModularThetaSourcePositiveState.Q y := by
    intro y
    calc
      F y = (thetaCuspFullSource y : ℂ) := by
        dsimp only [F, H, thetaCuspModularODEState]
        simpa only [Nat.zero_add, iteratedDeriv_zero] using
          completedThetaProfile_sourceJet_at 0 y
      _ = H y * thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q y := by
        dsimp only [H]
        exact ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ y
  have hgeneral := HTGeometry.modularThetaReflectedEighthGeneralClosure_of_ode
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState x
  have hsource :=
    HTGeometry.modularThetaSourcePositiveReflectedEighthClosure_of_ode
      thetaCuspModularSourcePositiveState
      hasDerivAt_thetaCuspModularSourcePositiveState H F
      hasDerivAt_thetaCuspModularMass_sourcePositive hF x
  dsimp only [F, H, thetaCuspModularODEState] at hsource
  rw [iteratedDeriv_thetaModularSourceCombination 0 x,
    iteratedDeriv_thetaModularSourceCombination 1 x,
    iteratedDeriv_thetaModularSourceCombination 2 x,
    iteratedDeriv_thetaModularSourceCombination 3 x,
    iteratedDeriv_thetaModularSourceCombination 4 x,
    iteratedDeriv_thetaModularSourceCombination 5 x,
    iteratedDeriv_thetaModularSourceCombination 6 x,
    iteratedDeriv_thetaModularSourceCombination 7 x,
    iteratedDeriv_thetaModularSourceCombination 8 x] at hsource
  change thetaCuspReflectedEighthGeneralModularValue x =
    thetaModularH x ^ 6 *
      thetaCuspReflectedEighthSourcePositiveModularValue x
  simpa only [thetaCuspReflectedEighthGeneralModularValue,
    thetaCuspReflectedEighthSourcePositiveModularValue] using
      hgeneral.symm.trans hsource

/-- The old normalized four-state polynomial and the reduced three-state polynomial agree
pointwise on the physical theta orbit. -/
theorem thetaCuspReflectedEighthReducedModularValue_eq_normalized
    (x : ℝ) :
    thetaCuspReflectedEighthReducedModularValue x =
      thetaCuspReflectedEighthNormalizedModularValue x := by
  have hred :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_reduced x
  have hnorm :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x
  rw [hnorm] at hred
  have hHne :
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hpos := thetaCuspModularODEState_H_re_pos x
    rw [hzero] at hpos
    simp at hpos
  exact (mul_left_cancel₀ hHne hred).symm

/-- The Lyapunov-chart polynomial is exactly the normalized modular D1 on the theta orbit. -/
theorem thetaCuspReflectedEighthLyapunovModularValue_eq_normalized
    (x : ℝ) :
    thetaCuspReflectedEighthLyapunovModularValue x =
      thetaCuspReflectedEighthNormalizedModularValue x := by
  have hlyapunov :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_lyapunov x
  have hnorm :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x
  rw [hnorm] at hlyapunov
  have hHne :
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hpos := thetaCuspModularODEState_H_re_pos x
    rw [hzero] at hpos
    simp at hpos
  exact (mul_left_cancel₀ hHne hlyapunov).symm

/-- The positive-chamber polynomial is exactly normalized modular D1 on the theta orbit. -/
theorem thetaCuspReflectedEighthPositiveModularValue_eq_normalized
    (x : ℝ) :
    thetaCuspReflectedEighthPositiveModularValue x =
      thetaCuspReflectedEighthNormalizedModularValue x := by
  have hpositive :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_positive x
  have hnorm :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x
  rw [hnorm] at hpositive
  have hHne :
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hpos := thetaCuspModularODEState_H_re_pos x
    rw [hzero] at hpos
    simp at hpos
  exact (mul_left_cancel₀ hHne hpositive).symm

/-- After canceling positive theta mass, source-positive D1 is normalized D1 on physical orbit. -/
theorem thetaCuspReflectedEighthSourcePositiveModularValue_eq_normalized
    (x : ℝ) :
    thetaCuspReflectedEighthSourcePositiveModularValue x =
      thetaCuspReflectedEighthNormalizedModularValue x := by
  have hsource :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_sourcePositive x
  have hnorm :=
    thetaCuspReflectedEighthGeneralModularValue_eq_H_pow_six_mul_normalized x
  rw [hnorm] at hsource
  have hHne :
      thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x ^ 6 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hpos := thetaCuspModularODEState_H_re_pos x
    rw [hzero] at hpos
    simp at hpos
  exact (mul_left_cancel₀ hHne hsource).symm

/-- At every source coordinate, raw rank-three curvature is the universal four-state polynomial. -/
theorem thetaCuspFullSource_reflectedEighthHankel_eq_generalModular
    (x : ℝ) :
    let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
    ((HilbertMetric.signedEvenHankelThreeDet
      (f 0 ^ 2)
      (HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2))
      (HilbertMetric.reflectedProductFourthJet
        (f 0) (f 1) (f 2) (f 3) (f 4))
      (HilbertMetric.reflectedProductSixthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
      (HilbertMetric.reflectedProductEighthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8)) : ℝ) : ℂ) =
      thetaCuspReflectedEighthGeneralModularValue x := by
  have h := HTGeometry.modularThetaReflectedEighthGeneralClosure_of_ode
    thetaCuspModularODEState hasDerivAt_thetaCuspModularODEState x
  dsimp only [thetaCuspModularODEState] at h
  rw [completedThetaProfile_sourceJet_at 0 x,
    completedThetaProfile_sourceJet_at 1 x,
    completedThetaProfile_sourceJet_at 2 x,
    completedThetaProfile_sourceJet_at 3 x,
    completedThetaProfile_sourceJet_at 4 x,
    completedThetaProfile_sourceJet_at 5 x,
    completedThetaProfile_sourceJet_at 6 x,
    completedThetaProfile_sourceJet_at 7 x,
    completedThetaProfile_sourceJet_at 8 x] at h
  simpa only [thetaCuspReflectedEighthGeneralModularValue,
    thetaCuspModularODEState,
    HilbertMetric.signedEvenHankelThreeDet,
    HilbertMetric.reflectedProductSecondJet,
    HilbertMetric.reflectedProductFourthJet,
    HilbertMetric.reflectedProductSixthJet,
    HilbertMetric.reflectedProductEighthJet,
    HTGeometry.signedEvenHankelThreeDetC, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using h

end

end RHTower
