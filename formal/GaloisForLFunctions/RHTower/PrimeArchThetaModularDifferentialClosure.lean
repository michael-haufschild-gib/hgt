import GaloisForLFunctions.Bottcher.ModularLambdaCovering
import GaloisForLFunctions.Bottcher.ThetaDiscriminant
import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeClosure
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

end

end RHTower
