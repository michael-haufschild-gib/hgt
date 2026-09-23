import GaloisForLFunctions.RHTower.ProlateBandJointSpectrum
import GaloisForLFunctions.RHTower.ProlateEndpointNonvanishing
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Simplicity of every live even Slepian band eigenvalue

Slepian--Pollak nondegeneracy has one analytic core.  Twice differentiating the sinc-kernel
eigen-equation gives a symmetric second-derivative transform.  Hence two smooth even functions
with the same live band eigenvalue have equal second-derivative pairings.  The Lagrange identity
then kills their endpoint Wronskian:

```text
f'(1) g(1) - f(1) g'(1) = 0.
```

For joint band/prolate modes, the regular-singular endpoint equation fixes
`2 f'(1) = -(chi + c^(2 : ℕ)) f(1)`, while endpoint nonvanishing makes both endpoint values nonzero.
The Wronskian identity therefore forces the two separation constants to agree.  Existing regular
ODE simplicity then shows that every nonzero even band eigenspace has dimension at most one.

This is the nondegeneracy half of the classical Slepian--Pollak no-crossing argument.  It uses no
spectral-ordering, nodal-count, asymptotic, or RH premise.
-/

open Filter MeasureTheory

noncomputable section

namespace RHTower

private theorem deriv_neg_of_even_bandSimplicity {f : ℝ → ℝ} (heven : Function.Even f)
    (hf : Differentiable ℝ f) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x :=
    (hf (-x)).hasDerivAt.comp x hneg
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  change deriv (fun y : ℝ => f (-y)) x = deriv f x at hderiv
  rw [hcomp.deriv] at hderiv
  linarith

/-- The second derivative of the entire sinc profile is even. -/
theorem deriv2_sincSmooth_even (c u : ℝ) :
    deriv (deriv (sincSmooth c)) (-u) = deriv (deriv (sincSmooth c)) u := by
  have hodd : Function.Odd (deriv (sincSmooth c)) := by
    intro x
    exact deriv_neg_of_even_bandSimplicity (fun y => sincSmooth_even c y)
      (differentiable_sincSmooth c) x
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) u := (hasDerivAt_id u).neg
  have hleft : HasDerivAt (fun y : ℝ => deriv (sincSmooth c) (-y))
      (deriv (deriv (sincSmooth c)) (-u) * (-1)) u :=
    ((differentiable_deriv_sincSmooth c) (-u)).hasDerivAt.comp u hneg
  have hright : HasDerivAt (fun y : ℝ => -deriv (sincSmooth c) y)
      (-deriv (deriv (sincSmooth c)) u) u :=
    ((differentiable_deriv_sincSmooth c) u).hasDerivAt.neg
  have heq : (fun y : ℝ => deriv (sincSmooth c) (-y)) =
      fun y : ℝ => -deriv (sincSmooth c) y := funext hodd
  have hleft' : HasDerivAt (fun y : ℝ => -deriv (sincSmooth c) y)
      (deriv (deriv (sincSmooth c)) (-u) * (-1)) u := by
    rwa [← heq]
  have huniq := hleft'.unique hright
  linarith

/-- Integral transform obtained by differentiating the Slepian kernel twice in its free
variable. -/
def bandSecondTransform (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-1 : ℝ)..1, deriv (deriv (sincSmooth c)) (x - y) * f y

/-- The twice-differentiated Slepian transform remains symmetric. -/
theorem bandSecondTransform_symmetric (c : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, bandSecondTransform c f x * g x =
      ∫ y in (-1 : ℝ)..1, f y * bandSecondTransform c g y := by
  have hK : Continuous (fun p : ℝ × ℝ => deriv (deriv (sincSmooth c)) (p.1 - p.2)) :=
    (continuous_deriv2_sincSmooth c).comp (continuous_fst.sub continuous_snd)
  have hFcont : Continuous (Function.uncurry
      (fun x y => deriv (deriv (sincSmooth c)) (x - y) * f y * g x)) :=
    (hK.mul (hf.comp continuous_snd)).mul (hg.comp continuous_fst)
  have h_int : Integrable (Function.uncurry
      (fun x y => deriv (deriv (sincSmooth c)) (x - y) * f y * g x))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod
        (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.IntegrableOn.mono_set
      (t := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ?_
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    exact hFcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (Set.Ioc (-1 : ℝ) 1))
    (f := fun x y => deriv (deriv (sincSmooth c)) (x - y) * f y * g x) h_int
  calc
    ∫ x in (-1 : ℝ)..1, bandSecondTransform c f x * g x =
        ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          deriv (deriv (sincSmooth c)) (x - y) * f y * g x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [intervalIntegral.integral_mul_const]
      simp only [bandSecondTransform]
    _ = ∫ x in (-1 : ℝ)..1, ∫ y,
          deriv (deriv (sincSmooth c)) (x - y) * f y * g x
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      intervalIntegral.integral_congr fun x _ =>
        intervalIntegral.integral_of_le (by norm_num)
    _ = ∫ y, (∫ x in (-1 : ℝ)..1,
          deriv (deriv (sincSmooth c)) (x - y) * f y * g x)
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) := hswap
    _ = ∫ y in (-1 : ℝ)..1, ∫ x in (-1 : ℝ)..1,
          deriv (deriv (sincSmooth c)) (x - y) * f y * g x :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = ∫ y in (-1 : ℝ)..1, f y * bandSecondTransform c g y := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [intervalIntegral.integral_congr
        (g := fun x => f y * (deriv (deriv (sincSmooth c)) (y - x) * g x))
          fun x _ => by
            rw [show x - y = -(y - x) by ring, deriv2_sincSmooth_even]
            ring,
        intervalIntegral.integral_const_mul]
      simp only [bandSecondTransform]

/-- Twice differentiating a smooth live band eigen-equation preserves its eigenvalue. -/
theorem bandSecondTransform_eq_eigen_secondDeriv {c lam : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hband : ∀ x, bandTransform c f x = lam * f x) (x : ℝ) :
    bandSecondTransform c f x = lam * deriv (deriv f) x := by
  have hfun : bandTransform c f = fun x => lam * f x := funext hband
  have h1 := congrArg deriv hfun
  have hmul1 : deriv (fun x => lam * f x) = fun x => lam * deriv f x := by
    funext y
    exact deriv_const_mul lam (hf y)
  rw [hmul1] at h1
  have h2 := congrArg deriv h1
  have hmul2 : deriv (fun x => lam * deriv f x) =
      fun x => lam * deriv (deriv f) x := by
    funext y
    exact deriv_const_mul lam (hf2 y)
  rw [hmul2] at h2
  unfold bandSecondTransform
  rw [← deriv2_bandTransform c hf.continuous x]
  exact congrFun h2 x

/-- Two functions carrying the same live band eigenvalue have equal second-derivative pairings. -/
theorem integral_secondDeriv_pairing_eq_of_same_bandEigenvalue
    {c lam : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x) :
    ∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x =
      ∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x := by
  have hs := bandSecondTransform_symmetric c hf.continuous hg.continuous
  have hleft : (∫ x in (-1 : ℝ)..1, bandSecondTransform c f x * g x) =
      lam * ∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandSecondTransform_eq_eigen_secondDeriv hf hf2 hfb]
    ring
  have hright : (∫ x in (-1 : ℝ)..1, f x * bandSecondTransform c g x) =
      lam * ∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandSecondTransform_eq_eigen_secondDeriv hg hg2 hgb]
    ring
  rw [hleft, hright] at hs
  exact mul_left_cancel₀ hlam hs

/-- **Same-band endpoint Wronskian law.**  Two smooth even functions with the same nonzero Slepian
band eigenvalue have zero unweighted Wronskian at the right endpoint. -/
theorem endpoint_wronskian_eq_zero_of_same_even_bandEigenvalue
    {c lam : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hf2c : Continuous (deriv (deriv f)))
    (hg2c : Continuous (deriv (deriv g)))
    (hfe : Function.Even f) (hge : Function.Even g)
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x) :
    deriv f 1 * g 1 - f 1 * deriv g 1 = 0 := by
  let W : ℝ → ℝ := fun x => deriv f x * g x - f x * deriv g x
  have hWd : ∀ x, HasDerivAt W
      (deriv (deriv f) x * g x - f x * deriv (deriv g) x) x := by
    intro x
    dsimp [W]
    have hraw := ((hf2 x).hasDerivAt.mul (hg x).hasDerivAt).sub
      ((hf x).hasDerivAt.mul (hg2 x).hasDerivAt)
    have heq :
        deriv (deriv f) x * g x + deriv f x * deriv g x -
            (deriv f x * deriv g x + f x * deriv (deriv g) x) =
          deriv (deriv f) x * g x - f x * deriv (deriv g) x := by ring
    rw [heq] at hraw
    exact hraw
  have hInt : IntervalIntegrable
      (fun x => deriv (deriv f) x * g x - f x * deriv (deriv g) x)
      volume (-1) 1 :=
    ((hf2c.mul hg.continuous).intervalIntegrable _ _).sub
      ((hf.continuous.mul hg2c).intervalIntegrable _ _)
  have hWderiv : deriv W =
      fun x => deriv (deriv f) x * g x - f x * deriv (deriv g) x :=
    funext fun x => (hWd x).deriv
  have hWInt : IntervalIntegrable (deriv W) volume (-1) 1 := by
    rw [hWderiv]
    exact hInt
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (f := W) (fun x _ => (hWd x).differentiableAt) hWInt
  have hpair := integral_secondDeriv_pairing_eq_of_same_bandEigenvalue
    hlam hf hf2 hg hg2 hfb hgb
  have hzero : (∫ x in (-1 : ℝ)..1,
      deriv (deriv f) x * g x - f x * deriv (deriv g) x) = 0 := by
    rw [intervalIntegral.integral_sub]
    linarith
    · exact (hf2c.mul hg.continuous).intervalIntegrable _ _
    · exact (hf.continuous.mul hg2c).intervalIntegrable _ _
  rw [hWderiv, hzero] at hFTC
  have hfneg := deriv_neg_of_even_bandSimplicity hfe hf 1
  have hgneg := deriv_neg_of_even_bandSimplicity hge hg 1
  have hfval := hfe 1
  have hgval := hge 1
  dsimp [W] at hFTC
  rw [hfneg, hgneg, hfval, hgval] at hFTC
  linarith

/-- Joint even prolate modes carrying one live band eigenvalue have the same separation constant. -/
theorem separation_eq_of_same_live_even_band
    {c lam chi_f chi_g : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hfsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfne : f ≠ 0) (hgne : g ≠ 0)
    (hfe : Function.Even f) (hge : Function.Even g)
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x)
    (hfp : ∀ x, prolateSLAction c f x = chi_f * f x)
    (hgp : ∀ x, prolateSLAction c g x = chi_g * g x) :
    chi_f = chi_g := by
  have hf : Differentiable ℝ f := (contDiff_infty_iff_deriv.mp hfsm).1
  have hfsm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) :=
    (contDiff_infty_iff_deriv.mp hfsm).2
  have hf2 : Differentiable ℝ (deriv f) := (contDiff_infty_iff_deriv.mp hfsm1).1
  have hf2c : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp hfsm1).2.continuous
  have hg : Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hgsm).1
  have hgsm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv g) :=
    (contDiff_infty_iff_deriv.mp hgsm).2
  have hg2 : Differentiable ℝ (deriv g) := (contDiff_infty_iff_deriv.mp hgsm1).1
  have hg2c : Continuous (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp hgsm1).2.continuous
  have hW := endpoint_wronskian_eq_zero_of_same_even_bandEigenvalue
    hlam hf hf2 hg hg2 hf2c hg2c hfe hge hfb hgb
  have hfend := two_mul_deriv_one_eq_of_prolateSLAction_eq (hfp 1)
  have hgend := two_mul_deriv_one_eq_of_prolateSLAction_eq (hgp 1)
  have hf1 : f 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen hfsm hfne hlam hfb hfp
  have hg1 : g 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen hgsm hgne hlam hgb hgp
  have hprod : f 1 * g 1 ≠ 0 := mul_ne_zero hf1 hg1
  have hgap : (chi_g - chi_f) * (f 1 * g 1) = 0 := by
    calc
      (chi_g - chi_f) * (f 1 * g 1) =
          (-(chi_f + c ^ (2 : ℕ)) * f 1) * g 1 -
            f 1 * (-(chi_g + c ^ (2 : ℕ)) * g 1) := by ring
      _ = (2 * deriv f 1) * g 1 - f 1 * (2 * deriv g 1) := by
        rw [hfend, hgend]
      _ = 2 * (deriv f 1 * g 1 - f 1 * deriv g 1) := by ring
      _ = 0 := by rw [hW]; ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hgap).resolve_right hprod)).symm

/-- **Even Slepian eigenvalue simplicity.**  At positive bandwidth, every nonzero even band
eigenvalue has multiplicity at most one. -/
theorem finrank_evenBandEigenspace_le_one
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Module.finrank ℝ (evenBandEigenspace c lam) ≤ 1 := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace_prolateBandJointSpectrum hlam
  rw [← Fin.subsingleton_iff_le_one]
  constructor
  intro i j
  apply evenBandSeparationValues_injective hc hlam
  obtain ⟨hfi, hfine, hfieven, hfiband, hfiprolate⟩ :=
    evenBandJointProfile_spec hc hlam i
  obtain ⟨hfj, hfj_ne, hfj_even, hfj_band, hfj_prolate⟩ :=
    evenBandJointProfile_spec hc hlam j
  exact separation_eq_of_same_live_even_band hlam hfi hfj hfine hfj_ne
    hfieven hfj_even hfiband hfj_band hfiprolate hfj_prolate

end RHTower

end
