import GaloisForLFunctions.RHTower.ProlateEvenBandEigenvalueSimplicity
import GaloisForLFunctions.RHTower.ProlateReflection
import GaloisForLFunctions.RHTower.ProlateSturmVariation
import GaloisForLFunctions.RHTower.ProlateL2Family
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Simplicity of every live Slepian band eigenvalue

The even-sector simplicity theorem leaves two genuine gaps before Kato continuation applies to the
full band operator: odd-sector multiplicity and a possible even/odd collision.  The first is closed
by the same twice-differentiated kernel identity as in the even sector.  The second uses a different
identity: the first derivative of the sinc kernel is odd, so its differentiated integral transform
is skew-symmetric.  For an even and an odd eigenprofile with one live band eigenvalue this forces
their endpoint-value product to vanish.  Joint prolate regularity makes both endpoint values
nonzero, ruling out the collision.

The final part combines these identities with the full finite-dimensional joint spectrum of the
commuting prolate action.  No spectral ordering, asymptotic expansion, or RH premise is used.
-/

open Filter MeasureTheory Set

noncomputable section

namespace RHTower

private theorem deriv_neg_of_even_fullBandSimplicity {f : ℝ → ℝ}
    (heven : Function.Even f) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x :=
    (hf (-x)).hasDerivAt.comp x hneg
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  change deriv (fun y : ℝ => f (-y)) x = deriv f x at hderiv
  rw [hcomp.deriv] at hderiv
  linarith

private theorem deriv_neg_of_odd_fullBandSimplicity {f : ℝ → ℝ}
    (hodd : ∀ x : ℝ, f (-x) = -f x) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv f (-x) = deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hleft : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x :=
    (hf (-x)).hasDerivAt.comp x hneg
  have hright : HasDerivAt (fun y : ℝ => -f y) (-deriv f x) x :=
    (hf x).hasDerivAt.neg
  have heq : (fun y : ℝ => f (-y)) = fun y : ℝ => -f y := funext hodd
  have hleft' : HasDerivAt (fun y : ℝ => -f y) (deriv f (-x) * (-1)) x := by
    rwa [← heq]
  have huniq := hleft'.unique hright
  linarith

/-- The first derivative of the entire sinc profile is odd. -/
theorem deriv_sincSmooth_odd (c u : ℝ) :
    deriv (sincSmooth c) (-u) = -deriv (sincSmooth c) u :=
  deriv_neg_of_even_fullBandSimplicity (fun y => sincSmooth_even c y)
    (differentiable_sincSmooth c) u

/-- Integral transform obtained by differentiating the Slepian kernel once in its free variable. -/
def bandFirstTransform (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * f y

/-- The once-differentiated Slepian transform is skew-symmetric. -/
theorem bandFirstTransform_skew (c : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, bandFirstTransform c f x * g x =
      -∫ y in (-1 : ℝ)..1, f y * bandFirstTransform c g y := by
  have hK : Continuous (fun p : ℝ × ℝ => deriv (sincSmooth c) (p.1 - p.2)) :=
    (contDiff_deriv_sincSmooth c).continuous.comp (continuous_fst.sub continuous_snd)
  have hFcont : Continuous (Function.uncurry
      (fun x y => deriv (sincSmooth c) (x - y) * f y * g x)) :=
    (hK.mul (hf.comp continuous_snd)).mul (hg.comp continuous_fst)
  have h_int : Integrable (Function.uncurry
      (fun x y => deriv (sincSmooth c) (x - y) * f y * g x))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod
        (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.IntegrableOn.mono_set
      (t := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ?_
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    exact hFcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (Set.Ioc (-1 : ℝ) 1))
    (f := fun x y => deriv (sincSmooth c) (x - y) * f y * g x) h_int
  calc
    ∫ x in (-1 : ℝ)..1, bandFirstTransform c f x * g x =
        ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          deriv (sincSmooth c) (x - y) * f y * g x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [intervalIntegral.integral_mul_const]
      simp only [bandFirstTransform]
    _ = ∫ x in (-1 : ℝ)..1, ∫ y,
          deriv (sincSmooth c) (x - y) * f y * g x
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      intervalIntegral.integral_congr fun x _ =>
        intervalIntegral.integral_of_le (by norm_num)
    _ = ∫ y, (∫ x in (-1 : ℝ)..1,
          deriv (sincSmooth c) (x - y) * f y * g x)
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) := hswap
    _ = ∫ y in (-1 : ℝ)..1, ∫ x in (-1 : ℝ)..1,
          deriv (sincSmooth c) (x - y) * f y * g x :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = ∫ y in (-1 : ℝ)..1, -(f y * bandFirstTransform c g y) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [intervalIntegral.integral_congr
        (g := fun x => -(f y * (deriv (sincSmooth c) (y - x) * g x)))
          fun x _ => by
            rw [show x - y = -(y - x) by ring, deriv_sincSmooth_odd]
            ring,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      simp only [bandFirstTransform]
    _ = -∫ y in (-1 : ℝ)..1, f y * bandFirstTransform c g y := by
      rw [intervalIntegral.integral_neg]

/-- Differentiating a smooth live band eigen-equation preserves its eigenvalue. -/
theorem bandFirstTransform_eq_eigen_deriv {c lam : ℝ} {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hband : ∀ x, bandTransform c f x = lam * f x) (x : ℝ) :
    bandFirstTransform c f x = lam * deriv f x := by
  have hfun : bandTransform c f = fun x => lam * f x := funext hband
  have h1 := congrArg deriv hfun
  have hmul : deriv (fun x => lam * f x) = fun x => lam * deriv f x := by
    funext y
    exact deriv_const_mul lam (hf y)
  rw [hmul] at h1
  unfold bandFirstTransform
  calc
    (∫ y in (-1 : ℝ)..1, deriv (sincSmooth c) (x - y) * f y) =
        deriv (bandTransform c f) x :=
      (congrFun (deriv_bandTransform c hf.continuous) x).symm
    _ = lam * deriv f x := congrFun h1 x

/-- Same live band eigenvalue gives the skew first-derivative pairing identity. -/
theorem integral_deriv_pairing_neg_of_same_bandEigenvalue
    {c lam : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x) :
    ∫ x in (-1 : ℝ)..1, deriv f x * g x =
      -∫ x in (-1 : ℝ)..1, f x * deriv g x := by
  have hs := bandFirstTransform_skew c hf.continuous hg.continuous
  have hleft : (∫ x in (-1 : ℝ)..1, bandFirstTransform c f x * g x) =
      lam * ∫ x in (-1 : ℝ)..1, deriv f x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandFirstTransform_eq_eigen_deriv hf hfb]
    ring
  have hright : (∫ x in (-1 : ℝ)..1, f x * bandFirstTransform c g x) =
      lam * ∫ x in (-1 : ℝ)..1, f x * deriv g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandFirstTransform_eq_eigen_deriv hg hgb]
    ring
  rw [hleft, hright] at hs
  apply mul_left_cancel₀ hlam
  calc
    lam * (∫ x in (-1 : ℝ)..1, deriv f x * g x) =
        -(lam * ∫ x in (-1 : ℝ)..1, f x * deriv g x) := hs
    _ = lam * (-∫ x in (-1 : ℝ)..1, f x * deriv g x) := by ring

/-- An even and an odd live band eigenprofile cannot both have nonzero right endpoint value. -/
theorem endpoint_product_eq_zero_of_same_even_odd_bandEigenvalue
    {c lam : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfd : Continuous (deriv f)) (hgd : Continuous (deriv g))
    (hfe : Function.Even f) (hgo : ∀ x : ℝ, g (-x) = -g x)
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x) :
    f 1 * g 1 = 0 := by
  let P : ℝ → ℝ := fun x => f x * g x
  have hPd : ∀ x, HasDerivAt P (deriv f x * g x + f x * deriv g x) x := by
    intro x
    exact (hf x).hasDerivAt.mul (hg x).hasDerivAt
  have hPderiv : deriv P = fun x => deriv f x * g x + f x * deriv g x :=
    funext fun x => (hPd x).deriv
  have hIntLeft : IntervalIntegrable (fun x => deriv f x * g x) volume (-1) 1 :=
    (hfd.mul hg.continuous).intervalIntegrable _ _
  have hIntRight : IntervalIntegrable (fun x => f x * deriv g x) volume (-1) 1 :=
    (hf.continuous.mul hgd).intervalIntegrable _ _
  have hPInt : IntervalIntegrable (deriv P) volume (-1) 1 := by
    rw [hPderiv]
    exact hIntLeft.add hIntRight
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (f := P) (fun x _ => (hPd x).differentiableAt) hPInt
  have hpair := integral_deriv_pairing_neg_of_same_bandEigenvalue
    hlam hf hg hfb hgb
  have hzero : (∫ x in (-1 : ℝ)..1,
      deriv f x * g x + f x * deriv g x) = 0 := by
    rw [intervalIntegral.integral_add hIntLeft hIntRight, hpair]
    ring
  rw [hPderiv, hzero] at hFTC
  have hfval := hfe 1
  have hgval := hgo 1
  dsimp [P] at hFTC
  rw [hfval, hgval] at hFTC
  linarith

/-- Opposite-parity nonzero joint prolate modes cannot carry one live band eigenvalue. -/
theorem not_same_live_band_of_even_odd_joint_prolate
    {c lam chi_f chi_g : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hfsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfne : f ≠ 0) (hgne : g ≠ 0)
    (hfe : Function.Even f) (hgo : ∀ x : ℝ, g (-x) = -g x)
    (hfb : ∀ x, bandTransform c f x = lam * f x)
    (hgb : ∀ x, bandTransform c g x = lam * g x)
    (hfp : ∀ x, prolateSLAction c f x = chi_f * f x)
    (hgp : ∀ x, prolateSLAction c g x = chi_g * g x) : False := by
  have hprod := endpoint_product_eq_zero_of_same_even_odd_bandEigenvalue
    hlam (contDiff_infty_iff_deriv.mp hfsm).1 (contDiff_infty_iff_deriv.mp hgsm).1
      (contDiff_infty_iff_deriv.mp hfsm).2.continuous
      (contDiff_infty_iff_deriv.mp hgsm).2.continuous hfe hgo hfb hgb
  have hf1 : f 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen hfsm hfne hlam hfb hfp
  have hg1 : g 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen hgsm hgne hlam hgb hgp
  exact (mul_ne_zero hf1 hg1) hprod

/-- Same-band endpoint Wronskian law in the odd sector. -/
theorem endpoint_wronskian_eq_zero_of_same_odd_bandEigenvalue
    {c lam : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hf2c : Continuous (deriv (deriv f)))
    (hg2c : Continuous (deriv (deriv g)))
    (hfo : ∀ x : ℝ, f (-x) = -f x) (hgo : ∀ x : ℝ, g (-x) = -g x)
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
  have hfneg := deriv_neg_of_odd_fullBandSimplicity hfo hf 1
  have hgneg := deriv_neg_of_odd_fullBandSimplicity hgo hg 1
  have hfval := hfo 1
  have hgval := hgo 1
  dsimp [W] at hFTC
  rw [hfneg, hgneg, hfval, hgval] at hFTC
  linarith

/-- Joint odd prolate modes carrying one live band eigenvalue have the same separation constant. -/
theorem separation_eq_of_same_live_odd_band
    {c lam chi_f chi_g : ℝ} {f g : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hfsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfne : f ≠ 0) (hgne : g ≠ 0)
    (hfo : ∀ x : ℝ, f (-x) = -f x) (hgo : ∀ x : ℝ, g (-x) = -g x)
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
  have hW := endpoint_wronskian_eq_zero_of_same_odd_bandEigenvalue
    hlam hf hf2 hg hg2 hf2c hg2c hfo hgo hfb hgb
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

/-! ## Full regular separation simplicity -/

/-- A nonzero live joint mode has nontrivial Cauchy data at the symmetry center. -/
theorem value_zero_ne_or_deriv_zero_ne_of_joint_prolate_band_eigen
    {c lam chi : ℝ} {Psi : ℝ → ℝ}
    (hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (hPsiNe : Psi ≠ 0) (hlam : lam ≠ 0)
    (hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lam * Psi x)
    (hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x) :
    Psi 0 ≠ 0 ∨ deriv Psi 0 ≠ 0 := by
  by_contra hcenter
  push Not at hcenter
  have hPsi1 : Differentiable ℝ Psi := (contDiff_infty_iff_deriv.mp hPsiSmooth).1
  have hPsi2 : Differentiable ℝ (deriv Psi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPsiSmooth).2).1
  have hzeroProlate : ∀ x : ℝ,
      prolateSLAction c (fun _ : ℝ => 0) x = chi * (fun _ : ℝ => 0) x := by
    intro x
    simp [prolateSLAction]
  have hzeroIoo : Set.EqOn Psi (fun _ : ℝ => 0) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hPsi1 hPsi2 (by fun_prop) (by fun_prop) hPsiProlate hzeroProlate
      (by simpa using hcenter.1) (by simpa using hcenter.2)
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hzeroIcc : Set.EqOn Psi (fun _ : ℝ => 0) (Set.Icc (-1 : ℝ) 1) := by
    rw [hclosure]
    exact hzeroIoo.closure hPsi1.continuous continuous_const
  have hBandZero : ∀ x : ℝ, bandTransform c Psi x = 0 := by
    intro x
    unfold bandTransform
    calc
      (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * Psi y) =
          ∫ _y in (-1 : ℝ)..1, 0 := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
            have hyzero : Psi y = 0 := by simpa using hzeroIcc hy'
            simp [hyzero]
      _ = 0 := by simp
  apply hPsiNe
  funext x
  have hxzero : lam * Psi x = 0 := by rw [← hPsiBand x, hBandZero x]
  exact (mul_eq_zero.mp hxzero).resolve_left hlam

/-- Any two smooth joint modes with one separation value are proportional on the aperture; no
parity assumption is needed. -/
theorem eqOn_Icc_const_mul_of_joint_prolate_eigen
    {c lamPsi chi : ℝ} {Phi Psi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (hPsiNe : Psi ≠ 0) (hlamPsi : lamPsi ≠ 0)
    (hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lamPsi * Psi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x) :
    ∃ mu : ℝ, Set.EqOn Phi (fun x => mu * Psi x) (Set.Icc (-1 : ℝ) 1) := by
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPhiSmooth).2).1
  have hPsi1 : Differentiable ℝ Psi := (contDiff_infty_iff_deriv.mp hPsiSmooth).1
  have hPsi2 : Differentiable ℝ (deriv Psi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPsiSmooth).2).1
  have hcenter := value_zero_ne_or_deriv_zero_ne_of_joint_prolate_band_eigen
    hPsiSmooth hPsiNe hlamPsi hPsiBand hPsiProlate
  have hW := prolateSturmWronskian_eq_zero
    hPhi1 hPhi2 hPsi1 hPsi2 hPhiProlate hPsiProlate 0
  norm_num at hW
  obtain ⟨mu, hvalue, hderiv⟩ : ∃ mu : ℝ,
      Phi 0 = mu * Psi 0 ∧ deriv Phi 0 = mu * deriv Psi 0 := by
    by_cases hPsi0 : Psi 0 = 0
    · have hPsiD0 : deriv Psi 0 ≠ 0 := by
        rcases hcenter with hne | hne
        · exact False.elim (hne hPsi0)
        · exact hne
      have hPhi0 : Phi 0 = 0 := by
        have hmul : Phi 0 * deriv Psi 0 = 0 := by
          rw [hPsi0] at hW
          linarith
        exact (mul_eq_zero.mp hmul).resolve_right hPsiD0
      refine ⟨deriv Phi 0 / deriv Psi 0, ?_, ?_⟩
      · rw [hPhi0, hPsi0]
        ring
      · field_simp
    · refine ⟨Phi 0 / Psi 0, ?_, ?_⟩
      · field_simp
      · field_simp
        linarith [hW]
  have hscaled1 : Differentiable ℝ (fun x => mu * Psi x) := by fun_prop
  have hscaledDeriv : deriv (fun x => mu * Psi x) = fun x => mu * deriv Psi x := by
    funext x
    exact deriv_const_mul mu (hPsi1 x)
  have hscaled2 : Differentiable ℝ (deriv (fun x => mu * Psi x)) := by
    rw [hscaledDeriv]
    fun_prop
  have hscaledProlate : ∀ x : ℝ,
      prolateSLAction c (fun y => mu * Psi y) x = chi * (mu * Psi x) := by
    intro x
    rw [GaloisForLFunctions.RHTower.prolateSLAction_const_mul mu hPsi1 hPsi2 x,
      hPsiProlate x]
    ring
  have hEqIoo : Set.EqOn Phi (fun x => mu * Psi x) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hPhi1 hPhi2 hscaled1 hscaled2 hPhiProlate hscaledProlate hvalue
      (by rw [hscaledDeriv]; exact hderiv)
  refine ⟨mu, ?_⟩
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [hclosure]
  exact hEqIoo.closure hPhi1.continuous hscaled1.continuous

/-- With one live band eigenvalue as well, aperture proportionality propagates globally. -/
theorem eq_const_mul_of_same_joint_prolate_eigen
    {c lam chi : ℝ} {Phi Psi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (hPsiNe : Psi ≠ 0) (hlam : lam ≠ 0)
    (hPhiBand : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lam * Psi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x) :
    ∃ mu : ℝ, Phi = fun x => mu * Psi x := by
  obtain ⟨mu, hEq⟩ := eqOn_Icc_const_mul_of_joint_prolate_eigen
    hPhiSmooth hPsiSmooth hPsiNe hlam hPsiBand hPhiProlate hPsiProlate
  have hBandProp : ∀ x : ℝ, bandTransform c Phi x = mu * bandTransform c Psi x := by
    intro x
    rw [bandTransform, bandTransform, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
    change sincKernelSmooth c x y * Phi y =
      mu * (sincKernelSmooth c x y * Psi y)
    rw [hEq hyIcc]
    ring
  refine ⟨mu, funext fun x => ?_⟩
  apply mul_left_cancel₀ hlam
  calc
    lam * Phi x = bandTransform c Phi x := (hPhiBand x).symm
    _ = mu * bandTransform c Psi x := hBandProp x
    _ = mu * (lam * Psi x) := by rw [hPsiBand x]
    _ = lam * (mu * Psi x) := by ring

/-- Eigenvectors of the full prolate action with one separation value are proportional. -/
theorem prolateOnEigenspace_eigenvectors_proportional
    {c lam chi : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {f g : GaloisForLFunctions.RHTower.bandEigenspace c lam}
    (hf : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam f = chi • f)
    (hg : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam g = chi • g)
    (hg0 : g ≠ 0) :
    ∃ mu : ℝ, f = mu • g := by
  let Phi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam f
  let Psi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam g
  have hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x := by
    have hrep := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hf
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (chi • f) x =
        chi * GaloisForLFunctions.RHTower.eigenRep c lam f x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam chi f x
    rw [hsmul] at hx
    exact hx
  have hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x := by
    have hrep := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hg
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (chi • g) x =
        chi * GaloisForLFunctions.RHTower.eigenRep c lam g x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam chi g x
    rw [hsmul] at hx
    exact hx
  have hPsiNe : Psi ≠ 0 := by
    intro hzero
    have hclassZero : GaloisForLFunctions.RHTower.bandClass Psi
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam g) = 0 := by
      have hstep := GaloisForLFunctions.RHTower.bandClass_congr
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam g)
        continuous_const hzero
      rw [hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    apply hg0
    apply Subtype.ext
    rw [← GaloisForLFunctions.RHTower.bandClass_eigenRep hlam g]
    exact hclassZero
  obtain ⟨mu, hEq⟩ := eqOn_Icc_const_mul_of_joint_prolate_eigen
    (GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam f)
    (GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam g)
    hPsiNe hlam (GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam g)
    hPhiProlate hPsiProlate
  have hscaled : Continuous (fun x : ℝ => mu * Psi x) :=
    continuous_const.mul (GaloisForLFunctions.RHTower.continuous_eigenRep c lam g)
  have hclassEq : GaloisForLFunctions.RHTower.bandClass Phi
      (GaloisForLFunctions.RHTower.continuous_eigenRep c lam f) =
      GaloisForLFunctions.RHTower.bandClass (fun x => mu * Psi x) hscaled :=
    bandClass_eq_of_eqOn_Icc
      (GaloisForLFunctions.RHTower.continuous_eigenRep c lam f) hscaled hEq
  have hval : f.1 = mu • g.1 := by
    calc
      f.1 = GaloisForLFunctions.RHTower.bandClass Phi
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam f) :=
        (GaloisForLFunctions.RHTower.bandClass_eigenRep hlam f).symm
      _ = GaloisForLFunctions.RHTower.bandClass (fun x => mu * Psi x) hscaled := hclassEq
      _ = mu • GaloisForLFunctions.RHTower.bandClass Psi
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam g) :=
        GaloisForLFunctions.RHTower.bandClass_smul
          (GaloisForLFunctions.RHTower.continuous_eigenRep c lam g) mu hscaled
      _ = mu • g.1 := by
        rw [GaloisForLFunctions.RHTower.bandClass_eigenRep hlam g]
  exact ⟨mu, Subtype.ext hval⟩

/-- Every separation eigenspace of the full prolate action inside a live band eigenspace has
dimension at most one. -/
theorem finrank_prolateOnEigenspace_eigenspace_le_one
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) (chi : ℝ) :
    Module.finrank ℝ
      (Module.End.eigenspace
        (GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam) chi) ≤ 1 := by
  classical
  let E := Module.End.eigenspace
    (GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam) chi
  by_cases hne : ∃ g : E, g ≠ 0
  · obtain ⟨g, hg0⟩ := hne
    apply finrank_le_one g
    intro f
    have hfEig : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam f.1 =
        chi • f.1 := Module.End.mem_eigenspace_iff.mp f.2
    have hgEig : GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam g.1 =
        chi • g.1 := Module.End.mem_eigenspace_iff.mp g.2
    have hg0' : (g.1 : GaloisForLFunctions.RHTower.bandEigenspace c lam) ≠ 0 := by
      intro h
      exact hg0 (Subtype.ext h)
    obtain ⟨mu, hfg⟩ :=
      prolateOnEigenspace_eigenvectors_proportional hc hlam hfEig hgEig hg0'
    exact ⟨mu, Subtype.ext hfg.symm⟩
  · push Not at hne
    apply finrank_le_one (0 : E)
    intro f
    refine ⟨0, ?_⟩
    simp [hne f]

/-! ## Parity and the full joint spectrum -/

/-- Every nonzero smooth global joint mode is either even or odd.  This is forced by regular
separation simplicity: reflection is another mode with the same band and separation eigenvalues,
so it is a scalar multiple; applying reflection twice makes that scalar `±1`. -/
theorem joint_prolate_even_or_odd
    {c lam chi : ℝ} {Phi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPhiNe : Phi ≠ 0) (hlam : lam ≠ 0)
    (hPhiBand : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    Function.Even Phi ∨ ∀ x : ℝ, Phi (-x) = -Phi x := by
  let Psi : ℝ → ℝ := fun x => Phi (-x)
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPhiSmooth).2).1
  have hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi := by
    dsimp [Psi]
    exact hPhiSmooth.comp contDiff_neg
  have hPsiNe : Psi ≠ 0 := by
    intro hzero
    apply hPhiNe
    funext x
    have hx := congrFun hzero (-x)
    simpa [Psi] using hx
  have hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lam * Psi x := by
    intro x
    exact bandTransform_eigen_comp_neg hPhiBand x
  have hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x := by
    intro x
    exact prolateSLAction_eigen_comp_neg hPhi1 hPhi2 hPhiProlate x
  obtain ⟨mu, hEq⟩ := eq_const_mul_of_same_joint_prolate_eigen
    hPhiSmooth hPsiSmooth hPsiNe hlam hPhiBand hPsiBand hPhiProlate hPsiProlate
  have hEqOne := congrFun hEq 1
  have hEqNegOne := congrFun hEq (-1)
  dsimp [Psi] at hEqOne hEqNegOne
  rw [neg_neg] at hEqNegOne
  have hPhiOne : Phi 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen
      hPhiSmooth hPhiNe hlam hPhiBand hPhiProlate
  have hEqCycle : Phi 1 = mu ^ (2 : ℕ) * Phi 1 := by
    calc
      Phi 1 = mu * Phi (-1) := hEqOne
      _ = mu * (mu * Phi 1) := by rw [hEqNegOne]
      _ = mu ^ (2 : ℕ) * Phi 1 := by ring
  have hsqProd : (mu ^ (2 : ℕ) - 1) * Phi 1 = 0 := by
    linarith [hEqCycle]
  have hmuSq : mu ^ (2 : ℕ) = 1 := by
    rcases mul_eq_zero.mp hsqProd with h | h
    · linarith
    · exact False.elim (hPhiOne h)
  rcases sq_eq_one_iff.mp hmuSq with hmu | hmu
  · left
    intro x
    have hx := congrFun hEq (-x)
    dsimp [Psi] at hx
    rw [neg_neg, hmu] at hx
    simpa using hx
  · right
    intro x
    have hx := congrFun hEq (-x)
    dsimp [Psi] at hx
    rw [neg_neg, hmu] at hx
    simpa using hx

/-- Ordered separation values carried by the full live band eigenspace. -/
noncomputable def bandSeparationValues
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Fin (Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam)) → ℝ := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  exact (GaloisForLFunctions.RHTower.isSymmetric_prolateOnEigenspace hc hlam).eigenvalues rfl

/-- Canonical orthonormal joint-eigenvector basis of the full live band eigenspace. -/
noncomputable def bandJointEigenbasis
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam))) ℝ
      (GaloisForLFunctions.RHTower.bandEigenspace c lam) := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  exact
    (GaloisForLFunctions.RHTower.isSymmetric_prolateOnEigenspace hc hlam).eigenvectorBasis rfl

/-- Each canonical basis vector carries its indexed separation value. -/
theorem prolateOnEigenspace_bandJointEigenbasis
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam))) :
    GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam (bandJointEigenbasis hc hlam i) =
      bandSeparationValues hc hlam i • bandJointEigenbasis hc hlam i := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  exact (GaloisForLFunctions.RHTower.isSymmetric_prolateOnEigenspace hc hlam).apply_eigenvectorBasis
    rfl i

/-- Full regular ODE simplicity makes the ordered separation list injective. -/
theorem bandSeparationValues_injective
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Function.Injective (bandSeparationValues hc hlam) := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let A := GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam
  let hA := GaloisForLFunctions.RHTower.isSymmetric_prolateOnEigenspace hc hlam
  intro i j hij
  have hcard :
      Finset.card {k | hA.eigenvalues rfl k = hA.eigenvalues rfl i} ≤ 1 := by
    have heq := hA.card_filter_eigenvalues_eq rfl (hA.eigenvalues rfl i)
    exact (le_of_eq heq).trans
      (finrank_prolateOnEigenspace_eigenspace_le_one
        hc hlam (hA.eigenvalues rfl i))
  apply Finset.card_le_one.mp hcard i
  · simp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change bandSeparationValues hc hlam j = bandSeparationValues hc hlam i
    exact hij.symm

/-- Smooth global representative of one canonical full joint separation line. -/
noncomputable def bandJointProfile
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam))) :
    ℝ → ℝ :=
  GaloisForLFunctions.RHTower.eigenRep c lam (bandJointEigenbasis hc hlam i)

/-- The canonical full joint profile is smooth, nonzero, and solves both eigenvalue equations. -/
theorem bandJointProfile_spec
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (i : Fin (Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bandJointProfile hc hlam i) ∧
      bandJointProfile hc hlam i ≠ 0 ∧
      (∀ x : ℝ, bandTransform c (bandJointProfile hc hlam i) x =
        lam * bandJointProfile hc hlam i x) ∧
      ∀ x : ℝ, prolateSLAction c (bandJointProfile hc hlam i) x =
        bandSeparationValues hc hlam i * bandJointProfile hc hlam i x := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let v : GaloisForLFunctions.RHTower.bandEigenspace c lam := bandJointEigenbasis hc hlam i
  let Phi : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam v
  have hvne : v ≠ 0 := (bandJointEigenbasis hc hlam).orthonormal.ne_zero i
  have hPhiNe : Phi ≠ 0 := by
    intro hzero
    have hclassZero : GaloisForLFunctions.RHTower.bandClass Phi
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam v) = 0 := by
      have hstep := GaloisForLFunctions.RHTower.bandClass_congr
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam v)
        continuous_const hzero
      rw [hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    apply hvne
    apply Subtype.ext
    rw [← GaloisForLFunctions.RHTower.bandClass_eigenRep hlam v]
    exact hclassZero
  have hrestricted := prolateOnEigenspace_bandJointEigenbasis hc hlam i
  have hrep := congrArg
    (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
      GaloisForLFunctions.RHTower.eigenRep c lam w) hrestricted
  rw [eigenRep_prolateOnEigenspace hc hlam] at hrep
  have hprolate : ∀ x : ℝ, prolateSLAction c Phi x =
      bandSeparationValues hc hlam i * Phi x := by
    intro x
    have hx := congrFun hrep x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam
        (bandSeparationValues hc hlam i • v) x =
          bandSeparationValues hc hlam i * GaloisForLFunctions.RHTower.eigenRep c lam v x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam
        (bandSeparationValues hc hlam i) v x
    rw [hsmul] at hx
    exact hx
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧
    (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
      ∀ x : ℝ, prolateSLAction c Phi x = bandSeparationValues hc hlam i * Phi x
  exact ⟨GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam v, hPhiNe,
    GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam v, hprolate⟩

/-- **Full Slepian eigenvalue simplicity.**  At positive bandwidth, every nonzero eigenvalue of
the real band operator has multiplicity at most one. -/
theorem finrank_bandEigenspace_le_one
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    Module.finrank ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) ≤ 1 := by
  letI : FiniteDimensional ℝ (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  rw [← Fin.subsingleton_iff_le_one]
  constructor
  intro i j
  apply bandSeparationValues_injective hc hlam
  obtain ⟨hfi, hfine, hfiband, hfiprolate⟩ := bandJointProfile_spec hc hlam i
  obtain ⟨hfj, hfjNe, hfjband, hfjprolate⟩ := bandJointProfile_spec hc hlam j
  have hpi := joint_prolate_even_or_odd hfi hfine hlam hfiband hfiprolate
  have hpj := joint_prolate_even_or_odd hfj hfjNe hlam hfjband hfjprolate
  rcases hpi with hfieven | hfiodd <;> rcases hpj with hfjeven | hfjodd
  · exact separation_eq_of_same_live_even_band hlam hfi hfj hfine hfjNe
      hfieven hfjeven hfiband hfjband hfiprolate hfjprolate
  · exact False.elim (not_same_live_band_of_even_odd_joint_prolate
      hlam hfi hfj hfine hfjNe hfieven hfjodd hfiband hfjband hfiprolate hfjprolate)
  · exact False.elim (not_same_live_band_of_even_odd_joint_prolate
      hlam hfj hfi hfjNe hfine hfjeven hfiodd hfjband hfiband hfjprolate hfiprolate)
  · exact separation_eq_of_same_live_odd_band hlam hfi hfj hfine hfjNe
      hfiodd hfjodd hfiband hfjband hfiprolate hfjprolate

/-! ## Unconditional local continuation -/

/-- A normalized generator is a scalar generator of its full live band eigenspace. -/
theorem bandOperatorL2_eigenvectors_proportional
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {psi phi : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hpsi : GaloisForLFunctions.RHTower.bandOperatorL2 c psi = lam • psi)
    (hpsiNe : psi ≠ 0)
    (hphi : GaloisForLFunctions.RHTower.bandOperatorL2 c phi = lam • phi) :
    ∃ s : ℝ, phi = s • psi := by
  let E := GaloisForLFunctions.RHTower.bandEigenspace c lam
  letI : FiniteDimensional ℝ E :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let epsi : E := ⟨psi, GaloisForLFunctions.RHTower.mem_bandEigenspace_iff.mpr hpsi⟩
  let ephi : E := ⟨phi, GaloisForLFunctions.RHTower.mem_bandEigenspace_iff.mpr hphi⟩
  have hepsiNe : epsi ≠ 0 := by
    intro hzero
    apply hpsiNe
    exact congrArg Subtype.val hzero
  have hspanFin : Module.finrank ℝ (ℝ ∙ epsi) = 1 := finrank_span_singleton hepsiNe
  have hEFin : Module.finrank ℝ E = 1 := by
    apply le_antisymm (finrank_bandEigenspace_le_one hc hlam)
    rw [← hspanFin]
    have hmono := Submodule.finrank_mono
      (show ℝ ∙ epsi ≤ (⊤ : Submodule ℝ E) from le_top)
    simpa only [finrank_top] using hmono
  have hspanTop : ℝ ∙ epsi = (⊤ : Submodule ℝ E) := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspanFin, hEFin]
  have hephiMem : ephi ∈ (ℝ ∙ epsi) := by
    rw [hspanTop]
    exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hephiMem
  exact ⟨s, (congrArg Subtype.val hs).symm⟩

/-- The existing Kato/Fredholm branch theorem is unconditional at every positive aperture and
every normalized live band eigenpair. -/
theorem exists_bandOperatorL2_branch_of_pos
    {c₀ ν₀ : ℝ}
    {ψ₀ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hc₀ : 0 < c₀)
    (heig : GaloisForLFunctions.RHTower.bandOperatorL2 c₀ ψ₀ = ν₀ • ψ₀)
    (hnorm : (inner ℝ ψ₀ ψ₀ : ℝ) = 1) (hnu₀ : ν₀ ≠ 0) :
    ∃ (ψ : ℝ → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
        (ν : ℝ → ℝ),
      ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in nhds c₀,
        GaloisForLFunctions.RHTower.bandOperatorL2 c (ψ c) = ν c • ψ c ∧
          (inner ℝ (ψ c) (ψ c) : ℝ) = 1) ∧
      HasDerivAt ν
        (inner ℝ ψ₀ (GaloisForLFunctions.RHTower.cosOperatorL2 c₀ ψ₀)) c₀ := by
  have hpsiNe : ψ₀ ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    simpa using hnorm
  apply GaloisForLFunctions.RHTower.exists_bandOperatorL2_branch heig hnorm hnu₀
  intro phi hphi
  exact bandOperatorL2_eigenvectors_proportional hc₀ hnu₀ heig hpsiNe hphi

end RHTower

end
