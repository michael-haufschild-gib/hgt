import GaloisForLFunctions.HTGeometry.CoshFourierTransform
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import GaloisForLFunctions.RHTower.ConnesLinearFourier
import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic
import GaloisForLFunctions.HTGeometry.BesselOrderIntegral
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellinSum

/-!
# Exact complex two-Bessel Mellin product for the HB Rankin--Selberg gate

This file closes C-A.9x-b in the actual completed-Eisenstein normalization route.  On the sharp
absolute-convergence chamber `|Re mu| + |Re nu| < Re s`, it proves

```text
integral_0^infinity x^(s-1) K_mu(x) K_nu(x) dx
  = 2^(s-3) / Gamma(s)
      * Gamma((s+mu+nu)/2) * Gamma((s+mu-nu)/2)
      * Gamma((s-mu+nu)/2) * Gamma((s-mu-nu)/2).
```

The proof is source-level and unconditional.  It first upgrades the corpus Fourier-only
hyperbolic transform to the full complex logistic/Beta transform, separates the resulting plane
kernel by the determinant-two map `(p,q) |-> (p+q,p-q)`, proves a whole-line exponential
Schlaefli representation of `modifiedBesselKOrder`, and closes the three-variable Fubini gate by
an exact integral of the norm.  No meromorphic continuation or unproved interchange is used.

Exact RH chain served:
`actual meromorphic scalar triple regularization -> classical four-Lambda family ->
normalization mismatch with canonical four-Xi vertex -> kill unmodified HB scalar landing`.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

noncomputable section

private theorem complexBetaIntegrand_logisticVar {s a : ℂ} (t : ℝ) :
    ((HTGeometry.logisticVar t : ℝ) : ℂ) ^ (((s + a) / 2) - 1) *
        ((1 : ℂ) - ((HTGeometry.logisticVar t : ℝ) : ℂ)) ^ (((s - a) / 2) - 1)
      = Complex.exp (a * (t : ℂ)) *
        ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - s) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
  have hv : (0 : ℝ) < HTGeometry.logisticVar t := HTGeometry.logisticVar_pos t
  have hv' : (0 : ℝ) < 1 - HTGeometry.logisticVar t :=
    HTGeometry.one_sub_logisticVar_pos t
  have hcast : (1 : ℂ) - ((HTGeometry.logisticVar t : ℝ) : ℂ) =
      ((1 - HTGeometry.logisticVar t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, HTGeometry.ofReal_cpow_eq_exp hv, HTGeometry.ofReal_cpow_eq_exp hv',
    HTGeometry.ofReal_cpow_eq_exp h2c, ← Complex.exp_add,
    HTGeometry.log_logisticVar, HTGeometry.log_one_sub_logisticVar]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem complexHyperbolicBeta_jacobian {s a : ℂ} (t : ℝ) :
    |1 / (2 * Real.cosh t ^ 2)| •
        (((HTGeometry.logisticVar t : ℝ) : ℂ) ^ (((s + a) / 2) - 1) *
          ((1 : ℂ) - ((HTGeometry.logisticVar t : ℝ) : ℂ)) ^ (((s - a) / 2) - 1))
      = (2 : ℂ) ^ (1 - s) *
          (((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.exp (a * (t : ℂ))) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
  have hcC : ((Real.cosh t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [complexBetaIntegrand_logisticVar, abs_of_pos (by positivity), Complex.real_smul]
  have hsplit : ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - s)
      = (2 : ℂ) ^ ((2 : ℂ) - s) * ((Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - s) := by
    convert Complex.mul_cpow_ofReal_nonneg
      (show (0 : ℝ) ≤ 2 by norm_num) hc.le ((2 : ℂ) - s) using 1 <;> norm_num
  rw [hsplit]
  have htwo : (2 : ℂ) ^ ((2 : ℂ) - s) = (2 : ℂ) ^ (1 - s) * 2 := by
    rw [show (2 : ℂ) - s = (1 - s) + 1 by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  have hcosh : ((Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - s) =
      ((Real.cosh t : ℝ) : ℂ) ^ (-s) * ((Real.cosh t : ℝ) : ℂ) ^ 2 := by
    calc
      ((Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - s) =
          ((Real.cosh t : ℝ) : ℂ) ^ (-s + (2 : ℂ)) := by ring_nf
      _ = ((Real.cosh t : ℝ) : ℂ) ^ (-s) *
          ((Real.cosh t : ℝ) : ℂ) ^ (2 : ℂ) :=
        Complex.cpow_add (-s) (2 : ℂ) hcC
      _ = ((Real.cosh t : ℝ) : ℂ) ^ (-s) *
          ((Real.cosh t : ℝ) : ℂ) ^ (2 : ℕ) := by
        congr 1
        exact Complex.cpow_natCast _ 2
  rw [htwo, hcosh]
  push_cast
  have hcC' : Complex.cosh (t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact hcC
  field_simp [hcC']

/-- Absolute convergence of the full complex hyperbolic Beta kernel. -/
theorem integrable_complex_cosh_cpow_neg_mul_exp {s a : ℂ}
    (hchamber : |a.re| < s.re) :
    Integrable (fun t : ℝ =>
      ((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.exp (a * (t : ℂ))) := by
  let d : ℝ := s.re - |a.re|
  have hd : 0 < d := by simp only [d]; linarith
  have hmajor : Integrable (fun t : ℝ =>
      2 ^ s.re * Real.exp (-(d * |t|))) :=
    (RHTower.integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hd).const_mul (2 ^ s.re)
  refine Integrable.mono' hmajor ?_ ?_
  · fun_prop
  · refine ae_of_all _ fun t => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t),
      Complex.neg_re, Complex.norm_exp]
    have hexpre : (a * (t : ℂ)).re = a.re * t := by simp
    rw [hexpre]
    have hcosh := HTGeometry.cosh_rpow_neg_le (show 0 ≤ s.re by
      exact le_trans (abs_nonneg a.re) hchamber.le) t
    have hat : a.re * t ≤ |a.re| * |t| := by
      calc
        a.re * t ≤ |a.re * t| := le_abs_self _
        _ = |a.re| * |t| := abs_mul _ _
    have hexp : Real.exp (a.re * t) ≤ Real.exp (|a.re| * |t|) :=
      Real.exp_le_exp.mpr hat
    calc
      (Real.cosh t) ^ (-s.re) * Real.exp (a.re * t)
          ≤ (2 ^ s.re * Real.exp (-(s.re * |t|))) *
              Real.exp (|a.re| * |t|) :=
        mul_le_mul hcosh hexp (Real.exp_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
            (Real.exp_nonneg _))
      _ = 2 ^ s.re * Real.exp (-(d * |t|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [d]
        ring

/-- Full complex hyperbolic Beta transform on its exact absolute-convergence chamber. -/
theorem integral_complex_cosh_cpow_neg_mul_exp {s a : ℂ}
    (hplus : 0 < ((s + a) / 2).re) (hminus : 0 < ((s - a) / 2).re) :
    (∫ t : ℝ, ((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.exp (a * (t : ℂ)))
      = (2 : ℂ) ^ (s - 1) *
          (Complex.Gamma ((s + a) / 2) * Complex.Gamma ((s - a) / 2) /
            Complex.Gamma s) := by
  have hinj : Set.InjOn HTGeometry.logisticVar Set.univ :=
    Set.injOn_of_injective HTGeometry.logisticVar_strictMono.injective
  have hderiv : ∀ t ∈ Set.univ,
      HasDerivWithinAt HTGeometry.logisticVar (1 / (2 * Real.cosh t ^ 2)) Set.univ t :=
    fun t _ => (HTGeometry.hasDerivAt_logisticVar t).hasDerivWithinAt
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hderiv hinj
    (fun v : ℝ => (v : ℂ) ^ (((s + a) / 2) - 1) *
      ((1 : ℂ) - (v : ℂ)) ^ (((s - a) / 2) - 1))
  rw [HTGeometry.logisticVar_image_univ] at hchange
  have hfun : (fun t : ℝ => |1 / (2 * Real.cosh t ^ 2)| •
      (((HTGeometry.logisticVar t : ℝ) : ℂ) ^ (((s + a) / 2) - 1) *
        ((1 : ℂ) - ((HTGeometry.logisticVar t : ℝ) : ℂ)) ^ (((s - a) / 2) - 1)))
      = fun t : ℝ => (2 : ℂ) ^ (1 - s) *
          (((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.exp (a * (t : ℂ))) :=
    funext complexHyperbolicBeta_jacobian
  rw [MeasureTheory.setIntegral_univ, hfun, MeasureTheory.integral_const_mul,
    ← HTGeometry.betaIntegral_eq_setIntegral] at hchange
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hplus hminus
  have hsum : (s + a) / 2 + (s - a) / 2 = s := by ring
  rw [hsum] at hbeta
  have hGne : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n => ?_
    intro h
    have hre : s.re = (-(n : ℂ)).re := congrArg Complex.re h
    have hsre : 0 < s.re := by
      have := add_pos hplus hminus
      norm_num [Complex.div_re, Complex.normSq_apply] at this
      linarith
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hB : Complex.betaIntegral ((s + a) / 2) ((s - a) / 2) =
      Complex.Gamma ((s + a) / 2) * Complex.Gamma ((s - a) / 2) /
        Complex.Gamma s := by
    rw [eq_div_iff hGne]
    simpa [mul_comm] using hbeta.symm
  rw [hB] at hchange
  have hmul : (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 - s) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
  rw [hchange, ← mul_assoc, hmul]
  simp

/-- The determinant-two hyperbolic pair transform `(p,q) ↦ (p+q,p-q)`. -/
def twoKPairMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.1 + z.2, z.1 - z.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro c x; ext <;> simp <;> ring

theorem twoKPairMap_det : LinearMap.det twoKPairMap = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, twoKPairMap]
  norm_num

/-- Plane kernel remaining after the positive-ray Mellin integral. -/
def twoKPlaneKernel (s mu nu : ℂ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ)) *
    (((Real.cosh z.1 + Real.cosh z.2 : ℝ) : ℂ) ^ (-s))

private theorem twoKPlaneKernel_pairMap (s mu nu : ℂ) (z : ℝ × ℝ) :
    twoKPlaneKernel s mu nu (twoKPairMap z) =
      (2 : ℂ) ^ (-s) *
        (((Real.cosh z.1 : ℝ) : ℂ) ^ (-s) *
          Complex.exp ((mu + nu) * (z.1 : ℂ))) *
        (((Real.cosh z.2 : ℝ) : ℂ) ^ (-s) *
          Complex.exp ((mu - nu) * (z.2 : ℂ))) := by
  have hp : 0 < Real.cosh z.1 := Real.cosh_pos _
  have hq : 0 < Real.cosh z.2 := Real.cosh_pos _
  have hcosh : Real.cosh (z.1 + z.2) + Real.cosh (z.1 - z.2) =
      2 * Real.cosh z.1 * Real.cosh z.2 := by
    rw [Real.cosh_add, Real.cosh_sub]
    ring
  have hpow : (((2 * Real.cosh z.1 * Real.cosh z.2 : ℝ) : ℂ) ^ (-s)) =
      (2 : ℂ) ^ (-s) * ((Real.cosh z.1 : ℝ) : ℂ) ^ (-s) *
        ((Real.cosh z.2 : ℝ) : ℂ) ^ (-s) := by
    have hfirst := Complex.mul_cpow_ofReal_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hp.le) hq.le (-s)
    have hsecond := Complex.mul_cpow_ofReal_nonneg
      (show (0 : ℝ) ≤ 2 by norm_num) hp.le (-s)
    push_cast at hfirst hsecond ⊢
    rw [hfirst, hsecond]
  change Complex.exp (mu * ((z.1 + z.2 : ℝ) : ℂ) + nu * ((z.1 - z.2 : ℝ) : ℂ)) *
      (((Real.cosh (z.1 + z.2) + Real.cosh (z.1 - z.2) : ℝ) : ℂ) ^ (-s)) = _
  rw [hcosh, hpow]
  have hexparg : mu * ((z.1 + z.2 : ℝ) : ℂ) + nu * ((z.1 - z.2 : ℝ) : ℂ) =
      (mu + nu) * (z.1 : ℂ) + (mu - nu) * (z.2 : ℂ) := by
    push_cast
    ring
  rw [hexparg, Complex.exp_add]
  ring

/-- Absolute convergence of the transformed plane kernel in the two-K chamber. -/
theorem integrable_twoKPlaneKernel_pairMap {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    Integrable (fun z : ℝ × ℝ => twoKPlaneKernel s mu nu (twoKPairMap z))
      ((volume : Measure ℝ).prod volume) := by
  have hp : |(mu + nu).re| < s.re := by
    rw [Complex.add_re]
    exact lt_of_le_of_lt (abs_add_le _ _) hchamber
  have hq : |(mu - nu).re| < s.re := by
    rw [Complex.sub_re]
    refine lt_of_le_of_lt ?_ hchamber
    calc
      |mu.re - nu.re| = |mu.re + (-nu.re)| := by ring_nf
      _ ≤ |mu.re| + |-nu.re| := abs_add_le _ _
      _ = |mu.re| + |nu.re| := by rw [abs_neg]
  have hfp := integrable_complex_cosh_cpow_neg_mul_exp hp
  have hfq := integrable_complex_cosh_cpow_neg_mul_exp hq
  have hprod := hfp.mul_prod hfq
  refine (hprod.const_mul ((2 : ℂ) ^ (-s))).congr (ae_of_all _ fun z => ?_)
  change (2 : ℂ) ^ (-s) *
      ((((Real.cosh z.1 : ℝ) : ℂ) ^ (-s) * Complex.exp ((mu + nu) * (z.1 : ℂ))) *
        (((Real.cosh z.2 : ℝ) : ℂ) ^ (-s) * Complex.exp ((mu - nu) * (z.2 : ℂ)))) =
      twoKPlaneKernel s mu nu (twoKPairMap z)
  rw [twoKPlaneKernel_pairMap]
  ring

/-- Absolute convergence of the original plane kernel, transported back through the invertible
determinant-two pair map. -/
theorem integrable_twoKPlaneKernel {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    Integrable (twoKPlaneKernel s mu nu) ((volume : Measure ℝ).prod volume) := by
  let m : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  have hmap : Measure.map (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) m =
      ENNReal.ofReal (1 / 2 : ℝ) • m := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar m
      (by rw [twoKPairMap_det]; norm_num)
    rw [twoKPairMap_det] at h
    norm_num at h ⊢
    exact h
  have hg : AEStronglyMeasurable (twoKPlaneKernel s mu nu) m := by
    unfold twoKPlaneKernel
    fun_prop
  have hgmap : AEStronglyMeasurable (twoKPlaneKernel s mu nu)
      (Measure.map (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) m) := by
    rw [hmap]
    exact hg.smul_measure _
  have hlin : AEMeasurable (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) m :=
    twoKPairMap.continuous_of_finiteDimensional.measurable.aemeasurable
  have hmapped : Integrable (twoKPlaneKernel s mu nu)
      (Measure.map (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) m) :=
    (MeasureTheory.integrable_map_measure hgmap hlin).mpr (by
      simpa [m, Function.comp_def] using integrable_twoKPlaneKernel_pairMap hchamber)
  rw [hmap] at hmapped
  exact (MeasureTheory.integrable_smul_measure (f := twoKPlaneKernel s mu nu)
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤)).mp hmapped

/-- Determinant-two separation of the plane kernel into two hyperbolic Beta transforms. -/
theorem integral_twoKPlaneKernel_eq_product {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    (∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu z ∂((volume : Measure ℝ).prod volume)) =
      2 * (2 : ℂ) ^ (-s) *
        (∫ p : ℝ, ((Real.cosh p : ℝ) : ℂ) ^ (-s) *
          Complex.exp ((mu + nu) * (p : ℂ))) *
        (∫ q : ℝ, ((Real.cosh q : ℝ) : ℂ) ^ (-s) *
          Complex.exp ((mu - nu) * (q : ℂ))) := by
  let fp : ℝ → ℂ := fun p => ((Real.cosh p : ℝ) : ℂ) ^ (-s) *
    Complex.exp ((mu + nu) * (p : ℂ))
  let fq : ℝ → ℂ := fun q => ((Real.cosh q : ℝ) : ℂ) ^ (-s) *
    Complex.exp ((mu - nu) * (q : ℂ))
  have hp : |(mu + nu).re| < s.re := by
    rw [Complex.add_re]
    exact lt_of_le_of_lt (abs_add_le _ _) hchamber
  have hq : |(mu - nu).re| < s.re := by
    rw [Complex.sub_re]
    refine lt_of_le_of_lt ?_ hchamber
    calc
      |mu.re - nu.re| = |mu.re + (-nu.re)| := by ring_nf
      _ ≤ |mu.re| + |-nu.re| := abs_add_le _ _
      _ = |mu.re| + |nu.re| := by rw [abs_neg]
  have hfp : Integrable fp := integrable_complex_cosh_cpow_neg_mul_exp hp
  have hfq : Integrable fq := integrable_complex_cosh_cpow_neg_mul_exp hq
  have hprod : Integrable (fun z : ℝ × ℝ => fp z.1 * fq z.2)
      ((volume : Measure ℝ).prod volume) := hfp.mul_prod hfq
  have hsep : (∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu (twoKPairMap z)
      ∂((volume : Measure ℝ).prod volume)) =
      (2 : ℂ) ^ (-s) * (∫ p : ℝ, fp p) * (∫ q : ℝ, fq q) := by
    calc
      (∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu (twoKPairMap z)
          ∂((volume : Measure ℝ).prod volume)) =
          ∫ z : ℝ × ℝ, (2 : ℂ) ^ (-s) * (fp z.1 * fq z.2)
            ∂((volume : Measure ℝ).prod volume) := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        change twoKPlaneKernel s mu nu (twoKPairMap z) =
          (2 : ℂ) ^ (-s) * (fp z.1 * fq z.2)
        rw [twoKPlaneKernel_pairMap]
        simp only [fp, fq]
        ring
      _ = (2 : ℂ) ^ (-s) *
          ∫ z : ℝ × ℝ, fp z.1 * fq z.2 ∂((volume : Measure ℝ).prod volume) :=
        by rw [MeasureTheory.integral_const_mul]
      _ = (2 : ℂ) ^ (-s) * ∫ p : ℝ, ∫ q : ℝ, fp p * fq q := by
        congr 1
        exact (MeasureTheory.integral_integral
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (f := fun p q => fp p * fq q) hprod).symm
      _ = (2 : ℂ) ^ (-s) * (∫ p : ℝ, fp p) * (∫ q : ℝ, fq q) := by
        simp_rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_mul_const]
        ring
  have hmeas : AEStronglyMeasurable (twoKPlaneKernel s mu nu) := by
    unfold twoKPlaneKernel
    fun_prop
  have hchange := GaloisForLFunctions.RHTower.integral_comp_linearMap_addHaar
    ((volume : Measure ℝ).prod volume) (f := twoKPairMap)
    (by rw [twoKPairMap_det]; norm_num) hmeas
  rw [twoKPairMap_det] at hchange
  norm_num at hchange
  rw [hsep] at hchange
  change (∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu z ∂((volume : Measure ℝ).prod volume)) =
      2 * (2 : ℂ) ^ (-s) * (∫ p : ℝ, fp p) * (∫ q : ℝ, fq q)
  linear_combination 2 * hchange.symm

/-- Four-Gamma evaluation of the determinant-two plane kernel. -/
theorem integral_twoKPlaneKernel_eq_gammaProduct {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    (∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu z ∂((volume : Measure ℝ).prod volume)) =
      (2 : ℂ) ^ (s - 1) *
        (Complex.Gamma ((s + mu + nu) / 2) *
          Complex.Gamma ((s + mu - nu) / 2) *
          Complex.Gamma ((s - mu + nu) / 2) *
          Complex.Gamma ((s - mu - nu) / 2) /
          Complex.Gamma s ^ 2) := by
  have hp : |(mu + nu).re| < s.re := by
    rw [Complex.add_re]
    exact lt_of_le_of_lt (abs_add_le _ _) hchamber
  have hq : |(mu - nu).re| < s.re := by
    rw [Complex.sub_re]
    refine lt_of_le_of_lt ?_ hchamber
    calc
      |mu.re - nu.re| = |mu.re + (-nu.re)| := by ring_nf
      _ ≤ |mu.re| + |-nu.re| := abs_add_le _ _
      _ = |mu.re| + |nu.re| := by rw [abs_neg]
  have hpBounds := (abs_lt.mp hp)
  have hqBounds := (abs_lt.mp hq)
  simp only [Complex.add_re, Complex.sub_re] at hpBounds hqBounds
  have hpp : 0 < ((s + (mu + nu)) / 2).re := by
    norm_num [Complex.div_re, Complex.normSq_apply]
    linarith
  have hpm : 0 < ((s - (mu + nu)) / 2).re := by
    norm_num [Complex.div_re, Complex.normSq_apply]
    linarith
  have hqp : 0 < ((s + (mu - nu)) / 2).re := by
    norm_num [Complex.div_re, Complex.normSq_apply]
    linarith
  have hqm : 0 < ((s - (mu - nu)) / 2).re := by
    norm_num [Complex.div_re, Complex.normSq_apply]
    linarith
  rw [integral_twoKPlaneKernel_eq_product hchamber,
    integral_complex_cosh_cpow_neg_mul_exp hpp hpm,
    integral_complex_cosh_cpow_neg_mul_exp hqp hqm]
  have hcoef : 2 * (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (s - 1) = 1 := by
    calc
      2 * (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (s - 1) =
          ((2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s)) * (2 : ℂ) ^ (s - 1) := by
        rw [Complex.cpow_one]
      _ = (2 : ℂ) ^ ((1 : ℂ) + (-s)) * (2 : ℂ) ^ (s - 1) := by
        congr 1
        exact (Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = (2 : ℂ) ^ (((1 : ℂ) + (-s)) + (s - 1)) := by
        exact (Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = 1 := by
        rw [show ((1 : ℂ) + (-s)) + (s - 1) = 0 by ring, Complex.cpow_zero]
  have hG : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n hsn => ?_
    have hspos : 0 < s.re := lt_of_le_of_lt
      (add_nonneg (abs_nonneg mu.re) (abs_nonneg nu.re)) hchamber
    have hre : s.re = (-(n : ℂ)).re := congrArg Complex.re hsn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [show s + (mu + nu) = s + mu + nu by ring,
    show s - (mu + nu) = s - mu - nu by ring,
    show s + (mu - nu) = s + mu - nu by ring,
    show s - (mu - nu) = s - mu + nu by ring]
  field_simp [hG]
  rw [hcoef]
  ring

/-- Whole-line exponential Schlaefli kernel for the order-variable Bessel function. -/
def besselOrderExpKernel (x : ℝ) (nu : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) * Complex.cosh (t : ℂ) + nu * (t : ℂ))

theorem integrable_besselOrderExpKernel {x : ℝ} (hx : 0 < x) (nu : ℂ) :
    Integrable (besselOrderExpKernel x nu) := by
  let B : ℝ → ℝ := fun t =>
    Real.exp (2 * nu.re ^ 2 / x) * Real.exp (-(x / 8) * t ^ 2)
  have hB : Integrable B := by
    simpa [B] using
      (integrable_exp_neg_mul_sq (div_pos hx (by norm_num : (0 : ℝ) < 8))).const_mul
        (Real.exp (2 * nu.re ^ 2 / x))
  refine Integrable.mono' hB (by unfold besselOrderExpKernel; fun_prop) ?_
  refine ae_of_all _ fun t => ?_
  rw [besselOrderExpKernel, Complex.norm_exp]
  have hre : (-(x : ℂ) * Complex.cosh (t : ℂ) + nu * (t : ℂ)).re =
      -x * Real.cosh t + nu.re * t := by
    rw [← Complex.ofReal_cosh]
    simp
  rw [hre]
  have htilt : nu.re * t ≤ |nu.re| * |t| := by
    calc
      nu.re * t ≤ |nu.re * t| := le_abs_self _
      _ = |nu.re| * |t| := abs_mul _ _
  have hbase := _root_.GaloisForLFunctions.HTGeometry.bessel_exponent_bound
    x |nu.re| hx (abs_nonneg t)
  have hbound : -x * Real.cosh t + nu.re * t ≤
      2 * nu.re ^ 2 / x - x / 8 * t ^ 2 := by
    calc
      -x * Real.cosh t + nu.re * t ≤ -x * Real.cosh t + |nu.re| * |t| := by linarith
      _ ≤ 2 * nu.re ^ 2 / x - x / 8 * |t| ^ 2 := by
        simpa only [Real.cosh_abs, sq_abs] using hbase
      _ = 2 * nu.re ^ 2 / x - x / 8 * t ^ 2 := by rw [sq_abs]
  calc
    Real.exp (-x * Real.cosh t + nu.re * t) ≤
        Real.exp (2 * nu.re ^ 2 / x - x / 8 * t ^ 2) := Real.exp_le_exp.mpr hbound
    _ = B t := by
      simp only [B, sub_eq_add_neg, neg_mul]
      rw [Real.exp_add]

private theorem besselOrderExpKernel_add_neg (x : ℝ) (nu : ℂ) (t : ℝ) :
    besselOrderExpKernel x nu t + besselOrderExpKernel x nu (-t) =
      2 * _root_.GaloisForLFunctions.HTGeometry.besselOrderKernel x nu t := by
  rw [besselOrderExpKernel, besselOrderExpKernel,
    _root_.GaloisForLFunctions.HTGeometry.besselOrderKernel]
  rw [Complex.ofReal_neg, Complex.cosh_neg]
  rw [show -(x : ℂ) * Complex.cosh (t : ℂ) + nu * (t : ℂ) =
      (-(x : ℂ) * Complex.cosh (t : ℂ)) + nu * (t : ℂ) by ring,
    show -(x : ℂ) * Complex.cosh (t : ℂ) + nu * (-(t : ℂ)) =
      (-(x : ℂ) * Complex.cosh (t : ℂ)) + -(nu * (t : ℂ)) by ring,
    Complex.exp_add, Complex.exp_add]
  have hcosh : Complex.exp (nu * (t : ℂ)) + Complex.exp (-(nu * (t : ℂ))) =
      2 * Complex.cosh (nu * (t : ℂ)) := by
    rw [Complex.cosh]
    ring
  rw [← mul_add, hcosh]
  ring

/-- The whole-line exponential Schlaefli integral is twice the corpus half-line Bessel carrier. -/
theorem integral_besselOrderExpKernel_eq_two_mul {x : ℝ} (hx : 0 < x) (nu : ℂ) :
    (∫ t : ℝ, besselOrderExpKernel x nu t) =
      2 * _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu := by
  let f : ℝ → ℂ := besselOrderExpKernel x nu
  let k : ℝ → ℂ := _root_.GaloisForLFunctions.HTGeometry.besselOrderKernel x nu
  have hf : Integrable f := integrable_besselOrderExpKernel hx nu
  have hfneg : Integrable (fun t : ℝ => f (-t)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
      (measurableEmbedding_neg (α := ℝ))).mpr hf
  have hsumInt : Integrable (fun t : ℝ => f t + f (-t)) := hf.add hfneg
  have hk : Integrable k := by
    refine (hsumInt.const_mul ((2 : ℂ)⁻¹)).congr (ae_of_all _ fun t => ?_)
    simp only [f, k]
    rw [besselOrderExpKernel_add_neg]
    field_simp
  have hsum : (∫ t : ℝ, f t + f (-t)) = 2 * ∫ t : ℝ, f t := by
    rw [MeasureTheory.integral_add hf hfneg,
      MeasureTheory.integral_neg_eq_self f (volume : Measure ℝ)]
    ring
  have hsumk : (∫ t : ℝ, f t + f (-t)) = 2 * ∫ t : ℝ, k t := by
    rw [integral_congr_ae (ae_of_all _ fun t => besselOrderExpKernel_add_neg x nu t)]
    rw [MeasureTheory.integral_const_mul]
  have heven : ∀ t : ℝ, k (-t) = k t := by
    intro t
    simp only [k, _root_.GaloisForLFunctions.HTGeometry.besselOrderKernel,
      Complex.ofReal_neg, Complex.cosh_neg]
    rw [show nu * (-(t : ℂ)) = -(nu * (t : ℂ)) by ring, Complex.cosh_neg]
  have hkhalf := HTGeometry.integral_even_eq_two_mul_complex hk heven
  have hkhalf' : (∫ t : ℝ, k t) =
      2 * _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu := by
    simpa only [k, _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder] using hkhalf
  have hfk : (∫ t : ℝ, f t) = ∫ t : ℝ, k t := by
    have h2 : 2 * (∫ t : ℝ, f t) = 2 * (∫ t : ℝ, k t) := hsum.symm.trans hsumk
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  change (∫ t : ℝ, f t) =
      2 * _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu
  rw [hfk, hkhalf']

/-- Three-variable kernel whose two integration orders give the Bessel product and the hyperbolic
plane kernel respectively. -/
def twoKMellinTripleKernel (s mu nu : ℂ) (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (z.1 : ℂ) ^ (s - 1) * besselOrderExpKernel z.1 mu z.2.1 *
    besselOrderExpKernel z.1 nu z.2.2

private theorem norm_twoKMellinTripleKernel {s mu nu : ℂ} {x t u : ℝ} (hx : 0 < x) :
    ‖twoKMellinTripleKernel s mu nu (x, (t, u))‖ =
      Real.exp (mu.re * t + nu.re * u) *
        ‖Real.exp (-((Real.cosh t + Real.cosh u) * x)) * x ^ (s.re - 1)‖ := by
  rw [twoKMellinTripleKernel, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re,
    besselOrderExpKernel, besselOrderExpKernel, Complex.norm_exp, Complex.norm_exp]
  have ht : (-(x : ℂ) * Complex.cosh (t : ℂ) + mu * (t : ℂ)).re =
      -x * Real.cosh t + mu.re * t := by
    rw [← Complex.ofReal_cosh]
    simp
  have hu : (-(x : ℂ) * Complex.cosh (u : ℂ) + nu * (u : ℂ)).re =
      -x * Real.cosh u + nu.re * u := by
    rw [← Complex.ofReal_cosh]
    simp
  rw [ht, hu, Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _))]
  have hexp : Real.exp (-x * Real.cosh t + mu.re * t) *
      Real.exp (-x * Real.cosh u + nu.re * u) =
      Real.exp (mu.re * t + nu.re * u) *
        Real.exp (-((Real.cosh t + Real.cosh u) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, hexp]
  ring

private theorem integrableOn_twoKMellinTripleKernel_section {s mu nu : ℂ}
    (hs : 0 < s.re) (z : ℝ × ℝ) :
    IntegrableOn (fun x : ℝ => twoKMellinTripleKernel s mu nu (x, z)) (Ioi 0) := by
  let rate : ℝ := Real.cosh z.1 + Real.cosh z.2
  have hrate : 0 < rate := by simp only [rate]; positivity
  have hbase := _root_.GaloisForLFunctions.HTGeometry.integrableOn_cpow_mul_exp_neg_mul_Ioi
    (s := s) (w := (rate : ℂ)) hs (by simpa [rate] using hrate)
  let C : ℂ := Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ))
  refine MeasureTheory.IntegrableOn.congr_fun (hbase.const_mul C) (fun x hx => ?_)
    measurableSet_Ioi
  have hx : 0 < x := hx
  simp only [C, twoKMellinTripleKernel, besselOrderExpKernel, rate]
  have hexp : Complex.exp (-((x : ℂ) * Complex.cosh (z.1 : ℂ)) + mu * (z.1 : ℂ)) *
      Complex.exp (-((x : ℂ) * Complex.cosh (z.2 : ℂ)) + nu * (z.2 : ℂ)) =
      Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ)) *
        Complex.exp (-(((Real.cosh z.1 + Real.cosh z.2 : ℝ) : ℂ) * (x : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
    congr 1
    push_cast
    ring
  have hexp' : Complex.exp (-(x : ℂ) * Complex.cosh (z.1 : ℂ) + mu * (z.1 : ℂ)) *
      Complex.exp (-(x : ℂ) * Complex.cosh (z.2 : ℂ) + nu * (z.2 : ℂ)) =
      Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ)) *
        Complex.exp (-(((Real.cosh z.1 + Real.cosh z.2 : ℝ) : ℂ) * (x : ℂ))) := by
    simpa only [neg_mul] using hexp
  rw [mul_assoc, hexp']
  ring

private theorem integral_norm_twoKMellinTripleKernel_section {s mu nu : ℂ}
    (hs : 0 < s.re) (z : ℝ × ℝ) :
    (∫ x in Ioi (0 : ℝ), ‖twoKMellinTripleKernel s mu nu (x, z)‖) =
      Real.Gamma s.re *
        ‖twoKPlaneKernel (s.re : ℂ) (mu.re : ℂ) (nu.re : ℂ) z‖ := by
  let rate : ℝ := Real.cosh z.1 + Real.cosh z.2
  have hrate : 0 < rate := by simp only [rate]; positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
    norm_twoKMellinTripleKernel (s := s) (mu := mu) (nu := nu) (x := x)
      (t := z.1) (u := z.2) hx)]
  rw [MeasureTheory.integral_const_mul]
  have hgamma :=
    _root_.GaloisForLFunctions.HTGeometry.DaiYoshikawa.integral_norm_exp_neg_mul_rpow
      hrate hs
  simp only [rate] at hgamma
  rw [hgamma]
  have hplane : ‖twoKPlaneKernel (s.re : ℂ) (mu.re : ℂ) (nu.re : ℂ) z‖ =
      Real.exp (mu.re * z.1 + nu.re * z.2) *
        (Real.cosh z.1 + Real.cosh z.2) ^ (-s.re) := by
    rw [twoKPlaneKernel, norm_mul, Complex.norm_exp]
    have hexpre : (((mu.re : ℂ) * (z.1 : ℂ) + (nu.re : ℂ) * (z.2 : ℂ))).re =
        mu.re * z.1 + nu.re * z.2 := by simp
    rw [hexpre, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    norm_num
  rw [hplane, Real.rpow_neg hrate.le]
  field_simp
  ring

/-- Absolute convergence of the full three-variable two-K Mellin kernel. -/
theorem integrable_twoKMellinTripleKernel {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    Integrable (twoKMellinTripleKernel s mu nu)
      ((volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).prod volume)) := by
  have hs : 0 < s.re := lt_of_le_of_lt
    (add_nonneg (abs_nonneg mu.re) (abs_nonneg nu.re)) hchamber
  have hmeas : AEStronglyMeasurable (twoKMellinTripleKernel s mu nu)
      ((volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure ℝ).prod volume)) := by
    unfold twoKMellinTripleKernel besselOrderExpKernel
    fun_prop
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · exact ae_of_all _ fun z => integrableOn_twoKMellinTripleKernel_section hs z
  · have hplane : Integrable
        (twoKPlaneKernel (s.re : ℂ) (mu.re : ℂ) (nu.re : ℂ))
        ((volume : Measure ℝ).prod volume) := by
      apply integrable_twoKPlaneKernel
      simpa using hchamber
    refine (hplane.norm.const_mul (Real.Gamma s.re)).congr (ae_of_all _ fun z => ?_)
    exact (integral_norm_twoKMellinTripleKernel_section
      (s := s) (mu := mu) (nu := nu) hs z).symm

private theorem integral_twoKMellinTripleKernel_section_eq {s mu nu : ℂ}
    (hs : 0 < s.re) (z : ℝ × ℝ) :
    (∫ x in Ioi (0 : ℝ), twoKMellinTripleKernel s mu nu (x, z)) =
      Complex.Gamma s * twoKPlaneKernel s mu nu z := by
  let rate : ℝ := Real.cosh z.1 + Real.cosh z.2
  have hrate : 0 < rate := by simp only [rate]; positivity
  let C : ℂ := Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ))
  have hpoint : ∀ x ∈ Ioi (0 : ℝ), twoKMellinTripleKernel s mu nu (x, z) =
      C * ((x : ℂ) ^ (s - 1) * Complex.exp (-((rate : ℂ) * (x : ℂ)))) := by
    intro x hx
    have hx : 0 < x := hx
    simp only [C, twoKMellinTripleKernel, besselOrderExpKernel, rate]
    have hexp : Complex.exp (-(x : ℂ) * Complex.cosh (z.1 : ℂ) + mu * (z.1 : ℂ)) *
        Complex.exp (-(x : ℂ) * Complex.cosh (z.2 : ℂ) + nu * (z.2 : ℂ)) =
        Complex.exp (mu * (z.1 : ℂ) + nu * (z.2 : ℂ)) *
          Complex.exp (-(((Real.cosh z.1 + Real.cosh z.2 : ℝ) : ℂ) * (x : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      rw [← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
      congr 1
      push_cast
      ring
    rw [mul_assoc, hexp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
    MeasureTheory.integral_const_mul]
  rw [_root_.GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
    hs (by simpa [rate] using hrate)]
  rw [twoKPlaneKernel]
  simp only [C, rate]
  ring

private theorem integral_twoKMellinTripleKernel_plane_eq {s mu nu : ℂ}
    {x : ℝ} (hx : 0 < x) :
    (∫ z : ℝ × ℝ, twoKMellinTripleKernel s mu nu (x, z)
      ∂((volume : Measure ℝ).prod volume)) =
      4 * (x : ℂ) ^ (s - 1) *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x mu *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu := by
  let f : ℝ → ℂ := besselOrderExpKernel x mu
  let g : ℝ → ℂ := besselOrderExpKernel x nu
  have hf : Integrable f := integrable_besselOrderExpKernel hx mu
  have hg : Integrable g := integrable_besselOrderExpKernel hx nu
  have hprod : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2)
      ((volume : Measure ℝ).prod volume) := hf.mul_prod hg
  have hfg : (∫ z : ℝ × ℝ, f z.1 * g z.2 ∂((volume : Measure ℝ).prod volume)) =
      (∫ t : ℝ, f t) * (∫ u : ℝ, g u) := by
    rw [MeasureTheory.integral_prod _ hprod]
    simp_rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_mul_const]
  rw [show (fun z : ℝ × ℝ => twoKMellinTripleKernel s mu nu (x, z)) =
      fun z => (x : ℂ) ^ (s - 1) * (f z.1 * g z.2) by
        funext z
        simp only [twoKMellinTripleKernel, f, g]
        ring]
  rw [MeasureTheory.integral_const_mul, hfg]
  rw [show (∫ t : ℝ, f t) =
      2 * _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x mu by
        simpa only [f] using integral_besselOrderExpKernel_eq_two_mul hx mu,
    show (∫ u : ℝ, g u) =
      2 * _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu by
        simpa only [g] using integral_besselOrderExpKernel_eq_two_mul hx nu]
  ring

/-- Exact complex two-K Mellin product on the sharp absolute-convergence chamber. -/
theorem integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder {s mu nu : ℂ}
    (hchamber : |mu.re| + |nu.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x mu *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu) =
      (2 : ℂ) ^ (s - 3) / Complex.Gamma s *
        (Complex.Gamma ((s + mu + nu) / 2) *
          Complex.Gamma ((s + mu - nu) / 2) *
          Complex.Gamma ((s - mu + nu) / 2) *
          Complex.Gamma ((s - mu - nu) / 2)) := by
  have hs : 0 < s.re := lt_of_le_of_lt
    (add_nonneg (abs_nonneg mu.re) (abs_nonneg nu.re)) hchamber
  have htriple := integrable_twoKMellinTripleKernel hchamber
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      (x : ℂ) ^ (s - 1) *
          _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x mu *
          _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu =
        (4 : ℂ)⁻¹ *
          (∫ z : ℝ × ℝ, twoKMellinTripleKernel s mu nu (x, z)
            ∂((volume : Measure ℝ).prod volume)) := by
    intro x hx
    rw [integral_twoKMellinTripleKernel_plane_eq (s := s) (mu := mu) (nu := nu) hx]
    norm_num
    ring
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := ((volume : Measure ℝ).prod volume))
    (f := fun x z => twoKMellinTripleKernel s mu nu (x, z)) htriple
  have hsection :
      (∫ z : ℝ × ℝ, (∫ x in Ioi (0 : ℝ), twoKMellinTripleKernel s mu nu (x, z))
          ∂((volume : Measure ℝ).prod volume)) =
        Complex.Gamma s *
          ∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu z
            ∂((volume : Measure ℝ).prod volume) := by
    rw [integral_congr_ae (ae_of_all _ fun z =>
      integral_twoKMellinTripleKernel_section_eq (s := s) (mu := mu) (nu := nu) hs z)]
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x mu *
        _root_.GaloisForLFunctions.HTGeometry.modifiedBesselKOrder x nu) =
        ∫ x in Ioi (0 : ℝ), (4 : ℂ)⁻¹ *
          (∫ z : ℝ × ℝ, twoKMellinTripleKernel s mu nu (x, z)
            ∂((volume : Measure ℝ).prod volume)) := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = (4 : ℂ)⁻¹ *
        (∫ x in Ioi (0 : ℝ), ∫ z : ℝ × ℝ,
          twoKMellinTripleKernel s mu nu (x, z)
            ∂((volume : Measure ℝ).prod volume)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (4 : ℂ)⁻¹ *
        (∫ z : ℝ × ℝ, (∫ x in Ioi (0 : ℝ),
          twoKMellinTripleKernel s mu nu (x, z))
            ∂((volume : Measure ℝ).prod volume)) := by rw [hswap]
    _ = (4 : ℂ)⁻¹ * (Complex.Gamma s *
        ∫ z : ℝ × ℝ, twoKPlaneKernel s mu nu z
          ∂((volume : Measure ℝ).prod volume)) := by rw [hsection]
    _ = (2 : ℂ) ^ (s - 3) / Complex.Gamma s *
        (Complex.Gamma ((s + mu + nu) / 2) *
          Complex.Gamma ((s + mu - nu) / 2) *
          Complex.Gamma ((s - mu + nu) / 2) *
          Complex.Gamma ((s - mu - nu) / 2)) := by
      rw [integral_twoKPlaneKernel_eq_gammaProduct hchamber]
      have hG : Complex.Gamma s ≠ 0 := by
        refine Complex.Gamma_ne_zero fun n hsn => ?_
        have hre : s.re = (-(n : ℂ)).re := congrArg Complex.re hsn
        simp only [Complex.neg_re, Complex.natCast_re] at hre
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hfour : (4 : ℂ)⁻¹ = (2 : ℂ) ^ (-(2 : ℂ)) := by
        norm_num [Complex.cpow_neg, Complex.cpow_natCast]
      have hpow : (4 : ℂ)⁻¹ * (2 : ℂ) ^ (s - 1) = (2 : ℂ) ^ (s - 3) := by
        rw [hfour]
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
        congr 1
        ring
      have hpow4 : (2 : ℂ) ^ (s - 1) = 4 * (2 : ℂ) ^ (s - 3) := by
        calc
          (2 : ℂ) ^ (s - 1) = (4 * (4 : ℂ)⁻¹) * (2 : ℂ) ^ (s - 1) := by norm_num
          _ = 4 * ((4 : ℂ)⁻¹ * (2 : ℂ) ^ (s - 1)) := by ring
          _ = 4 * (2 : ℂ) ^ (s - 3) := by rw [hpow]
      field_simp [hG]
      rw [hpow4]
      ring

end

end GaloisForLFunctions.RHTower
