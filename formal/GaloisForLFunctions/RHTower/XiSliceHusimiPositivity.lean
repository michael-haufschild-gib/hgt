import GaloisForLFunctions.RHTower.XiSliceMixedClassDetection
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAllShiftedTails

/-!
# Husimi positivity of the height-averaged slice

Let `Ξ(z) = ∫ Φ(u) e^{−izu} du` with `Φ` the even theta source, and let
`g_t(x) = Ξ(t − ix) Ξ(t + ix) = ξ(½+x+it) ξ(½−x+it)` be the horizontal slice.  Average the slice over
heights with the Gaussian `G_σ(τ) = (σ/√π) e^{−σ²τ²}` and multiply by the heat factor `e^{σ²x²}`.

**Theorem** (`exp_mul_xiSliceHeightAverage_eq`).  For `σ > 0` and real `t`, `x`,

  `e^{σ²x²} ∫ G_σ(t − t′) g_{t′}(x) dt′ = (σ√π)⁻¹ ∫ e^{2xs} |V_σ(s,t)|² ds`,

where `V_σ(s,t) = ∫ Φ(u) e^{−(u+s)²/(2σ²)} e^{−itu} du` is the Gabor (coherent-state) transform of
`Φ`.  The right side is the exponential transform of the nonnegative Husimi density
`|V_σ(·,t)|²`.  So, at every height and for every `σ`, the height-averaged slice times
`e^{σ²x²}` has all Taylor coefficients nonnegative (its coefficients are moments of a positive
density).

**Meaning.**  Slice positivity at every height is the Riemann hypothesis
(`riemannHypothesis_iff_ae_xiSliceCoeff_nonneg`).  The identity is its uncertainty-limited form.
Localizing in height at scale `1/σ` costs exactly the heat factor `e^{σ²x²}`.  In coefficients, the
average of `c_{2j}` is bounded below by `−σ²` times the average of `c_{2j−2}`, up to higher terms.
That is informative only while `σ` is below the local zero density.  This is the bandwidth-one wall
in Wigner form.

The proof is the abstract identity `exp_mul_heightAverage_eq` for any even real source with all
exponential moments: two Gaussian integrals (`integral_cexp_quadratic`) and two Fubini exchanges.
-/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- **Height Gaussian.**  `∫ (σ/√π) e^{−σ²(t−t′)²} e^{−it′ξ} dt′ = e^{−itξ − ξ²/(4σ²)}`. -/
theorem integral_heightGaussian_mul_cexp {σ : ℝ} (hσ : 0 < σ) (t ξ : ℝ) :
    ∫ t' : ℝ, ((σ / Real.sqrt π * Real.exp (-(σ ^ 2 * (t - t') ^ 2)) : ℝ) : ℂ) *
        cexp (-(I * t' * ξ)) =
      cexp (-(I * t * ξ) - (ξ : ℂ) ^ 2 / (4 * σ ^ 2)) := by
  have hb : ((-(σ : ℂ) ^ 2)).re < 0 := by
    simp only [neg_re, ← ofReal_pow, ofReal_re]
    exact neg_neg_of_pos (pow_pos hσ 2)
  have hint := integral_cexp_quadratic hb (2 * σ ^ 2 * t - I * ξ) (-((σ : ℂ) ^ 2 * t ^ 2))
  have e : ∀ t' : ℝ, ((σ / Real.sqrt π * Real.exp (-(σ ^ 2 * (t - t') ^ 2)) : ℝ) : ℂ) *
      cexp (-(I * t' * ξ)) = ((σ / Real.sqrt π : ℝ) : ℂ) *
        cexp (-(σ : ℂ) ^ 2 * (t' : ℂ) ^ 2 + (2 * σ ^ 2 * t - I * ξ) * t' +
          (-((σ : ℂ) ^ 2 * t ^ 2))) := by
    intro t'
    rw [ofReal_mul, ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [integral_const_mul, hint]
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hsq : ((π : ℂ) / -(-(σ : ℂ) ^ 2)) ^ (1 / 2 : ℂ) = ((Real.sqrt π / σ : ℝ) : ℂ) := by
    rw [neg_neg, show ((π : ℂ) / (σ : ℂ) ^ 2) = ((π / σ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), Real.sqrt_eq_rpow, Real.div_rpow hpi.le (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
    norm_num
  rw [hsq, ← mul_assoc, ← ofReal_mul]
  have hone : σ / Real.sqrt π * (Real.sqrt π / σ) = 1 := by
    field_simp
  rw [hone, ofReal_one, one_mul]
  congr 1
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Centre Gaussian.**  `∫ e^{2xs} e^{−((u+s)² + (v−s)²)/(2σ²)} ds
`= σ√π e^{σ²x² − x(u−v) − (u+v)²/(4σ²)}`. -/
theorem integral_centreGaussian {σ : ℝ} (hσ : 0 < σ) (x u v : ℝ) :
    ∫ s : ℝ, cexp (2 * x * s - ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2)) =
      ((σ * Real.sqrt π : ℝ) : ℂ) *
        cexp (σ ^ 2 * x ^ 2 - x * (u - v) - (u + v) ^ 2 / (4 * σ ^ 2)) := by
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hb : (-(1 / (σ : ℂ) ^ 2)).re < 0 := by
    rw [show (1 / (σ : ℂ) ^ 2) = ((1 / σ ^ 2 : ℝ) : ℂ) by push_cast; ring, neg_re, ofReal_re]
    exact neg_neg_of_pos (by positivity)
  have hint := integral_cexp_quadratic hb (2 * x - (u - v) / σ ^ 2)
    (-(((u : ℂ) ^ 2 + v ^ 2) / (2 * σ ^ 2)))
  have e : ∀ s : ℝ, cexp (2 * x * s - ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2)) =
      cexp (-(1 / (σ : ℂ) ^ 2) * (s : ℂ) ^ 2 + (2 * x - (u - v) / σ ^ 2) * s +
        (-(((u : ℂ) ^ 2 + v ^ 2) / (2 * σ ^ 2)))) := by
    intro s
    congr 1
    field_simp
    ring
  simp_rw [e]
  rw [hint]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hsq : ((π : ℂ) / -(-(1 / (σ : ℂ) ^ 2))) ^ (1 / 2 : ℂ) = ((σ * Real.sqrt π : ℝ) : ℂ) := by
    rw [neg_neg, show ((π : ℂ) / (1 / (σ : ℂ) ^ 2)) = ((σ ^ 2 * π : ℝ) : ℂ) by
        push_cast; field_simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), Real.mul_rpow (by positivity) hpi.le, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hσ.le]
  rw [hsq]
  congr 1
  field_simp
  ring

/-! ## The abstract identity for an even source with all exponential moments -/

section Abstract

/-- The Fourier–Laplace transform `F(z) = ∫ e^{−izu} f(u) du` (the convention of
`sourceTransform`). -/
def sourceFL (f : ℝ → ℝ) (z : ℂ) : ℂ := ∫ u : ℝ, cexp (-I * z * u) * (f u : ℂ)

/-- The Gabor amplitude `V_σ(s,t) = ∫ f(u) e^{−(u+s)²/(2σ²)} e^{−itu} du`. -/
def gaborAmp (f : ℝ → ℝ) (σ t s : ℝ) : ℂ :=
  ∫ u : ℝ, (f u : ℂ) * ((Real.exp (-((u + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) * cexp (-I * t * u)

/-- The height Gaussian `G_σ(τ) = (σ/√π) e^{−σ²τ²}` centred at `t`. -/
def heightGaussian (σ t t' : ℝ) : ℝ := σ / Real.sqrt π * Real.exp (-(σ ^ 2 * (t - t') ^ 2))

theorem integrable_heightGaussian {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Integrable (fun t' : ℝ => heightGaussian σ t t') := by
  have h := ((integrable_exp_neg_mul_sq (pow_pos hσ 2)).comp_sub_left t).const_mul
    (σ / Real.sqrt π)
  refine h.congr (Filter.Eventually.of_forall fun t' => ?_)
  simp only [heightGaussian, neg_mul]

variable {f : ℝ → ℝ}

theorem integrable_exp_mul_abs_of_moments
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (b : ℝ) :
    Integrable (fun u => Real.exp (b * u) * |f u|) := by
  refine (hexp b).norm.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **The slice as a double integral.** -/
theorem sourceFL_sub_mul_add (f : ℝ → ℝ) (t x : ℝ) :
    sourceFL f ((t : ℂ) - I * x) * sourceFL f ((t : ℂ) + I * x) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-I * t * (p.1 + p.2) - x * (p.1 - p.2)) := by
  unfold sourceFL
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : -I * ((t : ℂ) - I * x) * p.1 + -I * ((t : ℂ) + I * x) * p.2 =
      -I * t * (p.1 + p.2) - x * (p.1 - p.2) := by
    ring_nf
    rw [I_sq]
    ring
  show cexp (-I * ((t : ℂ) - I * x) * p.1) * (f p.1 : ℂ) *
      (cexp (-I * ((t : ℂ) + I * x) * p.2) * (f p.2 : ℂ)) =
    ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2) - x * (p.1 - p.2))
  rw [← e, Complex.exp_add]
  push_cast
  ring

/-- **The height average of the slice.** -/
theorem integral_heightGaussian_mul_sourceFL {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) *
        (sourceFL f ((t' : ℂ) - I * x) * sourceFL f ((t' : ℂ) + I * x)) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-(x * (p.1 - p.2)) - I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 /
          (4 * σ ^ 2)) := by
  simp_rw [sourceFL_sub_mul_add, ← integral_const_mul]
  rw [integral_integral_swap]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have e : ∀ t' : ℝ, (heightGaussian σ t t' : ℂ) * (((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-I * t' * (p.1 + p.2) - x * (p.1 - p.2))) =
        (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-(x * (p.1 - p.2)))) *
          (((σ / Real.sqrt π * Real.exp (-(σ ^ 2 * (t - t') ^ 2)) : ℝ) : ℂ) *
            cexp (-(I * t' * ((p.1 + p.2 : ℝ))))) := by
      intro t'
      simp only [heightGaussian]
      rw [show -I * (t' : ℂ) * (p.1 + p.2) - x * (p.1 - p.2) =
          -(x * (p.1 - p.2)) + -(I * t' * ((p.1 + p.2 : ℝ) : ℂ)) by push_cast; ring,
        Complex.exp_add]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_heightGaussian_mul_cexp hσ, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · -- integrability of the triple integrand
    have hG := integrable_heightGaussian hσ t
    have hA := integrable_exp_mul_abs_of_moments hexp (-x)
    have hB := integrable_exp_mul_abs_of_moments hexp x
    have hprod := hG.mul_prod (hA.mul_prod hB)
    refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      unfold heightGaussian
      fun_prop
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp]
      have hGz : 0 ≤ heightGaussian σ t z.1 := by unfold heightGaussian; positivity
      rw [abs_of_nonneg hGz]
      have hre : (-I * (z.1 : ℂ) * (z.2.1 + z.2.2) - x * (z.2.1 - z.2.2)).re =
          -(x * (z.2.1 - z.2.2)) := by simp
      rw [hre]
      have : Real.exp (-(x * (z.2.1 - z.2.2))) = Real.exp (-x * z.2.1) * Real.exp (x * z.2.2) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      apply le_of_eq
      ring

/-- The Husimi density as a double integral (reflection uses that `f` is even). -/
theorem normSq_gaborAmp_eq_integral {σ : ℝ} (hσ : 0 < σ) (heven : ∀ u, f (-u) = f u) (t s : ℝ) :
    (Complex.normSq (gaborAmp f σ t s) : ℂ) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-I * t * (p.1 + p.2) - ((((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2) : ℝ) : ℂ)) := by
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  set Q : ℝ → ℝ → ℝ → ℝ := fun s u v => ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2) with hQ
  -- the reflected conjugate amplitude
  have hconj : ∀ s : ℝ, (starRingEnd ℂ) (gaborAmp f σ t s) =
      ∫ v : ℝ, (f v : ℂ) * ((Real.exp (-((v - s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
        cexp (-I * t * v) := by
    intro s
    unfold gaborAmp
    rw [← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show (starRingEnd ℂ) ((f (-v) : ℂ) * ((Real.exp (-((-v + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
        cexp (-I * t * ((-v : ℝ) : ℂ))) = _
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj, heven]
    have h1 : (-v + s) ^ 2 = (v - s) ^ 2 := by ring
    have h2 : (starRingEnd ℂ) (-I * (t : ℂ) * ((-v : ℝ) : ℂ)) = -I * t * v := by
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, ofReal_neg]
      ring
    rw [h1, h2]
  -- the amplitude times its conjugate as a double integral
  have hprod : ∀ s : ℝ, (Complex.normSq (gaborAmp f σ t s) : ℂ) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ)) := by
    intro s
    rw [← Complex.mul_conj, hconj s]
    unfold gaborAmp
    rw [← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show (f p.1 : ℂ) * ((Real.exp (-((p.1 + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
        cexp (-I * t * p.1) * ((f p.2 : ℂ) * ((Real.exp (-((p.2 - s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
          cexp (-I * t * p.2)) = _
    simp only [ofReal_exp, hQ]
    rw [show -I * (t : ℂ) * (p.1 + p.2) - ((((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2) : ℝ) : ℂ) =
        ((-((p.1 + s) ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ) + -I * t * p.1 +
          (((-((p.2 - s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) + -I * t * p.2 by push_cast; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add]
    push_cast
    ring
  exact hprod s

/-- Integrability of the triple Husimi integrand. -/
theorem integrable_husimiTriple {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (p : ℝ × ℝ) => cexp (2 * x * s) *
      (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2) -
        ((((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2) : ℝ) : ℂ))))
      (volume.prod (volume.prod volume)) := by
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  set Q : ℝ → ℝ → ℝ → ℝ := fun s u v => ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2) with hQ
  -- the real centre Gaussian
  have hreal : ∀ u v : ℝ, ∫ s : ℝ, Real.exp (2 * x * s - Q s u v) =
      σ * Real.sqrt π * Real.exp (σ ^ 2 * x ^ 2 - x * (u - v) - (u + v) ^ 2 / (4 * σ ^ 2)) := by
    intro u v
    have h := integral_centreGaussian hσ x u v
    have e1 : (fun s : ℝ => cexp (2 * x * s - ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2))) =
        fun s : ℝ => ((Real.exp (2 * x * s - Q s u v) : ℝ) : ℂ) := by
      funext s; rw [ofReal_exp]; simp only [hQ]; push_cast; ring_nf
    rw [e1, integral_complex_ofReal] at h
    have e2 : cexp (σ ^ 2 * x ^ 2 - x * (u - v) - (u + v) ^ 2 / (4 * σ ^ 2)) =
        ((Real.exp (σ ^ 2 * x ^ 2 - x * (u - v) - (u + v) ^ 2 / (4 * σ ^ 2)) : ℝ) : ℂ) := by
      rw [ofReal_exp]; push_cast; ring_nf
    rw [e2, ← ofReal_mul] at h
    exact_mod_cast h
  -- the triple integrand and its norm
  set F : ℝ → ℝ × ℝ → ℂ := fun s p => cexp (2 * x * s) *
    (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ))) with hF
  have hnorm : ∀ s p, ‖F s p‖ = |f p.1 * f p.2| * Real.exp (2 * x * s - Q s p.1 p.2) := by
    intro s p
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have r1 : (2 * (x : ℂ) * s).re = 2 * x * s := by simp
    have r2 : (-I * (t : ℂ) * (p.1 + p.2) - (Q s p.1 p.2 : ℂ)).re = -Q s p.1 p.2 := by simp
    rw [r1, r2, ← mul_assoc, mul_comm (Real.exp (2 * x * s)), mul_assoc, ← Real.exp_add,
      abs_mul]
    ring_nf
  have hnormint : ∀ p : ℝ × ℝ, ∫ s : ℝ, ‖F s p‖ = |f p.1 * f p.2| * (σ * Real.sqrt π *
      Real.exp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2))) := by
    intro p
    simp_rw [hnorm]
    rw [integral_const_mul, hreal]
  change Integrable (Function.uncurry F) _
  have hA := integrable_exp_mul_abs_of_moments hexp (-x)
  have hB := integrable_exp_mul_abs_of_moments hexp x
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF, hQ]
    fun_prop
  rw [integrable_prod_iff' hFc.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun p => ?_
    have hq := (integrable_cexp_quadratic (b := 1 / (σ : ℂ) ^ 2) (by
      rw [show (1 / (σ : ℂ) ^ 2) = ((1 / σ ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
      positivity) (2 * x - (p.1 - p.2) / σ ^ 2)
      (-(((p.1 : ℂ) ^ 2 + p.2 ^ 2) / (2 * σ ^ 2)) - I * t * (p.1 + p.2))).const_mul
      (((f p.1 * f p.2 : ℝ) : ℂ))
    refine hq.congr (Filter.Eventually.of_forall fun s => ?_)
    show _ = F s p
    simp only [hF]
    rw [show cexp (2 * x * s) * (((f p.1 * f p.2 : ℝ) : ℂ) *
          cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ))) =
        ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (2 * x * s + (-I * t * (p.1 + p.2) -
          (Q s p.1 p.2 : ℂ))) by rw [Complex.exp_add]; ring]
    congr 2
    simp only [hQ]
    push_cast
    field_simp
    ring
  · have hbound := ((hA.mul_prod hB).const_mul
      (σ * Real.sqrt π * Real.exp (σ ^ 2 * x ^ 2)))
    have hc : Continuous (fun p : ℝ × ℝ => |f p.1 * f p.2| * (σ * Real.sqrt π *
        Real.exp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2)))) := by
      fun_prop
    refine hbound.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine (hc.congr fun p => (hnormint p).symm).aestronglyMeasurable
    · show ‖∫ s : ℝ, ‖F s p‖‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _),
        hnormint, abs_mul]
      have hsq : Real.exp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2)) ≤
          Real.exp (σ ^ 2 * x ^ 2) * (Real.exp (-x * p.1) * Real.exp (x * p.2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (p.1 + p.2) ^ 2 / (4 * σ ^ 2) := by positivity
        nlinarith
      have h0 : 0 ≤ |f p.1| * |f p.2| := by positivity
      have hk : 0 ≤ σ * Real.sqrt π := by positivity
      calc |f p.1| * |f p.2| * (σ * Real.sqrt π *
            Real.exp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2)))
          ≤ |f p.1| * |f p.2| * (σ * Real.sqrt π *
            (Real.exp (σ ^ 2 * x ^ 2) * (Real.exp (-x * p.1) * Real.exp (x * p.2)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hk) h0
        _ = σ * Real.sqrt π * Real.exp (σ ^ 2 * x ^ 2) *
            (Real.exp (-x * p.1) * |f p.1| * (Real.exp (x * p.2) * |f p.2|)) := by ring

/-- **The Husimi side.** -/
theorem integral_exp_mul_normSq_gaborAmp {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (heven : ∀ u, f (-u) = f u)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    ∫ s : ℝ, cexp (2 * x * s) * (Complex.normSq (gaborAmp f σ t s) : ℂ) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * (((σ * Real.sqrt π : ℝ) : ℂ) *
        cexp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - I * t * (p.1 + p.2) -
          ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2))) := by
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  set Q : ℝ → ℝ → ℝ → ℝ := fun s u v => ((u + s) ^ 2 + (v - s) ^ 2) / (2 * σ ^ 2) with hQ
  have hprod : ∀ s : ℝ, (Complex.normSq (gaborAmp f σ t s) : ℂ) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ)) :=
    fun s => normSq_gaborAmp_eq_integral hσ heven t s
  set F : ℝ → ℝ × ℝ → ℂ := fun s p => cexp (2 * x * s) *
    (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ))) with hF
  simp_rw [hprod, ← integral_const_mul]
  change ∫ s : ℝ, ∫ p : ℝ × ℝ, F s p = _
  rw [integral_integral_swap]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have e : ∀ s : ℝ, F s p = (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2))) *
          cexp (2 * x * s - ((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2)) := by
      intro s
      simp only [hF]
      rw [show cexp (2 * x * s) * (((f p.1 * f p.2 : ℝ) : ℂ) *
            cexp (-I * t * (p.1 + p.2) - (Q s p.1 p.2 : ℂ))) =
          ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (2 * x * s + (-I * t * (p.1 + p.2) -
            (Q s p.1 p.2 : ℂ))) by rw [Complex.exp_add]; ring,
        show ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2)) *
            cexp (2 * x * s - ((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2)) =
          ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2) +
            (2 * x * s - ((p.1 + s) ^ 2 + (p.2 - s) ^ 2) / (2 * σ ^ 2))) by
          rw [Complex.exp_add]; ring]
      congr 2
      simp only [hQ]
      push_cast
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_centreGaussian hσ]
    rw [show ((f p.1 * f p.2 : ℝ) : ℂ) * cexp (-I * t * (p.1 + p.2)) *
        (((σ * Real.sqrt π : ℝ) : ℂ) *
          cexp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2))) =
        ((f p.1 * f p.2 : ℝ) : ℂ) * (((σ * Real.sqrt π : ℝ) : ℂ) *
          (cexp (-I * t * (p.1 + p.2)) *
            cexp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - (p.1 + p.2) ^ 2 / (4 * σ ^ 2)))) by ring,
      ← Complex.exp_add]
    congr 3
    push_cast
    ring
  · exact integrable_husimiTriple hσ hfc hexp t x

/-- The exponential transform of the Husimi density converges at every real `x`. -/
theorem integrable_exp_mul_normSq_gaborAmp {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (heven : ∀ u, f (-u) = f u)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    Integrable (fun s : ℝ => cexp (2 * x * s) * (Complex.normSq (gaborAmp f σ t s) : ℂ)) := by
  refine (integrable_husimiTriple hσ hfc hexp t x).integral_prod_left.congr
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.uncurry]
  rw [integral_const_mul, normSq_gaborAmp_eq_integral hσ heven t s]
  rfl

/-- The Gabor amplitude is continuous in the centre variable. -/
theorem gaborAmp_continuous {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t : ℝ) :
    Continuous (fun s => gaborAmp f σ t s) := by
  unfold gaborAmp
  refine continuous_of_dominated (bound := fun u => |f u|) (fun s => ?_) (fun s => ?_) ?_ ?_
  · exact (by fun_prop : Continuous fun u : ℝ => (f u : ℂ) *
      ((Real.exp (-((u + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) * cexp (-I * t * u)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-((u + s) ^ 2 / (2 * σ ^ 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : 0 ≤ (u + s) ^ 2 / (2 * σ ^ 2) := by positivity
      linarith
    have h2 : (-I * (t : ℂ) * u).re = 0 := by simp
    rw [h2, Real.exp_zero, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  · simpa using (hexp 0).norm
  · exact Filter.Eventually.of_forall fun u => by fun_prop

/-- The Husimi density is even in the centre variable. -/
theorem normSq_gaborAmp_neg (heven : ∀ u, f (-u) = f u) (σ t s : ℝ) :
    Complex.normSq (gaborAmp f σ t (-s)) = Complex.normSq (gaborAmp f σ t s) := by
  have h : gaborAmp f σ t (-s) = (starRingEnd ℂ) (gaborAmp f σ t s) := by
    unfold gaborAmp
    rw [← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (f (-u) : ℂ) * ((Real.exp (-((-u + -s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
        cexp (-I * t * ((-u : ℝ) : ℂ)) = (starRingEnd ℂ) ((f u : ℂ) *
          ((Real.exp (-((u + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) * cexp (-I * t * u))
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj, heven]
    have h1 : (-u + -s) ^ 2 = (u + s) ^ 2 := by ring
    have h2 : (starRingEnd ℂ) (-I * (t : ℂ) * u) = -I * t * ((-u : ℝ) : ℂ) := by
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, ofReal_neg]
      ring
    rw [h1, h2]
  rw [h, Complex.normSq_conj]

theorem integrable_rexp_mul_normSq_gaborAmp {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (heven : ∀ u, f (-u) = f u)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t y : ℝ) :
    Integrable (fun s : ℝ => Real.exp (2 * y * s) * Complex.normSq (gaborAmp f σ t s)) := by
  refine (integrable_exp_mul_normSq_gaborAmp hσ hfc heven hexp t y).norm.congr
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _)]
  congr 1
  simp

/-- **The moment series of the Husimi transform.**  For real `x`,
`∫ e^{2xs} q(s) ds = Σₙ xⁿ ∫ (2s)ⁿ/n! q(s) ds` with `q = |V_σ(·,t)|²`. -/
theorem hasSum_husimiMoments {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (heven : ∀ u, f (-u) = f u)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    HasSum (fun n : ℕ => x ^ n * ∫ s : ℝ, (2 * s) ^ n / (n.factorial : ℝ) * Complex.normSq (gaborAmp f σ t s))
      (∫ s : ℝ, Real.exp (2 * x * s) * Complex.normSq (gaborAmp f σ t s)) := by
  set q : ℝ → ℝ := fun s => Complex.normSq (gaborAmp f σ t s) with hq
  have hq0 : ∀ s, 0 ≤ q s := fun s => Complex.normSq_nonneg _
  set D : ℝ → ℝ := fun s => (Real.exp (2 * |x| * s) + Real.exp (2 * -|x| * s)) * q s with hD
  have hdom : Integrable D := by
    refine ((integrable_rexp_mul_normSq_gaborAmp hσ hfc heven hexp t |x|).add
      (integrable_rexp_mul_normSq_gaborAmp hσ hfc heven hexp t (-|x|))).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [hD, hq, add_mul, Pi.add_apply]
  have hexpabs : ∀ s, Real.exp |2 * x * s| ≤ Real.exp (2 * |x| * s) + Real.exp (2 * -|x| * s) := by
    intro s
    rcases le_total 0 s with hs | hs
    · have : |2 * x * s| = 2 * |x| * s := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs]; norm_num
      rw [this]
      linarith [Real.exp_pos (2 * -|x| * s)]
    · have : |2 * x * s| = 2 * -|x| * s := by
        rw [abs_mul, abs_mul, abs_of_nonpos hs]; norm_num
      rw [this]
      linarith [Real.exp_pos (2 * |x| * s)]
  have hq_cont : Continuous q :=
    Complex.continuous_normSq.comp (gaborAmp_continuous hσ hfc hexp t)
  have hint : ∀ n : ℕ, Integrable (fun s => (2 * x * s) ^ n / (n.factorial : ℝ) * q s) := by
    intro n
    refine hdom.mono' (by fun_prop) (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 s)]
    refine mul_le_mul_of_nonneg_right ?_ (hq0 s)
    calc |(2 * x * s) ^ n / (n.factorial : ℝ)| = |2 * x * s| ^ n / (n.factorial : ℝ) := by
          rw [abs_div, abs_pow, Nat.abs_cast]
      _ ≤ Real.exp |2 * x * s| := Real.pow_div_factorial_le_exp _ (abs_nonneg _) n
      _ ≤ _ := hexpabs s
  have hsum : Summable (fun n : ℕ => ∫ s, ‖(2 * x * s) ^ n / (n.factorial : ℝ) * q s‖) := by
    refine summable_of_sum_range_le (c := ∫ s, D s)
      (fun n => integral_nonneg fun s => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ (fun n _ => (hint n).norm)]
    refine integral_mono (integrable_finsetSum _ fun n _ => (hint n).norm) hdom fun s => ?_
    have hterm : ∀ n, ‖(2 * x * s) ^ n / (n.factorial : ℝ) * q s‖ = |2 * x * s| ^ n / (n.factorial : ℝ) * q s := by
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 s), abs_div, abs_pow, Nat.abs_cast]
    simp only [hterm, ← Finset.sum_mul, hD]
    refine mul_le_mul_of_nonneg_right ?_ (hq0 s)
    exact (Real.sum_le_exp_of_nonneg (abs_nonneg _) N).trans (hexpabs s)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ s, ∑' n : ℕ, (2 * x * s) ^ n / (n.factorial : ℝ) * q s = Real.exp (2 * x * s) * q s := by
    intro s
    rw [tsum_mul_right, Real.exp_eq_exp_ℝ,
      (NormedSpace.expSeries_div_hasSum_exp (2 * x * s)).tsum_eq]
  simp_rw [htsum] at h
  refine h.congr_fun fun n => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [hq]
  ring

/-- Odd Husimi moments vanish and even ones are nonnegative. -/
theorem husimiMoment_nonneg (heven : ∀ u, f (-u) = f u) (σ t : ℝ) (n : ℕ) :
    0 ≤ ∫ s : ℝ, (2 * s) ^ n / (n.factorial : ℝ) * Complex.normSq (gaborAmp f σ t s) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine integral_nonneg fun s => mul_nonneg (div_nonneg ?_ (by positivity))
      (Complex.normSq_nonneg _)
    rw [← two_mul, pow_mul]
    positivity
  · have hodd : ∫ s : ℝ, (2 * s) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
        Complex.normSq (gaborAmp f σ t s) = 0 := by
      have h := integral_neg_eq_self (fun s : ℝ => (2 * s) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) *
        Complex.normSq (gaborAmp f σ t s)) volume
      simp only [normSq_gaborAmp_neg heven, mul_neg, Odd.neg_pow ⟨k, rfl⟩, neg_div, neg_mul,
        integral_neg] at h
      linarith
    rw [hodd]

end Abstract

/-- **The abstract Husimi identity.**  For an even real source with all exponential moments,
`e^{σ²x²} ∫ G_σ(t − t′) F(t′−ix)F(t′+ix) dt′ = (σ√π)⁻¹ ∫ e^{2xs} |V_σ(s,t)|² ds`. -/
theorem exp_mul_heightAverage_eq {f : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) (hfc : Continuous f)
    (heven : ∀ u, f (-u) = f u)
    (hexp : ∀ b : ℝ, Integrable (fun u => Real.exp (b * u) * f u)) (t x : ℝ) :
    (Real.exp (σ ^ 2 * x ^ 2) : ℂ) * ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) *
        (sourceFL f ((t' : ℂ) - I * x) * sourceFL f ((t' : ℂ) + I * x)) =
      ((1 / (σ * Real.sqrt π) : ℝ) : ℂ) *
        ∫ s : ℝ, cexp (2 * x * s) * (Complex.normSq (gaborAmp f σ t s) : ℂ) := by
  rw [integral_heightGaussian_mul_sourceFL hσ hfc hexp,
    integral_exp_mul_normSq_gaborAmp hσ hfc heven hexp, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hk : σ * Real.sqrt π ≠ 0 := by positivity
  have h1 : ((1 / (σ * Real.sqrt π) : ℝ) : ℂ) * ((σ * Real.sqrt π : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, one_div, inv_mul_cancel₀ hk, ofReal_one]
  beta_reduce
  rw [show ((1 / (σ * Real.sqrt π) : ℝ) : ℂ) * (((f p.1 * f p.2 : ℝ) : ℂ) *
      (((σ * Real.sqrt π : ℝ) : ℂ) * cexp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) - I * t * (p.1 + p.2) -
        ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2)))) =
      (((1 / (σ * Real.sqrt π) : ℝ) : ℂ) * ((σ * Real.sqrt π : ℝ) : ℂ)) *
        (((f p.1 * f p.2 : ℝ) : ℂ) * cexp (σ ^ 2 * x ^ 2 - x * (p.1 - p.2) -
          I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2))) by ring, h1, one_mul,
    ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The theta source in the `sourceFL` convention is `Ξ`. -/
theorem sourceFL_thetaCuspFullSource (z : ℂ) : sourceFL thetaCuspFullSource z = XiC z :=
  sourceTransform_thetaSourceC z

/-- **Husimi positivity of the height-averaged slice.**  For `σ > 0` and real `t`, `x`,
`e^{σ²x²} ∫ G_σ(t − t′) ξ(½+x+it′) ξ(½−x+it′) dt′ = (σ√π)⁻¹ ∫ e^{2xs} |V_σ(s,t)|² ds`,
with `V_σ` the Gabor transform of the theta source. -/
theorem exp_mul_xiSliceHeightAverage_eq {σ : ℝ} (hσ : 0 < σ) (t x : ℝ) :
    (Real.exp (σ ^ 2 * x ^ 2) : ℂ) * ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) * xiSliceProduct t' x =
      ((1 / (σ * Real.sqrt π) : ℝ) : ℂ) *
        ∫ s : ℝ, cexp (2 * x * s) * (Complex.normSq (gaborAmp thetaCuspFullSource σ t s) : ℂ) := by
  simp_rw [xiSliceProduct_eq_XiC_mul, ← sourceFL_thetaCuspFullSource]
  exact exp_mul_heightAverage_eq hσ contDiff_thetaCuspFullSource.continuous
    thetaCuspFullSource_neg HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource t x

/-- The Husimi moments of the height-averaged slice:
`(σ√π)⁻¹ ∫ (2s)ⁿ/n! |V_σ(s,t)|² ds`. -/
def xiSliceHusimiMoment (σ t : ℝ) (n : ℕ) : ℝ :=
  1 / (σ * Real.sqrt π) *
    ∫ s : ℝ, (2 * s) ^ n / (n.factorial : ℝ) * Complex.normSq (gaborAmp thetaCuspFullSource σ t s)

/-- Every Husimi moment is nonnegative (the odd ones vanish). -/
theorem xiSliceHusimiMoment_nonneg {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHusimiMoment σ t n :=
  mul_nonneg (by positivity) (husimiMoment_nonneg thetaCuspFullSource_neg σ t n)

/-- **All Taylor coefficients of the heated height average are nonnegative.**  For `σ > 0`, every
height `t` and every real `x`,
`e^{σ²x²} ∫ G_σ(t − t′) ξ(½+x+it′) ξ(½−x+it′) dt′ = Σₙ mₙ(σ,t) xⁿ` with
`mₙ(σ,t) = xiSliceHusimiMoment σ t n ≥ 0`. -/
theorem hasSum_exp_mul_xiSliceHeightAverage {σ : ℝ} (hσ : 0 < σ) (t x : ℝ) :
    HasSum (fun n : ℕ => ((xiSliceHusimiMoment σ t n : ℝ) : ℂ) * (x : ℂ) ^ n)
      ((Real.exp (σ ^ 2 * x ^ 2) : ℂ) * ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) *
        xiSliceProduct t' x) := by
  rw [exp_mul_xiSliceHeightAverage_eq hσ t x]
  have h := (hasSum_husimiMoments hσ contDiff_thetaCuspFullSource.continuous
    thetaCuspFullSource_neg HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource t x).mul_left
      (1 / (σ * Real.sqrt π))
  have h3 := Complex.hasSum_ofReal.mpr h
  have hR : ∫ s : ℝ, cexp (2 * x * s) *
      (Complex.normSq (gaborAmp thetaCuspFullSource σ t s) : ℂ) =
      ((∫ s : ℝ, Real.exp (2 * x * s) *
        Complex.normSq (gaborAmp thetaCuspFullSource σ t s) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    push_cast
    rfl
  rw [hR, ← ofReal_mul]
  refine h3.congr_fun fun n => ?_
  simp only [xiSliceHusimiMoment]
  push_cast
  ring

end

end RHTower
