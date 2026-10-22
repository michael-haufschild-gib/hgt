import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussConnectionCoefficient
import GaloisForLFunctions.HTGeometry.CentralBinomialAbelTransfer
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Square-root Gauss endpoint and BM normalizable connection coefficient

The ordinary hypergeometric derivative coefficients at Gauss gap `1/2` obey a half-order Abel
law. Componentwise one-sided l'Hopital transfer converts the derivative edge into the exact
square-root boundary residue. Comparing this residue with the exact AdS connection phase identifies
the Wronskian/Cramer normalizable coefficient with the literal Birmingham--Mokhtari decaying
Gamma/Jost coefficient.
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

theorem tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul_complex
    {u : ℕ → ℂ} {L : ℂ}
    (h : Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) * u n) atTop (𝓝 L))
    (hsum : ∀ x : ℝ, x ∈ Ico (0 : ℝ) 1 →
      Summable (fun n : ℕ => u n * (x : ℂ) ^ n)) :
    Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) *
        ∑' n : ℕ, u n * (x : ℂ) ^ n)
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 ((Real.sqrt Real.pi : ℂ) * L)) := by
  have hreCoeff : Tendsto (fun n : ℕ => Real.sqrt n * (u n).re)
      atTop (𝓝 L.re) := by
    have hreRaw := (Complex.continuous_re.tendsto L).comp h
    convert hreRaw using 1
    funext n
    simp [Function.comp_apply, Complex.mul_re]
  have himCoeff : Tendsto (fun n : ℕ => Real.sqrt n * (u n).im)
      atTop (𝓝 L.im) := by
    have himRaw := (Complex.continuous_im.tendsto L).comp h
    convert himRaw using 1
    funext n
    simp [Function.comp_apply, Complex.mul_im]
  have hre := tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul hreCoeff
  have him := tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul himCoeff
  have hreC := hre.ofReal
  have himC := him.ofReal.const_mul Complex.I
  have hcomb := hreC.add himC
  have hcomb' : Tendsto
      (fun x : ℝ =>
        ((Real.sqrt (1 - x) * ∑' n : ℕ, (u n).re * x ^ n : ℝ) : ℂ) +
          Complex.I *
            ((Real.sqrt (1 - x) * ∑' n : ℕ, (u n).im * x ^ n : ℝ) : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 ((Real.sqrt Real.pi : ℂ) * L)) := by
    have hlim :
        (Real.sqrt Real.pi : ℂ) * L =
          (Real.sqrt Real.pi * L.re : ℝ) +
            Complex.I * (Real.sqrt Real.pi * L.im : ℝ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hlim]
    exact hcomb
  apply hcomb'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hs := hsum x hx
  have hreSum :
      (∑' n : ℕ, u n * (x : ℂ) ^ n).re =
        ∑' n : ℕ, (u n).re * x ^ n := by
    rw [← (Complex.hasSum_re hs.hasSum).tsum_eq]
    apply tsum_congr
    intro n
    have hpow : (x : ℂ) ^ n = (x ^ n : ℝ) :=
      (Complex.ofReal_pow x n).symm
    rw [hpow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have himSum :
      (∑' n : ℕ, u n * (x : ℂ) ^ n).im =
        ∑' n : ℕ, (u n).im * x ^ n := by
    rw [← (Complex.hasSum_im hs.hasSum).tsum_eq]
    apply tsum_congr
    intro n
    have hpow : (x : ℂ) ^ n = (x ^ n : ℝ) :=
      (Complex.ofReal_pow x n).symm
    rw [hpow, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, hreSum, himSum]

/-- Complex-valued square-root endpoint transfer from a derivative edge. The proof applies the
real one-sided l'Hopital theorem to real and imaginary components separately. -/
theorem tendsto_sub_div_sqrt_one_sub_of_derivative_edge
    {F F' : ℝ → ℂ} {A B : ℂ}
    (hderiv : ∀ᶠ x in 𝓝[<] (1 : ℝ), HasDerivAt F (F' x) x)
    (hF : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 A))
    (hedge : Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) * F' x)
      (𝓝[<] (1 : ℝ)) (𝓝 B)) :
    Tendsto (fun x : ℝ => (F x - A) / (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B)) := by
  let g : ℝ → ℝ := fun x => Real.sqrt (1 - x)
  let g' : ℝ → ℝ := fun x => (1 / (2 * Real.sqrt (1 - x))) * (-1)
  have hgderiv : ∀ᶠ x in 𝓝[<] (1 : ℝ), HasDerivAt g (g' x) x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hw : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
    have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hcomp := (Real.hasDerivAt_sqrt hw).comp x hinner
    simpa only [g, g', Function.comp_def] using hcomp
  have hg' : ∀ᶠ x in 𝓝[<] (1 : ℝ), g' x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsqrt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (sub_pos.mpr hx)
    dsimp only [g']
    positivity
  have hg : Tendsto g (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => Real.sqrt (1 - x)) 1 := by fun_prop
    change Tendsto g (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 0)
    simpa only [g, sub_self, Real.sqrt_zero] using hcont.tendsto.mono_left inf_le_left
  have hreDeriv : ∀ᶠ x in 𝓝[<] (1 : ℝ),
      HasDerivAt (fun y : ℝ => (F y - A).re) (F' x).re x := by
    filter_upwards [hderiv] with x hx
    have hsub := hx.sub_const A
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hsub
  have himDeriv : ∀ᶠ x in 𝓝[<] (1 : ℝ),
      HasDerivAt (fun y : ℝ => (F y - A).im) (F' x).im x := by
    filter_upwards [hderiv] with x hx
    have hsub := hx.sub_const A
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hsub
  have hreF : Tendsto (fun x : ℝ => (F x - A).re)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hproj := (Complex.continuous_re.tendsto A).comp hF
    have hconst : Tendsto (fun _ : ℝ => A.re) (𝓝[<] (1 : ℝ)) (𝓝 A.re) :=
      tendsto_const_nhds
    have hsub := hproj.sub hconst
    simpa only [Function.comp_def, Complex.sub_re, sub_self] using hsub
  have himF : Tendsto (fun x : ℝ => (F x - A).im)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hproj := (Complex.continuous_im.tendsto A).comp hF
    have hconst : Tendsto (fun _ : ℝ => A.im) (𝓝[<] (1 : ℝ)) (𝓝 A.im) :=
      tendsto_const_nhds
    have hsub := hproj.sub hconst
    simpa only [Function.comp_def, Complex.sub_im, sub_self] using hsub
  have hreEdge : Tendsto (fun x : ℝ => Real.sqrt (1 - x) * (F' x).re)
      (𝓝[<] (1 : ℝ)) (𝓝 B.re) := by
    have hproj := (Complex.continuous_re.tendsto B).comp hedge
    simpa [Function.comp_def, Complex.mul_re] using hproj
  have himEdge : Tendsto (fun x : ℝ => Real.sqrt (1 - x) * (F' x).im)
      (𝓝[<] (1 : ℝ)) (𝓝 B.im) := by
    have hproj := (Complex.continuous_im.tendsto B).comp hedge
    simpa [Function.comp_def, Complex.mul_im] using hproj
  have hreRatio : Tendsto (fun x : ℝ => (F' x).re / g' x)
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B.re)) := by
    have hscaled := hreEdge.const_mul (-2 : ℝ)
    apply hscaled.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsqrt : Real.sqrt (1 - x) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hx))
    dsimp only [g']
    field_simp
  have himRatio : Tendsto (fun x : ℝ => (F' x).im / g' x)
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B.im)) := by
    have hscaled := himEdge.const_mul (-2 : ℝ)
    apply hscaled.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsqrt : Real.sqrt (1 - x) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hx))
    dsimp only [g']
    field_simp
  have hreQuot : Tendsto (fun x : ℝ => (F x - A).re / g x)
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B.re)) :=
    HasDerivAt.lhopital_zero_nhdsLT hreDeriv hgderiv hg' hreF hg hreRatio
  have himQuot : Tendsto (fun x : ℝ => (F x - A).im / g x)
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B.im)) :=
    HasDerivAt.lhopital_zero_nhdsLT himDeriv hgderiv hg' himF hg himRatio
  have hcomplex := hreQuot.ofReal.add (himQuot.ofReal.const_mul Complex.I)
  have hcomplex' : Tendsto
      (fun x : ℝ => ((F x - A).re / g x : ℝ) +
        Complex.I * ((F x - A).im / g x : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 (-2 * B)) := by
    have hlim : -2 * B =
        ((-2 * B.re : ℝ) : ℂ) + Complex.I * ((-2 * B.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hlim]
    exact hcomplex
  apply hcomplex'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  apply Complex.ext <;>
    simp [g, Complex.div_re, Complex.div_im]

/-- At Gauss gap `1/2`, the derivative-series coefficients have exact square-root
normalization. -/
theorem tendsto_sqrtNat_mul_shifted_ordinaryHypergeometricCoefficient_of_gap_half
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : c - a - b = 1 / 2) :
    Tendsto
      (fun n : ℕ => (Real.sqrt n : ℂ) *
        ((n + 1 : ℕ) : ℂ) *
          ordinaryHypergeometricCoefficient a b c (n + 1))
      atTop
      (𝓝 (Complex.Gamma c / (Complex.Gamma a * Complex.Gamma b))) := by
  have hnorm := tendsto_normalized_ordinaryHypergeometricCoefficient a b c ha hb hc
  apply hnorm.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : (Real.sqrt n : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hhalf]
    change ((Real.sqrt (n : ℝ) : ℝ) : ℂ) =
      ((n : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnpos.le]
  rw [hgap, hsqrt]
  push_cast
  rfl

/-- BM specialization of the square-root derivative-coefficient law. -/
theorem tendsto_d4BMPlusPlusRegularDerivativeCoefficient_sqrtNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun j : ℕ => (Real.sqrt j : ℂ) * ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricCoefficient
          (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
          (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) (j + 1))
      atTop
      (𝓝 (Complex.Gamma
            (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
          (Complex.Gamma
              (d4BMCausalHypergeometricA
                (d4BMCausalPlusPlusFrequency n chi) chi) *
            Complex.Gamma
              (d4BMCausalHypergeometricB
                (d4BMCausalPlusPlusFrequency n chi) chi)))) := by
  have hp (j : ℕ) :=
    d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j
  exact tendsto_sqrtNat_mul_shifted_ordinaryHypergeometricCoefficient_of_gap_half
    _ _ _ (fun j => (hp j).1) (fun j => (hp j).2.1) (fun j => (hp j).2.2)
    (d4BMPlusPlusHypergeometric_gaussGap n chi)

/-- The BM regular derivative has the exact half-order Abel edge constant. -/
theorem tendsto_sqrt_one_sub_mul_d4BMPlusPlusRegularHypergeometricSolutionDerivative
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) *
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 ((Real.sqrt Real.pi : ℂ) *
        (Complex.Gamma
              (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
          (Complex.Gamma
                (d4BMCausalHypergeometricA
                  (d4BMCausalPlusPlusFrequency n chi) chi) *
            Complex.Gamma
                (d4BMCausalHypergeometricB
                  (d4BMCausalPlusPlusFrequency n chi) chi))))) := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  let u : ℕ → ℂ := fun j => ((j + 1 : ℕ) : ℂ) *
    ordinaryHypergeometricCoefficient a b c (j + 1)
  let L := Complex.Gamma c / (Complex.Gamma a * Complex.Gamma b)
  have hcoeff : Tendsto (fun j : ℕ => (Real.sqrt j : ℂ) * u j)
      atTop (𝓝 L) := by
    simpa only [u, L, a, b, c, mul_assoc] using
      tendsto_d4BMPlusPlusRegularDerivativeCoefficient_sqrtNat n chi hchi
  have hsum : ∀ x : ℝ, x ∈ Ico (0 : ℝ) 1 →
      Summable (fun j : ℕ => u j * (x : ℂ) ^ j) := by
    intro x hx
    have hxnorm : ‖(x : ℂ)‖ₑ < 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx.1]
      exact ENNReal.ofReal_lt_one.mpr hx.2
    have hrad : (ordinaryHypergeometricSeries ℂ a b c).radius = 1 := by
      change (d4BMPlusPlusRegularHypergeometricSeries n chi).radius = 1
      exact d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one n chi hchi
    have hz : ‖(x : ℂ)‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
      rw [hrad]
      exact hxnorm
    have hs := (ordinaryHypergeometric_hasSum_value_first_second
      a b c (x : ℂ) hz).2.1
    simpa only [u, ordinaryHypergeometricFormalCoefficient] using hs.summable
  have habel := tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul_complex hcoeff hsum
  have htarget : Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) *
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 ((Real.sqrt Real.pi : ℂ) * L)) := by
    apply habel.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxnorm : ‖(x : ℂ)‖ₑ < 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx.1]
      exact ENNReal.ofReal_lt_one.mpr hx.2
    have hrad : (ordinaryHypergeometricSeries ℂ a b c).radius = 1 := by
      change (d4BMPlusPlusRegularHypergeometricSeries n chi).radius = 1
      exact d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one n chi hchi
    have hz : ‖(x : ℂ)‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
      rw [hrad]
      exact hxnorm
    have hs := (ordinaryHypergeometric_hasSum_value_first_second
      a b c (x : ℂ) hz).2.1
    congr 1
    change (∑' j : ℕ, ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricCoefficient a b c (j + 1) * (x : ℂ) ^ j) =
      ordinaryHypergeometricFirstDerivativeSeriesValue a b c (x : ℂ)
    simpa only [ordinaryHypergeometricFormalCoefficient] using hs.tsum_eq
  simpa only [L, a, b, c] using htarget

/-- The first nonconstant BM boundary term is the exact square-root Gauss coefficient. -/
theorem tendsto_d4BMPlusPlusRegular_sub_forbidden_div_sqrt_one_sub
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ) -
            d4BMCausalForbiddenBoundaryCoefficient
              (d4BMCausalPlusPlusFrequency n chi) chi) /
          (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (-2 * (Real.sqrt Real.pi : ℂ) *
        (Complex.Gamma
              (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
          (Complex.Gamma
                (d4BMCausalHypergeometricA
                  (d4BMCausalPlusPlusFrequency n chi) chi) *
            Complex.Gamma
                (d4BMCausalHypergeometricB
                  (d4BMCausalPlusPlusFrequency n chi) chi))))) := by
  let F : ℝ → ℂ := fun x =>
    d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ)
  let F' : ℝ → ℂ := fun x =>
    d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)
  let A := d4BMCausalForbiddenBoundaryCoefficient
    (d4BMCausalPlusPlusFrequency n chi) chi
  let L := Complex.Gamma
      (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
    (Complex.Gamma
          (d4BMCausalHypergeometricA
            (d4BMCausalPlusPlusFrequency n chi) chi) *
      Complex.Gamma
          (d4BMCausalHypergeometricB
            (d4BMCausalPlusPlusFrequency n chi) chi))
  have hpos : ∀ᶠ x in 𝓝[<] (1 : ℝ), 0 < x := by
    have h : ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have hderiv : ∀ᶠ x in 𝓝[<] (1 : ℝ), HasDerivAt F (F' x) x := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx1 hx0
    have hxnorm : ‖(x : ℂ)‖ₑ < 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx0.le]
      exact ENNReal.ofReal_lt_one.mpr hx1
    simpa only [F, F'] using
      (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution
        n chi (x : ℂ) hchi hxnorm).comp_ofReal
  have hF : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 A) := by
    simpa only [F, A] using
      tendsto_d4BMPlusPlusRegularHypergeometricSolution_one n chi hchi
  have hedge : Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) * F' x)
      (𝓝[<] (1 : ℝ)) (𝓝 ((Real.sqrt Real.pi : ℂ) * L)) := by
    have h :=
      tendsto_sqrt_one_sub_mul_d4BMPlusPlusRegularHypergeometricSolutionDerivative
        n chi hchi
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)] at h
    simpa only [F', L] using h
  have h := tendsto_sub_div_sqrt_one_sub_of_derivative_edge
    hderiv hF hedge
  simpa only [F, A, L, mul_assoc] using h

/-- The analytic forbidden branch has no square-root boundary residue. -/
theorem tendsto_d4BMPlusPlusAdSForbiddenSolution_sub_one_div_sqrt_one_sub
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (d4BMPlusPlusAdSForbiddenSolution n chi x - 1) /
          (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  let F := d4BMPlusPlusAdSForbiddenSolution n chi
  let F' := d4BMPlusPlusAdSForbiddenSolutionDerivative n chi
  have hpos : ∀ᶠ x in 𝓝[<] (1 : ℝ), 0 < x := by
    have h : ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have hderiv : ∀ᶠ x in 𝓝[<] (1 : ℝ), HasDerivAt F (F' x) x := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx1 hx0
    exact hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hx0 hx1
  have hF : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [F] using tendsto_d4BMPlusPlusAdSForbiddenSolution_one n chi hchi
  have hsqrt : Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ)) 1 := by
      fun_prop
    change Tendsto (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) (𝓝 (0 : ℂ))
    simpa using hcont.tendsto.mono_left inf_le_left
  have hfd0 := (hasDerivAt_d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative
    n chi 0 hchi (by simp)).continuousAt
  have hw : ContinuousAt (fun x : ℝ => ((1 - x : ℝ) : ℂ)) 1 := by fun_prop
  have hfdC : ContinuousAt
      (fun x : ℝ =>
        d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
          ((1 - x : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hfd0.comp_of_eq hw (by norm_num)
  have hfd : Tendsto
      (fun x : ℝ =>
        d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
          ((1 - x : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi 0)) := by
    change Tendsto _ (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) _
    have ht := hfdC.tendsto.mono_left
      (show 𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from inf_le_left)
    simpa using ht
  have hF' : Tendsto F' (𝓝[<] (1 : ℝ))
      (𝓝 (-d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi 0)) := by
    change Tendsto
      (fun x : ℝ =>
        -d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi
          ((1 - x : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (-d4BMPlusPlusAdSForbiddenHypergeometricFirstDerivative n chi 0))
    exact hfd.neg
  have hedge : Tendsto
      (fun x : ℝ => (Real.sqrt (1 - x) : ℂ) * F' x)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [zero_mul] using hsqrt.mul hF'
  have h := tendsto_sub_div_sqrt_one_sub_of_derivative_edge
    hderiv hF hedge
  simpa only [F, mul_zero, neg_zero] using h

/-- The normalizable AdS branch has unit square-root boundary residue. -/
theorem tendsto_d4BMPlusPlusAdSNormalizableSolution_div_sqrt_one_sub
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (fun x : ℝ => d4BMPlusPlusAdSNormalizableSolution n chi x /
        (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hV0 := (hasDerivAt_d4BMPlusPlusAdSNormalizableHypergeometricFactor
    n chi 0 hchi (by simp)).continuousAt
  have hw : ContinuousAt (fun x : ℝ => ((1 - x : ℝ) : ℂ)) 1 := by fun_prop
  have hVC : ContinuousAt
      (fun x : ℝ => d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
        ((1 - x : ℝ) : ℂ)) 1 := by
    simpa only [Function.comp_def] using hV0.comp_of_eq hw (by norm_num)
  have hV : Tendsto
      (fun x : ℝ => d4BMPlusPlusAdSNormalizableHypergeometricFactor n chi
        ((1 - x : ℝ) : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    change Tendsto _ (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ))) _
    have ht := hVC.tendsto.mono_left
      (show 𝓝 (1 : ℝ) ⊓ 𝓟 (Iio (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from inf_le_left)
    simpa using ht
  apply hV.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hsqrt : (Real.sqrt (1 - x) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hx))
  rw [d4BMPlusPlusAdSNormalizableSolution,
    d4BMPlusPlusAdSLeadingNormalizableBranch_eq_sqrt hx]
  field_simp

/-- The Wronskian-defined normalizable connection coefficient is the literal square-root edge
constant extracted from the regular Gauss series. -/
theorem d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq_sqrt_gamma_ratio
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi =
      -2 * (Real.sqrt Real.pi : ℂ) *
        (Complex.Gamma
              (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
          (Complex.Gamma
                (d4BMCausalHypergeometricA
                  (d4BMCausalPlusPlusFrequency n chi) chi) *
            Complex.Gamma
                (d4BMCausalHypergeometricB
                  (d4BMCausalPlusPlusFrequency n chi) chi))) := by
  let A := d4BMCausalForbiddenBoundaryCoefficient
    (d4BMCausalPlusPlusFrequency n chi) chi
  let CN := d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi
  let L := Complex.Gamma
      (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) /
    (Complex.Gamma
          (d4BMCausalHypergeometricA
            (d4BMCausalPlusPlusFrequency n chi) chi) *
      Complex.Gamma
          (d4BMCausalHypergeometricB
            (d4BMCausalPlusPlusFrequency n chi) chi))
  have hleft : Tendsto
      (fun x : ℝ =>
        (d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ) - A) /
          (Real.sqrt (1 - x) : ℂ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (-2 * (Real.sqrt Real.pi : ℂ) * L)) := by
    simpa only [A, L] using
      tendsto_d4BMPlusPlusRegular_sub_forbidden_div_sqrt_one_sub n chi hchi
  have hS :=
    tendsto_d4BMPlusPlusAdSForbiddenSolution_sub_one_div_sqrt_one_sub
      n chi hchi
  have hN := tendsto_d4BMPlusPlusAdSNormalizableSolution_div_sqrt_one_sub
    n chi hchi
  have hA : Tendsto (fun _ : ℝ => A) (𝓝[<] (1 : ℝ)) (𝓝 A) :=
    tendsto_const_nhds
  have hCN : Tendsto (fun _ : ℝ => CN) (𝓝[<] (1 : ℝ)) (𝓝 CN) :=
    tendsto_const_nhds
  have hright : Tendsto
      (fun x : ℝ =>
        A * ((d4BMPlusPlusAdSForbiddenSolution n chi x - 1) /
              (Real.sqrt (1 - x) : ℂ)) +
          CN * (d4BMPlusPlusAdSNormalizableSolution n chi x /
              (Real.sqrt (1 - x) : ℂ)))
      (𝓝[<] (1 : ℝ)) (𝓝 CN) := by
    have h := (hA.mul hS).add (hCN.mul hN)
    simpa only [mul_zero, mul_one, zero_add] using h
  have hpos : ∀ᶠ x in 𝓝[<] (1 : ℝ), 0 < x := by
    have h : ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x := Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  have heq :
      (fun x : ℝ =>
        (d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ) - A) /
          (Real.sqrt (1 - x) : ℂ)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun x : ℝ =>
        A * ((d4BMPlusPlusAdSForbiddenSolution n chi x - 1) /
              (Real.sqrt (1 - x) : ℂ)) +
          CN * (d4BMPlusPlusAdSNormalizableSolution n chi x /
              (Real.sqrt (1 - x) : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hx1 hx0
    have hsqrt : (Real.sqrt (1 - x) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hx1))
    have hphase := (d4BMPlusPlusRegularAdSConnection_phase
      n chi hchi hx0 hx1).1
    rw [d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_eq
      n chi hchi] at hphase
    change d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ) =
      A * d4BMPlusPlusAdSForbiddenSolution n chi x +
        CN * d4BMPlusPlusAdSNormalizableSolution n chi x at hphase
    rw [hphase]
    field_simp
    ring
  have hright' := hright.congr' heq.symm
  have hCNedge : CN = -2 * (Real.sqrt Real.pi : ℂ) * L :=
    tendsto_nhds_unique hright' hleft
  simpa only [CN, L] using hCNedge

theorem gamma_neg_half_eq_neg_two_mul_sqrt_pi :
    Complex.Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt Real.pi : ℂ) := by
  rw [gamma_neg_half_eq_neg_two_mul_gamma_half, Complex.Gamma_one_half_eq]
  have hsqrt : (Real.sqrt Real.pi : ℂ) =
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hhalf]
    change ((Real.sqrt Real.pi : ℝ) : ℂ) =
      (Real.pi : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  rw [← hsqrt]

/-- Exact Gauss connection theorem: the Wronskian/Cramer normalizable coefficient equals the
literal Birmingham--Mokhtari decaying Gamma/Jost coefficient. -/
theorem d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi =
      d4BMCausalDecayingBoundaryCoefficient
        (d4BMCausalPlusPlusFrequency n chi) chi := by
  rw [d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq_sqrt_gamma_ratio
    n chi hchi, d4BMCausalDecayingBoundaryCoefficient,
    gamma_neg_half_eq_neg_two_mul_sqrt_pi]
  rw [div_eq_mul_inv]
  ring

end
end RHTower
