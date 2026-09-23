import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent
import GaloisForLFunctions.RHTower.XiUnitEulerPoleBezoutianSufficiency
import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry

/-!
# The critical Xi Bezoutian is the pointed global incidence kernel

Clearing the completed logarithmic derivative by the centred trace `X (w) = ξ (1/2 + w)` produces
the Hermitian Bezoutian

```
B_X (w, v) = (X' w · conj (X v) + X w · conj (X' v)) / (w + conj v).
```

Written in the holomorphic variable `y = conj v` the numerator vanishes on the antidiagonal
`y = -w`, because `X` is even and `X'` is odd, so the quotient extends to an entire function of `y`.
On the Euler half plane `Re w > 1/2` the trace is zero-free, so the diagonal congruence by
`diag (X w_j)` identifies positivity of the Bezoutian with positivity of the critical
logarithmic-derivative kernel; by the two-channel complete-detector theorem this is exactly the
Riemann hypothesis, and the Bezoutian is the completed two-channel Weil Gram.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace RHTower

/-! ### Evenness, Schwarz reality, and their first jets -/

theorem xiCent_even (W : ℂ) : xiCent (-W) = xiCent W := by
  rw [xiCent, xiCent, show (1 : ℂ) / 2 + -W = 1 - (1 / 2 + W) by ring, xi_one_sub]

theorem deriv_xiCent_neg (W : ℂ) : deriv xiCent (-W) = -deriv xiCent W := by
  have hfun : (fun u : ℂ => xiCent (-u)) = xiCent := by
    funext u
    exact xiCent_even u
  have hcomp : HasDerivAt (fun u : ℂ => xiCent (-u)) (deriv xiCent (-W) * (-1)) W := by
    have h := (xiCent_differentiable (-W)).hasDerivAt.comp W (hasDerivAt_neg W)
    simpa [Function.comp_def] using h
  rw [hfun] at hcomp
  have huniq := hcomp.unique (xiCent_differentiable W).hasDerivAt
  linear_combination -huniq

theorem deriv_xiCent_eq_shift (W : ℂ) : deriv xiCent W = deriv xi (1 / 2 + W) := by
  have hfun : xiCent = fun W : ℂ => xi (1 / 2 + W) := rfl
  rw [hfun, deriv_comp_const_add]

theorem xiCent_conj (W : ℂ) : xiCent (conj W) = conj (xiCent W) := by
  have hhalf : conj ((1 : ℂ) / 2 + W) = 1 / 2 + conj W := by
    rw [map_add, show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [xiCent, xiCent, ← hhalf, xi_conj]

theorem deriv_xiCent_conj (W : ℂ) : deriv xiCent (conj W) = conj (deriv xiCent W) := by
  have hhalf : conj ((1 : ℂ) / 2 + W) = 1 / 2 + conj W := by
    rw [map_add, show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [deriv_xiCent_eq_shift, deriv_xiCent_eq_shift, ← hhalf, deriv_xi_conj]

/-! ### The entire Bezoutian -/

/-- **Equation (3).**  The Bezoutian numerator in the holomorphic variable `y = conj v`. -/
def xiCentBezoutianNumerator (w y : ℂ) : ℂ :=
  deriv xiCent w * xiCent y + xiCent w * deriv xiCent y

/-- **Equation (4).**  The numerator vanishes on the antidiagonal. -/
theorem xiCentBezoutianNumerator_antidiagonal (w : ℂ) :
    xiCentBezoutianNumerator w (-w) = 0 := by
  rw [xiCentBezoutianNumerator, xiCent_even, deriv_xiCent_neg]
  ring

/-- **Equation (2).**  The Bezoutian, defined across the antidiagonal by the divided difference. -/
def xiCentBezoutian (w y : ℂ) : ℂ := dslope (xiCentBezoutianNumerator w) (-w) y

theorem xiCentBezoutian_eq_div {w y : ℂ} (h : w + y ≠ 0) :
    xiCentBezoutian w y = xiCentBezoutianNumerator w y / (w + y) := by
  have hne : y ≠ -w := by
    intro hy
    apply h
    rw [hy]
    ring
  rw [xiCentBezoutian, dslope_of_ne _ hne, slope_def_module,
    xiCentBezoutianNumerator_antidiagonal, sub_zero, smul_eq_mul]
  have hsub : y - -w = w + y := by ring
  rw [hsub, ← div_eq_inv_mul]

/-- **Removability.**  The Bezoutian is entire in the holomorphic variable. -/
theorem differentiable_xiCentBezoutian (w : ℂ) : Differentiable ℂ (xiCentBezoutian w) := by
  have hnum : Differentiable ℂ (xiCentBezoutianNumerator w) := by
    have hd : Differentiable ℂ (deriv xiCent) := fun z =>
      ((xiCent_analytic z (Set.mem_univ z)).deriv).differentiableAt
    exact (Differentiable.const_mul xiCent_differentiable _).add
      (Differentiable.const_mul hd _)
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (by simp)).mpr hnum.differentiableOn

/-- The Bezoutian is the value-fibre Bezoutian of the corpus at the marked origin. -/
theorem xiCentBezoutian_eq_xiTranslatedBezoutian {w v : ℂ} (h : w + conj v ≠ 0) :
    xiCentBezoutian w (conj v) = xiTranslatedBezoutian 0 w v := by
  have hfun : xiTranslatedCentered 0 = xiCent := by
    funext u
    exact (xiCent_eq u).symm
  rw [xiCentBezoutian_eq_div h, xiCentBezoutianNumerator, xiTranslatedBezoutian, hfun,
    xiCent_conj, deriv_xiCent_conj]

/-- **Equation (5).**  The Bezoutian is the trace-cleared critical logarithmic-derivative
kernel. -/
theorem xiCentBezoutian_eq_mul_criticalKernel {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    xiCentBezoutian w (conj v)
      = xiCent w * conj (xiCent v) * criticalLogDerivKernel w v := by
  have hsum : w + conj v ≠ 0 := add_conj_ne_zero (by linarith) (by linarith)
  have hxw : xiCent w ≠ 0 := xiCent_ne_zero_of_half_lt_re hw
  have hxv : xiCent v ≠ 0 := xiCent_ne_zero_of_half_lt_re hv
  have hcv : conj (xiCent v) ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hxv
  rw [xiCentBezoutian_eq_div hsum, xiCentBezoutianNumerator, criticalLogDerivKernel,
    xiCent_conj, deriv_xiCent_conj, logDeriv_apply, logDeriv_apply, map_div₀]
  field_simp

/-! ### Equation (7): Euler-half-plane positivity is the Riemann hypothesis -/

/-- **Equation (7).**  Positivity of the entire Bezoutian at every finite node system of the Euler
half plane is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_posSemidef_xiCentBezoutian :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        (Matrix.of fun j k =>
          xiCentBezoutian ((w j : ℂ)) (conj ((w k : ℂ)))).PosSemidef := by
  rw [riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel (le_refl (1 / 2 : ℝ))]
  constructor
  · intro hK n w
    have hcong := posSemidef_congr_diagonal (hK.posSemidef w) (fun j => xiCent ((w j : ℂ)))
    have heq : (Matrix.of fun j k => xiCent ((w j : ℂ)) *
          (Matrix.of fun j k : Fin n =>
            criticalLogDerivKernel ((w j : ℂ)) ((w k : ℂ))) j k *
          conj (xiCent ((w k : ℂ))))
        = Matrix.of fun j k => xiCentBezoutian ((w j : ℂ)) (conj ((w k : ℂ))) := by
      ext j k
      simp only [Matrix.of_apply]
      rw [xiCentBezoutian_eq_mul_criticalKernel (w j).2 (w k).2]
      ring
    rwa [heq] at hcong
  · intro hmat
    refine isPSDKernel_of_forall_posSemidef (fun x y => criticalLogDerivKernel_conj_symm _ _)
      (fun n w => ?_)
    have hcong := posSemidef_congr_diagonal (hmat n w) (fun j => (xiCent ((w j : ℂ)))⁻¹)
    have heq : (Matrix.of fun j k => (xiCent ((w j : ℂ)))⁻¹ *
          (Matrix.of fun j k : Fin n =>
            xiCentBezoutian ((w j : ℂ)) (conj ((w k : ℂ)))) j k *
          conj ((xiCent ((w k : ℂ)))⁻¹))
        = Matrix.of fun j k => criticalLogDerivKernel ((w j : ℂ)) ((w k : ℂ)) := by
      ext j k
      simp only [Matrix.of_apply]
      have h1 : xiCent ((w j : ℂ)) ≠ 0 := xiCent_ne_zero_of_half_lt_re (w j).2
      have h2 : xiCent ((w k : ℂ)) ≠ 0 := xiCent_ne_zero_of_half_lt_re (w k).2
      have h2c : conj (xiCent ((w k : ℂ))) ≠ 0 := by
        simpa using (map_ne_zero (starRingEnd ℂ)).mpr h2
      rw [xiCentBezoutian_eq_mul_criticalKernel (w j).2 (w k).2, map_inv₀]
      field_simp
    rwa [heq] at hcong

/-! ### Equations (10)-(12): the completed two-channel Weil identity -/

/-- **Equation (10).**  The Bezoutian is the completed two-channel polarized Weil Gram. -/
theorem xiCentBezoutian_eq_twoChannelWeil {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    xiCentBezoutian w (conj v)
      = xiWeilPolarization (fun z => xiCent w * weilChannelA w z)
            (fun z => xiCent v * weilChannelA v z)
        + xiWeilPolarization (fun z => xiCent w * weilChannelB w z)
            (fun z => xiCent v * weilChannelB v z) := by
  rw [xiWeilPolarization_const_smul_left, xiWeilPolarization_const_smul_right,
    xiWeilPolarization_const_smul_left, xiWeilPolarization_const_smul_right,
    xiCentBezoutian_eq_mul_criticalKernel hw hv, criticalLogDerivKernel_eq_twoChannel hw hv]
  ring

theorem channel_pair_value {w u z : ℂ} (hw : w ^ (2 : ℕ) + z ^ (2 : ℕ) ≠ 0) (hu : u ^ (2 : ℕ) + z ^ (2 : ℕ) ≠ 0) :
    weilChannelA w z * weilChannelA u z + weilChannelB w z * weilChannelB u z
      = (w * u + z ^ (2 : ℕ)) / ((w ^ (2 : ℕ) + z ^ (2 : ℕ)) * (u ^ (2 : ℕ) + z ^ (2 : ℕ))) := by
  simp only [weilChannelA, weilChannelB]
  field_simp

/-- **Equation (11).**  The explicit divisor expansion of the Bezoutian. -/
theorem xiCentBezoutian_eq_tsum {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    xiCentBezoutian w (conj v)
      = ∑' q : XiZeroCopy, xiCent w * conj (xiCent v)
          * ((w * conj v + xiSpectralPoint q ^ (2 : ℕ))
            / ((w ^ (2 : ℕ) + xiSpectralPoint q ^ (2 : ℕ)) * ((conj v) ^ (2 : ℕ) + xiSpectralPoint q ^ (2 : ℕ)))) := by
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  have hA := summable_channelA_mul w (conj v)
  have hB := summable_channelB_mul w (conj v)
  rw [xiCentBezoutian_eq_mul_criticalKernel hw hv, criticalLogDerivKernel_eq_twoChannel hw hv]
  simp only [xiWeilPolarization, xiWeilSharp_channelA, xiWeilSharp_channelB]
  rw [← Summable.tsum_add hA hB, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [channel_pair_value (sq_add_spectral_sq_ne_zero hw q) (sq_add_spectral_sq_ne_zero hcv q)]

/-- The even entire feature channel `(12)`. -/
def xiFeatureChannelEven (q : XiZeroCopy) (w : ℂ) : ℂ :=
  xiCent w * weilChannelA w (xiSpectralPoint q)

/-- The odd entire feature channel `(12)`. -/
def xiFeatureChannelOdd (q : XiZeroCopy) (w : ℂ) : ℂ :=
  xiCent w * weilChannelB w (xiSpectralPoint q)

/-- **Equation (12).**  Under the Riemann hypothesis the Bezoutian is the positive Gram sum of the
two entire feature channels of the divisor. -/
theorem xiCentBezoutian_eq_featureGram_of_riemannHypothesis (hRH : RiemannHypothesis)
    {w v : ℂ} (hw : 1 / 2 < w.re) (hv : 1 / 2 < v.re) :
    xiCentBezoutian w (conj v)
      = ∑' q : XiZeroCopy, (xiFeatureChannelEven q w * conj (xiFeatureChannelEven q v)
          + xiFeatureChannelOdd q w * conj (xiFeatureChannelOdd q v)) := by
  rw [xiCentBezoutian_eq_tsum hw hv]
  refine tsum_congr fun q => ?_
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hconjq : conj (xiSpectralPoint q) = xiSpectralPoint q := by
    rw [ht, Complex.conj_ofReal]
  have hne : (w : ℂ) ^ (2 : ℕ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := sq_add_spectral_sq_ne_zero hw q
  have hcv : 1 / 2 < (conj v).re := by
    rwa [Complex.conj_re]
  have hnev : (conj v : ℂ) ^ (2 : ℕ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := sq_add_spectral_sq_ne_zero hcv q
  simp only [xiFeatureChannelEven, xiFeatureChannelOdd, weilChannelA, weilChannelB, map_mul,
    map_div₀, map_add, map_pow, hconjq]
  field_simp

/-! ### Equation (16): a source Gram factorization proves RH -/

/-- **Equation (16).**  If the entire Bezoutian is the Gram kernel of source-defined vectors on the
Euler half plane, the Riemann hypothesis holds.  Compatibility under enlargement of finite node sets
is automatic in the Hilbert-space formulation. -/
theorem riemannHypothesis_of_bezoutianGram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (R : {W : ℂ // 1 / 2 < W.re} → H)
    (hR : ∀ x y : {W : ℂ // 1 / 2 < W.re},
      xiCentBezoutian ((x : ℂ)) (conj ((y : ℂ))) = ⟪R y, R x⟫_ℂ) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_posSemidef_xiCentBezoutian.mpr fun n w => ?_
  have hgram := (isPSDKernel_gram R).posSemidef w
  have heq : (Matrix.of fun j k => ⟪R (w k), R (w j)⟫_ℂ)
      = Matrix.of fun j k => xiCentBezoutian ((w j : ℂ)) (conj ((w k : ℂ))) := by
    ext j k
    rw [Matrix.of_apply, Matrix.of_apply, hR]
  rwa [heq] at hgram

end RHTower
