import GaloisForLFunctions.HTGeometry.OneSidedFeatureGramIsometry
import GaloisForLFunctions.HTGeometry.FourierCircleTruncation
import GaloisForLFunctions.RHTower.DetectorDuality
import GaloisForLFunctions.RHTower.GaussOnePrimeReducedDefectEnergy

/-!
# Correctly normalized Connes--Consani prime source features

The literal circle multiplier `B_p` has squared modulus `p^(1-x)`.  This file proves directly that
its Fourier-feature Gram matrix is

`⟪B_p e_m, B_p e_n⟫ = (p-1) / (log p + 2πi(m-n))`.

Dividing these features by `sqrt (p-1)` gives the Cauchy Gram matrix intended in
Connes--Consani Lemma 3.3.  The normalized features remain total: self-adjointness moves `B_p`
onto an annihilating vector, Fourier completeness kills the result, and pointwise positivity makes
`B_p` injective.  These facts supply the exact source side of the corrected Hardy isometry.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squaring the prime-scale amplitude replaces `p` by `p²`. -/
theorem gaussPrimeScaleCircle_sq (p : ℝ) (z : AddCircle (1 : ℝ)) :
    gaussPrimeScaleCircle p z * gaussPrimeScaleCircle p z =
      gaussPrimeScaleCircle (p ^ 2) z := by
  let x := ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)
  have hreal : gaussPrimeScale p x * gaussPrimeScale p x = gaussPrimeScale (p ^ 2) x := by
    unfold gaussPrimeScale
    rw [Real.log_pow, ← Real.exp_add]
    congr 1
    ring
  change (((gaussPrimeScale p x : ℝ) : ℂ) * ((gaussPrimeScale p x : ℝ) : ℂ)) =
    ((gaussPrimeScale (p ^ 2) x : ℝ) : ℂ)
  exact_mod_cast hreal

/-- Applying `B_p` twice is exactly the single multiplier `B_(p²)`. -/
theorem gaussPrimeScaleBlock_apply_self_eq_square {p : ℝ} (hp : 1 < p)
    (f : GaussCircleL2) :
    gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp f) =
      gaussPrimeScaleBlock (show 1 < p ^ 2 by nlinarith) f := by
  apply Lp.ext
  filter_upwards [gaussPrimeScaleBlock_coeFn hp (gaussPrimeScaleBlock hp f),
    gaussPrimeScaleBlock_coeFn hp f,
    gaussPrimeScaleBlock_coeFn (show 1 < p ^ 2 by nlinarith) f] with z h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, gaussPrimeScaleCircle_sq p]

/-- Exact raw Gram matrix of the literal `B_p`-weighted Fourier source features. -/
theorem inner_gaussPrimeScaleBlock_fourierLp
    {p : ℝ} (hp : 1 < p) (m n : ℤ) :
    inner ℂ (gaussPrimeScaleBlock hp (fourierLp 2 m : GaussCircleL2))
        (gaussPrimeScaleBlock hp (fourierLp 2 n : GaussCircleL2)) =
      (((p - 1 : ℝ) : ℂ) /
        (((Real.log p : ℝ) : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * ((m - n : ℤ) : ℂ))) := by
  rw [gaussPrimeScaleBlock_inner hp,
    gaussPrimeScaleBlock_apply_self_eq_square hp,
    GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_gaussPrimeScaleBlock_fourierLp,
    gaussPrimeScaleFourierCoefficient]
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsqrt : Real.sqrt (p ^ 2) = p := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hp0]
  have hlog : Real.log (p ^ 2) / 2 = Real.log p := by
    rw [Real.log_pow]
    ring
  rw [hsqrt, hlog]

/-- Literal prime source features with the normalization required by their exact Gram matrix. -/
def connesConsaniNormalizedPrimeSourceFeature (p : Nat.Primes) (n : ℤ) : GaussCircleL2 :=
  (((Real.sqrt ((p : ℝ) - 1))⁻¹ : ℝ) : ℂ) •
    gaussPrimeScaleBlock (show (1 : ℝ) < p by exact_mod_cast p.prop.one_lt)
      (fourierLp 2 n)

/-- Normalized source features have the intended Cauchy Gram kernel. -/
theorem inner_connesConsaniNormalizedPrimeSourceFeature
    (p : Nat.Primes) (m n : ℤ) :
    inner ℂ (connesConsaniNormalizedPrimeSourceFeature p m)
        (connesConsaniNormalizedPrimeSourceFeature p n) =
      (1 : ℂ) /
        (((Real.log p : ℝ) : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * ((m - n : ℤ) : ℂ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hsub : 0 < (p : ℝ) - 1 := sub_pos.mpr hp
  have hsqrt : Real.sqrt ((p : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.2 hsub).ne'
  rw [connesConsaniNormalizedPrimeSourceFeature,
    connesConsaniNormalizedPrimeSourceFeature, inner_smul_left, inner_smul_right,
    inner_gaussPrimeScaleBlock_fourierLp hp]
  simp only [Complex.conj_ofReal]
  have hsqrtSq : Real.sqrt ((p : ℝ) - 1) ^ 2 = (p : ℝ) - 1 :=
    Real.sq_sqrt hsub.le
  have hscalarReal :
      (Real.sqrt ((p : ℝ) - 1))⁻¹ * (Real.sqrt ((p : ℝ) - 1))⁻¹ *
          ((p : ℝ) - 1) = 1 := by
    calc
      (Real.sqrt ((p : ℝ) - 1))⁻¹ * (Real.sqrt ((p : ℝ) - 1))⁻¹ *
          ((p : ℝ) - 1) =
        (Real.sqrt ((p : ℝ) - 1))⁻¹ * (Real.sqrt ((p : ℝ) - 1))⁻¹ *
          (Real.sqrt ((p : ℝ) - 1) ^ 2) := by rw [hsqrtSq]
      _ = 1 := by field_simp
  have hscalar :
      ((((Real.sqrt ((p : ℝ) - 1))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt ((p : ℝ) - 1))⁻¹ : ℝ) : ℂ)) *
          (((p : ℝ) - 1 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hscalarReal
  rw [div_eq_mul_inv, div_eq_mul_inv]
  let c : ℂ := (((Real.sqrt ((p : ℝ) - 1))⁻¹ : ℝ) : ℂ)
  let d : ℂ := ((Real.log p : ℝ) : ℂ) +
    2 * (Real.pi : ℂ) * Complex.I * ((m - n : ℤ) : ℂ)
  change c * (c * ((((p : ℝ) - 1 : ℝ) : ℂ) * d⁻¹)) = 1 * d⁻¹
  calc
    c * (c * ((((p : ℝ) - 1 : ℝ) : ℂ) * d⁻¹)) =
        (c * c * (((p : ℝ) - 1 : ℝ) : ℂ)) * d⁻¹ := by ring
    _ = 1 * d⁻¹ := by simpa [c] using congrArg (fun z : ℂ => z * d⁻¹) hscalar

/-- Positivity of the source multiplier makes `B_p` injective. -/
theorem gaussPrimeScaleBlock_injective {p : ℝ} (hp : 1 < p) :
    Function.Injective (gaussPrimeScaleBlock hp) := by
  intro f g hfg
  apply Lp.ext
  have hout :
      ((gaussPrimeScaleBlock hp f : GaussCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[
        AddCircle.haarAddCircle]
      ((gaussPrimeScaleBlock hp g : GaussCircleL2) : AddCircle (1 : ℝ) → ℂ) := by
    rw [hfg]
  filter_upwards [gaussPrimeScaleBlock_coeFn hp f,
    gaussPrimeScaleBlock_coeFn hp g, hout] with z hf hg heq
  rw [hf, hg] at heq
  exact mul_left_cancel₀ (by
    have hpos := gaussPrimeScale_pos p
      ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)
    change (((gaussPrimeScale p
      ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ)) ≠ 0
    exact_mod_cast hpos.ne') heq

/-- The correctly normalized prime source features span a dense subspace of circle `L²`. -/
theorem dense_connesConsaniNormalizedPrimeSourceFeature (p : Nat.Primes) :
    Dense ((LinearMap.range
      (featureSynthesis (connesConsaniNormalizedPrimeSourceFeature p)) :
        Submodule ℂ GaussCircleL2) : Set GaussCircleL2) := by
  rw [range_featureSynthesis_eq_span, Submodule.dense_iff_topologicalClosure_eq_top]
  rw [topologicalClosure_span_eq_top_iff]
  intro w hw
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hsub : 0 < (p : ℝ) - 1 := sub_pos.mpr hp
  have hc : ((((Real.sqrt ((p : ℝ) - 1))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (inv_ne_zero (Real.sqrt_pos.2 hsub).ne')
  have hfreq : ∀ n : ℤ,
      inner ℂ (gaussPrimeScaleBlock hp w) (fourierLp 2 n : GaussCircleL2) = 0 := by
    intro n
    rw [gaussPrimeScaleBlock_inner]
    have hn := hw (connesConsaniNormalizedPrimeSourceFeature p n) ⟨n, rfl⟩
    rw [connesConsaniNormalizedPrimeSourceFeature, inner_smul_right] at hn
    exact (mul_eq_zero.mp hn).resolve_left hc
  have hBw : gaussPrimeScaleBlock hp w = 0 := by
    have hdenseFourier :
        (Submodule.span ℂ (Set.range (fun n : ℤ =>
          (fourierLp 2 n : GaussCircleL2)))).topologicalClosure = ⊤ := by
      simpa only [coe_fourierBasis] using
        (fourierBasis (T := (1 : ℝ))).dense_span
    refine (topologicalClosure_span_eq_top_iff _).mp hdenseFourier
      (gaussPrimeScaleBlock hp w) ?_
    intro s hs
    obtain ⟨n, rfl⟩ := hs
    exact hfreq n
  apply gaussPrimeScaleBlock_injective hp
  simpa using hBw

end

end RHTower
