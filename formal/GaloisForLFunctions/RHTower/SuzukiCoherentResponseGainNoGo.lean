import GaloisForLFunctions.RHTower.SuzukiCausalDepthFrostmanTransfer
import GaloisForLFunctions.RHTower.SuzukiRectangularWallGramGate

/-!
# Vanishing cofinal gain of the coherent Suzuki response

The exact causal depth-fused response is a valid absolutely summable all-prime field, but its
observer innovation damps the underlying sharp wall amplitude by `1 / (p + 1)`.  The depth
resolvent has a prime-uniform bound, so it cannot reverse this damping.

At the prime-dependent moving-wall aperture, the sharp rectangular gate is exactly one.  Thus the
source cell retains its full observer-free wall amplitude while the causal response/source ratio
vanishes cofinally.  No finite uniform inverse gain can recover the sharp wall source from this
response.  Any successful Robin--Gamma weld through this carrier must therefore use an unbounded,
cutoff-dependent relative observation.

No RH premise, Xi zero, numerical computation, estimate for zeta, or target positivity is used.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Prime-uniform cap for the causal depth-resolvent radius. -/
def suzukiSharpWallResponseRadiusCap : ℝ :=
  Real.exp (-(1 / 4 : ℝ) * Real.log 2)

/-- The cap is strictly below one. -/
theorem suzukiSharpWallResponseRadiusCap_lt_one :
    suzukiSharpWallResponseRadiusCap < 1 := by
  rw [suzukiSharpWallResponseRadiusCap, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

/-- Every positive-aperture causal depth radius is below the uniform cap. -/
theorem suzukiCriticalApertureDepthFusionRadius_le_sharpWallResponseCap
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius h a p ≤
      suzukiSharpWallResponseRadiusCap := by
  rw [suzukiCriticalApertureDepthFusionRadius, suzukiSharpWallResponseRadiusCap]
  let d := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hd0 : 0 ≤ d := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hd1 : d < 1 := xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p
  have hdSq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.property.two_le
  have hexp : Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) ≤
      Real.exp (-(1 / 4 : ℝ) * Real.log 2) := by
    rw [Real.exp_le_exp]
    nlinarith
  exact (mul_le_of_le_one_right (Real.exp_nonneg _) hdSq).trans hexp

/-- Fixed source-to-response gain constant; all prime dependence remains in `1 / (p + 1)`. -/
def suzukiCausalResponseGainConstant (h : ℝ) : ℝ :=
  (h * Real.sqrt h)⁻¹ * (1 - suzukiSharpWallResponseRadiusCap)⁻¹

/-- The gain constant is strictly positive at positive aperture scale. -/
theorem suzukiCausalResponseGainConstant_pos {h : ℝ} (hh : 0 < h) :
    0 < suzukiCausalResponseGainConstant h := by
  rw [suzukiCausalResponseGainConstant]
  exact mul_pos (inv_pos.mpr (mul_pos hh (Real.sqrt_pos.2 hh)))
    (inv_pos.mpr (sub_pos.mpr suzukiSharpWallResponseRadiusCap_lt_one))

/-- Unit-modulus half-prime-log phase. -/
private theorem norm_suzukiCriticalApertureDepthFusionPhase_eq_one
    (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthFusionPhase t p‖ = 1 := by
  rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue,
    Complex.norm_exp_ofReal_mul_I]

/-- The depth-zero observer innovation loses an exact reciprocal-prime factor relative to the
observer-free sharp wall amplitude. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_zero_le_source_div_prime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 ≤
      (h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ *
        suzukiCriticalEntryWallBareAmplitude p 0 := by
  rw [suzukiCriticalEntryWallEndpointAmplitude_eq_bare_mul_innovation]
  simp only [xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature, pow_zero]
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
  let d := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  have hd0 : 0 < d := xiMobiusContinuousApertureDiskNode_pos _ p
  have hd1 : d < 1 := xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) = ((p : ℝ) + 1)⁻¹ := by
    field_simp
  rw [hq]
  simp only [mul_one]
  have hbare : 0 ≤ suzukiCriticalEntryWallBareAmplitude p 0 := Real.sqrt_nonneg _
  have hinvh : 0 ≤ (h * Real.sqrt h)⁻¹ := by positivity
  have hinvp : 0 ≤ ((p : ℝ) + 1)⁻¹ := by positivity
  have hdsq : (1 - d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  change suzukiCriticalEntryWallBareAmplitude p 0 *
      ((h * Real.sqrt h)⁻¹ * (((p : ℝ) + 1)⁻¹ * (1 - d) ^ 2)) ≤
    (h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ *
      suzukiCriticalEntryWallBareAmplitude p 0
  calc
    suzukiCriticalEntryWallBareAmplitude p 0 *
        ((h * Real.sqrt h)⁻¹ * (((p : ℝ) + 1)⁻¹ * (1 - d) ^ 2))
        ≤ suzukiCriticalEntryWallBareAmplitude p 0 *
          ((h * Real.sqrt h)⁻¹ * (((p : ℝ) + 1)⁻¹ * 1)) := by gcongr
    _ = (h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ *
          suzukiCriticalEntryWallBareAmplitude p 0 := by ring

/-- **Sharp causal gain law.**  The complete valuation-depth fused response loses at least one
reciprocal-prime order relative to the exact sharp wall source amplitude. -/
theorem norm_suzukiCriticalApertureDepthFusedAtom_le_source_div_prime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthFusedAtom h a t p‖ ≤
      suzukiCausalResponseGainConstant h *
        suzukiCriticalEntryWallBareAmplitude p 0 / ((p : ℝ) + 1) := by
  rw [suzukiCriticalApertureDepthFusedAtom_eq_mobius hh ha]
  let r := suzukiCriticalApertureDepthFusionRadius h a p
  let z := suzukiCriticalApertureDepthFusionPhase t p
  have hr0 : 0 < r := suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hrcap : r ≤ suzukiSharpWallResponseRadiusCap :=
    suzukiCriticalApertureDepthFusionRadius_le_sharpWallResponseCap hh ha p
  have hcap1 : suzukiSharpWallResponseRadiusCap < 1 :=
    suzukiSharpWallResponseRadiusCap_lt_one
  have hbase : 0 < 1 - suzukiSharpWallResponseRadiusCap := sub_pos.mpr hcap1
  have hz : ‖z‖ = 1 := norm_suzukiCriticalApertureDepthFusionPhase_eq_one t p
  have hrz : ‖(r : ℂ) * z‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hz, mul_one]
  have hden : 1 - suzukiSharpWallResponseRadiusCap ≤ ‖1 - (r : ℂ) * z‖ := by
    calc
      1 - suzukiSharpWallResponseRadiusCap ≤ 1 - r := by linarith
      _ ≤ ‖(1 : ℂ) - (r : ℂ) * z‖ := by
        have hnorm := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
        rw [norm_one, hrz] at hnorm
        exact hnorm
  have hdenPos : 0 < ‖1 - (r : ℂ) * z‖ := hbase.trans_le hden
  have hinv : ‖(1 - (r : ℂ) * z)⁻¹‖ ≤
      (1 - suzukiSharpWallResponseRadiusCap)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ hdenPos hbase).2 hden
  have hend0 : 0 ≤ suzukiCriticalEntryWallEndpointAmplitude h a p 0 :=
    (suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p).le
  have hend :=
    suzukiCriticalEntryWallEndpointAmplitude_zero_le_source_div_prime hh ha p
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hend0, hz]
  simp only [mul_one]
  dsimp only [suzukiCausalResponseGainConstant]
  have hbare : 0 ≤ suzukiCriticalEntryWallBareAmplitude p 0 := Real.sqrt_nonneg _
  have hinvh : 0 ≤ (h * Real.sqrt h)⁻¹ := by positivity
  have hinvp : 0 ≤ ((p : ℝ) + 1)⁻¹ := by positivity
  calc
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 *
        ‖(1 - (r : ℂ) * z)⁻¹‖
        ≤ ((h * Real.sqrt h)⁻¹ * ((p : ℝ) + 1)⁻¹ *
          suzukiCriticalEntryWallBareAmplitude p 0) *
          (1 - suzukiSharpWallResponseRadiusCap)⁻¹ := by gcongr
    _ = (h * Real.sqrt h)⁻¹ *
          (1 - suzukiSharpWallResponseRadiusCap)⁻¹ *
          suzukiCriticalEntryWallBareAmplitude p 0 / ((p : ℝ) + 1) := by ring

/-- Moving-wall aperture whose sharp rectangular tent is centered on the depth-zero prime lag. -/
def suzukiPrimeMovingWallAperture (p : Nat.Primes) : ℝ :=
  (Real.log (p : ℝ) + 1) / 2

/-- At the moving-wall aperture, every prime with `log p ≥ 1` retains the complete unit-width
sharp source gate. -/
theorem suzukiRectangularWallGramGate_movingPrime_eq_one
    (p : Nat.Primes) (hp : 1 ≤ Real.log (p : ℝ)) :
    suzukiRectangularWallGramGate 1 (suzukiPrimeMovingWallAperture p) p 0 = 1 := by
  rw [suzukiRectangularWallGramGate,
    rectangularTwoEdgeAutocorrelation_eq_four_tents]
  simp only [xiGammaEulerValuationNat, pow_succ, pow_zero, one_mul]
  dsimp only [suzukiPrimeMovingWallAperture]
  have hlog0 : 0 ≤ Real.log (p : ℝ) := le_trans (by norm_num) hp
  rw [abs_of_nonneg hlog0]
  have hfirst : max 0 (1 - Real.log (p : ℝ)) = 0 := by
    rw [max_eq_left]
    linarith
  rw [hfirst]
  have hcenter : 2 * ((Real.log (p : ℝ) + 1) / 2) - 1 =
      Real.log (p : ℝ) := by ring
  rw [hcenter, sub_self, abs_zero]
  have hreverse : max 0 (1 - |Real.log (p : ℝ) + Real.log (p : ℝ)|) = 0 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (p : ℝ) + Real.log (p : ℝ))]
    rw [max_eq_left]
    linarith
  rw [hreverse]
  norm_num

/-- The corresponding sharp wall diagonal is exactly the square of the observer-free source
amplitude. -/
theorem suzukiRectangularWallGramKernel_movingPrime_diagonal_eq_bare_sq
    (t : ℝ) (p : Nat.Primes) (hp : 1 ≤ Real.log (p : ℝ)) :
    suzukiRectangularWallGramKernel 1 (suzukiPrimeMovingWallAperture p) t t p 0 =
      ((suzukiCriticalEntryWallBareAmplitude p 0 ^ 2 : ℝ) : ℂ) := by
  rw [suzukiRectangularWallGramKernel_diagonal_eq_primeCell,
    suzukiRectangularPrimePowerWallCell,
    suzukiRectangularWallGramGate_movingPrime_eq_one p hp, one_mul,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]

/-- The observer-free sharp wall amplitude is strictly positive. -/
theorem suzukiCriticalEntryWallBareAmplitude_zero_pos (p : Nat.Primes) :
    0 < suzukiCriticalEntryWallBareAmplitude p 0 := by
  have hsq : 0 < suzukiCriticalEntryWallBareAmplitude p 0 ^ 2 := by
    rw [sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
    exact suzukiCriticalFarHingeWeight_pos p 0
  have hnonneg : 0 ≤ suzukiCriticalEntryWallBareAmplitude p 0 := Real.sqrt_nonneg _
  nlinarith

/-- **No uniform recovery theorem.**  For every finite proposed inverse gain, one moving prime
wall cell has strictly larger sharp source amplitude than the gain times its complete causal
response.  Hence the coherent response is not uniformly bounded below on the sharp source. -/
theorem exists_prime_suzukiCausalResponse_not_uniformly_recovers_sharpWall
    {h : ℝ} (hh : 0 < h) (t M : ℝ) (hM : 0 ≤ M) :
    ∃ p : Nat.Primes,
      1 ≤ Real.log (p : ℝ) ∧
      M * ‖suzukiCriticalApertureDepthFusedAtom h
          (suzukiPrimeMovingWallAperture p) t p‖ <
        suzukiCriticalEntryWallBareAmplitude p 0 := by
  let C := suzukiCausalResponseGainConstant h
  have hC : 0 < C := suzukiCausalResponseGainConstant_pos hh
  obtain ⟨q, hq, hqprime⟩ :=
    Nat.exists_infinite_primes (max 3 ⌈M * C⌉₊ + 1)
  let p : Nat.Primes := ⟨q, hqprime⟩
  have hq3 : 3 < q := by omega
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hqprime.pos
  have hlog : 1 < Real.log (p : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hp0).2
    exact Real.exp_one_lt_three.trans (by exact_mod_cast hq3)
  have hceil : M * C ≤ (⌈M * C⌉₊ : ℝ) := Nat.le_ceil _
  have hceilq : (⌈M * C⌉₊ : ℝ) < (p : ℝ) := by
    exact_mod_cast (show ⌈M * C⌉₊ < q by omega)
  have hMCp : M * C < (p : ℝ) + 1 :=
    (lt_of_le_of_lt hceil hceilq).trans (by linarith)
  have hppos : 0 < (p : ℝ) + 1 := by positivity
  have hratio : M * C / ((p : ℝ) + 1) < 1 :=
    (div_lt_one hppos).2 hMCp
  have ha : 0 < suzukiPrimeMovingWallAperture p := by
    rw [suzukiPrimeMovingWallAperture]
    linarith
  have hbound :=
    norm_suzukiCriticalApertureDepthFusedAtom_le_source_div_prime hh ha t p
  have hbare := suzukiCriticalEntryWallBareAmplitude_zero_pos p
  refine ⟨p, hlog.le, ?_⟩
  calc
    M * ‖suzukiCriticalApertureDepthFusedAtom h
          (suzukiPrimeMovingWallAperture p) t p‖
        ≤ M * (C * suzukiCriticalEntryWallBareAmplitude p 0 /
          ((p : ℝ) + 1)) := mul_le_mul_of_nonneg_left hbound hM
    _ = (M * C / ((p : ℝ) + 1)) *
          suzukiCriticalEntryWallBareAmplitude p 0 := by ring
    _ < 1 * suzukiCriticalEntryWallBareAmplitude p 0 :=
      mul_lt_mul_of_pos_right hratio hbare
    _ = suzukiCriticalEntryWallBareAmplitude p 0 := one_mul _

end

end RHTower
