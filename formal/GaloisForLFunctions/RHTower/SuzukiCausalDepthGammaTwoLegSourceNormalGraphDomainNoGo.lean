import GaloisForLFunctions.RHTower.SuzukiCoherentCausalDepthFusion
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaSchurCoherence
import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedCofinalDepthCountertransport
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Two-leg source-normal Gamma graph-domain obstruction

The actual causal Gamma source is trace class before deattenuation.  The canonical source-normal
operation used by inverse-Wold lowering acts on two polarized legs, so its amplitude gain is the
square of one critical deattenuation: exactly `p` at prime `p`.

After that physical gain, the depth-zero squared amplitude dominates a positive constant times
`1 / p` on a cofinite set of primes.  Prime-harmonic divergence therefore excludes even `ℓ²`
graph admission of the full prime-depth source.  Thus the canonical two-leg source-normal
operation cannot realize the moving/singular-domain repair surviving the bounded-response
Gamma--Robin no-go.  This does not exclude a different cutoff-moving or non-`S¹` source law.
-/

open Filter Topology

namespace RHTower

noncomputable section

open PrimitivePromotedCofinalDepth

private theorem tendsto_exp_neg_scaled_primeLog
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => Real.exp (-(a * Real.log (p : ℝ))))
      cofinite (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (Filter.Tendsto.const_mul_atTop ha
      GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop))

private theorem tendsto_suzukiCausalDepthGammaDiskNode_cofinite_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => xiMobiusContinuousApertureDiskNode a p)
      cofinite (𝓝 0) := by
  refine (tendsto_exp_neg_scaled_primeLog ha).congr fun p => ?_
  rw [xiMobiusContinuousApertureDiskNode]
  congr 1
  ring

/-- Exact squared depth-zero causal Gamma amplitude after the two-leg gain `p`. -/
theorem sq_prime_mul_suzukiCausalDepthGammaWeight_zero_eq
    {h a : ℝ} (p : Nat.Primes) :
    (((p : ℝ) * suzukiCausalDepthGammaWeight h a (p, 0)) ^ (2 : ℕ)) =
      ((p : ℝ) ^ (2 : ℕ)) *
        (Real.log (p : ℝ) * Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) *
        ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ) *
        (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
  rw [suzukiCausalDepthGammaWeight, pow_zero, mul_one,
    suzukiCriticalEntryWallEndpointAmplitude_zero_eq_coherentWeight]
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  have hexp : 0 ≤ Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) :=
    (Real.exp_pos _).le
  calc
    _ = ((p : ℝ) ^ (2 : ℕ)) *
        (Real.sqrt (Real.log (p : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) ^ (2 : ℕ)) *
        ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ) *
        (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
      ring
    _ = _ := by rw [Real.sq_sqrt (mul_nonneg hlog hexp)]

/-- The two-leg deattenuated depth-zero source misses `ℓ²` for every positive physical scale and
aperture. -/
theorem not_summable_sq_prime_mul_suzukiCausalDepthGammaWeight_zero
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    ¬ Summable (fun p : Nat.Primes =>
      (((p : ℝ) * suzukiCausalDepthGammaWeight h a (p, 0)) ^ (2 : ℕ))) := by
  intro hsum
  let C : ℝ := (h * Real.sqrt h)⁻¹
  let K : ℝ := Real.log 2 * C ^ (2 : ℕ) / 64
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hap : 0 < (h / 2) * a := by positivity
  have hdisk : ∀ᶠ p : Nat.Primes in cofinite,
      xiMobiusContinuousApertureDiskNode ((h / 2) * a) p < 1 / 2 :=
    (tendsto_suzukiCausalDepthGammaDiskNode_cofinite_zero hap).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlower : ∀ᶠ p : Nat.Primes in cofinite,
      K * (1 / (p : ℝ)) ≤
        (((p : ℝ) * suzukiCausalDepthGammaWeight h a (p, 0)) ^ (2 : ℕ)) := by
    filter_upwards [hdisk] with p hpDisk
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
    have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.one_lt.le
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hp hpTwo
    have hexp : 1 / (p : ℝ) ≤
        Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) := by
      calc
        1 / (p : ℝ) = Real.exp (-Real.log (p : ℝ)) := by
          rw [Real.exp_neg, Real.exp_log hp]
          simp only [one_div]
        _ ≤ Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpOne
          linarith
    have hratio : (1 / 4 : ℝ) ≤
        ((p : ℝ) ^ (2 : ℕ)) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ) := by
      have hden : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      have hhalf : (1 / 2 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) := by
        apply (le_div_iff₀ hden).2
        nlinarith
      have hsquare : (1 / 4 : ℝ) ≤
          ((p : ℝ) / ((p : ℝ) + 1)) ^ (2 : ℕ) := by
        nlinarith
      calc
        (1 / 4 : ℝ) ≤ ((p : ℝ) / ((p : ℝ) + 1)) ^ (2 : ℕ) := hsquare
        _ = ((p : ℝ) ^ (2 : ℕ)) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ) := by
          rw [div_eq_mul_inv]
          ring
    have hdisk4 : (1 / 16 : ℝ) ≤
        (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
      calc
        (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ (4 : ℕ) := by norm_num
        _ ≤ (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
          gcongr
          linarith
    rw [sq_prime_mul_suzukiCausalDepthGammaWeight_zero_eq]
    dsimp [K, C]
    calc
      Real.log 2 * (h * Real.sqrt h)⁻¹ ^ (2 : ℕ) / 64 * (1 / (p : ℝ)) =
          (1 / 4 : ℝ) * Real.log 2 * (1 / (p : ℝ)) *
            (h * Real.sqrt h)⁻¹ ^ (2 : ℕ) * (1 / 16 : ℝ) := by
        ring
      _ ≤ (((p : ℝ) ^ (2 : ℕ)) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ)) *
          Real.log (p : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
          (h * Real.sqrt h)⁻¹ ^ (2 : ℕ) *
          (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
        gcongr
      _ = ((p : ℝ) ^ (2 : ℕ)) *
          (Real.log (p : ℝ) *
            Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) *
          (h * Real.sqrt h)⁻¹ ^ (2 : ℕ) * (((p : ℝ) + 1)⁻¹) ^ (2 : ℕ) *
          (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ (4 : ℕ) := by
        ring
  have hscaled : Summable (fun p : Nat.Primes => K * (1 / (p : ℝ))) :=
    Summable.of_norm_bounded_eventually hsum (by
      filter_upwards [hlower] with p hpLower
      simpa [Real.norm_eq_abs, abs_of_pos hK, abs_of_pos (by
        exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ))] using hpLower)
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff hK.ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Actual causal Gamma amplitude after the canonical two-polarized-leg source-normal operation. -/
def suzukiCausalDepthGammaTwoLegSourceNormalWeight
    (h a : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  criticalDepthDeattenuation pe 1 ^ (2 : ℕ) *
    suzukiCausalDepthGammaWeight h a pe

/-- The physical two-leg source-normal multiplier is exactly the prime. -/
theorem suzukiCausalDepthGammaTwoLegSourceNormalWeight_eq
    (h a : ℝ) (pe : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaTwoLegSourceNormalWeight h a pe =
      (pe.1 : ℝ) * suzukiCausalDepthGammaWeight h a pe := by
  rw [suzukiCausalDepthGammaTwoLegSourceNormalWeight,
    criticalDepthDeattenuation_sq]
  simp

/-- Hilbert graph admission demanded by the canonical two-leg source-normal Gamma repair. -/
def SuzukiCausalDepthGammaTwoLegSourceNormalGraphAdmissible
    (h a : ℝ) : Prop :=
  Summable (fun pe : Nat.Primes × ℕ =>
    (suzukiCausalDepthGammaTwoLegSourceNormalWeight h a pe) ^ (2 : ℕ))

/-- **C30, canonical source-normal moving-domain no-go.** The full physical causal Gamma source
cannot enter the Hilbert graph domain after its canonical two-leg source-normal deattenuation. -/
theorem not_suzukiCausalDepthGammaTwoLegSourceNormalGraphAdmissible
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    ¬ SuzukiCausalDepthGammaTwoLegSourceNormalGraphAdmissible h a := by
  intro hfull
  have hzero : Summable (fun p : Nat.Primes =>
      (suzukiCausalDepthGammaTwoLegSourceNormalWeight h a (p, 0)) ^ (2 : ℕ)) :=
    hfull.comp_injective (by
      intro p q hpq
      exact congrArg Prod.fst hpq)
  have hzero' : Summable (fun p : Nat.Primes =>
      (((p : ℝ) * suzukiCausalDepthGammaWeight h a (p, 0)) ^ (2 : ℕ))) := by
    simpa only [suzukiCausalDepthGammaTwoLegSourceNormalWeight_eq] using hzero
  exact not_summable_sq_prime_mul_suzukiCausalDepthGammaWeight_zero hh ha hzero'

end

end RHTower
