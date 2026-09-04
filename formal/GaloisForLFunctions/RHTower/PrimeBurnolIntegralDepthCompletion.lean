import GaloisForLFunctions.HTGeometry.IntegralTailCompletion
import GaloisForLFunctions.RHTower.PrimeBurnolDepthCompletion

/-!
# Integer combinations of literal prime-depth columns are dense

The Euler amplitude is exactly sqrt(log p) * (1 / sqrt(p))^(n+1), hence summable.
The generic tail-rounding law therefore applies without replacing the unsquared
amplitudes. The real columns are identified almost everywhere with the real
coordinate of the corpus's existing complex Burnol source.

Thus integer coefficients alone do not provide a discrete prime sector in
ordinary L² completion. No conclusion about bounded coefficients, multiplicative
Euler products, a source-labelled comparison graph, or RH is asserted.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace RHTower
noncomputable section

def primeBurnolRealAmplitude (p : Nat.Primes) (n : ℕ) : ℝ :=
  (primeBurnolAmplitude (p, n)).re

theorem primeBurnolRealAmplitude_ne_zero (p : Nat.Primes) (n : ℕ) :
    primeBurnolRealAmplitude p n ≠ 0 := by
  have h := primeBurnolAmplitude_ne_zero (p, n)
  simpa only [primeBurnolRealAmplitude, primeBurnolAmplitude, Complex.ofReal_re,
    ne_eq, Complex.ofReal_eq_zero] using h

private theorem sqrt_nat_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem primeBurnolRealAmplitude_eq_geometric (p : Nat.Primes) (n : ℕ) :
    primeBurnolRealAmplitude p n =
      Real.sqrt (Real.log (p : ℝ)) * ((Real.sqrt (p : ℝ))⁻¹) ^ (n + 1) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : 0 < Real.log (p : ℝ) := (primeBurnolLogRate p).property
  simp only [primeBurnolRealAmplitude, primeBurnolAmplitude, Complex.ofReal_re,
    primeBurnolValuation, Nat.cast_pow]
  rw [Real.sqrt_div hlog.le, sqrt_nat_pow (p : ℝ) hp.le, div_eq_mul_inv, inv_pow]

theorem summable_abs_primeBurnolRealAmplitude (p : Nat.Primes) :
    Summable (fun n => |primeBurnolRealAmplitude p n|) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hsqrt : 1 < Real.sqrt (p : ℝ) := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp
    simpa using this
  have hr0 : 0 ≤ (Real.sqrt (p : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr1 : (Real.sqrt (p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt
  have hs := ((summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one hr0 hr1)).mul_left (Real.sqrt (Real.log (p : ℝ)))
  simpa only [primeBurnolRealAmplitude_eq_geometric, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (pow_nonneg hr0 _)] using hs

/-- The real-valued literal source columns, retaining the unsquared Euler amplitudes. -/
def primeBurnolRealDepthFeatureLp (p : Nat.Primes) (n : ℕ) : HTGeometry.RealBurnolHalfLineL2 :=
  primeBurnolRealAmplitude p n • HTGeometry.realBurnolDepthFeatureL2 (primeBurnolLogRate p) n

/-- Identification with the real coordinate of the already-defined literal complex source. -/
theorem primeBurnolRealDepthFeatureLp_ae (p : Nat.Primes) (n : ℕ) :
    (primeBurnolRealDepthFeatureLp p n : ℝ → ℝ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (primeBurnolWindowFeatureLp (p, n) 0 t).re) := by
  filter_upwards [Lp.coeFn_smul (primeBurnolRealAmplitude p n)
      (HTGeometry.realBurnolDepthFeatureL2 (primeBurnolLogRate p) n),
    HTGeometry.realBurnolDepthFeatureL2_ae (primeBurnolLogRate p) n,
    primeBurnolWindowFeatureLp_coeFn (p, n) 0] with t hs hd hp
  change (primeBurnolRealAmplitude p n •
    HTGeometry.realBurnolDepthFeatureL2 (primeBurnolLogRate p) n) t = _
  rw [hs, hp, primeBurnolWindowFeature_zero_eq_depth]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  simp only [primeBurnolRealAmplitude,
    HTGeometry.burnolDepthFeature, HTGeometry.realBurnolDepthFeature,
    primeBurnolLogRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- Even integer linear combinations of a single prime's exact unsquared depth columns are
dense in the real half-line output. Integrality alone does not survive this completion. -/
theorem dense_integer_primeBurnolRealDepthSpan (p : Nat.Primes) :
    Dense (Submodule.span ℤ (Set.range (primeBurnolRealDepthFeatureLp p)) :
      Set HTGeometry.RealBurnolHalfLineL2) :=
  HTGeometry.dense_integer_weighted_realBurnolDepthSpan (primeBurnolLogRate p)
    (primeBurnolRealAmplitude p) (primeBurnolRealAmplitude_ne_zero p)
    (summable_abs_primeBurnolRealAmplitude p)

end
end RHTower

