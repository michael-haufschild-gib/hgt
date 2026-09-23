import GaloisForLFunctions.RHTower.XiWardCubicLogMomentHellingerCauchySeparator
import GaloisForLFunctions.RHTower.XiWardMultiscaleEulerSourceDivergence
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain
import GaloisForLFunctions.RHTower.VonMangoldtGammaOrientedAnomaly

/-!
# Cubic log-moment separator on the balanced Euler source

The scale-invariant Hellinger diagonal preserves the nonsummable balanced weight `Λ(n) / n`.
The cubic log-moment diagonal is instead `115 / (864 (log n)^(3 : ℕ))`.  On a prime-power coordinate
`n = p^(e+1)`, multiplication by the literal balanced source coefficient gives

`115 / (864 (e+1)^(3 : ℕ) p^(e+1) (log p)^(2 : ℕ))`.

This family is positive and summable.  Thus cubic weighting simultaneously retains a uniform
(indeed increasing) charge on every strict-right zeta displacement and removes the global Euler
diagonal divergence.  No Xi density conclusion or source-to-zero trace comparison is asserted.
-/

namespace RHTower

noncomputable section

/-- Positive real form of the cubic balanced Euler prime-depth diagonal. -/
def xiGammaEulerPrimitiveCubicLogMomentWeight
    (pe : Nat.Primes × ℕ) : ℝ :=
  (115 / 864 : ℝ) * invNatLogSq pe.1 *
    ((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ (3 : ℕ))⁻¹

theorem xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg
    (pe : Nat.Primes × ℕ) :
    0 ≤ xiGammaEulerPrimitiveCubicLogMomentWeight pe := by
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  positivity

/-- Explicit product majorant: prime factor `1/(p log^(2 : ℕ) p)` and geometric depth factor. -/
theorem xiGammaEulerPrimitiveCubicLogMomentWeight_le
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCubicLogMomentWeight pe ≤
      (115 / 864 : ℝ) * invNatLogSq pe.1 * (1 / 2 : ℝ) ^ pe.2 := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hp2 : (2 : ℝ) ≤ (pe.1 : ℝ) := by exact_mod_cast pe.1.property.two_le
  have hpInv : (pe.1 : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hpPow : ((pe.1 : ℝ)⁻¹) ^ pe.2 ≤ (1 / 2 : ℝ) ^ pe.2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hpInv pe.2
  have hkOne : (1 : ℝ) ≤ (pe.2 : ℝ) + 1 := by
    exact_mod_cast Nat.le_add_left 1 pe.2
  have hkCube : (1 : ℝ) ≤ ((pe.2 : ℝ) + 1) ^ (3 : ℕ) := by
    exact one_le_pow₀ hkOne
  have hkInv : (((pe.2 : ℝ) + 1) ^ (3 : ℕ))⁻¹ ≤ (1 : ℝ) := by
    simpa using
      (inv_le_inv₀ (by positivity : 0 < ((pe.2 : ℝ) + 1) ^ (3 : ℕ))
        (by norm_num : (0 : ℝ) < 1)).2 hkCube
  have hbase : 0 ≤ (115 / 864 : ℝ) * invNatLogSq pe.1 := by
    rw [invNatLogSq]
    positivity
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight]
  calc
    (115 / 864 : ℝ) * invNatLogSq pe.1 *
          ((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ (3 : ℕ))⁻¹ ≤
        (115 / 864 : ℝ) * invNatLogSq pe.1 *
          (1 / 2 : ℝ) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ (3 : ℕ))⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpPow hbase)
        (inv_nonneg.mpr (by positivity))
    _ ≤ (115 / 864 : ℝ) * invNatLogSq pe.1 *
          (1 / 2 : ℝ) ^ pe.2 * 1 := by
      exact mul_le_mul_of_nonneg_left hkInv
        (mul_nonneg hbase (by positivity))
    _ = _ := by ring

/-- The cubic balanced Euler diagonal is summable on the full prime-depth carrier. -/
theorem summable_xiGammaEulerPrimitiveCubicLogMomentWeight :
    Summable xiGammaEulerPrimitiveCubicLogMomentWeight := by
  let major : Nat.Primes × ℕ → ℝ := fun pe =>
    (115 / 864 : ℝ) * invNatLogSq pe.1 * (1 / 2 : ℝ) ^ pe.2
  have hmajorNonneg : 0 ≤ major := by
    intro pe
    dsimp only [major]
    rw [invNatLogSq]
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        ((115 / 864 : ℝ) * invNatLogSq p)
    · have hprime := summable_prime_invNatLogSq.mul_left (115 / 432 : ℝ)
      apply hprime.congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  exact Summable.of_nonneg_of_le
    xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg
    xiGammaEulerPrimitiveCubicLogMomentWeight_le hmajor

/-- The cubic horizontal self-kernel placed on the literal balanced primitive source. -/
def xiGammaEulerPrimitiveCubicLogMomentDiagonal
    (a : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  (cubicLogMomentHellingerHorizontalKernel
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiGammaEulerPrimitiveLogFrequency pe) : ℂ) *
    (xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
      star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe))

/-- Exact balanced prime-depth coefficient of the cubic source diagonal. -/
theorem xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCubicLogMomentDiagonal a pe =
      (xiGammaEulerPrimitiveCubicLogMomentWeight pe : ℂ) := by
  rw [xiGammaEulerPrimitiveCubicLogMomentDiagonal,
    cubicLogMomentHellingerHorizontalKernel_self
      (xiGammaEulerPrimitiveLogFrequency_pos pe),
    xiGammaEulerPrimitiveBalancedReflectionCoeff_eq,
    finiteVonMangoldtWeight_eq_ofReal]
  · rw [show xiGammaEulerValuationNat pe = pe.1 ^ (pe.2 + 1) by rfl,
      vonMangoldt_prime_pow_succ_eq_log pe]
    have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
    have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
    have hk : ((pe.2 : ℝ) + 1) ≠ 0 := by positivity
    have hpow : ((pe.1 : ℝ) ^ (pe.2 + 1) : ℝ) ≠ 0 := by positivity
    have hlogFrequency :
        xiGammaEulerPrimitiveLogFrequency pe =
          ((pe.2 : ℝ) + 1) * Real.log (pe.1 : ℝ) := by
      rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat,
        Nat.cast_pow, Real.log_pow]
      push_cast
      ring
    rw [hlogFrequency, xiGammaEulerPrimitiveCubicLogMomentWeight,
      invNatLogSq]
    norm_cast
    push_cast
    rw [pow_succ (pe.1 : ℝ) pe.2]
    field_simp [hp.ne', hlog, hk, hpow]
    rw [← mul_pow]
    have hcancel : (pe.1 : ℝ) * (1 / (pe.1 : ℝ)) = 1 := by
      field_simp [hp.ne']
    rw [hcancel, one_pow]
  · unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ pe.1.property.ne_zero

/-- **Cubic Euler-source admission.** The positive diagonal that separates every strict-right
shift is a genuine summable family on the literal balanced primitive Euler carrier. -/
theorem summable_xiGammaEulerPrimitiveCubicLogMomentDiagonal
    (a : ℝ) :
    Summable (xiGammaEulerPrimitiveCubicLogMomentDiagonal a) := by
  have hcomplex : Summable (fun pe : Nat.Primes × ℕ =>
      (xiGammaEulerPrimitiveCubicLogMomentWeight pe : ℂ)) :=
    summable_xiGammaEulerPrimitiveCubicLogMomentWeight.map
      Complex.ofRealCLM Complex.ofRealCLM.continuous
  exact hcomplex.congr fun pe =>
    (xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight a pe).symm

end

end RHTower
