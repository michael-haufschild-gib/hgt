import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeNormalForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers

/-!
# Infinitely divisible prime-tail corrections and chain gauges

The square-zero tail correction has no nonzero compatible backward tower.
The two-prime gauge, including its restriction to every arithmetic cutoff,
has exactly one backward tower through every starting chain. The inverse
gauge iterates are affine in the iteration number.
-/

noncomputable section

namespace GaloisForLFunctions.EffectiveScalingGeometry

open RHTower ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable (R : Type*) [CommRing R]

/-- A prime-tail correction cannot be divided indefinitely by that correction. -/
theorem primeTailShear_backwardOrbit_eq_zero (k : ℕ)
    (x : backwardOrbits (primeTailShear R k)) : x = 0 := by
  apply (backwardOrbits_uniform_torsion_iff (primeTailShear R k) x 2).mp
  intro n
  change primeTailShear R k (primeTailShear R k (x.1 n)) = 0
  exact LinearMap.congr_fun (primeTailShear_sq R k) (x.1 n)

/-- No persistent image survives repeated prime-tail correction. -/
theorem primeTailShear_stableImage_eq_bot (k : ℕ) :
    (⨅ n : ℕ, LinearMap.range (primeTailShear R k ^ n)) = ⊥ := by
  apply le_antisymm _ bot_le
  refine le_trans (iInf_le _ 2) ?_
  have h : primeTailShear R k ^ 2 = 0 := primeTailShear_sq R k
  rw [h, LinearMap.range_zero]

/-- The two-prime gauge as an automorphism of the full prime-chain space. -/
def primeTwoPrimeGaugeEquiv (k : ℕ) : PrimeChainSpace R k ≃ₗ[R] PrimeChainSpace R k :=
  LinearEquiv.ofLinear (primeTwoPrimeGauge R k) (primeTwoPrimeGaugeInv R k)
    (primeTwoPrimeGauge_inverse R k).1 (primeTwoPrimeGauge_inverse R k).2

/-- Evaluation at level zero classifies all compatible two-prime gauge towers. -/
def primeTwoPrimeGaugeTowerEquiv (k : ℕ) :
    backwardOrbits (primeTwoPrimeGauge R k) ≃ₗ[R] PrimeChainSpace R k :=
  backwardOrbitsEquiv (primeTwoPrimeGaugeEquiv R k)

/-- The same classification holds without changing any arithmetic cutoff. -/
def primeTwoPrimeCutoffTowerEquiv (k N : ℕ) :
    backwardOrbits (R := R) (M := ↥(primeChainCutoff R k N))
      (primeTwoPrimeCutoffEquiv R k N).toLinearMap ≃ₗ[R]
      primeChainCutoff R k N :=
  backwardOrbitsEquiv (R := R) (M := ↥(primeChainCutoff R k N))
    (primeTwoPrimeCutoffEquiv R k N)

/-- Repeated inverse gauge adds the square-zero tail correction once per step. -/
theorem primeTwoPrimeGaugeInv_pow_apply (k n : ℕ) (x : PrimeChainSpace R k) :
    (primeTwoPrimeGaugeInv R k ^ n) x = x + n • primeTailShear R k x := by
  have hs (y : PrimeChainSpace R k) : primeTailShear R k (primeTailShear R k y) = 0 :=
    LinearMap.congr_fun (primeTailShear_sq R k) y
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, zero_smul, add_zero]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp only [primeTwoPrimeGaugeInv, LinearMap.add_apply, LinearMap.id_apply,
        map_add, map_nsmul, hs, add_zero, add_smul, one_smul]
      abel

/-- Every backward gauge orbit is determined by its initial chain and tail correction. -/
theorem primeTwoPrimeGauge_backwardOrbit_formula (k : ℕ)
    (x : backwardOrbits (primeTwoPrimeGauge R k)) (n : ℕ) :
    x.1 n = x.1 0 + n • primeTailShear R k (x.1 0) := by
  have he := congrArg (fun y : backwardOrbits (primeTwoPrimeGauge R k) => y.1 n)
    ((primeTwoPrimeGaugeTowerEquiv R k).symm_apply_apply x)
  have hpow : (primeTwoPrimeGaugeInv R k ^ n) (x.1 0) = x.1 n := he
  exact hpow.symm.trans (primeTwoPrimeGaugeInv_pow_apply R k n (x.1 0))

#print axioms primeTailShear_backwardOrbit_eq_zero
#print axioms primeTailShear_stableImage_eq_bot
#print axioms primeTwoPrimeCutoffTowerEquiv
#print axioms primeTwoPrimeGauge_backwardOrbit_formula

end GaloisForLFunctions.EffectiveScalingGeometry
