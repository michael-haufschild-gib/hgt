import GaloisForLFunctions.RHTower.XiWardMultiscaleHellingerCauchySeparator
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthBiorthogonalCommonTest

/-!
# All-scale Hellinger separator at the balanced Euler-source wall

The logarithmic-scale dyadic Hellinger kernel gives the same `log (9/8)` self-charge at every
positive frequency. On the primitive Euler carrier, balanced source/co-source reflection is the
literal von Mangoldt prime-power weight. Consequently the all-scale source diagonal is a nonzero
constant multiple of the already-proved nonsummable balanced Euler family.

This formally closes the naive finite-source realization of the multiscale zero separator. A
viable density argument would need a renormalized, height-localized cofinal source law rather than
a global Hilbert trace at balanced reflection.
-/

namespace RHTower

noncomputable section

/-- Positive prime-power logarithmic frequency on the primitive Euler carrier. -/
def xiGammaEulerPrimitiveLogFrequency (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (xiGammaEulerValuationNat pe : ℝ)

theorem xiGammaEulerPrimitiveLogFrequency_pos
    (pe : Nat.Primes × ℕ) :
    0 < xiGammaEulerPrimitiveLogFrequency pe := by
  have hpow : 1 < (pe.1 : ℕ) ^ (pe.2 + 1) :=
    one_lt_pow₀ pe.1.property.one_lt (Nat.succ_ne_zero pe.2)
  rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat]
  exact Real.log_pos (by exact_mod_cast hpow)

/-- Full logarithmic-scale diagonal placed on the balanced primitive Euler source. -/
def xiGammaEulerPrimitiveDyadicAllScaleDiagonal
    (a : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  (Real.log (9 / 8 : ℝ) : ℂ) *
    (xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
      star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe))

/-- The fixed all-scale factor is exactly the dyadic Hellinger self-kernel at every
prime-power logarithmic frequency. -/
theorem xiGammaEulerPrimitiveDyadicAllScaleDiagonal_eq_kernel
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveDyadicAllScaleDiagonal a pe =
      (dyadicHellingerHorizontalKernel
        (xiGammaEulerPrimitiveLogFrequency pe)
        (xiGammaEulerPrimitiveLogFrequency pe) : ℂ) *
      (xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
        star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe)) := by
  rw [xiGammaEulerPrimitiveDyadicAllScaleDiagonal,
    dyadicHellingerHorizontalKernel_self
      (xiGammaEulerPrimitiveLogFrequency_pos pe)]

/-- At balanced reflection the all-scale diagonal is the fixed `log(9/8)` multiple of the
literal von Mangoldt prime-power weight. -/
theorem xiGammaEulerPrimitiveDyadicAllScaleDiagonal_eq_vonMangoldtWeight
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveDyadicAllScaleDiagonal a pe =
      (Real.log (9 / 8 : ℝ) : ℂ) *
        finiteVonMangoldtWeight (xiGammaEulerValuationNat pe) := by
  rw [xiGammaEulerPrimitiveDyadicAllScaleDiagonal,
    xiGammaEulerPrimitiveBalancedReflectionCoeff_eq]

/-- **All-scale Euler-source wall no-go.** The scale-invariant diagonal that separates every
positive zero displacement also preserves every balanced prime-power coefficient. Its full
primitive Euler diagonal is therefore nonsummable. -/
theorem not_summable_xiGammaEulerPrimitiveDyadicAllScaleDiagonal
    (a : ℝ) :
    ¬ Summable (xiGammaEulerPrimitiveDyadicAllScaleDiagonal a) := by
  intro hsum
  have hlog : Real.log (9 / 8 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hlogComplex : (Real.log (9 / 8 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hlog
  have hbalanced : Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
        star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe)) :=
    (summable_mul_left_iff hlogComplex).mp hsum
  exact not_summable_xiGammaEulerPrimitiveBalancedReflectionCoeff a hbalanced

end

end RHTower
