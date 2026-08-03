import GaloisForLFunctions.RHTower.GammaSignedSummableOrbitNoShorting

/-!
# Signed unconditional Gamma-orbit no-shorting

The summable-orbit theorem assumes absolute summability of the physical
amplitudes.  This module shows that an unordered scalar Gamma orbit cannot
evade that hypothesis by claiming a genuinely beyond-`ℓ¹` cancellation.

Every canonical cross-prime/depth frequency is at least `log 6`, so its
hyperbolic value at the real displacement `1` has a uniform lower bound.
Unconditional summability of the complex scalar orbit at that one point
therefore forces absolute summability of the physical amplitudes.  Bohr
coefficient uniqueness then makes every universal orbit cancellation
coefficientwise trivial.

Thus the surviving Route-R object cannot be an ordinary unordered scalar
`tsum`.  It must remain relative or distribution-valued before frequency
separation, or couple its coefficients to divisor provenance before that
separation.  No Xi zero, computation, or Riemann-hypothesis premise occurs.
-/

open Complex Function Set Topology MeasureTheory intervalIntegral Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A canonical cross-prime/depth product is at least `2 * 3`. -/
theorem xiGammaEulerCanonicalCrossPrimePairNat_six_le
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    6 ≤ xiGammaEulerCanonicalCrossPrimePairNat ij := by
  unfold xiGammaEulerCanonicalCrossPrimePairNat xiGammaEulerValuationNat
  have hp : 2 ≤ (ij.1.1.1 : ℕ) := ij.1.1.1.2.two_le
  have hpq : (ij.1.1.1 : ℕ) < (ij.1.2.1 : ℕ) := ij.2
  have hq : 3 ≤ (ij.1.2.1 : ℕ) := by omega
  have hpe : (ij.1.1.1 : ℕ) ≤ (ij.1.1.1 : ℕ) ^ (ij.1.1.2 + 1) :=
    Nat.le_pow (by omega)
  have hqf : (ij.1.2.1 : ℕ) ≤ (ij.1.2.1 : ℕ) ^ (ij.1.2.2 + 1) :=
    Nat.le_pow (by omega)
  exact (Nat.mul_le_mul hp hq).trans (Nat.mul_le_mul hpe hqf)

/-- The real-unit Gamma orbit has a uniform positive scalar floor. -/
theorem one_le_sinh_xiGammaEulerCanonicalCrossPrimeFrequency
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    1 ≤ Real.sinh (xiGammaEulerCanonicalCrossPrimeFrequency ij) := by
  have hpair := xiGammaEulerCanonicalCrossPrimePairNat_six_le ij
  have hlog : Real.log 6 ≤ xiGammaEulerCanonicalCrossPrimeFrequency ij := by
    rw [xiGammaEulerCanonicalCrossPrimeFrequency]
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hpair
  have hsinh := Real.sinh_le_sinh.mpr hlog
  rw [Real.sinh_log (by norm_num : (0 : ℝ) < 6)] at hsinh
  norm_num at hsinh ⊢
  linarith

/-- In the scalar orbit, summability after multiplication by a hyperbolic
factor bounded below by one forces absolute summability of the original
coefficients. -/
theorem summable_norm_coeff_of_summable_complexSinh_at_one
    (lam : ℕ → ℝ) (hfloor : ∀ n, 1 ≤ Real.sinh (lam n))
    (d : ℕ → ℂ)
    (hsum : Summable (fun n => d n * (Real.sinh (lam n) : ℂ))) :
    Summable (fun n => ‖d n‖) := by
  have hnorm : Summable
      (fun n => ‖d n * (Real.sinh (lam n) : ℂ)‖) := hsum.norm
  refine Summable.of_norm_bounded hnorm (fun n => ?_)
  rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (hfloor n))]
  exact le_mul_of_one_le_right (norm_nonneg _) (hfloor n)

/-- **Unordered-scalar no-shorting.**  If the actual canonical Gamma orbit
is unconditionally summable at the real displacement `1` and vanishes on
the full imaginary modular axis, then every source coefficient is zero. -/
theorem
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_unconditional_noShorting
    (edge : ℕ → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) (c : ℕ → ℂ)
    (hatOne : Summable (fun n =>
      c n * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
        (edge n) 1))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
        (edge n) (Complex.I * (y : ℂ)) = 0) :
    ∀ n, c n = 0 := by
  let d : ℕ → ℂ := fun n =>
    c n * (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge n) : ℂ)
  have hatOne' : Summable (fun n => d n *
      (Real.sinh (xiGammaEulerCanonicalCrossPrimeFrequency (edge n)) : ℂ)) := by
    simpa [d, xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit,
      mul_assoc] using hatOne
  have hd : Summable (fun n => ‖d n‖) :=
    summable_norm_coeff_of_summable_complexSinh_at_one
      (fun n => xiGammaEulerCanonicalCrossPrimeFrequency (edge n))
      (fun n => one_le_sinh_xiGammaEulerCanonicalCrossPrimeFrequency (edge n))
      d hatOne'
  apply
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_summable_noShorting
      edge hedge c
  · simpa [d] using hd
  · exact hvan

/-- `HasSum` is Lean's unordered finite-subset convergence.  Existence of
such a scalar sum at the real displacement `1` is therefore already enough
to exclude a nontrivial beyond-`ℓ¹` universal cancellation. -/
theorem
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_hasSum_noShorting
    (edge : ℕ → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) (c : ℕ → ℂ) (s : ℂ)
    (hatOne : HasSum (fun n =>
      c n * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
        (edge n) 1) s)
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
        (edge n) (Complex.I * (y : ℂ)) = 0) :
    ∀ n, c n = 0 := by
  exact
    xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_unconditional_noShorting
      edge hedge c hatOne.summable hvan

end

end RHTower
