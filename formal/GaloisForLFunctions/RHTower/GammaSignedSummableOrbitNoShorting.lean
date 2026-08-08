import GaloisForLFunctions.RHTower.GammaSignedFiniteOrbitNoShorting
import GaloisForLFunctions.HTGeometry.BohrCoefficientUniqueness

/-!
# Signed summable Gamma-orbit no-shorting

Finite signed rigidity still leaves cancellation after a countable limit.
This module closes every absolutely summable orbit-amplitude chain.

For distinct positive frequencies, an absolutely summable series of
`sinh(lambda_n z)` cannot vanish on the imaginary modular axis unless every
coefficient is zero.  The proof doubles each sinh into its positive and
negative unitary characters and uses Bohr--Cesaro coefficient extraction.
Positivity prevents cross-sign frequency collisions; injectivity isolates
the selected positive-frequency coefficient.

Applied to the actual canonical cross-prime/depth Gamma orbit, unique
factorization supplies frequency injectivity and the physical amplitude is
strictly positive.  Hence every orbit-universal signed chain with summable
physical amplitudes is coefficientwise zero.

The surviving Route-R source null-homotopy must therefore be singular beyond
absolute summability, or couple its coefficients nonseparably to divisor
provenance.  No Xi zero, computation, or RH premise occurs.
-/

open Complex Function Set Topology MeasureTheory intervalIntegral Filter
open scoped BigOperators

namespace RHTower

noncomputable section

theorem complexSinh_tsum_coeff_zero
    (lam : ℕ → ℝ) (hlam : Function.Injective lam)
    (hpos : ∀ n, 0 < lam n) (c : ℕ → ℂ)
    (hsum : Summable (fun n => ‖c n‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.sinh ((lam n : ℂ) * (Complex.I * (y : ℂ))) = 0) :
    ∀ n, c n = 0 := by
  let C : ℕ → Bool → ℂ := fun n b => if b then c n / 2 else -(c n / 2)
  let F : ℕ → Bool → ℝ := fun n b => if b then lam n else -lam n
  have hCsum : Summable (fun n => ∑ b : Bool, ‖C n b‖) := by
    have heq : (fun n => ∑ b : Bool, ‖C n b‖) = fun n => ‖c n‖ := by
      funext n
      simp [C]
    rw [heq]
    exact hsum
  have hterm (n : ℕ) (y : ℝ) :
      ∑ b : Bool, C n b *
          Complex.exp ((F n b : ℂ) * Complex.I * (y : ℂ)) =
        c n * Complex.sinh ((lam n : ℂ) * (Complex.I * (y : ℂ))) := by
    simp [C, F, Complex.sinh]
    ring
  intro m
  have havg := char_avg_finsum (Finset.univ : Finset Bool) C
    (fun n b => F n b - lam m) hCsum
  have hzero : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0 : ℝ)..T,
      ∑' n : ℕ, ∑ b : Bool, C n b *
        Complex.exp (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ)))
      atTop (𝓝 0) := by
    have hInt : ∀ y : ℝ, (∑' n : ℕ, ∑ b : Bool, C n b *
        Complex.exp (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ))) = 0 := by
      intro y
      have hshift (n : ℕ) :
          (∑ b : Bool, C n b *
              Complex.exp (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ))) =
            Complex.exp (((-lam m : ℝ) : ℂ) * Complex.I * (y : ℂ)) *
              (∑ b : Bool, C n b *
                Complex.exp ((F n b : ℂ) * Complex.I * (y : ℂ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [show (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ)) =
            (F n b : ℂ) * Complex.I * (y : ℂ) +
              ((-lam m : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [tsum_congr hshift, tsum_mul_left]
      simp_rw [hterm]
      rw [hvan y, mul_zero]
    have hfun : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0 : ℝ)..T,
        ∑' n : ℕ, ∑ b : Bool, C n b *
          Complex.exp (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ))) =
        fun _ : ℝ => (0 : ℂ) := by
      funext T
      rw [show (fun y : ℝ => ∑' n : ℕ, ∑ b : Bool, C n b *
          Complex.exp (((F n b - lam m : ℝ) : ℂ) * Complex.I * (y : ℂ))) =
          fun _ => (0 : ℂ) from funext hInt,
        intervalIntegral.integral_zero, mul_zero]
    rw [hfun]
    exact tendsto_const_nhds
  have hdiag :
      (∑' n : ℕ, ∑ b : Bool,
        if F n b - lam m = 0 then C n b else 0) = 0 :=
    tendsto_nhds_unique havg hzero
  have hcollapse :
      (∑' n : ℕ, ∑ b : Bool,
        if F n b - lam m = 0 then C n b else 0) = c m / 2 := by
    have hpt : ∀ n : ℕ,
        (∑ b : Bool, if F n b - lam m = 0 then C n b else 0) =
          if n = m then c m / 2 else 0 := by
      intro n
      by_cases hnm : n = m
      · subst n
        have hneg : -lam m - lam m ≠ 0 := by linarith [hpos m]
        simp [C, F, hneg]
      · have hplus : lam n - lam m ≠ 0 := by
          exact sub_ne_zero.mpr (fun h => hnm (hlam h))
        have hneg : -lam n - lam m ≠ 0 := by linarith [hpos n, hpos m]
        simp [C, F, hnm, hplus, hneg]
    rw [tsum_congr hpt, tsum_eq_single m (fun n hn => if_neg hn), if_pos rfl]
  rw [hcollapse] at hdiag
  exact (div_eq_zero_iff.mp hdiag).resolve_right (by norm_num)

/-- **Absolutely summable signed Gamma-orbit no-shorting.**  Even a
countably infinite canonical cross-prime depth chain cannot annihilate the
universal modular orbit when its physical orbit amplitudes are absolutely
summable. -/
theorem xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_summable_noShorting
    (edge : ℕ → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) (c : ℕ → ℂ)
    (hsum : Summable (fun n =>
      ‖c n * (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge n) : ℂ)‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit
        (edge n) (Complex.I * (y : ℂ)) = 0) :
    ∀ n, c n = 0 := by
  let d : ℕ → ℂ := fun n =>
    c n * (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge n) : ℂ)
  have hd : ∀ n, d n = 0 := by
    apply complexSinh_tsum_coeff_zero
      (fun n => xiGammaEulerCanonicalCrossPrimeFrequency (edge n))
      (xiGammaEulerCanonicalCrossPrimeFrequency_injective.comp hedge)
      (fun n => xiGammaEulerCanonicalCrossPrimeFrequency_pos (edge n)) d
    · simpa [d] using hsum
    · intro y
      simpa only [d,
        xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit, mul_assoc] using hvan y
  intro n
  have hn := hd n
  simp only [d] at hn
  exact (mul_eq_zero.mp hn).resolve_right
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude_pos (edge n))))

end

end RHTower
