import GaloisForLFunctions.RHTower.PrimeBurnolFiniteModularSupport
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Prime Burnol finite off-diagonal faithfulness

The complete literal Burnol Gram has an explicit Cauchy-cubic entry formula. Every entry is
nonzero, so no cross-prime source edge disappears before theta completion. This is analytic
source formation only; it uses no divisor, Xi datum, positivity selection, or numerical
computation.
-/

open Complex Matrix Set MeasureTheory

namespace RHTower

noncomputable section

def primeBurnolPairRate
    (u v : Nat.Primes × ℕ) (kappa nu : ℝ) : ℂ :=
  ((primeBurnolLogFrequency u + primeBurnolLogFrequency v : ℝ) : ℂ) +
    I * ((nu - kappa : ℝ) : ℂ)

theorem primeBurnolPairRate_re_pos
    (u v : Nat.Primes × ℕ) (kappa nu : ℝ) :
    0 < (primeBurnolPairRate u v kappa nu).re := by
  simp [primeBurnolPairRate]
  exact add_pos (primeBurnolLogFrequency_pos u) (primeBurnolLogFrequency_pos v)

theorem star_primeBurnolAmplitude (u : Nat.Primes × ℕ) :
    star (primeBurnolAmplitude u) = primeBurnolAmplitude u := by
  rw [primeBurnolAmplitude]
  simp

theorem star_primeBurnolWindowFeature_mul
    (u v : Nat.Primes × ℕ) (kappa nu L : ℝ) :
    star (primeBurnolWindowFeature u kappa L) *
        primeBurnolWindowFeature v nu L =
      primeBurnolAmplitude u * primeBurnolAmplitude v *
        ((L : ℂ) ^ 2 *
          Complex.exp (-(primeBurnolPairRate u v kappa nu * (L : ℂ)))) := by
  rw [primeBurnolWindowFeature, primeBurnolWindowFeature]
  rw [star_mul, star_mul, star_primeBurnolAmplitude]
  rw [show star (Complex.exp (primeBurnolComplexExponent u kappa * (L : ℂ))) =
      Complex.exp (star (primeBurnolComplexExponent u kappa * (L : ℂ))) by
    change (starRingEnd ℂ) (Complex.exp _) = Complex.exp ((starRingEnd ℂ) _)
    exact (Complex.exp_conj _).symm]
  rw [star_mul, show star (L : ℂ) = (L : ℂ) by simp]
  rw [show
      Complex.exp ((L : ℂ) * star (primeBurnolComplexExponent u kappa)) *
            ((L : ℂ) * primeBurnolAmplitude u) *
          (primeBurnolAmplitude v * (L : ℂ) *
            Complex.exp (primeBurnolComplexExponent v nu * (L : ℂ))) =
        primeBurnolAmplitude u * primeBurnolAmplitude v * ((L : ℂ) ^ 2 *
          (Complex.exp ((L : ℂ) * star (primeBurnolComplexExponent u kappa)) *
            Complex.exp (primeBurnolComplexExponent v nu * (L : ℂ)))) by ring]
  rw [← Complex.exp_add]
  congr 2
  have hstar :
      star (primeBurnolComplexExponent u kappa) =
        -((primeBurnolLogFrequency u : ℂ) - I * (kappa : ℂ)) := by
    apply Complex.ext <;> simp [primeBurnolComplexExponent]
  rw [hstar, primeBurnolComplexExponent, primeBurnolPairRate]
  push_cast
  ring_nf

theorem inner_primeBurnolWindowFeatureLp_eq
    (u v : Nat.Primes × ℕ) (kappa nu : ℝ) :
    inner ℂ (primeBurnolWindowFeatureLp u kappa)
        (primeBurnolWindowFeatureLp v nu) =
      primeBurnolAmplitude u * primeBurnolAmplitude v *
        ((2 : ℂ) / primeBurnolPairRate u v kappa nu ^ 3) := by
  rw [MeasureTheory.L2.inner_def]
  have hinner :
      (∫ L : ℝ,
        inner ℂ
          ((primeBurnolWindowFeatureLp u kappa : primeBurnolHalfLineL2) L)
          ((primeBurnolWindowFeatureLp v nu : primeBurnolHalfLineL2) L)
          ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫ L : ℝ in Ioi 0,
        primeBurnolAmplitude u * primeBurnolAmplitude v *
          ((L : ℂ) ^ 2 *
            Complex.exp (-(primeBurnolPairRate u v kappa nu * (L : ℂ)))) := by
    apply integral_congr_ae
    filter_upwards [primeBurnolWindowFeatureLp_coeFn u kappa,
      primeBurnolWindowFeatureLp_coeFn v nu] with L hu hv
    rw [hu, hv, RCLike.inner_apply, starRingEnd_apply, mul_comm,
      star_primeBurnolWindowFeature_mul]
  rw [hinner, MeasureTheory.integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp
      (primeBurnolPairRate_re_pos u v kappa nu) 2]
  norm_num

theorem primeBurnolWindowGramMatrix_apply
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) :
    primeBurnolWindowGramMatrix pe kappa i j =
      primeBurnolAmplitude (pe i) * primeBurnolAmplitude (pe j) *
        ((2 : ℂ) / primeBurnolPairRate (pe i) (pe j) (kappa i) (kappa j) ^ 3) := by
  rw [primeBurnolWindowGramMatrix, Matrix.gram_apply,
    inner_primeBurnolWindowFeatureLp_eq]

theorem primeBurnolWindowGramMatrix_apply_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) : primeBurnolWindowGramMatrix pe kappa i j ≠ 0 := by
  rw [primeBurnolWindowGramMatrix_apply]
  apply mul_ne_zero (mul_ne_zero (primeBurnolAmplitude_ne_zero _) (primeBurnolAmplitude_ne_zero _))
  apply div_ne_zero
  · norm_num
  · apply pow_ne_zero
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    exact (primeBurnolPairRate_re_pos _ _ _ _).ne' hre

end

end RHTower
