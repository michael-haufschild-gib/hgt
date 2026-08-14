import GaloisForLFunctions.RHTower.RoutePPrimeGammaCubicCarrierIdentification
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthFiniteClockJetGaugeNoGo

/-!
# Route P primitive depth-square modular law

P-G178 identifies the arithmetic content of Route P's doubled Hardy node.  Sending the primitive
cell `(p,e)` to `(p,2e+1)` squares its valuation and doubles its logarithmic clock.  Keeping the
original von Mangoldt half-density under this map requires the modular gain `sqrt (p^(e+1))`, which
is unbounded in counting norm.

That obstruction is not terminal.  The native cubic prime--Gamma carrier absorbs the square of
this gain with the exact Radon--Nikodym factor `1/8`.  Consequently coefficient-faithful depth
squaring is an exact `1/8` contraction of squared energy on every finite cubic-weighted packet.
This explains why the cubic moment and doubled node occur together and supplies a pre-zero,
source-side contraction mechanism.  No source-to-Xi incidence or RH conclusion is asserted here.
-/

open Complex Filter Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Arithmetic squaring on one primitive prime-power cell. -/
def routePPrimitiveDepthSquare (pe : Nat.Primes × ℕ) : Nat.Primes × ℕ :=
  (pe.1, 2 * pe.2 + 1)

theorem xiGammaEulerValuationNat_routePPrimitiveDepthSquare
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerValuationNat (routePPrimitiveDepthSquare pe) =
      xiGammaEulerValuationNat pe ^ 2 := by
  rcases pe with ⟨p, e⟩
  simp only [routePPrimitiveDepthSquare, xiGammaEulerValuationNat]
  rw [← pow_mul]
  congr 1
  omega

theorem xiGammaEulerPrimitiveLogFrequency_routePPrimitiveDepthSquare
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveLogFrequency (routePPrimitiveDepthSquare pe) =
      2 * xiGammaEulerPrimitiveLogFrequency pe := by
  rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerValuationNat_routePPrimitiveDepthSquare, Nat.cast_pow,
    Real.log_pow]
  norm_num

theorem xiGammaEulerPrimitivePrimeDepthLogClock_routePPrimitiveDepthSquare
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitivePrimeDepthLogClock (routePPrimitiveDepthSquare pe) =
      2 * xiGammaEulerPrimitivePrimeDepthLogClock pe := by
  rw [xiGammaEulerPrimitivePrimeDepthLogClock,
    xiGammaEulerPrimitivePrimeDepthLogClock,
    xiGammaEulerValuationNat_routePPrimitiveDepthSquare, Nat.cast_pow,
    Real.log_pow]
  norm_num

theorem xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_depthSquare
    (a : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy a
        (routePPrimitiveDepthSquare i) (routePPrimitiveDepthSquare j) =
      xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy (2 * a) i j := by
  rw [xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy,
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy,
    xiGammaEulerPrimitivePrimeDepthLogClock_routePPrimitiveDepthSquare,
    xiGammaEulerPrimitivePrimeDepthLogClock_routePPrimitiveDepthSquare]
  congr 1
  push_cast
  ring

theorem xiGammaEulerPrimitiveReflectedNormalizedIncidence_depthSquare
    (eps : ℝ) (a : ℂ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectedNormalizedIncidence eps a
        (routePPrimitiveDepthSquare i) (routePPrimitiveDepthSquare j) =
      xiGammaEulerPrimitiveReflectedNormalizedIncidence eps (2 * a) i j := by
  rw [xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy,
    xiGammaEulerPrimitiveReflectedNormalizedIncidence_eq_holonomy,
    xiGammaEulerPrimitiveReflectedOffDiagonalHolonomy_depthSquare]

/-- The modular gain required to keep the original resolved-von-Mangoldt amplitude after
arithmetic depth squaring. -/
def routePPrimitiveDepthSquareModularGain (pe : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt (xiGammaEulerValuationNat pe : ℝ)

theorem routePPrimitiveDepthSquareModularGain_mul_amplitude
    (pe : Nat.Primes × ℕ) :
    (routePPrimitiveDepthSquareModularGain pe : ℂ) *
        finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat (routePPrimitiveDepthSquare pe)) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) := by
  let n := xiGammaEulerValuationNat pe
  have hnNat : n ≠ 0 := by
    dsimp [n, xiGammaEulerValuationNat]
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hnNat
  have hΛ : ArithmeticFunction.vonMangoldt (n ^ 2) =
      ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_apply_pow (by omega)
  rw [routePPrimitiveDepthSquareModularGain,
    xiGammaEulerValuationNat_routePPrimitiveDepthSquare,
    finiteVonMangoldtDepthOneAmplitude, finiteVonMangoldtDepthOneAmplitude]
  norm_cast
  rw [hΛ, Nat.cast_pow]
  rw [← Real.sqrt_mul hn.le]
  congr 1
  simp only [n]
  field_simp [show (xiGammaEulerValuationNat pe : ℝ) ≠ 0 by
    exact_mod_cast hnNat]

theorem routePPrimitiveDepthSquare_injective :
    Function.Injective routePPrimitiveDepthSquare := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  simp only [routePPrimitiveDepthSquare, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by omega⟩

/-- Although the coefficient-preserving modular gain is pointwise unbounded, the cubic Route P
carrier absorbs its square with the exact Radon--Nikodym factor `1/8`. -/
theorem routePPrimitiveDepthSquare_cubicWeight_modularGain_sq
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCubicLogMomentWeight
          (routePPrimitiveDepthSquare pe) *
        routePPrimitiveDepthSquareModularGain pe ^ 2 =
      xiGammaEulerPrimitiveCubicLogMomentWeight pe / 8 := by
  rcases pe with ⟨p, e⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hprime :
      ((p : ℝ)⁻¹) ^ (2 * e + 1) * (p : ℝ) ^ (e + 1) =
        ((p : ℝ)⁻¹) ^ e := by
    rw [show 2 * e + 1 = e + (e + 1) by omega, pow_add]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, mul_one]
  have hdepth :
      (((2 * (e : ℝ) + 1) + 1) ^ 3)⁻¹ =
        (((e : ℝ) + 1) ^ 3)⁻¹ / 8 := by
    have he : (e : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [routePPrimitiveDepthSquareModularGain, Real.sq_sqrt (by positivity)]
  simp only [routePPrimitiveDepthSquare,
    xiGammaEulerPrimitiveCubicLogMomentWeight, xiGammaEulerValuationNat]
  push_cast
  rw [hdepth]
  calc
    (115 / 864 : ℝ) * invNatLogSq p * ((p : ℝ)⁻¹) ^ (2 * e + 1) *
          ((((e : ℝ) + 1) ^ 3)⁻¹ / 8) * (p : ℝ) ^ (e + 1) =
        ((115 / 864 : ℝ) * invNatLogSq p) *
          (((p : ℝ)⁻¹) ^ (2 * e + 1) * (p : ℝ) ^ (e + 1)) *
          (((e : ℝ) + 1) ^ 3)⁻¹ / 8 := by ring
    _ = (115 / 864 : ℝ) * invNatLogSq p * ((p : ℝ)⁻¹) ^ e *
          (((e : ℝ) + 1) ^ 3)⁻¹ / 8 := by rw [hprime]

theorem tendsto_routePPrimitiveDepthSquareModularGain_primeTwo :
    Tendsto
      (fun e : ℕ => routePPrimitiveDepthSquareModularGain
        (⟨2, Nat.prime_two⟩, e)) atTop atTop := by
  have hpow : Tendsto (fun e : ℕ => (2 : ℕ) ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hreal : Tendsto (fun e : ℕ => (((2 : ℕ) ^ (e + 1) : ℕ) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hpow.comp (tendsto_add_atTop_nat 1))
  convert Real.tendsto_sqrt_atTop.comp hreal using 1
  rfl

theorem not_bddAbove_range_routePPrimitiveDepthSquareModularGain :
    ¬ BddAbove (Set.range routePPrimitiveDepthSquareModularGain) := by
  intro hbounded
  rcases hbounded with ⟨C, hC⟩
  have hEventually :
      ∀ᶠ e : ℕ in atTop,
        C < routePPrimitiveDepthSquareModularGain
          (⟨2, Nat.prime_two⟩, e) :=
    tendsto_routePPrimitiveDepthSquareModularGain_primeTwo.eventually_gt_atTop C
  rcases hEventually.exists with ⟨e, he⟩
  exact (not_lt_of_ge (hC ⟨(⟨2, Nat.prime_two⟩, e), rfl⟩)) he

/-- Native natural-number form of the exact cubic Radon--Nikodym law. -/
theorem routePPrimeGammaCubicWeight_depthSquare_modularGain_sq
    (pe : Nat.Primes × ℕ) :
    routePPrimeGammaCubicWeight
          (xiGammaEulerValuationNat (routePPrimitiveDepthSquare pe)) *
        routePPrimitiveDepthSquareModularGain pe ^ 2 =
      routePPrimeGammaCubicWeight (xiGammaEulerValuationNat pe) / 8 := by
  rw [routePPrimeGammaCubicWeight_valuation,
    routePPrimeGammaCubicWeight_valuation,
    routePPrimitiveDepthSquare_cubicWeight_modularGain_sq]

/-- On every finite primitive packet, coefficient-faithful arithmetic squaring is an exact
`1/8` contraction for squared energy in the native cubic source measure. -/
theorem routePPrimitiveDepthSquare_cubicWeightedEnergy
    (s : Finset (Nat.Primes × ℕ)) (f : Nat.Primes × ℕ → ℝ) :
    ∑ pe ∈ s,
        xiGammaEulerPrimitiveCubicLogMomentWeight
            (routePPrimitiveDepthSquare pe) *
          (routePPrimitiveDepthSquareModularGain pe * f pe) ^ 2 =
      (∑ pe ∈ s,
          xiGammaEulerPrimitiveCubicLogMomentWeight pe * f pe ^ 2) / 8 := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro pe hpe
  rw [mul_pow]
  rw [← mul_assoc,
    routePPrimitiveDepthSquare_cubicWeight_modularGain_sq]
  ring

/-- P-G173's doubled Hardy node is the actual squared prime-power clock, but with the original
collision ordinate retained. -/
theorem routePCollisionDoubledNode_inr_eq_depthSquare
    {N : ℕ} (R : ℝ) (pe : Fin N → Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (i : Fin N) :
    routePCollisionDoubledNode R
        (fun j => xiGammaEulerPrimitiveLogFrequency (pe j)) kappa (Sum.inr i) =
      ((R * xiGammaEulerPrimitiveLogFrequency
          (routePPrimitiveDepthSquare (pe i)) : ℝ) : ℂ) -
        (kappa i : ℂ) * I := by
  simp [routePCollisionDoubledNode,
    xiGammaEulerPrimitiveLogFrequency_routePPrimitiveDepthSquare]

end

end RHTower
