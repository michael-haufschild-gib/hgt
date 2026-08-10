import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# The mean square passes to the Ramaré bilinear form

The bilinear factorisation is exact up to an additive error `E`, so the two mean squares differ by
at most the trivial amount the error can contribute:

```text
∫_{|w| ≤ T} ‖ ∑_{n ≤ M} μ(n) n^{2πiw} ‖² dw  ≤  2∫_{|w| ≤ T} ‖B(w)‖² dw  +  4T·E² ,
```

`B(w) = ∑_{p ∈ P} μ(p)p^{2πiw}·(∑_{p ∤ m} (μ(m)/(ω_P(m)+1)) m^{2πiw})`.  With a dyadic prime range
`P ⊂ [Q, 2Q]` the square-multiple part of `E` is `O(M/(Q log Q))`, so its contribution `4T·E²` is
below the budget `ε·M²` as soon as `T·M²/(Q log Q)² ≤ ε M²`, i.e. for every height `T` up to
`ε(Q log Q)²`.  The whole residue is then carried by the bilinear form, whose prime factor is
prime-supported and therefore obeys the sharp near-diagonal weight.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

theorem continuous_unitLogPhase (n : ℕ) : Continuous fun w : ℝ => unitLogPhase w n := by
  refine Complex.continuous_exp.comp ?_
  refine Continuous.mul ?_ continuous_const
  refine Complex.continuous_ofReal.comp ?_
  fun_prop

theorem continuous_moebiusPhase (n : ℕ) : Continuous fun w : ℝ => moebiusPhase w n := by
  simp only [moebiusPhase]
  exact continuous_const.mul (continuous_unitLogPhase n)

/-- The Ramaré bilinear form of the Möbius Dirichlet polynomial on `[1, M]`. -/
def ramareBilinear (P : Finset ℕ) (M : ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ P, moebiusPhase w p
    * logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w

theorem continuous_ramareBilinear (P : Finset ℕ) (M : ℕ) :
    Continuous fun w : ℝ => ramareBilinear P M w := by
  refine continuous_finsetSum P fun p _ => ?_
  exact (continuous_moebiusPhase p).mul (continuous_logPoly _ _)

/-- A norm square is at most twice the square of an approximant plus twice the square of the
error. -/
theorem normSq_le_two_add_two {a b : ℂ} {E : ℝ} (hE : ‖a - b‖ ≤ E) :
    ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * E ^ 2 := by
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) hE
  have htri : ‖a‖ ≤ ‖b‖ + E := by
    have := norm_add_le b (a - b)
    have hb : b + (a - b) = a := by ring
    rw [hb] at this
    linarith [this, hE]
  have hsq : ‖a‖ ^ 2 ≤ (‖b‖ + E) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (‖b‖ - E)]

/-- **The Möbius mean square passes to the Ramaré bilinear form.** -/
theorem integral_Icc_normSq_logPoly_moebius_le_bilinear {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {T E : ℝ} (hT : 0 ≤ T)
    (hE : (∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)))
        + (({n ∈ Finset.Icc 1 M | primeFactorsIn P n = ∅}).card : ℝ) ≤ E) :
    (∫ w in Set.Icc (-T) T,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ 2 * (∫ w in Set.Icc (-T) T, ‖ramareBilinear P M w‖ ^ 2) + 4 * T * E ^ 2 := by
  classical
  have hcontF : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hcontB : Continuous fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2 :=
    ((continuous_ramareBilinear P M).norm).pow 2
  have hle : ∀ w ∈ Set.Icc (-T) T,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2
        ≤ 2 * ‖ramareBilinear P M w‖ ^ 2 + 2 * E ^ 2 := by
    intro w _
    refine normSq_le_two_add_two ?_
    rw [ramareBilinear]
    exact le_trans (norm_logPoly_moebius_Icc_sub_ramare_bilinear_le hPprime M w) hE
  have hmajInt : IntegrableOn
      (fun w : ℝ => 2 * ‖ramareBilinear P M w‖ ^ 2 + 2 * E ^ 2) (Set.Icc (-T) T) volume :=
    ((hcontB.const_mul 2).add continuous_const).integrableOn_Icc
  have hmono := setIntegral_mono_on hcontF.integrableOn_Icc hmajInt measurableSet_Icc hle
  refine le_trans hmono (le_of_eq ?_)
  have hBint : IntegrableOn (fun w : ℝ => ‖ramareBilinear P M w‖ ^ 2)
      (Set.Icc (-T) T) volume := hcontB.integrableOn_Icc
  have hconstInt : IntegrableOn (fun _ : ℝ => 2 * E ^ 2) (Set.Icc (-T) T) volume :=
    (continuous_const).integrableOn_Icc
  rw [integral_add (hBint.const_mul 2) hconstInt, integral_const_mul, setIntegral_const,
    smul_eq_mul]
  have hv : volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hv]
  ring

end RHTower.Sieve

end
