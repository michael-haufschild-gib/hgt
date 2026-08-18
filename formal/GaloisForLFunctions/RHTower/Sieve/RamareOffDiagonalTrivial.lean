import GaloisForLFunctions.RHTower.Sieve.RamarePrimeOffDiagonal
import GaloisForLFunctions.RHTower.Sieve.RamareEnergy

/-!
# The trivial bound on the Ramaré prime off-diagonal

Pairing the two cofactor polynomials by the arithmetic–geometric mean and summing over ordered pairs
of designated primes gives

`|ramarePrimeOffDiagonal P M W| ≤ (#P − 1) · ∑_{p ∈ P} ∫_{|w| ≤ W} ‖G_p‖² ,`

with no oscillation used at all.  Against the diagonal budget `10WM + εM²` this is over the
Matomäki–Radziwiłł budget by exactly the factor `#P`, which is the precise size of the saving the
oscillation of `p^{2πiw}\overline{q^{2πiw}}` has to produce.  Every improvement of the route is
measured against this inequality.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

theorem integrableOn_normSq_ramareCofactorPoly (P : Finset ℕ) (M p : ℕ) (W : ℝ) :
    IntegrableOn (fun w : ℝ => ‖ramareCofactorPoly P M p w‖ ^ 2) (Set.Icc (-W) W) volume :=
  (((continuous_ramareCofactorPoly P M p).norm).pow 2).integrableOn_Icc

/-- **The off-diagonal, bounded without oscillation.** -/
theorem abs_ramarePrimeOffDiagonal_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ)
    (W : ℝ) :
    |ramarePrimeOffDiagonal P M W|
      ≤ ((P.card : ℝ) - 1)
          * ∑ p ∈ P, ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w‖ ^ 2 := by
  classical
  set I : ℕ → ℝ := fun p => ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w‖ ^ 2 with hIdef
  have hI0 : ∀ p, 0 ≤ I p := by
    intro p
    rw [hIdef]
    refine setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
  -- the pointwise pairing bound
  have hpair : ∀ p ∈ P, ∀ q ∈ P,
      |∫ w in Set.Icc (-W) W,
          ((moebiusPhase w p * ramareCofactorPoly P M p w)
            * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re|
        ≤ (I p + I q) / 2 := by
    intro p hp q hq
    have hbd : ∀ w ∈ Set.Icc (-W) W,
        |((moebiusPhase w p * ramareCofactorPoly P M p w)
            * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re|
          ≤ (‖ramareCofactorPoly P M p w‖ ^ 2 + ‖ramareCofactorPoly P M q w‖ ^ 2) / 2 := by
      intro w _
      have hre := Complex.abs_re_le_norm
        ((moebiusPhase w p * ramareCofactorPoly P M p w)
          * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w))
      have hnorm : ‖(moebiusPhase w p * ramareCofactorPoly P M p w)
            * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)‖
          = ‖ramareCofactorPoly P M p w‖ * ‖ramareCofactorPoly P M q w‖ := by
        rw [norm_mul, norm_mul, RCLike.norm_conj, norm_mul,
          norm_moebiusPhase_prime (hPprime p hp), norm_moebiusPhase_prime (hPprime q hq),
          one_mul, one_mul]
      rw [hnorm] at hre
      refine hre.trans ?_
      nlinarith [sq_nonneg (‖ramareCofactorPoly P M p w‖ - ‖ramareCofactorPoly P M q w‖)]
    have hint : IntegrableOn (fun w : ℝ =>
        ((moebiusPhase w p * ramareCofactorPoly P M p w)
          * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re)
        (Set.Icc (-W) W) volume := by
      refine (Continuous.integrableOn_Icc ?_)
      exact Complex.continuous_re.comp
        (((continuous_moebiusPhase p).mul (continuous_ramareCofactorPoly P M p)).mul
          (((continuous_moebiusPhase q).mul
            (continuous_ramareCofactorPoly P M q)).star))
    have hmajInt : IntegrableOn (fun w : ℝ =>
        (‖ramareCofactorPoly P M p w‖ ^ 2 + ‖ramareCofactorPoly P M q w‖ ^ 2) / 2)
        (Set.Icc (-W) W) volume :=
      ((integrableOn_normSq_ramareCofactorPoly P M p W).add
        (integrableOn_normSq_ramareCofactorPoly P M q W)).div_const 2
    have hstep : |∫ w in Set.Icc (-W) W,
        ((moebiusPhase w p * ramareCofactorPoly P M p w)
          * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re|
        ≤ ∫ w in Set.Icc (-W) W,
            (‖ramareCofactorPoly P M p w‖ ^ 2 + ‖ramareCofactorPoly P M q w‖ ^ 2) / 2 := by
      refine le_trans (abs_integral_le_integral_abs) ?_
      exact setIntegral_mono_on hint.abs hmajInt measurableSet_Icc hbd
    refine hstep.trans (le_of_eq ?_)
    rw [integral_div, integral_add (integrableOn_normSq_ramareCofactorPoly P M p W)
      (integrableOn_normSq_ramareCofactorPoly P M q W)]
  -- sum the pairs
  have hsum : |ramarePrimeOffDiagonal P M W|
      ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, (I p + I q) / 2 := by
    rw [ramarePrimeOffDiagonal]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun p hp => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun q hq => hpair p hp q (Finset.mem_of_mem_erase hq)
  refine hsum.trans (le_of_eq ?_)
  have hinner : ∀ p ∈ P, ∑ q ∈ P.erase p, (I p + I q) / 2
      = (((P.card : ℝ) - 1) * I p + ((∑ q ∈ P, I q) - I p)) / 2 := by
    intro p hp
    have hcard1 : 1 ≤ P.card := Finset.card_pos.2 ⟨p, hp⟩
    have hcard : (((P.card - 1 : ℕ)) : ℝ) = (P.card : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hcard1
      simpa using this
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_erase_of_mem hp, Finset.sum_erase_eq_sub hp, nsmul_eq_mul, hcard]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The off-diagonal against the diagonal budget.**  Without oscillation the off-diagonal is at
most `#P` times the diagonal, so the Möbius mean square admits the unconditional affine majorant
whose intercept exceeds the Matomäki--Radziwiłł budget by exactly the factor `#P`. -/
theorem integral_Icc_normSq_logPoly_moebius_le_trivialOffDiagonal {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {T δ ε : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPM : (P.card : ℝ) ≤ (M : ℝ))
    (hA : 15 * Real.exp 1 / (2 * ε) ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
    (hsq : ∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ ε * (M : ℝ))
    (hsq2 : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ 2 * ε / (5 * Real.exp 1)) :
    (∫ w in Set.Icc (-T) T,
        ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (1 + (P.card : ℝ)) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2)
        + 2 * (1 + 1 / δ)
            * (12 * T * (M : ℝ) + (1 + 5 * Real.exp 1 / 2) * ε * (M : ℝ) ^ 2) := by
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hdiag := sum_integral_normSq_ramareCofactorPoly_le_budget hPprime M hT hε hsq2
  have hOD := abs_ramarePrimeOffDiagonal_le hPprime M T
  have hdiag' : (∑ p ∈ P, ∫ w in Set.Icc (-T) T, ‖ramareCofactorPoly P M p w‖ ^ 2)
      ≤ 10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2 := by
    simp only [ramareCofactorPoly]
    exact hdiag
  have hbudget0 : (0 : ℝ) ≤ 10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2 := by positivity
  have hcard0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hsum0 : (0 : ℝ) ≤ ∑ p ∈ P, ∫ w in Set.Icc (-T) T, ‖ramareCofactorPoly P M p w‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
  have hODle : ramarePrimeOffDiagonal P M T
      ≤ (P.card : ℝ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2) := by
    have h1 : ramarePrimeOffDiagonal P M T ≤ |ramarePrimeOffDiagonal P M T| := le_abs_self _
    have h2 : ((P.card : ℝ) - 1)
        * ∑ p ∈ P, ∫ w in Set.Icc (-T) T, ‖ramareCofactorPoly P M p w‖ ^ 2
        ≤ (P.card : ℝ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2) := by
      nlinarith [hdiag', hsum0, hcard0, hbudget0]
    linarith [h1, hOD, h2]
  have hbase := integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal hPprime M hT hδ hε hε1
    hPM hA hsq hsq2
  have hc0 : (0 : ℝ) ≤ 1 + δ := by linarith
  have hmul : (1 + δ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2 + ramarePrimeOffDiagonal P M T)
      ≤ (1 + δ) * (1 + (P.card : ℝ)) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hODle hc0
    calc (1 + δ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2 + ramarePrimeOffDiagonal P M T)
        = (1 + δ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2)
          + (1 + δ) * ramarePrimeOffDiagonal P M T := by ring
      _ ≤ (1 + δ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2)
          + (1 + δ) * ((P.card : ℝ) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2)) := by linarith [h]
      _ = (1 + δ) * (1 + (P.card : ℝ)) * (10 * T * (M : ℝ) + ε * (M : ℝ) ^ 2) := by ring
  linarith [hbase, hmul]

end

end RHTower.Sieve
