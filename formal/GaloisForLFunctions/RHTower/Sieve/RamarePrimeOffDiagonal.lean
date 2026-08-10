import GaloisForLFunctions.RHTower.Sieve.RamareSquareMultiple

/-!
# The prime off-diagonal of the Ramaré bilinear form

Expanding the mean square of `B(w) = ∑_{p ∈ P} μ(p)p^{2πiw}·G_p(w)` over pairs of designated primes
separates it exactly into its diagonal and its off-diagonal.  Every `p ∈ P` is prime, so
`|μ(p)p^{2πiw}| = 1` and the diagonal is the plain mean square of the cofactor polynomials:

```text
∫_{|w| ≤ W}‖B‖² dw  =  ∑_{p ∈ P} ∫_{|w| ≤ W}‖G_p‖² dw
                        + ∑_{p ≠ q} ∫_{|w| ≤ W} Re( p^{2πiw}\overline{q^{2πiw}} G_p \overline{G_q} ) .
```

The diagonal is inside the Matomäki–Radziwiłł budget because the Ramaré weight preserves the
coefficient energy; the off-diagonal is a bilinear oscillatory sum over **pairs of primes**, and it
is the entire remaining content of the route.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

/-- The cofactor polynomial of a designated prime. -/
def ramareCofactorPoly (P : Finset ℕ) (M p : ℕ) (w : ℝ) : ℂ :=
  logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w

theorem ramareBilinear_eq_sum (P : Finset ℕ) (M : ℕ) (w : ℝ) :
    ramareBilinear P M w = ∑ p ∈ P, moebiusPhase w p * ramareCofactorPoly P M p w := rfl

theorem continuous_ramareCofactorPoly (P : Finset ℕ) (M p : ℕ) :
    Continuous fun w : ℝ => ramareCofactorPoly P M p w := continuous_logPoly _ _

/-- A designated prime carries a unimodular coefficient: `μ(p) = -1`. -/
theorem norm_moebiusPhase_prime {p : ℕ} (hp : p.Prime) (w : ℝ) : ‖moebiusPhase w p‖ = 1 := by
  rw [moebiusPhase, norm_mul, norm_unitLogPhase, mul_one,
    ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- The squared norm of a finite sum, expanded over pairs. -/
theorem normSq_sum_eq_double (P : Finset ℕ) (f : ℕ → ℂ) :
    ‖∑ p ∈ P, f p‖ ^ 2 = ∑ p ∈ P, ∑ q ∈ P, (f p * (starRingEnd ℂ) (f q)).re := by
  have h1 : ‖∑ p ∈ P, f p‖ ^ 2 = ((∑ p ∈ P, f p) * (starRingEnd ℂ) (∑ p ∈ P, f p)).re := by
    rw [Complex.mul_conj, Complex.sq_norm]
    norm_num
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun p _ => Complex.re_sum _ _

/-- **The pointwise diagonal/off-diagonal split of the bilinear form.** -/
theorem normSq_ramareBilinear_eq {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) (w : ℝ) :
    ‖ramareBilinear P M w‖ ^ 2
      = (∑ p ∈ P, ‖ramareCofactorPoly P M p w‖ ^ 2)
        + ∑ p ∈ P, ∑ q ∈ P.erase p,
            ((moebiusPhase w p * ramareCofactorPoly P M p w)
              * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re := by
  classical
  rw [ramareBilinear_eq_sum, normSq_sum_eq_double, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.add_sum_erase P _ hp]
  congr 1
  rw [Complex.mul_conj]
  simp only [Complex.ofReal_re]
  rw [← Complex.sq_norm, norm_mul, norm_moebiusPhase_prime (hPprime p hp), one_mul]

/-- The prime off-diagonal of the Ramaré bilinear mean square. -/
def ramarePrimeOffDiagonal (P : Finset ℕ) (M : ℕ) (W : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P.erase p, (∫ w in Set.Icc (-W) W,
    ((moebiusPhase w p * ramareCofactorPoly P M p w)
      * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re)

/-- **The bilinear mean square is its `p`-diagonal plus its prime off-diagonal.** -/
theorem integral_normSq_ramareBilinear_eq {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ)
    (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      = (∑ p ∈ P, ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w‖ ^ 2)
        + ramarePrimeOffDiagonal P M W := by
  classical
  have hcontG : ∀ p : ℕ, Continuous fun w : ℝ => ‖ramareCofactorPoly P M p w‖ ^ 2 :=
    fun p => ((continuous_ramareCofactorPoly P M p).norm).pow 2
  have hcontPair : ∀ p q : ℕ, Continuous fun w : ℝ =>
      ((moebiusPhase w p * ramareCofactorPoly P M p w)
        * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re := by
    intro p q
    refine Complex.continuous_re.comp ?_
    exact (((continuous_moebiusPhase p).mul (continuous_ramareCofactorPoly P M p)).mul
      (Complex.continuous_conj.comp
        ((continuous_moebiusPhase q).mul (continuous_ramareCofactorPoly P M q))))
  have hcongr : ∀ w ∈ Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2
      = (∑ p ∈ P, ‖ramareCofactorPoly P M p w‖ ^ 2)
        + ∑ p ∈ P, ∑ q ∈ P.erase p,
            ((moebiusPhase w p * ramareCofactorPoly P M p w)
              * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re :=
    fun w _ => normSq_ramareBilinear_eq hPprime M w
  rw [setIntegral_congr_fun measurableSet_Icc hcongr]
  have hintDiag : ∀ p ∈ P, IntegrableOn (fun w : ℝ => ‖ramareCofactorPoly P M p w‖ ^ 2)
      (Set.Icc (-W) W) volume := fun p _ => (hcontG p).integrableOn_Icc
  have hintPair : ∀ p q : ℕ, IntegrableOn (fun w : ℝ =>
      ((moebiusPhase w p * ramareCofactorPoly P M p w)
        * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re)
      (Set.Icc (-W) W) volume := fun p q => (hcontPair p q).integrableOn_Icc
  have hintRow : ∀ p ∈ P, IntegrableOn (fun w : ℝ =>
      ∑ q ∈ P.erase p, ((moebiusPhase w p * ramareCofactorPoly P M p w)
        * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re)
      (Set.Icc (-W) W) volume :=
    fun p _ => integrable_finsetSum _ fun q _ => hintPair p q
  have hintSum1 : IntegrableOn (fun w : ℝ => ∑ p ∈ P, ‖ramareCofactorPoly P M p w‖ ^ 2)
      (Set.Icc (-W) W) volume := integrable_finsetSum _ hintDiag
  have hintSum2 : IntegrableOn (fun w : ℝ => ∑ p ∈ P, ∑ q ∈ P.erase p,
      ((moebiusPhase w p * ramareCofactorPoly P M p w)
        * (starRingEnd ℂ) (moebiusPhase w q * ramareCofactorPoly P M q w)).re)
      (Set.Icc (-W) W) volume := integrable_finsetSum _ hintRow
  rw [integral_add hintSum1 hintSum2, integral_finsetSum _ hintDiag, ramarePrimeOffDiagonal,
    integral_finsetSum _ hintRow]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  exact integral_finsetSum _ fun q _ => hintPair p q

/-- **The card's residue, in one statement.**  Under the standing conditions on the designated
primes — at most `M` of them, harmonic mass `A ≥ 15e/(2ε)`, and `∑_{p ∈ P} p^{-2}` small — the
Möbius mean square is bounded by the Matomäki–Radziwiłł budget **plus the prime off-diagonal alone**.
Every other term of the decomposition has been discharged unconditionally. -/
theorem integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) {W δ ε : ℝ} (hW : 1 ≤ W) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPM : (P.card : ℝ) ≤ (M : ℝ))
    (hA : 15 * Real.exp 1 / (2 * ε) ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
    (hsq : ∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ ε * (M : ℝ))
    (hsq2 : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * (p : ℝ)) ≤ 2 * ε / (5 * Real.exp 1)) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (10 * W * (M : ℝ) + ε * (M : ℝ) ^ 2 + ramarePrimeOffDiagonal P M W)
        + 2 * (1 + 1 / δ)
            * (12 * W * (M : ℝ) + (1 + 5 * Real.exp 1 / 2) * ε * (M : ℝ) ^ 2) := by
  classical
  have hdiag : (∑ p ∈ P, ∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w‖ ^ 2)
      ≤ 10 * W * (M : ℝ) + ε * (M : ℝ) ^ 2 := by
    simp only [ramareCofactorPoly]
    exact sum_integral_normSq_ramareCofactorPoly_le_budget hPprime M hW hε hsq2
  have hbil : (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ 2)
      ≤ 10 * W * (M : ℝ) + ε * (M : ℝ) ^ 2 + ramarePrimeOffDiagonal P M W := by
    rw [integral_normSq_ramareBilinear_eq hPprime M W]
    linarith [hdiag]
  refine le_trans (integral_Icc_normSq_logPoly_moebius_le_bilinear_budget hPprime M hW hδ hε hε1
    hPM hA hsq) ?_
  have hc0 : (0 : ℝ) ≤ 1 + δ := by linarith
  exact add_le_add (mul_le_mul_of_nonneg_left hbil hc0) le_rfl

end RHTower.Sieve

end
