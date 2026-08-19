import GaloisForLFunctions.RHTower.Sieve.RamareLadderAffine
import GaloisForLFunctions.RHTower.Sieve.NonRoughBilinearExact
import GaloisForLFunctions.RHTower.Sieve.LadderAffineMajorant
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# The Ramaré bilinear form against the window kernel

The bilinear form is itself a Dirichlet polynomial: `Sieve/NonRoughBilinearExact` identifies it with
the polynomial of the non-rough Möbius coefficient, exactly, with no diagonal and no rough term.  So
Gallagher's dyadic-tail machinery — which is stated for an arbitrary coefficient sequence — applies
to it verbatim once the ladder supplies the affine majorant of its mean square.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The non-rough Möbius coefficient as a complex sequence. -/
def nonRoughCoeff (P : Finset ℕ) (n : ℕ) : ℂ := ((nonRoughMoebius P n : ℝ) : ℂ)

theorem norm_nonRoughCoeff_le_one (P : Finset ℕ) (n : ℕ) : ‖nonRoughCoeff P n‖ ≤ 1 := by
  rw [nonRoughCoeff, Complex.norm_real, Real.norm_eq_abs]
  exact abs_nonRoughMoebius_le_one P n

/-- **The bilinear form is the non-rough Möbius polynomial.** -/
theorem logPoly_nonRoughCoeff_eq_ramareBilinear {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    (M : ℕ) (w : ℝ) :
    logPoly (nonRoughCoeff P) (Finset.Icc 1 M) w = ramareBilinear P M w := by
  rw [ramareBilinear]
  exact logPoly_nonRoughMoebius_eq_ramare_bilinear hPprime (Finset.Icc 1 M) w

/-- The energy of the non-rough coefficient over an initial block. -/
theorem sum_normSq_nonRoughCoeff_le (P : Finset ℕ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, ‖nonRoughCoeff P n‖ ^ 2) ≤ (M : ℝ) := by
  classical
  have hle : ∑ n ∈ Finset.Icc 1 M, ‖nonRoughCoeff P n‖ ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 M, (1 : ℝ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have h := norm_nonRoughCoeff_le_one P n
    nlinarith [norm_nonneg (nonRoughCoeff P n)]
  refine hle.trans (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Icc]
  simp

/-- **The kernel-weighted bilinear mean square, with both Gallagher regimes paid by the ladder.** -/
theorem integral_kernel_normSq_ramareBilinear_le {P : Finset ℕ} {M : ℕ} {δ G T₀ αL βL β₀ : ℝ}
    (hPprime : ∀ q ∈ P, q.Prime) (hδ : 0 < δ) (hG : 1 ≤ G) (hGT₀ : G ≤ T₀)
    (hαL : 0 ≤ αL) (hβL : 0 ≤ βL)
    (hhead : (∫ w in Set.Icc (-G) G, ‖ramareBilinear P M w‖ ^ 2) ≤ β₀)
    (hmid : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖ramareBilinear P M w‖ ^ 2) ≤ αL * T + βL) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2 * ‖ramareBilinear P M w‖ ^ 2)
      ≤ 2 * δ ^ 2 * β₀
        + (4 * (αL + 5 * Real.pi / 2 * (M : ℝ) + 5 * Real.exp 1 / 2 * (M : ℝ) * (M : ℝ) / T₀)
            / (Real.pi ^ 2 * G)
          + 4 * βL / (3 * Real.pi ^ 2 * G ^ 2)) := by
  classical
  set S : Finset ℕ := Finset.Icc 1 M with hS
  set a : ℕ → ℂ := nonRoughCoeff P with ha
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ M := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hconv : ∀ w : ℝ, logPoly a S w = ramareBilinear P M w := fun w =>
    logPoly_nonRoughCoeff_eq_ramareBilinear hPprime M w
  have hhead' : (∫ w in Set.Icc (-G) G, ‖logPoly a S w‖ ^ 2) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hhead
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hconv]
  have hmid' : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖logPoly a S w‖ ^ 2) ≤ αL * T + βL := by
    intro T h1 h2
    refine le_trans (le_of_eq ?_) (hmid T h1 h2)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hconv]
  have haff := affineMajorant_two_regime (a := a) hs0 hsM hG hGT₀ hαL hβL hmid'
  have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
  have hgal := gallagher_split_integral_dyadic_head a S hδ hG0 hhead' haff
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  have hkern : (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2 * ‖ramareBilinear P M w‖ ^ 2)
      = ∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a S w‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [hconv]
  rw [hkern]
  refine hgal.trans ?_
  -- the energy of the non-rough coefficient is at most the length of the block
  have hE := sum_normSq_nonRoughCoeff_le P M
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ S, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => by positivity
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (le_trans hG hGT₀)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  gcongr

end

end RHTower.Sieve
