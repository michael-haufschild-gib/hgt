import GaloisForLFunctions.RHTower.MobiusRieszQuarticSampling
import GaloisForLFunctions.RHTower.SelbergWeightEvaluation

/-!
Square blocks have unit square-root clock mass. The one-sided variation law for
the Chebyshev remainder therefore bounds the difference between the completed
Abel moment at `N²` and the unweighted source sample at squares by `9N²`.
The existing fourth-power sampling theorem transfers RH to a one-sided bound
for these unweighted sums. No such arithmetic upper bound is assumed or proved.
-/

open scoped BigOperators
open _root_.RHTower

namespace GaloisForLFunctions.RHTower

/-- Completed Chebyshev source sampled at square arguments below `N²`. -/
noncomputable def completedChebyshevSquareSampleMoment (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ico 1 N, (psiRemainder (s ^ 2) + 2 * Real.eulerMascheroniConstant)

private theorem squareBlock_clock_mass (s : ℕ) :
    ∑ k ∈ Finset.Ico (s ^ 2) ((s + 1) ^ 2),
      (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) = 1 := by
  have hab : s ^ 2 ≤ (s + 1) ^ 2 := by gcongr; omega
  rw [Finset.sum_Ico_sub (fun k : ℕ => Real.sqrt k) hab]
  rw [Nat.cast_pow, Nat.cast_pow]
  rw [Real.sqrt_sq (Nat.cast_nonneg (s + 1)), Real.sqrt_sq (Nat.cast_nonneg s)]
  push_cast
  ring

private theorem squareBlock_moment_eq {s : ℕ} (hs : 1 ≤ s) :
    mobiusDivisorSquareRootAbelMoment ((s + 1) ^ 2) -
        mobiusDivisorSquareRootAbelMoment (s ^ 2) =
      ∑ k ∈ Finset.Ico (s ^ 2) ((s + 1) ^ 2),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
          (psiRemainder k + 2 * Real.eulerMascheroniConstant) := by
  rw [← Finset.sum_Ico_sub mobiusDivisorSquareRootAbelMoment (by nlinarith)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mobiusDivisorSquareRootAbelMoment_succ_sub (by
    have := (Finset.mem_Ico.mp hk).1
    nlinarith)]

/-- Each unit-clock block lies between its endpoint sources, up to its index width. -/
theorem mobiusDivisorSquareRootAbel_squareBlock_bounds {s : ℕ} (hs : 1 ≤ s) :
    psiRemainder (s ^ 2) + 2 * Real.eulerMascheroniConstant - (2 * s + 1 : ℝ) ≤
        mobiusDivisorSquareRootAbelMoment ((s + 1) ^ 2) -
          mobiusDivisorSquareRootAbelMoment (s ^ 2) ∧
      mobiusDivisorSquareRootAbelMoment ((s + 1) ^ 2) -
          mobiusDivisorSquareRootAbelMoment (s ^ 2) ≤
        psiRemainder ((s + 1) ^ 2) + 2 * Real.eulerMascheroniConstant + (2 * s + 1 : ℝ) := by
  rw [squareBlock_moment_eq hs]
  have hw (k : ℕ) : 0 ≤ Real.sqrt (k + 1 : ℕ) - Real.sqrt k := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ k
  constructor
  · calc
      _ = (∑ k ∈ Finset.Ico (s ^ 2) ((s + 1) ^ 2),
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) *
            (psiRemainder (s ^ 2) + 2 * Real.eulerMascheroniConstant - (2 * s + 1 : ℝ)) := by
        rw [squareBlock_clock_mass, one_mul]
      _ ≤ _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hw k)
        have hk' := Finset.mem_Ico.mp hk
        have hfall := psiRemainder_sub_ge hk'.1
        have htop : (k : ℝ) ≤ ((s : ℝ) + 1) ^ 2 := by
          exact_mod_cast hk'.2.le
        norm_cast at hfall
        push_cast at hfall
        nlinarith
  · calc
      _ ≤ (∑ k ∈ Finset.Ico (s ^ 2) ((s + 1) ^ 2),
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)) *
            (psiRemainder ((s + 1) ^ 2) + 2 * Real.eulerMascheroniConstant + (2 * s + 1 : ℝ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left _ (hw k)
        have hk' := Finset.mem_Ico.mp hk
        have hfall := psiRemainder_sub_ge hk'.2.le
        have hbot : (s : ℝ) ^ 2 ≤ k := by exact_mod_cast hk'.1
        push_cast at hfall
        nlinarith
      _ = _ := by rw [squareBlock_clock_mass, one_mul]

/-- Signed square-block quadrature retains the terminal source in the upper bound. -/
theorem mobiusDivisorSquareRootAbel_square_quadrature_bounds {N : ℕ} (hN : 1 ≤ N) :
    completedChebyshevSquareSampleMoment N - ((N : ℝ) ^ 2 - 1) ≤
        mobiusDivisorSquareRootAbelMoment (N ^ 2) ∧
      mobiusDivisorSquareRootAbelMoment (N ^ 2) ≤
        completedChebyshevSquareSampleMoment N + psiRemainder (N ^ 2) - psiRemainder 1 +
          ((N : ℝ) ^ 2 - 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hbase : mobiusDivisorSquareRootAbelMoment 1 = 0 := by
      rw [mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh (by omega)]
      simp
    simp [completedChebyshevSquareSampleMoment, hbase]
  | succ N hN ih =>
    have hb := mobiusDivisorSquareRootAbel_squareBlock_bounds hN
    have hs : completedChebyshevSquareSampleMoment (N + 1) =
        completedChebyshevSquareSampleMoment N +
          (psiRemainder (N ^ 2) + 2 * Real.eulerMascheroniConstant) := by
      exact Finset.sum_Ico_succ_top hN _
    rw [hs]
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, hb.1, hb.2]

/-- Unconditional quadratic quadrature error; the Euler--Mascheroni shift cancels. -/
theorem abs_mobiusDivisorSquareRootAbel_sub_squareSample_le {N : ℕ} (hN : 1 ≤ N) :
    |mobiusDivisorSquareRootAbelMoment (N ^ 2) - completedChebyshevSquareSampleMoment N| ≤
      9 * (N : ℝ) ^ 2 := by
  have hb := mobiusDivisorSquareRootAbel_square_quadrature_bounds hN
  have he := abs_psiRemainder_le (N ^ 2)
  have he1 : psiRemainder 1 = -1 := by norm_num [psiRemainder, chebyshevPsi]
  rw [he1] at hb
  rw [abs_le] at he ⊢
  push_cast at he
  constructor <;> nlinarith [hb.1, hb.2, he.1, he.2]

/-- Only square cutoffs of the square-sampled completed source need an eventual upper bound. -/
theorem riemannHypothesis_iff_completedChebyshevSquareSample_square_eventually_boundedAbove :
    RiemannHypothesis ↔ ∃ (B : ℝ) (N₀ : ℕ), ∀ n : ℕ, max 2 N₀ ≤ n →
      completedChebyshevSquareSampleMoment (n ^ 2) / (n ^ 4 : ℕ) ≤ B := by
  have herr (n : ℕ) (hn : 2 ≤ n) :
      |mobiusDivisorSquareRootAbelMoment (n ^ 4) -
          completedChebyshevSquareSampleMoment (n ^ 2)| ≤ 9 * (n ^ 4 : ℕ) := by
    have hsq : 1 ≤ n ^ 2 := by nlinarith
    simpa only [← pow_mul, Nat.cast_pow] using
      abs_mobiusDivisorSquareRootAbel_sub_squareSample_le hsq
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_quartic_eventually_boundedAbove]
  constructor
  · rintro ⟨B, N₀, hB⟩
    refine ⟨B + 9, N₀, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_left 2 N₀).trans hn
    have hd : (0 : ℝ) < (n ^ 4 : ℕ) := by positivity
    have he := (abs_le.mp (herr n hn2)).1
    have hb := (div_le_iff₀ hd).mp (hB n hn)
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rintro ⟨B, N₀, hB⟩
    refine ⟨B + 9, N₀, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_left 2 N₀).trans hn
    have hd : (0 : ℝ) < (n ^ 4 : ℕ) := by positivity
    have he := (abs_le.mp (herr n hn2)).2
    have hb := (div_le_iff₀ hd).mp (hB n hn)
    apply (div_le_iff₀ hd).mpr
    nlinarith

private theorem abs_completedChebyshevSquareSample_sub_remainderSum_le (N : ℕ) :
    |completedChebyshevSquareSampleMoment N -
        ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| ≤
      |2 * Real.eulerMascheroniConstant| * N := by
  have heq : completedChebyshevSquareSampleMoment N =
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) +
        (N - 1 : ℕ) * (2 * Real.eulerMascheroniConstant) := by
    simp [completedChebyshevSquareSampleMoment, Finset.sum_add_distrib]
  rw [heq, add_sub_cancel_left, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]

/-- The completed-source shift can be removed from the sparse one-sided RH criterion. -/
theorem riemannHypothesis_iff_psiRemainder_squareSample_eventually_boundedAbove :
    RiemannHypothesis ↔ ∃ (B : ℝ) (N₀ : ℕ), ∀ n : ℕ, max 2 N₀ ≤ n →
      (∑ s ∈ Finset.Ico 1 (n ^ 2), psiRemainder (s ^ 2)) / (n ^ 4 : ℕ) ≤ B := by
  have herr (n : ℕ) (hn : 2 ≤ n) :
      |completedChebyshevSquareSampleMoment (n ^ 2) -
          ∑ s ∈ Finset.Ico 1 (n ^ 2), psiRemainder (s ^ 2)| ≤
        |2 * Real.eulerMascheroniConstant| * (n ^ 4 : ℕ) := by
    have hs : (n ^ 2 : ℕ) ≤ n ^ 4 := by nlinarith [sq_nonneg (n ^ 2 - 1 : ℤ)]
    exact (abs_completedChebyshevSquareSample_sub_remainderSum_le (n ^ 2)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (abs_nonneg _))
  rw [riemannHypothesis_iff_completedChebyshevSquareSample_square_eventually_boundedAbove]
  constructor
  · rintro ⟨B, N₀, hB⟩
    refine ⟨B + |2 * Real.eulerMascheroniConstant|, N₀, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_left 2 N₀).trans hn
    have hd : (0 : ℝ) < (n ^ 4 : ℕ) := by positivity
    have he := (abs_le.mp (herr n hn2)).1
    have hb := (div_le_iff₀ hd).mp (hB n hn)
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rintro ⟨B, N₀, hB⟩
    refine ⟨B + |2 * Real.eulerMascheroniConstant|, N₀, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_left 2 N₀).trans hn
    have hd : (0 : ℝ) < (n ^ 4 : ℕ) := by positivity
    have he := (abs_le.mp (herr n hn2)).2
    have hb := (div_le_iff₀ hd).mp (hB n hn)
    apply (div_le_iff₀ hd).mpr
    nlinarith

/-- RH is equivalent to a quadratic upper bound for the unweighted sum of Chebyshev
remainders at squares. This theorem does not discharge that arithmetic bound. -/
theorem riemannHypothesis_iff_psiRemainder_squareSum_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) ≤ B * (N : ℝ) ^ 2 := by
  constructor
  · intro hRH
    obtain ⟨B, hB⟩ :=
      _root_.RHTower.riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mp hRH
    refine ⟨B + 9 + |2 * Real.eulerMascheroniConstant|, fun N hN => ?_⟩
    have hsq : 2 ≤ N ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (N ^ 2 : ℕ) := by positivity
    have hb := (div_le_iff₀ hd).mp (hB (N ^ 2) hsq)
    have hq := (abs_le.mp
      (abs_mobiusDivisorSquareRootAbel_sub_squareSample_le (by omega : 1 ≤ N))).1
    have he := (abs_le.mp
      (abs_completedChebyshevSquareSample_sub_remainderSum_le N)).1
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hg : |2 * Real.eulerMascheroniConstant| * (N : ℝ) ≤
        |2 * Real.eulerMascheroniConstant| * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith
    push_cast at hb
    nlinarith
  · rintro ⟨B, hB⟩
    apply riemannHypothesis_iff_psiRemainder_squareSample_eventually_boundedAbove.mpr
    refine ⟨B, 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := by simpa using hn
    have hsq : 2 ≤ n ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (n ^ 4 : ℕ) := by positivity
    apply (div_le_iff₀ hd).mpr
    simpa only [Nat.cast_pow, ← pow_mul] using hB (n ^ 2) hsq

end GaloisForLFunctions.RHTower
