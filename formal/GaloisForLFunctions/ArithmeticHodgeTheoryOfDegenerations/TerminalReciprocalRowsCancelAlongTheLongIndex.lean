import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadTheNonpolarCenter
import GaloisForLFunctions.RHTower.Sieve.LipschitzBoundCalculus

/-!
# Long-index cancellation in reciprocal terminal rows

At a fixed short offset, the reciprocal kernel varies with the ratio
of that offset to the overlap. Clamping below one quarter gives a
uniform bounded Lipschitz extension. Periodic cancellation then costs
the conductor divided by the horizon, without comparing the conductor
to the overlap.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory
open _root_.RHTower.Sieve

/-- A reciprocal coordinate with a fixed lower cutoff. -/
def terminalReciprocalCoordinate (x : ℝ) : ℝ := 1 / max (1 / 4 : ℝ) x

theorem terminalReciprocalCoordinate_bounds (x : ℝ) :
    0 ≤ terminalReciprocalCoordinate x ∧ terminalReciprocalCoordinate x ≤ 4 := by
  have hx : (1 / 4 : ℝ) ≤ max (1 / 4 : ℝ) x := le_max_left _ _
  have hx0 : 0 < max (1 / 4 : ℝ) x := lt_of_lt_of_le (by norm_num) hx
  constructor
  · exact (div_pos one_pos hx0).le
  · apply (div_le_iff₀ hx0).mpr
    linarith only [hx]

theorem terminalReciprocalCoordinate_lipschitz (x y : ℝ) :
    |terminalReciprocalCoordinate x - terminalReciprocalCoordinate y| ≤ 16 * |x - y| := by
  have hx : (1 / 4 : ℝ) ≤ max (1 / 4 : ℝ) x := le_max_left _ _
  have hy : (1 / 4 : ℝ) ≤ max (1 / 4 : ℝ) y := le_max_left _ _
  have hx0 : 0 < max (1 / 4 : ℝ) x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < max (1 / 4 : ℝ) y := lt_of_lt_of_le (by norm_num) hy
  have hprod : (1 / 16 : ℝ) ≤ max (1 / 4 : ℝ) x * max (1 / 4 : ℝ) y := by
    have hh := mul_le_mul hx hy (by norm_num : (0 : ℝ) ≤ 1 / 4) hx0.le
    norm_num only at hh
    exact hh
  have hclamp : |max (1 / 4 : ℝ) y - max (1 / 4 : ℝ) x| ≤ |x - y| := by
    have hh := (LipschitzWith.id.const_max (1 / 4 : ℝ)).dist_le_mul y x
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_comm y x] using hh
  have he : terminalReciprocalCoordinate x - terminalReciprocalCoordinate y =
      (max (1 / 4 : ℝ) y - max (1 / 4 : ℝ) x) /
        (max (1 / 4 : ℝ) x * max (1 / 4 : ℝ) y) := by
    unfold terminalReciprocalCoordinate
    field_simp [hx0.ne', hy0.ne']
    <;> ring
  rw [he, abs_div, abs_of_pos (mul_pos hx0 hy0)]
  calc
    _ ≤ |x - y| / (max (1 / 4 : ℝ) x * max (1 / 4 : ℝ) y) :=
      div_le_div_of_nonneg_right hclamp (mul_pos hx0 hy0).le
    _ ≤ |x - y| / (1 / 16 : ℝ) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hprod
    _ = _ := by ring

/-- The reciprocal-offset kernel retains its offset-to-overlap ratio. -/
def terminalReciprocalWeight (F K : ℝ → ℝ) (θ x : ℝ) : ℝ :=
  F x * terminalReciprocalCoordinate x * K (θ * terminalReciprocalCoordinate x)

theorem terminalReciprocalWeight_bound
    {F K : ℝ → ℝ} {BF BK : ℝ} (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (θ x : ℝ) : |terminalReciprocalWeight F K θ x| ≤ 4 * BF * BK := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  obtain ⟨hi0, hi4⟩ := terminalReciprocalCoordinate_bounds x
  unfold terminalReciprocalWeight
  rw [abs_mul, abs_mul, abs_of_nonneg hi0]
  exact (mul_le_mul (mul_le_mul (hF x) hi4 hi0 hBF) (hK _) (abs_nonneg _)
    (mul_nonneg hBF (by norm_num))).trans_eq (by ring)

/-- The Lipschitz constant depends on `|θ|`, not on the reciprocal width itself. -/
theorem terminalReciprocalWeight_lipschitz
    {F K : ℝ → ℝ} {BF BK LF LK T θ : ℝ}
    (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hLK : 0 ≤ LK)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hKL : ∀ x y, |K x - K y| ≤ LK * |x - y|) (hθ : |θ| ≤ T)
    (x y : ℝ) :
    |terminalReciprocalWeight F K θ x - terminalReciprocalWeight F K θ y| ≤
      (64 * BF * LK * T + 16 * BF * BK + 4 * BK * LF) * |x - y| := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hT : 0 ≤ T := (abs_nonneg _).trans hθ
  have hFI : LipschitzBound (fun z => F z * terminalReciprocalCoordinate z)
      Set.univ (BF * 16 + 4 * LF) :=
    (show LipschitzBound F Set.univ LF from fun a _ b _ => hFL a b).mul
      (fun a _ b _ => terminalReciprocalCoordinate_lipschitz a b)
      (fun a _ => hF a) (fun a _ => by
        rw [abs_of_nonneg (terminalReciprocalCoordinate_bounds a).1]
        exact (terminalReciprocalCoordinate_bounds a).2)
  have hKI : LipschitzBound (fun z => K (θ * terminalReciprocalCoordinate z))
      Set.univ (LK * T * 16) := by
    intro a _ b _
    calc
      _ ≤ LK * |θ * terminalReciprocalCoordinate a - θ * terminalReciprocalCoordinate b| := hKL _ _
      _ = LK * |θ| * |terminalReciprocalCoordinate a - terminalReciprocalCoordinate b| := by
        rw [← mul_sub, abs_mul, mul_assoc]
      _ ≤ LK * T * (16 * |a - b|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hθ hLK)
          (terminalReciprocalCoordinate_lipschitz a b) (abs_nonneg _) (mul_nonneg hLK hT)
      _ = _ := by ring
  have hprod := hFI.mul hKI
    (show ∀ z ∈ (Set.univ : Set ℝ), |F z * terminalReciprocalCoordinate z| ≤ BF * 4 from by
      intro z _
      rw [abs_mul, abs_of_nonneg (terminalReciprocalCoordinate_bounds z).1]
      exact mul_le_mul (hF z) (terminalReciprocalCoordinate_bounds z).2
        (terminalReciprocalCoordinate_bounds z).1 hBF)
    (fun z _ => hK (θ * terminalReciprocalCoordinate z))
  exact (hprod x (Set.mem_univ x) y (Set.mem_univ y)).trans_eq (by ring)

/-- A reciprocal terminal row has a conductor-over-horizon bound, uniformly in its short shifts. -/
theorem abs_terminal_reciprocal_gap_row_le
    {F K : ℝ → ℝ} {BF BK LF LK T θ : ℝ}
    (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hLK : 0 ≤ LK)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hKL : ∀ x y, |K x - K y| ≤ LK * |x - y|) (hθ : |θ| ≤ T)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {J N s : ℕ} (hN : 1 ≤ N) (hJN : J ≤ N) (hs : 4 * s ≤ N) (t : ℕ) :
    |∑ n ∈ Icc 1 J, F (((n + s : ℕ) : ℝ) / N) * p (n + t) *
        K (θ * N / n) / n| ≤
      2 * q * B * (20 * BF * BK + 64 * BF * LK * T + 4 * BK * LF) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hT : 0 ≤ T := (abs_nonneg _).trans hθ
  let Fs := fun x : ℝ => F (x + s / N)
  have hFs : ∀ x, |Fs x| ≤ BF := fun x => hF _
  have hFsL : ∀ x y, |Fs x - Fs y| ≤ LF * |x - y| := by
    intro x y
    simpa only [Fs, add_sub_add_right_eq_sub] using hFL (x + s / N) (y + s / N)
  let C := 64 * BF * LK * T + 16 * BF * BK + 4 * BK * LF
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrow := abs_terminal_shifted_periodic_zero_mean_le
    (terminalReciprocalWeight_bound hFs hK θ) hC
    (terminalReciprocalWeight_lipschitz hFs hK hLF hLK hFsL hKL hθ)
    hq hp hz hB hN hJN 0 t
  simp only [Nat.add_zero] at hrow
  have heq : (∑ n ∈ Icc 1 J, terminalReciprocalWeight Fs K θ ((n : ℝ) / N) * p (n + t)) / N =
      ∑ n ∈ Icc 1 J, F (((n + s : ℕ) : ℝ) / N) * p (n + t) * K (θ * N / n) / n := by
    rw [sum_div]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1)
    have harg : ((n + s : ℕ) : ℝ) / N = (n : ℝ) / N + s / N := by
      rw [Nat.cast_add, add_div]
    by_cases hzero : F (((n + s : ℕ) : ℝ) / N) = 0
    · simp only [terminalReciprocalWeight, Fs, ← harg, hzero, zero_mul, zero_div]
    · have hsR : (s : ℝ) / N ≤ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ hN0).mpr
        have hh : (4 : ℝ) * s ≤ N := by exact_mod_cast hs
        linarith only [hh]
      have hnq : (1 / 4 : ℝ) ≤ (n : ℝ) / N := by
        by_contra h
        have hh := lt_of_not_ge h
        exact hzero (hlow _ (by rw [harg]; linarith only [hh, hsR]))
      have hi : terminalReciprocalCoordinate ((n : ℝ) / N) = (N : ℝ) / n := by
        rw [terminalReciprocalCoordinate, max_eq_right hnq]
        field_simp [hN0.ne', hn0.ne']
      simp only [terminalReciprocalWeight, Fs, hi, ← harg]
      rw [show θ * ((N : ℝ) / n) = θ * N / n by ring]
      field_simp [hN0.ne', hn0.ne']
      <;> ring
  rw [← heq, abs_div, abs_of_pos hN0]
  exact (div_le_div_of_nonneg_right hrow hN0.le).trans_eq (by dsimp only [C]; ring)

/-- Moving interval endpoints cost two periodic prefix estimates. -/
theorem abs_terminal_reciprocal_gap_interval_le
    {F K : ℝ → ℝ} {BF BK LF LK T θ : ℝ}
    (hF : ∀ x, |F x| ≤ BF) (hK : ∀ x, |K x| ≤ BK)
    (hLF : 0 ≤ LF) (hLK : 0 ≤ LK)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    (hKL : ∀ x y, |K x - K y| ≤ LK * |x - y|) (hθ : |θ| ≤ T)
    (hlow : ∀ x, x ≤ (1 / 2 : ℝ) → F x = 0)
    {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    (hz : periodicMean p q = 0) {B : ℝ} (hB : ∀ n, |p n| ≤ B)
    {a b N s : ℕ} (ha : 1 ≤ a) (hN : 1 ≤ N) (hbN : b ≤ N)
    (hs : 4 * s ≤ N) (t : ℕ) :
    |∑ n ∈ Icc a b, F (((n + s : ℕ) : ℝ) / N) * p (n + t) *
        K (θ * N / n) / n| ≤
      4 * q * B * (20 * BF * BK + 64 * BF * LK * T + 4 * BK * LF) / N := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hK 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hT : 0 ≤ T := (abs_nonneg _).trans hθ
  by_cases hab : a ≤ b
  · let row := fun n : ℕ => F (((n + s : ℕ) : ℝ) / N) * p (n + t) * K (θ * N / n) / n
    have hdis : Disjoint (Icc 1 (a - 1)) (Icc a b) := by
      apply disjoint_left.mpr
      intro n hn hm
      obtain ⟨_, hn⟩ := mem_Icc.mp hn
      obtain ⟨hm, _⟩ := mem_Icc.mp hm
      omega
    have hunion : Icc 1 (a - 1) ∪ Icc a b = Icc 1 b := by
      ext n
      simp only [mem_union, mem_Icc]
      omega
    have heq : (∑ n ∈ Icc a b, row n) =
        (∑ n ∈ Icc 1 b, row n) - ∑ n ∈ Icc 1 (a - 1), row n := by
      have hh : (∑ n ∈ Icc 1 b, row n) =
          (∑ n ∈ Icc 1 (a - 1), row n) + ∑ n ∈ Icc a b, row n := by
        rw [← hunion, sum_union hdis]
      linarith only [hh]
    have h₁ := abs_terminal_reciprocal_gap_row_le hF hK hLF hLK hFL hKL hθ hlow
      hq hp hz hB hN hbN hs t
    have h₂ := abs_terminal_reciprocal_gap_row_le hF hK hLF hLK hFL hKL hθ hlow
      hq hp hz hB hN (show a - 1 ≤ N by omega) hs t
    change |∑ n ∈ Icc a b, row n| ≤ _
    rw [heq]
    exact ((abs_sub_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), sum_empty, abs_zero]
    positivity

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminalReciprocalWeight_lipschitz
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_reciprocal_gap_row_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_reciprocal_gap_interval_le
