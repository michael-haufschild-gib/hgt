import GaloisForLFunctions.RHTower.EulerDeletionFirstTailWindowEnergy
import GaloisForLFunctions.RHTower.EulerDeletionPredictableDriftFirstTail
import GaloisForLFunctions.RHTower.Sieve.ShiftReindex

/-!
# Exact pair-correlation kernel of the first Euler-deletion tail

The literal fixed-start first tail is a triangular sum of Möbius increments.
Expanding it before any estimate gives one signed two-point kernel.  The
physical reciprocal weight telescopes exactly, so this file records the
complete correlation target without an average, a positive completion, or an
absolute-value bound.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.DeletionFirstTail

private theorem sum_reciprocal_Icc (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (a : ℝ) - 1 / ((b : ℝ) + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hab' : a ≤ b
    · rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1), ih hab']
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
      have hbR : ((b : ℝ) + 1) ≠ 0 := by positivity
      have hbR' : ((b : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · have heq : a = b + 1 := by omega
      subst a
      have hsingle : Finset.Icc (b + 1) (b + 1) = {b + 1} := by
        ext n
        simp
      rw [hsingle, Finset.sum_singleton]
      have hbR : ((b : ℝ) + 1) ≠ 0 := by positivity
      have hbR' : ((b : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- Exact first-tail pair correlation.  Every off-diagonal Möbius interaction
remains signed, and the reciprocal kernel is the literal physical weight of
the common terminal prefix range. -/
theorem incrementEnergy_eq_signed_pair_kernel (N : ℕ) :
    incrementEnergy N =
      ∑ a ∈ Finset.Ioc N (2 * N), ∑ b ∈ Finset.Ioc N (2 * N),
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (1 / (max a b : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ)) := by
  let S := Finset.Ioc N (2 * N)
  let c : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  have hprefix (n : ℕ) (hn : n ∈ S) :
      (∑ m ∈ Finset.Ioc N n, c m) =
        ∑ m ∈ S, if m ≤ n then c m else 0 := by
    have hnupper : n ≤ 2 * N := (Finset.mem_Ioc.mp hn).2
    change (∑ m ∈ Finset.Ioc N n, c m) =
      ∑ m ∈ Finset.Ioc N (2 * N), if m ≤ n then c m else 0
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hexpand (n : ℕ) (hn : n ∈ S) :
      (∑ m ∈ Finset.Ioc N n, c m) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ a ∈ S, ∑ b ∈ S,
          (if max a b ≤ n then c a * c b else 0) / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [hprefix n hn, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hmax : max a b ≤ n
    · have han : a ≤ n := le_trans (le_max_left _ _) hmax
      have hbn : b ≤ n := le_trans (le_max_right _ _) hmax
      simp [hmax, han, hbn]
    · by_cases han : a ≤ n
      · have hbn : ¬ b ≤ n := by
          intro hbn
          exact hmax (max_le han hbn)
        simp [hmax, han, hbn]
      · simp [hmax, han]
  have hinner (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) :
      (∑ n ∈ S,
        (if max a b ≤ n then c a * c b else 0) / ((n : ℝ) * ((n : ℝ) + 1))) =
        c a * c b *
          (1 / (max a b : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ)) := by
    have hmaxpos : 0 < max a b := by
      have haN : N < a := (Finset.mem_Ioc.mp ha).1
      exact lt_of_le_of_lt (Nat.zero_le N) (lt_of_lt_of_le haN (le_max_left _ _))
    have hmaxle : max a b ≤ 2 * N := by
      exact max_le (Finset.mem_Ioc.mp ha).2 (Finset.mem_Ioc.mp hb).2
    rw [show (fun n =>
      (if max a b ≤ n then c a * c b else 0) / ((n : ℝ) * ((n : ℝ) + 1))) =
        fun n => if max a b ≤ n then
          (c a * c b) / ((n : ℝ) * ((n : ℝ) + 1)) else 0 by
        funext n
        split_ifs <;> ring]
    rw [← Finset.sum_filter]
    have hmaxN : N < max a b :=
      lt_of_lt_of_le (Finset.mem_Ioc.mp ha).1 (le_max_left _ _)
    have hfilter : S.filter (fun n => max a b ≤ n) = Finset.Icc (max a b) (2 * N) := by
      ext n
      simp only [Finset.mem_filter, S, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hfilter]
    calc
      (∑ n ∈ Finset.Icc (max a b) (2 * N),
        c a * c b / ((n : ℝ) * ((n : ℝ) + 1))) =
          ∑ n ∈ Finset.Icc (max a b) (2 * N),
            c a * c b * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = c a * c b *
          (∑ n ∈ Finset.Icc (max a b) (2 * N),
            1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          rw [Finset.mul_sum]
      _ = _ := by
        rw [sum_reciprocal_Icc (max a b) (2 * N) hmaxpos hmaxle]
        push_cast
        ring
  unfold incrementEnergy
  change (∑ n ∈ S, (Sieve.mertensM n - Sieve.mertensM N) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1)) ) = _
  have hinc (n : ℕ) (hn : n ∈ S) :
      Sieve.mertensM n - Sieve.mertensM N = ∑ m ∈ Finset.Ioc N n, c m := by
    have hNn : N < n := (Finset.mem_Ioc.mp hn).1
    rw [Sieve.mertensM, Sieve.mertensM]
    rw [show Finset.Ioc N n = Finset.Ico (N + 1) (n + 1) by ext m; simp]
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
  calc
    (∑ n ∈ S, (Sieve.mertensM n - Sieve.mertensM N) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) =
        ∑ n ∈ S, ∑ a ∈ S, ∑ b ∈ S,
          (if max a b ≤ n then c a * c b else 0) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hinc n hn, hexpand n hn]
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ n ∈ S,
          (if max a b ≤ n then c a * c b else 0) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simpa only [S, c] using hinner a b ha hb

private theorem sum_symmetric_pair_eq_diagonal_add_two_mul_strictOffDiagonal
    (S : Finset ℕ) (f : ℕ × ℕ → ℝ)
    (hsymm : ∀ a ∈ S, ∀ b ∈ S, f (a, b) = f (b, a)) :
    (∑ a ∈ S, ∑ b ∈ S, f (a, b)) =
      (∑ ab ∈ (S.product S).filter (fun ab => ab.1 = ab.2), f ab) +
        2 * ∑ ab ∈ (S.product S).filter (fun ab => ab.2 < ab.1), f ab := by
  rw [← Finset.sum_product]
  let A := S.product S
  have hfirst := Finset.sum_filter_add_sum_filter_not A (fun ab => ab.2 < ab.1) f
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (A.filter fun ab => ¬ ab.2 < ab.1) (fun ab => ab.1 = ab.2) f
  have hEq :
      (A.filter fun ab => ¬ ab.2 < ab.1).filter (fun ab => ab.1 = ab.2) =
        A.filter (fun ab => ab.1 = ab.2) := by
    ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, _⟩, heq⟩
      exact ⟨hA, heq⟩
    · rintro ⟨hA, heq⟩
      exact ⟨⟨hA, by omega⟩, heq⟩
  have hLt :
      (A.filter fun ab => ¬ ab.2 < ab.1).filter (fun ab => ¬ ab.1 = ab.2) =
        A.filter (fun ab => ab.1 < ab.2) := by
    ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, hnotLt⟩, hne⟩
      exact ⟨hA, by omega⟩
    · rintro ⟨hA, hlt⟩
      exact ⟨⟨hA, by omega⟩, by omega⟩
  rw [hEq, hLt] at hsecond
  have hpartition :
      ∑ ab ∈ A, f ab =
        (∑ ab ∈ A.filter (fun ab => ab.2 < ab.1), f ab) +
        (∑ ab ∈ A.filter (fun ab => ab.1 = ab.2), f ab) +
        (∑ ab ∈ A.filter (fun ab => ab.1 < ab.2), f ab) := by
    rw [← hfirst, ← hsecond]
    ring
  have hswap :
      (∑ ab ∈ A.filter (fun ab => ab.1 < ab.2), f ab) =
        ∑ ab ∈ A.filter (fun ab => ab.2 < ab.1), f ab := by
    apply Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
    · rintro ⟨a, b⟩
      simp [A, and_comm]
    · rintro ⟨a, b⟩ hab
      have hab' : (a ∈ S ∧ b ∈ S) ∧ a < b := by
        simpa [A] using hab
      exact hsymm a hab'.1.1 b hab'.1.2
  change (∑ ab ∈ A, f ab) =
    (∑ ab ∈ A.filter (fun ab => ab.1 = ab.2), f ab) +
      2 * ∑ ab ∈ A.filter (fun ab => ab.2 < ab.1), f ab
  rw [hpartition, hswap]
  ring

/-- Diagonal contribution to the literal first-tail pair kernel. -/
def diagonalPairKernel (N : ℕ) : ℝ :=
  ∑ ab ∈ (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N)) |>.filter
      (fun ab => ab.1 = ab.2),
    ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ) *
      (1 / (max ab.1 ab.2 : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ))

/-- The literal pair-kernel diagonal is nonnegative.  Thus any small physical
energy must come from the unchanged strict signed off-diagonal term. -/
theorem diagonalPairKernel_nonneg (N : ℕ) : 0 ≤ diagonalPairKernel N := by
  unfold diagonalPairKernel
  apply Finset.sum_nonneg
  rintro ⟨a, b⟩ hab
  rcases Finset.mem_filter.mp hab with ⟨hprod, heq⟩
  rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
  have habEq : a = b := by simpa using heq
  subst b
  have ha' : a ∈ Finset.Ioc N (2 * N) := by simpa using ha
  have haUpper : a ≤ 2 * N := (Finset.mem_Ioc.mp ha').2
  have ha0 : 0 < (a : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp ha).1)
  have haupper : (a : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show a ≤ 2 * N + 1 by omega)
  have hweight : 0 ≤ 1 / (a : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ) := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le ha0 haupper
  simpa only [max_self] using
    mul_nonneg (mul_self_nonneg (((ArithmeticFunction.moebius a : ℤ) : ℝ))) hweight

/-- One strictly ordered half of the literal signed first-tail pair kernel. -/
def strictOffDiagonalPairKernel (N : ℕ) : ℝ :=
  ∑ ab ∈ (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N)) |>.filter
      (fun ab => ab.2 < ab.1),
    ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ) *
      (1 / (max ab.1 ab.2 : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ))

/-- The literal first-tail energy is its diagonal plus twice the strict signed
off-diagonal correlation. -/
theorem incrementEnergy_eq_diagonal_add_two_mul_strictOffDiagonal (N : ℕ) :
    incrementEnergy N =
      diagonalPairKernel N + 2 * strictOffDiagonalPairKernel N := by
  rw [incrementEnergy_eq_signed_pair_kernel]
  let S := Finset.Ioc N (2 * N)
  let f : ℕ × ℕ → ℝ := fun ab =>
    ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ) *
      (1 / (max ab.1 ab.2 : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ))
  change (∑ a ∈ S, ∑ b ∈ S, f (a, b)) =
    (∑ ab ∈ (S.product S).filter (fun ab => ab.1 = ab.2), f ab) +
      2 * ∑ ab ∈ (S.product S).filter (fun ab => ab.2 < ab.1), f ab
  apply sum_symmetric_pair_eq_diagonal_add_two_mul_strictOffDiagonal
  intro a ha b hb
  dsimp [f]
  rw [max_comm (b : ℝ) (a : ℝ)]
  ring

/-- Literal fixed-start first-tail off-diagonal as all signed shifted correlations.

For shift `h`, the inner interval remains exactly `N < a ≤ 2N-h`; no endpoint
is completed and no signs are changed. -/
def shiftedOffDiagonalPairKernel (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ico 1 N, ∑ a ∈ Finset.Ioc N (2 * N - h),
    ((ArithmeticFunction.moebius (a + h) : ℤ) : ℝ) * ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
      (1 / ((a + h : ℕ) : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ))

/-- The strict half of the physical pair kernel is precisely its full literal
family of shifted signed correlations. -/
theorem strictOffDiagonalPairKernel_eq_shiftedOffDiagonalPairKernel (N : ℕ) :
    strictOffDiagonalPairKernel N = shiftedOffDiagonalPairKernel N := by
  unfold strictOffDiagonalPairKernel shiftedOffDiagonalPairKernel
  rw [show
    (∑ ab ∈ (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N)) |>.filter
        (fun ab => ab.2 < ab.1),
      ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ) *
        (1 / (max ab.1 ab.2 : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ))) =
    ∑ ab ∈ (Finset.Ioc N (2 * N)).product (Finset.Ioc N (2 * N)) |>.filter
        (fun ab => ab.2 < ab.1),
      ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius ab.2 : ℤ) : ℝ) *
        (1 / (ab.1 : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ)) by
      apply Finset.sum_congr rfl
      rintro ⟨u, a⟩ hmem
      have hlt : a < u := (Finset.mem_filter.mp hmem).2
      have hle : (a : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.le_of_lt hlt
      rw [max_eq_left hle]]
  exact Sieve.sum_strict_ioc_eq_sum_shift N (fun u a =>
    ((ArithmeticFunction.moebius u : ℤ) : ℝ) * ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
      (1 / (u : ℝ) - 1 / ((2 * N + 1 : ℕ) : ℝ)))

/-- The literal strict shifted kernel is already controlled by the full EDQ
predictable drift.  Hence a cofinal EDQ ceiling must establish its one-sided
signed cancellation without changing any endpoint or source. -/
theorem strictOffDiagonalPairKernel_le_twelve_drift_sq_add_thirty (N : ℕ) :
    strictOffDiagonalPairKernel N ≤
      12 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 + 30 := by
  have hsplit := incrementEnergy_eq_diagonal_add_two_mul_strictOffDiagonal N
  have hdiag := diagonalPairKernel_nonneg N
  have henergy :=
    DeletionPredictableFirstTail.incrementEnergy_le_twentyfour_drift_sq_add_sixty N
  nlinarith

end RHTower.DeletionFirstTail
