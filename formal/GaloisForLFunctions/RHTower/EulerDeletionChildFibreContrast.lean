import GaloisForLFunctions.RHTower.EulerDeletionNonclockLcmTailBridge
import GaloisForLFunctions.RHTower.EulerDeletionPhysicalCellMoebiusIdentity

/-!
# EDQ physical child contrasts

The parent beta resolvent cancels exactly between two genuine child coordinates.
What remains is the contrast of the two physical source--cofactor blocks and
their two local innovations.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

/-- The complete signed source--cofactor scalar in one physical selected child block. -/
def childSourceCofactorBlock (N l u b : ℕ) (x : ℝ) : ℝ :=
  (x ^ (u + b * clock l) *
    ((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
      x ^ clock (l + 1) * (1 - x ^ clock (l + 1)) *
        ∑ m ∈ futureResidualCarrier N (l + 1),
          ∑ r ∈ futureOldCofactorCarrier N (l + 1) m,
            clockResidualBetaWeight (l + 1) (u + b * clock l + 1)
              (canonicalClockRatio N (l + 1) - 1) x (m * r)) *
    (1 - x ^ clock N)⁻¹) /
  (∑ a ∈ range (clock (l + 1)), x ^ a)

/-- A canonical selected-child block is precisely its one signed source--cofactor scalar. -/
theorem canonicalRefinementBlockKernel_eq_childSourceCofactorBlock
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hx : 0 ≤ x) :
    canonicalRefinementBlockKernel N l u b x = childSourceCofactorBlock N l u b x := by
  simpa only [childSourceCofactorBlock] using
    canonicalRefinementBlockKernel_eq_source_futureCofactor N l u b x hlN hx

/-- Neighboring selected-child kernels satisfy an exact lower-clock forward-difference law. -/
theorem canonicalRefinementBlockKernel_child_forward_difference
    (N l u b : ℕ) (x : ℝ) :
    canonicalRefinementBlockKernel N l u (b + 1) x -
      x ^ clock l * canonicalRefinementBlockKernel N l u b x =
      (1 - x) * x ^ (u + (b + 1) * clock l) *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ (a * clock (l + 1)) *
            (pairedMoebiusSource N (u + (b + 1) * clock l + a * clock (l + 1)) -
              pairedMoebiusSource N (u + b * clock l + a * clock (l + 1)))) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
  rw [canonicalRefinementBlockKernel_eq_canonical_finite_kernel,
    canonicalRefinementBlockKernel_eq_canonical_finite_kernel]
  have hpow : x ^ clock l * x ^ (u + b * clock l) =
      x ^ (u + (b + 1) * clock l) := by
    rw [← pow_add]
    congr 1
    rw [Nat.succ_mul]
    omega
  have hfactor (z : ℝ) :
      x ^ clock l * ((1 - x) * x ^ (u + b * clock l) * z) =
        (1 - x) * x ^ (u + (b + 1) * clock l) * z := by
    calc
      x ^ clock l * ((1 - x) * x ^ (u + b * clock l) * z) =
          (1 - x) * (x ^ clock l * x ^ (u + b * clock l)) * z := by ring
      _ = _ := by rw [hpow]
  rw [hfactor, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The neighboring-child forward difference is one complete signed physical
truncated-divisor window at the lower history clock. -/
theorem canonicalRefinementBlockKernel_child_forward_difference_eq_truncated_divisor_window
    (N l u b : ℕ) (x : ℝ) :
    canonicalRefinementBlockKernel N l u (b + 1) x -
      x ^ clock l * canonicalRefinementBlockKernel N l u b x =
      (1 - x) * x ^ (u + (b + 1) * clock l) *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ (a * clock (l + 1)) *
            ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
              ∑ k ∈ Ioc (u + b * clock l + a * clock (l + 1) + 1)
                (u + b * clock l + a * clock (l + 1) + clock l + 1),
                truncMoebiusDivisorSum N k)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
  rw [canonicalRefinementBlockKernel_child_forward_difference]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have harg :
      u + b * clock l + a * clock (l + 1) + clock l =
        u + (b + 1) * clock l + a * clock (l + 1) := by
    rw [Nat.succ_mul]
    omega
  rw [← harg, pairedMoebiusSource_increment_eq_truncated_divisor_window]

/-- The explicit source--future-cofactor block has the same lower-clock signed
truncated-divisor forward difference. -/
theorem childSourceCofactorBlock_forward_difference_eq_truncated_divisor_window
    (N l u b : ℕ) (x : ℝ) (hlN : l < N) (hx : 0 ≤ x) :
    childSourceCofactorBlock N l u (b + 1) x -
      x ^ clock l * childSourceCofactorBlock N l u b x =
      (1 - x) * x ^ (u + (b + 1) * clock l) *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ (a * clock (l + 1)) *
            ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
              ∑ k ∈ Ioc (u + b * clock l + a * clock (l + 1) + 1)
                (u + b * clock l + a * clock (l + 1) + clock l + 1),
                truncMoebiusDivisorSum N k)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
  rw [← canonicalRefinementBlockKernel_eq_childSourceCofactorBlock N l u (b + 1) x hlN hx,
    ← canonicalRefinementBlockKernel_eq_childSourceCofactorBlock N l u b x hlN hx,
    canonicalRefinementBlockKernel_child_forward_difference_eq_truncated_divisor_window]

private theorem finite_twisted_forward_recurrence (f : ℕ → ℝ) (y : ℝ) (K : ℕ) :
    f K = y ^ K * f 0 +
      ∑ s ∈ range K, y ^ (K - 1 - s) * (f (s + 1) - y * f s) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have hsum :
        (∑ s ∈ range K, y ^ (K - s) * (f (s + 1) - y * f s)) =
          y * ∑ s ∈ range K, y ^ (K - 1 - s) * (f (s + 1) - y * f s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hsK : s < K := mem_range.mp hs
      have hexp : K - s = (K - 1 - s) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hsum]
    have hpart :
        y * ∑ s ∈ range K, y ^ (K - 1 - s) * (f (s + 1) - y * f s) =
          y * (f K - y ^ K * f 0) := by
      rw [ih]
      ring
    rw [hpart, pow_succ]
    ring

/-- A selected source--future-cofactor block is exactly its initial block plus a finite
geometrically weighted Abel sum of complete signed lower-clock truncated-divisor windows. -/
theorem childSourceCofactorBlock_child_unroll
    (N l u K : ℕ) (x : ℝ) (hlN : l < N) (hx : 0 ≤ x) :
    childSourceCofactorBlock N l u K x =
      (x ^ clock l) ^ K * childSourceCofactorBlock N l u 0 x +
        ∑ s ∈ range K, (x ^ clock l) ^ (K - 1 - s) *
          ((1 - x) * x ^ (u + (s + 1) * clock l) *
            ∑ a : Fin (canonicalClockRatio N (l + 1)),
              (x ^ (a * clock (l + 1)) *
                ((clock l : ℝ) * (∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
                  ∑ k ∈ Ioc (u + s * clock l + a * clock (l + 1) + 1)
                    (u + s * clock l + a * clock (l + 1) + clock l + 1),
                    truncMoebiusDivisorSum N k)) *
                (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) := by
  rw [finite_twisted_forward_recurrence
    (fun b => childSourceCofactorBlock N l u b x) (x ^ clock l) K]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [childSourceCofactorBlock_forward_difference_eq_truncated_divisor_window
    N l u s x hlN hx]

/-- The terminal selected source--future-cofactor block vanishes exactly. -/
theorem terminal_childSourceCofactorBlock_eq_zero (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    childSourceCofactorBlock (n + 1) n (clock n - 1)
      (clock (n + 1) / clock n - 1) x = 0 := by
  rw [← canonicalRefinementBlockKernel_eq_childSourceCofactorBlock
    (n + 1) n (clock n - 1) (clock (n + 1) / clock n - 1) x
    (Nat.lt_succ_self n) hx,
    terminalRefinementBlockKernel_eq_zero]

/-- The terminal zero converts the last physical child block into an exact signed Abel
cancellation between its initial source--cofactor block and all intermediate lower-clock windows. -/
theorem terminal_childSourceCofactorBlock_abel_eq_zero (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ clock n) ^ (clock (n + 1) / clock n - 1) *
        childSourceCofactorBlock (n + 1) n (clock n - 1) 0 x +
      ∑ s ∈ range (clock (n + 1) / clock n - 1),
        (x ^ clock n) ^ (clock (n + 1) / clock n - 1 - 1 - s) *
          ((1 - x) * x ^ (clock n - 1 + (s + 1) * clock n) *
            ∑ a : Fin (canonicalClockRatio (n + 1) (n + 1)),
              (x ^ (a * clock (n + 1)) *
                ((clock n : ℝ) *
                    (∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
                  ∑ k ∈ Ioc (clock n - 1 + s * clock n + a * clock (n + 1) + 1)
                    (clock n - 1 + s * clock n + a * clock (n + 1) + clock n + 1),
                    truncMoebiusDivisorSum (n + 1) k)) *
                (1 - x ^ (canonicalClockRatio (n + 1) (n + 1) * clock (n + 1)))⁻¹) = 0 := by
  rw [← childSourceCofactorBlock_child_unroll
    (n + 1) n (clock n - 1) (clock (n + 1) / clock n - 1) x
    (Nat.lt_succ_self n) hx]
  exact terminal_childSourceCofactorBlock_eq_zero n x hx

/-- The signed innovation in the `s`-th terminal physical child window of length `clock n`. -/
def terminalChildWindowDeviation (n s : ℕ) : ℝ :=
  (clock n : ℝ) * ∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ) -
    ∑ k ∈ Ioc (clock n + s * clock n) (clock n + (s + 1) * clock n),
      truncMoebiusDivisorSum (n + 1) k

/-- A terminal child-window deviation is the exact increment of the literal physical Möbius
source between its two clock-aligned endpoints.  This transfers the remaining signed tail to the
existing physical source-energy carrier without an estimate. -/
theorem terminalChildWindowDeviation_eq_physicalCell_increment (n s : ℕ) :
    terminalChildWindowDeviation n s =
      DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
        (clock n + (s + 1) * clock n) -
      DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
        (clock n + s * clock n) := by
  let A := clock n
  let a := A + s * A
  let b := A + (s + 1) * A
  have hab : a ≤ b := by
    dsimp [a, b]
    rw [Nat.succ_mul]
    omega
  have hsplit := Finset.sum_Ioc_consecutive
    (fun j : ℕ => truncMoebiusDivisorSum (n + 1) j) (Nat.zero_le a) hab
  have hprefix :
      (∑ j ∈ Icc 1 a, truncMoebiusDivisorSum (n + 1) j) +
        ∑ j ∈ Ioc a b, truncMoebiusDivisorSum (n + 1) j =
      ∑ j ∈ Icc 1 b, truncMoebiusDivisorSum (n + 1) j := by
    simpa only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add] using hsplit
  have hwindow :
      (∑ j ∈ Ioc a b, truncMoebiusDivisorSum (n + 1) j) =
        (∑ j ∈ Icc 1 b, truncMoebiusDivisorSum (n + 1) j) -
          ∑ j ∈ Icc 1 a, truncMoebiusDivisorSum (n + 1) j := by
    linarith
  rw [RHTower.physical_moebius_cell_eq_truncated_divisor_tail,
    RHTower.physical_moebius_cell_eq_truncated_divisor_tail]
  change (A : ℝ) * (∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ)) -
      ∑ j ∈ Ioc a b, truncMoebiusDivisorSum (n + 1) j = _
  rw [hwindow]
  dsimp [a, b, A]
  push_cast
  ring

/-- The complete tail carried by one terminal child block telescopes to one literal physical
source cell.  Its far clock endpoint vanishes because every divisor in the cutoff divides that
clock.  Thus no multi-window estimate remains inside a terminal child tail. -/
theorem terminalChildWindowDeviation_tail_eq_neg_physicalCell
    (n b : ℕ) (hb : b < clock (n + 1) / clock n) :
    (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
      terminalChildWindowDeviation n (b + s)) =
      -DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
        (clock n * (b + 1)) := by
  let q := clock (n + 1) / clock n
  let A := clock n
  let K := q - 1 - b
  let F : ℕ → ℝ := fun s =>
    DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
      (A + (b + s) * A)
  have htel : ∀ T : ℕ, (∑ s ∈ range T, (F (s + 1) - F s)) = F T - F 0 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, ih]
      ring
  have hdeviation (s : ℕ) : terminalChildWindowDeviation n (b + s) = F (s + 1) - F s := by
    unfold F
    simpa [A, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      terminalChildWindowDeviation_eq_physicalCell_increment n (b + s)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (Nat.le_of_dvd (clock_pos (n + 1)) (clock_dvd (Nat.le_succ n)))
      (clock_pos n)
  have hbK : b + K = q - 1 := by
    dsimp [K]
    omega
  have hspan : q * A = clock (n + 1) := by
    dsimp [q, A]
    exact Nat.div_mul_cancel (clock_dvd (Nat.le_succ n))
  have hendpoint : A + (b + K) * A = clock (n + 1) := by
    rw [hbK]
    have : A + (q - 1) * A = q * A := by
      calc
        A + (q - 1) * A = (1 + (q - 1)) * A := by rw [Nat.add_mul, one_mul]
        _ = q * A := by congr 1; omega
    rw [this, hspan]
  have hcellclock :
      DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
        (clock (n + 1)) = 0 := by
    unfold DeletionCoefficientTransfer.cell
    apply Finset.sum_eq_zero
    intro i hi
    have hidvd : i + 1 ∣ clock (n + 1) :=
      dvd_clock (Nat.succ_pos i) (Nat.succ_le_of_lt (mem_range.mp hi))
    simp [Nat.mod_eq_zero_of_dvd hidvd]
  change (∑ s ∈ range K, terminalChildWindowDeviation n (b + s)) = _
  rw [Finset.sum_congr rfl (fun s _ => hdeviation s), htel]
  unfold F
  rw [hendpoint, hcellclock]
  dsimp [A]
  rw [zero_sub]
  congr 1
  rw [Nat.mul_succ]
  ac_rfl

/-- The terminal physical child innovations have exact signed zero total over the complete
child cycle.  This identifies the cancellation carrier that remains after Euler deletion. -/
theorem terminalChildWindowDeviation_sum_eq_zero
    (n : ℕ) (hn : 0 < n) :
    ∑ s ∈ range (clock (n + 1) / clock n), terminalChildWindowDeviation n s = 0 := by
  have hzero := selectedRefinementBlock_truncatedDivisorDeviation_sum_eq_zero
    (n + 1) (n - 1) (clock n - 1) 0 (by omega)
  have hratio : canonicalClockRatio (n + 1) n = clock (n + 1) / clock n :=
    canonicalClockRatio_eq_div_of_le (n + 1) n (Nat.le_succ n)
  have hbase : clock n - 1 + 1 = clock n :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr (clock_pos n))
  have hnbase : n - 1 + 1 = n := by omega
  dsimp at hzero
  simp only [hnbase, zero_mul, Nat.add_zero] at hzero
  rw [hratio, hbase] at hzero
  simpa [terminalChildWindowDeviation] using hzero

/-- At a terminal refinement, the exact source--cofactor block at the initial child is the
last physical lower-clock signed divisor-window innovation.  The terminal zero and the
complete-cycle cancellation eliminate every intervening innovation without an estimate. -/
theorem terminal_childSourceCofactorBlock_initial_eq_final_innovation
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ clock n) ^ (clock (n + 1) / clock n - 1) *
        childSourceCofactorBlock (n + 1) n (clock n - 1) 0 x =
      (1 - x) * x ^ (clock (n + 1) - 1) *
        terminalChildWindowDeviation n (clock (n + 1) / clock n - 1) *
          (1 - x ^ clock (n + 1))⁻¹ := by
  let q := clock (n + 1) / clock n
  let A := clock n
  let C := clock (n + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (Nat.le_of_dvd (clock_pos (n + 1)) (clock_dvd (Nat.le_succ n)))
      (clock_pos n)
  have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqpos)
  have hspan : q * A = C := by
    dsimp [q, A, C]
    exact Nat.div_mul_cancel (clock_dvd (Nat.le_succ n))
  have hratio : canonicalClockRatio (n + 1) (n + 1) = 1 := by
    rw [canonicalClockRatio_eq_div_of_le (n + 1) (n + 1) le_rfl]
    exact Nat.div_self (clock_pos (n + 1))
  have hzero := terminalChildWindowDeviation_sum_eq_zero n hn
  change ∑ s ∈ range q, terminalChildWindowDeviation n s = 0 at hzero
  rw [← hqeq, Finset.sum_range_succ] at hzero
  have hprefix : ∑ s ∈ range (q - 1), terminalChildWindowDeviation n s =
      - terminalChildWindowDeviation n (q - 1) := by
    linarith
  have hterminal := terminal_childSourceCofactorBlock_abel_eq_zero n x hx
  rw [hratio] at hterminal
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.zero_mul, pow_zero, one_mul] at hterminal
  simp only [Nat.add_zero] at hterminal
  have hraw (s : ℕ) :
      (clock n : ℝ) * ∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ) -
          ∑ k ∈ Ioc (clock n - 1 + s * clock n + 1)
            (clock n - 1 + s * clock n + clock n + 1),
            truncMoebiusDivisorSum (n + 1) k = terminalChildWindowDeviation n s := by
    unfold terminalChildWindowDeviation
    have hclockpos : 0 < clock n := clock_pos n
    have hstart : clock n - 1 + s * clock n + 1 = clock n + s * clock n := by omega
    have hend : clock n - 1 + s * clock n + clock n + 1 =
        clock n + (s + 1) * clock n := by
      rw [Nat.succ_mul]
      omega
    rw [hstart, hend]
  simp_rw [hraw] at hterminal
  have hsummand (s : ℕ) (hs : s ∈ range (q - 1)) :
      (x ^ A) ^ (q - 1 - 1 - s) *
          ((1 - x) * x ^ (A - 1 + (s + 1) * A) *
            (terminalChildWindowDeviation n s * (1 - x ^ C)⁻¹)) =
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n s *
          (1 - x ^ C)⁻¹ := by
    have hsq : s < q - 1 := mem_range.mp hs
    have hqle : s + 2 ≤ q := by omega
    have hsub : q - 1 - 1 - s = q - (s + 2) := by omega
    have hmul : (s + 2) * A = A + (s + 1) * A := by ring
    have hle : (s + 2) * A ≤ q * A := Nat.mul_le_mul_right A hqle
    have hexp : A * (q - 1 - 1 - s) + (A - 1 + (s + 1) * A) = C - 1 := by
      calc
        A * (q - 1 - 1 - s) + (A - 1 + (s + 1) * A) =
            (q - (s + 2)) * A + (A - 1 + (s + 1) * A) := by
              rw [hsub, Nat.mul_comm]
        _ = (q * A - (s + 2) * A) + (A - 1 + (s + 1) * A) := by rw [Nat.sub_mul]
        _ = q * A - 1 := by
          rw [hmul] at hle
          have hcancel := Nat.sub_add_cancel hle
          have hP : A - 1 + (s + 1) * A + 1 = A + (s + 1) * A := by
            have hApos : 0 < A := by dsimp [A]; exact clock_pos n
            omega
          omega
        _ = C - 1 := by rw [hspan]
    have hpow :
        (x ^ A) ^ (q - 1 - 1 - s) * x ^ (A - 1 + (s + 1) * A) = x ^ (C - 1) := by
      rw [← pow_mul, ← pow_add, hexp]
    calc
      (x ^ A) ^ (q - 1 - 1 - s) *
          ((1 - x) * x ^ (A - 1 + (s + 1) * A) *
            (terminalChildWindowDeviation n s * (1 - x ^ C)⁻¹)) =
          (1 - x) *
            ((x ^ A) ^ (q - 1 - 1 - s) * x ^ (A - 1 + (s + 1) * A)) *
            terminalChildWindowDeviation n s * (1 - x ^ C)⁻¹ := by ring
      _ = _ := by rw [hpow]
  have hsum :
      (∑ s ∈ range (q - 1),
        (x ^ A) ^ (q - 1 - 1 - s) *
          ((1 - x) * x ^ (A - 1 + (s + 1) * A) *
            (terminalChildWindowDeviation n s * (1 - x ^ C)⁻¹))) =
        ∑ s ∈ range (q - 1),
          (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n s *
            (1 - x ^ C)⁻¹ := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hsummand s hs
  have hterminal' :
      (x ^ A) ^ (q - 1) * childSourceCofactorBlock (n + 1) n (A - 1) 0 x +
        ∑ s ∈ range (q - 1),
          (x ^ A) ^ (q - 1 - 1 - s) *
            ((1 - x) * x ^ (A - 1 + (s + 1) * A) *
              (terminalChildWindowDeviation n s * (1 - x ^ C)⁻¹)) = 0 := by
    simpa [q, A, C] using hterminal
  rw [hsum] at hterminal'
  have hfactor :
      (∑ s ∈ range (q - 1),
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n s *
          (1 - x ^ C)⁻¹) =
        (1 - x) * x ^ (C - 1) *
          (∑ s ∈ range (q - 1), terminalChildWindowDeviation n s) *
            (1 - x ^ C)⁻¹ := by
    calc
      (∑ s ∈ range (q - 1),
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n s *
          (1 - x ^ C)⁻¹) =
        (∑ s ∈ range (q - 1),
          (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n s) *
          (1 - x ^ C)⁻¹ := by rw [Finset.sum_mul]
      _ = (1 - x) * x ^ (C - 1) *
          (∑ s ∈ range (q - 1), terminalChildWindowDeviation n s) *
            (1 - x ^ C)⁻¹ := by rw [Finset.mul_sum]
  rw [hfactor, hprefix] at hterminal'
  have hfinal :
      (x ^ A) ^ (q - 1) * childSourceCofactorBlock (n + 1) n (A - 1) 0 x =
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (q - 1) *
          (1 - x ^ C)⁻¹ := by
    linear_combination hterminal'
  simpa [q, A, C] using hfinal

/-- Every physical child block in a terminal refinement is exactly the beta-scaled negative
tail of its signed lower-clock divisor-window innovations.  Thus the terminal child profile is
controlled by one chronological signed innovation sequence before any energy estimate. -/
theorem terminal_childSourceCofactorBlock_scaled_eq_tail_innovations
    (n b : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hb : b < clock (n + 1) / clock n) :
    (x ^ clock n) ^ (clock (n + 1) / clock n - 1 - b) *
        childSourceCofactorBlock (n + 1) n (clock n - 1) b x =
      -((1 - x) * x ^ (clock (n + 1) - 1) *
        (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
          terminalChildWindowDeviation n (b + s)) *
          (1 - x ^ clock (n + 1))⁻¹) := by
  let q := clock (n + 1) / clock n
  let A := clock n
  let C := clock (n + 1)
  let K := q - 1 - b
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (Nat.le_of_dvd (clock_pos (n + 1)) (clock_dvd (Nat.le_succ n)))
      (clock_pos n)
  have hratio : canonicalClockRatio (n + 1) (n + 1) = 1 := by
    rw [canonicalClockRatio_eq_div_of_le (n + 1) (n + 1) le_rfl]
    exact Nat.div_self (clock_pos (n + 1))
  have hspan : q * A = C := by
    dsimp [q, A, C]
    exact Nat.div_mul_cancel (clock_dvd (Nat.le_succ n))
  have hbq : b ≤ q - 1 := Nat.le_pred_of_lt (by simpa [q] using hb)
  have hbK : b + K = q - 1 := by
    dsimp [K]
    exact Nat.add_sub_of_le hbq
  have htotal : A - 1 + b * A + K * A = A - 1 + (q - 1) * A := by
    have hsum : b + (q - 1 - b) = q - 1 := Nat.add_sub_of_le hbq
    change A - 1 + b * A + (q - 1 - b) * A = A - 1 + (q - 1) * A
    calc
      A - 1 + b * A + (q - 1 - b) * A =
          A - 1 + (b + (q - 1 - b)) * A := by ring
      _ = _ := by rw [hsum]
  have hterminal : childSourceCofactorBlock (n + 1) n (A - 1 + b * A) K x = 0 := by
    have hsame :
        childSourceCofactorBlock (n + 1) n (A - 1 + b * A) K x =
          childSourceCofactorBlock (n + 1) n (A - 1) (q - 1) x := by
      unfold childSourceCofactorBlock
      rw [show A - 1 + b * A + K * clock n = A - 1 + (q - 1) * clock n by
        simpa [A, K] using htotal]
    calc
      childSourceCofactorBlock (n + 1) n (A - 1 + b * A) K x =
          childSourceCofactorBlock (n + 1) n (A - 1) (q - 1) x := hsame
      _ = 0 := by simpa [A, q] using terminal_childSourceCofactorBlock_eq_zero n x hx
  have hbase :
      childSourceCofactorBlock (n + 1) n (A - 1 + b * A) 0 x =
        childSourceCofactorBlock (n + 1) n (A - 1) b x := by
    unfold childSourceCofactorBlock
    simp [A]
  have hunroll := childSourceCofactorBlock_child_unroll
    (n + 1) n (A - 1 + b * A) K x (Nat.lt_succ_self n) hx
  rw [hterminal, hratio] at hunroll
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.zero_mul, pow_zero, one_mul] at hunroll
  simp only [Nat.add_zero] at hunroll
  rw [hbase] at hunroll
  have hraw (s : ℕ) :
      (clock n : ℝ) * ∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ) -
          ∑ k ∈ Ioc (A - 1 + b * A + s * A + 1)
            (A - 1 + b * A + s * A + A + 1),
            truncMoebiusDivisorSum (n + 1) k = terminalChildWindowDeviation n (b + s) := by
    unfold terminalChildWindowDeviation
    have hApos : 0 < A := by dsimp [A]; exact clock_pos n
    have hstart : A - 1 + b * A + s * A + 1 = A + (b + s) * A := by
      rw [Nat.add_mul]
      omega
    have hend : A - 1 + b * A + s * A + A + 1 = A + (b + s + 1) * A := by
      rw [Nat.add_mul]
      omega
    rw [hstart, hend]
  have hraw' (s : ℕ) :
      (clock n : ℝ) * ∑ d ∈ Icc 1 (n + 1), ((moebius d : ℤ) : ℝ) / (d : ℝ) -
          ∑ k ∈ Ioc (A - 1 + b * A + s * clock n + 1)
            (A - 1 + b * A + s * clock n + clock n + 1),
            truncMoebiusDivisorSum (n + 1) k = terminalChildWindowDeviation n (b + s) := by
    simpa [A] using hraw s
  simp_rw [hraw'] at hunroll
  have hsummand (s : ℕ) (hs : s ∈ range K) :
      (x ^ clock n) ^ (K - 1 - s) *
          ((1 - x) * x ^ (A - 1 + b * A + (s + 1) * clock n) *
            (terminalChildWindowDeviation n (b + s) * (1 - x ^ C)⁻¹)) =
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (b + s) *
          (1 - x ^ C)⁻¹ := by
    have hsK : s < K := mem_range.mp hs
    have hsle : s + 1 ≤ K := Nat.succ_le_iff.mpr hsK
    have hsub : K - 1 - s = K - (s + 1) := by omega
    have hle : (s + 1) * A ≤ K * A := Nat.mul_le_mul_right A hsle
    have hcancel := Nat.sub_add_cancel hle
    have hBK : b * A + K * A = (q - 1) * A := by
      rw [← Nat.add_mul, hbK]
    have hP : A - 1 + b * A + (s + 1) * A + 1 =
        A + b * A + (s + 1) * A := by
      have hApos : 0 < A := by dsimp [A]; exact clock_pos n
      omega
    have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqpos)
    have hqpred : (q - 1) * A + A = C := by
      calc
        (q - 1) * A + A = (q - 1 + 1) * A := by
          simpa using (Nat.add_mul (q - 1) 1 A).symm
        _ = q * A := by rw [hqeq]
        _ = C := hspan
    have hexp : A * (K - 1 - s) + (A - 1 + b * A + (s + 1) * A) = C - 1 := by
      calc
        A * (K - 1 - s) + (A - 1 + b * A + (s + 1) * A) =
            (K - (s + 1)) * A + (A - 1 + b * A + (s + 1) * A) := by
              rw [hsub, Nat.mul_comm]
        _ = (K * A - (s + 1) * A) + (A - 1 + b * A + (s + 1) * A) := by
          rw [Nat.sub_mul]
        _ = C - 1 := by
          have hplus :
              (K * A - (s + 1) * A) +
                  (A - 1 + b * A + (s + 1) * A) + 1 = C := by
            omega
          omega
    have hpow :
        (x ^ A) ^ (K - 1 - s) * x ^ (A - 1 + b * A + (s + 1) * A) = x ^ (C - 1) := by
      rw [← pow_mul, ← pow_add, hexp]
    calc
      (x ^ clock n) ^ (K - 1 - s) *
          ((1 - x) * x ^ (A - 1 + b * A + (s + 1) * clock n) *
            (terminalChildWindowDeviation n (b + s) * (1 - x ^ C)⁻¹)) =
          (1 - x) *
            ((x ^ A) ^ (K - 1 - s) * x ^ (A - 1 + b * A + (s + 1) * A)) *
            terminalChildWindowDeviation n (b + s) * (1 - x ^ C)⁻¹ := by
              simp only [A]
              ring
      _ = _ := by rw [hpow]
  have hsum :
      (∑ s ∈ range K,
        (x ^ clock n) ^ (K - 1 - s) *
          ((1 - x) * x ^ (A - 1 + b * A + (s + 1) * clock n) *
            (terminalChildWindowDeviation n (b + s) * (1 - x ^ clock (n + 1))⁻¹))) =
        ∑ s ∈ range K,
          (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (b + s) *
            (1 - x ^ C)⁻¹ := by
    apply Finset.sum_congr rfl
    intro s hs
    simpa [A, C] using hsummand s hs
  rw [hsum] at hunroll
  have hfactor :
      (∑ s ∈ range K,
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (b + s) *
          (1 - x ^ C)⁻¹) =
        (1 - x) * x ^ (C - 1) *
          (∑ s ∈ range K, terminalChildWindowDeviation n (b + s)) *
            (1 - x ^ C)⁻¹ := by
    calc
      (∑ s ∈ range K,
        (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (b + s) *
          (1 - x ^ C)⁻¹) =
        (∑ s ∈ range K,
          (1 - x) * x ^ (C - 1) * terminalChildWindowDeviation n (b + s)) *
          (1 - x ^ C)⁻¹ := by rw [Finset.sum_mul]
      _ = (1 - x) * x ^ (C - 1) *
          (∑ s ∈ range K, terminalChildWindowDeviation n (b + s)) *
            (1 - x ^ C)⁻¹ := by rw [Finset.mul_sum]
  rw [hfactor] at hunroll
  have hfinal :
      (x ^ A) ^ K * childSourceCofactorBlock (n + 1) n (A - 1) b x =
        -((1 - x) * x ^ (C - 1) *
          (∑ s ∈ range K, terminalChildWindowDeviation n (b + s)) *
            (1 - x ^ C)⁻¹) := by
    have hunroll' : 0 =
        (x ^ A) ^ K * childSourceCofactorBlock (n + 1) n (A - 1) b x +
          ((1 - x) * x ^ (C - 1) *
            (∑ s ∈ range K, terminalChildWindowDeviation n (b + s)) *
              (1 - x ^ C)⁻¹) := by
      simpa [A] using hunroll
    linarith
  simpa [q, A, C, K] using hfinal

/-- The signed chronological innovation tail which carries one terminal physical child block. -/
def terminalChildTailKernel (n b : ℕ) (x : ℝ) : ℝ :=
  -((1 - x) * x ^ (clock n * (b + 1) - 1) *
    (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
      terminalChildWindowDeviation n (b + s)) *
    (1 - x ^ clock (n + 1))⁻¹)

/-- Away from the zero endpoint, the terminal child block itself is a signed tail sum of
physical divisor-window innovations.  The beta powers cancel exactly, leaving the local
chronological exponent `clock n * (b + 1) - 1`. -/
theorem terminal_childSourceCofactorBlock_eq_tail_innovations_of_pos
    (n b : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxpos : 0 < x)
    (hb : b < clock (n + 1) / clock n) :
    childSourceCofactorBlock (n + 1) n (clock n - 1) b x =
      -((1 - x) * x ^ (clock n * (b + 1) - 1) *
        (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
          terminalChildWindowDeviation n (b + s)) *
          (1 - x ^ clock (n + 1))⁻¹) := by
  let q := clock (n + 1) / clock n
  let A := clock n
  let C := clock (n + 1)
  let K := q - 1 - b
  have hspan : q * A = C := by
    dsimp [q, A, C]
    exact Nat.div_mul_cancel (clock_dvd (Nat.le_succ n))
  have hbq : b ≤ q - 1 := Nat.le_pred_of_lt (by simpa [q] using hb)
  have hbK : b + K = q - 1 := by
    dsimp [K]
    exact Nat.add_sub_of_le hbq
  have hsum : K + (b + 1) = q := by omega
  have hweight : (x ^ A) ^ K ≠ 0 := by
    rw [← pow_mul]
    exact pow_ne_zero _ (ne_of_gt hxpos)
  apply (mul_left_cancel₀ hweight)
  rw [terminal_childSourceCofactorBlock_scaled_eq_tail_innovations n b x hx hb]
  have hexp : A * K + (A * (b + 1) - 1) = C - 1 := by
    have hP : A * (b + 1) - 1 + 1 = A * (b + 1) := by
      have hApos : 0 < A := by dsimp [A]; exact clock_pos n
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.mul_pos hApos (by omega)))
    have hQC : A * K + A * (b + 1) = C := by
      calc
        A * K + A * (b + 1) = A * (K + (b + 1)) := by ring
        _ = A * q := by rw [hsum]
        _ = q * A := by rw [Nat.mul_comm]
        _ = C := hspan
    omega
  have hpow : x ^ (A * K) * x ^ (A * (b + 1) - 1) = x ^ (C - 1) := by
    rw [← pow_add, hexp]
  have hweightpow : x ^ (A * K) = (x ^ A) ^ K := by rw [pow_mul]
  calc
    -((1 - x) * x ^ (clock (n + 1) - 1) *
          (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
            terminalChildWindowDeviation n (b + s)) *
          (1 - x ^ clock (n + 1))⁻¹) =
        x ^ (A * K) *
          -((1 - x) * x ^ (A * (b + 1) - 1) *
            (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
              terminalChildWindowDeviation n (b + s)) *
            (1 - x ^ clock (n + 1))⁻¹) := by
              rw [← hpow]
              ring
    _ = _ := by
      rw [hweightpow]

/-- Integrating a terminal source--cofactor child block is exactly integrating its signed
innovation-tail kernel.  The excluded `x = 0` endpoint is null for the physical interval. -/
theorem intervalIntegral_terminal_childSourceCofactorBlock_eq_tailKernel (n b : ℕ)
    (hb : b < clock (n + 1) / clock n) :
    (∫ x in (0 : ℝ)..1, childSourceCofactorBlock (n + 1) n (clock n - 1) b x) =
      ∫ x in (0 : ℝ)..1, terminalChildTailKernel n b x := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa [terminalChildTailKernel] using
    terminal_childSourceCofactorBlock_eq_tail_innovations_of_pos n b x hx.1.le hx.1 hb

/-- A lower residue and an admissible child index give a genuine child residue coordinate. -/
theorem childResidue_lt_clock_succ (l u b : ℕ)
    (hu : u < clock l) (hb : b < clock (l + 1) / clock l) :
    u + b * clock l < clock (l + 1) := by
  have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ l))
  calc
    u + b * clock l < clock l + b * clock l := Nat.add_lt_add_right hu _
    _ = (b + 1) * clock l := by ring
    _ ≤ (clock (l + 1) / clock l) * clock l :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hb)
    _ = clock (l + 1) := hclock

/-- Each physical parent fibre is exactly the disjoint union of its genuine successor fibres. -/
theorem historyFibre_parent_eq_child_biUnion (l u : ℕ) (hu : u < clock l) :
    historyFibre l u =
      ⋃ b ∈ range (clock (l + 1) / clock l),
        historyFibre (l + 1) (u + b * clock l) := by
  ext j
  constructor
  · intro hj
    have hdiv : clock l ∣ clock (l + 1) := clock_dvd (Nat.le_succ l)
    let r := j % clock (l + 1)
    let b := r / clock l
    have hmod : r % clock l = u := by
      rw [show r = j % clock (l + 1) by rfl, Nat.mod_mod_of_dvd j hdiv]
      exact hj
    have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
      Nat.div_mul_cancel hdiv
    have hr : r < clock (l + 1) := by
      exact Nat.mod_lt _ (clock_pos _)
    have hb : b < clock (l + 1) / clock l := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm, hclock]
      exact hr
    have hrdecomp : r = u + b * clock l := by
      calc
        r = r % clock l + clock l * (r / clock l) :=
          (Nat.mod_add_div r (clock l)).symm
        _ = u + b * clock l := by rw [hmod, Nat.mul_comm]
    refine Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨mem_range.mpr hb, ?_⟩⟩
    change j % clock (l + 1) = u + b * clock l
    rw [← hrdecomp]
  · simp only [Set.mem_iUnion]
    rintro ⟨b, hb, hj⟩
    have hdiv : clock l ∣ clock (l + 1) := clock_dvd (Nat.le_succ l)
    change j % clock l = u
    rw [← Nat.mod_mod_of_dvd j hdiv, hj, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hu]

/-- Actual physical parent mass is the sum of actual successor-fibre masses.  This retains the
nonuniform Báez--Duarte weights and supplies the normalization for a physical child variance. -/
theorem historyFibre_parent_mass_eq_child_mass_sum (l u : ℕ) (hu : u < clock l) :
    cellMeasure.real (historyFibre l u) =
      ∑ b ∈ range (clock (l + 1) / clock l),
        cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) := by
  let q := clock (l + 1) / clock l
  let child : ℕ → Set ℕ := fun b => historyFibre (l + 1) (u + b * clock l)
  have hpartition : historyFibre l u = ⋃ b ∈ range q, child b := by
    simpa only [q, child] using historyFibre_parent_eq_child_biUnion l u hu
  have hdisjoint : Set.Pairwise (↑(range q) : Set ℕ)
      (Function.onFun Disjoint child) := by
    intro b hb c hc hbc
    refine Set.disjoint_left.2 ?_
    intro j hjb hjc
    apply hbc
    change j % clock (l + 1) = u + b * clock l at hjb
    change j % clock (l + 1) = u + c * clock l at hjc
    have heq : u + b * clock l = u + c * clock l := hjb.symm.trans hjc
    have hmul : b * clock l = c * clock l := Nat.add_left_cancel heq
    exact Nat.eq_of_mul_eq_mul_right (clock_pos l) hmul
  have hmeas : ∀ b ∈ range q, MeasurableSet (child b) := by
    intro b hb
    exact (Set.to_countable _).measurableSet
  calc
    cellMeasure.real (historyFibre l u) = cellMeasure.real (⋃ b ∈ range q, child b) := by
      rw [hpartition]
    _ = ∑ b ∈ range q, cellMeasure.real (child b) :=
      measureReal_biUnion_finset hdisjoint hmeas
    _ = _ := by rfl

/-- A predictable-drift layer is pointwise constant on each genuine successor fibre. -/
theorem historyLayer_predictableDrift_const_on_childFibre
    (l N r j : ℕ) (hj : j ∈ historyFibre (l + 1) r)
    (hr : r < clock (l + 1)) :
    (historyLayer l (predictableDrift N)) j =
      (historyLayer l (predictableDrift N)) r := by
  obtain ⟨h, hh, hpoint⟩ := historySpace_factors_through_clock (l + 1)
    (historyLayer l (predictableDrift N))
    (historyLayer_mem_historySpace_succ l (predictableDrift N))
  change j % clock (l + 1) = r at hj
  calc
    (historyLayer l (predictableDrift N)) j = h (j % clock (l + 1)) := hpoint j
    _ = h r := by rw [hj]
    _ = h (r % clock (l + 1)) := by rw [Nat.mod_eq_of_lt hr]
    _ = (historyLayer l (predictableDrift N)) r := (hpoint r).symm

/-- The physical weighted sum of the child layer coordinates of each parent is exactly zero. -/
theorem historyLayer_predictableDrift_child_weighted_sum_eq_zero
    (l N u : ℕ) (hu : u < clock l) :
    ∑ b ∈ range (clock (l + 1) / clock l),
      cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
        (historyLayer l (predictableDrift N)) (u + b * clock l) = 0 := by
  let q := clock (l + 1) / clock l
  let child : ℕ → Set ℕ := fun b => historyFibre (l + 1) (u + b * clock l)
  let h := historyLayer l (predictableDrift N)
  have hpartition : historyFibre l u = ⋃ b ∈ range q, child b := by
    simpa only [q, child] using historyFibre_parent_eq_child_biUnion l u hu
  have hdisjoint : Set.Pairwise (↑(range q) : Set ℕ)
      (Function.onFun Disjoint child) := by
    intro b hb c hc hbc
    refine Set.disjoint_left.2 ?_
    intro j hjb hjc
    apply hbc
    change j % clock (l + 1) = u + b * clock l at hjb
    change j % clock (l + 1) = u + c * clock l at hjc
    have heq : u + b * clock l = u + c * clock l := hjb.symm.trans hjc
    have hmul : b * clock l = c * clock l := Nat.add_left_cancel heq
    exact Nat.eq_of_mul_eq_mul_right (clock_pos l) hmul
  have hmeas : ∀ b ∈ range q, MeasurableSet (child b) := by
    intro b hb
    exact (Set.to_countable _).measurableSet
  have hint : Integrable (h : ℕ → ℝ) cellMeasure :=
    (Lp.memLp h).integrable one_le_two
  have hchild_int (b : ℕ) (hb : b ∈ range q) :
      ∫ j in child b, h j ∂cellMeasure =
        cellMeasure.real (child b) * h (u + b * clock l) := by
    have hr : u + b * clock l < clock (l + 1) := by
      apply childResidue_lt_clock_succ l u b hu
      exact mem_range.mp hb
    rw [show (∫ j in child b, h j ∂cellMeasure) =
        ∫ _j in child b, h (u + b * clock l) ∂cellMeasure by
      apply setIntegral_congr_fun (hmeas b hb)
      intro j hj
      exact historyLayer_predictableDrift_const_on_childFibre l N
        (u + b * clock l) j hj hr]
    simpa only [smul_eq_mul] using
      (setIntegral_const (μ := cellMeasure) (s := child b) (h (u + b * clock l)))
  calc
    ∑ b ∈ range (clock (l + 1) / clock l),
        cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
          (historyLayer l (predictableDrift N)) (u + b * clock l) =
        ∑ b ∈ range q, ∫ j in child b, h j ∂cellMeasure := by
          apply Finset.sum_congr rfl
          intro b hb
          exact (hchild_int b hb).symm
    _ = ∫ j in ⋃ b ∈ range q, child b, h j ∂cellMeasure := by
      exact (integral_biUnion_finset (range q) hmeas hdisjoint
        (fun _ _ => hint.integrableOn)).symm
    _ = ∫ j in historyFibre l u, h j ∂cellMeasure := by rw [hpartition]
    _ = 0 := historyLayer_integral_lower_fibre_eq_zero l u (predictableDrift N)

private theorem two_mul_weighted_bilinear_eq_rank_one_add_pairwise
    {ι : Type*} (s : Finset ι) (w a b : ι → ℝ) :
    2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) =
      2 * (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) +
        ∑ i ∈ s, ∑ j ∈ s,
          w i * w j * (a i - a j) * (b i - b j) := by
  let L0 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a j * b j
  let L1 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a i * b i
  let C0 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a i * b j
  let C1 := ∑ i ∈ s, ∑ j ∈ s, w i * w j * a j * b i
  have hWC : (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) = L0 := by
    dsimp [L0]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hAB : (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) = C0 := by
    dsimp [C0]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hL : L0 = L1 := by
    dsimp [L0, L1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hC : C0 = C1 := by
    dsimp [C0, C1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show (2 * (∑ i ∈ s, w i)) * (∑ i ∈ s, w i * a i * b i) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i)) by ring,
    show (2 * (∑ i ∈ s, w i * a i)) * (∑ i ∈ s, w i * b i) =
      2 * ((∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) by ring,
    hWC, hAB]
  calc
    2 * L0 = L0 + L1 := by rw [← hL]; ring
    _ = 2 * C0 + (L1 + L0 - C0 - C1) := by rw [← hC]; ring
    _ = 2 * C0 + ∑ i ∈ s, ∑ j ∈ s,
        w i * w j * (a i - a j) * (b i - b j) := by
      congr 1
      dsimp [L0, L1, C0, C1]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Exact physical child-fibre Dirichlet form for one EDQ layer.  The parent-weighted child
energy is the pairwise energy of its child contrasts, so the common parent block has been
eliminated before any estimate. -/
theorem two_mul_historyLayer_parent_child_energy_eq_pairwise
    (l N u : ℕ) (hu : u < clock l) :
    2 * cellMeasure.real (historyFibre l u) *
        (∑ b ∈ range (clock (l + 1) / clock l),
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
            (historyLayer l (predictableDrift N)) (u + b * clock l) ^ 2) =
      ∑ b ∈ range (clock (l + 1) / clock l),
        ∑ c ∈ range (clock (l + 1) / clock l),
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
            cellMeasure.real (historyFibre (l + 1) (u + c * clock l)) *
            ((historyLayer l (predictableDrift N)) (u + b * clock l) -
              (historyLayer l (predictableDrift N)) (u + c * clock l)) ^ 2 := by
  let q := clock (l + 1) / clock l
  let w : ℕ → ℝ := fun b => cellMeasure.real (historyFibre (l + 1) (u + b * clock l))
  let value : ℕ → ℝ := fun b => (historyLayer l (predictableDrift N)) (u + b * clock l)
  have hmass : cellMeasure.real (historyFibre l u) = ∑ b ∈ range q, w b := by
    simpa only [q, w] using historyFibre_parent_mass_eq_child_mass_sum l u hu
  have hzero : ∑ b ∈ range q, w b * value b = 0 := by
    simpa only [q, w, value] using
      historyLayer_predictableDrift_child_weighted_sum_eq_zero l N u hu
  have hvariance := two_mul_weighted_bilinear_eq_rank_one_add_pairwise
    (range q) w value value
  rw [hzero, mul_zero, zero_add] at hvariance
  rw [hmass]
  simpa only [q, w, value, pow_two, mul_assoc] using hvariance

/-- The contrast of two genuine physical children cancels their common parent resolvent exactly. -/
theorem historyLayer_predictableDrift_child_difference_eq_blockContrast
    (l N u b c : ℕ) (hlN : l < N)
    (hub : u + b * clock l < clock (l + 1))
    (huc : u + c * clock l < clock (l + 1)) :
    (historyLayer l (predictableDrift N)) (u + b * clock l) -
      (historyLayer l (predictableDrift N)) (u + c * clock l) =
      ((∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u b x) /
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) -
        (∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u c x) /
          cellMeasure.real (historyFibre (l + 1) (u + c * clock l))) -
      (signedInnovation l (u + b * clock l) - signedInnovation l (u + c * clock l)) := by
  rw [historyLayer_predictableDrift_apply_eq_canonicalBetaResolvent_sub_innovation l N
        (u + b * clock l) hlN,
      historyLayer_predictableDrift_apply_eq_canonicalBetaResolvent_sub_innovation l N
        (u + c * clock l) hlN]
  have hmodb : (u + b * clock l) % clock l = u % clock l := by
    rw [Nat.add_mul_mod_self_right]
  have hmodc : (u + c * clock l) % clock l = u % clock l := by
    rw [Nat.add_mul_mod_self_right]
  rw [hmodb, hmodc, Nat.mod_eq_of_lt hub, Nat.mod_eq_of_lt huc,
    canonicalBetaResolvent_succ_eq_refinementBlockKernel,
    canonicalBetaResolvent_succ_eq_refinementBlockKernel]
  ring

/-- Every genuine child contrast is an exact physical contrast of the two signed
source--future-cofactor blocks, plus only the two local innovations.  The common lower
resolvent and its complete parent aggregate are absent. -/
theorem historyLayer_predictableDrift_child_difference_eq_sourceCofactorContrast
    (l N u b c : ℕ) (hlN : l < N)
    (hub : u + b * clock l < clock (l + 1))
    (huc : u + c * clock l < clock (l + 1)) :
    (historyLayer l (predictableDrift N)) (u + b * clock l) -
      (historyLayer l (predictableDrift N)) (u + c * clock l) =
      ((∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u b x) /
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) -
        (∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u c x) /
          cellMeasure.real (historyFibre (l + 1) (u + c * clock l))) -
      (signedInnovation l (u + b * clock l) - signedInnovation l (u + c * clock l)) := by
  have hblockb :
      (∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u b x) =
        ∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u b x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementBlockKernel_eq_childSourceCofactorBlock N l u b x hlN hx'.1
  have hblockc :
      (∫ x in (0 : ℝ)..1, canonicalRefinementBlockKernel N l u c x) =
        ∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u c x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
    exact canonicalRefinementBlockKernel_eq_childSourceCofactorBlock N l u c x hlN hx'.1
  rw [historyLayer_predictableDrift_child_difference_eq_blockContrast l N u b c hlN hub huc,
    hblockb, hblockc]

/-- Exact physical EDQ child-fibre energy in the only remaining signed coordinates: pairwise
differences of the two source--future-cofactor blocks and their local innovations.  No parent
aggregate, uniform-period substitute, absolute-value split, or deleted residual-one channel
remains in this formula. -/
theorem two_mul_historyLayer_parent_child_energy_eq_sourceCofactor_pairwise
    (l N u : ℕ) (hlN : l < N) (hu : u < clock l) :
    2 * cellMeasure.real (historyFibre l u) *
        (∑ b ∈ range (clock (l + 1) / clock l),
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
            (historyLayer l (predictableDrift N)) (u + b * clock l) ^ 2) =
      ∑ b ∈ range (clock (l + 1) / clock l),
        ∑ c ∈ range (clock (l + 1) / clock l),
          cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) *
            cellMeasure.real (historyFibre (l + 1) (u + c * clock l)) *
            (((∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u b x) /
                cellMeasure.real (historyFibre (l + 1) (u + b * clock l)) -
              (∫ x in (0 : ℝ)..1, childSourceCofactorBlock N l u c x) /
                cellMeasure.real (historyFibre (l + 1) (u + c * clock l))) -
              (signedInnovation l (u + b * clock l) - signedInnovation l (u + c * clock l))) ^ 2 := by
  rw [two_mul_historyLayer_parent_child_energy_eq_pairwise l N u hu]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have hub : u + b * clock l < clock (l + 1) :=
    childResidue_lt_clock_succ l u b hu (mem_range.mp hb)
  have huc : u + c * clock l < clock (l + 1) :=
    childResidue_lt_clock_succ l u c hu (mem_range.mp hc)
  rw [historyLayer_predictableDrift_child_difference_eq_sourceCofactorContrast
    l N u b c hlN hub huc]

/-- Exact terminal physical EDQ energy written entirely in signed chronological innovation
tails and the untouched local innovations.  This is the remaining energy object to bound. -/
theorem two_mul_terminal_historyLayer_parent_child_energy_eq_tail_pairwise (n : ℕ) :
    2 * cellMeasure.real (historyFibre n (clock n - 1)) *
        (∑ b ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            (historyLayer n (predictableDrift (n + 1)) (clock n - 1 + b * clock n)) ^ 2) =
      ∑ b ∈ range (clock (n + 1) / clock n),
        ∑ c ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n)) *
            (((∫ x in (0 : ℝ)..1, terminalChildTailKernel n b x) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) -
              (∫ x in (0 : ℝ)..1, terminalChildTailKernel n c x) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n))) -
              (signedInnovation n (clock n - 1 + b * clock n) -
                signedInnovation n (clock n - 1 + c * clock n))) ^ 2 := by
  have hu : clock n - 1 < clock n := by
    have hpos : 0 < clock n := clock_pos n
    omega
  rw [two_mul_historyLayer_parent_child_energy_eq_sourceCofactor_pairwise
    n (n + 1) (clock n - 1) (Nat.lt_succ_self n) hu]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [intervalIntegral_terminal_childSourceCofactorBlock_eq_tailKernel n b (mem_range.mp hb),
    intervalIntegral_terminal_childSourceCofactorBlock_eq_tailKernel n c (mem_range.mp hc)]

/-- The exact beta weight of a terminal chronological innovation tail. -/
def terminalChildTailWeight (n b : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (1 - x) * x ^ (clock n * (b + 1) - 1) *
      (1 - x ^ clock (n + 1))⁻¹

/-- A finite initial segment of a nonnegative geometric denominator controls its last power.
This is the pointwise half-prefix estimate needed to compare a terminal beta weight with the
native physical cell mass. -/
theorem geometric_denominator_half_prefix_lower
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h C : ℕ) (hhC : h ≤ C) :
    (h : ℝ) * x ^ (h - 1) ≤ ∑ i ∈ range C, x ^ i := by
  calc
    (h : ℝ) * x ^ (h - 1) ≤ ∑ i ∈ range h, x ^ i := by
      calc
        (h : ℝ) * x ^ (h - 1) = ∑ i ∈ range h, x ^ (h - 1) := by simp
        _ ≤ ∑ i ∈ range h, x ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_of_le_one hx0 hx1 (Nat.le_pred_of_lt (mem_range.mp hi))
    _ ≤ ∑ i ∈ range C, x ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (range_mono hhC)
      intro i _ _
      positivity

/-- The terminal tail kernel integral is its signed finite innovation sum times its exact beta
weight.  No absolute value, asymptotic replacement, or unproved analytic remainder occurs. -/
theorem intervalIntegral_terminalChildTailKernel_eq_weighted_tail (n b : ℕ) :
    (∫ x in (0 : ℝ)..1, terminalChildTailKernel n b x) =
      -(∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
        terminalChildWindowDeviation n (b + s)) * terminalChildTailWeight n b := by
  unfold terminalChildTailKernel terminalChildTailWeight
  calc
    (∫ x in (0 : ℝ)..1,
        -((1 - x) * x ^ (clock n * (b + 1) - 1) *
          (∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
            terminalChildWindowDeviation n (b + s)) *
          (1 - x ^ clock (n + 1))⁻¹)) =
        ∫ x in (0 : ℝ)..1,
          -(∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
            terminalChildWindowDeviation n (b + s)) *
            ((1 - x) * x ^ (clock n * (b + 1) - 1) *
              (1 - x ^ clock (n + 1))⁻¹) := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- A terminal tail-kernel integral is one literal physical Möbius source cell times its beta
weight.  The signed tail has telescoped completely, leaving no unresolved window sum. -/
theorem intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight
    (n b : ℕ) (hb : b < clock (n + 1) / clock n) :
    (∫ x in (0 : ℝ)..1, terminalChildTailKernel n b x) =
      DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
        (clock n * (b + 1)) * terminalChildTailWeight n b := by
  rw [intervalIntegral_terminalChildTailKernel_eq_weighted_tail,
    terminalChildWindowDeviation_tail_eq_neg_physicalCell n b hb]
  ring

/-- Exact terminal child energy in physical endpoint-cell coordinates.  Each child block is now
one literal source cell weighted by its beta carrier; the only remaining nonlocal term is the
unchanged local signed innovation. -/
theorem two_mul_terminal_historyLayer_parent_child_energy_eq_physicalCell_pairwise (n : ℕ) :
    2 * cellMeasure.real (historyFibre n (clock n - 1)) *
        (∑ b ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            (historyLayer n (predictableDrift (n + 1)) (clock n - 1 + b * clock n)) ^ 2) =
      ∑ b ∈ range (clock (n + 1) / clock n),
        ∑ c ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n)) *
            (((DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
                  (clock n * (b + 1)) * terminalChildTailWeight n b) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) -
              (DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
                  (clock n * (c + 1)) * terminalChildTailWeight n c) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n))) -
              (signedInnovation n (clock n - 1 + b * clock n) -
                signedInnovation n (clock n - 1 + c * clock n))) ^ 2 := by
  rw [two_mul_terminal_historyLayer_parent_child_energy_eq_tail_pairwise]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight n b (mem_range.mp hb),
    intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight n c (mem_range.mp hc)]

/-- The terminal physical EDQ energy is a finite pairwise quadratic form in signed chronological
innovation-tail sums, their exact beta weights, and the pre-existing local innovations. -/
theorem two_mul_terminal_historyLayer_parent_child_energy_eq_weighted_tail_pairwise (n : ℕ) :
    2 * cellMeasure.real (historyFibre n (clock n - 1)) *
        (∑ b ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            (historyLayer n (predictableDrift (n + 1)) (clock n - 1 + b * clock n)) ^ 2) =
      ∑ b ∈ range (clock (n + 1) / clock n),
        ∑ c ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n)) *
            (((-(∑ s ∈ range (clock (n + 1) / clock n - 1 - b),
                terminalChildWindowDeviation n (b + s)) * terminalChildTailWeight n b) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) -
              (-(∑ s ∈ range (clock (n + 1) / clock n - 1 - c),
                terminalChildWindowDeviation n (c + s)) * terminalChildTailWeight n c) /
                cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n))) -
              (signedInnovation n (clock n - 1 + b * clock n) -
                signedInnovation n (clock n - 1 + c * clock n))) ^ 2 := by
  rw [two_mul_terminal_historyLayer_parent_child_energy_eq_tail_pairwise]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [intervalIntegral_terminalChildTailKernel_eq_weighted_tail,
    intervalIntegral_terminalChildTailKernel_eq_weighted_tail]

/-- At every composite terminal level, local EDQ innovations vanish pointwise.  The remaining
child contrast is exactly the difference of the two beta-weighted literal physical Möbius cells.
Thus the terminal signed-covariance problem has a prime-level local correction only; no
uniform-period or absolute-value replacement is used. -/
theorem terminal_historyLayer_child_difference_eq_physicalCell_of_not_prime
    (n b c : ℕ) (hn : ¬ (n + 1).Prime)
    (hb : b < clock (n + 1) / clock n)
    (hc : c < clock (n + 1) / clock n) :
    (historyLayer n (predictableDrift (n + 1))
      (clock n - 1 + b * clock n) -
      historyLayer n (predictableDrift (n + 1))
        (clock n - 1 + c * clock n)) =
      (DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
          (clock n * (b + 1)) * terminalChildTailWeight n b /
        cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) -
      DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
          (clock n * (c + 1)) * terminalChildTailWeight n c /
        cellMeasure.real (historyFibre (n + 1) (clock n - 1 + c * clock n))) := by
  have hu : clock n - 1 < clock n := by
    have hpos : 0 < clock n := clock_pos n
    omega
  have hub : clock n - 1 + b * clock n < clock (n + 1) :=
    childResidue_lt_clock_succ n (clock n - 1) b hu hb
  have huc : clock n - 1 + c * clock n < clock (n + 1) :=
    childResidue_lt_clock_succ n (clock n - 1) c hu hc
  have hinnovb : signedInnovation n (clock n - 1 + b * clock n) = 0 := by
    exact cell_point_eq_of_ae (f := fun k => signedInnovation n k)
      (g := fun _ => 0) (by
        rw [signedInnovation_eq_zero_of_not_prime n hn]
        exact Lp.coeFn_zero ℝ 2 cellMeasure) _
  have hinnovc : signedInnovation n (clock n - 1 + c * clock n) = 0 := by
    exact cell_point_eq_of_ae (f := fun k => signedInnovation n k)
      (g := fun _ => 0) (by
        rw [signedInnovation_eq_zero_of_not_prime n hn]
        exact Lp.coeFn_zero ℝ 2 cellMeasure) _
  rw [historyLayer_predictableDrift_child_difference_eq_sourceCofactorContrast
    n (n + 1) (clock n - 1) b c (Nat.lt_succ_self n) hub huc,
    intervalIntegral_terminal_childSourceCofactorBlock_eq_tailKernel n b hb,
    intervalIntegral_terminal_childSourceCofactorBlock_eq_tailKernel n c hc,
    intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight n b hb,
    intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight n c hc,
    hinnovb, hinnovc]
  ring

end RHTower.DeletionResidueMartingale
