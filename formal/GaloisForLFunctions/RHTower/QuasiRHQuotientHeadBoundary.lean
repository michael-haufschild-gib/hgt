import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusQuotientTail
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusRieszPrimeCellSign

/-!
# The physical boundary of a shortened quotient head

Abel transport of the truncated head keeps its upper-edge term. The first
quotient channel also reconstructs the full Möbius--Riesz tail along dyadic
scales. The boundary has the same intrinsic-abscissa saving as the discarded
quotient tail, so the increment head retains the full cutoff estimate.
-/

noncomputable section

namespace RHTower

open Finset

/-- The short head retains the boundary absent from the full physical range. -/
theorem mobiusDivisorQuotientHead_eq_increment_rieszTail_boundary (M Q : ℕ) :
    mobiusDivisorQuotientHead M Q =
      (∑ n ∈ Icc 1 (min Q (M - 1)),
        primeFreeDivisorIncrement n * mobiusDilationRieszTail M n) -
      primeFreeDivisorDefect (min Q (M - 1)) *
        mobiusDilationRieszTail M (min Q (M - 1) + 1) := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    primeFreeDivisorIncrement (mobiusDilationRieszTail M) (min Q (M - 1))
  simp_rw [sum_primeFreeDivisorIncrement] at h
  have hg :
      (∑ n ∈ Icc 1 (min Q (M - 1)), primeFreeDivisorDefect n *
        (mobiusDilationRieszTail M n - mobiusDilationRieszTail M (n + 1))) =
          mobiusDivisorQuotientHead M Q := by
    apply sum_congr rfl
    intro n hn
    rw [← mobiusClippedAbelKernel_eq_rieszTailGradient (mem_Icc.mp hn).1
      ((mem_Icc.mp hn).2.trans (min_le_right _ _))]
  rw [hg] at h
  linarith

/-- The first quotient kernel is an exact dyadic difference of the signed Riesz tail. -/
theorem mobiusClippedAbelKernel_one_double (M : ℕ) :
    mobiusClippedAbelKernel (2 * M) 1 =
      mobiusDilationRieszTail (2 * M) 1 - Real.sqrt 2 * mobiusDilationRieszTail M 1 := by
  by_cases hM : M = 0
  · subst M
    simp [mobiusClippedAbelKernel, mobiusDilationRieszTail]
  · rw [mobiusClippedAbelKernel_eq_rieszTailGradient (by omega) (by omega)]
    have hd := MobiusRieszCancellation.tail_dilate M 1 2 (by omega) (by omega)
    norm_num only [mul_one] at hd
    rw [hd]

/-- Telescoping the first quotient channel reconstructs the tail on every dyadic ladder. -/
theorem mobiusDilationRieszTail_dyadic_reconstruction (M j : ℕ) :
    mobiusDilationRieszTail (2 ^ j * M) 1 / Real.sqrt 2 ^ j =
      mobiusDilationRieszTail M 1 +
        ∑ i ∈ range j,
          mobiusClippedAbelKernel (2 ^ (i + 1) * M) 1 / Real.sqrt 2 ^ (i + 1) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have hscale : 2 ^ (j + 1) * M = 2 * (2 ^ j * M) := by ring
    have hk := mobiusClippedAbelKernel_one_double (2 ^ j * M)
    rw [← hscale] at hk
    rw [hk, pow_succ (Real.sqrt 2)]
    field_simp [hs]
    ring

/-- Summing the actual kernel bound controls the transported tail beyond any positive cutoff. -/
theorem abs_mobiusDilationRieszTail_succ_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M Q : ℕ, 1 ≤ Q →
      |mobiusDilationRieszTail M (Q + 1)| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Q : ℝ) ^ (-(zetaZeroAbscissa + ε)) := by
  obtain ⟨C, hC, hbound⟩ := abs_mobiusClippedAbelKernel_subpower ε hε
  let β := zetaZeroAbscissa + ε
  have hβ : 0 < β := by dsimp [β]; linarith [half_le_zetaZeroAbscissa]
  refine ⟨C / β, by positivity, fun M Q hQ => ?_⟩
  have hpower :
      (∑ q ∈ Icc (Q + 1) (M - 1), (q : ℝ) ^ (-β - 1)) ≤
        (Q : ℝ) ^ (-β) / β := by
    rw [show -β - 1 = -(β + 1) by ring,
      ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    have h := sum_range_add_rpow_neg_le (c := β + 1) (by linarith) hQ
      (M - 1 + 1 - (Q + 1))
    simpa only [Nat.add_comm, show 1 - (β + 1) = -β by ring,
      show β + 1 - 1 = β by ring] using h
  change |mobiusDilationRieszTail M (Q + 1)| ≤
    (C / β) * (M : ℝ) ^ (β + 1 / 2) * (Q : ℝ) ^ (-β)
  rw [← sum_mobiusClippedAbelKernel_tail_eq_rieszTail M (by omega : 1 ≤ Q + 1)]
  calc
    _ ≤ ∑ q ∈ Icc (Q + 1) (M - 1), |mobiusClippedAbelKernel M q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc (Q + 1) (M - 1),
        (C * (M : ℝ) ^ (β + 1 / 2)) * (q : ℝ) ^ (-β - 1) := by
      apply sum_le_sum
      intro q hq
      exact hbound M q (by have := (mem_Icc.mp hq).1; omega)
    _ = (C * (M : ℝ) ^ (β + 1 / 2)) *
        ∑ q ∈ Icc (Q + 1) (M - 1), (q : ℝ) ^ (-β - 1) :=
      (mul_sum _ _ _).symm
    _ ≤ (C * (M : ℝ) ^ (β + 1 / 2)) * ((Q : ℝ) ^ (-β) / β) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring

/-- The retained Abel boundary has the same intrinsic cutoff saving as the discarded quotient tail. -/
theorem abs_mobiusDivisorQuotientHead_boundary_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M Q : ℕ, 1 ≤ Q →
      |primeFreeDivisorDefect (min Q (M - 1)) *
        mobiusDilationRieszTail M (min Q (M - 1) + 1)| ≤
      C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
        (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) := by
  obtain ⟨C, hC, hbound⟩ := abs_mobiusDilationRieszTail_succ_subpower ε hε
  refine ⟨24 * C, by positivity, fun M Q hQ => ?_⟩
  by_cases hQM : Q ≤ M - 1
  · rw [min_eq_left hQM, abs_mul]
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    calc
      _ ≤ (24 * Real.sqrt Q) *
          (C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
            (Q : ℝ) ^ (-(zetaZeroAbscissa + ε))) :=
        mul_le_mul (abs_primeFreeDivisorDefect_le hQ) (hbound M Q hQ)
          (abs_nonneg _) (by positivity)
      _ = (24 * C) * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Real.sqrt Q * (Q : ℝ) ^ (-(zetaZeroAbscissa + ε))) := by ring
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ0]
        congr 2
        ring
  · have hz : mobiusDilationRieszTail M (min Q (M - 1) + 1) = 0 := by
      rw [min_eq_right (by omega : M - 1 ≤ Q)]
      by_cases hM : M = 0
      · simp [hM, mobiusDilationRieszTail]
      · rw [Nat.sub_add_cancel (by omega : 1 ≤ M)]
        exact mobiusDilationRieszTail_boundary_zero M
    rw [hz, mul_zero, abs_zero]
    positivity

/-- The literal increment head approximates the full Abel action with a controlled boundary. -/
theorem mobiusDivisorQuotientIncrementHead_error_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M Q : ℕ, 1 ≤ Q →
      |mobiusDivisorSquareRootAbelMoment M -
        ∑ n ∈ Icc 1 (min Q (M - 1)),
          primeFreeDivisorIncrement n * mobiusDilationRieszTail M n| ≤
      C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
        (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) := by
  obtain ⟨C₁, hC₁, htail⟩ := mobiusDivisorQuotientHead_error_subpower ε hε
  obtain ⟨C₂, hC₂, hboundary⟩ := abs_mobiusDivisorQuotientHead_boundary_subpower ε hε
  refine ⟨C₁ + C₂, by positivity, fun M Q hQ => ?_⟩
  have hid := mobiusDivisorQuotientHead_eq_increment_rieszTail_boundary M Q
  have htriangle := _root_.abs_sub_le
    (mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M Q) 0
    (primeFreeDivisorDefect (min Q (M - 1)) *
      mobiusDilationRieszTail M (min Q (M - 1) + 1))
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  have heq : mobiusDivisorSquareRootAbelMoment M -
      (∑ n ∈ Icc 1 (min Q (M - 1)),
        primeFreeDivisorIncrement n * mobiusDilationRieszTail M n) =
      (mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M Q) -
        primeFreeDivisorDefect (min Q (M - 1)) *
          mobiusDilationRieszTail M (min Q (M - 1) + 1) := by linarith
  rw [heq]
  calc
    _ ≤ _ := htriangle
    _ ≤ C₁ * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) +
        C₂ * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) :=
      add_le_add (htail M Q hQ) (hboundary M Q hQ)
    _ = _ := by ring

end RHTower
