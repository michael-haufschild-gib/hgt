import GaloisForLFunctions.RHTower.MobiusSquareCornerMoments

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

private theorem corner_sum_Icc_split (f : ℕ → ℝ) {N U : ℕ} (hUN : U ≤ N) :
    (∑ a ∈ Icc 1 N, f a) = (∑ a ∈ Icc 1 U, f a) + ∑ a ∈ Ioc U N, f a := by
  have hset : Icc 1 U ∪ Ioc U N = Icc 1 N := by
    ext a
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 U) (Ioc U N) := by
    apply disjoint_left.mpr
    intro a ha hb
    have := (mem_Icc.mp ha).2
    have := (mem_Ioc.mp hb).1
    omega
  rw [← hset, sum_union hd]

private theorem corner_symmetric_square_split (f : ℕ → ℕ → ℝ)
    (hsymm : ∀ a b, f a b = f b a) {N U : ℕ} (hUN : U ≤ N) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, f a b) =
      (∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, f a b) +
        2 * (∑ a ∈ Icc 1 U, ∑ b ∈ Ioc U N, f a b) +
        ∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N, f a b := by
  have hrow (a : ℕ) := corner_sum_Icc_split (fun b => f a b) hUN
  rw [corner_sum_Icc_split (fun a => ∑ b ∈ Icc 1 N, f a b) hUN]
  simp_rw [hrow, sum_add_distrib]
  have hcross : (∑ a ∈ Ioc U N, ∑ b ∈ Icc 1 U, f a b) =
      ∑ a ∈ Icc 1 U, ∑ b ∈ Ioc U N, f a b := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    exact hsymm b a
  rw [hcross]
  ring

/-- The mixed rows joining the inner square to the outer corner. -/
noncomputable def mobiusSquareCornerCrossAction (N U : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, ∑ b ∈ Ioc U N,
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      mobiusSquareShortBilinearKernel N (a * b)

/-- Mixed rows with precisely their share of the original counterterm. -/
noncomputable def mobiusSquareCornerCenteredCross (N U : ℕ) : ℝ :=
  mobiusSquareCornerCrossAction N U -
    (∑ d ∈ Ioc U N, (ArithmeticFunction.moebius d : ℝ) * Real.log d / d) *
      ∑ s ∈ range N, (s : ℝ) ^ 2

theorem logMobiusShortBilinearSquareAction_eq_corner_partition
    {N U : ℕ} (hUN : U ≤ N) :
    logMobiusShortBilinearSquareAction N =
      logMobiusCutoffBilinearSquareAction N U + 2 * mobiusSquareCornerCrossAction N U +
        mobiusSquareCornerAction N U := by
  have h := corner_symmetric_square_split
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      mobiusSquareShortBilinearKernel N (a * b))
    (by intro a b; rw [Nat.mul_comm a b]; ring) hUN
  simpa only [logMobiusShortBilinearSquareAction, logMobiusCutoffBilinearSquareAction,
    mobiusSquareCornerCrossAction, mobiusSquareCornerAction, mul_sum, mul_assoc] using h

/-- The four-moment corner sits in the full source with mixed rows and counterterm intact. -/
theorem mobiusShortBilinearSquareSource_eq_corner_moments
    {N U : ℕ} (hUN : U ≤ N) (hcell : (N - 1) ^ 2 < 2 * (U + 1) ^ 2) :
    mobiusShortBilinearSquareSource N =
      mobiusCutoffBilinearSquareSource N U + 2 * mobiusSquareCornerCenteredCross N U +
        mobiusSquareCornerContinuous N U - mobiusSquareCornerRounding N U := by
  have hC := corner_sum_Icc_split
    (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log d / d) hUN
  unfold mobiusShortBilinearSquareSource mobiusCutoffBilinearSquareSource
    mobiusSquareCornerCenteredCross
  rw [logMobiusShortBilinearSquareAction_eq_corner_partition hUN,
    mobiusSquareCornerAction_eq_continuous_sub_rounding N U hcell, hC]
  ring

theorem abs_mobiusShortBilinearSquareSource_sub_corner_moments_le
    {N U : ℕ} (hUN : U ≤ N) (hcell : (N - 1) ^ 2 < 2 * (U + 1) ^ 2) :
    |mobiusShortBilinearSquareSource N -
      (mobiusCutoffBilinearSquareSource N U + 2 * mobiusSquareCornerCenteredCross N U +
        mobiusSquareCornerContinuous N U)| ≤
      2 * ((N - U : ℕ) : ℝ) ^ 2 * Real.log (N : ℝ) := by
  have heq : mobiusShortBilinearSquareSource N -
      (mobiusCutoffBilinearSquareSource N U + 2 * mobiusSquareCornerCenteredCross N U +
        mobiusSquareCornerContinuous N U) = -mobiusSquareCornerRounding N U := by
    rw [mobiusShortBilinearSquareSource_eq_corner_moments hUN hcell]
    ring
  rw [heq, abs_neg]
  exact abs_mobiusSquareCornerRounding_le N U

end RHTower
