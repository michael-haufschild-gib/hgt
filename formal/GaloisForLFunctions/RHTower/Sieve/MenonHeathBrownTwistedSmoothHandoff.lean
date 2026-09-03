import GaloisForLFunctions.RHTower.Sieve.MaynardAggregateSelection
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPerron
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistSharpSum

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- A compactly supported smooth weight sees the twisted finite Heath--Brown packet as the
twisted von Mangoldt coefficients. -/
theorem tsum_heathBrownFiniteCompressedPacket_twist_smoothWeight_eq_vonMangoldt
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) (tau : ℝ) {N H : ℝ} (hH : 0 < H)
    (hsupport : N + H ≤ X) :
    (∑' n : ℕ, complexCoeff (heathBrownFiniteCompressedPacket L X k) n *
        (n : ℂ) ^ (-((tau : ℂ) * I)) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, vonMangoldtTwist tau n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  apply tsum_congr
  intro n
  by_cases hnX : n ≤ X
  · have hncut : n < (L + 1) ^ k := hnX.trans_lt hXL
    rw [complexCoeff_apply,
      ← heathBrown_finite_compressed_identity L X k n hnX hncut]
    rfl
  · have hXn : X < n := Nat.lt_of_not_ge hnX
    have hzero : GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) = 0 := by
      apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
      have hcast : (X : ℝ) < (n : ℝ) := by exact_mod_cast hXn
      exact hsupport.trans hcast.le
    rw [hzero]
    simp

/-- Dirichlet series of a vertically twisted finite packet is its L-series at the shifted
ordinate. -/
theorem tsum_complexCoeff_twist_cpow_eq_LSeries
    (F : ArithmeticFunction ℝ) (tau : ℝ) (s : ℂ) :
    (∑' n : ℕ, complexCoeff F n * (n : ℂ) ^ (-((tau : ℂ) * I)) *
        (n : ℂ) ^ (-s)) =
      LSeries (complexCoeff F) (s + (tau : ℂ) * I) := by
  rw [← tsum_cpow_neg_eq_LSeries (a := complexCoeff F) (by simp)
    (s + (tau : ℂ) * I)]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [mul_assoc, ← Complex.cpow_add _ _ hn0,
      show -((tau : ℂ) * I) + -s = -(s + (tau : ℂ) * I) by ring]

/-- Contrapositive sharp-to-smooth handoff for a twisted von Mangoldt prefix. -/
theorem norm_tsum_vonMangoldtTwist_smoothWeight_gt_of_partialSum_gt
    (tau : ℝ) {K : ℕ} {H B : ℝ} (hH : 0 < H) (hKH : 1 ≤ (K : ℝ) + H)
    (hlarge : B / (2 * Real.pi) + Real.log ((K : ℝ) + H) * H <
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist tau n‖) :
    B < (2 * Real.pi) * ‖∑' n : ℕ,
      vonMangoldtTwist tau n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ := by
  by_contra hnot
  have hB : (2 * Real.pi) * ‖∑' n : ℕ,
      vonMangoldtTwist tau n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ ≤ B := le_of_not_gt hnot
  have hsharp := norm_partialSum_vonMangoldtTwist_le_of_smoothed_bound
    tau hH hKH hB
  linarith

/-- Exact twisted smooth Perron identity for the complete signed Heath--Brown aggregate.  The
physical twist translates only the aggregate ordinate; every selected box remains a literal full
Dirichlet product. -/
theorem tsum_vonMangoldtTwist_smoothWeight_eq_integral_heathBrownDyadicAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) (tau : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + H ≤ X) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist tau n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownDyadicAggregate L X k
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownFiniteCompressedPacket L X k
  let c : ℕ → ℂ := fun n => complexCoeff F n * (n : ℂ) ^ (-((tau : ℂ) * I))
  have hc0 : c 0 = 0 := by simp [c]
  have hsumF : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownFiniteCompressedPacket L X k (sigma : ℂ))
  have hnorm : ∀ n : ℕ, ‖c n‖ = ‖complexCoeff F n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [c]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
      have hphase : ‖((n : ℕ) : ℂ) ^ (-((tau : ℂ) * I))‖ = 1 := by
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
        simp
      simp [c, hphase]
  have hsum : Summable fun n : ℕ => ‖c n‖ * (n : ℝ) ^ (-sigma) := by
    refine hsumF.congr fun n => ?_
    rw [hnorm]
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := c) hc0 hN hH hsigma hsum
  rw [← tsum_heathBrownFiniteCompressedPacket_twist_smoothWeight_eq_vonMangoldt
    L X k hXL tau hH hsupport]
  rw [show (∑' n : ℕ, complexCoeff F n * (n : ℂ) ^ (-((tau : ℂ) * I)) *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, c n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) by rfl]
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only [c]
  congr 1
  rw [tsum_complexCoeff_twist_cpow_eq_LSeries]
  have harg : ((sigma : ℂ) + (y : ℝ) * I) + (tau : ℂ) * I =
      (sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg, LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts]
  rfl

/-- Exact Case-II source handoff: a large sharp twisted Chebyshev prefix forces a large vertical
Mellin integral of the literal complete signed Heath--Brown aggregate. -/
theorem norm_integral_heathBrownDyadicAggregate_gt_of_vonMangoldtTwist_prefix_gt
    (L X k K : ℕ) (hXL : X < (L + 1) ^ k) (tau : ℝ) {H B sigma : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hKH : 1 ≤ (K : ℝ) + H)
    (hsupport : (K : ℝ) + H ≤ X) (hsigma : 1 < sigma)
    (hlarge : B / (2 * Real.pi) + Real.log ((K : ℝ) + H) * H <
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist tau n‖) :
    B < ‖∫ y : ℝ,
      heathBrownDyadicAggregate L X k
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (K : ℝ) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)‖ := by
  have hsm := norm_tsum_vonMangoldtTwist_smoothWeight_gt_of_partialSum_gt
    tau hH hKH hlarge
  have hid := tsum_vonMangoldtTwist_smoothWeight_eq_integral_heathBrownDyadicAggregate
    L X k hXL tau (N := (K : ℝ)) (H := H) (sigma := sigma)
      (by exact_mod_cast hK) hH hsupport hsigma
  have hnorm := congrArg norm hid
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi] at hnorm
  rw [hnorm] at hsm
  exact hsm

end RHTower.Sieve
