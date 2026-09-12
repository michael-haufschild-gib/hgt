import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepValueTruncation
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualHeadMainApproximation
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFiniteDetectorDirichlet

/-!
# Height-uniform displaced zeta value truncation

The direct Gaussian edge has an explicit `L^-1` tail.  The deep reflected
edge has the fixed `L^(-7/2)` tail, uniformly up to polynomial height growth.
Their exact AFE is then compared to the finite classical reflected head.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

/-- Uniform `n^-2` envelope for the direct value coefficients. -/
theorem exists_norm_smoothAFEZetaDisplacedDirectTerm_le_rpow
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (tau : ℝ) (n : ℕ),
      ‖smoothAFEZetaDisplacedDirectTerm d x tau n‖ ≤
        C * (n + 1 : ℝ) ^ (-2 : ℝ) := by
  obtain ⟨K, hK, hcut⟩ :=
    exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  let C : ℝ := K * x ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun tau n => ?_⟩
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have harg : 0 < r / x := div_pos hr0 hx
  have hcutPower :
      ‖smoothAFECutoff (r / x)‖ ≤ K * x ^ 2 * r ^ (-2 : ℝ) := by
    calc
      ‖smoothAFECutoff (r / x)‖ ≤ K * (r / x) ^ (-2 : ℝ) := hcut harg
      _ = K * x ^ 2 * r ^ (-2 : ℝ) := by
        rw [Real.div_rpow hr0.le hx.le]
        rw [Real.rpow_neg hr0.le, Real.rpow_neg hx.le]
        have hr2 : r ^ (2 : ℝ) ≠ 0 :=
          (Real.rpow_pos_of_pos hr0 2).ne'
        have hx2 : x ^ (2 : ℝ) ≠ 0 :=
          (Real.rpow_pos_of_pos hx 2).ne'
        field_simp [hr2, hx2]
        rw [Real.rpow_two]
  rw [smoothAFEZetaDisplacedDirectTerm, norm_mul,
    norm_natSucc_cpow_neg_displacedLinePt]
  have hp : 0 ≤ r ^ (-(1 / 2 - d)) := Real.rpow_nonneg hr0.le _
  calc
    r ^ (-(1 / 2 - d)) * ‖smoothAFECutoff (r / x)‖
      ≤ r ^ (-(1 / 2 - d)) * (K * x ^ 2 * r ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcutPower hp
    _ = C * r ^ (d - 5 / 2) := by
      dsimp only [C]
      rw [show r ^ (-(1 / 2 - d)) * (K * x ^ 2 * r ^ (-2 : ℝ)) =
          (K * x ^ 2) *
            (r ^ (-(1 / 2 - d)) * r ^ (-2 : ℝ)) by ring_nf]
      rw [← Real.rpow_add hr0]
      congr 1
      ring_nf
    _ ≤ C * r ^ (-2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) hC
    _ = C * (n + 1 : ℝ) ^ (-2 : ℝ) := rfl

/-- Explicit `L^-1` tail of the direct value series. -/
theorem exists_norm_smoothAFEZetaDisplacedDirectTerm_tsum_sub_sum_le
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖(∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x tau n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectTerm d x tau n‖ ≤
        C * (L : ℝ) ^ (-1 : ℝ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectTerm_le_rpow hdhalf hx
  refine ⟨C, hC, fun tau L hL => ?_⟩
  let f : ℕ → ℂ := fun n => smoothAFEZetaDisplacedDirectTerm d x tau n
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    simpa only [f] using
      summable_norm_smoothAFEZetaDisplacedDirectTerm hdhalf hx tau
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [show (fun n : ℕ => smoothAFEZetaDisplacedDirectTerm d x tau n) = f by
    rfl, heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) := by
    have hbase := Real.summable_nat_rpow.mpr
      (show (-2 : ℝ) < -1 by norm_num)
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      C * (((j + L + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) := hpow.mul_left C
  calc
    ‖∑' j : ℕ, f (j + L)‖ ≤ ∑' j : ℕ, ‖f (j + L)‖ :=
      norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ, C * (((j + L + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) := by
      exact Summable.tsum_le_tsum (fun j => by
        have h := hpoint tau (j + L)
        have hcast :
            ((j + L : ℕ) : ℝ) + 1 = ((j + L + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast] at h
        simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc] using h)
        hnormTail hmajor
    _ = C * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) := by
      rw [tsum_mul_left]
    _ ≤ C * ((L : ℝ) ^ ((1 : ℝ) - 2) / ((2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le (show (1 : ℝ) < 2 by norm_num) hL) hC
    _ = C * (L : ℝ) ^ (-1 : ℝ) := by ring_nf

/-- Finite deep-edge approximation to the zeta value. -/
def smoothAFEZetaDisplacedDeepFiniteValue
    (d x tau : ℝ) (L : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDirectTerm d x tau n) -
    (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
    smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x

/-- Exact displaced AFE with the reflected edge on the deep contour. -/
theorem riemannZeta_displaced_eq_direct_tsum_sub_deep_tsum
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) :
    riemannZeta (displacedLinePt d tau) =
      (∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x tau n) -
      (∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x := by
  have hdhalf : d < 1 / 2 := hdq.trans_lt (by norm_num)
  have hbase :=
    riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight
      hx hd hdhalf tau
  have hweighted :
      (∑' n : ℕ,
        (zetaChi (displacedLinePt d tau) *
          (n + 1 : ℂ) ^ (displacedLinePt d tau - 1)) *
          smoothAFEZetaDisplacedDualWeight d tau ((n + 1 : ℝ) * x)) =
        -(∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [smoothAFEZetaDisplacedDeepCoefficient_eq_general hx hd hdq tau n,
      smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight hx d tau n]
    ring
  rw [hweighted] at hbase
  simpa only [smoothAFEZetaDisplacedDirectTerm, sub_eq_add_neg] using hbase

/-- Direct plus deep reflected tails with explicit fourth-power height growth. -/
theorem exists_norm_riemannZeta_displaced_sub_deepFiniteValue_rpow_four_le
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedDeepFiniteValue d x tau L‖ ≤
        C * (L : ℝ) ^ (-1 : ℝ) +
          D * (1 + |tau|) ^ 4 *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  have hdhalf : d < 1 / 2 := hdq.trans_lt (by norm_num)
  obtain ⟨C, hC, hdirect⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectTerm_tsum_sub_sum_le
      hdhalf hx
  obtain ⟨D, hD, hreflected⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficient_tsum_sub_sum_rpow_four_le
      hx hd hdq
  refine ⟨C, D, hC, hD, fun tau L hL => ?_⟩
  rw [riemannZeta_displaced_eq_direct_tsum_sub_deep_tsum hx hd hdq tau]
  unfold smoothAFEZetaDisplacedDeepFiniteValue
  have hdecomp :
      ((∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x tau n) -
          (∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
          smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x) -
        ((∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectTerm d x tau n) -
          (∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
          smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x) =
        ((∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x tau n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectTerm d x tau n) -
        ((∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficient d tau x n) := by ring
  rw [hdecomp]
  exact (norm_sub_le _ _).trans
    (add_le_add (hdirect tau L hL) (hreflected tau L hL))

/-- Polynomial-form compatibility wrapper for the explicit fourth-power AFE. -/
theorem exists_norm_riemannZeta_displaced_sub_deepFiniteValue_le
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    ∃ (C D : ℝ) (N : ℕ), 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedDeepFiniteValue d x tau L‖ ≤
        C * (L : ℝ) ^ (-1 : ℝ) +
          D * (1 + |tau|) ^ N *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  obtain ⟨C, D, hC, hD, hbound⟩ :=
    exists_norm_riemannZeta_displaced_sub_deepFiniteValue_rpow_four_le hx hd hdq
  exact ⟨C, D, 4, hC, hD, hbound⟩

/-- Height-uniform classical value truncation with explicit fourth-power deep tail. -/
theorem exists_norm_riemannZeta_displaced_sub_finiteClassicalValue_rpow_four_uniform_le
    {x d eta : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaq : eta ≤ 1 / 4) :
    ∃ C D E : ℝ,
      0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧
      ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalValue d x tau L‖ ≤
        C * (L : ℝ) ^ (-1 : ℝ) +
          D * (1 + |tau|) ^ 4 *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
  obtain ⟨C, D, hC, hD, hdeep⟩ :=
    exists_norm_riemannZeta_displaced_sub_deepFiniteValue_rpow_four_le hx hd hdq
  have hdhalf : d < 1 / 2 := hdq.trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaq.trans_lt (by norm_num)
  obtain ⟨E, hE, hcorr⟩ :=
    exists_norm_sum_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le
      hd.le hdhalf heta hetaHalf
  refine ⟨C, D, E, hC, hD, hE, fun tau L hL => ?_⟩
  have hcorr' :
      ‖smoothAFEZetaDisplacedDeepFiniteValue d x tau L -
          smoothAFEZetaDisplacedFiniteClassicalValue d x tau L‖ ≤
        E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
    have hsum :
        (∑ n ∈ Finset.range L,
          (smoothAFEZetaDisplacedDeepCoefficient d tau x n +
            zetaChi (displacedLinePt d tau) *
              (n + 1 : ℂ) ^ (displacedLinePt d tau - 1))) =
        ∑ n ∈ Finset.range L,
          (smoothAFEZetaDualCoefficientGeneral
              (displacedLinePt d tau) x n +
            zetaChi (displacedLinePt d tau) *
              (n + 1 : ℂ) ^ (displacedLinePt d tau - 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [smoothAFEZetaDisplacedDeepCoefficient_eq_general hx hd hdq tau n]
    have hdiff :
        smoothAFEZetaDisplacedDeepFiniteValue d x tau L -
            smoothAFEZetaDisplacedFiniteClassicalValue d x tau L =
          -(∑ n ∈ Finset.range L,
            (smoothAFEZetaDisplacedDeepCoefficient d tau x n +
              zetaChi (displacedLinePt d tau) *
                (n + 1 : ℂ) ^ (displacedLinePt d tau - 1))) := by
      unfold smoothAFEZetaDisplacedDeepFiniteValue
        smoothAFEZetaDisplacedFiniteClassicalValue
        smoothAFEZetaDisplacedReflectedMainTerm
      rw [Finset.sum_add_distrib]
      ring
    rw [hdiff, norm_neg, hsum]
    exact hcorr d hd le_rfl tau hx L
  have hsplit :
      riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalValue d x tau L =
        (riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedDeepFiniteValue d x tau L) +
        (smoothAFEZetaDisplacedDeepFiniteValue d x tau L -
          smoothAFEZetaDisplacedFiniteClassicalValue d x tau L) := by ring
  rw [hsplit]
  exact (norm_add_le _ _).trans
    (add_le_add (hdeep tau L hL) hcorr')

/-- Polynomial-form compatibility wrapper for the explicit fourth-power truncation. -/
theorem exists_norm_riemannZeta_displaced_sub_finiteClassicalValue_uniform_le
    {x d eta : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaq : eta ≤ 1 / 4) :
    ∃ (C D E : ℝ) (N : ℕ),
      0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧
      ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalValue d x tau L‖ ≤
        C * (L : ℝ) ^ (-1 : ℝ) +
          D * (1 + |tau|) ^ N *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
  obtain ⟨C, D, E, hC, hD, hE, hbound⟩ :=
    exists_norm_riemannZeta_displaced_sub_finiteClassicalValue_rpow_four_uniform_le
      hx hd hdq heta hetaq
  exact ⟨C, D, E, 4, hC, hD, hE, hbound⟩

end RHTower
