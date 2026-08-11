import GaloisForLFunctions.RHTower.Sieve.MaynardLowTotalBound
import GaloisForLFunctions.RHTower.Sieve.PerronSummable

/-!
# Exact short-window projection of low-total boxes

Low-total boxes cannot be discarded from a smooth prefix: the prefix weight equals one below its
edge.  They do, however, cancel exactly between the two adjacent prefixes defining the smooth
short window.  This support-exact projection avoids every fixed power loss near `sigma = 1`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Smoothed Perron identity for one literal signed Heath--Brown box. -/
theorem smul_tsum_heathBrownDyadicTermBox_smoothWeight_eq_integral
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownDyadicTermBox L X k m a b q) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownDyadicTermProduct L X k m a b q
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownDyadicTermBox L X k m a b q
  have hF0 : complexCoeff F 0 = 0 := by
    have hsupport := upperSupported_heathBrownDyadicTermBox L X k m a b q
    by_contra hne
    have hmem := hsupport 0 (by
      intro hzero
      apply hne
      simp [F, complexCoeff_apply, hzero])
    simp at hmem
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k m a b q (sigma : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hsigma hsum
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownDyadicTermBox
    L X k m a b q ((sigma : ℂ) + (y : ℝ) * I)

/-- A box supported below `N` contributes identical adjacent smooth-prefix integrals. -/
theorem integral_heathBrownDyadicTermProduct_adjacent_smoothWeight_eq
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma)
    (hupper : (heathBrownDyadicCoreUpper (k - m) a b q : ℝ) ≤ N) :
    (∫ y : ℝ,
      heathBrownDyadicTermProduct L X k m a b q
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownDyadicTermProduct L X k m a b q
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownDyadicTermBox L X k m a b q
  have hsumEq : (∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight
          (N + H) H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, complexCoeff F n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    intro n
    by_cases hn : complexCoeff F n = 0
    · rw [hn]
      simp
    · have hnmem := complexCoeff_heathBrownDyadicTermBox_support_Icc_edges
        L X k m a b q n hn
      have hnupper := (Finset.mem_Icc.mp hnmem).2
      have hnN : (n : ℝ) ≤ N :=
        (by exact_mod_cast hnupper : (n : ℝ) ≤
          (heathBrownDyadicCoreUpper (k - m) a b q : ℝ)).trans hupper
      rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
          (hnN.trans (by linarith)),
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hnN]
  have hplus := smul_tsum_heathBrownDyadicTermBox_smoothWeight_eq_integral
    L X k m a b q (N := N + H) (H := H) (sigma := sigma)
      (by linarith) hH hsigma
  have hbase := smul_tsum_heathBrownDyadicTermBox_smoothWeight_eq_integral
    L X k m a b q (N := N) (H := H) (sigma := sigma) hN hH hsigma
  rw [hsumEq] at hplus
  exact hplus.symm.trans hbase

/-- Heterogeneous factor lower edge is the dyadic core lower edge. -/
theorem groupedDyadicLower_heathBrownBoxFactorExponent
    {k m : ℕ} (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    groupedDyadicLower (heathBrownBoxFactorExponent a b q) =
      heathBrownDyadicCoreLower (k - m) a b q := by
  simp [groupedDyadicLower, heathBrownBoxFactorExponent,
    HeathBrownBoxFactorIndex, heathBrownDyadicCoreLower]
  ring

/-- Low total logarithmic mass forces the exact box support below the corresponding power edge. -/
theorem heathBrownBox_upper_lt_of_not_eligible
    (L X k : ℕ) {T0 t : ℝ} (hT0 : 1 < T0)
    (c : HeathBrownBoxChoice L X k)
    (hnot : ¬ IsHeathBrownBoxEligible L X k T0 t c) :
    (heathBrownDyadicCoreUpper (k - c.m) c.a c.b c.q : ℝ) <
      (2 ^ (2 * (k - c.m)) : ℝ) * T0 ^ t := by
  have hmass : heathBrownBoxTotalExponent L X k T0 c < t := by
    simpa [IsHeathBrownBoxEligible] using lt_of_not_ge hnot
  have hedge :
      (heathBrownDyadicCoreLower (k - c.m) c.a c.b c.q : ℝ) =
        T0 ^ heathBrownBoxTotalExponent L X k T0 c := by
    rw [← groupedDyadicLower_heathBrownBoxFactorExponent c.a c.b c.q]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT0
        (heathBrownBoxFactorExponent c.a c.b c.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k c.m))
  have hm : c.m < k := by
    simpa [HeathBrownBoxChoice.m] using c.1.isLt
  rw [heathBrownDyadicCoreUpper_eq_twoPow_mul_lower (by omega)]
  push_cast
  rw [hedge]
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow_of_exponent_lt hT0 hmass) (by positivity)

end RHTower.Sieve
