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

private theorem arithmeticFunction_sum_apply
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

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

/-- One common scale inequality places every ineligible box below the short-window edge. -/
theorem heathBrownBox_upper_le_window_of_not_eligible
    (L X k : ℕ) {T0 t N : ℝ} (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (c : HeathBrownBoxChoice L X k)
    (hnot : ¬ IsHeathBrownBoxEligible L X k T0 t c) :
    (heathBrownDyadicCoreUpper (k - c.m) c.a c.b c.q : ℝ) ≤ N := by
  have hsmall := heathBrownBox_upper_lt_of_not_eligible L X k hT0 c hnot
  push_cast at hscale
  have hpow : (2 : ℝ) ^ (2 * (k - c.m)) ≤ (2 : ℝ) ^ (2 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact hsmall.le.trans <|
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by linarith) t)).trans hscale

/-- Arithmetic-function packet containing exactly the low-total signed boxes. -/
def heathBrownLowTotalPacket
    (L X k : ℕ) (T0 t : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ∑ c : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t c then 0 else
      heathBrownDyadicTermBox L X k c.m c.a c.b c.q

/-- L-series of the low-total packet is the pointwise low-total aggregate. -/
theorem LSeries_heathBrownLowTotalPacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownLowTotalPacket L X k T0 t)) s =
      heathBrownLowTotalDyadicAggregate L X k T0 t s := by
  classical
  rw [heathBrownLowTotalPacket, complexCoeff_sum, LSeries_sum]
  · simp only [heathBrownLowTotalDyadicAggregate]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases h : IsHeathBrownBoxEligible L X k T0 t c
    · simp only [h, if_true]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact congrFun LSeries_zero s
    · simp [h, heathBrownBoxTerm]
      exact LSeries_heathBrownDyadicTermBox L X k c.m c.a c.b c.q s
  · intro c _hc
    by_cases h : IsHeathBrownBoxEligible L X k T0 t c
    · simp only [h, if_true]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact LSeriesSummable_zero
    · simp only [h, if_false]
      exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k c.m c.a c.b c.q s

theorem LSeriesSummable_heathBrownLowTotalPacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownLowTotalPacket L X k T0 t)) s := by
  classical
  rw [heathBrownLowTotalPacket, complexCoeff_sum]
  apply LSeriesSummable.sum
  intro c _hc
  by_cases h : IsHeathBrownBoxEligible L X k T0 t c
  · simp only [h, if_true]
    have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
      funext n
      simp [complexCoeff_apply]
    rw [hzero]
    exact LSeriesSummable_zero
  · simp only [h, if_false]
    exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
      L X k c.m c.a c.b c.q s

/-- Under the common scale condition, every nonzero low-packet coefficient lies below `N`. -/
theorem complexCoeff_heathBrownLowTotalPacket_nonzero_le
    (L X k : ℕ) {T0 t N : ℝ} (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    {n : ℕ}
    (hn : complexCoeff (heathBrownLowTotalPacket L X k T0 t) n ≠ 0) :
    (n : ℝ) ≤ N := by
  classical
  by_contra hnot
  have hnN : N < (n : ℝ) := lt_of_not_ge hnot
  have hpacket : heathBrownLowTotalPacket L X k T0 t n = 0 := by
    rw [heathBrownLowTotalPacket]
    rw [arithmeticFunction_sum_apply]
    apply Finset.sum_eq_zero
    intro c _hc
    by_cases h : IsHeathBrownBoxEligible L X k T0 t c
    · simp [h]
    · simp only [h, if_false]
      by_contra hterm
      have hnmem := upperSupported_heathBrownDyadicTermBox
        L X k c.m c.a c.b c.q n hterm
      have hnupper : (n : ℝ) ≤
          (heathBrownDyadicCoreUpper (k - c.m) c.a c.b c.q : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hnmem).2
      have hbox := heathBrownBox_upper_le_window_of_not_eligible
        L X k hT0 hscale c h
      linarith
  apply hn
  simp [complexCoeff_apply, hpacket]

/-- Smoothed Perron identity for the complete low-total packet. -/
theorem smul_tsum_heathBrownLowTotalPacket_smoothWeight_eq_integral
    (L X k : ℕ) (T0 t : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownLowTotalPacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownLowTotalDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownLowTotalPacket L X k T0 t
  have hF0 : complexCoeff F 0 = 0 := by
    classical
    have hpacket : F 0 = 0 := by
      dsimp only [F]
      rw [heathBrownLowTotalPacket, arithmeticFunction_sum_apply]
      apply Finset.sum_eq_zero
      intro c _hc
      by_cases h : IsHeathBrownBoxEligible L X k T0 t c
      · simp [h]
      · simp only [h, if_false]
        by_contra hterm
        have hmem := upperSupported_heathBrownDyadicTermBox
          L X k c.m c.a c.b c.q 0 hterm
        simp at hmem
    simp [complexCoeff_apply, hpacket]
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownLowTotalPacket L X k T0 t (sigma : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hsigma hsum
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownLowTotalPacket
    L X k T0 t ((sigma : ℂ) + (y : ℝ) * I)

/-- **Exact low-total cancellation in the adjacent-prefix short window.** -/
theorem integral_heathBrownLowTotalDyadicAggregate_adjacent_smoothWeight_eq
    (L X k : ℕ) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (∫ y : ℝ,
      heathBrownLowTotalDyadicAggregate L X k T0 t
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownLowTotalDyadicAggregate L X k T0 t
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownLowTotalPacket L X k T0 t
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
    · have hnN := complexCoeff_heathBrownLowTotalPacket_nonzero_le
        L X k hT0 hscale hn
      rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH
          (hnN.trans (by linarith)),
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hnN]
  have hplus := smul_tsum_heathBrownLowTotalPacket_smoothWeight_eq_integral
    L X k T0 t (N := N + H) (H := H) (sigma := sigma) (by linarith) hH hsigma
  have hbase := smul_tsum_heathBrownLowTotalPacket_smoothWeight_eq_integral
    L X k T0 t (N := N) (H := H) (sigma := sigma) hN hH hsigma
  rw [hsumEq] at hplus
  exact hplus.symm.trans hbase

end RHTower.Sieve
